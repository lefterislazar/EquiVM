import Examples.Precompiles.Modexp.MultiLimbSchoolbookOuterComplete
import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookDenormalizationSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookZeroShiftRemainderSemantic

/-!
# Complete semantic composition of schoolbook division

This module identifies the quotient loop's terminal `(count+1)`-word window with the low `u`
array consumed by the two remainder-return branches. The reduced-remainder theorem forces the
extra top word to zero; it is not assumed as an execution postcondition.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookCompleteSemantic

open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookDivisionSemantic
open MultiLimbSchoolbookDigitSemantic
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookOuterComplete
open MultiLimbSchoolbookOuterSemantic
open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookNormalizationSemantic
open MultiLimbSchoolbookDenormalizationSemantic
open MultiLimbSchoolbookZeroShiftRemainderSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem terminalUAddress_eq_arrayAddress
    (u : UInt256) (index : Nat)
    (hindex : index ≤ 32)
    (hfit : u.toNat + 32 * (index + 1) < UInt256.size) :
    multiplySubtractUAddress u (UInt256.ofNat 1) (UInt256.ofNat index) =
      arrayAddress u index := by
  apply u256_inj
  rw [multiplySubtractUAddress_ofNat_toNat u 1 index (by omega) (by omega) (by omega)
    (by simpa only [Nat.add_comm 1 index] using hfit)]
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  rw [MultiLimbOddCompare.elementPtr_ofNat_toNat u index hindex hfit]
  omega

theorem windowReadSlice_one_eq_arrayReadWords
    (mem : ByteArray) (aw u : UInt256) (start count : Nat)
    (hrange : start + count ≤ 32)
    (hfit : u.toNat + 32 * (start + count + 1) < UInt256.size) :
    windowReadSlice mem aw u 1 start count =
      arrayReadWords mem aw u start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      have haddress := terminalUAddress_eq_arrayAddress u start (by omega) (by omega)
      simp only [windowReadSlice, arrayReadWords]
      rw [haddress]
      unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
        MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
        MultiLimbOddCompare.headerWord arrayAddress MultiLimbSchoolbookSingle.arrayAddress
      rw [ih (start + 1) (by omega) (by omega)]

@[simp] theorem divisorReadSlice_length
    (mem : ByteArray) (aw v : UInt256) (start count : Nat) :
    (divisorReadSlice mem aw v start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [divisorReadSlice, ih]

theorem divisorReadSlice_eq_arrayReadWords
    (mem : ByteArray) (aw v : UInt256) (start count : Nat) :
    divisorReadSlice mem aw v start count = arrayReadWords mem aw v start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [divisorReadSlice, arrayReadWords]
      change MultiLimbSchoolbookNormalization.arrayWord mem aw v start :: _ = _
      rw [ih]

/-- A nonempty continuation chain's abstract divisor words are the exact concrete normalized `v`
slice loaded by its first generated multiply-subtract pass. -/
theorem semanticContinuations_divisor_eq_array
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ []) :
    Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 count) := by
  cases h with
  | done => exact (hnonempty rfl).elim
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest =>
      rw [← semantic.hvSlice, divisorReadSlice_eq_arrayReadWords]

/-- The terminal window observer is the ordinary low `u` slice plus `u[count]` as its top word. -/
theorem terminalRemainderNat_eq_array
    (mem : ByteArray) (aw u : UInt256) (count : Nat)
    (hrange : count ≤ 32)
    (hfit : u.toNat + 32 * (count + 1) < UInt256.size) :
    terminalRemainderNat mem aw u count =
      Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 count) +
        UInt256.size ^ count * (arrayWord mem aw u count).toNat := by
  have hlower := windowReadSlice_one_eq_arrayReadWords mem aw u 0 count
    (by simpa using hrange) (by simpa using hfit)
  have htop := terminalUAddress_eq_arrayAddress u count hrange hfit
  unfold terminalRemainderNat windowNat
  rw [hlower, htop, arrayReadWords_length]
  rfl

/-- Every nonempty semantic chain identifies a divisor list of exactly `count` words. -/
theorem semanticContinuations_divisor_length
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ []) :
    (vRest ++ [vSecond, vTop]).length = count := by
  cases h with
  | done => exact (hnonempty rfl).elim
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest =>
      have hlength := congrArg List.length semantic.hvSlice
      simpa only [divisorReadSlice_length] using hlength.symm

/-- Reduced remainder plus the concrete terminal-window equation forces the unused top `u` word
to zero. -/
theorem semanticContinuations_terminal_top_eq_zero
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hrange : count ≤ 32)
    (hfit : u.toNat + 32 * (count + 1) < UInt256.size) :
    arrayWord finalMem finalAw u count = ⟨0⟩ := by
  let divisorWords := vRest ++ [vSecond, vTop]
  let divisor := Modexp.wordLimbsToNat divisorWords
  have hlength : divisorWords.length = count :=
    semanticContinuations_divisor_length h hnonempty
  have hdivisorPos : 0 < divisor := normalizedDivisor_positive vRest vSecond vTop hnormalized
  have hdivisorBound : divisor < UInt256.size ^ count := by
    have hbound := Modexp.wordLimbsToNat_lt_pow divisorWords
    simpa only [hlength] using hbound
  have hremainder := semanticContinuations_remainder_eq_mod h hnonempty hnormalized
  have hwindow := terminalRemainderNat_eq_array finalMem finalAw u count hrange hfit
  have hterminalBound : terminalRemainderNat finalMem finalAw u count <
      UInt256.size ^ count := by
    calc
      terminalRemainderNat finalMem finalAw u count =
          digitsToNatMSB UInt256.size inputs % divisor := hremainder
      _ < divisor := Nat.mod_lt _ hdivisorPos
      _ < UInt256.size ^ count := hdivisorBound
  rw [hwindow] at hterminalBound
  have htopNat : (arrayWord finalMem finalAw u count).toNat = 0 := by
    by_contra hne
    have hone : 1 ≤ (arrayWord finalMem finalAw u count).toNat :=
      Nat.one_le_iff_ne_zero.mpr hne
    have hpow : 0 < UInt256.size ^ count :=
      Nat.pow_pos (by norm_num [UInt256.size])
    nlinarith
  apply u256_inj
  norm_num [htopNat]

/-- The exact low `u` slice consumed by denormalization/direct-copy is the normalized natural
remainder produced by the quotient loop. -/
theorem semanticContinuations_terminal_slice_eq_mod
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hrange : count ≤ 32)
    (hfit : u.toNat + 32 * (count + 1) < UInt256.size) :
    Modexp.wordLimbsToNat (arrayReadWords finalMem finalAw u 0 count) =
      digitsToNatMSB UInt256.size inputs %
        Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  have htop := semanticContinuations_terminal_top_eq_zero h hnonempty hnormalized hrange hfit
  have hwindow := terminalRemainderNat_eq_array finalMem finalAw u count hrange hfit
  have hremainder := semanticContinuations_remainder_eq_mod h hnonempty hnormalized
  rw [htop] at hwindow
  simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.mul_zero, Nat.add_zero] at hwindow
  exact hwindow.symm.trans hremainder

/-- Positive normalization cancels from the exact quotient computed by the semantic chain. -/
theorem positiveShift_quotient_eq_original_div
    {count uCount quotientCount shiftNat dividend divisor : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (inputs.length + count)) = dividend * 2 ^ shiftNat)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 count) =
      divisor * 2 ^ shiftNat) :
    natLimbsToNat UInt256.size
        (quotientReadNats finalMem finalAw quotient inputs.length) = dividend / divisor := by
  have hquotient := semanticContinuations_quotient_eq_div h hnormalized
  have hinput := semanticContinuations_zero_inputValue h hnonempty hnormalized hquotBelowU
  have hv := semanticContinuations_divisor_eq_array h hnonempty
  rw [hinput, hdividend, hv, hdivisor] at hquotient
  rw [Nat.mul_div_mul_right dividend divisor (by positivity : 0 < 2 ^ shiftNat)] at hquotient
  exact hquotient

/-- Positive-shift remainder extraction cancels the same normalization factor from the concrete
terminal modulo result. -/
theorem positiveShift_remainder_eq_original_mod
    {count uCount quotientCount shiftNat dividend divisor : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hshiftPos : 0 < shiftNat) (hshift : shiftNat < 256)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (inputs.length + count)) = dividend * 2 ^ shiftNat)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 count) =
      divisor * 2 ^ shiftNat)
    (hrange : count ≤ 32)
    (huFit : u.toNat + 32 * (count + 1) < UInt256.size)
    (hawFit : finalAw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem j).toNat + 32 ≤ finalMem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress rem j).toNat + 32 ≤ 32 * finalAw.toNat)
    (hremBelowU : ∀ i j, i < count -> j < count ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress u j).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw u rem
          shiftNat 0 count finalMem).memory finalAw rem 0 count) =
      dividend % divisor := by
  have hterminal := semanticContinuations_terminal_slice_eq_mod h hnonempty hnormalized
    hrange huFit
  have hinput := semanticContinuations_zero_inputValue h hnonempty hnormalized hquotBelowU
  have hv := semanticContinuations_divisor_eq_array h hnonempty
  have hdenormalized := denormalizeRange_finalSlice_toNat finalAw u rem shiftNat 0 count
    finalMem hshiftPos hshift hawFit (by simpa using hwrite) (by simpa using hactive)
    (by
      intro i j hi hj
      simpa only [Nat.zero_add] using hremBelowU i j hi hj)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hordered i j hij hj)
  rw [hterminal, hinput, hdividend, hv, hdivisor] at hdenormalized
  rw [Nat.mul_mod_mul_right] at hdenormalized
  rw [Nat.mul_div_left _ (by positivity : 0 < 2 ^ shiftNat)] at hdenormalized
  exact hdenormalized

/-- The marker-0 direct-copy branch returns the unscaled modulo result in concrete memory. -/
theorem zeroShift_remainder_eq_original_mod
    {count uCount quotientCount dividend divisor : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (inputs.length + count)) = dividend)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 count) = divisor)
    (hrange : count ≤ 32)
    (huFit : u.toNat + 32 * (count + 1) < UInt256.size)
    (hawFit : finalAw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress rem j).toNat + 32 ≤ finalMem.size)
    (hactive : ∀ j, j < count ->
      (arrayAddress rem j).toNat + 32 ≤ 32 * finalAw.toNat)
    (hremBelowU : ∀ i j, i < count -> j < count ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress u j).toNat)
    (hordered : ∀ i j, i < j -> j < count ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw u rem 0 count
          finalMem).memory finalAw rem 0 count) =
      dividend % divisor := by
  have hterminal := semanticContinuations_terminal_slice_eq_mod h hnonempty hnormalized
    hrange huFit
  have hinput := semanticContinuations_zero_inputValue h hnonempty hnormalized hquotBelowU
  have hv := semanticContinuations_divisor_eq_array h hnonempty
  have hcopied := copyRange_finalSlice_toNat finalAw u rem 0 count finalMem hawFit
    (by simpa using hwrite) (by simpa using hactive)
    (by
      intro i j hi hj
      simpa only [Nat.zero_add] using hremBelowU i j hi hj)
    (by
      intro i j hij hj
      simpa only [Nat.zero_add] using hordered i j hij hj)
  rw [hinput, hdividend, hv, hdivisor] at hterminal
  exact hcopied.trans hterminal

end Modexp.MultiLimbSchoolbookCompleteSemantic
