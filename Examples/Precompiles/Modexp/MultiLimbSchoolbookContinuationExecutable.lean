import Examples.Precompiles.Modexp.MultiLimbSchoolbookCompleteSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookIterationExecutable

/-!
# Constructive arbitrary schoolbook continuation

This module derives the recursive long-division invariant from each concrete selected digit. The
eventual constructor produces `SemanticContinuations` and its exact path gas without taking a
continuation certificate as an input.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookContinuationExecutable

open MultiLimbSchoolbookCompleteSemantic
open MultiLimbSchoolbookDivisionSemantic
open MultiLimbSchoolbookIterationExecutable
open MultiLimbSchoolbookIterationComplete
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookEstimateSemantic
open MultiLimbSchoolbookDigitSemantic
open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookNormalizationSemantic
open MultiLimbSchoolbookOuterComplete
open MultiLimbSchoolbookOuterLoopFunction
open MultiLimbSchoolbookOuterSemantic

set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Comparing equal-length little-endian lists with explicit top limbs compares those top limbs
weakly. This is the leading-digit fact used by every Knuth continuation. -/
theorem top_toNat_le_of_wordLimbsToNat_lt
    (left right : List UInt256) (leftTop rightTop : UInt256)
    (hlength : left.length = right.length)
    (hlt : Modexp.wordLimbsToNat (left ++ [leftTop]) <
      Modexp.wordLimbsToNat (right ++ [rightTop])) :
    leftTop.toNat ≤ rightTop.toNat := by
  have hleftBound := Modexp.wordLimbsToNat_lt_pow left
  have hrightBound := Modexp.wordLimbsToNat_lt_pow right
  have hpowPos : 0 < UInt256.size ^ left.length := by
    exact Nat.pow_pos (by norm_num [UInt256.size])
  rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append] at hlt
  simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero] at hlt
  rw [← hlength] at hlt hrightBound
  by_contra hnot
  have htop : rightTop.toNat + 1 ≤ leftTop.toNat := by omega
  nlinarith

/-- Prefixing a zero little-endian limb is multiplication by the EVM word radix. -/
theorem wordLimbsToNat_zero_cons (words : List UInt256) :
    Modexp.wordLimbsToNat ((⟨0⟩ : UInt256) :: words) =
      UInt256.size * Modexp.wordLimbsToNat words := by
  simp only [Modexp.wordLimbsToNat, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    zero_add]

/-- A reduced `count`-word remainder has a top word no larger than the normalized divisor top. -/
theorem reduced_top_le
    (remainderLow divisorLow : List UInt256) (remainderTop divisorTop : UInt256)
    (hlength : remainderLow.length = divisorLow.length)
    (hreduced : Modexp.wordLimbsToNat (remainderLow ++ [remainderTop]) <
      Modexp.wordLimbsToNat (divisorLow ++ [divisorTop])) :
    remainderTop.toNat ≤ divisorTop.toNat :=
  top_toNat_le_of_wordLimbsToNat_lt remainderLow divisorLow remainderTop divisorTop
    hlength hreduced

/-- Adding one lower radix digit to a reduced remainder remains below radix times the divisor. -/
theorem nextWindow_lt_radix_mul
    (input remainder divisor : Nat)
    (hinput : input < UInt256.size)
    (hdivisor : 0 < divisor)
    (hremainder : remainder < divisor) :
    input + UInt256.size * remainder < UInt256.size * divisor := by
  have hremSucc : remainder + 1 ≤ divisor := by omega
  nlinarith

/-- Generated current-window loads split at any limb boundary. -/
theorem windowReadSlice_add
    (mem : ByteArray) (aw u : UInt256) (cursor start left right : Nat) :
    windowReadSlice mem aw u cursor start (left + right) =
      windowReadSlice mem aw u cursor start left ++
        windowReadSlice mem aw u cursor (start + left) right := by
  induction left generalizing start with
  | zero => simp [windowReadSlice]
  | succ left ih =>
      simp only [Nat.succ_add, windowReadSlice, List.cons_append]
      rw [ih (start + 1)]
      congr 2
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Generated divisor loads split at any limb boundary. -/
theorem divisorReadSlice_add
    (mem : ByteArray) (aw v : UInt256) (start left right : Nat) :
    divisorReadSlice mem aw v start (left + right) =
      divisorReadSlice mem aw v start left ++
        divisorReadSlice mem aw v (start + left) right := by
  induction left generalizing start with
  | zero => simp [divisorReadSlice]
  | succ left ih =>
      simp only [Nat.succ_add, divisorReadSlice, List.cons_append]
      rw [ih (start + 1)]
      congr 2
      simp [Nat.add_comm, Nat.add_left_comm]

/-- A `count >= 2` divisor slice consists of its low prefix and the two refinement words. -/
theorem divisorReadSlice_lastTwo
    (mem : ByteArray) (aw v : UInt256) (count : Nat) (hcount : 2 ≤ count) :
    divisorReadSlice mem aw v 0 count =
      divisorReadSlice mem aw v 0 (count - 2) ++
        [MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v
          (UInt256.ofNat (count - 2)),
         MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v
          (UInt256.ofNat (count - 1))] := by
  have hsplit := divisorReadSlice_add mem aw v 0 (count - 2) 2
  have hcountEq : count - 2 + 2 = count := by omega
  rw [hcountEq] at hsplit
  calc
    divisorReadSlice mem aw v 0 count =
        divisorReadSlice mem aw v 0 (count - 2) ++
          divisorReadSlice mem aw v (count - 2) 2 := by
      simpa only [Nat.zero_add] using hsplit
    _ = divisorReadSlice mem aw v 0 (count - 2) ++
          [MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v
            (UInt256.ofNat (count - 2)),
           MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v
            (UInt256.ofNat (count - 1))] := by
      apply congrArg (fun tail => divisorReadSlice mem aw v 0 (count - 2) ++ tail)
      change
        [MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v
            (UInt256.ofNat (count - 2)),
          MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v
            (UInt256.ofNat (count - 2 + 1))] = _
      have hsecond : count - 2 + 1 = count - 1 := by omega
      rw [hsecond]

/-- A `count >= 2` generated window slice consists of its low prefix and the two concrete words
used by q-hat refinement. -/
theorem windowReadSlice_lastTwo
    (mem : ByteArray) (aw u : UInt256) (cursor count : Nat)
    (hcount : 2 ≤ count) :
    windowReadSlice mem aw u cursor 0 count =
      windowReadSlice mem aw u cursor 0 (count - 2) ++
        [MultiLimbDivisionTrace.readWord mem aw
          (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
            (UInt256.ofNat cursor) (UInt256.ofNat (count - 2))),
         MultiLimbDivisionTrace.readWord mem aw
          (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
            (UInt256.ofNat cursor) (UInt256.ofNat (count - 1)))] := by
  have hsplit := windowReadSlice_add mem aw u cursor 0 (count - 2) 2
  have hcountEq : count - 2 + 2 = count := by omega
  rw [hcountEq] at hsplit
  calc
    windowReadSlice mem aw u cursor 0 count =
        windowReadSlice mem aw u cursor 0 (count - 2) ++
          windowReadSlice mem aw u cursor (count - 2) 2 := by
      simpa only [Nat.zero_add] using hsplit
    _ = windowReadSlice mem aw u cursor 0 (count - 2) ++
          [MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat (count - 2))),
           MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat (count - 1)))] := by
      apply congrArg (fun tail => windowReadSlice mem aw u cursor 0 (count - 2) ++ tail)
      change
        [MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat (count - 2))),
          MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat (count - 2 + 1)))] = _
      have hsecond : count - 2 + 1 = count - 1 := by omega
      rw [hsecond]

/-- A bounded generated window load is the corresponding guarded concrete array word. -/
theorem windowReadWord_eq_arrayWord
    (mem : ByteArray) (aw u : UInt256) (cursor index : Nat)
    (hcursor : 0 < cursor)
    (hrange : cursor + index ≤ 66)
    (hsumWord : cursor + index < UInt256.size)
    (hfit : u.toNat + 32 * (cursor + index) < UInt256.size) :
    MultiLimbDivisionTrace.readWord mem aw
        (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
          (UInt256.ofNat cursor) (UInt256.ofNat index)) =
      arrayWord mem aw u (cursor + index - 1) := by
  have haddress := currentUAddress_eq_arrayAddress u cursor index hcursor hsumWord
    (by omega) hfit
  change MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
        (UInt256.ofNat cursor) (UInt256.ofNat index)) =
    MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookSingle.arrayAddress u (cursor + index - 1))
  rw [haddress]

/-- The generated `(count+1)`-word window model is exactly its concrete array segment. -/
theorem windowModel_eq_arraySegment
    (mem : ByteArray) (aw u : UInt256) (cursor count : Nat)
    (hcursor : 0 < cursor)
    (hwindowRange : cursor + count ≤ 66)
    (hsumWord : cursor + count < UInt256.size)
    (huFit : u.toNat + 32 * (cursor + count) < UInt256.size) :
    Modexp.wordLimbsToNat (arrayReadWords mem aw u (cursor - 1) (count + 1)) =
      windowNat (windowReadSlice mem aw u cursor 0 count)
        (MultiLimbDivisionTrace.readWord mem aw
          (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
            (UInt256.ofNat cursor) (UInt256.ofNat count))) := by
  rw [arrayReadWords_succ_append, windowNat_eq_append]
  have hlower0 := windowReadSlice_eq_arrayReadWords mem aw u cursor 0 count hcursor
    (by simpa using hwindowRange) (by simpa using hsumWord) (by simpa using huFit)
  have hlower : windowReadSlice mem aw u cursor 0 count =
      arrayReadWords mem aw u (cursor - 1) count := by
    simpa only [Nat.add_zero] using hlower0
  have htop := currentUAddress_eq_arrayAddress u cursor count hcursor hsumWord
    (by omega) huFit
  have htopIndex : cursor - 1 + count = cursor + count - 1 := by omega
  rw [htopIndex, ← hlower]
  change Modexp.wordLimbsToNat
      (windowReadSlice mem aw u cursor 0 count ++
        [MultiLimbDivisionTrace.readWord mem aw
          (MultiLimbSchoolbookSingle.arrayAddress u (cursor + count - 1))]) = _
  rw [← htop]

/-- A bounded generated divisor load is its guarded concrete array word. -/
theorem divisorReadWord_eq_arrayWord
    (mem : ByteArray) (aw v : UInt256) (index count : Nat)
    (hindex : index < count)
    (hfit : v.toNat + 32 * (count + 1) < UInt256.size) :
    MultiLimbSchoolbookDivision.multiplySubtractVi mem aw v (UInt256.ofNat index) =
      arrayWord mem aw v index := by
  have haddress :
      (MultiLimbSchoolbookDivision.multiplySubtractVAddress v
        (UInt256.ofNat index)).toNat = v.toNat + 32 * (index + 1) := by
    exact MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit v index (by omega)
  change MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookDivision.multiplySubtractVAddress v (UInt256.ofNat index)) =
    MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookSingle.arrayAddress v index)
  apply congrArg (MultiLimbDivisionTrace.readWord mem aw)
  apply u256_inj
  rw [haddress]
  exact (MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit v index (by omega)).symm

/-- The full reduced-window bound implies the weak top-limb comparison consumed by the generated
q-hat selector. -/
theorem windowTop_le_of_lt_radix_mul
    (vRest uRest : List UInt256) (vSecond vTop uSecond uLo uHi : UInt256)
    (hlength : uRest.length = vRest.length)
    (hwindow : Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
      UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) :
    uHi.toNat ≤ vTop.toNat := by
  have hright :
      Modexp.wordLimbsToNat
          (((⟨0⟩ : UInt256) :: (vRest ++ [vSecond])) ++ [vTop]) =
        UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
    have hlist :
        (((⟨0⟩ : UInt256) :: (vRest ++ [vSecond])) ++ [vTop]) =
          (⟨0⟩ : UInt256) :: (vRest ++ [vSecond, vTop]) := by
      simp only [List.cons_append, List.append_assoc, List.nil_append]
    rw [hlist, wordLimbsToNat_zero_cons]
  have hlowerLength :
      (uRest ++ [uSecond, uLo]).length =
        ((⟨0⟩ : UInt256) :: (vRest ++ [vSecond])).length := by
    simp only [List.length_append, List.length_cons, List.length_singleton]
    omega
  apply top_toNat_le_of_wordLimbsToNat_lt
    (uRest ++ [uSecond, uLo]) ((⟨0⟩ : UInt256) :: (vRest ++ [vSecond])) uHi vTop
    hlowerLength
  rw [hright]
  simpa only [List.append_assoc] using hwindow

@[simp] theorem windowReadSlice_length
    (mem : ByteArray) (aw u : UInt256) (cursor start count : Nat) :
    (windowReadSlice mem aw u cursor start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [windowReadSlice, ih]

/-- An already-covered array-header load leaves the active-word counter unchanged. -/
theorem arrayAfterHeader_eq_of_active
    (aw array : UInt256)
    (hactive : array.toNat + 32 ≤ 32 * aw.toNat) :
    arrayAfterHeader aw array = aw := by
  unfold arrayAfterHeader MultiLimbSchoolbookSingle.arrayAfterHeader
    MultiLimbSchoolbookShort.arrayAfterHeader MultiLimbOddCompare.afterHeader
    MultiLimbDivisionTrace.readWords1
  rw [machineM_eq_of_access hactive, u256_ofNat_toNat]

/-- An already-covered array-element load leaves the active-word counter unchanged. -/
theorem arrayAfterWord_eq_of_active
    (aw array : UInt256) (index : Nat)
    (hactive : (MultiLimbSchoolbookSingle.arrayAddress array index).toNat + 32 ≤
      32 * aw.toNat) :
    arrayAfterWord aw array index = aw := by
  change (MultiLimbSchoolbookShort.arrayAddress array index).toNat + 32 ≤
    32 * aw.toNat at hactive
  unfold arrayAfterWord MultiLimbSchoolbookSingle.arrayAfterWord
    MultiLimbSchoolbookShort.arrayAfterWord MultiLimbOddCompare.afterLoad
    MultiLimbOddCompare.afterHeader MultiLimbDivisionTrace.readWords1
  rw [machineM_eq_of_access hactive, u256_ofNat_toNat]

/-- Address and active-memory facts shared by every descending quotient cursor. -/
structure ContinuationGeometry
    (aw u v quotient : UInt256) (count uCount quotientCount : Nat) : Prop where
  hcountTwo : 2 ≤ count
  hcountRange : count ≤ 32
  hcountWord : count < UInt256.size
  hquotientCountPos : 0 < quotientCount
  hquotientCountWord : quotientCount < UInt256.size
  huCountEq : uCount = quotientCount + count
  hwindowRange : quotientCount + count ≤ 66
  hawFit : aw.toNat * 32 < UInt256.size
  hvFit : v.toNat + 32 * (count + 1) < UInt256.size
  huFit : u.toNat + 32 * (quotientCount + count) < UInt256.size
  hquotientFit : quotient.toNat + 32 * (quotientCount + 1) < UInt256.size
  hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat
  huTopActive : u.toNat + 32 * (quotientCount + count + 1) ≤ 32 * aw.toNat
  htopBelowV : u.toNat + 32 * (quotientCount + count + 1) ≤ v.toNat
  hquotientPayloadBelowU : quotient.toNat + 32 * (quotientCount + 1) ≤ u.toNat
  hvHeaderAw : arrayAfterHeader aw v = aw
  huHeaderAw : arrayAfterHeader aw u = aw
  hquotientHeaderAw : arrayAfterHeader aw quotient = aw
  hvWordAw : ∀ i, i < count -> arrayAfterWord aw v i = aw
  huWordAw : ∀ i, i < uCount -> arrayAfterWord aw u i = aw
  hquotientWordAw : ∀ i, i < quotientCount -> arrayAfterWord aw quotient i = aw

/-- Headers, divisor contents, and byte extent retained as the concrete memory changes. -/
structure ContinuationMemory
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (vRest : List UInt256) (vSecond vTop : UInt256) (mem : ByteArray) : Prop where
  huHeader : arrayHeader mem aw u = UInt256.ofNat uCount
  hvHeader : arrayHeader mem aw v = UInt256.ofNat count
  hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount
  hvSlice : divisorReadSlice mem aw v 0 count = vRest ++ [vSecond, vTop]
  hvSecondWord : arrayWord mem aw v (count - 2) = vSecond
  hnormalized : UInt256.size ≤ 2 * vTop.toNat
  hvMem : v.toNat + 32 * (count + 1) ≤ mem.size
  huTopMem : u.toNat + 32 * (quotientCount + count + 1) ≤ mem.size

/-- At a concrete cursor, fixed allocator geometry and the reduced-window bound construct the
actual complete estimate/digit execution from the words currently stored in memory. -/
theorem semanticIterationAt_exists
    {mem : ByteArray} {aw : UInt256}
    {cursor count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (memory : ContinuationMemory geometry vRest vSecond vTop mem)
    (hcursorPos : 0 < cursor)
    (hcursor : cursor ≤ quotientCount)
    (hwindow :
      windowNat (windowReadSlice mem aw u cursor 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat count))) <
        UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) :
    ∃ uHi uLo uRest uSecond estimate digit,
      OperandLayout mem aw u uHi uLo cursor count uCount ∧
        SemanticIteration mem aw (cursor - 1) cursor count uCount quotientCount
          uHi vTop uLo u shift ret rem v quotient normalizationMarker
          vRest uRest vSecond uSecond estimate digit := by
  have hcountTwo := geometry.hcountTwo
  have hquotientCountPos := geometry.hquotientCountPos
  have hquotientCountWord := geometry.hquotientCountWord
  have hwindowRangeMax := geometry.hwindowRange
  have huCountEq := geometry.huCountEq
  let uRest := windowReadSlice mem aw u cursor 0 (count - 2)
  let uSecond := arrayWord mem aw u (cursor + count - 3)
  let uLo := arrayWord mem aw u (cursor + count - 2)
  let uHi := arrayWord mem aw u (cursor + count - 1)
  have hwindowRange : cursor + count ≤ 66 := by
    have := hwindowRangeMax
    omega
  have hsumWord : cursor + count < UInt256.size := by
    exact lt_of_le_of_lt hwindowRange (by norm_num [UInt256.size])
  have huFit : u.toNat + 32 * (cursor + count) < UInt256.size := by
    have := geometry.huFit
    omega
  have huSlice : windowReadSlice mem aw u cursor 0 count =
      uRest ++ [uSecond, uLo] := by
    have hsplit := windowReadSlice_lastTwo mem aw u cursor count geometry.hcountTwo
    have hsecond := windowReadWord_eq_arrayWord mem aw u cursor (count - 2) hcursorPos
      (by omega) (by omega) (by have := huFit; omega)
    have hlo := windowReadWord_eq_arrayWord mem aw u cursor (count - 1) hcursorPos
      (by omega) (by omega) (by have := huFit; omega)
    simpa only [uRest, uSecond, uLo, show cursor + (count - 2) - 1 =
      cursor + count - 3 by omega, show cursor + (count - 1) - 1 =
      cursor + count - 2 by omega, hsecond, hlo] using hsplit
  have huTop : MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
        (UInt256.ofNat cursor) (UInt256.ofNat count)) = uHi := by
    simpa only [uHi] using windowReadWord_eq_arrayWord mem aw u cursor count hcursorPos
      hwindowRange hsumWord huFit
  have hcontext : MultiLimbSchoolbookEstimateSemantic.EstimateContext
      vRest uRest vTop vSecond uHi uLo uSecond := by
    have hlength : uRest.length = vRest.length := by
      have hvLength := congrArg List.length memory.hvSlice
      simp only [MultiLimbSchoolbookOuterComplete.divisorReadSlice_length,
        List.length_append, List.length_cons, List.length_nil] at hvLength
      simp only [uRest, windowReadSlice_length]
      omega
    have hsaturated : Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
        UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
      rw [windowNat_eq_append, huSlice, huTop] at hwindow
      simpa only [List.append_assoc] using hwindow
    exact {
      hlength := hlength
      hnormalized := memory.hnormalized
      huHiLe := windowTop_le_of_lt_radix_mul vRest uRest vSecond vTop uSecond uLo uHi
        hlength hsaturated
      hsaturatedNeverLow := hsaturated
    }
  have hlayout : MultiLimbSchoolbookOuterLoopFunction.OperandLayout
      mem aw u uHi uLo cursor count uCount := {
    hcursorPos := hcursorPos
    hcursorWord := lt_of_le_of_lt hcursor hquotientCountWord
    hkEffPos := by omega
    hsumWord := by omega
    huCountWord := by rw [huCountEq]; norm_num [UInt256.size]; omega
    hhiIndex := by rw [huCountEq]; omega
    hloIndex := by rw [huCountEq]; omega
    huHeader := memory.huHeader
    huHeaderAw := geometry.huHeaderAw
    huHiAw := geometry.huWordAw (cursor - 1 + count) (by
      rw [huCountEq]
      omega)
    huLoAw := geometry.huWordAw (cursor - 1 + count - 1) (by
      rw [huCountEq]
      omega)
    huHi := by simpa only [uHi, show cursor - 1 + count = cursor + count - 1 by omega]
    huLo := by simpa only [uLo, show cursor - 1 + count - 1 = cursor + count - 2 by omega]
  }
  have hquotAddress :
      (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat =
        quotient.toNat + 32 * cursor := by
    simpa only [Nat.sub_add_cancel hcursorPos] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit quotient (cursor - 1) (by
        have := geometry.hquotientFit
        omega)
  have hquotBelowU :
      (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤ u.toNat := by
    rw [hquotAddress]
    have := geometry.hquotientPayloadBelowU
    omega
  have hquotWrite :
      (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤ mem.size :=
    le_trans hquotBelowU (le_trans (by omega) memory.huTopMem)
  have hquotActive :
      (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤
        32 * aw.toNat := le_trans hquotBelowU (le_trans (by omega) geometry.huTopActive)
  have huMem : u.toNat + 32 * (cursor + count) ≤ mem.size := by
    have := memory.huTopMem
    omega
  have htopMem : u.toNat + 32 * (cursor + count + 1) ≤ mem.size := by
    have := memory.huTopMem
    omega
  have huActive : u.toNat + 32 * (cursor + count) ≤ 32 * aw.toNat := by
    have := geometry.huTopActive
    omega
  have htopActive : u.toNat + 32 * (cursor + count + 1) ≤ 32 * aw.toNat := by
    have := geometry.huTopActive
    omega
  have htopBelowV : u.toNat + 32 * (cursor + count + 1) ≤ v.toNat := by
    have := geometry.htopBelowV
    omega
  have hquotBelowWindow : ∀ i, i < count ->
      (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤
        (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
          (UInt256.ofNat cursor) (UInt256.ofNat i)).toNat := by
    intro i hi
    have haddress := multiplySubtractUAddress_ofNat_toNat u cursor i hcursorPos (by omega)
      (by omega) (by have := huFit; omega)
    rw [haddress]
    omega
  have hquotBelowTop :
      (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤
        (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
          (UInt256.ofNat cursor) (UInt256.ofNat count)).toNat := by
    rw [multiplySubtractUAddress_ofNat_toNat u cursor count hcursorPos hsumWord
      (by omega) huFit]
    omega
  have hquotBaseBelowUWindow : quotient.toNat + 32 ≤ u.toNat + 32 * cursor := by
    rw [hquotAddress] at hquotBelowU
    omega
  obtain ⟨estimate, digit, hsemantic⟩ := semanticIteration_exists hlayout hcontext
    hcountTwo geometry.hcountRange geometry.hcountWord (by omega) (by rw [huCountEq]; omega)
    memory.hvHeader geometry.hvHeaderAw (geometry.hvWordAw (count - 2) (by omega))
    memory.hvSecondWord (geometry.huWordAw (cursor - 1 + count - 2) (by
      rw [huCountEq]; omega))
    (by simpa only [uSecond, show cursor - 1 + count - 2 = cursor + count - 3 by omega])
    hwindowRange hsumWord geometry.hvFit huFit memory.hvMem huMem geometry.hvActive
    huActive htopMem htopActive htopBelowV
    geometry.hawFit memory.hvSlice huSlice huTop hquotWrite hquotActive
    memory.hquotientHeader geometry.hquotientHeaderAw
    (geometry.hquotientWordAw (cursor - 1) (by omega))
    hquotBaseBelowUWindow hquotBelowWindow hquotBelowTop (by omega)
    (by norm_num [UInt256.size]; omega) hquotientCountWord
  exact ⟨uHi, uLo, uRest, uSecond, estimate, digit, hlayout, hsemantic⟩

/-- A selected iteration preserves the dynamic continuation package. This is the concrete memory
induction step used to invoke the next generated cursor. -/
theorem continuationMemory_after_iteration
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi uLo u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : MultiLimbSchoolbookEstimateSelector.EstimateResult}
    {digit : MultiLimbSchoolbookIterationFunction.DigitResult}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (memory : ContinuationMemory geometry vRest vSecond vTop mem)
    (hsemantic : SemanticIteration mem aw jj cursor count uCount quotientCount
      uHi vTop uLo u shift ret rem v quotient normalizationMarker
      vRest uRest vSecond uSecond estimate digit)
    (hjj : jj < quotientCount) :
    ContinuationMemory geometry vRest vSecond vTop digit.memory := by
  have hresult := semanticIteration_eq_div_mod hsemantic
  have hquotAddress :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat =
        quotient.toNat + 32 * (jj + 1) := by
    exact MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit quotient jj (by
      have := geometry.hquotientFit
      omega)
  have hquotBelowU :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤ u.toNat := by
    rw [hquotAddress]
    have := geometry.hquotientPayloadBelowU
    omega
  have hquotFit : quotient.toNat + 32 * (jj + 2) < UInt256.size := by
    have := geometry.hquotientFit
    omega
  have hvHeader := semanticIteration_preserves_v_header hsemantic
  have huHeader := semanticIteration_preserves_u_header hsemantic hquotBelowU
  have hquotientHeader := semanticIteration_preserves_quotient_header hsemantic hquotFit
  have hvSlice := semanticIteration_preserves_v_slice hsemantic
  have hvSecondWord := semanticIteration_preserves_v_word hsemantic (i := count - 2) (by
    have := geometry.hcountTwo
    omega)
  rw [hresult.1] at hvHeader huHeader hquotientHeader hvSlice hvSecondWord
  exact {
    huHeader := huHeader.trans memory.huHeader
    hvHeader := hvHeader.trans memory.hvHeader
    hquotientHeader := hquotientHeader
    hvSlice := hvSlice.trans memory.hvSlice
    hvSecondWord := hvSecondWord.trans memory.hvSecondWord
    hnormalized := memory.hnormalized
    hvMem := by rw [hresult.2.1]; exact memory.hvMem
    huTopMem := by rw [hresult.2.1]; exact memory.huTopMem
  }

/-- Every selected continuation digit preserves the normalized dividend header when all quotient
destinations lie below it. -/
theorem semanticContinuations_preserves_u_header
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat}
    {mem finalMem : ByteArray} {aw finalAw : UInt256} {steps gas : Nat}
    (h : SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (hquotBelowU : ∀ jj, jj < quotientCount ->
      (arrayAddress quotient jj).toNat + 32 ≤ u.toNat) :
    arrayHeader finalMem finalAw u = arrayHeader mem aw u := by
  induction h with
  | done => rfl
  | step state input inputs mem aw uHi uLo uSecond uRest estimate digit finalMem finalAw
      restSteps restGas
      layout semantic hwindow hindex hsourceBelowU hstoreBelowSource rest ih =>
      exact ih.trans (semanticIteration_preserves_u_header semantic
        (hquotBelowU inputs.length hindex))

/-- The next cursor reads one preserved lower source word followed by the exact reduced remainder
written by the current concrete digit. -/
theorem semanticIteration_nextWindow_eq
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : MultiLimbSchoolbookEstimateSelector.EstimateResult}
    {digit : MultiLimbSchoolbookIterationFunction.DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hcursorTwo : 2 ≤ cursor)
    (hstoreBelowSource :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
        (MultiLimbSchoolbookSingle.arrayAddress u (cursor - 2)).toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords digit.memory digit.activeWords u (cursor - 2) (count + 1)) =
      (arrayWord mem aw u (cursor - 2)).toNat +
        UInt256.size *
          (windowNat (uRest ++ [uSecond, uLo]) uHi %
            Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) := by
  have hactive := (semanticIteration_eq_div_mod h).1
  have hsource := semanticIteration_preserves_u_word_below h
    (sourceIndex := cursor - 2) (by omega) hstoreBelowSource
  change MultiLimbSchoolbookNormalization.arrayWord digit.memory aw u (cursor - 2) =
    MultiLimbSchoolbookNormalization.arrayWord mem aw u (cursor - 2) at hsource
  have hremainder := semanticIteration_resultSegment_eq_mod h hnormalized
  rw [hactive] at hremainder ⊢
  change
    (arrayWord digit.memory aw u (cursor - 2)).toNat +
        UInt256.size * Modexp.wordLimbsToNat
          (arrayReadWords digit.memory aw u (cursor - 2 + 1) count) = _
  have hnext : cursor - 2 + 1 = cursor - 1 := by omega
  rw [hnext, hsource, hremainder]

/-- Every positive descending cursor constructs a complete concrete continuation chain. The input
and reduced-window equalities are arithmetic invariants; all estimate and correction paths, result
memories, step counts, and gas values are selected internally. -/
theorem semanticContinuations_exists
    {mem : ByteArray} {aw : UInt256}
    {cursor count uCount quotientCount input : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (memory : ContinuationMemory geometry vRest vSecond vTop mem)
    (hcursorPos : 0 < cursor)
    (hcursor : cursor ≤ quotientCount)
    (hwindow :
      windowNat (windowReadSlice mem aw u cursor 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat count))) =
        state.remainder * UInt256.size + input)
    (hbound :
      windowNat (windowReadSlice mem aw u cursor 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat cursor) (UInt256.ofNat count))) <
        UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) :
    ∃ inputs finalMem finalAw steps gas,
      inputs.length = cursor ∧
        SemanticContinuations count uCount quotientCount u shift ret rem v quotient vTop
          normalizationMarker vRest vSecond state inputs mem aw finalMem finalAw steps gas := by
  induction cursor using Nat.strong_induction_on generalizing mem state input with
  | h cursor ih =>
      obtain ⟨uHi, uLo, uRest, uSecond, estimate, digit, layout, semantic⟩ :=
        semanticIterationAt_exists (shift := shift) (ret := ret) (rem := rem)
          (normalizationMarker := normalizationMarker) geometry memory hcursorPos hcursor hbound
      let divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])
      let nextState := divisionDigitStep UInt256.size divisor input state
      have hsemanticWindow : windowNat (uRest ++ [uSecond, uLo]) uHi =
          state.remainder * UInt256.size + input := by
        rw [← semantic.huSlice, ← semantic.huTop]
        exact hwindow
      have hnextMemory := continuationMemory_after_iteration geometry memory semantic (by
        omega)
      have hquotAddress :
          (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat =
            quotient.toNat + 32 * cursor := by
        simpa only [Nat.sub_add_cancel hcursorPos] using
          MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit quotient (cursor - 1) (by
            have := geometry.hquotientFit
            omega)
      have hsourceBelowU : ∀ sourceIndex, cursor ≤ sourceIndex ->
          sourceIndex < quotientCount ->
          (MultiLimbSchoolbookSingle.arrayAddress quotient sourceIndex).toNat + 32 ≤
            u.toNat + 32 * cursor := by
        intro sourceIndex hsourceLo hsourceHi
        have hsourceAddress :=
          MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit quotient sourceIndex (by
            have := geometry.hquotientFit
            omega)
        change (MultiLimbOddCompare.elementPtr quotient
          (UInt256.ofNat sourceIndex)).toNat + 32 ≤ u.toNat + 32 * cursor
        rw [hsourceAddress]
        have := geometry.hquotientPayloadBelowU
        omega
      have hstoreBelowSource : ∀ sourceIndex, cursor ≤ sourceIndex ->
          sourceIndex < quotientCount ->
          (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤
            (MultiLimbSchoolbookSingle.arrayAddress quotient sourceIndex).toNat := by
        intro sourceIndex hsourceLo hsourceHi
        have hsourceAddress :=
          MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit quotient sourceIndex (by
            have := geometry.hquotientFit
            omega)
        rw [hquotAddress]
        change quotient.toNat + 32 * cursor + 32 ≤
          (MultiLimbOddCompare.elementPtr quotient (UInt256.ofNat sourceIndex)).toNat
        rw [hsourceAddress]
        omega
      by_cases hlast : cursor = 1
      · subst cursor
        have rest : SemanticContinuations count uCount quotientCount u shift ret rem v
            quotient vTop normalizationMarker vRest vSecond nextState [] digit.memory
            digit.activeWords digit.memory digit.activeWords 0 0 :=
          SemanticContinuations.done nextState digit.memory digit.activeWords
        have hstep := SemanticContinuations.step state input [] mem aw uHi uLo uSecond
          uRest estimate digit digit.memory digit.activeWords 0 0 layout semantic
          hsemanticWindow (by simpa using geometry.hquotientCountPos)
          (by simpa using hsourceBelowU)
          (by simpa using hstoreBelowSource) rest
        exact ⟨[input], digit.memory, digit.activeWords,
          109 + (estimate.steps + digit.steps),
          397 + (estimate.gas + digit.gas), rfl, by simpa only [nextState, divisor] using hstep⟩
      · have hcursorTwo : 2 ≤ cursor := by omega
        let nextInput := (arrayWord mem aw u (cursor - 2)).toNat
        have hquotBelowNextSource :
            (MultiLimbSchoolbookSingle.arrayAddress quotient (cursor - 1)).toNat + 32 ≤
              (MultiLimbSchoolbookSingle.arrayAddress u (cursor - 2)).toNat := by
          have huAddress := MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit u (cursor - 2) (by
            have := geometry.huFit
            omega)
          rw [hquotAddress]
          change quotient.toNat + 32 * cursor + 32 ≤
            (MultiLimbOddCompare.elementPtr u (UInt256.ofNat (cursor - 2))).toNat
          rw [huAddress]
          have := geometry.hquotientPayloadBelowU
          omega
        have hnextArray := semanticIteration_nextWindow_eq semantic memory.hnormalized
          hcursorTwo hquotBelowNextSource
        have hactive := (semanticIteration_eq_div_mod semantic).1
        have hnextSum : cursor - 1 + count < UInt256.size := by
          have hle : cursor - 1 + count ≤ 66 := by
            have := geometry.hwindowRange
            omega
          exact lt_of_le_of_lt hle (by norm_num [UInt256.size])
        have hnextModel := windowModel_eq_arraySegment digit.memory digit.activeWords u
          (cursor - 1) count (by omega) (by
            have := geometry.hwindowRange
            omega) hnextSum (by
            have := geometry.huFit
            omega)
        have hnextIndex : cursor - 1 - 1 = cursor - 2 := by omega
        rw [hnextIndex] at hnextModel
        have hnextWindow :
            windowNat (windowReadSlice digit.memory aw u (cursor - 1) 0 count)
                (MultiLimbDivisionTrace.readWord digit.memory aw
                  (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
                    (UInt256.ofNat (cursor - 1)) (UInt256.ofNat count))) =
              nextState.remainder * UInt256.size + nextInput := by
          rw [← hactive]
          rw [← hnextModel]
          rw [hnextArray]
          rw [hsemanticWindow]
          simp only [nextState, divisor, divisionDigitStep, nextInput]
          ring
        have hdivisorPos : 0 < divisor :=
          normalizedDivisor_positive vRest vSecond vTop memory.hnormalized
        have hnextRemainder : nextState.remainder < divisor := by
          exact divisionDigitStep_remainder_lt UInt256.size divisor input state hdivisorPos
        have hnextBound :
            windowNat (windowReadSlice digit.memory aw u (cursor - 1) 0 count)
                (MultiLimbDivisionTrace.readWord digit.memory aw
                  (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
                    (UInt256.ofNat (cursor - 1)) (UInt256.ofNat count))) <
              UInt256.size * divisor := by
          rw [hnextWindow]
          have hinputBound : nextInput < UInt256.size := by
            exact (arrayWord mem aw u (cursor - 2)).val.isLt
          simpa only [Nat.add_comm, Nat.mul_comm] using
            nextWindow_lt_radix_mul nextInput nextState.remainder divisor hinputBound
              hdivisorPos hnextRemainder
        obtain ⟨inputs, finalMem, finalAw, restSteps, restGas, hinputsLength, rest⟩ :=
          ih (cursor - 1) (by omega) hnextMemory (by omega) (by omega) hnextWindow
            (by simpa only [divisor] using hnextBound)
        have hcursorEq : inputs.length + 1 = cursor := by omega
        have hcursorSucc : cursor - 1 + 1 = cursor := by omega
        have layout' : OperandLayout mem aw u uHi uLo (inputs.length + 1) count uCount := by
          simpa only [hcursorEq] using layout
        have semantic' : SemanticIteration mem aw inputs.length (inputs.length + 1) count
            uCount quotientCount uHi vTop uLo u shift ret rem v quotient
            normalizationMarker vRest uRest vSecond uSecond estimate digit := by
          simpa only [hinputsLength, hcursorEq, Nat.sub_add_cancel hcursorPos] using semantic
        have rest' : SemanticContinuations count uCount quotientCount u shift ret rem v
            quotient vTop normalizationMarker vRest vSecond
            (divisionDigitStep UInt256.size
              (Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) input state)
            inputs digit.memory digit.activeWords finalMem finalAw restSteps restGas := by
          simpa only [nextState, divisor, hactive] using rest
        have hstep := SemanticContinuations.step state input inputs mem aw uHi uLo uSecond
          uRest estimate digit finalMem finalAw restSteps restGas layout' semantic'
          hsemanticWindow (by omega) (by simpa only [hcursorEq] using hsourceBelowU)
          (by simpa only [hinputsLength, hcursorSucc] using hstoreBelowSource) rest'
        exact ⟨input :: inputs, finalMem, finalAw,
          109 + (estimate.steps + digit.steps) + restSteps,
          397 + (estimate.gas + digit.gas) + restGas,
          by simp only [List.length_cons, hinputsLength, hcursorSucc], hstep⟩

end Modexp.MultiLimbSchoolbookContinuationExecutable
