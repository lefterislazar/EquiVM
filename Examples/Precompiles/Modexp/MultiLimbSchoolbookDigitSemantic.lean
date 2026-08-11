import Examples.Precompiles.Modexp.MultiLimbSchoolbookIterationSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookEstimateSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookOuterSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookIterationFunction

/-!
# Pure semantics of one executed schoolbook quotient digit

This layer reads the remainder window from the concrete direct/corrected memory and relates it to
the accepted Algorithm D window. The selector bounds then make that pair ordinary natural-number
division and remainder. No execution result is supplied as a semantic callback.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookDigitSemantic

open MultiLimbSchoolbookDivisionSemantic
open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookOuterSemantic
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookEstimateSemantic
open MultiLimbSchoolbookSingle
open MultiLimbSchoolbookIterationFunction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Quotient digit and current remainder window observed immediately before quotient storage. -/
def concreteCoreResult
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat) : Nat × Nat :=
  let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  let topAddress := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  if top.negative = ⟨0⟩ then
    (qHat.toNat, windowNat (windowReadSlice top.memory aw u current 0 count)
      (MultiLimbDivisionTrace.readWord top.memory top.activeWords topAddress))
  else
    let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
      (UInt256.ofNat current) qHat count
    (qHat.toNat - 1, windowNat (windowReadSlice corrected.memory aw u current 0 count)
      (MultiLimbDivisionTrace.readWord corrected.memory corrected.activeWords topAddress))

/-- The concrete direct/correction branch computes exactly the pure accepted-window pair. -/
theorem concreteCoreResult_eq_acceptedWindowResult
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    concreteCoreResult mem aw v u qHat current count =
      acceptedWindowResult qHat
        (windowReadSlice mem aw u current 0 count)
        (divisorReadSlice mem aw v 0 count)
        (MultiLimbDivisionTrace.readWord mem aw
          (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count))) := by
  let uLower := windowReadSlice mem aw u current 0 count
  let vDigits := divisorReadSlice mem aw v 0 count
  let topAddress := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let uTop := MultiLimbDivisionTrace.readWord mem aw topAddress
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  have htop := topResult_eq_knuthSubtractWindow mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have hnegative : subtracted.negative = top.negative := by
    simpa only [subtracted, uLower, vDigits, uTop, top, topAddress] using htop.2.2.1
  by_cases hzero : top.negative = ⟨0⟩
  · have hpureZero : subtracted.negative = ⟨0⟩ := hnegative.trans hzero
    have hlower : subtracted.lower = windowReadSlice top.memory aw u current 0 count := by
      simpa only [subtracted, uLower, vDigits, uTop, top, topAddress] using htop.1
    have htopWord : subtracted.top =
        MultiLimbDivisionTrace.readWord top.memory top.activeWords topAddress := by
      simpa only [subtracted, uLower, vDigits, uTop, top, topAddress] using htop.2.1
    simp only [concreteCoreResult, top, hzero, if_pos, acceptedWindowResult]
    rw [← hlower, ← htopWord]
    rw [if_pos (by
      simpa only [subtracted, uLower, vDigits, uTop, topAddress] using hpureZero)]
  · have hpureNonzero : subtracted.negative ≠ ⟨0⟩ := by
      intro hpure
      exact hzero (hnegative.symm.trans hpure)
    have hcorrected := correctionTop_eq_knuthAddBack mem aw v u qHat current count
      hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
      htopMem htopActive htopBelowV hawFit
    let correctedPure := knuthAddBack subtracted.lower vDigits subtracted.top
    let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
      (UInt256.ofNat current) qHat count
    have hlower : correctedPure.lower =
        windowReadSlice corrected.memory aw u current 0 count := by
      simpa only [correctedPure, subtracted, uLower, vDigits, uTop, corrected,
        topAddress] using hcorrected.1
    have htopWord : correctedPure.top =
        MultiLimbDivisionTrace.readWord corrected.memory corrected.activeWords topAddress := by
      simpa only [correctedPure, subtracted, uLower, vDigits, uTop, corrected,
        topAddress] using hcorrected.2.1
    simp only [concreteCoreResult, top, hzero, acceptedWindowResult]
    rw [← hlower, ← htopWord]
    simp only [if_false]
    rw [if_neg (by
      simpa only [subtracted, uLower, vDigits, uTop, topAddress] using hpureNonzero)]

/-- Normalization makes the represented divisor strictly positive. -/
theorem normalizedDivisor_positive
    (vRest : List UInt256) (vSecond vTop : UInt256)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    0 < Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  have hvTop : 0 < vTop.toNat := by
    norm_num [UInt256.size] at hnormalized
    omega
  rw [show vRest ++ [vSecond, vTop] = (vRest ++ [vSecond]) ++ [vTop] by simp,
    Modexp.wordLimbsToNat_append]
  have htopTerm :
      0 < UInt256.size ^ (vRest ++ [vSecond]).length * vTop.toNat :=
    Nat.mul_pos (pow_pos (by norm_num [UInt256.size]) _) hvTop
  simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
  omega

theorem windowNat_eq_append (lower : List UInt256) (top : UInt256) :
    windowNat lower top = Modexp.wordLimbsToNat (lower ++ [top]) := by
  rw [Modexp.wordLimbsToNat_append]
  simp only [windowNat, Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]

/-- Solidity's checked correction word is ordinary natural predecessor on the proved nonzero
branch. -/
theorem correctedQHat_toNat (qHat : UInt256) (hnonzero : qHat ≠ ⟨0⟩) :
    (MultiLimbSchoolbookDigitFunction.correctedQHat qHat).toNat = qHat.toNat - 1 := by
  have hpos : 0 < qHat.toNat := by
    by_contra hnot
    have hz : qHat.toNat = 0 := by omega
    apply hnonzero
    apply u256_inj
    simpa using hz
  have hmax : ((⟨0⟩ : UInt256).lnot).toNat = UInt256.size - 1 := by
    native_decide
  unfold MultiLimbSchoolbookDigitFunction.correctedQHat
  rw [uadd_toNat, hmax]
  have hq : qHat.toNat < UInt256.size := qHat.val.isLt
  have hge : UInt256.size ≤ qHat.toNat + (UInt256.size - 1) := by omega
  rw [Nat.mod_eq_sub_mod hge]
  have hsub : qHat.toNat + (UInt256.size - 1) - UInt256.size = qHat.toNat - 1 := by
    omega
  rw [hsub, Nat.mod_eq_of_lt (by omega)]

/-- An in-bounds quotient store below the current window records its word and preserves the
already computed concrete remainder window. -/
theorem storeQuotient_observation
    (mem : ByteArray) (aw quotient u value topAddress : UInt256)
    (index current count : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : (arrayAddress quotient index).toNat + 32 ≤ mem.size)
    (hactive : (arrayAddress quotient index).toNat + 32 ≤ 32 * aw.toNat)
    (hbelowWindow : ∀ i, i < count ->
      (arrayAddress quotient index).toNat + 32 ≤
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)).toNat)
    (hbelowTop : (arrayAddress quotient index).toNat + 32 ≤ topAddress.toNat) :
    let stored := storeQuotient mem quotient index value
    arrayWord stored aw quotient index = value ∧
      windowNat (windowReadSlice stored aw u current 0 count)
          (MultiLimbDivisionTrace.readWord stored aw topAddress) =
        windowNat (windowReadSlice mem aw u current 0 count)
          (MultiLimbDivisionTrace.readWord mem aw topAddress) := by
  let stored := storeQuotient mem quotient index value
  have hwindow := windowReadSlice_wordWrite_below mem aw u value current 0 count
    (arrayAddress quotient index).toNat hwrite (by
      intro i hiLo hiHi
      exact hbelowWindow i (by omega))
  have htop := readWord_wordWrite_below mem aw topAddress value
    (arrayAddress quotient index).toNat hwrite hbelowTop
  have hself := arrayWord_storeQuotient_self mem aw quotient value index hawFit hwrite hactive
  have hremainder :
      windowNat
          (windowReadSlice (value.toByteArray.write 0 mem
            (arrayAddress quotient index).toNat 32) aw u current 0 count)
          (MultiLimbDivisionTrace.readWord
            (value.toByteArray.write 0 mem (arrayAddress quotient index).toNat 32)
            aw topAddress) =
        windowNat (windowReadSlice mem aw u current 0 count)
          (MultiLimbDivisionTrace.readWord mem aw topAddress) := by
    rw [hwindow, htop]
  simpa only [stored, storeQuotient] using ⟨hself, hremainder⟩

/-- A selector certificate plus concrete slice identification makes the executed digit ordinary
natural division/remainder of the current window. -/
theorem concreteCoreResult_eq_div_mod
    {mem : ByteArray} {aw v u qHat : UInt256} {current count : Nat}
    {vRest uRest : List UInt256} {vTop vSecond uHi uLo uSecond : UInt256}
    (hcore : concreteCoreResult mem aw v u qHat current count =
      acceptedWindowResult qHat (uRest ++ [uSecond, uLo])
        (vRest ++ [vSecond, vTop]) uHi)
    (hcontext : EstimateContext vRest uRest vTop vSecond uHi uLo uSecond)
    (hnotLow :
      windowNat (uRest ++ [uSecond, uLo]) uHi <
        (qHat.toNat + 1) * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]))
    (hatMostOne :
      qHat.toNat * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ≤
        windowNat (uRest ++ [uSecond, uLo]) uHi +
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])) :
    (concreteCoreResult mem aw v u qHat current count).1 =
        windowNat (uRest ++ [uSecond, uLo]) uHi /
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ∧
      (concreteCoreResult mem aw v u qHat current count).2 =
        windowNat (uRest ++ [uSecond, uLo]) uHi %
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  have hlength : (uRest ++ [uSecond, uLo]).length =
      (vRest ++ [vSecond, vTop]).length := by
    simpa only [List.length_append, List.length_cons, List.length_nil] using
      congrArg (fun n => n + 2) hcontext.hlength
  have hdivisor := normalizedDivisor_positive vRest vSecond vTop hcontext.hnormalized
  have hresult := knuthAcceptedWindow_eq_div_mod qHat (uRest ++ [uSecond, uLo])
    (vRest ++ [vSecond, vTop]) uHi hlength hdivisor hnotLow hatMostOne
  rw [hcore]
  exact hresult

/-- End-to-end local semantic theorem: any of the seven executed estimate routes, followed by the
executed direct/corrected arithmetic core, computes the unique natural quotient digit and
remainder for the concrete window. -/
theorem validEstimateConcreteCore_eq_div_mod
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount : Nat}
    {u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256}
    {vTop vSecond uHi uLo uSecond : UInt256}
    (estimate : EstimateResult)
    (context : EstimateContext vRest uRest vTop vSecond uHi uLo uSecond)
    (hvSecondWord : MultiLimbSchoolbookNormalization.arrayWord mem aw v (count - 2) =
      vSecond)
    (huSecondWord : MultiLimbSchoolbookNormalization.arrayWord mem aw u (jj + count - 2) =
      uSecond)
    (hvalid : ValidEstimate mem aw jj cursor count uCount vTop uLo u shift ret rem v
      quotient normalizationMarker uHi estimate)
    (hcurrent : 0 < cursor)
    (hrange : count ≤ 32)
    (hwindowRange : cursor + count ≤ 66)
    (hsumWord : cursor + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (cursor + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (cursor + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (cursor + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (cursor + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (cursor + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (cursor + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hvSlice : divisorReadSlice mem aw v 0 count = vRest ++ [vSecond, vTop])
    (huSlice : windowReadSlice mem aw u cursor 0 count = uRest ++ [uSecond, uLo])
    (huTop : MultiLimbDivisionTrace.readWord mem aw
      (multiplySubtractUAddress u (UInt256.ofNat cursor) (UInt256.ofNat count)) = uHi) :
    (concreteCoreResult mem aw v u estimate.qHat cursor count).1 =
        windowNat (uRest ++ [uSecond, uLo]) uHi /
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ∧
      (concreteCoreResult mem aw v u estimate.qHat cursor count).2 =
        windowNat (uRest ++ [uSecond, uLo]) uHi %
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  have hcore := concreteCoreResult_eq_acceptedWindowResult mem aw v u estimate.qHat
    cursor count hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem
    hvActive huActive htopMem htopActive htopBelowV hawFit
  rw [huSlice, hvSlice, huTop] at hcore
  have hbounds := validEstimateBounds vRest uRest vTop vSecond uHi uLo uSecond
    estimate context hvSecondWord huSecondWord hvalid
  have hwindow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) =
        windowNat (uRest ++ [uSecond, uLo]) uHi := by
    rw [windowNat_eq_append]
    congr 1
    simp
  rw [hwindow] at hbounds
  exact concreteCoreResult_eq_div_mod hcore context hbounds.1 hbounds.2

/-- Both execution constructors store the quotient digit represented by `concreteCoreResult` and
preserve its remainder window. -/
theorem validDigit_observation
    {mem : ByteArray} {aw v u qHat quotient : UInt256}
    {current count jj quotientCount : Nat}
    {shift ret rem vTop normalizationMarker : UInt256}
    {result : DigitResult}
    (hvalid : ValidDigit mem aw count jj quotientCount v u (UInt256.ofNat current) qHat
      shift ret rem quotient vTop normalizationMarker result)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hquotWrite : (arrayAddress quotient jj).toNat + 32 ≤ mem.size)
    (hquotActive : (arrayAddress quotient jj).toNat + 32 ≤ 32 * aw.toNat)
    (hquotBelowWindow : ∀ i, i < count ->
      (arrayAddress quotient jj).toNat + 32 ≤
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)).toNat)
    (hquotBelowTop : (arrayAddress quotient jj).toNat + 32 ≤
      (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)).toNat) :
    let topAddress := multiplySubtractUAddress u (UInt256.ofNat current)
      (UInt256.ofNat count)
    result.activeWords = aw ∧ result.memory.size = mem.size ∧
      (arrayWord result.memory aw quotient jj).toNat =
        (concreteCoreResult mem aw v u qHat current count).1 ∧
      windowNat (windowReadSlice result.memory aw u current 0 count)
          (MultiLimbDivisionTrace.readWord result.memory aw topAddress) =
        (concreteCoreResult mem aw v u qHat current count).2 := by
  let topAddress := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  cases hvalid with
  | direct hnonnegative hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
        (UInt256.ofNat current) qHat count
      have htop := topResult_eq_knuthSubtractWindow mem aw v u qHat current count hcurrent
        hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
        htopActive htopBelowV hawFit
      have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have htopActiveEq : top.activeWords = aw := by simpa only [top] using htop.2.2.2
      have htopSize : top.memory.size = mem.size := by simpa only [top] using hphase.2
      have hobs := storeQuotient_observation top.memory aw quotient u qHat topAddress jj
        current count hawFit (by rw [htopSize]; exact hquotWrite) hquotActive
        hquotBelowWindow hquotBelowTop
      have hcore : concreteCoreResult mem aw v u qHat current count =
          (qHat.toNat, windowNat (windowReadSlice top.memory aw u current 0 count)
            (MultiLimbDivisionTrace.readWord top.memory aw topAddress)) := by
        simp only [concreteCoreResult, top, hnonnegative, if_pos]
        rw [htopActiveEq]
      have hstoredSize := storeQuotient_size_eq top.memory quotient jj qHat
        (by rw [htopSize]; exact hquotWrite)
      dsimp only [topAddress]
      refine ⟨htopActiveEq, ?_, ?_, ?_⟩
      · simpa only [MultiLimbSchoolbookDigitFunction.directMemory, top] using
          hstoredSize.trans htopSize
      · rw [hcore]
        simpa only [MultiLimbSchoolbookDigitFunction.directMemory, top] using
          congrArg UInt256.toNat hobs.1
      · rw [hcore]
        simpa only [MultiLimbSchoolbookDigitFunction.directMemory, top] using hobs.2
  | corrected hnegative hqHat hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
        (UInt256.ofNat current) qHat count
      have hcorrected := correctionTop_eq_knuthAddBack mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have hcorrectedActive : corrected.activeWords = aw := by
        simpa only [corrected] using hcorrected.2.2.1
      have hcorrectedSize : corrected.memory.size = mem.size := by
        simpa only [corrected] using hcorrected.2.2.2
      let storedQHat := MultiLimbSchoolbookDigitFunction.correctedQHat qHat
      have hobs := storeQuotient_observation corrected.memory aw quotient u storedQHat
        topAddress jj current count hawFit (by rw [hcorrectedSize]; exact hquotWrite)
        hquotActive hquotBelowWindow hquotBelowTop
      have hstoredQHat : storedQHat.toNat = qHat.toNat - 1 := by
        exact correctedQHat_toNat qHat hqHat
      have hcore : concreteCoreResult mem aw v u qHat current count =
          (qHat.toNat - 1,
            windowNat (windowReadSlice corrected.memory aw u current 0 count)
              (MultiLimbDivisionTrace.readWord corrected.memory aw topAddress)) := by
        simp [concreteCoreResult, hnegative, corrected, hcorrectedActive]
        rfl
      have hstoredSize := storeQuotient_size_eq corrected.memory quotient jj storedQHat
        (by rw [hcorrectedSize]; exact hquotWrite)
      dsimp only [topAddress]
      refine ⟨hcorrectedActive, ?_, ?_, ?_⟩
      · simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, corrected,
          storedQHat] using hstoredSize.trans hcorrectedSize
      · rw [hcore]
        simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, corrected,
          storedQHat, hstoredQHat] using congrArg UInt256.toNat hobs.1
      · rw [hcore]
        simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, corrected,
          storedQHat] using hobs.2

/-- A complete digit preserves a previously stored quotient word below `u` when the current
quotient destination is strictly below that word. -/
theorem validDigit_read_frame
    {mem : ByteArray} {aw v u qHat quotient : UInt256}
    {current count jj quotientCount read : Nat}
    {shift ret rem vTop normalizationMarker : UInt256}
    {result : DigitResult}
    (hvalid : ValidDigit mem aw count jj quotientCount v u (UInt256.ofNat current) qHat
      shift ret rem quotient vTop normalizationMarker result)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hreadBelowU : read + 32 ≤ u.toNat + 32 * current)
    (hquotWrite : (arrayAddress quotient jj).toNat + 32 ≤ mem.size)
    (hstoreBelowRead : (arrayAddress quotient jj).toNat + 32 ≤ read) :
    result.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  cases hvalid with
  | direct hnonnegative hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
        (UInt256.ofNat current) qHat count
      have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have htopSize : top.memory.size = mem.size := by simpa only [top] using hphase.2
      have htopFrame := topResult_read_below_eq mem aw v u qHat current count read
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem hreadBelowU
      have hstoreFrame := write32_read_above_padded qHat.toByteArray top.memory
        (arrayAddress quotient jj).toNat read (by rw [toByteArray_size])
        (by rw [htopSize]; exact hquotWrite) hstoreBelowRead
      calc
        (MultiLimbSchoolbookDigitFunction.directMemory mem aw v u (UInt256.ofNat current)
            qHat quotient count jj).readWithPadding read 32 =
            top.memory.readWithPadding read 32 := by
          simpa only [MultiLimbSchoolbookDigitFunction.directMemory, storeQuotient, top] using
            hstoreFrame
        _ = mem.readWithPadding read 32 := by simpa only [top] using htopFrame
  | corrected hnegative hqHat hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
        (UInt256.ofNat current) qHat count
      let storedQHat := MultiLimbSchoolbookDigitFunction.correctedQHat qHat
      have hcorrected := correctionTop_eq_knuthAddBack mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have hcorrectedSize : corrected.memory.size = mem.size := by
        simpa only [corrected] using hcorrected.2.2.2
      have hcorrectedFrame := correctionTop_read_below_eq mem aw v u qHat current count read
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit hreadBelowU
      have hstoreFrame := write32_read_above_padded storedQHat.toByteArray corrected.memory
        (arrayAddress quotient jj).toNat read (by rw [toByteArray_size])
        (by rw [hcorrectedSize]; exact hquotWrite) hstoreBelowRead
      calc
        (MultiLimbSchoolbookDigitFunction.correctedMemory mem aw v u
            (UInt256.ofNat current) qHat quotient count jj).readWithPadding read 32 =
            corrected.memory.readWithPadding read 32 := by
          simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, storeQuotient,
            corrected, storedQHat] using hstoreFrame
        _ = mem.readWithPadding read 32 := by simpa only [corrected] using hcorrectedFrame

/-- A complete digit preserves a word below both the mutable `u` window and the quotient store.
This is the allocator ordering used by the remainder header. -/
theorem validDigit_read_below_frame
    {mem : ByteArray} {aw v u qHat quotient : UInt256}
    {current count jj quotientCount read : Nat}
    {shift ret rem vTop normalizationMarker : UInt256}
    {result : DigitResult}
    (hvalid : ValidDigit mem aw count jj quotientCount v u (UInt256.ofNat current) qHat
      shift ret rem quotient vTop normalizationMarker result)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hreadBelowU : read + 32 ≤ u.toNat + 32 * current)
    (hquotWrite : (arrayAddress quotient jj).toNat + 32 ≤ mem.size)
    (hreadBelowStore : read + 32 ≤ (arrayAddress quotient jj).toNat) :
    result.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  cases hvalid with
  | direct hnonnegative hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
        (UInt256.ofNat current) qHat count
      have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have htopSize : top.memory.size = mem.size := by simpa only [top] using hphase.2
      have htopFrame := topResult_read_below_eq mem aw v u qHat current count read
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem hreadBelowU
      have hstoreFrame := write32_read_below qHat.toByteArray top.memory
        (arrayAddress quotient jj).toNat read (by rw [toByteArray_size])
        (by rw [htopSize]; omega) hreadBelowStore
      calc
        (MultiLimbSchoolbookDigitFunction.directMemory mem aw v u (UInt256.ofNat current)
            qHat quotient count jj).readWithPadding read 32 =
            top.memory.readWithPadding read 32 := by
          simpa only [MultiLimbSchoolbookDigitFunction.directMemory, storeQuotient, top] using
            hstoreFrame
        _ = mem.readWithPadding read 32 := by simpa only [top] using htopFrame
  | corrected hnegative hqHat hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
        (UInt256.ofNat current) qHat count
      let storedQHat := MultiLimbSchoolbookDigitFunction.correctedQHat qHat
      have hcorrected := correctionTop_eq_knuthAddBack mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have hcorrectedSize : corrected.memory.size = mem.size := by
        simpa only [corrected] using hcorrected.2.2.2
      have hcorrectedFrame := correctionTop_read_below_eq mem aw v u qHat current count read
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit hreadBelowU
      have hstoreFrame := write32_read_below storedQHat.toByteArray corrected.memory
        (arrayAddress quotient jj).toNat read (by rw [toByteArray_size])
        (by rw [hcorrectedSize]; omega) hreadBelowStore
      calc
        (MultiLimbSchoolbookDigitFunction.correctedMemory mem aw v u
            (UInt256.ofNat current) qHat quotient count jj).readWithPadding read 32 =
            corrected.memory.readWithPadding read 32 := by
          simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, storeQuotient,
            corrected, storedQHat] using hstoreFrame
        _ = mem.readWithPadding read 32 := by simpa only [corrected] using hcorrectedFrame

/-- A complete digit also preserves an arbitrary word above the current `u` window when the
quotient store lies below that word. This is used to retain the normalized `v` header between
outer-loop iterations. -/
theorem validDigit_read_above_frame
    {mem : ByteArray} {aw v u qHat quotient : UInt256}
    {current count jj quotientCount read : Nat}
    {shift ret rem vTop normalizationMarker : UInt256}
    {result : DigitResult}
    (hvalid : ValidDigit mem aw count jj quotientCount v u (UInt256.ofNat current) qHat
      shift ret rem quotient vTop normalizationMarker result)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hreadAbove : u.toNat + 32 * (current + count + 1) ≤ read)
    (hquotWrite : (arrayAddress quotient jj).toNat + 32 ≤ mem.size)
    (hstoreBelowRead : (arrayAddress quotient jj).toNat + 32 ≤ read) :
    result.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  cases hvalid with
  | direct hnonnegative hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
        (UInt256.ofNat current) qHat count
      have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have htopSize : top.memory.size = mem.size := by simpa only [top] using hphase.2
      have htopFrame := topResult_read_above_eq mem aw v u qHat current count read
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem hreadAbove
      have hstoreFrame := write32_read_above_padded qHat.toByteArray top.memory
        (arrayAddress quotient jj).toNat read (by rw [toByteArray_size])
        (by rw [htopSize]; exact hquotWrite) hstoreBelowRead
      calc
        (MultiLimbSchoolbookDigitFunction.directMemory mem aw v u (UInt256.ofNat current)
            qHat quotient count jj).readWithPadding read 32 =
            top.memory.readWithPadding read 32 := by
          simpa only [MultiLimbSchoolbookDigitFunction.directMemory, storeQuotient, top] using
            hstoreFrame
        _ = mem.readWithPadding read 32 := by simpa only [top] using htopFrame
  | corrected hnegative hqHat hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
        (UInt256.ofNat current) qHat count
      let storedQHat := MultiLimbSchoolbookDigitFunction.correctedQHat qHat
      have hcorrected := correctionTop_eq_knuthAddBack mem aw v u qHat current count
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit
      have hcorrectedSize : corrected.memory.size = mem.size := by
        simpa only [corrected] using hcorrected.2.2.2
      have hcorrectedFrame := correctionTop_read_above_eq mem aw v u qHat current count read
        hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
        htopMem htopActive htopBelowV hawFit hreadAbove
      have hstoreFrame := write32_read_above_padded storedQHat.toByteArray corrected.memory
        (arrayAddress quotient jj).toNat read (by rw [toByteArray_size])
        (by rw [hcorrectedSize]; exact hquotWrite) hstoreBelowRead
      calc
        (MultiLimbSchoolbookDigitFunction.correctedMemory mem aw v u
            (UInt256.ofNat current) qHat quotient count jj).readWithPadding read 32 =
            corrected.memory.readWithPadding read 32 := by
          simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, storeQuotient,
            corrected, storedQHat] using hstoreFrame
        _ = mem.readWithPadding read 32 := by simpa only [corrected] using hcorrectedFrame

end Modexp.MultiLimbSchoolbookDigitSemantic
