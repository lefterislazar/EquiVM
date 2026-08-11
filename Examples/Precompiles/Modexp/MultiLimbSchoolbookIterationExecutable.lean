import Examples.Precompiles.Modexp.MultiLimbSchoolbookDigitExecutable
import Examples.Precompiles.Modexp.MultiLimbSchoolbookOuterLoopFunction

/-!
# Constructive complete schoolbook iteration

This module combines the executable estimate and digit selectors into the semantic certificate for
one concrete quotient cursor. All premises are memory geometry or the long-division invariant;
neither the q-hat path nor the accepted result memory is supplied by the caller.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookIterationExecutable

open MultiLimbSchoolbookDigitExecutable
open MultiLimbSchoolbookDigitSemantic
open MultiLimbSchoolbookEstimateExecutable
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookEstimateSemantic
open MultiLimbSchoolbookIterationComplete
open MultiLimbSchoolbookIterationFunction
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookOuterLoopFunction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Concrete layout and the reduced-window invariant construct one complete semantic iteration,
including its actual estimate route, direct/corrected digit memory, and exact gas. -/
theorem semanticIteration_exists
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    (layout : OperandLayout mem aw u uHi uLo cursor count uCount)
    (context : EstimateContext vRest uRest vTop vSecond uHi uLo uSecond)
    (hcountTwo : 2 ≤ count)
    (hcountRange : count ≤ 32)
    (hcountWord : count < UInt256.size)
    (hindexWord : jj + count < UInt256.size)
    (huIndex : jj + count - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat count)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (count - 2) = aw)
    (hvSecondWord : arrayWord mem aw v (count - 2) = vSecond)
    (huSecondAw : arrayAfterWord aw u (jj + count - 2) = aw)
    (huSecondWord : arrayWord mem aw u (jj + count - 2) = uSecond)
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
      (MultiLimbSchoolbookDivision.multiplySubtractUAddress u (UInt256.ofNat cursor)
        (UInt256.ofNat count)) = uHi)
    (hquotWrite : (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤ mem.size)
    (hquotActive : (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
      32 * aw.toNat)
    (hquotHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hquotHeaderAw : arrayAfterHeader aw quotient = aw)
    (hquotElementAw : arrayAfterWord aw quotient jj = aw)
    (hquotBelowU : quotient.toNat + 32 ≤ u.toNat + 32 * cursor)
    (hquotBelowWindow : ∀ i, i < count ->
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
        (MultiLimbSchoolbookDivision.multiplySubtractUAddress u (UInt256.ofNat cursor)
          (UInt256.ofNat i)).toNat)
    (hquotBelowTop : (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
      (MultiLimbSchoolbookDivision.multiplySubtractUAddress u (UInt256.ofNat cursor)
        (UInt256.ofNat count)).toNat)
    (hjj : jj < quotientCount)
    (hjjWord : jj < UInt256.size)
    (hquotientCountWord : quotientCount < UInt256.size) :
    ∃ estimate digit,
      SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
        shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond
        estimate digit := by
  let refinementLayout : RefinementLayout mem aw v u vSecond uSecond jj count uCount :=
    {
      hkEffTwo := hcountTwo
      hkEffWord := hcountWord
      hindexWord := hindexWord
      huCountWord := layout.huCountWord
      huIndex := huIndex
      hvHeader := hvHeader
      hvHeaderAw := hvHeaderAw
      hvSecondAw := hvSecondAw
      hvSecond := hvSecondWord
      huHeader := layout.huHeader
      huHeaderAw := layout.huHeaderAw
      huSecondAw := huSecondAw
      huSecond := huSecondWord
    }
  obtain ⟨estimate, hestimate⟩ := validEstimate_exists uHi context.hnormalized refinementLayout
  obtain ⟨digit, hdigit⟩ := validDigit_exists layout.hcursorPos hcountRange hwindowRange
    hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem htopActive htopBelowV hawFit
    hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw hquotElementAw hquotBelowU
  exact ⟨estimate, digit, {
    context := context
    hvSecondWord := hvSecondWord
    huSecondWord := huSecondWord
    hestimate := hestimate
    hdigit := hdigit
    hcurrent := layout.hcursorPos
    hrange := hcountRange
    hwindowRange := hwindowRange
    hsumWord := hsumWord
    hvFit := hvFit
    huFit := huFit
    hvMem := hvMem
    huMem := huMem
    hvActive := hvActive
    huActive := huActive
    htopMem := htopMem
    htopActive := htopActive
    htopBelowV := htopBelowV
    hawFit := hawFit
    hvSlice := hvSlice
    huSlice := huSlice
    huTop := huTop
    hquotWrite := hquotWrite
    hquotActive := hquotActive
    hquotBelowWindow := hquotBelowWindow
    hquotBelowTop := hquotBelowTop
  }⟩

/-- One selected digit leaves the normalized divisor header intact because every arithmetic write
ends below `v` and the quotient write is lower still. -/
theorem semanticIteration_preserves_v_header
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit) :
    arrayHeader digit.memory digit.activeWords v = arrayHeader mem aw v := by
  have hresult := semanticIteration_eq_div_mod h
  have hwindowRange := h.hwindowRange
  have htopBelowV := h.htopBelowV
  have htopAddress := multiplySubtractUAddress_ofNat_toNat u cursor count h.hcurrent
    h.hsumWord (by omega) h.huFit
  have hstoreBelowV :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤ v.toNat := by
    exact le_trans h.hquotBelowTop (by rw [htopAddress]; omega)
  have hread := validDigit_read_above_frame h.hdigit h.hcurrent h.hrange h.hwindowRange
    h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem
    h.htopActive h.htopBelowV h.hawFit h.htopBelowV h.hquotWrite hstoreBelowV
  unfold arrayHeader MultiLimbSchoolbookSingle.arrayHeader
    MultiLimbSchoolbookShort.arrayHeader MultiLimbOddCompare.headerWord
  rw [hresult.1]
  exact readWord_eq_of_size_read_eq digit.memory mem aw v hresult.2.1 hread

/-- Every selected digit preserves each normalized divisor payload word. -/
theorem semanticIteration_preserves_v_word
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount i : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hi : i < count) :
    arrayWord digit.memory digit.activeWords v i = arrayWord mem aw v i := by
  have hresult := semanticIteration_eq_div_mod h
  have haddress :
      (MultiLimbSchoolbookSingle.arrayAddress v i).toNat = v.toNat + 32 * (i + 1) := by
    exact MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit v i (by
      have := h.hvFit
      omega)
  have hreadAbove : u.toNat + 32 * (cursor + count + 1) ≤
      (MultiLimbSchoolbookSingle.arrayAddress v i).toNat := by
    rw [haddress]
    exact le_trans h.htopBelowV (by omega)
  have hstoreBelowRead :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
        (MultiLimbSchoolbookSingle.arrayAddress v i).toNat := by
    exact le_trans h.hquotBelowTop (le_trans (by
      rw [multiplySubtractUAddress_ofNat_toNat u cursor count h.hcurrent h.hsumWord
        (by have := h.hwindowRange; omega) h.huFit]
      omega) hreadAbove)
  have hread := validDigit_read_above_frame h.hdigit h.hcurrent h.hrange h.hwindowRange
    h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem
    h.htopActive h.htopBelowV h.hawFit hreadAbove h.hquotWrite hstoreBelowRead
  rw [hresult.1]
  change MultiLimbDivisionTrace.readWord digit.memory aw
      (MultiLimbSchoolbookSingle.arrayAddress v i) =
    MultiLimbDivisionTrace.readWord mem aw (MultiLimbSchoolbookSingle.arrayAddress v i)
  exact readWord_eq_of_size_read_eq digit.memory mem aw
    (MultiLimbSchoolbookSingle.arrayAddress v i) hresult.2.1 hread

/-- Every selected digit preserves the complete normalized divisor payload. Arithmetic writes end
below `v`, while the quotient digit is stored below the `u` header, hence below `v` as well. -/
theorem semanticIteration_preserves_v_slice
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit) :
    divisorReadSlice digit.memory digit.activeWords v 0 count =
      divisorReadSlice mem aw v 0 count := by
  have hresult := semanticIteration_eq_div_mod h
  rw [hresult.1]
  have hslices : ∀ start remaining, start + remaining ≤ count ->
      divisorReadSlice digit.memory aw v start remaining =
        divisorReadSlice mem aw v start remaining := by
    intro start remaining hrange
    induction remaining generalizing start with
    | zero => rfl
    | succ remaining ih =>
        have hstart : start < count := by omega
        have haddress :
            (MultiLimbSchoolbookDivision.multiplySubtractVAddress v
              (UInt256.ofNat start)).toNat = v.toNat + 32 * (start + 1) := by
          exact MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit v start (by
            have := h.hvFit
            omega)
        have hreadAbove : u.toNat + 32 * (cursor + count + 1) ≤
            (MultiLimbSchoolbookDivision.multiplySubtractVAddress v
              (UInt256.ofNat start)).toNat := by
          rw [haddress]
          exact le_trans h.htopBelowV (by omega)
        have hstoreBelowRead :
            (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
              (MultiLimbSchoolbookDivision.multiplySubtractVAddress v
                (UInt256.ofNat start)).toNat := by
          have htopRange : cursor + count - 1 ≤ 65 := by
            have := h.hwindowRange
            omega
          exact le_trans h.hquotBelowTop (le_trans (by
            rw [multiplySubtractUAddress_ofNat_toNat u cursor count h.hcurrent h.hsumWord
              htopRange h.huFit]
            omega) hreadAbove)
        have hread := validDigit_read_above_frame h.hdigit h.hcurrent h.hrange
          h.hwindowRange h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive
          h.huActive h.htopMem h.htopActive h.htopBelowV h.hawFit hreadAbove
          h.hquotWrite hstoreBelowRead
        simp only [divisorReadSlice]
        congr 1
        · unfold MultiLimbSchoolbookDivision.multiplySubtractVi
          exact readWord_eq_of_size_read_eq digit.memory mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractVAddress v
              (UInt256.ofNat start)) hresult.2.1 hread
        · exact ih (start + 1) (by omega)
  exact hslices 0 count (by omega)

/-- The selected quotient-word store preserves the quotient array header. The explicit fit premise
is the allocator's non-wrapping payload bound and supports Barrett's possible index 33. -/
theorem semanticIteration_preserves_quotient_header
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hquotFit : quotient.toNat + 32 * (jj + 2) < UInt256.size) :
    arrayHeader digit.memory digit.activeWords quotient = UInt256.ofNat quotientCount := by
  have haddress :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat =
        quotient.toNat + 32 * (jj + 1) := by
    exact MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit quotient jj (by omega)
  have hheaderBelow : quotient.toNat + 32 ≤
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat := by
    rw [haddress]
    omega
  cases h.hdigit with
  | direct hnonnegative hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
        (UInt256.ofNat cursor) estimate.qHat count
      have hphase := topResult_preserves_divisor_and_size mem aw v u estimate.qHat cursor count
        h.hcurrent h.hrange h.hwindowRange h.hsumWord h.hvFit h.huFit h.hvMem h.huMem
        h.hvActive h.huActive h.htopMem h.htopActive h.htopBelowV h.hawFit
      have hwrite : (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
          top.memory.size := by
        rw [show top.memory.size = mem.size by simpa only [top] using hphase.2]
        exact h.hquotWrite
      have hframe := MultiLimbSchoolbookSingle.arrayHeader_storeQuotient_eq top.memory
        top.activeWords quotient quotient jj estimate.qHat hwrite hheaderBelow
      exact (by
        simpa only [MultiLimbSchoolbookDigitFunction.directMemory, top] using
          hframe.trans hquotHeader)
  | corrected hnegative hqHat hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      let corrected := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
        (UInt256.ofNat cursor) estimate.qHat count
      let storedQHat := MultiLimbSchoolbookDigitFunction.correctedQHat estimate.qHat
      have hcorrected := correctionTop_eq_knuthAddBack mem aw v u estimate.qHat cursor count
        h.hcurrent h.hrange h.hwindowRange h.hsumWord h.hvFit h.huFit h.hvMem h.huMem
        h.hvActive h.huActive h.htopMem h.htopActive h.htopBelowV h.hawFit
      have hwrite : (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤
          corrected.memory.size := by
        rw [show corrected.memory.size = mem.size by
          simpa only [corrected] using hcorrected.2.2.2]
        exact h.hquotWrite
      have hframe := MultiLimbSchoolbookSingle.arrayHeader_storeQuotient_eq corrected.memory
        corrected.activeWords quotient quotient jj storedQHat hwrite hheaderBelow
      exact (by
        simpa only [MultiLimbSchoolbookDigitFunction.correctedMemory, corrected, storedQHat]
          using hframe.trans hquotHeader)

/-- The quotient store is below the `u` header and all arithmetic stores are above it, so one digit
preserves the normalized dividend array header as well. -/
theorem semanticIteration_preserves_u_header
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hquotBelowUHeader :
      (MultiLimbSchoolbookSingle.arrayAddress quotient jj).toNat + 32 ≤ u.toNat) :
    arrayHeader digit.memory digit.activeWords u = arrayHeader mem aw u := by
  have hresult := semanticIteration_eq_div_mod h
  have hreadBelow : u.toNat + 32 ≤ u.toNat + 32 * cursor := by
    have hcurrent := h.hcurrent
    omega
  have hread := validDigit_read_frame h.hdigit h.hcurrent h.hrange h.hwindowRange
    h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem
    h.htopActive h.htopBelowV h.hawFit hreadBelow h.hquotWrite hquotBelowUHeader
  unfold arrayHeader MultiLimbSchoolbookSingle.arrayHeader
    MultiLimbSchoolbookShort.arrayHeader MultiLimbOddCompare.headerWord
  rw [hresult.1]
  exact readWord_eq_of_size_read_eq digit.memory mem aw u hresult.2.1 hread

end Modexp.MultiLimbSchoolbookIterationExecutable
