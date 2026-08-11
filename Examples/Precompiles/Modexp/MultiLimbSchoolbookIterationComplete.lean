import Examples.Precompiles.Modexp.MultiLimbSchoolbookDigitSemantic

/-!
# Complete semantic certificate for one schoolbook iteration

`ValidIteration` is intentionally an execution certificate. This file adds the concrete layout
facts needed to interpret that execution, without changing or postulating its result memory.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookIterationComplete

open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookDivisionSemantic
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookEstimateSemantic
open MultiLimbSchoolbookIterationFunction
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookDigitSemantic
open MultiLimbSchoolbookSingle

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Concrete layout and model identification accompanying one execution certificate. -/
structure SemanticIteration
    (mem : ByteArray) (aw : UInt256)
    (jj cursor count uCount quotientCount : Nat)
    (uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256)
    (vRest uRest : List UInt256) (vSecond uSecond : UInt256)
    (estimate : EstimateResult) (digit : DigitResult) : Prop where
  context : EstimateContext vRest uRest vTop vSecond uHi uLo uSecond
  hvSecondWord : MultiLimbSchoolbookNormalization.arrayWord mem aw v (count - 2) = vSecond
  huSecondWord : MultiLimbSchoolbookNormalization.arrayWord mem aw u (jj + count - 2) = uSecond
  hestimate : ValidEstimate mem aw jj cursor count uCount vTop uLo u shift ret rem v
    quotient normalizationMarker uHi estimate
  hdigit : ValidDigit mem aw count jj quotientCount v u (UInt256.ofNat cursor)
    estimate.qHat shift ret rem quotient vTop normalizationMarker digit
  hcurrent : 0 < cursor
  hrange : count ≤ 32
  hwindowRange : cursor + count ≤ 66
  hsumWord : cursor + count < UInt256.size
  hvFit : v.toNat + 32 * (count + 1) < UInt256.size
  huFit : u.toNat + 32 * (cursor + count) < UInt256.size
  hvMem : v.toNat + 32 * (count + 1) ≤ mem.size
  huMem : u.toNat + 32 * (cursor + count) ≤ mem.size
  hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat
  huActive : u.toNat + 32 * (cursor + count) ≤ 32 * aw.toNat
  htopMem : u.toNat + 32 * (cursor + count + 1) ≤ mem.size
  htopActive : u.toNat + 32 * (cursor + count + 1) ≤ 32 * aw.toNat
  htopBelowV : u.toNat + 32 * (cursor + count + 1) ≤ v.toNat
  hawFit : aw.toNat * 32 < UInt256.size
  hvSlice : divisorReadSlice mem aw v 0 count = vRest ++ [vSecond, vTop]
  huSlice : windowReadSlice mem aw u cursor 0 count = uRest ++ [uSecond, uLo]
  huTop : MultiLimbDivisionTrace.readWord mem aw
    (multiplySubtractUAddress u (UInt256.ofNat cursor) (UInt256.ofNat count)) = uHi
  hquotWrite : (arrayAddress quotient jj).toNat + 32 ≤ mem.size
  hquotActive : (arrayAddress quotient jj).toNat + 32 ≤ 32 * aw.toNat
  hquotBelowWindow : ∀ i, i < count ->
    (arrayAddress quotient jj).toNat + 32 ≤
      (multiplySubtractUAddress u (UInt256.ofNat cursor) (UInt256.ofNat i)).toNat
  hquotBelowTop : (arrayAddress quotient jj).toNat + 32 ≤
    (multiplySubtractUAddress u (UInt256.ofNat cursor) (UInt256.ofNat count)).toNat

/-- Forgetting semantic layout leaves the original exact execution certificate. -/
theorem SemanticIteration.toValidIteration
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit) :
    ValidIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u shift ret rem
      v quotient normalizationMarker
      ⟨digit.memory, digit.activeWords, estimate.steps + digit.steps,
        estimate.gas + digit.gas⟩ := by
  exact ValidIteration.intro estimate digit h.hestimate h.hdigit

/-- One complete deployed iteration stores the unique quotient digit and reduced remainder for
its identified concrete window. -/
theorem semanticIteration_eq_div_mod
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit) :
    let divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])
    let window := windowNat (uRest ++ [uSecond, uLo]) uHi
    let topAddress := multiplySubtractUAddress u (UInt256.ofNat cursor)
      (UInt256.ofNat count)
    digit.activeWords = aw ∧ digit.memory.size = mem.size ∧
      (arrayWord digit.memory aw quotient jj).toNat = window / divisor ∧
      windowNat (windowReadSlice digit.memory aw u cursor 0 count)
          (MultiLimbDivisionTrace.readWord digit.memory aw topAddress) = window % divisor := by
  let divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])
  let window := windowNat (uRest ++ [uSecond, uLo]) uHi
  let topAddress := multiplySubtractUAddress u (UInt256.ofNat cursor) (UInt256.ofNat count)
  have hcore := validEstimateConcreteCore_eq_div_mod estimate h.context h.hvSecondWord
    h.huSecondWord h.hestimate h.hcurrent h.hrange h.hwindowRange h.hsumWord h.hvFit
    h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem h.htopActive h.htopBelowV
    h.hawFit h.hvSlice h.huSlice h.huTop
  have hstored := validDigit_observation h.hdigit h.hcurrent h.hrange h.hwindowRange
    h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem
    h.htopActive h.htopBelowV h.hawFit h.hquotWrite h.hquotActive h.hquotBelowWindow
    h.hquotBelowTop
  dsimp only [divisor, window, topAddress]
  exact ⟨hstored.1, hstored.2.1,
    hstored.2.2.1.trans hcore.1,
    hstored.2.2.2.trans hcore.2⟩

/-- A semantic iteration preserves a padded word below both its mutable dividend window and its
quotient-digit store. -/
theorem semanticIteration_read_below_frame
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount read : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hreadBelowU : read + 32 ≤ u.toNat + 32 * cursor)
    (hreadBelowStore : read + 32 ≤ (arrayAddress quotient jj).toNat) :
    digit.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  exact validDigit_read_below_frame h.hdigit h.hcurrent h.hrange h.hwindowRange h.hsumWord
    h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem h.htopActive
    h.htopBelowV h.hawFit hreadBelowU h.hquotWrite hreadBelowStore

/-- A lower-index iteration preserves any already stored higher quotient word. -/
theorem semanticIteration_preserves_quotient_word
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount sourceIndex : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hsourceBelowU : (arrayAddress quotient sourceIndex).toNat + 32 ≤
      u.toNat + 32 * cursor)
    (hstoreBelowSource : (arrayAddress quotient jj).toNat + 32 ≤
      (arrayAddress quotient sourceIndex).toNat) :
    arrayWord digit.memory aw quotient sourceIndex = arrayWord mem aw quotient sourceIndex := by
  have hframe := validDigit_read_frame h.hdigit h.hcurrent h.hrange h.hwindowRange
    h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem
    h.htopActive h.htopBelowV h.hawFit hsourceBelowU h.hquotWrite hstoreBelowSource
  have hsemantic := semanticIteration_eq_div_mod h
  unfold arrayWord MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
  exact readWord_eq_of_size_read_eq digit.memory mem aw (arrayAddress quotient sourceIndex)
    hsemantic.2.1 hframe

/-- One quotient iteration preserves a lower, not-yet-consumed `u` word.  The source bound puts
the word below the first multiply-subtract destination; the final premise is the concrete
allocator separation between the quotient store and that source word. -/
theorem semanticIteration_preserves_u_word_below
    {mem : ByteArray} {aw : UInt256}
    {jj cursor count uCount quotientCount sourceIndex : Nat}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {vRest uRest : List UInt256} {vSecond uSecond : UInt256}
    {estimate : EstimateResult} {digit : DigitResult}
    (h : SemanticIteration mem aw jj cursor count uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker vRest uRest vSecond uSecond estimate digit)
    (hsource : sourceIndex + 2 ≤ cursor)
    (hstoreBelowSource : (arrayAddress quotient jj).toNat + 32 ≤
      (arrayAddress u sourceIndex).toNat) :
    arrayWord digit.memory aw u sourceIndex = arrayWord mem aw u sourceIndex := by
  have hsourceFit : u.toNat + 32 * (sourceIndex + 1) < UInt256.size := by
    have := h.huFit
    omega
  have hsourceAddress : (arrayAddress u sourceIndex).toNat =
      u.toNat + 32 * (sourceIndex + 1) := by
    change (MultiLimbOddCompare.elementPtr u (UInt256.ofNat sourceIndex)).toNat = _
    exact MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit u sourceIndex hsourceFit
  have hreadBelowU : (arrayAddress u sourceIndex).toNat + 32 ≤
      u.toNat + 32 * cursor := by
    rw [hsourceAddress]
    omega
  have hframe := validDigit_read_frame h.hdigit h.hcurrent h.hrange h.hwindowRange
    h.hsumWord h.hvFit h.huFit h.hvMem h.huMem h.hvActive h.huActive h.htopMem
    h.htopActive h.htopBelowV h.hawFit hreadBelowU h.hquotWrite hstoreBelowSource
  have hsemantic := semanticIteration_eq_div_mod h
  unfold arrayWord MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
  exact readWord_eq_of_size_read_eq digit.memory mem aw (arrayAddress u sourceIndex)
    hsemantic.2.1 hframe

end Modexp.MultiLimbSchoolbookIterationComplete
