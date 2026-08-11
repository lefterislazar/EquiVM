import Examples.Precompiles.Modexp.MultiLimbSchoolbookDenormalizationSemantic
import Examples.Precompiles.Modexp.MultiLimbQhatLoop

/-!
# Knuth q-hat estimate semantics

This module isolates the radix argument behind the generated q-hat refinement loop.  It turns
the top-two-digit division invariant and final second-divisor-digit comparison into the two
estimate bounds consumed by `knuthAcceptedWindow`.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookQhatSemantic

open Modexp.MultiLimbSchoolbookDivisionSemantic
open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 50000
set_option maxHeartbeats 0

/-- Radix-level form of the Knuth estimate theorem.  `scale` is the weight of the divisor's
second-highest digit; `vRest` and `uRest` are the lower parts below that weight. -/
theorem refinedEstimateBounds
    {radix scale q r vTop vSecond vRest uHi uLo uSecond uRest divisor window : Nat}
    (hradix : 1 < radix)
    (hscale : 0 < scale)
    (hq : q < radix)
    (hr : r < vTop)
    (hvTop : 0 < vTop)
    (hvSecond : vSecond < radix)
    (huSecond : uSecond < radix)
    (hvRest : vRest < scale)
    (huRest : uRest < scale)
    (hestimate : uHi * radix + uLo = q * vTop + r)
    (hrefined : q * vSecond ≤ r * radix + uSecond)
    (hdivisor : divisor = vRest + scale * (vSecond + radix * vTop))
    (hwindow : window = uRest + scale *
      (uSecond + radix * uLo + radix * radix * uHi)) :
    window < (q + 1) * divisor ∧ q * divisor ≤ window + divisor := by
  have htopPair : uHi * radix + uLo + 1 ≤ (q + 1) * vTop := by
    rw [hestimate]
    nlinarith
  have hwindowUpper :
      window < scale * radix * (uHi * radix + uLo + 1) := by
    have hlowBlock : uRest + scale * uSecond < scale * radix := by
      calc
        uRest + scale * uSecond < scale + scale * uSecond := by omega
        _ = scale * (uSecond + 1) := by ring
        _ ≤ scale * radix := Nat.mul_le_mul_left scale (by omega)
    calc
      window = (uRest + scale * uSecond) +
          scale * radix * (uLo + radix * uHi) := by rw [hwindow]; ring
      _ < scale * radix + scale * radix * (uLo + radix * uHi) := by
        exact Nat.add_lt_add_right hlowBlock _
      _ = scale * radix * (uHi * radix + uLo + 1) := by ring
  have hdivisorLower : scale * radix * vTop ≤ divisor := by
    rw [hdivisor]
    nlinarith
  constructor
  · calc
      window < scale * radix * (uHi * radix + uLo + 1) := hwindowUpper
      _ ≤ scale * radix * ((q + 1) * vTop) :=
        Nat.mul_le_mul_left _ htopPair
      _ = (q + 1) * (scale * radix * vTop) := by ring
      _ ≤ (q + 1) * divisor := Nat.mul_le_mul_left _ hdivisorLower
  · by_cases hqZero : q = 0
    · subst q
      simp
    · let qPred := q - 1
      have hqDecomp : q = qPred + 1 := by
        dsimp only [qPred]
        omega
      have hqPred : qPred < radix := by omega
      have hrestTop :
          qPred * (vSecond + radix * vTop + 1) ≤
            uSecond + radix * (uHi * radix + uLo) := by
        rw [hestimate, hqDecomp]
        have hrefined' : (qPred + 1) * vSecond ≤ r * radix + uSecond := by
          simpa only [hqDecomp] using hrefined
        have hvTopRadix : radix ≤ radix * vTop := by nlinarith
        nlinarith
      have hdivisorUpper : divisor < scale * (vSecond + radix * vTop + 1) := by
        rw [hdivisor]
        nlinarith
      have hpredDivisor : qPred * divisor ≤ window := by
        have hlower :
            scale * (uSecond + radix * (uHi * radix + uLo)) ≤ window := by
          rw [hwindow]
          ring_nf
          omega
        by_cases hqPredZero : qPred = 0
        · rw [hqPredZero]
          simp
        · exact Nat.le_of_lt (calc
            qPred * divisor < qPred * (scale * (vSecond + radix * vTop + 1)) :=
              Nat.mul_lt_mul_of_pos_left hdivisorUpper (Nat.zero_lt_of_ne_zero hqPredZero)
            _ = scale * (qPred * (vSecond + radix * vTop + 1)) := by ring
            _ ≤ scale * (uSecond + radix * (uHi * radix + uLo)) :=
              Nat.mul_le_mul_left scale hrestTop
            _ ≤ window := hlower)
      calc
        q * divisor = qPred * divisor + divisor := by rw [hqDecomp]; ring
        _ ≤ window + divisor := Nat.add_le_add_right hpredDivisor divisor

/-- The top-two-word quotient equation and a proper remainder alone show that the initial estimate
has not been decremented below the true quotient; the second-word refinement comparison is not
needed for this direction. -/
theorem initialEstimateNeverLow
    {radix scale q r vTop vSecond vRest uHi uLo uSecond uRest divisor window : Nat}
    (hscale : 0 < scale)
    (hr : r < vTop)
    (hvTop : 0 < vTop)
    (huSecond : uSecond < radix)
    (huRest : uRest < scale)
    (hestimate : uHi * radix + uLo = q * vTop + r)
    (hdivisor : divisor = vRest + scale * (vSecond + radix * vTop))
    (hwindow : window = uRest + scale *
      (uSecond + radix * uLo + radix * radix * uHi)) :
    window < (q + 1) * divisor := by
  have htopPair : uHi * radix + uLo + 1 ≤ (q + 1) * vTop := by
    rw [hestimate]
    nlinarith
  have hlowBlock : uRest + scale * uSecond < scale * radix := by
    calc
      uRest + scale * uSecond < scale + scale * uSecond := by omega
      _ = scale * (uSecond + 1) := by ring
      _ ≤ scale * radix := Nat.mul_le_mul_left scale (by omega)
  have hwindowUpper :
      window < scale * radix * (uHi * radix + uLo + 1) := by
    calc
      window = (uRest + scale * uSecond) +
          scale * radix * (uLo + radix * uHi) := by rw [hwindow]; ring
      _ < scale * radix + scale * radix * (uLo + radix * uHi) := by
        exact Nat.add_lt_add_right hlowBlock _
      _ = scale * radix * (uHi * radix + uLo + 1) := by ring
  have hdivisorLower : scale * radix * vTop ≤ divisor := by
    rw [hdivisor]
    nlinarith
  calc
    window < scale * radix * (uHi * radix + uLo + 1) := hwindowUpper
    _ ≤ scale * radix * ((q + 1) * vTop) := Nat.mul_le_mul_left _ htopPair
    _ = (q + 1) * (scale * radix * vTop) := by ring
    _ ≤ (q + 1) * divisor := Nat.mul_le_mul_left _ hdivisorLower

/-- The final refinement comparison gives the standard at-most-one-overestimate bound without
requiring the synthetic remainder to remain below the top divisor digit. -/
theorem refinedEstimateAtMostOne
    {radix scale q r vTop vSecond vRest uHi uLo uSecond uRest divisor window : Nat}
    (hq : q < radix)
    (hvTop : 0 < vTop)
    (hvRest : vRest < scale)
    (hestimate : uHi * radix + uLo = q * vTop + r)
    (hrefined : q * vSecond ≤ r * radix + uSecond)
    (hdivisor : divisor = vRest + scale * (vSecond + radix * vTop))
    (hwindow : window = uRest + scale *
      (uSecond + radix * uLo + radix * radix * uHi)) :
    q * divisor ≤ window + divisor := by
  by_cases hqZero : q = 0
  · subst q
    simp
  · let qPred := q - 1
    have hqDecomp : q = qPred + 1 := by
      dsimp only [qPred]
      omega
    have hqPred : qPred < radix := by omega
    have hrestTop :
        qPred * (vSecond + radix * vTop + 1) ≤
          uSecond + radix * (uHi * radix + uLo) := by
      rw [hestimate, hqDecomp]
      have hrefined' : (qPred + 1) * vSecond ≤ r * radix + uSecond := by
        simpa only [hqDecomp] using hrefined
      have hvTopRadix : radix ≤ radix * vTop := by nlinarith
      nlinarith
    have hdivisorUpper : divisor < scale * (vSecond + radix * vTop + 1) := by
      rw [hdivisor]
      nlinarith
    have hpredDivisor : qPred * divisor ≤ window := by
      have hlower :
          scale * (uSecond + radix * (uHi * radix + uLo)) ≤ window := by
        rw [hwindow]
        ring_nf
        omega
      by_cases hqPredZero : qPred = 0
      · rw [hqPredZero]
        simp
      · exact Nat.le_of_lt (calc
          qPred * divisor < qPred * (scale * (vSecond + radix * vTop + 1)) :=
            Nat.mul_lt_mul_of_pos_left hdivisorUpper
              (Nat.zero_lt_of_ne_zero hqPredZero)
          _ = scale * (qPred * (vSecond + radix * vTop + 1)) := by ring
          _ ≤ scale * (uSecond + radix * (uHi * radix + uLo)) :=
            Nat.mul_le_mul_left scale hrestTop
          _ ≤ window := hlower)
    calc
      q * divisor = qPred * divisor + divisor := by rw [hqDecomp]; ring
      _ ≤ window + divisor := Nat.add_le_add_right hpredDivisor divisor

/-- The comparison that triggered the last non-overflowing decrement proves that the resulting
estimate was not decremented below the true quotient. -/
theorem lastRefinementNeverLow
    {radix scale q r vTop vSecond vRest uHi uLo uSecond uRest divisor window : Nat}
    (hscale : 0 < scale)
    (hrTop : vTop ≤ r)
    (huRest : uRest < scale)
    (hestimate : uHi * radix + uLo = q * vTop + r)
    (hlast : (q + 1) * vSecond > (r - vTop) * radix + uSecond)
    (hdivisor : divisor = vRest + scale * (vSecond + radix * vTop))
    (hwindow : window = uRest + scale *
      (uSecond + radix * uLo + radix * radix * uHi)) :
    window < (q + 1) * divisor := by
  have hrDecomp : r = (r - vTop) + vTop := by omega
  have hhigh :
      uSecond + radix * r < (q + 1) * vSecond + radix * vTop := by
    rw [hrDecomp]
    nlinarith
  have hlow :
      uRest + scale * (uSecond + radix * r) <
        scale * ((q + 1) * vSecond + radix * vTop) := by
    calc
      uRest + scale * (uSecond + radix * r) <
          scale + scale * (uSecond + radix * r) := by omega
      _ = scale * (uSecond + radix * r + 1) := by ring
      _ ≤ scale * ((q + 1) * vSecond + radix * vTop) :=
        Nat.mul_le_mul_left scale hhigh
  have hwindowEstimate :
      window = uRest + scale *
        (uSecond + radix * r + radix * q * vTop) := by
    rw [hwindow]
    congr 2
    calc
      uSecond + radix * uLo + radix * radix * uHi =
          uSecond + radix * (uHi * radix + uLo) := by ring
      _ = uSecond + radix * (q * vTop + r) := by rw [hestimate]
      _ = uSecond + radix * r + radix * q * vTop := by ring
  have hdivisorLower : scale * (vSecond + radix * vTop) ≤ divisor := by
    rw [hdivisor]
    omega
  calc
    window = uRest + scale * (uSecond + radix * r) +
        scale * (radix * q * vTop) := by rw [hwindowEstimate]; ring
    _ < scale * ((q + 1) * vSecond + radix * vTop) +
        scale * (radix * q * vTop) := Nat.add_lt_add_right hlow _
    _ = (q + 1) * (scale * (vSecond + radix * vTop)) := by ring
    _ ≤ (q + 1) * divisor := Nat.mul_le_mul_left _ hdivisorLower

/-- When the refinement's `r + vTop` update overflows one word, the decremented q-hat still
satisfies both Algorithm D estimate bounds. The unbounded synthetic remainder is `r + vTop`;
the bytecode may discard its wrapped word because the overflow itself makes the second-digit
at-most-one bound immediate. -/
theorem overflowEstimateBounds
    {radix scale q r vTop vSecond vRest uHi uLo uSecond uRest divisor window : Nat}
    (hradix : 1 < radix)
    (hscale : 0 < scale)
    (hq : q < radix)
    (hqPos : 0 < q)
    (hr : r < radix)
    (hvSecond : vSecond < radix)
    (hvRest : vRest < scale)
    (huRest : uRest < scale)
    (hestimate : uHi * radix + uLo = q * vTop + r)
    (hrefine : q * vSecond > r * radix + uSecond)
    (hoverflow : radix ≤ r + vTop)
    (hdivisor : divisor = vRest + scale * (vSecond + radix * vTop))
    (hwindow : window = uRest + scale *
      (uSecond + radix * uLo + radix * radix * uHi)) :
    window < ((q - 1) + 1) * divisor ∧
      (q - 1) * divisor ≤ window + divisor := by
  have hqDecomp : q = (q - 1) + 1 := by omega
  have hestimate' :
      uHi * radix + uLo = (q - 1) * vTop + (r + vTop) := by
    nlinarith [hestimate]
  have hvTopPos : 0 < vTop := by omega
  have hlast :
      ((q - 1) + 1) * vSecond >
        ((r + vTop) - vTop) * radix + uSecond := by
    rw [Nat.add_sub_cancel_right, ← hqDecomp]
    exact hrefine
  have hrefined' :
      (q - 1) * vSecond ≤ (r + vTop) * radix + uSecond := by
    have hleft : (q - 1) * vSecond < radix * radix := by
      nlinarith
    have hright : radix * radix ≤ (r + vTop) * radix := by
      exact Nat.mul_le_mul_right radix hoverflow
    omega
  constructor
  · exact lastRefinementNeverLow hscale (by omega) huRest hestimate' hlast
      hdivisor hwindow
  · exact refinedEstimateAtMostOne (by omega) hvTopPos hvRest hestimate'
      hrefined' hdivisor hwindow

theorem qhatDone_iff_le (qHat rHat vSecond uSecond : UInt256) :
    qhatNeedsRefinement qHat rHat vSecond uSecond = ⟨0⟩ ↔
      qHat.toNat * vSecond.toNat ≤ rHat.toNat * UInt256.size + uSecond.toNat := by
  constructor
  · intro hdone
    by_contra hnot
    have hrefine : qhatNeedsRefinement qHat rHat vSecond uSecond ≠ ⟨0⟩ :=
      (qhatNeedsRefinement_iff qHat rHat vSecond uSecond).mpr (by omega)
    exact hrefine hdone
  · intro hle
    by_contra hnotZero
    have hrefine := (qhatNeedsRefinement_iff qHat rHat vSecond uSecond).mp hnotZero
    omega

/-- Every non-overflowing generated refinement path preserves the top-two-digit division
equation. -/
theorem qhatRefinementPath_preserves_estimate
    {vTop vSecond uSecond : UInt256}
    {initial : QhatState} {states : List QhatState}
    (path : QhatRefinementPath vTop vSecond uSecond initial states)
    {numerator : Nat}
    (hinitial : numerator = initial.qHat.toNat * vTop.toNat + initial.rHat.toNat) :
    numerator = (qhatPathEnd initial states).qHat.toNat * vTop.toNat +
      (qhatPathEnd initial states).rHat.toNat := by
  have harithmetic := qhatRefinementPath_arithmetic path
  rw [hinitial]
  nlinarith

/-- The generated overflow guard is equivalent to overflow of the unbounded `rHat + vTop`
addition. -/
theorem qhatAdvance_overflow_sum_ge_size
    (vTop : UInt256) (state : QhatState)
    (hoverflow : (qhatAdvance vTop state).rHat.lt vTop ≠ ⟨0⟩) :
    UInt256.size ≤ state.rHat.toNat + vTop.toNat := by
  have hltNat : (qhatAdvance vTop state).rHat.toNat < vTop.toNat := by
    by_contra hnot
    have hzero : (qhatAdvance vTop state).rHat.lt vTop = ⟨0⟩ :=
      ult_zero (by omega)
    exact hoverflow hzero
  have hone : (qhatAdvance vTop state).rHat.lt vTop = ⟨1⟩ := ult_one hltNat
  have hrec := Modexp.evmAddCarry_recompose vTop state.rHat
  have hone' : UInt256.lt (vTop + state.rHat) vTop = ⟨1⟩ := by
    simpa only [qhatAdvance, u256_add_comm] using hone
  rw [hone'] at hrec
  simp only [show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mul_one] at hrec
  omega

/-- With a normalized top divisor word, a non-overflowing refinement path contains at most one
decrement.  A second decrement necessarily takes the generated overflow exit instead. -/
theorem normalizedQhatRefinementPath_length_le_one
    {vTop vSecond uSecond : UInt256}
    {initial : QhatState} {states : List QhatState}
    (path : QhatRefinementPath vTop vSecond uSecond initial states)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    states.length ≤ 1 := by
  have harithmetic := qhatRefinementPath_arithmetic path
  have hendBound : (qhatPathEnd initial states).rHat.toNat < UInt256.size :=
    (qhatPathEnd initial states).rHat.val.isLt
  by_contra hlong
  have htwo : 2 ≤ states.length := by omega
  have hproduct : 2 * vTop.toNat ≤ states.length * vTop.toNat :=
    Nat.mul_le_mul_right vTop.toNat htwo
  nlinarith [harithmetic.2]

/-- A normalized generated path is empty, or its final state records the comparison that caused
its unique non-overflowing decrement. -/
theorem normalizedQhatRefinementPath_empty_or_last_condition
    {vTop vSecond uSecond : UInt256}
    {initial : QhatState} {states : List QhatState}
    (path : QhatRefinementPath vTop vSecond uSecond initial states)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    states = [] ∨
      ((qhatPathEnd initial states).qHat.toNat + 1) * vSecond.toNat >
        ((qhatPathEnd initial states).rHat.toNat - vTop.toNat) * UInt256.size +
          uSecond.toNat := by
  have hlength := normalizedQhatRefinementPath_length_le_one path hnormalized
  cases path with
  | nil state => exact Or.inl rfl
  | cons state rest hrefine hnoOverflow tail =>
      cases rest with
      | cons next rest =>
          simp only [List.length_cons] at hlength
          omega
      | nil =>
          have hrefineNat :=
            (qhatNeedsRefinement_iff initial.qHat initial.rHat vSecond uSecond).mp hrefine
          have hpos := qhatRefinement_qHat_positive
            initial.qHat initial.rHat vSecond uSecond hrefine
          have hq := qhatAdvance_qHat_toNat vTop initial hpos
          have hr := qhatAdvance_rHat_toNat vTop initial hnoOverflow
          simp only [qhatPathEnd]
          rw [hq, hr]
          have hqDecomp : initial.qHat.toNat - 1 + 1 = initial.qHat.toNat := by omega
          rw [hqDecomp, Nat.add_sub_cancel_right]
          exact Or.inr hrefineNat

/-- Word-list specialization of `refinedEstimateBounds`. -/
theorem refinedWordEstimateBounds
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond qHat rHat : UInt256)
    (hlength : uRest.length = vRest.length)
    (hvTopPos : 0 < vTop.toNat)
    (hestimate :
      uHi.toNat * UInt256.size + uLo.toNat =
        qHat.toNat * vTop.toNat + rHat.toNat)
    (hrHat : rHat.toNat < vTop.toNat)
    (hrefined :
      qHat.toNat * vSecond.toNat ≤
        rHat.toNat * UInt256.size + uSecond.toNat) :
    let divisorDigits := vRest ++ [vSecond, vTop]
    let windowDigits := uRest ++ [uSecond, uLo, uHi]
    Modexp.wordLimbsToNat windowDigits <
        (qHat.toNat + 1) * Modexp.wordLimbsToNat divisorDigits ∧
      qHat.toNat * Modexp.wordLimbsToNat divisorDigits ≤
        Modexp.wordLimbsToNat windowDigits + Modexp.wordLimbsToNat divisorDigits := by
  let scale := UInt256.size ^ vRest.length
  have hradixPos : 0 < UInt256.size := by norm_num [UInt256.size]
  have hscale : 0 < scale := Nat.pow_pos hradixPos
  have hvRest := Modexp.wordLimbsToNat_lt_pow vRest
  have huRest := Modexp.wordLimbsToNat_lt_pow uRest
  rw [hlength] at huRest
  have hdivisor :
      Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) =
        Modexp.wordLimbsToNat vRest +
          scale * (vSecond.toNat + UInt256.size * vTop.toNat) := by
    rw [Modexp.wordLimbsToNat_append]
    congr 1
  have hscaleLength : UInt256.size ^ uRest.length = scale := by
    rw [hlength]
  have hwindow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) =
        Modexp.wordLimbsToNat uRest + scale *
          (uSecond.toNat + UInt256.size * uLo.toNat +
            UInt256.size * UInt256.size * uHi.toNat) := by
    rw [Modexp.wordLimbsToNat_append, hscaleLength]
    congr 1
    simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
    ring
  have hbounds := refinedEstimateBounds
    (radix := UInt256.size) (scale := scale)
    (q := qHat.toNat) (r := rHat.toNat)
    (vTop := vTop.toNat) (vSecond := vSecond.toNat)
    (vRest := Modexp.wordLimbsToNat vRest)
    (uHi := uHi.toNat) (uLo := uLo.toNat) (uSecond := uSecond.toNat)
    (uRest := Modexp.wordLimbsToNat uRest)
    (divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]))
    (window := Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]))
    (by norm_num [UInt256.size]) hscale qHat.val.isLt hrHat hvTopPos
    vSecond.val.isLt uSecond.val.isLt hvRest huRest hestimate hrefined
    hdivisor hwindow
  exact hbounds

/-- Word-list form of the initial never-too-low estimate, independent of whether the generated
second-word comparison requests a refinement. -/
theorem initialWordEstimateNeverLow
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond qHat rHat : UInt256)
    (hlength : uRest.length = vRest.length)
    (hvTopPos : 0 < vTop.toNat)
    (hestimate :
      uHi.toNat * UInt256.size + uLo.toNat =
        qHat.toNat * vTop.toNat + rHat.toNat)
    (hrHat : rHat.toNat < vTop.toNat) :
    Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
      (qHat.toNat + 1) * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  let scale := UInt256.size ^ vRest.length
  have hradixPos : 0 < UInt256.size := by norm_num [UInt256.size]
  have hscale : 0 < scale := Nat.pow_pos hradixPos
  have huRest := Modexp.wordLimbsToNat_lt_pow uRest
  rw [hlength] at huRest
  have hscaleLength : UInt256.size ^ uRest.length = scale := by rw [hlength]
  have hdivisor :
      Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) =
        Modexp.wordLimbsToNat vRest +
          scale * (vSecond.toNat + UInt256.size * vTop.toNat) := by
    rw [Modexp.wordLimbsToNat_append]
    congr 1
  have hwindow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) =
        Modexp.wordLimbsToNat uRest + scale *
          (uSecond.toNat + UInt256.size * uLo.toNat +
            UInt256.size * UInt256.size * uHi.toNat) := by
    rw [Modexp.wordLimbsToNat_append, hscaleLength]
    congr 1
    simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
    ring
  exact initialEstimateNeverLow hscale hrHat hvTopPos uSecond.val.isLt huRest hestimate
    hdivisor hwindow

/-- Word-list form of the at-most-one-overestimate inequality for an arbitrary synthetic
remainder. This is used by the saturated route, where the synthetic remainder can exceed one
word as an unbounded natural even though no wrapped value is needed afterward. -/
theorem arbitraryWordEstimateAtMostOne
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond qHat : UInt256) (rHat : Nat)
    (hlength : uRest.length = vRest.length)
    (hvTopPos : 0 < vTop.toNat)
    (hestimate :
      uHi.toNat * UInt256.size + uLo.toNat = qHat.toNat * vTop.toNat + rHat)
    (hrefined :
      qHat.toNat * vSecond.toNat ≤ rHat * UInt256.size + uSecond.toNat) :
    qHat.toNat * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ≤
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) +
        Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  let scale := UInt256.size ^ vRest.length
  have hradixPos : 0 < UInt256.size := by norm_num [UInt256.size]
  have hscale : 0 < scale := Nat.pow_pos hradixPos
  have hvRest := Modexp.wordLimbsToNat_lt_pow vRest
  have hscaleLength : UInt256.size ^ uRest.length = scale := by rw [hlength]
  have hdivisor :
      Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) =
        Modexp.wordLimbsToNat vRest +
          scale * (vSecond.toNat + UInt256.size * vTop.toNat) := by
    rw [Modexp.wordLimbsToNat_append]
    congr 1
  have hwindow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) =
        Modexp.wordLimbsToNat uRest + scale *
          (uSecond.toNat + UInt256.size * uLo.toNat +
            UInt256.size * UInt256.size * uHi.toNat) := by
    rw [Modexp.wordLimbsToNat_append, hscaleLength]
    congr 1
    simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
    ring
  exact refinedEstimateAtMostOne qHat.val.isLt hvTopPos hvRest hestimate hrefined
    hdivisor hwindow

/-- The normal generated refinement path preserves an initial never-too-low estimate and derives
the at-most-one bound from the final comparison. This form also covers Solidity's saturated
estimate, whose synthetic initial remainder need not be below `vTop`. -/
theorem refinedWordPathEstimateBoundsOfInitialNeverLow
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond : UInt256)
    (initial : QhatState) (states : List QhatState)
    (hlength : uRest.length = vRest.length)
    (hvTopPos : 0 < vTop.toNat)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hinitial :
      uHi.toNat * UInt256.size + uLo.toNat =
        initial.qHat.toNat * vTop.toNat + initial.rHat.toNat)
    (hinitialNeverLow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
        (initial.qHat.toNat + 1) *
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]))
    (path : QhatRefinementPath vTop vSecond uSecond initial states)
    (hdone : qhatNeedsRefinement
      (qhatPathEnd initial states).qHat (qhatPathEnd initial states).rHat
      vSecond uSecond = ⟨0⟩) :
    let final := qhatPathEnd initial states
    let divisorDigits := vRest ++ [vSecond, vTop]
    let windowDigits := uRest ++ [uSecond, uLo, uHi]
    Modexp.wordLimbsToNat windowDigits <
        (final.qHat.toNat + 1) * Modexp.wordLimbsToNat divisorDigits ∧
      final.qHat.toNat * Modexp.wordLimbsToNat divisorDigits ≤
        Modexp.wordLimbsToNat windowDigits + Modexp.wordLimbsToNat divisorDigits := by
  dsimp only
  let final := qhatPathEnd initial states
  let scale := UInt256.size ^ vRest.length
  have hradixPos : 0 < UInt256.size := by norm_num [UInt256.size]
  have hscale : 0 < scale := Nat.pow_pos hradixPos
  have hvRest := Modexp.wordLimbsToNat_lt_pow vRest
  have huRest := Modexp.wordLimbsToNat_lt_pow uRest
  rw [hlength] at huRest
  have hscaleLength : UInt256.size ^ uRest.length = scale := by rw [hlength]
  have hdivisor :
      Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) =
        Modexp.wordLimbsToNat vRest +
          scale * (vSecond.toNat + UInt256.size * vTop.toNat) := by
    rw [Modexp.wordLimbsToNat_append]
    congr 1
  have hwindow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) =
        Modexp.wordLimbsToNat uRest + scale *
          (uSecond.toNat + UInt256.size * uLo.toNat +
            UInt256.size * UInt256.size * uHi.toNat) := by
    rw [Modexp.wordLimbsToNat_append, hscaleLength]
    congr 1
    simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
    ring
  have hfinalEstimate :
      uHi.toNat * UInt256.size + uLo.toNat =
        final.qHat.toNat * vTop.toNat + final.rHat.toNat := by
    exact qhatRefinementPath_preserves_estimate path hinitial
  have hfinalRefined :
      final.qHat.toNat * vSecond.toNat ≤
        final.rHat.toNat * UInt256.size + uSecond.toNat :=
    (qhatDone_iff_le final.qHat final.rHat vSecond uSecond).mp hdone
  have hatMostOne :
      final.qHat.toNat * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ≤
        Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) +
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) :=
    refinedEstimateAtMostOne final.qHat.val.isLt hvTopPos hvRest hfinalEstimate
      hfinalRefined hdivisor hwindow
  constructor
  · by_cases hempty : states = []
    · subst states
      simpa [final, qhatPathEnd] using hinitialNeverLow
    · have hlastCases :=
        normalizedQhatRefinementPath_empty_or_last_condition path hnormalized
      have hlast :
          (final.qHat.toNat + 1) * vSecond.toNat >
            (final.rHat.toNat - vTop.toNat) * UInt256.size + uSecond.toNat := by
        rcases hlastCases with hzero | hlast
        · exact (hempty hzero).elim
        · exact hlast
      have harithmetic := qhatRefinementPath_arithmetic path
      have hlengthPos : 1 ≤ states.length := by
        cases states with
        | nil => exact (hempty rfl).elim
        | cons state rest => simp
      have htopProduct : vTop.toNat ≤ states.length * vTop.toNat := by
        have := Nat.mul_le_mul_right vTop.toNat hlengthPos
        simpa only [one_mul] using this
      have hfinalRTop : vTop.toNat ≤ final.rHat.toNat := by
        dsimp only [final]
        rw [harithmetic.2]
        omega
      exact lastRefinementNeverLow hscale hfinalRTop huRest hfinalEstimate hlast
        hdivisor hwindow
  · exact hatMostOne

/-- The ordinary top-two-word division estimate supplies the initial never-too-low premise used
by the generalized normal-path theorem. -/
theorem refinedWordPathEstimateBounds
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond : UInt256)
    (initial : QhatState) (states : List QhatState)
    (hlength : uRest.length = vRest.length)
    (hvTopPos : 0 < vTop.toNat)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hinitial :
      uHi.toNat * UInt256.size + uLo.toNat =
        initial.qHat.toNat * vTop.toNat + initial.rHat.toNat)
    (hrInitial : initial.rHat.toNat < vTop.toNat)
    (path : QhatRefinementPath vTop vSecond uSecond initial states)
    (hdone : qhatNeedsRefinement
      (qhatPathEnd initial states).qHat (qhatPathEnd initial states).rHat
      vSecond uSecond = ⟨0⟩) :
    let final := qhatPathEnd initial states
    let divisorDigits := vRest ++ [vSecond, vTop]
    let windowDigits := uRest ++ [uSecond, uLo, uHi]
    Modexp.wordLimbsToNat windowDigits <
        (final.qHat.toNat + 1) * Modexp.wordLimbsToNat divisorDigits ∧
      final.qHat.toNat * Modexp.wordLimbsToNat divisorDigits ≤
        Modexp.wordLimbsToNat windowDigits + Modexp.wordLimbsToNat divisorDigits := by
  have hinitialNeverLow := initialWordEstimateNeverLow vRest uRest vTop vSecond uHi uLo
    uSecond initial.qHat initial.rHat hlength hvTopPos hinitial hrInitial
  exact refinedWordPathEstimateBoundsOfInitialNeverLow vRest uRest vTop vSecond uHi uLo
    uSecond initial states hlength hvTopPos hnormalized hinitial hinitialNeverLow path hdone

/-- Word-list specialization for the distinct generated overflow break. The returned q-hat is
the concrete decremented word from `qhatAdvance`; both accepted-window bounds follow from the
executed prefix, taken refinement comparison, and taken overflow comparison. -/
theorem refinedWordPathOverflowEstimateBounds
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond : UInt256)
    (initial : QhatState) (states : List QhatState)
    (hlength : uRest.length = vRest.length)
    (hinitial :
      uHi.toNat * UInt256.size + uLo.toNat =
        initial.qHat.toNat * vTop.toNat + initial.rHat.toNat)
    (path : QhatRefinementPath vTop vSecond uSecond initial states)
    (hrefine : qhatNeedsRefinement
      (qhatPathEnd initial states).qHat (qhatPathEnd initial states).rHat
      vSecond uSecond ≠ ⟨0⟩)
    (hoverflow :
      (qhatAdvance vTop (qhatPathEnd initial states)).rHat.lt vTop ≠ ⟨0⟩) :
    let returned := qhatAdvance vTop (qhatPathEnd initial states)
    let divisorDigits := vRest ++ [vSecond, vTop]
    let windowDigits := uRest ++ [uSecond, uLo, uHi]
    Modexp.wordLimbsToNat windowDigits <
        (returned.qHat.toNat + 1) * Modexp.wordLimbsToNat divisorDigits ∧
      returned.qHat.toNat * Modexp.wordLimbsToNat divisorDigits ≤
        Modexp.wordLimbsToNat windowDigits + Modexp.wordLimbsToNat divisorDigits := by
  dsimp only
  let final := qhatPathEnd initial states
  let scale := UInt256.size ^ vRest.length
  have hradixPos : 0 < UInt256.size := by norm_num [UInt256.size]
  have hscale : 0 < scale := Nat.pow_pos hradixPos
  have hvRest := Modexp.wordLimbsToNat_lt_pow vRest
  have huRest := Modexp.wordLimbsToNat_lt_pow uRest
  rw [hlength] at huRest
  have hscaleLength : UInt256.size ^ uRest.length = scale := by rw [hlength]
  have hdivisor :
      Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) =
        Modexp.wordLimbsToNat vRest +
          scale * (vSecond.toNat + UInt256.size * vTop.toNat) := by
    rw [Modexp.wordLimbsToNat_append]
    congr 1
  have hwindow :
      Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) =
        Modexp.wordLimbsToNat uRest + scale *
          (uSecond.toNat + UInt256.size * uLo.toNat +
            UInt256.size * UInt256.size * uHi.toNat) := by
    rw [Modexp.wordLimbsToNat_append, hscaleLength]
    congr 1
    simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
    ring
  have hfinalEstimate :
      uHi.toNat * UInt256.size + uLo.toNat =
        final.qHat.toNat * vTop.toNat + final.rHat.toNat :=
    qhatRefinementPath_preserves_estimate path hinitial
  have hrefineNat :=
    (qhatNeedsRefinement_iff final.qHat final.rHat vSecond uSecond).mp hrefine
  have hqPos := qhatRefinement_qHat_positive final.qHat final.rHat vSecond uSecond hrefine
  have hoverflowNat := qhatAdvance_overflow_sum_ge_size vTop final hoverflow
  have hbounds := overflowEstimateBounds
    (radix := UInt256.size) (scale := scale)
    (q := final.qHat.toNat) (r := final.rHat.toNat)
    (vTop := vTop.toNat) (vSecond := vSecond.toNat)
    (vRest := Modexp.wordLimbsToNat vRest)
    (uHi := uHi.toNat) (uLo := uLo.toNat) (uSecond := uSecond.toNat)
    (uRest := Modexp.wordLimbsToNat uRest)
    (divisor := Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]))
    (window := Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]))
    (by norm_num [UInt256.size]) hscale final.qHat.val.isLt hqPos final.rHat.val.isLt
    vSecond.val.isLt hvRest huRest hfinalEstimate hrefineNat hoverflowNat
    hdivisor hwindow
  have hreturned := qhatAdvance_qHat_toNat vTop final hqPos
  simpa only [final, hreturned] using hbounds

end Modexp.MultiLimbSchoolbookQhatSemantic
