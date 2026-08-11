import Examples.Precompiles.Modexp.MultiLimbSchoolbookEstimateSemantic

/-!
# Constructive schoolbook estimate selection

The selector contracts expose explicit q-hat refinement paths so exact gas remains path-sensitive.
This module proves that a concrete path certificate always exists for a normalized divisor and
packages the bytecode's ordinary, saturated, and wrapping estimate branches.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookEstimateExecutable

open MultiLimbDivisionTrace
open MultiLimbSchoolbookEstimateSelector

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The two concrete ways in which the generated refinement loop can stop. -/
inductive QhatExitCertificate (vTop vSecond uSecond : UInt256) (initial : QhatState) : Prop
  | done (states : List QhatState)
      (path : QhatRefinementPath vTop vSecond uSecond initial states)
      (hdone : qhatNeedsRefinement (qhatPathEnd initial states).qHat
        (qhatPathEnd initial states).rHat vSecond uSecond = ⟨0⟩) :
      QhatExitCertificate vTop vSecond uSecond initial
  | overflow (states : List QhatState)
      (path : QhatRefinementPath vTop vSecond uSecond initial states)
      (hrefine : qhatNeedsRefinement (qhatPathEnd initial states).qHat
        (qhatPathEnd initial states).rHat vSecond uSecond ≠ ⟨0⟩)
      (hoverflow : (qhatAdvance vTop (qhatPathEnd initial states)).rHat.lt vTop ≠ ⟨0⟩) :
      QhatExitCertificate vTop vSecond uSecond initial

/-- Normalization bounds the generated refinement path to one successful decrement. Therefore
inspection of at most two refinement conditions constructs the exact normal or overflow exit. -/
theorem qhatExitCertificate_exists
    (vTop vSecond uSecond : UInt256) (initial : QhatState)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat) :
    QhatExitCertificate vTop vSecond uSecond initial := by
  by_cases hdone : qhatNeedsRefinement initial.qHat initial.rHat vSecond uSecond = ⟨0⟩
  · exact QhatExitCertificate.done [] (.nil initial) (by simpa [qhatPathEnd] using hdone)
  · by_cases hoverflow : (qhatAdvance vTop initial).rHat.lt vTop ≠ ⟨0⟩
    · exact QhatExitCertificate.overflow [] (.nil initial)
        (by simpa [qhatPathEnd] using hdone) (by simpa [qhatPathEnd] using hoverflow)
    · have hnoOverflow : (qhatAdvance vTop initial).rHat.lt vTop = ⟨0⟩ := by
        exact Classical.not_not.mp hoverflow
      let next := qhatAdvance vTop initial
      have pathOne : QhatRefinementPath vTop vSecond uSecond initial [next] := by
        exact .cons initial [] hdone hnoOverflow (.nil next)
      by_cases hnextDone : qhatNeedsRefinement next.qHat next.rHat vSecond uSecond = ⟨0⟩
      · exact QhatExitCertificate.done [next] pathOne (by
          simpa [qhatPathEnd, next] using hnextDone)
      · have hnextOverflow : (qhatAdvance vTop next).rHat.lt vTop ≠ ⟨0⟩ := by
          intro hnextNoOverflow
          have pathTwo : QhatRefinementPath vTop vSecond uSecond initial
              [next, qhatAdvance vTop next] := by
            exact .cons initial [qhatAdvance vTop next] hdone hnoOverflow
              (.cons next [] hnextDone hnextNoOverflow (.nil (qhatAdvance vTop next)))
          have hlength :=
            MultiLimbSchoolbookQhatSemantic.normalizedQhatRefinementPath_length_le_one
              pathTwo hnormalized
          simp at hlength
        exact QhatExitCertificate.overflow [next] pathOne
          (by simpa [qhatPathEnd, next] using hnextDone)
          (by simpa [qhatPathEnd, next] using hnextOverflow)

/-- Every concrete estimate selector state with a normalized divisor top has a closed execution
certificate. The returned existential contains the selected q-hat and its exact path gas. -/
theorem validEstimate_exists
    {mem : ByteArray} {aw : UInt256} {jj cursor kEff uCount : Nat}
    {vTop uLo u shift ret rem v quotient normalizationMarker vSecond uSecond : UInt256}
    (uHi : UInt256)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount) :
    ∃ result, ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v
      quotient normalizationMarker uHi result := by
  have hvTopPos : 0 < vTop.toNat := by
    norm_num [UInt256.size] at hnormalized
    omega
  by_cases hlt : uHi.toNat < vTop.toNat
  · by_cases hhi : uHi = ⟨0⟩
    · subst uHi
      let initial : QhatState := ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩
      cases qhatExitCertificate_exists vTop vSecond uSecond initial hnormalized with
      | done states path hdone =>
          exact ⟨_, ValidEstimate.ordinaryZero vSecond uSecond states hvTopPos layout
            path hdone⟩
      | overflow states path hrefine hoverflow =>
          exact ⟨_, ValidEstimate.ordinaryZeroOverflow vSecond uSecond states hvTopPos layout
            path hrefine hoverflow⟩
    · let initial : QhatState :=
        ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
          MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩
      cases qhatExitCertificate_exists vTop vSecond uSecond initial hnormalized with
      | done states path hdone =>
          exact ⟨_, ValidEstimate.ordinaryNonzero uHi vSecond uSecond states hlt hhi layout
            path hdone⟩
      | overflow states path hrefine hoverflow =>
          exact ⟨_, ValidEstimate.ordinaryNonzeroOverflow uHi vSecond uSecond states hlt hhi
            layout path hrefine hoverflow⟩
  · have hge : vTop.toNat ≤ uHi.toNat := by omega
    by_cases hsum : uLo.toNat + vTop.toNat < UInt256.size
    · let initial : QhatState := ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩
      cases qhatExitCertificate_exists vTop vSecond uSecond initial hnormalized with
      | done states path hdone =>
          exact ⟨_, ValidEstimate.saturated uHi vSecond uSecond states hge hsum layout
            path hdone⟩
      | overflow states path hrefine hoverflow =>
          exact ⟨_, ValidEstimate.saturatedOverflow uHi vSecond uSecond states hge hsum layout
            path hrefine hoverflow⟩
    · exact ⟨_, ValidEstimate.saturatedWrapped uHi hge (by omega)⟩

end Modexp.MultiLimbSchoolbookEstimateExecutable
