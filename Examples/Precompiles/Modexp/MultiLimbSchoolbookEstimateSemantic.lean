import Examples.Precompiles.Modexp.MultiLimbSchoolbookEstimateSelector
import Examples.Precompiles.Modexp.MultiLimbSchoolbookQhatSemantic

/-!
# Arithmetic semantics of the closed q-hat selector

This module discharges the two Algorithm D estimate inequalities for every constructor of the
execution selector. Ordinary estimates derive their initial equation from the verified 512/256
division model; saturated estimates use the reduced-window invariant supplied by the outer loop.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookEstimateSemantic

open MultiLimbDivisionTrace
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookQhatSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem lnotZero_toNat :
    ((⟨0⟩ : UInt256).lnot).toNat = UInt256.size - 1 := by
  native_decide

/-- The verified nonzero 512/256 helper returns quotient and remainder satisfying the ordinary
division equation used to initialize refinement. -/
theorem nonzeroInitialEquation
    (uHi uLo vTop : UInt256)
    (hhi : uHi ≠ ⟨0⟩)
    (hlt : uHi.toNat < vTop.toNat)
    (hvTop : 1 < vTop.toNat) :
    uHi.toNat * UInt256.size + uLo.toNat =
      (MultiLimbDiv512.nonzeroQuotient uHi uLo vTop).toNat * vTop.toNat +
        (MultiLimbDiv512.nonzeroRemainder uHi uLo vTop).toNat := by
  have hq := MultiLimbDiv512.nonzeroQuotient_toNat uHi uLo vTop hhi hvTop hlt
  have hr := MultiLimbDiv512.nonzeroRemainder_toNat uHi uLo vTop hvTop
  have hsplit := Nat.mod_add_div (MultiLimbDiv512.numerator uHi uLo) vTop.toNat
  rw [hq, hr]
  dsimp only [MultiLimbDiv512.numerator] at hsplit ⊢
  nlinarith

theorem nonzeroInitialRemainderLt
    (uHi uLo vTop : UInt256) (hvTop : 1 < vTop.toNat) :
    (MultiLimbDiv512.nonzeroRemainder uHi uLo vTop).toNat < vTop.toNat := by
  rw [MultiLimbDiv512.nonzeroRemainder_toNat uHi uLo vTop hvTop]
  exact Nat.mod_lt _ (by omega)

/-- The zero-high-word helper is ordinary one-word division. -/
theorem zeroInitialEquation
    (uLo vTop : UInt256) (hvTop : 0 < vTop.toNat) :
    uLo.toNat = (UInt256.div uLo vTop).toNat * vTop.toNat +
      (UInt256.mod uLo vTop).toNat := by
  rw [udiv_toNat, umod_toNat (by omega)]
  have hsplit := Nat.mod_add_div uLo.toNat vTop.toNat
  nlinarith

theorem zeroInitialRemainderLt
    (uLo vTop : UInt256) (hvTop : 0 < vTop.toNat) :
    (UInt256.mod uLo vTop).toNat < vTop.toNat := by
  rw [umod_toNat (by omega)]
  exact Nat.mod_lt _ hvTop

/-- On the saturated branch the outer reduced-window invariant forces `uHi = vTop`; a
nonwrapping synthetic remainder then preserves the top-two-word equation exactly. -/
theorem saturatedInitialEquation
    (uHi uLo vTop : UInt256)
    (hge : vTop.toNat ≤ uHi.toNat)
    (hle : uHi.toNat ≤ vTop.toNat)
    (hsum : uLo.toNat + vTop.toNat < UInt256.size) :
    uHi.toNat * UInt256.size + uLo.toNat =
      ((⟨0⟩ : UInt256).lnot).toNat * vTop.toNat + (uLo + vTop).toNat := by
  have heq : uHi.toNat = vTop.toNat := by omega
  rw [uadd_toNat, Nat.mod_eq_of_lt hsum, lnotZero_toNat, heq]
  have hsize : UInt256.size = (UInt256.size - 1) + 1 := by
    norm_num [UInt256.size]
  conv_lhs => rw [hsize]
  ring

theorem saturatedNaturalEquation
    (uHi uLo vTop : UInt256)
    (hge : vTop.toNat ≤ uHi.toNat)
    (hle : uHi.toNat ≤ vTop.toNat) :
    uHi.toNat * UInt256.size + uLo.toNat =
      ((⟨0⟩ : UInt256).lnot).toNat * vTop.toNat +
        (uLo.toNat + vTop.toNat) := by
  have heq : uHi.toNat = vTop.toNat := by omega
  rw [lnotZero_toNat, heq]
  have hsize : UInt256.size = (UInt256.size - 1) + 1 := by
    norm_num [UInt256.size]
  conv_lhs => rw [hsize]
  ring

structure EstimateContext
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond : UInt256) : Prop where
  hlength : uRest.length = vRest.length
  hnormalized : UInt256.size ≤ 2 * vTop.toNat
  huHiLe : uHi.toNat ≤ vTop.toNat
  hsaturatedNeverLow :
    Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
      UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop])

/-- Every executable q-hat selector constructor satisfies the two arithmetic bounds consumed by
the accepted-window proof. -/
theorem validEstimateBounds
    {mem : ByteArray} {aw : UInt256}
    {jj cursor kEff uCount : Nat}
    {u shift ret rem v quotient normalizationMarker : UInt256}
    (vRest uRest : List UInt256)
    (vTop vSecond uHi uLo uSecond : UInt256)
    (result : EstimateResult)
    (context : EstimateContext vRest uRest vTop vSecond uHi uLo uSecond)
    (hvSecondWord : MultiLimbSchoolbookNormalization.arrayWord mem aw v (kEff - 2) =
      vSecond)
    (huSecondWord : MultiLimbSchoolbookNormalization.arrayWord mem aw u (jj + kEff - 2) =
      uSecond)
    (hvalid : ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v
      quotient normalizationMarker uHi result) :
    Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
        (result.qHat.toNat + 1) *
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ∧
      result.qHat.toNat * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) ≤
        Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) +
          Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
  have hvTopPos : 0 < vTop.toNat := by
    have hnormalized := context.hnormalized
    norm_num [UInt256.size] at hnormalized
    omega
  have hvTopTwo : 1 < vTop.toNat := by
    have hnormalized := context.hnormalized
    norm_num [UInt256.size] at hnormalized
    omega
  cases hvalid with
  | ordinaryNonzero caseHi caseVSecond caseUSecond states hlt hhi layout path hdone =>
      have hvEq : caseVSecond = vSecond := by
        rw [← layout.hvSecond, hvSecondWord]
      have huEq : caseUSecond = uSecond := by
        rw [← layout.huSecond, huSecondWord]
      subst caseVSecond
      subst caseUSecond
      have heq := nonzeroInitialEquation uHi uLo vTop hhi hlt hvTopTwo
      have hr := nonzeroInitialRemainderLt uHi uLo vTop hvTopTwo
      simpa only [EstimateResult.qHat] using
        (refinedWordPathEstimateBounds vRest uRest vTop vSecond uHi uLo uSecond
          ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
            MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states context.hlength
          hvTopPos context.hnormalized heq hr path hdone)
  | ordinaryZero caseVSecond caseUSecond states _ layout path hdone =>
      have hvEq : caseVSecond = vSecond := by
        rw [← layout.hvSecond, hvSecondWord]
      have huEq : caseUSecond = uSecond := by
        rw [← layout.huSecond, huSecondWord]
      subst caseVSecond
      subst caseUSecond
      have heq0 := zeroInitialEquation uLo vTop hvTopPos
      have heq :
          (⟨0⟩ : UInt256).toNat * UInt256.size + uLo.toNat =
            (UInt256.div uLo vTop).toNat * vTop.toNat +
              (UInt256.mod uLo vTop).toNat := by simpa using heq0
      have hr := zeroInitialRemainderLt uLo vTop hvTopPos
      simpa only [EstimateResult.qHat] using
        (refinedWordPathEstimateBounds vRest uRest vTop vSecond ⟨0⟩ uLo uSecond
          ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states context.hlength
          hvTopPos context.hnormalized heq hr path hdone)
  | ordinaryNonzeroOverflow caseHi caseVSecond caseUSecond states hlt hhi layout path
      hrefine hoverflow =>
      have hvEq : caseVSecond = vSecond := by
        rw [← layout.hvSecond, hvSecondWord]
      have huEq : caseUSecond = uSecond := by
        rw [← layout.huSecond, huSecondWord]
      subst caseVSecond
      subst caseUSecond
      have heq := nonzeroInitialEquation uHi uLo vTop hhi hlt hvTopTwo
      simpa only [EstimateResult.qHat] using
        (refinedWordPathOverflowEstimateBounds vRest uRest vTop vSecond uHi uLo
          uSecond ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
            MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states context.hlength
          heq path hrefine hoverflow)
  | ordinaryZeroOverflow caseVSecond caseUSecond states _ layout path hrefine hoverflow =>
      have hvEq : caseVSecond = vSecond := by
        rw [← layout.hvSecond, hvSecondWord]
      have huEq : caseUSecond = uSecond := by
        rw [← layout.huSecond, huSecondWord]
      subst caseVSecond
      subst caseUSecond
      have heq0 := zeroInitialEquation uLo vTop hvTopPos
      have heq :
          (⟨0⟩ : UInt256).toNat * UInt256.size + uLo.toNat =
            (UInt256.div uLo vTop).toNat * vTop.toNat +
              (UInt256.mod uLo vTop).toNat := by simpa using heq0
      simpa only [EstimateResult.qHat] using
        (refinedWordPathOverflowEstimateBounds vRest uRest vTop vSecond ⟨0⟩ uLo
          uSecond ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states context.hlength
          heq path hrefine hoverflow)
  | saturated caseHi caseVSecond caseUSecond states hge hsum layout path hdone =>
      have hvEq : caseVSecond = vSecond := by
        rw [← layout.hvSecond, hvSecondWord]
      have huEq : caseUSecond = uSecond := by
        rw [← layout.huSecond, huSecondWord]
      subst caseVSecond
      subst caseUSecond
      have heq := saturatedInitialEquation uHi uLo vTop hge context.huHiLe hsum
      have hnever :
          Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
            (((⟨0⟩ : UInt256).lnot).toNat + 1) *
              Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
        rw [lnotZero_toNat]
        norm_num [UInt256.size] at ⊢
        exact context.hsaturatedNeverLow
      simpa only [EstimateResult.qHat] using
        (refinedWordPathEstimateBoundsOfInitialNeverLow vRest uRest vTop vSecond
          uHi uLo uSecond ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states
          context.hlength hvTopPos context.hnormalized heq hnever path hdone)
  | saturatedOverflow caseHi caseVSecond caseUSecond states hge hsum layout path hrefine
      hoverflow =>
      have hvEq : caseVSecond = vSecond := by
        rw [← layout.hvSecond, hvSecondWord]
      have huEq : caseUSecond = uSecond := by
        rw [← layout.huSecond, huSecondWord]
      subst caseVSecond
      subst caseUSecond
      have heq := saturatedInitialEquation uHi uLo vTop hge context.huHiLe hsum
      simpa only [EstimateResult.qHat] using
        (refinedWordPathOverflowEstimateBounds vRest uRest vTop vSecond uHi uLo
          uSecond ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states context.hlength
          heq path hrefine hoverflow)
  | saturatedWrapped caseHi hge hwrap =>
      have hnever :
          Modexp.wordLimbsToNat (uRest ++ [uSecond, uLo, uHi]) <
            (((⟨0⟩ : UInt256).lnot).toNat + 1) *
              Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
        rw [lnotZero_toNat]
        norm_num [UInt256.size] at ⊢
        exact context.hsaturatedNeverLow
      have heq := saturatedNaturalEquation uHi uLo vTop hge context.huHiLe
      have hrefined :
          ((⟨0⟩ : UInt256).lnot).toNat * vSecond.toNat ≤
            (uLo.toNat + vTop.toNat) * UInt256.size + uSecond.toNat := by
        rw [lnotZero_toNat]
        have hvSecond := vSecond.val.isLt
        have hleft : (UInt256.size - 1) * vSecond.toNat <
            UInt256.size * UInt256.size := by
          calc
            (UInt256.size - 1) * vSecond.toNat <
                (UInt256.size - 1) * UInt256.size :=
              Nat.mul_lt_mul_of_pos_left hvSecond (by norm_num [UInt256.size])
            _ < UInt256.size * UInt256.size :=
              Nat.mul_lt_mul_of_pos_right (by norm_num [UInt256.size])
                (by norm_num [UInt256.size])
        have hright : UInt256.size * UInt256.size ≤
            (uLo.toNat + vTop.toNat) * UInt256.size :=
          Nat.mul_le_mul_right UInt256.size hwrap
        omega
      have hatMostOne := arbitraryWordEstimateAtMostOne vRest uRest vTop vSecond
        uHi uLo uSecond (⟨0⟩ : UInt256).lnot (uLo.toNat + vTop.toNat)
        context.hlength hvTopPos heq hrefined
      exact ⟨hnever, hatMostOne⟩

end Modexp.MultiLimbSchoolbookEstimateSemantic
