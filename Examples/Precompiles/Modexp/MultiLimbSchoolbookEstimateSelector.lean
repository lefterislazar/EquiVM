import Examples.Precompiles.Modexp.MultiLimbSchoolbookEstimateFunction

/-!
# Complete schoolbook q-hat estimate selector

This module packages every deployed estimate route into a closed certificate and proves that each
certificate executes from the selector at PC 5516 to the common multiply-subtract cursor.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookEstimateSelector

open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookEstimateFunction

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

structure RefinementLayout
    (mem : ByteArray) (aw v u vSecond uSecond : UInt256)
    (jj kEff uCount : Nat) : Prop where
  hkEffTwo : 2 ≤ kEff
  hkEffWord : kEff < UInt256.size
  hindexWord : jj + kEff < UInt256.size
  huCountWord : uCount < UInt256.size
  huIndex : jj + kEff - 2 < uCount
  hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff
  hvHeaderAw : arrayAfterHeader aw v = aw
  hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw
  hvSecond : arrayWord mem aw v (kEff - 2) = vSecond
  huHeader : arrayHeader mem aw u = UInt256.ofNat uCount
  huHeaderAw : arrayAfterHeader aw u = aw
  huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw
  huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond

structure EstimateResult where
  qHat : UInt256
  steps : Nat
  gas : Nat

inductive ValidEstimate
    (mem : ByteArray) (aw : UInt256) (jj cursor kEff uCount : Nat)
    (vTop uLo u shift ret rem v quotient normalizationMarker : UInt256) :
    UInt256 → EstimateResult → Prop
  | ordinaryNonzero
      (uHi vSecond uSecond : UInt256)
      (states : List MultiLimbDivisionTrace.QhatState)
      (hlt : uHi.toNat < vTop.toNat)
      (hhi : uHi ≠ ⟨0⟩)
      (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount)
      (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
        ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
          MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states)
      (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
            MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states).qHat
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
            MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states).rHat
        vSecond uSecond = ⟨0⟩) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker uHi
        ⟨(MultiLimbDivisionTrace.qhatPathEnd
            ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
              MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states).qHat,
          55 * states.length + 317, 185 * states.length + 1100⟩
  | ordinaryZero
      (vSecond uSecond : UInt256)
      (states : List MultiLimbDivisionTrace.QhatState)
      (hlt : 0 < vTop.toNat)
      (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount)
      (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
        ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states)
      (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).qHat
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).rHat
        vSecond uSecond = ⟨0⟩) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker ⟨0⟩
        ⟨(MultiLimbDivisionTrace.qhatPathEnd
            ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).qHat,
          55 * states.length + 240, 185 * states.length + 825⟩
  | ordinaryNonzeroOverflow
      (uHi vSecond uSecond : UInt256)
      (states : List MultiLimbDivisionTrace.QhatState)
      (hlt : uHi.toNat < vTop.toNat)
      (hhi : uHi ≠ ⟨0⟩)
      (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount)
      (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
        ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
          MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states)
      (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
            MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states).qHat
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
            MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states).rHat
        vSecond uSecond ≠ ⟨0⟩)
      (hoverflow :
        (MultiLimbDivisionTrace.qhatAdvance vTop
          (MultiLimbDivisionTrace.qhatPathEnd
            ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
              MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states)).rHat.lt vTop ≠ ⟨0⟩) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker uHi
        ⟨(MultiLimbDivisionTrace.qhatAdvance vTop
            (MultiLimbDivisionTrace.qhatPathEnd
              ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
                MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states)).qHat,
          55 * states.length + 337, 185 * states.length + 1167⟩
  | ordinaryZeroOverflow
      (vSecond uSecond : UInt256)
      (states : List MultiLimbDivisionTrace.QhatState)
      (hlt : 0 < vTop.toNat)
      (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount)
      (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
        ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states)
      (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).qHat
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).rHat
        vSecond uSecond ≠ ⟨0⟩)
      (hoverflow :
        (MultiLimbDivisionTrace.qhatAdvance vTop
          (MultiLimbDivisionTrace.qhatPathEnd
            ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states)).rHat.lt vTop ≠ ⟨0⟩) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker ⟨0⟩
        ⟨(MultiLimbDivisionTrace.qhatAdvance vTop
            (MultiLimbDivisionTrace.qhatPathEnd
              ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states)).qHat,
          55 * states.length + 260, 185 * states.length + 892⟩
  | saturated
      (uHi vSecond uSecond : UInt256)
      (states : List MultiLimbDivisionTrace.QhatState)
      (hge : vTop.toNat ≤ uHi.toNat)
      (hsum : uLo.toNat + vTop.toNat < UInt256.size)
      (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount)
      (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
        ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states)
      (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).qHat
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).rHat
        vSecond uSecond = ⟨0⟩) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker uHi
        ⟨(MultiLimbDivisionTrace.qhatPathEnd
            ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).qHat,
          55 * states.length + 202, 185 * states.length + 688⟩
  | saturatedOverflow
      (uHi vSecond uSecond : UInt256)
      (states : List MultiLimbDivisionTrace.QhatState)
      (hge : vTop.toNat ≤ uHi.toNat)
      (hsum : uLo.toNat + vTop.toNat < UInt256.size)
      (layout : RefinementLayout mem aw v u vSecond uSecond jj kEff uCount)
      (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
        ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states)
      (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).qHat
        (MultiLimbDivisionTrace.qhatPathEnd
          ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).rHat
        vSecond uSecond ≠ ⟨0⟩)
      (hoverflow :
        (MultiLimbDivisionTrace.qhatAdvance vTop
          (MultiLimbDivisionTrace.qhatPathEnd
            ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states)).rHat.lt vTop ≠ ⟨0⟩) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker uHi
        ⟨(MultiLimbDivisionTrace.qhatAdvance vTop
            (MultiLimbDivisionTrace.qhatPathEnd
              ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states)).qHat,
          55 * states.length + 222, 185 * states.length + 755⟩
  | saturatedWrapped
      (uHi : UInt256)
      (hge : vTop.toNat ≤ uHi.toNat)
      (hwrap : UInt256.size ≤ uLo.toNat + vTop.toNat) :
      ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v quotient
        normalizationMarker uHi
        ⟨(⟨0⟩ : UInt256).lnot, 41, 125⟩

/-- Execute any certified deployed estimate route. -/
theorem estimateExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj cursor kEff uCount : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {result : EstimateResult}
    (hvalid : ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v
      quotient normalizationMarker uHi result)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat jj :: vTop ::
        UInt256.ofNat cursor :: uLo :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat cursor :: result.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  cases hvalid with
  | ordinaryNonzero uHi vSecond uSecond states hlt hhi layout path hdone =>
      have rd5869 := enterDivEstimateExact hlt (by omega) h
      have rd5563 := ordinaryNonzeroExact hhi layout.hkEffTwo layout.hkEffWord
        layout.hindexWord layout.huCountWord layout.huIndex layout.hvHeader
        layout.hvHeaderAw layout.hvSecondAw layout.hvSecond layout.huHeader
        layout.huHeaderAw layout.huSecondAw layout.huSecond path hdone hdepth rd5869
      have normalized := rd5563.withIndices
        (k' := k + (55 * states.length + 317))
        (C' := C + (185 * states.length + 1100)) (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized
  | ordinaryZero vSecond uSecond states hlt layout path hdone =>
      have hlt' : (⟨0⟩ : UInt256).toNat < vTop.toNat := by simpa using hlt
      have rd5869 := enterDivEstimateExact hlt' (by omega) h
      have rd5563 := ordinaryZeroExact layout.hkEffTwo layout.hkEffWord
        layout.hindexWord layout.huCountWord layout.huIndex layout.hvHeader
        layout.hvHeaderAw layout.hvSecondAw layout.hvSecond layout.huHeader
        layout.huHeaderAw layout.huSecondAw layout.huSecond path hdone hdepth rd5869
      have normalized := rd5563.withIndices
        (k' := k + (55 * states.length + 240))
        (C' := C + (185 * states.length + 825)) (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized
  | ordinaryNonzeroOverflow uHi vSecond uSecond states hlt hhi layout path hrefine
      hoverflow =>
      have rd5869 := enterDivEstimateExact hlt (by omega) h
      have rd5882 := divEstimateNonzeroExact hhi (by omega) rd5869
      have rd5792 := enterRefinementFromDivExact layout.hkEffWord layout.hkEffTwo
        (by omega) rd5882
      have rd5563 := refinedPathOverflowExact layout.hkEffTwo layout.hkEffWord
        layout.hindexWord layout.huCountWord layout.huIndex layout.hvHeader
        layout.hvHeaderAw layout.hvSecondAw layout.hvSecond layout.huHeader
        layout.huHeaderAw layout.huSecondAw layout.huSecond path hrefine hoverflow
        hdepth rd5792
      have normalized := rd5563.withIndices
        (k' := k + (55 * states.length + 337))
        (C' := C + (185 * states.length + 1167)) (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized
  | ordinaryZeroOverflow vSecond uSecond states hlt layout path hrefine hoverflow =>
      have hlt' : (⟨0⟩ : UInt256).toNat < vTop.toNat := by simpa using hlt
      have rd5869 := enterDivEstimateExact hlt' (by omega) h
      have rd5882 := divEstimateZeroExact (by omega) rd5869
      have rd5792 := enterRefinementFromDivExact layout.hkEffWord layout.hkEffTwo
        (by omega) rd5882
      have rd5563 := refinedPathOverflowExact layout.hkEffTwo layout.hkEffWord
        layout.hindexWord layout.huCountWord layout.huIndex layout.hvHeader
        layout.hvHeaderAw layout.hvSecondAw layout.hvSecond layout.huHeader
        layout.huHeaderAw layout.huSecondAw layout.huSecond path hrefine hoverflow
        hdepth rd5792
      have normalized := rd5563.withIndices
        (k' := k + (55 * states.length + 260))
        (C' := C + (185 * states.length + 892)) (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized
  | saturated uHi vSecond uSecond states hge hsum layout path hdone =>
      have rd5517 := enterSaturatedEstimateExact hge (by omega) h
      have rd5563 := saturatedRefinementExact hsum layout.hkEffTwo layout.hkEffWord
        layout.hindexWord layout.huCountWord layout.huIndex layout.hvHeader
        layout.hvHeaderAw layout.hvSecondAw layout.hvSecond layout.huHeader
        layout.huHeaderAw layout.huSecondAw layout.huSecond path hdone hdepth rd5517
      have normalized := rd5563.withIndices
        (k' := k + (55 * states.length + 202))
        (C' := C + (185 * states.length + 688)) (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized
  | saturatedOverflow uHi vSecond uSecond states hge hsum layout path hrefine hoverflow =>
      have rd5517 := enterSaturatedEstimateExact hge (by omega) h
      have rd5792 := saturatedEstimateRefinementExact hsum layout.hkEffTwo
        layout.hkEffWord (by omega) rd5517
      have rd5563 := refinedPathOverflowExact layout.hkEffTwo layout.hkEffWord
        layout.hindexWord layout.huCountWord layout.huIndex layout.hvHeader
        layout.hvHeaderAw layout.hvSecondAw layout.hvSecond layout.huHeader
        layout.huHeaderAw layout.huSecondAw layout.huSecond path hrefine hoverflow
        hdepth rd5792
      have normalized := rd5563.withIndices
        (k' := k + (55 * states.length + 222))
        (C' := C + (185 * states.length + 755)) (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized
  | saturatedWrapped uHi hge hwrap =>
      have rd5517 := enterSaturatedEstimateExact hge (by omega) h
      have rd5563 := saturatedEstimateWrappedExact hwrap (by omega) rd5517
      have normalized := rd5563.withIndices (k' := k + 41) (C' := C + 125)
        (by omega) (by omega)
      simpa only [EstimateResult.qHat, EstimateResult.steps, EstimateResult.gas] using normalized

end Modexp.MultiLimbSchoolbookEstimateSelector
