import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisionContract

/-!
# Complete Knuth q-hat estimate paths

These contracts compose the deployed estimate selection, 512-by-256 helper, second-limb loads,
generated refinement loop, and multiply-subtract setup.  The explicit refinement path is an
arithmetic execution certificate: every state is connected by the proved generated cycle, so no
estimate or loop iteration is replaced by an abstract callback.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookEstimateFunction

open MultiLimbSchoolbookNormalization MultiLimbSchoolbookDivision

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

variable {normalizationMarker : UInt256}

/-- From an initial `(qHat,rHat)`, execute second-limb setup, every refinement cycle, and the
common multiply-subtract initialization. -/
theorem refinedExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {rHat qHat vTop u shift ret rem v quotient vSecond uSecond : UInt256}
    (hkEffTwo : 2 ≤ kEff) (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
    (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
      ⟨qHat, rHat⟩ states)
    (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
      (MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states).qHat
      (MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states).rHat
      vSecond uSecond = ⟨0⟩)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5792⟩
      (v :: UInt256.ofNat kEff :: rHat :: vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: qHat :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let final := MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: final.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 172)
        (C + 185 * states.length + 581) := by
  have rd8511 := refinementSetupExact hkEffTwo hkEffWord hindexWord huCountWord huIndex
    hvHeader hvHeaderAw hvSecondAw hvSecond huHeader huHeaderAw huSecondAw huSecond
    (by omega) h
  have rd5846 := qhatPathReturnExact ⟨qHat, rHat⟩ path hdone (by omega) rd8511
  have rd5563 := multiplySubtractSetupExact (by omega) rd5846
  exact rd5563.withIndices (by omega) (by omega)

/-- From an initial `(qHat,rHat)`, execute second-limb setup and the source-level overflow break
after its required decrement, then initialize multiply-subtract with that decremented estimate. -/
theorem refinedOverflowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {rHat qHat vTop u shift ret rem v quotient vSecond uSecond : UInt256}
    (hkEffTwo : 2 ≤ kEff) (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
    (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
      qHat rHat vSecond uSecond ≠ ⟨0⟩)
    (hoverflow :
      (MultiLimbDivisionTrace.qhatAdvance vTop ⟨qHat, rHat⟩).rHat.lt vTop ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5792⟩
      (v :: UInt256.ofNat kEff :: rHat :: vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: qHat :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let final := MultiLimbDivisionTrace.qhatAdvance vTop ⟨qHat, rHat⟩
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: final.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 192) (C + 648) := by
  have rd8511 := refinementSetupExact hkEffTwo hkEffWord hindexWord huCountWord huIndex
    hvHeader hvHeaderAw hvSecondAw hvSecond huHeader huHeaderAw huSecondAw huSecond
    (by omega) h
  have rd5846 := qhatOverflowReturnExact ⟨qHat, rHat⟩ hrefine hoverflow
    (by omega) rd8511
  have rd5563 := multiplySubtractSetupExact (by omega) rd5846
  exact rd5563.withIndices (by omega) (by omega)

/-- Execute an explicit non-overflowing refinement prefix followed by the overflow break, then
initialize multiply-subtract with the final decremented estimate. -/
theorem refinedPathOverflowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {rHat qHat vTop u shift ret rem v quotient vSecond uSecond : UInt256}
    (hkEffTwo : 2 ≤ kEff) (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
    (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
      ⟨qHat, rHat⟩ states)
    (hrefine : MultiLimbDivisionTrace.qhatNeedsRefinement
      (MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states).qHat
      (MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states).rHat
      vSecond uSecond ≠ ⟨0⟩)
    (hoverflow :
      (MultiLimbDivisionTrace.qhatAdvance vTop
        (MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states)).rHat.lt vTop ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5792⟩
      (v :: UInt256.ofNat kEff :: rHat :: vTop :: UInt256.ofNat jj ::
        UInt256.ofNat numQ :: qHat :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    let pathEnd := MultiLimbDivisionTrace.qhatPathEnd ⟨qHat, rHat⟩ states
    let final := MultiLimbDivisionTrace.qhatAdvance vTop pathEnd
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: final.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 192)
        (C + 185 * states.length + 648) := by
  have rd8511 := refinementSetupExact hkEffTwo hkEffWord hindexWord huCountWord huIndex
    hvHeader hvHeaderAw hvSecondAw hvSecond huHeader huHeaderAw huSecondAw huSecond
    (by omega) h
  have rd5846 := qhatPathOverflowReturnExact ⟨qHat, rHat⟩ path hrefine hoverflow
    (by omega) rd8511
  have rd5563 := multiplySubtractSetupExact (by omega) rd5846
  exact rd5563.withIndices (by omega) (by omega)

/-- Ordinary nonzero-high-word 512-by-256 estimate through refinement. -/
theorem ordinaryNonzeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {uHi vTop uLo u shift ret rem v quotient vSecond uSecond : UInt256}
    (hhi : uHi ≠ ⟨0⟩)
    (hkEffTwo : 2 ≤ kEff) (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size) (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
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
      vSecond uSecond = ⟨0⟩)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5869⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u :: shift ::
        ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    let final := MultiLimbDivisionTrace.qhatPathEnd
      ⟨MultiLimbDiv512.nonzeroQuotient uHi uLo vTop,
        MultiLimbDiv512.nonzeroRemainder uHi uLo vTop⟩ states
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: final.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 316)
        (C + 185 * states.length + 1090) := by
  have rd5882 := divEstimateNonzeroExact hhi (by omega) h
  have rd5792 := enterRefinementFromDivExact hkEffWord hkEffTwo (by omega) rd5882
  have rd5563 := refinedExact hkEffTwo hkEffWord hindexWord huCountWord huIndex
    hvHeader hvHeaderAw hvSecondAw hvSecond huHeader huHeaderAw huSecondAw huSecond
    path hdone hdepth rd5792
  exact rd5563.withIndices (by omega) (by omega)

/-- Ordinary zero-high-word estimate through refinement. -/
theorem ordinaryZeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {vTop uLo u shift ret rem v quotient vSecond uSecond : UInt256}
    (hkEffTwo : 2 ≤ kEff) (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size) (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
    (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
      ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states)
    (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
      (MultiLimbDivisionTrace.qhatPathEnd
        ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).qHat
      (MultiLimbDivisionTrace.qhatPathEnd
        ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states).rHat
      vSecond uSecond = ⟨0⟩)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5869⟩
      (⟨0⟩ :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u :: shift ::
        ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    let final := MultiLimbDivisionTrace.qhatPathEnd
      ⟨UInt256.div uLo vTop, UInt256.mod uLo vTop⟩ states
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: final.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 239)
        (C + 185 * states.length + 815) := by
  have rd5882 := divEstimateZeroExact (by omega) h
  have rd5792 := enterRefinementFromDivExact hkEffWord hkEffTwo (by omega) rd5882
  have rd5563 := refinedExact hkEffTwo hkEffWord hindexWord huCountWord huIndex
    hvHeader hvHeaderAw hvSecondAw hvSecond huHeader huHeaderAw huSecondAw huSecond
    path hdone hdepth rd5792
  exact rd5563.withIndices (by omega) (by omega)

/-- Saturated all-ones estimate with a nonwrapping `rHat = uLo + vTop`, through refinement. -/
theorem saturatedRefinementExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj numQ kEff uCount : Nat} {tail : List UInt256}
    {states : List MultiLimbDivisionTrace.QhatState}
    {uHi vTop uLo u shift ret rem v quotient vSecond uSecond : UInt256}
    (hsum : uLo.toNat + vTop.toNat < UInt256.size)
    (hkEffTwo : 2 ≤ kEff) (hkEffWord : kEff < UInt256.size)
    (hindexWord : jj + kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size) (huIndex : jj + kEff - 2 < uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hvSecondAw : arrayAfterWord aw v (kEff - 2) = aw)
    (hvSecond : arrayWord mem aw v (kEff - 2) = vSecond)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huSecondAw : arrayAfterWord aw u (jj + kEff - 2) = aw)
    (huSecond : arrayWord mem aw u (jj + kEff - 2) = uSecond)
    (path : MultiLimbDivisionTrace.QhatRefinementPath vTop vSecond uSecond
      ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states)
    (hdone : MultiLimbDivisionTrace.qhatNeedsRefinement
      (MultiLimbDivisionTrace.qhatPathEnd
        ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).qHat
      (MultiLimbDivisionTrace.qhatPathEnd
        ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states).rHat
      vSecond uSecond = ⟨0⟩)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5517⟩
      (uHi :: UInt256.ofNat jj :: vTop :: UInt256.ofNat numQ :: uLo :: u :: shift ::
        ret :: rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u ::
        vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    let final := MultiLimbDivisionTrace.qhatPathEnd
      ⟨(⟨0⟩ : UInt256).lnot, uLo + vTop⟩ states
    RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat numQ :: final.qHat :: shift :: ret ::
        rem :: UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc (k + 55 * states.length + 201)
        (C + 185 * states.length + 678) := by
  have rd5792 := saturatedEstimateRefinementExact hsum hkEffTwo hkEffWord
    (by omega) h
  have rd5563 := refinedExact hkEffTwo hkEffWord hindexWord huCountWord huIndex
    hvHeader hvHeaderAw hvSecondAw hvSecond huHeader huHeaderAw huSecondAw huSecond
    path hdone hdepth rd5792
  exact rd5563.withIndices (by omega) (by omega)

end Modexp.MultiLimbSchoolbookEstimateFunction
