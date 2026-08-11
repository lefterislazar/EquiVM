import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisorExitContract

/-!
# Nonzero schoolbook scan prefix

This module composes both deployed leading-zero scans for the Barrett `reduceBase` caller. The
dividend may have any number of explicitly allocated high zero limbs; its effective top limb and
the converted modulus top limb are required to be nonzero concrete loads.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookNonzeroPrefix

open MultiLimbSchoolbookTrim
open MultiLimbSchoolbookDivisorTrim

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Execute the dividend trim, its positive-length transfer, and the nonzero divisor exit. -/
theorem exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed m zeroLimbs divisorCount dividendCount : Nat}
    {tail : List UInt256}
    {rem dividend ret divisor dividendTop divisorTop : UInt256}
    (hdepth : tail.length ≤ 1013)
    (hmPos : 0 < m)
    (hdividendCount : dividendCount = m + zeroLimbs)
    (hdivisorTwo : 2 ≤ divisorCount)
    (hdividendBound : dividendCount ≤ 65)
    (hdivisorBound : divisorCount ≤ 32)
    (hdividendHeader : dividendHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hdividendHeaderAw : dividendAfterHeader aw dividend = aw)
    (hzeroAw : ∀ i, m ≤ i -> i < m + zeroLimbs ->
      dividendAfterWord aw dividend i = aw)
    (hzero : ∀ i, m ≤ i -> i < m + zeroLimbs ->
      dividendWord mem aw dividend i = ⟨0⟩)
    (hdividendTopAw : dividendAfterWord aw dividend (m - 1) = aw)
    (hdividendTop : dividendWord mem aw dividend (m - 1) = dividendTop)
    (hdividendTopNonzero : dividendTop ≠ ⟨0⟩)
    (hdivisorHeader : divisorHeader mem aw divisor = UInt256.ofNat divisorCount)
    (hdivisorHeaderAw : divisorAfterHeader aw divisor = aw)
    (hdivisorTopAw : divisorAfterWord aw divisor (divisorCount - 1) = aw)
    (hdivisorTop : divisorWord mem aw divisor (divisorCount - 1) = divisorTop)
    (hdivisorTopNonzero : divisorTop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5199⟩
      (rem :: UInt256.ofNat dividendCount :: dividend :: ret ::
        UInt256.ofNat divisorCount :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨5266⟩
      (UInt256.ofNat divisorCount :: rem :: dividend :: ret :: UInt256.ofNat m ::
        divisor :: tail)
      mem aw rdata acc (steps + 118 + 72 * zeroLimbs)
      (gasUsed + 431 + 270 * zeroLimbs) := by
  subst dividendCount
  have rd5201 := entryThroughZeroCycles
    (tail := ret :: UInt256.ofNat divisorCount :: divisor :: tail)
    (start := m) (n := zeroLimbs) (by simp only [List.length_cons]; omega)
    hdividendBound hdividendHeader hdividendHeaderAw hzeroAw hzero h
  have rd5229 := MultiLimbSchoolbookTrim.nonzeroExit
    (remaining := m - 1) (count := m + zeroLimbs)
    (value := dividendTop)
    (tail := ret :: UInt256.ofNat divisorCount :: divisor :: tail)
    (by simp only [List.length_cons]; omega) (by omega) hdividendBound hdividendHeader
    hdividendHeaderAw hdividendTopAw hdividendTop hdividendTopNonzero (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using rd5201)
  have hmWord : UInt256.ofNat m ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    have hsize : 65 < UInt256.size := by native_decide
    rw [UInt256.toNat_ofNat_of_lt (by omega : m < UInt256.size)] at hzNat
    norm_num at hzNat
    exact (Nat.ne_of_gt hmPos) hzNat
  have rd5229' : RDx runtimeBytecode ee g s0 ⟨5229⟩
      (UInt256.ofNat m :: rem :: dividend :: ret :: UInt256.ofNat divisorCount ::
        divisor :: tail)
      mem aw rdata acc (steps + 2 + 72 * zeroLimbs + 55)
        (gasUsed + 4 + 270 * zeroLimbs + 202) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using rd5229
  have rd5237 := positiveLengthToDivisorTrim (by omega) hmWord rd5229'
  have rd5237' : RDx runtimeBytecode ee g s0 ⟨5237⟩
      (UInt256.ofNat (divisorCount - 1 + 1) :: rem :: dividend :: ret ::
        UInt256.ofNat m :: divisor :: tail)
      mem aw rdata acc (steps + 2 + 72 * zeroLimbs + 55 + 6)
        (gasUsed + 4 + 270 * zeroLimbs + 202 + 23) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ divisorCount)] using rd5237
  have rd5266 := MultiLimbSchoolbookDivisorExit.nonzeroExit
    (tail := tail) (top := divisorCount - 1) (count := divisorCount) (value := divisorTop)
    (by omega) (by omega) (by omega) hdivisorBound
    hdivisorHeader hdivisorHeaderAw hdivisorTopAw hdivisorTop hdivisorTopNonzero (by
      exact rd5237')
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ divisorCount)] using
    rd5266.withIndices (by omega) (by omega)

/-- Executable PC selector for the deployed multi-limb dividend-size branch. -/
def sizeBranchPc (m divisorCount : Nat) : Nat :=
  if m < divisorCount then 6214 else 5287

/-- Expose the selected short-copy or Knuth cursor with exact common dispatch cost. -/
theorem selectedSizeBranchExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed m divisorCount : Nat} {tail : List UInt256}
    {rem dividend ret divisor : UInt256}
    (hdepth : tail.length ≤ 1013)
    (hm : m ≤ 65) (hdivisorTwo : 2 ≤ divisorCount)
    (hdivisorBound : divisorCount ≤ 32)
    (h : RDx runtimeBytecode ee g s0 ⟨5266⟩
      (UInt256.ofNat divisorCount :: rem :: dividend :: ret :: UInt256.ofNat m ::
        divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat (sizeBranchPc m divisorCount))
      (UInt256.ofNat divisorCount :: UInt256.ofNat m :: rem :: dividend :: ret ::
        divisor :: tail)
      mem aw rdata acc (steps + 16) (gasUsed + 60) := by
  have hsize : 65 < UInt256.size := by native_decide
  have rd5280 := multiLengthToSizeCheck (kEff := divisorCount) (tail := tail)
    (by omega) hdivisorTwo (by omega) h
  by_cases hshort : m < divisorCount
  · have rd6214 := shorterDividend (m := m) (kEff := divisorCount) (tail := tail)
      (by omega) hshort (by omega) (by omega) rd5280
    simpa [sizeBranchPc, hshort] using rd6214.withIndices (by omega) (by omega)
  · have rd5287 := sufficientDividend (m := m) (kEff := divisorCount) (tail := tail)
      (by omega) (by omega) (by omega) (by omega) rd5280
    simpa [sizeBranchPc, hshort] using rd5287.withIndices (by omega) (by omega)

/-- Both concrete leading-zero scans followed by the exposed size selector. -/
theorem exactToSelectedSizeBranch
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed m zeroLimbs divisorCount dividendCount : Nat}
    {tail : List UInt256}
    {rem dividend ret divisor dividendTop divisorTop : UInt256}
    (hdepth : tail.length ≤ 1013)
    (hmPos : 0 < m) (hdividendCount : dividendCount = m + zeroLimbs)
    (hdivisorTwo : 2 ≤ divisorCount)
    (hdividendBound : dividendCount ≤ 65) (hdivisorBound : divisorCount ≤ 32)
    (hdividendHeader : dividendHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hdividendHeaderAw : dividendAfterHeader aw dividend = aw)
    (hzeroAw : ∀ i, m ≤ i -> i < m + zeroLimbs ->
      dividendAfterWord aw dividend i = aw)
    (hzero : ∀ i, m ≤ i -> i < m + zeroLimbs ->
      dividendWord mem aw dividend i = ⟨0⟩)
    (hdividendTopAw : dividendAfterWord aw dividend (m - 1) = aw)
    (hdividendTop : dividendWord mem aw dividend (m - 1) = dividendTop)
    (hdividendTopNonzero : dividendTop ≠ ⟨0⟩)
    (hdivisorHeader : divisorHeader mem aw divisor = UInt256.ofNat divisorCount)
    (hdivisorHeaderAw : divisorAfterHeader aw divisor = aw)
    (hdivisorTopAw : divisorAfterWord aw divisor (divisorCount - 1) = aw)
    (hdivisorTop : divisorWord mem aw divisor (divisorCount - 1) = divisorTop)
    (hdivisorTopNonzero : divisorTop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5199⟩
      (rem :: UInt256.ofNat dividendCount :: dividend :: ret ::
        UInt256.ofNat divisorCount :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat (sizeBranchPc m divisorCount))
      (UInt256.ofNat divisorCount :: UInt256.ofNat m :: rem :: dividend :: ret ::
        divisor :: tail)
      mem aw rdata acc (steps + 134 + 72 * zeroLimbs)
      (gasUsed + 491 + 270 * zeroLimbs) := by
  have rd5266 := exact hdepth hmPos hdividendCount hdivisorTwo hdividendBound
    hdivisorBound hdividendHeader hdividendHeaderAw hzeroAw hzero hdividendTopAw
    hdividendTop hdividendTopNonzero hdivisorHeader hdivisorHeaderAw hdivisorTopAw
    hdivisorTop hdivisorTopNonzero h
  have rdSelected := selectedSizeBranchExact hdepth (by omega) hdivisorTwo
    hdivisorBound rd5266
  exact rdSelected.withIndices (by omega) (by omega)

end Modexp.MultiLimbSchoolbookNonzeroPrefix
