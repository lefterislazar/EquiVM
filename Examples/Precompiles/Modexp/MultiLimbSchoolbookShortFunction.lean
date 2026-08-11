import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisorExitContract
import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortContract

/-!
# Complete short-dividend `schoolbookDiv` execution

This module composes both leading-zero scans with the already verified direct remainder-copy
implementation.  It covers every positive effective dividend shorter than a multi-limb divisor,
including arbitrary zero limbs above the dividend's most significant nonzero limb.  The theorem
retains the one-limb quotient allocation and every remainder-copy iteration.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookShortFunction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def totalSteps (m zeroLimbs : Nat) : Nat :=
  202 + 58 * m + 72 * zeroLimbs

def totalGas (aw : UInt256) (fp m zeroLimbs : Nat) : Nat :=
  540 + 208 * m + 270 * zeroLimbs +
    MultiLimbSchoolbookShort.shortAllocationGas aw fp

/-- Execute the complete positive short-dividend branch through the internal return. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp m zeroLimbs divisorCount : Nat} {tail : List UInt256}
    {rem dividend ret divisor dividendTop divisorTop : UInt256}
    (hmPos : 0 < m) (hdividendCount : m + zeroLimbs ≤ 32)
    (hdivisorTwo : 2 ≤ divisorCount) (hdivisorBound : divisorCount ≤ 32)
    (hshort : m < divisorCount)
    (hdividendHeader : MultiLimbSchoolbookTrim.dividendHeader mem aw dividend =
      UInt256.ofNat (m + zeroLimbs))
    (hdividendHeaderAw : MultiLimbSchoolbookTrim.dividendAfterHeader aw dividend = aw)
    (htrimAw : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendAfterWord aw dividend i = aw)
    (htrimZero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw dividend i = ⟨0⟩)
    (hdividendTopAw :
      MultiLimbSchoolbookTrim.dividendAfterWord aw dividend (m - 1) = aw)
    (hdividendTop :
      MultiLimbSchoolbookTrim.dividendWord mem aw dividend (m - 1) = dividendTop)
    (hdividendTopNonzero : dividendTop ≠ ⟨0⟩)
    (hdivisorHeader : MultiLimbSchoolbookDivisorTrim.divisorHeader mem aw divisor =
      UInt256.ofNat divisorCount)
    (hdivisorHeaderAw : MultiLimbSchoolbookDivisorTrim.divisorAfterHeader aw divisor = aw)
    (hdivisorTopAw : MultiLimbSchoolbookDivisorTrim.divisorAfterWord aw divisor
      (divisorCount - 1) = aw)
    (hdivisorTop : MultiLimbSchoolbookDivisorTrim.divisorWord mem aw divisor
      (divisorCount - 1) = divisorTop)
    (hdivisorTopNonzero : divisorTop ≠ ⟨0⟩)
    (hfp : 96 ≤ fp) (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdivHeader : ∀ i, i < m →
      MultiLimbSchoolbookShort.arrayHeader
          (MultiLimbSchoolbookShort.copyLoopMemory
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
            (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend rem i)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend =
            UInt256.ofNat (m + zeroLimbs))
    (hdivHeaderAw : MultiLimbSchoolbookShort.arrayAfterHeader
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (hdivElementAw : ∀ i, i < m → MultiLimbSchoolbookShort.arrayAfterWord
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend i =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (hremHeader : ∀ i, i < m →
      MultiLimbSchoolbookShort.arrayHeader
          (MultiLimbSchoolbookShort.copyLoopMemory
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
            (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend rem i)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rem =
            UInt256.ofNat divisorCount)
    (hremHeaderAw : MultiLimbSchoolbookShort.arrayAfterHeader
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rem =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (hremElementAw : ∀ i, i < m → MultiLimbSchoolbookShort.arrayAfterWord
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rem i =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (htail : tail.length ≤ 1007)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (rem :: UInt256.ofNat (m + zeroLimbs) :: dividend :: ret ::
        UInt256.ofNat divisorCount :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (rem :: UInt256.ofNat fp :: tail)
      (MultiLimbSchoolbookShort.copyLoopMemory
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend rem m)
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rdata acc
      (steps + totalSteps m zeroLimbs)
      (gasUsed + totalGas aw fp m zeroLimbs) := by
  have hmPred : m - 1 < m + zeroLimbs := by omega
  have rd5201 := MultiLimbSchoolbookTrim.entryThroughZeroCycles
    (start := m) (n := zeroLimbs)
    (tail := ret :: UInt256.ofNat divisorCount :: divisor :: tail)
    (by simp only [List.length_cons]; omega) (by omega) hdividendHeader
    hdividendHeaderAw htrimAw htrimZero h
  have hmAsSucc : m - 1 + 1 = m := by omega
  have rd5229 := MultiLimbSchoolbookTrim.nonzeroExit
    (remaining := m - 1) (count := m + zeroLimbs)
    (tail := ret :: UInt256.ofNat divisorCount :: divisor :: tail)
    (by simp only [List.length_cons]; omega) hmPred (by omega)
    hdividendHeader hdividendHeaderAw hdividendTopAw hdividendTop
    hdividendTopNonzero (by simpa [hmAsSucc] using rd5201)
  have rd5237 := MultiLimbSchoolbookTrim.positiveLengthToDivisorTrim
    (tail := tail) (by omega) (by
      intro hz
      have hzNat := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt (by
        have : 32 < UInt256.size := by decide
        omega)] at hzNat
      simp at hzNat) rd5229
  rw [hmAsSucc] at rd5237
  have hdivisorSucc : divisorCount - 1 + 1 = divisorCount := by omega
  have rd5266 := MultiLimbSchoolbookDivisorExit.nonzeroExit
    (top := divisorCount - 1) (count := divisorCount)
    (tail := tail) (by omega) (by omega) (by omega) hdivisorBound
    hdivisorHeader hdivisorHeaderAw hdivisorTopAw hdivisorTop
    hdivisorTopNonzero (by simpa [hdivisorSucc] using rd5237)
  rw [hdivisorSucc] at rd5266
  have hdivisorWord : divisorCount < UInt256.size := by
    have : 32 < UInt256.size := by decide
    omega
  have hmWord : m < UInt256.size := lt_trans hshort hdivisorWord
  have rd5280 := MultiLimbSchoolbookDivisorTrim.multiLengthToSizeCheck
    (kEff := divisorCount) (tail := tail) (by omega) hdivisorTwo hdivisorWord rd5266
  have rd6214 := MultiLimbSchoolbookDivisorTrim.shorterDividend
    (m := m) (kEff := divisorCount) (tail := tail)
    (by omega) hshort hmWord hdivisorWord rd5280
  have rdret := MultiLimbSchoolbookShort.executeThroughReturn
    (fp := fp) (m := m) (dividendCount := m + zeroLimbs)
    (remCount := divisorCount) (tail := tail)
    hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
    (by omega) (by omega) (by omega) hdividendCount hdivisorBound
    hdivHeader hdivHeaderAw hdivElementAw hremHeader hremHeaderAw
    hremElementAw hret rd6214
  have normalized := rdret.withIndices
    (k' := steps + totalSteps m zeroLimbs)
    (C' := gasUsed + totalGas aw fp m zeroLimbs)
    (by simp [totalSteps]; omega)
    (by simp [totalGas]; omega)
  exact normalized

end Modexp.MultiLimbSchoolbookShortFunction
