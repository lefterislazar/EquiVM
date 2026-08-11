import Examples.Precompiles.Modexp.MultiLimbSchoolbookZeroContract

/-!
# Complete all-zero `schoolbookDiv` execution

This module composes the generated arbitrary-length leading-zero scan with the concrete
zero-dividend allocation/return contract.  It is needed for nonempty base byte strings whose
converted limbs are all zero; treating only the declared empty-base case would miss these valid
inputs and would avoid byte conversion and division dispatch.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookZeroFunction

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def totalSteps (dividendCount : Nat) : Nat := 78 + 72 * dividendCount

def totalGas (aw : UInt256) (fp dividendCount : Nat) : Nat :=
  89 + 270 * dividendCount +
    MultiLimbSchoolbookShort.shortAllocationGas aw fp

/-- Execute `schoolbookDiv` when all `dividendCount` allocated limbs are zero. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp dividendCount : Nat} {tail : List UInt256}
    {rem dividend ret count divisor : UInt256}
    (hcountBound : dividendCount ≤ 32)
    (hheader : MultiLimbSchoolbookTrim.dividendHeader mem aw dividend =
      UInt256.ofNat dividendCount)
    (hheaderAw : MultiLimbSchoolbookTrim.dividendAfterHeader aw dividend = aw)
    (helementAw : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendAfterWord aw dividend i = aw)
    (hzero : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendWord mem aw dividend i = ⟨0⟩)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1007)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (rem :: UInt256.ofNat dividendCount :: dividend :: ret :: count :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (rem :: UInt256.ofNat fp :: tail)
      (MultiLimbSchoolbookZero.allocatedMemory mem fp)
      (MultiLimbSchoolbookZero.allocatedWords aw fp)
      rdata acc (steps + totalSteps dividendCount)
      (gasUsed + totalGas aw fp dividendCount) := by
  have rd5201 := MultiLimbSchoolbookTrim.entryThroughZeroCycles
    (start := 0) (n := dividendCount)
    (tail := ret :: count :: divisor :: tail)
    (by simp only [List.length_cons]; omega) (by omega)
    (by simpa using hheader) hheaderAw
    (fun i _ hi => helementAw i (by omega))
    (fun i _ hi => hzero i (by omega)) (by simpa using h)
  have rd5229 := MultiLimbSchoolbookTrim.zeroLengthExit
    (tail := ret :: count :: divisor :: tail)
    (by simp only [List.length_cons]; omega) rd5201
  have rdret := MultiLimbSchoolbookZero.exact
    (fp := fp) (tail := tail) hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by omega) hret rd5229
  have normalized := rdret.withIndices
    (k' := steps + totalSteps dividendCount)
    (C' := gasUsed + totalGas aw fp dividendCount)
    (by simp [totalSteps]; omega)
    (by simp [totalGas, MultiLimbSchoolbookZero.totalGas]; omega)
  exact normalized

end Modexp.MultiLimbSchoolbookZeroFunction
