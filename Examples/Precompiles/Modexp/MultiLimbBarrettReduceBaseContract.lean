import Examples.Precompiles.Modexp.MultiLimbBarrettConversionContract
import Examples.Precompiles.Modexp.MultiLimbReduceBaseContract

/-!
# Barrett base-reduction call contract

This module connects the modulus-conversion continuation at PC 1700 to the independently proved
`reduceBase` implementation. The five-instruction call frame was also checked with
`symcheck run --pc 1700 --target-pc 2957`: it reached the target solver-free, with no
overapproximation, in five steps and 18 gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReduceBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- PC 1700 retains `n` below the `reduceBase` return frame and invokes the concrete helper. -/
theorem callExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {basePtr modulusPtr : UInt256} {k : Nat}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨1700⟩
      (modulusPtr :: UInt256.ofNat k :: ⟨1707⟩ :: basePtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨2957⟩
      (basePtr :: modulusPtr :: UInt256.ofNat k :: ⟨1707⟩ :: modulusPtr :: tail)
      mem aw rdata acc (steps + 5) (gasUsed + 18) := by
  have rd := evm_run h with [
    jumpdest,
    dup1,
    swap4,
    pushCanonical 2 .PUSH2 ⟨2957⟩ (by decide),
    jump (by native_decide)]
  exact rd.withIndices (by omega) (by omega)

/-- For a nonempty base, continue through the selected-width base conversion and the concrete
`k`-limb remainder allocation, stopping at the real `schoolbookDiv` entry. -/
theorem nonzeroToDivisionEntry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize k baseFp remFp : Nat} {tail : List UInt256}
    {basePtr modulusPtr : UInt256}
    (hdepth : tail.length ≤ 1002)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024) (hk : k ≤ 32)
    (hbaseAccess : basePtr.toNat + 32 ≤ 32 * aw.toNat)
    (hbaseLoad : wideLoadWord mem aw basePtr = UInt256.ofNat baseSize)
    (hbaseFp : 96 ≤ baseFp)
    (hbaseBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize k) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hbaseFree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat baseFp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseAccessAllocated : basePtr.toNat + 32 ≤
      32 * (MultiLimbReduceBase.baseAllocatedWords aw baseFp baseSize k).toNat)
    (hbaseLoadAllocated : wideLoadWord
      (MultiLimbReduceBase.baseAllocatedMemory mem baseFp baseSize k)
      (MultiLimbReduceBase.baseAllocatedWords aw baseFp baseSize k) basePtr =
        UInt256.ofNat baseSize)
    (hremFp : 96 ≤ remFp)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64)
    (hconvertedSize : 96 ≤
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hconvertedLe :
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k basePtr).size <
        USize.size)
    (hconvertedAw3 : 3 ≤
      (MultiLimbReduceBase.convertedWords mem aw baseFp baseSize k basePtr).toNat)
    (hconvertedAw64 : ¬ (⟨64⟩ : UInt256) ≥
      MultiLimbReduceBase.convertedWords mem aw baseFp baseSize k basePtr * ⟨32⟩)
    (hremFree :
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k basePtr).readWithPadding
          64 32 = UInt256.toByteArray (UInt256.ofNat remFp))
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
      (modulusPtr :: UInt256.ofNat k :: ⟨1707⟩ :: basePtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remFp :: UInt256.ofNat (MultiLimbReduceBase.baseWords baseSize k) ::
        UInt256.ofNat baseFp :: ⟨3010⟩ :: UInt256.ofNat k :: modulusPtr :: ⟨1707⟩ ::
        modulusPtr :: tail)
      (MultiLimbReduceBase.remainderMemory mem aw baseFp remFp baseSize k basePtr)
      (MultiLimbReduceBase.remainderWords mem aw baseFp remFp baseSize k basePtr)
      rdata acc (steps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize k)
      (gasUsed + 18 +
        MultiLimbReduceBase.nonzeroGas mem aw baseFp remFp baseSize k basePtr) := by
  have rd2957 := callExact (by omega) h
  have rd5199 := MultiLimbReduceBase.nonzeroToDivisionEntry
    (tail := modulusPtr :: tail) (ret := ⟨1707⟩)
    (by simp only [List.length_cons]; omega) hbasePos hbaseSize hk hbaseAccess hbaseLoad
    hbaseFp hbaseBound hmemSize hmemLe hbaseGap haw3 haw64 hbaseFree hcalldata
    hbaseAccessAllocated hbaseLoadAllocated hremFp hremBound hconvertedSize hconvertedLe
    hremGap hconvertedAw3 hconvertedAw64 hremFree rd2957
  exact rd5199.withIndices (by omega) (by omega)

end Modexp.MultiLimbBarrettReduceBase
