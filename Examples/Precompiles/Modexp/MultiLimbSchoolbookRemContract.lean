import Examples.Precompiles.Modexp.MultiLimbOddConversionSemantic

/-!
# `schoolbookRem` caller and remainder allocation

This module covers the wrapper from PC 2279 through allocation of the `k`-limb remainder array,
ending at the `schoolbookDiv` entry at PC 5199.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookRem

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def allocatedMemory (mem : ByteArray) (fp words : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words

def allocatedWords (aw : UInt256) (fp words : Nat) : UInt256 :=
  newWordArrayWords aw fp words

/-- The two internal wrappers arrange the remainder length, dynamic returns, and division
arguments at the standard word-array allocator. -/
theorem allocationCallSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {dividend divisor count : UInt256}
    (hdepth : tail.length + 7 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨2279⟩
      (divisor :: count :: dividend :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (count :: ⟨5199⟩ :: count :: dividend :: ⟨2289⟩ :: count :: divisor :: tail)
      mem aw rdata acc (k + 15) (C + 51) := by
  have rd1487 := (evm_run h with [
    jumpdest,
    dup2,
    pushCanonical 2 .PUSH2 ⟨0x8f1⟩ (by decide),
    swap4,
    pushCanonical 2 .PUSH2 ⟨0x1442⟩ (by decide),
    jump (by native_decide),
    jumpdest,
    swap1,
    swap4,
    swap2,
    swap4,
    pushCanonical 2 .PUSH2 ⟨0x144f⟩ (by decide),
    dup5,
    pushCanonical 2 .PUSH2 ⟨0x5cf⟩ (by decide),
    jump (by native_decide)
  ])
  exact rd1487.withIndices (k' := k + 15) (C' := C + 51) (by omega) (by omega)

def entrySteps : Nat := 93

def entryGas (aw : UInt256) (fp words : Nat) : Nat :=
  51 + newWordArrayGas aw fp words

/-- Exact `schoolbookRem` wrapper and remainder allocation through the first instruction of
`schoolbookDiv`. -/
theorem entryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp words : Nat} {tail : List UInt256}
    {dividend divisor : UInt256}
    (hwords : words ≤ 32)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1007)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2279⟩
      (divisor :: UInt256.ofNat words :: dividend :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat fp :: UInt256.ofNat words :: dividend :: ⟨2289⟩ ::
        UInt256.ofNat words :: divisor :: tail)
      (allocatedMemory mem fp words) (allocatedWords aw fp words)
      rdata acc (k + entrySteps) (C + entryGas aw fp words) := by
  have rd1487 := allocationCallSetup (by omega) h
  have hret : (D_J runtimeBytecode 0).contains ⟨5199⟩ = true := by
    native_decide
  have rd5199 := newWordArrayExact hwords hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega) hret rd1487
  have normalized := rd5199.withIndices
    (k' := k + entrySteps) (C' := C + entryGas aw fp words)
    (by simp [entrySteps]) (by simp [entryGas]; omega)
  simpa only [allocatedMemory, allocatedWords] using normalized

end Modexp.MultiLimbSchoolbookRem
