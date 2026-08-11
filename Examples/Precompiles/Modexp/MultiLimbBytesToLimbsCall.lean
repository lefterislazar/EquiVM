import Examples.Precompiles.Modexp.MultiLimbGenerated
import Examples.Precompiles.Modexp.BarrettWordCaller

/-!
# Backend-neutral `bytesToLimbs` caller contract

Both the Montgomery and Barrett backends call the same deployed helper.  Earlier proofs exposed
the arbitrary loop only after its PC 2857 guard, while the PC 2847 length-load wrapper remained
embedded in an odd-backend-specific theorem.  This file extracts that wrapper so Barrett can reuse
the generated arbitrary-length loop without duplicating its execution proof.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBytesToLimbsCall

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem shiftRight_div32 {n : Nat} (hn : n ≤ 1024) :
    UInt256.shiftRight (UInt256.ofNat n) ⟨5⟩ = UInt256.ofNat (n / 32) := by
  have hnWord : n < UInt256.size :=
    lt_trans (lt_of_le_of_lt hn (by decide : 1024 < 2 ^ 64)) (by decide)
  have hdivWord : n / 32 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_le_self n 32) hnWord
  apply u256_inj
  rw [shiftRight_toNat_of_lt256 _ _ (by decide),
    UInt256.toNat_ofNat_of_lt hnWord,
    show (⟨5⟩ : UInt256).toNat = 5 by decide,
    UInt256.toNat_ofNat_of_lt hdivWord]
  norm_num

/-- Execute the post-allocation wrapper up to the generic full-word loop head.  The memory access
premises say exactly that `dataPtr` is an active bytes object whose length word is `dataLen`. -/
theorem postAllocatorToLoopHead
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dataLen : Nat} {tail : List UInt256}
    {limbsPtr innerRet dataPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (haccess : dataPtr.toNat + 32 ≤ 32 * aw.toNat)
    (hload : wideLoadWord mem aw dataPtr = UInt256.ofNat dataLen)
    (h : RDx runtimeBytecode ee g s0 ⟨2847⟩
      (limbsPtr :: innerRet :: dataPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨2857⟩
      (MultiLimbGenerated.fullWordLoopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32))
        dataPtr (UInt256.ofNat dataLen) innerRet limbsPtr tail)
      mem aw rdata acc (steps + 9) (gasUsed + 24) := by
  have rd2850 := evm_run h with [jumpdest, swap2, dup1]
  have rd2851 := RDx.mloadWithin rd2850 (by native_decide) haccess
    (by simp only [List.length_cons]; omega)
  rw [hload] at rd2851
  have rd2857 := evm_run rd2851 with [
    swap1,
    dup2,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shr,
    push0]
  rw [shiftRight_div32 hlen] at rd2857
  simpa [MultiLimbGenerated.fullWordLoopStack, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using rd2857

/-- Complete `bytesToLimbs` from its post-allocation return point for every Osaka-valid byte
length, including zero full words and an optional partial word. -/
theorem postAllocatorComplete
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dataLen : Nat} {tail : List UInt256}
    {limbsPtr innerRet dataPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (haccess : dataPtr.toNat + 32 ≤ 32 * aw.toNat)
    (hload : wideLoadWord mem aw dataPtr = UInt256.ofNat dataLen)
    (hret : (D_J runtimeBytecode 0).contains innerRet = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2847⟩
      (limbsPtr :: innerRet :: dataPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 innerRet (limbsPtr :: tail)
      (MultiLimbGenerated.bytesToLimbsMemory mem aw dataPtr limbsPtr dataLen)
      (MultiLimbGenerated.bytesToLimbsActiveWords mem aw dataPtr limbsPtr dataLen)
      rdata acc
      (steps + 9 + MultiLimbGenerated.bytesToLimbsSteps dataLen)
      (gasUsed + 24 + MultiLimbGenerated.bytesToLimbsGas mem aw dataPtr limbsPtr dataLen) := by
  have rd2857 := postAllocatorToLoopHead hdepth hlen haccess hload h
  have rdDone := MultiLimbGenerated.bytesToLimbsTotalOfNat
    hdepth hlen hret rd2857
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdDone

end Modexp.MultiLimbBytesToLimbsCall
