import Benchmarks.ActAmm4.SwapOutputErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4SwapRecipientErrorTextWord : UInt256 :=
  ⟨33214008156304899519218583759897427912137402410168225116503634110448933011456⟩

theorem amm4SwapRecipientErrorTextStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5840⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret R
      ((UInt256.toByteArray amm4SwapRecipientErrorTextWord).write 0
        mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray amm4SwapRecipientErrorTextWord).write 0
    mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd5874 := RD.pushConst (evm_run h with [jumpdest])
    amm4SwapRecipientErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd := evm_run rd5874 with [
    push0, dup3, add,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rw [hptr0])
      (by rw [hptr0]) (by rw [hptr0]) (by evm_ov),
    pop, jump hret]
  exact ⟨_, _, rd⟩

theorem amm4SwapRecipientErrorPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5880⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray amm4SwapRecipientErrorTextWord).write 0
        ((UInt256.toByteArray (⟨10⟩ : UInt256)).write 0
          mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd5616 := evm_run h with [
    jumpdest, push0, push2 ⟨5892⟩, push1 ⟨10⟩,
    dup4, push2 ⟨5616⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5892⟩ := amm4ErrorWordStore rd5616
    (by jump_dest) (by simp; omega)
  have rd5840 := evm_run rd5892 with [
    jumpdest, swap2, pop, push2 ⟨5903⟩, dup3,
    push2 ⟨5840⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5903⟩ := amm4SwapRecipientErrorTextStore rd5840
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd5903 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

def amm4SwapRecipientErrorHeaderMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0
    mem ptr.toNat 32

def amm4SwapRecipientErrorPayloadMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨10⟩ : UInt256)).write 0
    (amm4SwapRecipientErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def amm4SwapRecipientErrorFinalMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amm4SwapRecipientErrorTextWord).write 0
    (amm4SwapRecipientErrorPayloadMem ptr mem)
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

theorem amm4SwapRecipientErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5914⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (amm4SwapRecipientErrorFinalMem ptr mem)
      (amm4MintErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := amm4SwapRecipientErrorHeaderMem ptr mem
  let aw1 := amm4MintErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd5928 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd5928
  have rd5929 := evm_run rd5928 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd5880 := evm_run rd5929 with [
    push2 ⟨5937⟩, dup2, push2 ⟨5880⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5937⟩ := amm4SwapRecipientErrorPayload rd5880
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd5937 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, by
    simpa [amm4SwapRecipientErrorFinalMem,
      amm4SwapRecipientErrorPayloadMem, amm4SwapRecipientErrorHeaderMem,
      amm4MintErrorFinalAw, amm4MintErrorPayloadAw,
      amm4MintErrorHeaderAw] using rdret⟩

end Benchmarks.ActAmm4
