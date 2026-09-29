import Benchmarks.ActAmm4.SwapRecipientErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4SwapInputErrorTextWord : UInt256 :=
  ⟨33213987989631693067883787898814972641004042246872011148465414892047977938944⟩

theorem amm4SwapInputErrorTextStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨6068⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret R
      ((UInt256.toByteArray amm4SwapInputErrorTextWord).write 0
        mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray amm4SwapInputErrorTextWord).write 0
    mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6102 := RD.pushConst (evm_run h with [jumpdest])
    amm4SwapInputErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd := evm_run rd6102 with [
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

theorem amm4SwapInputErrorPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨6108⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray amm4SwapInputErrorTextWord).write 0
        ((UInt256.toByteArray (⟨25⟩ : UInt256)).write 0
          mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd5616 := evm_run h with [
    jumpdest, push0, push2 ⟨6120⟩, push1 ⟨25⟩,
    dup4, push2 ⟨5616⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6120⟩ := amm4ErrorWordStore rd5616
    (by jump_dest) (by simp; omega)
  have rd6068 := evm_run rd6120 with [
    jumpdest, swap2, pop, push2 ⟨6131⟩, dup3,
    push2 ⟨6068⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6131⟩ := amm4SwapInputErrorTextStore rd6068
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd6131 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

def amm4SwapInputErrorHeaderMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0
    mem ptr.toNat 32

def amm4SwapInputErrorPayloadMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨25⟩ : UInt256)).write 0
    (amm4SwapInputErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def amm4SwapInputErrorFinalMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amm4SwapInputErrorTextWord).write 0
    (amm4SwapInputErrorPayloadMem ptr mem)
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

theorem amm4SwapInputErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨6142⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (amm4SwapInputErrorFinalMem ptr mem)
      (amm4MintErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := amm4SwapInputErrorHeaderMem ptr mem
  let aw1 := amm4MintErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6156 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd6156
  have rd6157 := evm_run rd6156 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6108 := evm_run rd6157 with [
    push2 ⟨6165⟩, dup2, push2 ⟨6108⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6165⟩ := amm4SwapInputErrorPayload rd6108
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd6165 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, by
    simpa [amm4SwapInputErrorFinalMem,
      amm4SwapInputErrorPayloadMem, amm4SwapInputErrorHeaderMem,
      amm4MintErrorFinalAw, amm4MintErrorPayloadAw,
      amm4MintErrorHeaderAw] using rdret⟩

end Benchmarks.ActAmm4
