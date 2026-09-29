import Benchmarks.ActAmm4.SwapInputErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4SwapKErrorTextWord : UInt256 :=
  ⟨33923463643744979127999312014264035503887690820011883995934839064818299699200⟩

theorem amm4SwapKErrorTextStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨6172⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret R
      ((UInt256.toByteArray amm4SwapKErrorTextWord).write 0
        mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray amm4SwapKErrorTextWord).write 0
    mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6206 := RD.pushConst (evm_run h with [jumpdest])
    amm4SwapKErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd := evm_run rd6206 with [
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

theorem amm4SwapKErrorPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨6212⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray amm4SwapKErrorTextWord).write 0
        ((UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
          mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd5616 := evm_run h with [
    jumpdest, push0, push2 ⟨6224⟩, push1 ⟨1⟩,
    dup4, push2 ⟨5616⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6224⟩ := amm4ErrorWordStore rd5616
    (by jump_dest) (by simp; omega)
  have rd6172 := evm_run rd6224 with [
    jumpdest, swap2, pop, push2 ⟨6235⟩, dup3,
    push2 ⟨6172⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6235⟩ := amm4SwapKErrorTextStore rd6172
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd6235 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

def amm4SwapKErrorHeaderMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0
    mem ptr.toNat 32

def amm4SwapKErrorPayloadMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0
    (amm4SwapKErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def amm4SwapKErrorFinalMem (ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amm4SwapKErrorTextWord).write 0
    (amm4SwapKErrorPayloadMem ptr mem)
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

theorem amm4SwapKErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨6246⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (amm4SwapKErrorFinalMem ptr mem)
      (amm4MintErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := amm4SwapKErrorHeaderMem ptr mem
  let aw1 := amm4MintErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6260 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd6260
  have rd6261 := evm_run rd6260 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6212 := evm_run rd6261 with [
    push2 ⟨6269⟩, dup2, push2 ⟨6212⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6269⟩ := amm4SwapKErrorPayload rd6212
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd6269 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, by
    simpa [amm4SwapKErrorFinalMem,
      amm4SwapKErrorPayloadMem, amm4SwapKErrorHeaderMem,
      amm4MintErrorFinalAw, amm4MintErrorPayloadAw,
      amm4MintErrorHeaderAw] using rdret⟩

end Benchmarks.ActAmm4
