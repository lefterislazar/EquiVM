import Benchmarks.ActAmm4.MintErrorTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4ErrorWordStore {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {ptr val ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5616⟩ (ptr :: val :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret ((ptr + ⟨32⟩) :: R)
      ((UInt256.toByteArray val).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray val).write 0 mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd := evm_run h with [
    jumpdest, push0, dup3, dup3,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, dup3, add, swap1, pop,
    swap3, swap2, pop, pop, jump hret]
  exact ⟨_, _, rd⟩

def amm4MintErrorTextWord : UInt256 :=
  ⟨33213987989631693067883787898815039108018434811435553381060466162610651267072⟩

theorem amm4MintErrorTextStore {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5632⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret R
      ((UInt256.toByteArray amm4MintErrorTextWord).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray amm4MintErrorTextWord).write 0 mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd5666 := RD.pushConst (evm_run h with [jumpdest])
    amm4MintErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd := evm_run rd5666 with [
    push0, dup3, add,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rw [hptr0])
      (by rw [hptr0])
      (by rw [hptr0]) (by evm_ov),
    pop, jump hret]
  exact ⟨_, _, rd⟩

theorem amm4MintErrorStringPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5672⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray amm4MintErrorTextWord).write 0
        ((UInt256.toByteArray (⟨22⟩ : UInt256)).write 0 mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  let mem1 := (UInt256.toByteArray (⟨22⟩ : UInt256)).write 0 mem ptr.toNat 32
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mem2 := (UInt256.toByteArray amm4MintErrorTextWord).write 0 mem1
    (ptr + ⟨32⟩).toNat 32
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (ptr + ⟨32⟩).toNat 32)
  have rd5616 := evm_run h with [
    jumpdest, push0, push2 ⟨5684⟩, push1 ⟨22⟩,
    dup4, push2 ⟨5616⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5684⟩ := amm4ErrorWordStore rd5616
    (by jump_dest) (by simp; omega)
  have rd5632 := evm_run rd5684 with [
    jumpdest, swap2, pop, push2 ⟨5695⟩, dup3,
    push2 ⟨5632⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5695⟩ := amm4MintErrorTextStore rd5632
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd5695 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

def amm4MintErrorHeaderMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0 mem ptr.toNat 32

def amm4MintErrorPayloadMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨22⟩ : UInt256)).write 0
    (amm4MintErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def amm4MintErrorFinalMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amm4MintErrorTextWord).write 0
    (amm4MintErrorPayloadMem ptr mem) ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

def amm4MintErrorHeaderAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def amm4MintErrorPayloadAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4MintErrorHeaderAw ptr aw).toNat
    (ptr + ⟨32⟩).toNat 32)

def amm4MintErrorFinalAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4MintErrorPayloadAw ptr aw).toNat
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32)

theorem amm4MintErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5706⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (amm4MintErrorFinalMem ptr mem) (amm4MintErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := amm4MintErrorHeaderMem ptr mem
  let aw1 := amm4MintErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd5720 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd5720
  have rd5721 := evm_run rd5720 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd5672 := evm_run rd5721 with [
    push2 ⟨5729⟩, dup2, push2 ⟨5672⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5729⟩ := amm4MintErrorStringPayload rd5672
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd5729 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

theorem amm4MintErrorRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨1971⟩ (endPtr :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  let off : UInt256 := ⟨64⟩
  let loadval : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd1974 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd1975 := RD.mload mcost loadval awout rd1974
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd1979 := evm_run rd1975 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd1979 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

end Benchmarks.ActAmm4
