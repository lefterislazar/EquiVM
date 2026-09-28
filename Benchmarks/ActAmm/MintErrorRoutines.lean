import Benchmarks.ActAmm.MintErrorTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammErrorWordStore {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {ptr val ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5941⟩ (ptr :: val :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret ((ptr + ⟨32⟩) :: R)
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

def ammMintErrorTextWord : UInt256 :=
  ⟨33213987989631693067883787898815039108018434811435553381060466162610651267072⟩

theorem ammMintErrorTextStore {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6061⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret R
      ((UInt256.toByteArray ammMintErrorTextWord).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray ammMintErrorTextWord).write 0 mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd6095 := RD.pushConst (evm_run h with [jumpdest])
    ammMintErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd := evm_run rd6095 with [
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

theorem ammMintErrorStringPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6101⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray ammMintErrorTextWord).write 0
        ((UInt256.toByteArray (⟨22⟩ : UInt256)).write 0 mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  let mem1 := (UInt256.toByteArray (⟨22⟩ : UInt256)).write 0 mem ptr.toNat 32
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mem2 := (UInt256.toByteArray ammMintErrorTextWord).write 0 mem1
    (ptr + ⟨32⟩).toNat 32
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (ptr + ⟨32⟩).toNat 32)
  have rd5941 := evm_run h with [
    jumpdest, push0, push2 ⟨6113⟩, push1 ⟨22⟩,
    dup4, push2 ⟨5941⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6113⟩ := ammErrorWordStore rd5941
    (by jump_dest) (by simp; omega)
  have rd6061 := evm_run rd6113 with [
    jumpdest, swap2, pop, push2 ⟨6124⟩, dup3,
    push2 ⟨6061⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6124⟩ := ammMintErrorTextStore rd6061
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd6124 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

def ammMintErrorHeaderMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0 mem ptr.toNat 32

def ammMintErrorPayloadMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨22⟩ : UInt256)).write 0
    (ammMintErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def ammMintErrorFinalMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ammMintErrorTextWord).write 0
    (ammMintErrorPayloadMem ptr mem) ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

def ammMintErrorHeaderAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def ammMintErrorPayloadAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammMintErrorHeaderAw ptr aw).toNat
    (ptr + ⟨32⟩).toNat 32)

def ammMintErrorFinalAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammMintErrorPayloadAw ptr aw).toNat
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32)

theorem ammMintErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6135⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (ammMintErrorFinalMem ptr mem) (ammMintErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := ammMintErrorHeaderMem ptr mem
  let aw1 := ammMintErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6149 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd6149
  have rd6150 := evm_run rd6149 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6101 := evm_run rd6150 with [
    push2 ⟨6158⟩, dup2, push2 ⟨6101⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6158⟩ := ammMintErrorStringPayload rd6101
    (by jump_dest) (by simp; omega)
  have rdret := evm_run rd6158 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]
  exact ⟨_, _, rdret⟩

theorem ammMintErrorRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨4102⟩ (endPtr :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  let off : UInt256 := ⟨64⟩
  let loadval : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off.toNat 32))
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd4105 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd4106 := RD.mload mcost loadval awout rd4105
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd4110 := evm_run rd4106 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd4110 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

end Benchmarks.ActAmm
