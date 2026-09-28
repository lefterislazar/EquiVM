import Benchmarks.ActAmm.Swap0SourceGuard
import Benchmarks.ActAmm.MintErrorRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def ammSwap0ErrorSelectorMem : ByteArray :=
  (UInt256.toByteArray ammMintErrorSelectorWord).write 0
    solcFreePtrMem 128 32

def ammSwap0ErrorSelectorAw : UInt256 :=
  UInt256.ofNat (MachineState.M 3 128 32)

theorem ammSwap0X_recipientErrorEnter
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1059⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨6239⟩
      [⟨128⟩ + ⟨4⟩, ⟨1108⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      ammSwap0ErrorSelectorMem ammSwap0ErrorSelectorAw ByteArray.empty
      (cA, σ) k' C' := by
  have rd1061 := evm_run rd with [push1 ⟨64⟩]
  obtain ⟨_, _, rd1062⟩ := ammMload64Wide rd1061
    (by native_decide)
    (by rw [solcFreePtrMem_size]; decide)
    solcFreePtrMem_read64 (by decide) (by decide) (by simp)
  have rd1095 := RD.pushConst rd1062 ammMintErrorSelectorWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by evm_ov)
  let memout := ammSwap0ErrorSelectorMem
  let awout := ammSwap0ErrorSelectorAw
  let mcost := Cₘ awout - Cₘ (UInt256.ofNat 3)
  have rd1097 := evm_run rd1095 with [
    dup2,
    raw mstore mcost memout awout (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6239 := evm_run rd1097 with [
    push1 ⟨4⟩, add, push2 ⟨1108⟩, swap1,
    push2 ⟨6239⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [ammSwap0ErrorSelectorMem, ammSwap0ErrorSelectorAw,
      u256_add_comm] using rd6239⟩

def ammSwap0ErrorTextWord : UInt256 :=
  ⟨33214008156304899519218583759897427912137402410168225116503634110448933011456⟩

theorem ammSwap0ErrorTextStore {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6165⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret R
      ((UInt256.toByteArray ammSwap0ErrorTextWord).write 0 mem ptr.toNat 32)
      (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32))
      rdata acc k' C' := by
  let memout := (UInt256.toByteArray ammSwap0ErrorTextWord).write 0
    mem ptr.toNat 32
  let awout := UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd6199 := RD.pushConst (evm_run h with [jumpdest])
    ammSwap0ErrorTextWord (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd := evm_run rd6199 with [
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

theorem ammSwap0ErrorStringPayload {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6205⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩) :: R)
      ((UInt256.toByteArray ammSwap0ErrorTextWord).write 0
        ((UInt256.toByteArray (⟨10⟩ : UInt256)).write 0 mem ptr.toNat 32)
        (ptr + ⟨32⟩).toNat 32)
      (UInt256.ofNat (MachineState.M
        (UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)).toNat
        (ptr + ⟨32⟩).toNat 32))
      rdata acc k' C' := by
  have rd5941 := evm_run h with [
    jumpdest, push0, push2 ⟨6217⟩, push1 ⟨10⟩,
    dup4, push2 ⟨5941⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6217⟩ := ammErrorWordStore rd5941
    (by jump_dest) (by simp; omega)
  have rd6165 := evm_run rd6217 with [
    jumpdest, swap2, pop, push2 ⟨6228⟩, dup3,
    push2 ⟨6165⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6228⟩ := ammSwap0ErrorTextStore rd6165
    (by jump_dest) (by simp; omega)
  exact ⟨_, _, evm_run rd6228 with [
    jumpdest, push1 ⟨32⟩, dup3, add, swap1, pop,
    swap2, swap1, pop, jump hret]⟩

def ammSwap0ErrorHeaderMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.sub (ptr + ⟨32⟩) ptr)).write 0
    mem ptr.toNat 32

def ammSwap0ErrorPayloadMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨10⟩ : UInt256)).write 0
    (ammSwap0ErrorHeaderMem ptr mem) (ptr + ⟨32⟩).toNat 32

def ammSwap0ErrorFinalMem (ptr : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ammSwap0ErrorTextWord).write 0
    (ammSwap0ErrorPayloadMem ptr mem)
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32

def ammSwap0ErrorHeaderAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def ammSwap0ErrorPayloadAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammSwap0ErrorHeaderAw ptr aw).toNat
    (ptr + ⟨32⟩).toNat 32)

def ammSwap0ErrorFinalAw (ptr aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammSwap0ErrorPayloadAw ptr aw).toNat
    ((ptr + ⟨32⟩) + ⟨32⟩).toNat 32)

theorem ammSwap0ErrorStringEncode {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {ptr ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6239⟩ (ptr :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (((ptr + ⟨32⟩) + ⟨32⟩ + ⟨32⟩) :: R)
      (ammSwap0ErrorFinalMem ptr mem) (ammSwap0ErrorFinalAw ptr aw)
      rdata acc k' C' := by
  let mem1 := ammSwap0ErrorHeaderMem ptr mem
  let aw1 := ammSwap0ErrorHeaderAw ptr aw
  let mcost := Cₘ aw1 - Cₘ aw
  have hptr0 : ptr + ⟨0⟩ = ptr := by rw [u256_add_comm, u256_zero_add]
  have rd6253 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add,
    swap1, pop, dup2, dup2, sub, push0, dup4, add]
  rw [hptr0] at rd6253
  have rd6254 := evm_run rd6253 with [
    raw mstore mcost mem1 aw1 (by native_decide)
      (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        rfl)
      (by rfl) (by rfl) (by evm_ov)]
  have rd6205 := evm_run rd6254 with [
    push2 ⟨6262⟩, dup2, push2 ⟨6205⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6262⟩ := ammSwap0ErrorStringPayload rd6205
    (by jump_dest) (by simp; omega)
  exact ⟨_, _, evm_run rd6262 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump hret]⟩

theorem ammSwap0ErrorRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : Nat} {endPtr : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨1108⟩ (endPtr :: R)
      mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  let off : UInt256 := ⟨64⟩
  let loadval : UInt256 :=
    if off.toNat ≥ mem.size ∨ off ≥ aw * ⟨32⟩ then ⟨0⟩
    else UInt256.ofNat (fromByteArrayBigEndian
      (mem.readWithPadding off.toNat 32))
  let awout := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  let mcost := Cₘ awout - Cₘ aw
  have rd1111 := evm_run h with [jumpdest, push1 ⟨64⟩]
  have rd1112 := RD.mload mcost loadval awout rd1111
    (by native_decide)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      rfl)
    (by rfl) (by rfl) (by simp; omega)
  have rd1116 := evm_run rd1112 with [dup1, swap2, sub, swap1]
  let revcost := Cₘ (UInt256.ofNat
    (MachineState.M awout.toNat loadval.toNat
      (UInt256.sub endPtr loadval).toNat)) - Cₘ awout
  exact RD.rev revcost rd1116 (by native_decide)
    (by
      intro s hs hst
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst, revcost])
    (by omega)

theorem ammSwap0X_recipientRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1059⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6239⟩ := ammSwap0X_recipientErrorEnter rd
  obtain ⟨_, _, rd1108⟩ := ammSwap0ErrorStringEncode rd6239
    (by jump_dest) (by simp)
  exact ammSwap0ErrorRevertTail rd1108 (by simp)

end Benchmarks.ActAmm
