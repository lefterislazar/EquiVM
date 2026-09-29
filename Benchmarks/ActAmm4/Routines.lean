import Benchmarks.ActAmm4.Common
import Reasoning.Stepping
import Reasoning.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

/-- Standard Solidity panic selector, left aligned in a 32 byte word. -/
def amm4PanicSelector : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def amm4PanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray amm4PanicSelector).write 0 mem 0 32

noncomputable def amm4PanicMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 (amm4PanicMem0 mem) 4 32

end Benchmarks.ActAmm4

namespace Reasoning.Reach
open Benchmarks.ActAmm4

/-- The repeated solc scratch-memory mapping hash suffix. -/
@[reducible] def amm4MappingHashSuffixWf (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  decode amm4Bytecode pc = some (.DUP2, .none)
  ∧ decode amm4Bytecode p1 = some (.MSTORE, .none)
  ∧ decode amm4Bytecode p2 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode amm4Bytecode p4 = some (.ADD, .none)
  ∧ decode amm4Bytecode p5 = some (.SWAP1, .none)
  ∧ decode amm4Bytecode p6 = some (.DUP2, .none)
  ∧ decode amm4Bytecode p7 = some (.MSTORE, .none)
  ∧ decode amm4Bytecode p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode amm4Bytecode p10 = some (.ADD, .none)
  ∧ decode amm4Bytecode p11 = some (.PUSH0, .none)
  ∧ decode amm4Bytecode p12 = some (.KECCAK256, .none)

macro "amm4_mapping_hash_wf" : term =>
  `(by
    unfold Reasoning.Reach.amm4MappingHashSuffixWf
    repeat' first | apply And.intro | native_decide)

@[reducible] def amm4MappingHashSuffixEndPc (pc : UInt256) : UInt256 :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p4 := p2 + UInt256.ofNat 2
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  p12 + ⟨1⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.amm4MappingHashSuffix {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc key baseSlot slot : UInt256} {R : List UInt256}
    {mem memKey memHash rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 pc (key :: ⟨0⟩ :: baseSlot :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwf : amm4MappingHashSuffixWf pc)
    (hkey : (UInt256.toByteArray key).write 0 mem 0 32 = memKey)
    (hbase : (UInt256.toByteArray baseSlot).write 0 memKey
      ((⟨32⟩ : UInt256) + ⟨0⟩).toNat 32 = memHash)
    (hslot : UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0
        ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨0⟩)).toNat))) = slot)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 (amm4MappingHashSuffixEndPc pc) (slot :: R)
      memHash (UInt256.ofNat 3) rdata acc k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10⟩
  have rd1 := h.dup2 hd0 (by evm_ov)
  have rd2 := rd1.mstore 0 memKey (UInt256.ofNat 3) hd1 mem_cost hkey
    (by native_decide) (by evm_ov)
  have rd3 := rd2.push1 ⟨32⟩ hd2 (by evm_ov)
  have rd4 := rd3.add hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.mstore 0 memHash (UInt256.ofNat 3) hd6 mem_cost hbase
    (by native_decide) (by evm_ov)
  have rd8 := rd7.push1 ⟨32⟩ hd7 (by evm_ov)
  have rd9 := rd8.add hd8 (by evm_ov)
  have rd10 := rd9.push0 hd9 (by evm_ov)
  exact ⟨_, _, rd10.keccak256 0 slot (UInt256.ofNat 3) hd10 mem_cost hslot
    (by native_decide) (by evm_ov)⟩

/-- Solc's shared identity cleanup for uint256 at PC 4677. -/
theorem RD.amm4RoutineCleanupUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4677⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD amm4Bytecode ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) :=
  evm_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump hret ]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
/-- Solidity's ABI uint256 identity check at PC 5499, used for returndata words. -/
theorem RD.amm4CheckUint256Identity {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4686⟩ (v :: ret :: v :: R) mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret (v :: R) mem aw rdata acc k' C' := by
  have rd4677 := evm_run h with [
    jumpdest, push2 ⟨4695⟩, dup2, push2 ⟨4677⟩, jump (by jump_dest)]
  have rd4695 := RD.amm4RoutineCleanupUint256 rd4677 (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have heq : UInt256.eq v v = ⟨1⟩ := u256_eq_refl v
  have rd4705 := evm_run rd4695 with [
    jumpdest, dup2, eq, push2 ⟨4705⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd4705 with [jumpdest, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- The shared ABI decoder for a full uint256 calldata word at PC 5521. -/
theorem RD.amm4DecodeUint256Ok {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4708⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata acc k' C' := by
  have rd4686 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨4722⟩, dup2, push2 ⟨4686⟩, jump (by jump_dest) ]
  have rd4695 := evm_run rd4686 with [
    jumpdest, push2 ⟨4695⟩, dup2, push2 ⟨4677⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest) ]
  have heq : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) = ⟨1⟩ :=
    u256_eq_refl _
  have rd4705 := evm_run rd4695 with [
    jumpdest, dup2, eq, push2 ⟨4705⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd4705 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked subtraction at PC 6645, successful branch. -/
theorem RD.amm4CheckedSubOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5253⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret (UInt256.sub a b :: R)
      mem aw rdata acc k' C' := by
  have rd5263₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5263⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest) ]
  have rd5263 := RD.amm4RoutineCleanupUint256 rd5263₀
    (by jump_dest) (by evm_ov)
  have rd5274₀ := evm_run rd5263 with [
    jumpdest, swap2, pop, push2 ⟨5274⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest) ]
  have rd5274 := RD.amm4RoutineCleanupUint256 rd5274₀
    (by jump_dest) (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsubNat]; omega)
  have rd6676 := evm_run rd5274 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd5298 := evm_run rd6676 with [
    iszero, push2 ⟨5298⟩,
    jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5298 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked addition at PC 6696, successful branch. -/
theorem RD.amm4CheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5304⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret ((a + b) :: R)
      mem aw rdata acc k' C' := by
  have rd5314₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5314⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest) ]
  have rd5314 := RD.amm4RoutineCleanupUint256 rd5314₀
    (by jump_dest) (by evm_ov)
  have rd5325₀ := evm_run rd5314 with [
    jumpdest, swap2, pop, push2 ⟨5325⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest) ]
  have rd5325 := RD.amm4RoutineCleanupUint256 rd5325₀
    (by jump_dest) (by evm_ov)
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgt : UInt256.gt a (a + b) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [haddNat]; omega)
  have rd6728 := evm_run rd5325 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd5349 := evm_run rd6728 with [
    iszero, push2 ⟨5349⟩,
    jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5349 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Shared Solidity checked-arithmetic panic revert at PC 6600. -/
theorem RD.amm4PanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5208⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have rd5209 := evm_run h with [jumpdest]
  have rd5242 := rd5209.pushConst amm4PanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd6641 := evm_run rd5242 with [
    push0,
    raw mstore 0 (amm4PanicMem0 mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (amm4PanicMem mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd6644 := evm_run rd6641 with [push1 ⟨36⟩, push0]
  exact rd6644.rev 0 (by native_decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- The checked-arithmetic panic also works after external calls expand memory. -/
theorem RD.amm4PanicOverflowRevertWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5208⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 2 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
    change UInt256.ofNat (max aw.toNat 1) = aw
    rw [max_eq_left (by omega : 1 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM4 : UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hMrev : UInt256.ofNat (MachineState.M aw.toNat 0 36) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have rd5209 := evm_run h with [jumpdest]
  have rd5242 := rd5209.pushConst amm4PanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd6641 := evm_run rd5242 with [
    push0,
    raw mstore 0 (amm4PanicMem0 mem) aw
      (by native_decide) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hM0, Nat.sub_self])
      (by rfl) (by simpa using hM0) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (amm4PanicMem mem) aw
      (by native_decide) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨4⟩ : UInt256).toNat = 4 from rfl, hM4, Nat.sub_self])
      (by rfl) (by simpa using hM4) (by evm_ov) ]
  have rd6644 := evm_run rd6641 with [push1 ⟨36⟩, push0]
  exact rd6644.rev 0 (by native_decide) (by
    intro s hs hst
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (⟨36⟩ : UInt256).toNat = 36 from rfl,
      hMrev, Nat.sub_self]) (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked subtraction at PC 6645, underflow branch. -/
theorem RD.amm4CheckedSubUnderflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5253⟩ (a :: b :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have rd5263₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5263⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest) ]
  have rd5263 := RD.amm4RoutineCleanupUint256 rd5263₀
    (by jump_dest) (by evm_ov)
  have rd5274₀ := evm_run rd5263 with [
    jumpdest, swap2, pop, push2 ⟨5274⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest) ]
  have rd5274 := RD.amm4RoutineCleanupUint256 rd5274₀
    (by jump_dest) (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6676 := evm_run rd5274 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd5208 := evm_run rd6676 with [
    iszero, push2 ⟨5298⟩,
    jumpiNT (by decide),
    push2 ⟨5297⟩, push2 ⟨5208⟩, jump (by jump_dest) ]
  exact RD.amm4PanicOverflowRevert rd5208 (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked addition at PC 6696, overflow branch. -/
theorem RD.amm4CheckedAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5304⟩ (a :: b :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have rd5314₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5314⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest) ]
  have rd5314 := RD.amm4RoutineCleanupUint256 rd5314₀
    (by jump_dest) (by evm_ov)
  have rd5325₀ := evm_run rd5314 with [
    jumpdest, swap2, pop, push2 ⟨5325⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest) ]
  have rd5325 := RD.amm4RoutineCleanupUint256 rd5325₀
    (by jump_dest) (by evm_ov)
  have hsum : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hgt : UInt256.gt a (a + b) = ⟨1⟩ := by
    show UInt256.fromBool (decide (a > a + b)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show a.toNat > (a + b).toNat
      rw [haddNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6728 := evm_run rd5325 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd5208 := evm_run rd6728 with [
    iszero, push2 ⟨5349⟩,
    jumpiNT (by decide),
    push2 ⟨5348⟩, push2 ⟨5208⟩, jump (by jump_dest) ]
  exact RD.amm4PanicOverflowRevert rd5208 (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.amm4CheckedSubUnderflowWide {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5253⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hlt : a.toNat < b.toNat) (haw : 3 ≤ aw.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have rd5263₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5263⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest) ]
  have rd5263 := RD.amm4RoutineCleanupUint256 rd5263₀
    (by jump_dest) (by evm_ov)
  have rd5274₀ := evm_run rd5263 with [
    jumpdest, swap2, pop, push2 ⟨5274⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest) ]
  have rd5274 := RD.amm4RoutineCleanupUint256 rd5274₀
    (by jump_dest) (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6676 := evm_run rd5274 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd5208 := evm_run rd6676 with [
    iszero, push2 ⟨5298⟩,
    jumpiNT (by decide),
    push2 ⟨5297⟩, push2 ⟨5208⟩, jump (by jump_dest) ]
  exact RD.amm4PanicOverflowRevertWide rd5208 haw (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.amm4CheckedAddOverflowWide {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5304⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (haw : 3 ≤ aw.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have rd5314₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5314⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest) ]
  have rd5314 := RD.amm4RoutineCleanupUint256 rd5314₀
    (by jump_dest) (by evm_ov)
  have rd5325₀ := evm_run rd5314 with [
    jumpdest, swap2, pop, push2 ⟨5325⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest) ]
  have rd5325 := RD.amm4RoutineCleanupUint256 rd5325₀
    (by jump_dest) (by evm_ov)
  have hsum : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    rw [Nat.mod_eq_of_lt (by omega)]
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hgt : UInt256.gt a (a + b) = ⟨1⟩ := by
    show UInt256.fromBool (decide (a > a + b)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show a.toNat > (a + b).toNat
      rw [haddNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6728 := evm_run rd5325 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd5208 := evm_run rd6728 with [
    iszero, push2 ⟨5349⟩,
    jumpiNT (by decide),
    push2 ⟨5348⟩, push2 ⟨5208⟩, jump (by jump_dest) ]
  exact RD.amm4PanicOverflowRevertWide rd5208 haw (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Shared one-word uint256 ABI encoder at PC 4856, preserving scratch memory. -/
theorem RD.amm4RoutineEncodeUint256FromMem
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4856⟩ (⟨128⟩ :: val :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hret : (D_J amm4Bytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨4875⟩, push0, dup4, add, dup5, push2 ⟨4841⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨4850⟩, dup2, push2 ⟨4677⟩,
    jump (by jump_dest),
    raw amm4RoutineCleanupUint256 (by jump_dest) (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 memout (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    pop, pop,
    jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.amm4RoutineBoolCleanup {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4790⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J amm4Bytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret (UInt256.isZero (UInt256.isZero v) :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, dup2, iszero, iszero, swap1, pop, swap2, swap1, pop,
    jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.amm4RoutineEncodeBoolFromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4816⟩ (⟨128⟩ :: val :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0
      mem 128 32 = memout)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  have rd4790 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨4835⟩, push0, dup4, add, dup5, push2 ⟨4801⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨4810⟩, dup2, push2 ⟨4790⟩,
    jump (by jump_dest) ]
  obtain ⟨_, _, rd4810⟩ := RD.amm4RoutineBoolCleanup rd4790
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd4810 with [
    jumpdest, dup3,
    raw mstore 6 memout (UInt256.ofNat 5) (by native_decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]
          exact hmemout)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Shared address decoder, through the mask routine to the canonicality check. -/
theorem RD.amm4DecodeAddrMask {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4657⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ⟨4644⟩
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          solcAddrMask
        :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: ⟨4671⟩
        :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)
        :: off :: csize :: ret :: R) mem aw rdata acc k' C' := by
  have rd4635 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨4671⟩, dup2,
    push2 ⟨4635⟩, jump (by jump_dest) ]
  have rd4618 := evm_run rd4635 with [
    jumpdest, push2 ⟨4644⟩, dup2, push2 ⟨4618⟩, jump (by jump_dest) ]
  exact ⟨_, _, evm_run rd4618 with [
    jumpdest, push0, push2 ⟨4628⟩, dup3, push2 ⟨4587⟩, jump (by jump_dest),
    jumpdest, push0, push20 solcAddrMask, dup3, and, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest),
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Successful shared address decode returns the canonical calldata word. -/
theorem RD.amm4DecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4657⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
      < EVM.addressModulus)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd⟩ := RD.amm4DecodeAddrMask h hov
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨1⟩ := solcAddrCanon_eq hcanon
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨4654⟩, jumpiT (by rw [hclean]; decide) (by jump_dest),
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- A noncanonical address fails the shared decoder's equality check. -/
theorem RD.amm4DecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨4657⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  obtain ⟨_, _, rd⟩ := RD.amm4DecodeAddrMask h hov
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨4654⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ] :
    RDrev amm4Bytecode g s0)

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4CheckedMulConditionOk (a b : UInt256)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    UInt256.lor (UInt256.isZero a)
      (UInt256.eq b (UInt256.div (UInt256.mul a b) a)) = ⟨1⟩ := by
  by_cases ha : a = ⟨0⟩
  · subst a
    by_cases hb : b = ⟨0⟩
    · subst b
      decide
    · have heq : UInt256.eq b ⟨0⟩ = ⟨0⟩ := u256_eq_of_ne hb
      have hmul0 : UInt256.mul (⟨0⟩ : UInt256) b = ⟨0⟩ := by
        apply u256_inj
        simp [u256_mul_toNat]
      rw [hmul0, show UInt256.div (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ from by decide,
        show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide,
        heq]
      decide
  · have hapos : 0 < a.toNat := by
      have hz : a.toNat ≠ 0 := by
        intro hzero
        exact ha (uint256_toNat_eq_zero hzero)
      omega
    have hdiv : UInt256.div (UInt256.mul a b) a = b := by
      apply u256_inj
      rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
      exact Nat.mul_div_cancel_left b.toNat hapos
    rw [hdiv, u256_eq_refl]
    have hiz : UInt256.isZero a = ⟨0⟩ := by
      change UInt256.fromBool (a == ⟨0⟩) = ⟨0⟩
      rw [beq_false_of_ne ha]
      rfl
    rw [hiz]
    decide

theorem amm4CheckedMulConditionOverflow (a b : UInt256)
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.lor (UInt256.isZero a)
      (UInt256.eq b (UInt256.div (UInt256.mul a b) a)) = ⟨0⟩ := by
  have hapos : 0 < a.toNat := by
    by_contra h
    have hz : a.toNat = 0 := by omega
    norm_num [hz, UInt256.size] at hover
  have ha : a ≠ ⟨0⟩ := by
    intro h
    subst a
    norm_num at hapos
  have hquot : (UInt256.div (UInt256.mul a b) a).toNat < b.toNat := by
    rw [udiv_toNat]
    apply (Nat.div_lt_iff_lt_mul hapos).2
    rw [Nat.mul_comm]
    exact lt_of_lt_of_le (UInt256.mul a b).val.isLt hover
  have hne : b ≠ UInt256.div (UInt256.mul a b) a := by
    intro heq
    have hn := congrArg UInt256.toNat heq
    omega
  have heq : UInt256.eq b (UInt256.div (UInt256.mul a b) a) = ⟨0⟩ :=
    u256_eq_of_ne hne
  have hiz : UInt256.isZero a = ⟨0⟩ := by
    change UInt256.fromBool (a == ⟨0⟩) = ⟨0⟩
    rw [beq_false_of_ne ha]
    rfl
  rw [heq, hiz]
  decide

theorem RD.amm4CheckedMulToCondition {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5458⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ⟨5504⟩
      (UInt256.lor (UInt256.isZero a)
        (UInt256.eq b (UInt256.div (UInt256.mul a b) a)) ::
       UInt256.mul a b :: UInt256.mul a b :: a :: b :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd5468₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5468⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest)]
  have rd5468 := RD.amm4RoutineCleanupUint256 rd5468₀
    (by jump_dest) (by evm_ov)
  have rd5479₀ := evm_run rd5468 with [
    jumpdest, swap2, pop, push2 ⟨5479⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest)]
  have rd5479 := RD.amm4RoutineCleanupUint256 rd5479₀
    (by jump_dest) (by evm_ov)
  have rd5493₀ := evm_run rd5479 with [
    jumpdest, swap3, pop, dup3, dup3, mul, push2 ⟨5493⟩,
    dup2, push2 ⟨4677⟩, jump (by jump_dest)]
  have rd5493 := RD.amm4RoutineCleanupUint256 rd5493₀
    (by jump_dest) (by evm_ov)
  have rd5504 := evm_run rd5493 with [
    jumpdest, swap2, pop, dup3, dup3, div, dup5, eq, dup4, iszero, or]
  exact ⟨_, _, rd5504⟩

theorem RD.amm4CheckedMulOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5458⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret (UInt256.mul a b :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5504₀⟩ := RD.amm4CheckedMulToCondition h hov
  have rd5504 := rd5504₀
  rw [amm4CheckedMulConditionOk a b hfit] at rd5504
  have rd5516 := evm_run rd5504 with [
    push2 ⟨5516⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd5516 with [
    jumpdest, pop, swap3, swap2, pop, pop, jump hret]⟩

theorem RD.amm4CheckedMulOverflowWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5458⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 12 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  obtain ⟨_, _, rd5504₀⟩ := RD.amm4CheckedMulToCondition h hov
  have rd5504 := rd5504₀
  rw [amm4CheckedMulConditionOverflow a b hover] at rd5504
  have rd5208 := evm_run rd5504 with [
    push2 ⟨5516⟩, jumpiNT (by decide),
    push2 ⟨5515⟩, push2 ⟨5208⟩, jump (by jump_dest)]
  exact RD.amm4PanicOverflowRevertWide rd5208 haw (by evm_ov)


theorem RD.amm4CheckedDivToGuard {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5568⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ⟨5593⟩
      (b :: ⟨0⟩ :: a :: b :: ret :: R) mem aw rdata acc k' C' := by
  have rd5578₀ := evm_run h with [
    jumpdest, push0, push2 ⟨5578⟩, dup3, push2 ⟨4677⟩, jump (by jump_dest)]
  have rd5578 := RD.amm4RoutineCleanupUint256 rd5578₀
    (by jump_dest) (by evm_ov)
  have rd5589₀ := evm_run rd5578 with [
    jumpdest, swap2, pop, push2 ⟨5589⟩, dup4, push2 ⟨4677⟩,
    jump (by jump_dest)]
  have rd5589 := RD.amm4RoutineCleanupUint256 rd5589₀
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5589 with [jumpdest, swap3, pop, dup3]⟩

theorem RD.amm4CheckedDivOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5568⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hb : b ≠ ⟨0⟩)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret (UInt256.div a b :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd5593⟩ := RD.amm4CheckedDivToGuard h hov
  have rd5605 := evm_run rd5593 with [
    push2 ⟨5605⟩, jumpiT hb (by jump_dest)]
  exact ⟨_, _, evm_run rd5605 with [
    jumpdest, dup3, dup3, div, swap1, pop,
    swap3, swap2, pop, pop, jump hret]⟩

noncomputable def amm4PanicDivMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨18⟩ : UInt256)).write 0 (amm4PanicMem0 mem) 4 32

theorem RD.amm4PanicDivZeroRevertWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5523⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 2 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
    change UInt256.ofNat (max aw.toNat 1) = aw
    rw [max_eq_left (by omega : 1 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM4 : UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hMrev : UInt256.ofNat (MachineState.M aw.toNat 0 36) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have rd5209 := evm_run h with [jumpdest]
  have rd5242 := rd5209.pushConst amm4PanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd5249 := evm_run rd5242 with [
    push0,
    raw mstore 0 (amm4PanicMem0 mem) aw
      (by native_decide) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hM0, Nat.sub_self])
      (by rfl) (by simpa using hM0) (by evm_ov),
    push1 ⟨18⟩, push1 ⟨4⟩,
    raw mstore 0 (amm4PanicDivMem mem) aw
      (by native_decide) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨4⟩ : UInt256).toNat = 4 from rfl, hM4, Nat.sub_self])
      (by rfl) (by simpa using hM4) (by evm_ov) ]
  have rd5252 := evm_run rd5249 with [push1 ⟨36⟩, push0]
  exact rd5252.rev 0 (by native_decide) (by
    intro s hs hst
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
      List.getElem!_cons_zero, List.getElem!_cons_succ]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (⟨36⟩ : UInt256).toNat = 36 from rfl,
      hMrev, Nat.sub_self]) (by evm_ov)

theorem RD.amm4CheckedDivZeroWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD amm4Bytecode ee g s0 ⟨5568⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hb : b = ⟨0⟩) (haw : 3 ≤ aw.toNat)
    (hov : R.length + 12 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  obtain ⟨_, _, rd5593₀⟩ := RD.amm4CheckedDivToGuard h hov
  have rd5593 := rd5593₀
  rw [hb] at rd5593
  have rd5523 := evm_run rd5593 with [
    push2 ⟨5605⟩, jumpiNT (by decide),
    push2 ⟨5604⟩, push2 ⟨5523⟩, jump (by jump_dest)]
  exact RD.amm4PanicDivZeroRevertWide rd5523 haw (by evm_ov)


end Reasoning.Reach

namespace Benchmarks.ActAmm4

-- LIBRARY CANDIDATE: Reasoning.Memory, one-word ABI return from 96-byte scratch memory.
noncomputable def amm4WordReturnMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem amm4WordReturnMem_size_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (amm4WordReturnMem mem val).size = 160 := by
  unfold amm4WordReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hmem]; omega)
      (by rw [hmem]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hmem,
    ByteArray_zeroes_size, toByteArray_size]

theorem amm4WordReturnMem_read64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (amm4WordReturnMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4WordReturnMem
  rw [toByteArray_write_read_below_of_gap val mem 128 64
    (by rw [hmem]) (by omega)
    (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread

theorem amm4WordReturnMem_mload64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (amm4WordReturnMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((amm4WordReturnMem mem val).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [amm4WordReturnMem_size_of_size96 val hmem]; decide)
    (by decide) (by simpa using amm4WordReturnMem_read64_of_size96 val hmem hread)

theorem amm4WordReturnMem_read128_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (amm4WordReturnMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold amm4WordReturnMem
  exact toByteArray_write_read_back_of_gap val mem 128
    (by rw [hmem]; exact lt_usize _ (by norm_num))

end Benchmarks.ActAmm4
