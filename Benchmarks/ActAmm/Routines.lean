import Benchmarks.ActAmm.Common
import Reasoning.Memory
import Reasoning.Stepping

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

/-- Standard Solidity panic selector, left-aligned in a 32-byte word. -/
def ammPanicSelector : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def ammPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray ammPanicSelector).write 0 mem 0 32

noncomputable def ammPanicMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 (ammPanicMem0 mem) 4 32
end Benchmarks.ActAmm

namespace Reasoning.Reach
open Benchmarks.ActAmm

/-- The repeated solc scratch-memory mapping hash suffix. -/
@[reducible] def ammMappingHashSuffixWf (pc : UInt256) : Prop :=
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
  decode ammBytecode pc = some (.DUP2, .none)
  ∧ decode ammBytecode p1 = some (.MSTORE, .none)
  ∧ decode ammBytecode p2 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode ammBytecode p4 = some (.ADD, .none)
  ∧ decode ammBytecode p5 = some (.SWAP1, .none)
  ∧ decode ammBytecode p6 = some (.DUP2, .none)
  ∧ decode ammBytecode p7 = some (.MSTORE, .none)
  ∧ decode ammBytecode p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode ammBytecode p10 = some (.ADD, .none)
  ∧ decode ammBytecode p11 = some (.PUSH0, .none)
  ∧ decode ammBytecode p12 = some (.KECCAK256, .none)

macro "amm_mapping_hash_wf" : term =>
  `(by
    unfold Reasoning.Reach.ammMappingHashSuffixWf
    repeat' first | apply And.intro | native_decide)

@[reducible] def ammMappingHashSuffixEndPc (pc : UInt256) : UInt256 :=
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
theorem RD.ammMappingHashSuffix {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc key baseSlot slot : UInt256} {R : List UInt256}
    {mem memKey memHash rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 pc (key :: ⟨0⟩ :: baseSlot :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwf : ammMappingHashSuffixWf pc)
    (hkey : (UInt256.toByteArray key).write 0 mem 0 32 = memKey)
    (hbase : (UInt256.toByteArray baseSlot).write 0 memKey
      ((⟨32⟩ : UInt256) + ⟨0⟩).toNat 32 = memHash)
    (hslot : UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0
        ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨0⟩)).toNat))) = slot)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 (ammMappingHashSuffixEndPc pc) (slot :: R)
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

/-- Solc's shared identity cleanup for uint256 at PC 5490. -/
theorem RD.ammRoutineCleanupUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5490⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true) (hov : R.length + 4 ≤ 1024) :
    RD ammBytecode ee g s0 ret (v :: R) mem aw rdata acc (k + 9) (C + 27) :=
  evm_run h with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump hret ]

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
/-- Solidity's ABI uint256 identity check at PC 5499, used for returndata words. -/
theorem RD.ammCheckUint256Identity {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5499⟩ (v :: ret :: v :: R) mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret (v :: R) mem aw rdata acc k' C' := by
  have rd5490 := evm_run h with [
    jumpdest, push2 ⟨5508⟩, dup2, push2 ⟨5490⟩, jump (by jump_dest)]
  have rd5508 := RD.ammRoutineCleanupUint256 rd5490 (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have heq : UInt256.eq v v = ⟨1⟩ := u256_eq_refl v
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨5518⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd5518 with [jumpdest, pop, jump hret]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- The shared ABI decoder for a full uint256 calldata word at PC 5521. -/
theorem RD.ammDecodeUint256Ok {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5521⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata acc k' C' := by
  have rd5499 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨5535⟩, dup2, push2 ⟨5499⟩, jump (by jump_dest) ]
  have rd5508 := evm_run rd5499 with [
    jumpdest, push2 ⟨5508⟩, dup2, push2 ⟨5490⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest) ]
  have heq : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) = ⟨1⟩ :=
    u256_eq_refl _
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨5518⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5518 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked subtraction at PC 6645, successful branch. -/
theorem RD.ammCheckedSubOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6645⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret (UInt256.sub a b :: R)
      mem aw rdata acc k' C' := by
  have rd6655₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6655⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest) ]
  have rd6655 := RD.ammRoutineCleanupUint256 rd6655₀
    (by jump_dest) (by evm_ov)
  have rd6666₀ := evm_run rd6655 with [
    jumpdest, swap2, pop, push2 ⟨6666⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest) ]
  have rd6666 := RD.ammRoutineCleanupUint256 rd6666₀
    (by jump_dest) (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsubNat]; omega)
  have rd6676 := evm_run rd6666 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd6690 := evm_run rd6676 with [
    iszero, push2 ⟨6690⟩,
    jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd6690 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked addition at PC 6696, successful branch. -/
theorem RD.ammCheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6696⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret ((a + b) :: R)
      mem aw rdata acc k' C' := by
  have rd6706₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6706⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest) ]
  have rd6706 := RD.ammRoutineCleanupUint256 rd6706₀
    (by jump_dest) (by evm_ov)
  have rd6717₀ := evm_run rd6706 with [
    jumpdest, swap2, pop, push2 ⟨6717⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest) ]
  have rd6717 := RD.ammRoutineCleanupUint256 rd6717₀
    (by jump_dest) (by evm_ov)
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgt : UInt256.gt a (a + b) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [haddNat]; omega)
  have rd6728 := evm_run rd6717 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd6741 := evm_run rd6728 with [
    iszero, push2 ⟨6741⟩,
    jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd6741 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Shared Solidity checked-arithmetic panic revert at PC 6600. -/
theorem RD.ammPanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6600⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  have rd6601 := evm_run h with [jumpdest]
  have rd6634 := rd6601.pushConst ammPanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd6641 := evm_run rd6634 with [
    push0,
    raw mstore 0 (ammPanicMem0 mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (ammPanicMem mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd6644 := evm_run rd6641 with [push1 ⟨36⟩, push0]
  exact rd6644.rev 0 (by native_decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- The checked-arithmetic panic also works after external calls expand memory. -/
theorem RD.ammPanicOverflowRevertWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6600⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 2 ≤ 1024) :
    RDrev ammBytecode g s0 := by
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
  have rd6601 := evm_run h with [jumpdest]
  have rd6634 := rd6601.pushConst ammPanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd6641 := evm_run rd6634 with [
    push0,
    raw mstore 0 (ammPanicMem0 mem) aw
      (by native_decide) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hM0, Nat.sub_self])
      (by rfl) (by simpa using hM0) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (ammPanicMem mem) aw
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
theorem RD.ammCheckedSubUnderflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6645⟩ (a :: b :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  have rd6655₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6655⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest) ]
  have rd6655 := RD.ammRoutineCleanupUint256 rd6655₀
    (by jump_dest) (by evm_ov)
  have rd6666₀ := evm_run rd6655 with [
    jumpdest, swap2, pop, push2 ⟨6666⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest) ]
  have rd6666 := RD.ammRoutineCleanupUint256 rd6666₀
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
  have rd6676 := evm_run rd6666 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd6600 := evm_run rd6676 with [
    iszero, push2 ⟨6690⟩,
    jumpiNT (by decide),
    push2 ⟨6689⟩, push2 ⟨6600⟩, jump (by jump_dest) ]
  exact RD.ammPanicOverflowRevert rd6600 (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked addition at PC 6696, overflow branch. -/
theorem RD.ammCheckedAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6696⟩ (a :: b :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  have rd6706₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6706⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest) ]
  have rd6706 := RD.ammRoutineCleanupUint256 rd6706₀
    (by jump_dest) (by evm_ov)
  have rd6717₀ := evm_run rd6706 with [
    jumpdest, swap2, pop, push2 ⟨6717⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest) ]
  have rd6717 := RD.ammRoutineCleanupUint256 rd6717₀
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
  have rd6728 := evm_run rd6717 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd6600 := evm_run rd6728 with [
    iszero, push2 ⟨6741⟩,
    jumpiNT (by decide),
    push2 ⟨6740⟩, push2 ⟨6600⟩, jump (by jump_dest) ]
  exact RD.ammPanicOverflowRevert rd6600 (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.ammCheckedSubUnderflowWide {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6645⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hlt : a.toNat < b.toNat) (haw : 3 ≤ aw.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  have rd6655₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6655⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest) ]
  have rd6655 := RD.ammRoutineCleanupUint256 rd6655₀
    (by jump_dest) (by evm_ov)
  have rd6666₀ := evm_run rd6655 with [
    jumpdest, swap2, pop, push2 ⟨6666⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest) ]
  have rd6666 := RD.ammRoutineCleanupUint256 rd6666₀
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
  have rd6676 := evm_run rd6666 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd6600 := evm_run rd6676 with [
    iszero, push2 ⟨6690⟩,
    jumpiNT (by decide),
    push2 ⟨6689⟩, push2 ⟨6600⟩, jump (by jump_dest) ]
  exact RD.ammPanicOverflowRevertWide rd6600 haw (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.ammCheckedAddOverflowWide {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6696⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (haw : 3 ≤ aw.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  have rd6706₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6706⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest) ]
  have rd6706 := RD.ammRoutineCleanupUint256 rd6706₀
    (by jump_dest) (by evm_ov)
  have rd6717₀ := evm_run rd6706 with [
    jumpdest, swap2, pop, push2 ⟨6717⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest) ]
  have rd6717 := RD.ammRoutineCleanupUint256 rd6717₀
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
  have rd6728 := evm_run rd6717 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd6600 := evm_run rd6728 with [
    iszero, push2 ⟨6741⟩,
    jumpiNT (by decide),
    push2 ⟨6740⟩, push2 ⟨6600⟩, jump (by jump_dest) ]
  exact RD.ammPanicOverflowRevertWide rd6600 haw (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Shared solc one-word uint256 ABI encoder at PC 5731, preserving scratch memory. -/
theorem RD.ammRoutineEncodeUint256FromMem
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5731⟩ (⟨128⟩ :: val :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hret : (D_J ammBytecode 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨5750⟩, push0, dup4, add, dup5, push2 ⟨5716⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨5725⟩, dup2, push2 ⟨5490⟩,
    jump (by jump_dest),
    raw ammRoutineCleanupUint256 (by jump_dest) (by evm_ov),
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
theorem RD.ammRoutineBoolCleanup {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5603⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J ammBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret (UInt256.isZero (UInt256.isZero v) :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, dup2, iszero, iszero, swap1, pop, swap2, swap1, pop,
    jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.ammRoutineEncodeBoolFromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5629⟩ (⟨128⟩ :: val :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0
      mem 128 32 = memout)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  have rd5603 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨5648⟩, push0, dup4, add, dup5, push2 ⟨5614⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨5623⟩, dup2, push2 ⟨5603⟩,
    jump (by jump_dest) ]
  obtain ⟨_, _, rd5623⟩ := RD.ammRoutineBoolCleanup rd5603
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5623 with [
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
theorem RD.ammDecodeAddrMask {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5470⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ⟨5457⟩
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          solcAddrMask
        :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: ⟨5484⟩
        :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)
        :: off :: csize :: ret :: R) mem aw rdata acc k' C' := by
  have rd5448 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨5484⟩, dup2,
    push2 ⟨5448⟩, jump (by jump_dest) ]
  have rd5431 := evm_run rd5448 with [
    jumpdest, push2 ⟨5457⟩, dup2, push2 ⟨5431⟩, jump (by jump_dest) ]
  exact ⟨_, _, evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩, jump (by jump_dest),
    jumpdest, push0, push20 solcAddrMask, dup3, and, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest),
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Successful shared address decode returns the canonical calldata word. -/
theorem RD.ammDecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5470⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
      < EVM.addressModulus)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd⟩ := RD.ammDecodeAddrMask h hov
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨1⟩ := solcAddrCanon_eq hcanon
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨5467⟩, jumpiT (by rw [hclean]; decide) (by jump_dest),
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- A noncanonical address fails the shared decoder's equality check. -/
theorem RD.ammDecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨5470⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  obtain ⟨_, _, rd⟩ := RD.ammDecodeAddrMask h hov
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨5467⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ] :
    RDrev ammBytecode g s0)

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammCheckedMulConditionOk (a b : UInt256)
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

theorem ammCheckedMulConditionOverflow (a b : UInt256)
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

theorem RD.ammCheckedMulToCondition {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6747⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ⟨6793⟩
      (UInt256.lor (UInt256.isZero a)
        (UInt256.eq b (UInt256.div (UInt256.mul a b) a)) ::
       UInt256.mul a b :: UInt256.mul a b :: a :: b :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd6757₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6757⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest)]
  have rd6757 := RD.ammRoutineCleanupUint256 rd6757₀
    (by jump_dest) (by evm_ov)
  have rd6768₀ := evm_run rd6757 with [
    jumpdest, swap2, pop, push2 ⟨6768⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest)]
  have rd6768 := RD.ammRoutineCleanupUint256 rd6768₀
    (by jump_dest) (by evm_ov)
  have rd6782₀ := evm_run rd6768 with [
    jumpdest, swap3, pop, dup3, dup3, mul, push2 ⟨6782⟩,
    dup2, push2 ⟨5490⟩, jump (by jump_dest)]
  have rd6782 := RD.ammRoutineCleanupUint256 rd6782₀
    (by jump_dest) (by evm_ov)
  have rd6793 := evm_run rd6782 with [
    jumpdest, swap2, pop, dup3, dup3, div, dup5, eq, dup4, iszero, or]
  exact ⟨_, _, rd6793⟩

theorem RD.ammCheckedMulOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6747⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret (UInt256.mul a b :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd6793₀⟩ := RD.ammCheckedMulToCondition h hov
  have rd6793 := rd6793₀
  rw [ammCheckedMulConditionOk a b hfit] at rd6793
  have rd6805 := evm_run rd6793 with [
    push2 ⟨6805⟩, jumpiT (by decide) (by jump_dest)]
  exact ⟨_, _, evm_run rd6805 with [
    jumpdest, pop, swap3, swap2, pop, pop, jump hret]⟩

theorem RD.ammCheckedMulOverflowWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6747⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 12 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  obtain ⟨_, _, rd6793₀⟩ := RD.ammCheckedMulToCondition h hov
  have rd6793 := rd6793₀
  rw [ammCheckedMulConditionOverflow a b hover] at rd6793
  have rd6600 := evm_run rd6793 with [
    push2 ⟨6805⟩, jumpiNT (by decide),
    push2 ⟨6804⟩, push2 ⟨6600⟩, jump (by jump_dest)]
  exact RD.ammPanicOverflowRevertWide rd6600 haw (by evm_ov)


theorem RD.ammCheckedDivToGuard {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6857⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ⟨6882⟩
      (b :: ⟨0⟩ :: a :: b :: ret :: R) mem aw rdata acc k' C' := by
  have rd6867₀ := evm_run h with [
    jumpdest, push0, push2 ⟨6867⟩, dup3, push2 ⟨5490⟩, jump (by jump_dest)]
  have rd6867 := RD.ammRoutineCleanupUint256 rd6867₀
    (by jump_dest) (by evm_ov)
  have rd6878₀ := evm_run rd6867 with [
    jumpdest, swap2, pop, push2 ⟨6878⟩, dup4, push2 ⟨5490⟩,
    jump (by jump_dest)]
  have rd6878 := RD.ammRoutineCleanupUint256 rd6878₀
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd6878 with [jumpdest, swap3, pop, dup3]⟩

theorem RD.ammCheckedDivOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6857⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hb : b ≠ ⟨0⟩)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret (UInt256.div a b :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd6882⟩ := RD.ammCheckedDivToGuard h hov
  have rd6894 := evm_run rd6882 with [
    push2 ⟨6894⟩, jumpiT hb (by jump_dest)]
  exact ⟨_, _, evm_run rd6894 with [
    jumpdest, dup3, dup3, div, swap1, pop,
    swap3, swap2, pop, pop, jump hret]⟩

noncomputable def ammPanicDivMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨18⟩ : UInt256)).write 0 (ammPanicMem0 mem) 4 32

theorem RD.ammPanicDivZeroRevertWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6812⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat) (hov : R.length + 2 ≤ 1024) :
    RDrev ammBytecode g s0 := by
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
  have rd6601 := evm_run h with [jumpdest]
  have rd6634 := rd6601.pushConst ammPanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd6641 := evm_run rd6634 with [
    push0,
    raw mstore 0 (ammPanicMem0 mem) aw
      (by native_decide) (by
        intro s hs hst
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
          List.getElem!_cons_zero]
        simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hM0, Nat.sub_self])
      (by rfl) (by simpa using hM0) (by evm_ov),
    push1 ⟨18⟩, push1 ⟨4⟩,
    raw mstore 0 (ammPanicDivMem mem) aw
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

theorem RD.ammCheckedDivZeroWide {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD ammBytecode ee g s0 ⟨6857⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hb : b = ⟨0⟩) (haw : 3 ≤ aw.toNat)
    (hov : R.length + 12 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  obtain ⟨_, _, rd6882₀⟩ := RD.ammCheckedDivToGuard h hov
  have rd6882 := rd6882₀
  rw [hb] at rd6882
  have rd6812 := evm_run rd6882 with [
    push2 ⟨6894⟩, jumpiNT (by decide),
    push2 ⟨6893⟩, push2 ⟨6812⟩, jump (by jump_dest)]
  exact RD.ammPanicDivZeroRevertWide rd6812 haw (by evm_ov)



end Reasoning.Reach

namespace Benchmarks.ActAmm

-- LIBRARY CANDIDATE: Reasoning.Memory, one-word ABI return from 96-byte scratch memory.
noncomputable def ammWordReturnMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem ammWordReturnMem_size_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (ammWordReturnMem mem val).size = 160 := by
  unfold ammWordReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hmem]; omega)
      (by rw [hmem]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hmem,
    ByteArray_zeroes_size, toByteArray_size]

theorem ammWordReturnMem_read64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ammWordReturnMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammWordReturnMem
  rw [toByteArray_write_read_below_of_gap val mem 128 64
    (by rw [hmem]) (by omega)
    (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread

theorem ammWordReturnMem_mload64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (ammWordReturnMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((ammWordReturnMem mem val).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [ammWordReturnMem_size_of_size96 val hmem]; decide)
    (by decide) (by simpa using ammWordReturnMem_read64_of_size96 val hmem hread)

theorem ammWordReturnMem_read128_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (ammWordReturnMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold ammWordReturnMem
  exact toByteArray_write_read_back_of_gap val mem 128
    (by rw [hmem]; exact lt_usize _ (by norm_num))

end Benchmarks.ActAmm
