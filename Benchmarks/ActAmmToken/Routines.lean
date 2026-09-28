import Benchmarks.ActAmmToken.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000


namespace Benchmarks.ActAmmToken


/-- Standard Solidity panic selector, left-aligned in a 32-byte word. -/
def tokenPanicSelector : UInt256 :=
  ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩

noncomputable def tokenPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray tokenPanicSelector).write 0 mem 0 32

noncomputable def tokenPanicMem (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨17⟩ : UInt256)).write 0 (tokenPanicMem0 mem) 4 32

end Benchmarks.ActAmmToken

namespace Reasoning.Reach
open Benchmarks.ActAmmToken

/-- The repeated solc scratch-memory mapping hash suffix. -/
@[reducible] def tokenMappingHashSuffixWf (pc : UInt256) : Prop :=
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
  decode Benchmarks.ActAmmToken.tokenBytecode pc = some (.DUP2, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p1 = some (.MSTORE, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p2 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p4 = some (.ADD, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p5 = some (.SWAP1, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p6 = some (.DUP2, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p7 = some (.MSTORE, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p10 = some (.ADD, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p11 = some (.PUSH0, .none)
  ∧ decode Benchmarks.ActAmmToken.tokenBytecode p12 = some (.KECCAK256, .none)

macro "token_mapping_hash_wf" : term =>
  `(by
    unfold Reasoning.Reach.tokenMappingHashSuffixWf
    repeat' first | apply And.intro | native_decide)

@[reducible] def tokenMappingHashSuffixEndPc (pc : UInt256) : UInt256 :=
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
theorem RD.tokenMappingHashSuffix {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc key baseSlot slot : UInt256} {R : List UInt256}
    {mem memKey memHash rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 pc (key :: ⟨0⟩ :: baseSlot :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hwf : tokenMappingHashSuffixWf pc)
    (hkey : (UInt256.toByteArray key).write 0 mem 0 32 = memKey)
    (hbase : (UInt256.toByteArray baseSlot).write 0 memKey
      ((⟨32⟩ : UInt256) + ⟨0⟩).toNat 32 = memHash)
    (hslot : UInt256.ofNat
      (fromByteArrayBigEndian (ffi.KEC (memHash.readWithPadding 0
        ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨0⟩)).toNat))) = slot)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 (tokenMappingHashSuffixEndPc pc) (slot :: R)
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



-- GENERALIZES Reasoning.Reach.RD.erc20Routine0766: the same identity routine at a new PC.
theorem RD.tokenRoutineB6e {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {v ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2926⟩ (v :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret (v :: R)
      mem aw rdata acc (k + 9) (C + 27) :=
  evm_run h with [jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump hret]

set_option maxHeartbeats 1000000 in
theorem RD.tokenRoutineEncodeUint256FromMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {mem memout : ByteArray}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3105⟩
      (⟨128⟩ :: val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray val).write 0 mem 128 32 = memout)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret
      ((⟨128⟩ + ⟨32⟩) :: R) memout (UInt256.ofNat 5)
      rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨3124⟩, push0, dup4, add, dup5, push2 ⟨3090⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨3099⟩, dup2, push2 ⟨2926⟩,
    jump (by jump_dest),
    raw tokenRoutineB6e (by jump_dest) (by evm_ov),
    jumpdest, dup3,
    raw mstore 6 memout (UInt256.ofNat 5) (by decide) mem_cost
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    pop, pop,
    jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop,
    jump hret ]
  exact ⟨_, _, rd⟩

theorem RD.tokenRoutineEncodeUint256 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3105⟩
      (⟨128⟩ :: val :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret
      ((⟨128⟩ + ⟨32⟩) :: R) (solcReturnMem val) (UInt256.ofNat 5)
      rdata acc k' C' := by
  exact RD.tokenRoutineEncodeUint256FromMem h (by rfl) hret hov

-- GENERALIZES Reasoning.Solc.RD.solcSingleMappingGetter: solc 0.8.28 uses DUP1 and PUSH0.
set_option maxHeartbeats 1000000 in
theorem RD.tokenSingleMappingGetter {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨1851⟩ (key :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨1⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have rd1 := h.jumpdest (by decide) (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨1⟩ (by decide) (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ (by decide) (by evm_ov)
  have rd6 := rd5.mstore 0 (solcMappingBaseSlotMem ⟨1⟩)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7 := rd6.dup1 (by decide) (by evm_ov)
  have rd8 := rd7.push0 (by decide) (by evm_ov)
  have rd9 := rd8.mstore 0 (solcMappingHashMem ⟨1⟩ key)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd11 := rd9.push1 ⟨64⟩ (by decide) (by evm_ov)
  have rd12 := rd11.push0 (by decide) (by evm_ov)
  have rd13 := rd12.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) (by decide) mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        solcMappingKeccakSlot ⟨1⟩ key)
    (by native_decide) (by evm_ov)
  have rd14 := rd13.push0 (by decide) (by evm_ov)
  have rd15 := rd14.swap2 (by decide) (by evm_ov)
  have rd16 := rd15.pop (by decide) (by evm_ov)
  have rd17 := rd16.swap1 (by decide) (by evm_ov)
  have rd18 := rd17.pop (by decide) (by evm_ov)
  obtain ⟨_, _, rd19⟩ := rd18.sload (by decide) (by evm_ov)
  have rd20 := rd19.dup2 (by decide) (by evm_ov)
  exact ⟨_, _, rd20.jump (by decide) hret (by evm_ov)⟩

-- GENERALIZES Reasoning.Solc: shared solc 0.8.28 address decoder and canonicality check.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.tokenDecodeAddrMask {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2906⟩
      (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2893⟩
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
          solcAddrMask
        :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: ⟨2920⟩
        :: uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)
        :: off :: csize :: ret :: R) mem aw rdata acc k' C' := by
  have rd2884 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨2920⟩, dup2,
    push2 ⟨2884⟩, jump (by jump_dest) ]
  have rd2867 := evm_run rd2884 with [
    jumpdest, push2 ⟨2893⟩, dup2, push2 ⟨2867⟩, jump (by jump_dest) ]
  exact ⟨_, _, evm_run rd2867 with [
    jumpdest, push0, push2 ⟨2877⟩, dup3, push2 ⟨2836⟩, jump (by jump_dest),
    jumpdest, push0, push20 solcAddrMask, dup3, and, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest),
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.tokenDecodeAddrOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2906⟩
      (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hcanon : (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)).toNat
      < EVM.addressModulus)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd⟩ := RD.tokenDecodeAddrMask h hov
  have hclean : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨1⟩ := solcAddrCanon_eq hcanon
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨2903⟩, jumpiT (by rw [hclean]; decide) (by jump_dest),
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.tokenDecodeAddrRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2906⟩
      (off :: csize :: ret :: R) mem aw rdata acc k C)
    (hnc : UInt256.eq (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (UInt256.land (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
        solcAddrMask) = ⟨0⟩)
    (hov : R.length + 14 ≤ 1024) :
    RDrev Benchmarks.ActAmmToken.tokenBytecode g s0 := by
  obtain ⟨_, _, rd⟩ := RD.tokenDecodeAddrMask h hov
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨2903⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ] :
    RDrev Benchmarks.ActAmmToken.tokenBytecode g s0)

-- GENERALIZES Reasoning.Solc.RD.solcNestedMappingGetter for the PUSH0 solc 0.8.28 shape.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.tokenNestedMappingGetter {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {owner spender ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2800⟩
      (spender :: owner :: ret :: R) solcFreePtrMem (UInt256.ofNat 3)
      rdata (cA, σ) k C)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot (solcMappingSlot ⟨2⟩ owner) spender)
        :: ret :: R)
      (solcNestedMappingHashMem ⟨2⟩ owner spender) (UInt256.ofNat 3)
      rdata (cA, σ) k' C' := by
  have rdBeforeLoad := evm_run h with [
    jumpdest, push1 ⟨2⟩, push1 ⟨32⟩,
    raw mstore 0 (solcMappingBaseSlotMem ⟨2⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    dup2, push0,
    raw mstore 0 (solcMappingHashMem ⟨2⟩ owner) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (solcMappingSlot ⟨2⟩ owner) (UInt256.ofNat 3)
      (by native_decide) mem_cost (solcMappingKeccakSlot ⟨2⟩ owner)
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    raw mstore 0 (solcNestedMappingOuterBaseMem ⟨2⟩ owner)
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    dup1, push0,
    raw mstore 0 (solcNestedMappingHashMem ⟨2⟩ owner spender)
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov),
    push1 ⟨64⟩, push0,
    raw keccak256 0 (solcMappingSlot (solcMappingSlot ⟨2⟩ owner) spender)
      (UInt256.ofNat 3) (by native_decide) mem_cost
      (solcNestedMappingKeccakSlot ⟨2⟩ owner spender)
      (by decide) (by evm_ov),
    push0, swap2, pop, swap2, pop, pop ]
  obtain ⟨_, _, rdLoaded⟩ := rdBeforeLoad.sload (by native_decide) (by evm_ov)
  have rdReturn := evm_run rdLoaded with [dup2, jump hret]
  exact ⟨_, _, rdReturn⟩

theorem RD.tokenRoutineBoolCleanup {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {v ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3039⟩ (v :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true) (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret (UInt256.isZero (UInt256.isZero v) :: R)
      mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, push0, dup2, iszero, iszero, swap1, pop, swap2, swap1, pop,
    jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem RD.tokenRoutineEncodeBoolFromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3065⟩ (⟨128⟩ :: val :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmemout : (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0
      mem 128 32 = memout)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret ((⟨128⟩ + ⟨32⟩) :: R)
      memout (UInt256.ofNat 5) rdata acc k' C' := by
  have rd5603 := evm_run h with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨3084⟩, push0, dup4, add, dup5, push2 ⟨3050⟩,
    jump (by jump_dest),
    jumpdest, push2 ⟨3059⟩, dup2, push2 ⟨3039⟩,
    jump (by jump_dest) ]
  obtain ⟨_, _, rd5623⟩ := RD.tokenRoutineBoolCleanup rd5603
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
/-- The shared ABI decoder for a full uint256 calldata word at PC 2957. -/
theorem RD.tokenDecodeUint256Ok {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {off csize ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨2957⟩ (off :: csize :: ret :: R)
      mem aw rdata acc k C)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32) :: R)
      mem aw rdata acc k' C' := by
  have rd5499 := evm_run h with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨2971⟩, dup2, push2 ⟨2935⟩, jump (by jump_dest) ]
  have rd5508 := evm_run rd5499 with [
    jumpdest, push2 ⟨2944⟩, dup2, push2 ⟨2926⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by jump_dest) ]
  have heq : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32))
      (uInt256OfByteArray (ee.calldata.readBytes off.toNat 32)) = ⟨1⟩ :=
    u256_eq_refl _
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨2954⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5518 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked subtraction at PC 3465, successful branch. -/
theorem RD.tokenCheckedSubOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3465⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret (UInt256.sub a b :: R)
      mem aw rdata acc k' C' := by
  have rd6655₀ := evm_run h with [
    jumpdest, push0, push2 ⟨3475⟩, dup3, push2 ⟨2926⟩, jump (by jump_dest) ]
  have rd6655 := RD.tokenRoutineB6e rd6655₀
    (by jump_dest) (by evm_ov)
  have rd6666₀ := evm_run rd6655 with [
    jumpdest, swap2, pop, push2 ⟨3486⟩, dup4, push2 ⟨2926⟩,
    jump (by jump_dest) ]
  have rd6666 := RD.tokenRoutineB6e rd6666₀
    (by jump_dest) (by evm_ov)
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [hsubNat]; omega)
  have rd6676 := evm_run rd6666 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop, dup2, dup2, gt ]
  rw [hgt] at rd6676
  have rd6690 := evm_run rd6676 with [
    iszero, push2 ⟨3510⟩,
    jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd6690 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked addition at PC 3516, successful branch. -/
theorem RD.tokenCheckedAddOk {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3516⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J Benchmarks.ActAmmToken.tokenBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ret ((a + b) :: R)
      mem aw rdata acc k' C' := by
  have rd6706₀ := evm_run h with [
    jumpdest, push0, push2 ⟨3526⟩, dup3, push2 ⟨2926⟩, jump (by jump_dest) ]
  have rd6706 := RD.tokenRoutineB6e rd6706₀
    (by jump_dest) (by evm_ov)
  have rd6717₀ := evm_run rd6706 with [
    jumpdest, swap2, pop, push2 ⟨3537⟩, dup4, push2 ⟨2926⟩,
    jump (by jump_dest) ]
  have rd6717 := RD.tokenRoutineB6e rd6717₀
    (by jump_dest) (by evm_ov)
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hgt : UInt256.gt a (a + b) = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero (by rw [haddNat]; omega)
  have rd6728 := evm_run rd6717 with [
    jumpdest, swap3, pop, dup3, dup3, add, swap1, pop, dup1, dup3, gt ]
  rw [hgt] at rd6728
  have rd6741 := evm_run rd6728 with [
    iszero, push2 ⟨3561⟩,
    jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd6741 with [
    jumpdest, swap3, swap2, pop, pop, jump hret ]⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Shared Solidity checked-arithmetic panic revert at PC 3420. -/
theorem RD.tokenPanicOverflowRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3420⟩ R mem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev Benchmarks.ActAmmToken.tokenBytecode g s0 := by
  have rd6601 := evm_run h with [jumpdest]
  have rd6634 := rd6601.pushConst tokenPanicSelector
    (width := 32) (op := .PUSH32) (by native_decide) (by decide) (by evm_ov)
  have rd6641 := evm_run rd6634 with [
    push0,
    raw mstore 0 (tokenPanicMem0 mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨17⟩, push1 ⟨4⟩,
    raw mstore 0 (tokenPanicMem mem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov) ]
  have rd6644 := evm_run rd6641 with [push1 ⟨36⟩, push0]
  exact rd6644.rev 0 (by native_decide) mem_cost (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked subtraction at PC 3465, underflow branch. -/
theorem RD.tokenCheckedSubUnderflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3465⟩ (a :: b :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev Benchmarks.ActAmmToken.tokenBytecode g s0 := by
  have rd6655₀ := evm_run h with [
    jumpdest, push0, push2 ⟨3475⟩, dup3, push2 ⟨2926⟩, jump (by jump_dest) ]
  have rd6655 := RD.tokenRoutineB6e rd6655₀
    (by jump_dest) (by evm_ov)
  have rd6666₀ := evm_run rd6655 with [
    jumpdest, swap2, pop, push2 ⟨3486⟩, dup4, push2 ⟨2926⟩,
    jump (by jump_dest) ]
  have rd6666 := RD.tokenRoutineB6e rd6666₀
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
    iszero, push2 ⟨3510⟩,
    jumpiNT (by decide),
    push2 ⟨3509⟩, push2 ⟨3420⟩, jump (by jump_dest) ]
  exact RD.tokenPanicOverflowRevert rd6600 (by evm_ov)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
/-- Solc checked addition at PC 3516, overflow branch. -/
theorem RD.tokenCheckedAddOverflow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD Benchmarks.ActAmmToken.tokenBytecode ee g s0 ⟨3516⟩ (a :: b :: ret :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev Benchmarks.ActAmmToken.tokenBytecode g s0 := by
  have rd6706₀ := evm_run h with [
    jumpdest, push0, push2 ⟨3526⟩, dup3, push2 ⟨2926⟩, jump (by jump_dest) ]
  have rd6706 := RD.tokenRoutineB6e rd6706₀
    (by jump_dest) (by evm_ov)
  have rd6717₀ := evm_run rd6706 with [
    jumpdest, swap2, pop, push2 ⟨3537⟩, dup4, push2 ⟨2926⟩,
    jump (by jump_dest) ]
  have rd6717 := RD.tokenRoutineB6e rd6717₀
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
    iszero, push2 ⟨3561⟩,
    jumpiNT (by decide),
    push2 ⟨3560⟩, push2 ⟨3420⟩, jump (by jump_dest) ]
  exact RD.tokenPanicOverflowRevert rd6600 (by evm_ov)


end Reasoning.Reach

namespace Benchmarks.ActAmmToken

-- LIBRARY CANDIDATE: Reasoning.Memory, one-word ABI return from 96-byte scratch memory.
noncomputable def tokenWordReturnMem (mem : ByteArray) (val : UInt256) : ByteArray :=
  (UInt256.toByteArray val).write 0 mem 128 32

theorem tokenWordReturnMem_size_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (tokenWordReturnMem mem val).size = 160 := by
  unfold tokenWordReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [hmem]; omega)
      (by rw [hmem]; exact lt_usize _ (by norm_num))]
  rw [ByteArray.size_append, ByteArray.size_append, hmem,
    ByteArray_zeroes_size, toByteArray_size]

theorem tokenWordReturnMem_read64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tokenWordReturnMem mem val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold tokenWordReturnMem
  rw [toByteArray_write_read_below_of_gap val mem 128 64
    (by rw [hmem]) (by omega)
    (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread

theorem tokenWordReturnMem_mload64_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (tokenWordReturnMem mem val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((tokenWordReturnMem mem val).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [tokenWordReturnMem_size_of_size96 val hmem]; decide)
    (by decide) (by simpa using tokenWordReturnMem_read64_of_size96 val hmem hread)

theorem tokenWordReturnMem_read128_of_size96 {mem : ByteArray} (val : UInt256)
    (hmem : mem.size = 96) :
    (tokenWordReturnMem mem val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  unfold tokenWordReturnMem
  exact toByteArray_write_read_back_of_gap val mem 128
    (by rw [hmem]; exact lt_usize _ (by norm_num))


end Benchmarks.ActAmmToken
