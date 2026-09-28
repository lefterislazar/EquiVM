import Benchmarks.ActAmm.ConstructorGuardTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorPostGuardSupplyStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨777⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨784⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata
      (acc.1, sstoreAccountMap I.codeOwner acc.2 ⟨0⟩ liquidity) k' C' := by
  have rd782 := amm_ctor_run rd with [
    jumpdest, dup1, push0, dup2, swap1]
  obtain ⟨_, _, rd783⟩ := rd782.sstore hperm (by amm_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, amm_ctor_run rd783 with [pop]⟩

theorem ammCtorTwoWordHashMem_size (key slot : UInt256) (mem : ByteArray)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem wordAt32Mem wordAt0Mem
  have hfirst : ((UInt256.toByteArray key).write 0 mem 0 32).size = mem.size :=
    toByteArray_write32_size_of_le mem key 0 mem.size mem.size rfl
      (by omega) (by simp [max_eq_left]; omega)
  exact toByteArray_write32_size_of_le _ slot 32 mem.size mem.size hfirst
    (by omega) (by simp [max_eq_left]; omega)

theorem ammCtorTwoWordHashMem_read0 (key slot : UInt256) (mem : ByteArray)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
    (by
      have hfirst := toByteArray_write32_size_of_le
        mem key 0 mem.size mem.size rfl
        (by omega) (by simp [max_eq_left]; omega)
      rw [wordAt0Mem, hfirst]
      omega) (by omega)]
  unfold wordAt0Mem
  exact toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)

theorem ammCtorTwoWordHashMem_read32 (key slot : UInt256) (mem : ByteArray)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  exact toByteArray_write32_read_back _ _ 32 (by
    have hfirst := toByteArray_write32_size_of_le
      mem key 0 mem.size mem.size rfl
      (by omega) (by simp [max_eq_left]; omega)
    rw [wordAt0Mem, hfirst]
    omega)

theorem ammCtorTwoWordHashMem_read0_64 (key slot : UInt256) (mem : ByteArray)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [ammCtorTwoWordHashMem_size key slot mem hmem]; omega)]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [← readWithPadding_eq_extract _ 0
      (by rw [ammCtorTwoWordHashMem_size key slot mem hmem]; omega),
    ← readWithPadding_eq_extract _ 32
      (by rw [ammCtorTwoWordHashMem_size key slot mem hmem]; omega),
    ammCtorTwoWordHashMem_read0 key slot mem hmem,
    ammCtorTwoWordHashMem_read32 key slot mem hmem]

theorem ammCtorTwoWordHashMem_keccak (key slot : UInt256) (mem : ByteArray)
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((twoWordHashMem key slot mem).readWithPadding 0 64))) =
      solcMappingSlot slot key := by
  rw [ammCtorTwoWordHashMem_read0_64 key slot mem hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

theorem ammCtorTwoWordHashMem_read64 (key slot : UInt256) (mem : ByteArray)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
  have hsize0 : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    exact toByteArray_write32_size_of_le mem key 0 mem.size mem.size rfl
      (by omega) (by simp; omega)
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
    (by rw [hsize0]; omega) (by omega) (by rw [hsize0]; omega)]
  unfold wordAt0Mem
  exact write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by omega) (by omega) (by omega)

theorem ammCtorSecondCallDecodeMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray (ammCtorAfterSecondReturnFreePtr ret1 ret2) := by
  unfold ammCtorSecondCallDecodeMem
  have hretsz2 : ret2.size < UInt256.size := by
    have hb := hbound2
    norm_num [UInt256.size] at *
    omega
  exact toByteArray_write32_read_back _ _ 64 (by
    rw [ammCtorSecondCallPostCallMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hretsz2]
    have hs := ammCtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (ammCtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega)

theorem ammCtorPostGuardSelfBalanceStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨784⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hperm : I.perm = true)
    (haw : 3 ≤ aw.toNat) (hmem : 64 ≤ mem.size) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨852⟩ [liquidity, EVM.word t1, EVM.word t0]
      (twoWordHashMem (UInt256.ofNat I.codeOwner.val) ⟨1⟩ mem)
      aw rdata
      (acc.1, sstoreAccountMap I.codeOwner acc.2
        (solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val)) ⟨1000⟩)
      k' C' := by
  let owner := UInt256.ofNat I.codeOwner.val
  have hcanon : owner.toNat < EVM.addressModulus := by
    have hto : owner.toNat = I.codeOwner.val := by
      apply UInt256.toNat_ofNat_of_lt
      exact lt_of_lt_of_le I.codeOwner.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide)
    rw [hto]
    change I.codeOwner.val < AccountAddress.size
    exact I.codeOwner.isLt
  have hclean : UInt256.land solcAddrMask owner = owner :=
    solcAddrMask_clean_left hcanon
  have hM0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
    change UInt256.ofNat (max aw.toNat 1) = aw
    rw [max_eq_left (by omega : 1 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have hM64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
    change UInt256.ofNat (max aw.toNat 2) = aw
    rw [max_eq_left (by omega : 2 ≤ aw.toNat)]
    exact u256_ofNat_toNat aw
  have rd835 := amm_ctor_run rd with [
    push2 ⟨1000⟩, push1 ⟨1⟩, push0, address,
    push20 solcAddrMask, and, push20 solcAddrMask, and, dup2]
  rw [hclean, hclean] at rd835
  have rd836 := rd835.mstore 0 (wordAt0Mem owner mem) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        hM0, Nat.sub_self])
    (by rfl) (by simpa using hM0) (by evm_ov)
  have rd842 := amm_ctor_run rd836 with [push1 ⟨32⟩, add, swap1, dup2]
  have h32 : (⟨32⟩ : UInt256) + ⟨0⟩ = ⟨32⟩ := by decide
  rw [h32] at rd842
  have rd843 := rd842.mstore 0 (twoWordHashMem owner ⟨1⟩ mem) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero]
      simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
        hM32, Nat.sub_self])
    (by rfl) (by simpa using hM32) (by evm_ov)
  have rd847 := amm_ctor_run rd843 with [push1 ⟨32⟩, add, push0]
  have hlen64 : (⟨32⟩ : UInt256) + ⟨32⟩ = ⟨64⟩ := by decide
  rw [hlen64] at rd847
  have rd848 := rd847.keccak256 0
    (solcMappingSlot ⟨1⟩ owner) aw
    (by amm_ctor_decode)
    (by
      intro s hs hst
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hs, hst,
        List.getElem!_cons_zero, List.getElem!_cons_succ]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
        show (⟨64⟩ : UInt256).toNat = 64 from rfl,
        hM64, Nat.sub_self])
    (by simpa only [owner] using ammCtorTwoWordHashMem_keccak owner ⟨1⟩ mem hmem)
    (by simpa using hM64) (by evm_ov)
  have rd850 := amm_ctor_run rd848 with [dup2, swap1]
  obtain ⟨_, _, rd851⟩ := rd850.sstore hperm (by amm_ctor_decode)
    (by evm_ov)
  exact ⟨_, _, by simpa only [owner, twoWordHashMem, wordAt32Mem] using
    (amm_ctor_run rd851 with [pop])⟩

theorem ammCtorPostGuardBaseSupplyRecomputed
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress} {liquidity : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨852⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw rdata acc k C)
    (hle : 1000 ≤ liquidity.toNat) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨865⟩ [UInt256.sub liquidity ⟨1000⟩, liquidity,
        EVM.word t1, EVM.word t0]
      mem aw rdata acc k' C' := by
  have rd1526 := amm_ctor_run rd with [
    push2 ⟨1000⟩, dup2, push2 ⟨865⟩, swap2, swap1,
    push2 ⟨1526⟩, jump (by amm_ctor_jd)]
  have rd1536₀ := amm_ctor_run rd1526 with [
    jumpdest, push0, push2 ⟨1536⟩, dup3, push2 ⟨1350⟩,
    jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1536⟩ := RD.ammCtorCleanupUint rd1536₀
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1547₀ := amm_ctor_run rd1536 with [
    jumpdest, swap2, pop, push2 ⟨1547⟩, dup4,
    push2 ⟨1350⟩, jump (by amm_ctor_jd)]
  obtain ⟨_, _, rd1547⟩ := RD.ammCtorCleanupUint rd1547₀
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1559 := amm_ctor_run rd1547 with [
    jumpdest, swap3, pop, dup3, dup3, sub, swap1, pop,
    dup2, dup2, gt, iszero]
  rw [ammCtorBaseSubNoUnderflowGt liquidity hle] at rd1559
  have rd1571 := amm_ctor_run rd1559 with [
    push2 ⟨1571⟩, jumpiT (by decide) (by amm_ctor_jd)]
  exact ⟨_, _, amm_ctor_run rd1571 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm_ctor_jd)]⟩

end Benchmarks.ActAmm
