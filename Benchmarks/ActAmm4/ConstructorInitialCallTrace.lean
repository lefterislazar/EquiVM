import Benchmarks.ActAmm4.ConstructorStorageTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

noncomputable def amm4CtorToken1Storage (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (amm4CtorToken0Storage I σ liquidity t0) ⟨4⟩
    (setAddressOffset0Word
      (amm4CtorStorageWord (amm4CtorToken0Storage I σ liquidity t0) I ⟨4⟩)
      (EVM.word t1))

noncomputable def amm4CtorInitialToken1Target (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress) : UInt256 :=
  UInt256.land solcAddrMask
    (UInt256.land solcAddrMask
      (UInt256.div
        (amm4CtorStorageWord (amm4CtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩)
        (UInt256.exp ⟨256⟩ ⟨0⟩)))

theorem amm4CtorInitialToken1Target_eq_masked (I : ExecutionEnv)
    (σ : AccountMap) (liquidity : UInt256) (t0 t1 : AccountAddress) :
    amm4CtorInitialToken1Target I σ liquidity t0 t1 =
      UInt256.land
        (amm4CtorStorageWord (amm4CtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩)
        solcAddrMask := by
  let w := amm4CtorStorageWord (amm4CtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩
  have hpow : UInt256.exp ⟨256⟩ ⟨0⟩ = ⟨1⟩ := by native_decide
  have hdiv : UInt256.div w (UInt256.exp ⟨256⟩ ⟨0⟩) = w := by
    rw [hpow]
    apply u256_inj
    rw [udiv_toNat]
    change w.toNat / 1 = w.toNat
    simp
  have hmask : UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land w solcAddrMask := by
    rw [u256_land_comm solcAddrMask w]
    exact solcAddrMask_clean_left (solcAddrMask_result_canonical w)
  unfold amm4CtorInitialToken1Target
  simp only [w, hdiv, hmask]

theorem amm4CtorReachInitialToken1Target
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨376⟩ [amm4CtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, amm4CtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd320⟩ := amm4CtorReachToken1Stored
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd324 := amm4_ctor_run rd320 with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd325⟩ := rd324.sload (by amm4_ctor_decode) (by simp)
  have rd376 := amm4_ctor_run rd325 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by simpa only [amm4CtorToken1Storage,
    amm4CtorStorageWord, amm4CtorInitialToken1Target] using rd376⟩

theorem amm4CtorSenderMem1_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorSenderMem1 I t0 t1 liquidity).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold amm4CtorSenderMem1
  rw [write32_read_above _ _ 32 64
    (by rw [toByteArray_size])
    (by rw [amm4CtorSenderMem0_size]; decide)
    (by decide)
    (by rw [amm4CtorSenderMem0_size]; decide)]
  unfold amm4CtorSenderMem0
  rw [write32_read_above _ _ 0 64
    (by rw [toByteArray_size])
    (by rw [amm4CtorDecodedMem_size]; decide)
    (by decide)
    (by rw [amm4CtorDecodedMem_size]; decide)]
  unfold amm4CtorDecodedMem
  exact toByteArray_write32_read_back _ _ 64
    (by rw [amm4CtorCopiedArgsMem_size]; decide)

theorem amm4CtorReachInitialToken1FreePtr
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨385⟩ [⟨224⟩, UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, amm4CtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd376⟩ := amm4CtorReachInitialToken1Target
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd384 := amm4_ctor_run rd376 with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd385 := rd384.mload 0 ⟨224⟩ (UInt256.ofNat 7)
    (by amm4_ctor_decode) mem_cost
    (mloadWordValue_of_readWithPadding
      (by rw [amm4CtorSenderMem1_size]; decide)
      (by native_decide)
      (amm4CtorSenderMem1_read64 I t0 t1 liquidity))
    (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd385⟩

noncomputable def amm4CtorInitialSelectorMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).write 0
      (amm4CtorSenderMem1 I t0 t1 liquidity) 224 32

theorem amm4CtorReachInitialToken1Selector
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨397⟩ [⟨224⟩, UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialSelectorMem I t0 t1 liquidity)
      (UInt256.ofNat 8) ByteArray.empty
      (createdAccounts, amm4CtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd385⟩ := amm4CtorReachInitialToken1FreePtr
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd396 := amm4_ctor_run rd385 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselector : UInt256.land ⟨4294967295⟩ ⟨1889567281⟩ =
      ⟨1889567281⟩ := by native_decide
  rw [hselector] at rd396
  have rd397 := rd396.mstore 3
    (amm4CtorInitialSelectorMem I t0 t1 liquidity) (UInt256.ofNat 8)
    (by amm4_ctor_decode) mem_cost (by rfl) (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd397⟩

end Benchmarks.ActAmm4
