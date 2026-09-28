import Benchmarks.ActAmm.ConstructorStorageTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

noncomputable def ammCtorToken1Storage (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (ammCtorToken0Storage I σ liquidity t0) ⟨4⟩
    (setAddressOffset0Word
      (ammCtorStorageWord (ammCtorToken0Storage I σ liquidity t0) I ⟨4⟩)
      (EVM.word t1))

noncomputable def ammCtorInitialToken1Target (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) (t0 t1 : AccountAddress) : UInt256 :=
  UInt256.land solcAddrMask
    (UInt256.land solcAddrMask
      (UInt256.div
        (ammCtorStorageWord (ammCtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩)
        (UInt256.exp ⟨256⟩ ⟨0⟩)))

theorem ammCtorInitialToken1Target_eq_masked (I : ExecutionEnv)
    (σ : AccountMap) (liquidity : UInt256) (t0 t1 : AccountAddress) :
    ammCtorInitialToken1Target I σ liquidity t0 t1 =
      UInt256.land
        (ammCtorStorageWord (ammCtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩)
        solcAddrMask := by
  let w := ammCtorStorageWord (ammCtorToken1Storage I σ liquidity t0 t1) I ⟨4⟩
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
  unfold ammCtorInitialToken1Target
  simp only [w, hdiv, hmask]

theorem ammCtorReachInitialToken1Target
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨376⟩ [ammCtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, ammCtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd320⟩ := ammCtorReachToken1Stored
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd324 := amm_ctor_run rd320 with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd325⟩ := rd324.sload (by amm_ctor_decode) (by simp)
  have rd376 := amm_ctor_run rd325 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by simpa only [ammCtorToken1Storage,
    ammCtorStorageWord, ammCtorInitialToken1Target] using rd376⟩

theorem ammCtorSenderMem1_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorSenderMem1 I t0 t1 liquidity).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold ammCtorSenderMem1
  rw [write32_read_above _ _ 32 64
    (by rw [toByteArray_size])
    (by rw [ammCtorSenderMem0_size]; decide)
    (by decide)
    (by rw [ammCtorSenderMem0_size]; decide)]
  unfold ammCtorSenderMem0
  rw [write32_read_above _ _ 0 64
    (by rw [toByteArray_size])
    (by rw [ammCtorDecodedMem_size]; decide)
    (by decide)
    (by rw [ammCtorDecodedMem_size]; decide)]
  unfold ammCtorDecodedMem
  exact toByteArray_write32_read_back _ _ 64
    (by rw [ammCtorCopiedArgsMem_size]; decide)

theorem ammCtorReachInitialToken1FreePtr
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨385⟩ [⟨224⟩, UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts, ammCtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd376⟩ := ammCtorReachInitialToken1Target
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd384 := amm_ctor_run rd376 with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd385 := rd384.mload 0 ⟨224⟩ (UInt256.ofNat 7)
    (by amm_ctor_decode) mem_cost
    (mloadWordValue_of_readWithPadding
      (by rw [ammCtorSenderMem1_size]; decide)
      (by native_decide)
      (ammCtorSenderMem1_read64 I t0 t1 liquidity))
    (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd385⟩

noncomputable def ammCtorInitialSelectorMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).write 0
      (ammCtorSenderMem1 I t0 t1 liquidity) 224 32

theorem ammCtorReachInitialToken1Selector
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = ammCtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true)
    (hle : 1000 ≤ liquidity.toNat)
    (hne : t0 ≠ t1) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨397⟩ [⟨224⟩, UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialSelectorMem I t0 t1 liquidity)
      (UInt256.ofNat 8) ByteArray.empty
      (createdAccounts, ammCtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd385⟩ := ammCtorReachInitialToken1FreePtr
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd396 := amm_ctor_run rd385 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselector : UInt256.land ⟨4294967295⟩ ⟨1889567281⟩ =
      ⟨1889567281⟩ := by native_decide
  rw [hselector] at rd396
  have rd397 := rd396.mstore 3
    (ammCtorInitialSelectorMem I t0 t1 liquidity) (UInt256.ofNat 8)
    (by amm_ctor_decode) mem_cost (by rfl) (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd397⟩

end Benchmarks.ActAmm
