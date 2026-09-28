import Benchmarks.ActAmm.ConstructorEncodeAddress

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorInitialToken1ArgMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val))).write 0
      (ammCtorInitialSelectorMem I t0 t1 liquidity) 228 32

theorem ammCtorReachInitialToken1Encoded
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
      ⟨409⟩ [⟨260⟩, ⟨1889567281⟩,
        ammCtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1ArgMem I t0 t1 liquidity)
      (UInt256.ofNat 9) ByteArray.empty
      (createdAccounts, ammCtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd397⟩ := ammCtorReachInitialToken1Selector
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd1592 := amm_ctor_run rd397 with [
    push1 ⟨4⟩, add, push2 ⟨409⟩, swap2, swap1,
    push2 ⟨1592⟩, jump (by amm_ctor_jd)]
  have hsum : (⟨4⟩ : UInt256) + ⟨224⟩ = ⟨228⟩ := by native_decide
  rw [hsum] at rd1592
  obtain ⟨_, _, rd409⟩ := RD.ammCtorEncodeAddressArg rd1592
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have hend : (⟨228⟩ : UInt256) + ⟨32⟩ = ⟨260⟩ := by native_decide
  have haw : UInt256.ofNat (MachineState.M 8 228 32) = ⟨9⟩ := by native_decide
  exact ⟨_, _, by simpa only [hend, haw, ammCtorInitialToken1ArgMem] using rd409⟩

theorem ammCtorInitialSelectorMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorInitialSelectorMem I t0 t1 liquidity).size = 256 := by
  unfold ammCtorInitialSelectorMem
  exact toByteArray_write32_size_of_le _ _ 224 224 256
    (ammCtorSenderMem1_size I t0 t1 liquidity)
    (by rw [ammCtorSenderMem1_size]) (by decide)

theorem ammCtorInitialToken1ArgMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorInitialToken1ArgMem I t0 t1 liquidity).size = 260 := by
  unfold ammCtorInitialToken1ArgMem
  exact toByteArray_write32_size_of_le _ _ 228 256 260
    (ammCtorInitialSelectorMem_size I t0 t1 liquidity)
    (by rw [ammCtorInitialSelectorMem_size]; decide) (by decide)

theorem ammCtorInitialToken1ArgMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold ammCtorInitialToken1ArgMem
  rw [write32_read_below _ _ 228 64
    (by rw [toByteArray_size])
    (by rw [ammCtorInitialSelectorMem_size]; decide)
    (by decide)]
  unfold ammCtorInitialSelectorMem
  rw [write32_read_below _ _ 224 64
    (by rw [toByteArray_size])
    (by rw [ammCtorSenderMem1_size])
    (by decide)]
  exact ammCtorSenderMem1_read64 I t0 t1 liquidity

theorem ammCtorInitialToken1ArgMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 4 =
      balanceOfSelector := by
  unfold ammCtorInitialToken1ArgMem
  rw [write32_read_below_len _ _ 228 224 4
    (by rw [toByteArray_size])
    (by rw [ammCtorInitialSelectorMem_size]; decide)
    (by decide)
    (by rw [ammCtorInitialSelectorMem_size]; decide)
    (by decide) (by decide)]
  unfold ammCtorInitialSelectorMem
  rw [write32_read_prefix_len _ _ 224 4
    (by rw [toByteArray_size])
    (by rw [ammCtorSenderMem1_size])
    (by decide) (by decide) (by decide)]
  native_decide

theorem ammCtorInitialToken1ArgMem_read32 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 228 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold ammCtorInitialToken1ArgMem
  rw [toByteArray_write32_read_back _ _ 228
    (by rw [ammCtorInitialSelectorMem_size]; decide)]
  have hcanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus :=
    ammCtorAddressWord_canonical I.codeOwner
  rw [solcAddrMask_clean_left hcanon]

theorem ammCtorInitialToken1ArgMem_read36 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  rw [byteArray_readWithPadding_split _ 224 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [ammCtorInitialToken1ArgMem_size])]
  rw [ammCtorInitialToken1ArgMem_read4,
    ammCtorInitialToken1ArgMem_read32]

theorem ammCtorInitialToken1ArgMem_encode (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammCtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36) := by
  rw [ammCtorInitialToken1ArgMem_read36]
  have hword : EVM.word (↑I.codeOwner.val) = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem ammCtorReachInitialToken1Staticcall
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
    ∃ gasWord k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨421⟩ [gasWord,
        ammCtorInitialToken1Target I σ liquidity t0 t1,
        ⟨224⟩, ⟨36⟩, ⟨224⟩, ⟨32⟩,
        ⟨260⟩, ⟨1889567281⟩,
        ammCtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1ArgMem I t0 t1 liquidity)
      (UInt256.ofNat 9) ByteArray.empty
      (createdAccounts, ammCtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd409⟩ := ammCtorReachInitialToken1Encoded
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd414 := amm_ctor_run rd409 with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd415 := rd414.mload 0 ⟨224⟩ (UInt256.ofNat 9)
    (by amm_ctor_decode) mem_cost
    (mloadWordValue_of_readWithPadding
      (by rw [ammCtorInitialToken1ArgMem_size]; decide)
      (by native_decide)
      (ammCtorInitialToken1ArgMem_read64 I t0 t1 liquidity))
    (by native_decide) (by simp)
  have rd420 := amm_ctor_run rd415 with [dup1, dup4, sub, dup2, dup7]
  have hsub : UInt256.sub ⟨260⟩ ⟨224⟩ = ⟨36⟩ := by native_decide
  rw [hsub] at rd420
  obtain ⟨gasWord, rd421⟩ := rd420.gas (by amm_ctor_decode) (by simp)
  exact ⟨gasWord, _, _, by simpa using rd421⟩

end Benchmarks.ActAmm
