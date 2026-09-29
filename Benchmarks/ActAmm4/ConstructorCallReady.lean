import Benchmarks.ActAmm4.ConstructorEncodeAddress

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorInitialToken1ArgMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val))).write 0
      (amm4CtorInitialSelectorMem I t0 t1 liquidity) 228 32

theorem amm4CtorReachInitialToken1Encoded
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
      ⟨409⟩ [⟨260⟩, ⟨1889567281⟩,
        amm4CtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1ArgMem I t0 t1 liquidity)
      (UInt256.ofNat 9) ByteArray.empty
      (createdAccounts, amm4CtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd397⟩ := amm4CtorReachInitialToken1Selector
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd1592 := amm4_ctor_run rd397 with [
    push1 ⟨4⟩, add, push2 ⟨409⟩, swap2, swap1,
    push2 ⟨1592⟩, jump (by amm4_ctor_jd)]
  have hsum : (⟨4⟩ : UInt256) + ⟨224⟩ = ⟨228⟩ := by native_decide
  rw [hsum] at rd1592
  obtain ⟨_, _, rd409⟩ := RD.amm4CtorEncodeAddressArg rd1592
    (by amm4_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have hend : (⟨228⟩ : UInt256) + ⟨32⟩ = ⟨260⟩ := by native_decide
  have haw : UInt256.ofNat (MachineState.M 8 228 32) = ⟨9⟩ := by native_decide
  exact ⟨_, _, by simpa only [hend, haw, amm4CtorInitialToken1ArgMem] using rd409⟩

theorem amm4CtorInitialSelectorMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorInitialSelectorMem I t0 t1 liquidity).size = 256 := by
  unfold amm4CtorInitialSelectorMem
  exact toByteArray_write32_size_of_le _ _ 224 224 256
    (amm4CtorSenderMem1_size I t0 t1 liquidity)
    (by rw [amm4CtorSenderMem1_size]) (by decide)

theorem amm4CtorInitialToken1ArgMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorInitialToken1ArgMem I t0 t1 liquidity).size = 260 := by
  unfold amm4CtorInitialToken1ArgMem
  exact toByteArray_write32_size_of_le _ _ 228 256 260
    (amm4CtorInitialSelectorMem_size I t0 t1 liquidity)
    (by rw [amm4CtorInitialSelectorMem_size]; decide) (by decide)

theorem amm4CtorInitialToken1ArgMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 64 32 =
      UInt256.toByteArray ⟨224⟩ := by
  unfold amm4CtorInitialToken1ArgMem
  rw [write32_read_below _ _ 228 64
    (by rw [toByteArray_size])
    (by rw [amm4CtorInitialSelectorMem_size]; decide)
    (by decide)]
  unfold amm4CtorInitialSelectorMem
  rw [write32_read_below _ _ 224 64
    (by rw [toByteArray_size])
    (by rw [amm4CtorSenderMem1_size])
    (by decide)]
  exact amm4CtorSenderMem1_read64 I t0 t1 liquidity

theorem amm4CtorInitialToken1ArgMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 4 =
      balanceOfSelector := by
  unfold amm4CtorInitialToken1ArgMem
  rw [write32_read_below_len _ _ 228 224 4
    (by rw [toByteArray_size])
    (by rw [amm4CtorInitialSelectorMem_size]; decide)
    (by decide)
    (by rw [amm4CtorInitialSelectorMem_size]; decide)
    (by decide) (by decide)]
  unfold amm4CtorInitialSelectorMem
  rw [write32_read_prefix_len _ _ 224 4
    (by rw [toByteArray_size])
    (by rw [amm4CtorSenderMem1_size])
    (by decide) (by decide) (by decide)]
  native_decide

theorem amm4CtorInitialToken1ArgMem_read32 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 228 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold amm4CtorInitialToken1ArgMem
  rw [toByteArray_write32_read_back _ _ 228
    (by rw [amm4CtorInitialSelectorMem_size]; decide)]
  have hcanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus :=
    amm4CtorAddressWord_canonical I.codeOwner
  rw [solcAddrMask_clean_left hcanon]

theorem amm4CtorInitialToken1ArgMem_read36 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  rw [byteArray_readWithPadding_split _ 224 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [amm4CtorInitialToken1ArgMem_size])]
  rw [amm4CtorInitialToken1ArgMem_read4,
    amm4CtorInitialToken1ArgMem_read32]

theorem amm4CtorInitialToken1ArgMem_encode (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4CtorInitialToken1ArgMem I t0 t1 liquidity).readWithPadding 224 36) := by
  rw [amm4CtorInitialToken1ArgMem_read36]
  have hword : EVM.word (↑I.codeOwner.val) = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem amm4CtorReachInitialToken1Staticcall
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
    ∃ gasWord k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨421⟩ [gasWord,
        amm4CtorInitialToken1Target I σ liquidity t0 t1,
        ⟨224⟩, ⟨36⟩, ⟨224⟩, ⟨32⟩,
        ⟨260⟩, ⟨1889567281⟩,
        amm4CtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1ArgMem I t0 t1 liquidity)
      (UInt256.ofNat 9) ByteArray.empty
      (createdAccounts, amm4CtorToken1Storage I σ liquidity t0 t1) k C := by
  obtain ⟨_, _, rd409⟩ := amm4CtorReachInitialToken1Encoded
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd414 := amm4_ctor_run rd409 with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd415 := rd414.mload 0 ⟨224⟩ (UInt256.ofNat 9)
    (by amm4_ctor_decode) mem_cost
    (mloadWordValue_of_readWithPadding
      (by rw [amm4CtorInitialToken1ArgMem_size]; decide)
      (by native_decide)
      (amm4CtorInitialToken1ArgMem_read64 I t0 t1 liquidity))
    (by native_decide) (by simp)
  have rd420 := amm4_ctor_run rd415 with [dup1, dup4, sub, dup2, dup7]
  have hsub : UInt256.sub ⟨260⟩ ⟨224⟩ = ⟨36⟩ := by native_decide
  rw [hsub] at rd420
  obtain ⟨gasWord, rd421⟩ := rd420.gas (by amm4_ctor_decode) (by simp)
  exact ⟨gasWord, _, _, by simpa using rd421⟩

end Benchmarks.ActAmm4
