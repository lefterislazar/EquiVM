import Benchmarks.ActAmm.ConstructorSupplyTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem ammCtorReachSenderHashKey
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
    (hle : 1000 ≤ liquidity.toNat) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨120⟩ [⟨0⟩, solcSourceWord I, ⟨0⟩, ⟨1⟩,
        UInt256.sub liquidity ⟨1000⟩,
        UInt256.sub liquidity ⟨1000⟩, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σ ⟨0⟩
          (UInt256.sub liquidity ⟨1000⟩)) k C := by
  obtain ⟨_, _, rd70⟩ := ammCtorReachBaseSupplyStored
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle
  have hclean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd120 := amm_ctor_run rd70 with [
    dup1, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and, dup2]
  rw [hclean] at rd120
  rw [hclean] at rd120
  exact ⟨_, _, by simpa using rd120⟩

noncomputable def ammCtorSenderMem0 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray (solcSourceWord I)).write 0
    (ammCtorDecodedMem t0 t1 liquidity) 0 32

noncomputable def ammCtorSenderMem1 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨1⟩).write 0
    (ammCtorSenderMem0 I t0 t1 liquidity) 32 32

theorem ammCtorSenderMem0_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorSenderMem0 I t0 t1 liquidity).size = 224 := by
  unfold ammCtorSenderMem0
  exact toByteArray_write32_size_of_le _ _ 0 224 224
    (ammCtorDecodedMem_size t0 t1 liquidity)
    (by rw [ammCtorDecodedMem_size]; decide) (by decide)

theorem ammCtorSenderMem1_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorSenderMem1 I t0 t1 liquidity).size = 224 := by
  unfold ammCtorSenderMem1
  exact toByteArray_write32_size_of_le _ _ 32 224 224
    (ammCtorSenderMem0_size I t0 t1 liquidity)
    (by rw [ammCtorSenderMem0_size]; decide) (by decide)

theorem ammCtorSenderMem1_read0 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorSenderMem1 I t0 t1 liquidity).readWithPadding 0 32 =
      UInt256.toByteArray (solcSourceWord I) := by
  unfold ammCtorSenderMem1
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
    (by rw [ammCtorSenderMem0_size]; decide) (by decide)]
  unfold ammCtorSenderMem0
  exact toByteArray_write32_read_back _ _ 0 (Nat.zero_le _)

theorem ammCtorSenderMem1_read32 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorSenderMem1 I t0 t1 liquidity).readWithPadding 32 32 =
      UInt256.toByteArray ⟨1⟩ := by
  unfold ammCtorSenderMem1
  exact toByteArray_write32_read_back _ _ 32
    (by rw [ammCtorSenderMem0_size]; decide)

theorem ammCtorSenderMem1_read0_64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    (ammCtorSenderMem1 I t0 t1 liquidity).readWithPadding 0 64 =
      UInt256.toByteArray (solcSourceWord I) ++ UInt256.toByteArray ⟨1⟩ := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
    (by rw [ammCtorSenderMem1_size]; omega)]
  rw [show (ammCtorSenderMem1 I t0 t1 liquidity).extract 0 64 =
      (ammCtorSenderMem1 I t0 t1 liquidity).extract 0 32 ++
        (ammCtorSenderMem1 I t0 t1 liquidity).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [← readWithPadding_eq_extract _ 0
      (by rw [ammCtorSenderMem1_size]; omega),
    ← readWithPadding_eq_extract _ 32
      (by rw [ammCtorSenderMem1_size]; omega),
    ammCtorSenderMem1_read0, ammCtorSenderMem1_read32]

theorem ammCtorSenderMem1_keccak (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
      (ffi.KEC ((ammCtorSenderMem1 I t0 t1 liquidity).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (solcSourceWord I) := by
  rw [ammCtorSenderMem1_read0_64]
  unfold solcMappingSlot
  exact mappingSlot_single (solcSourceWord I) ⟨1⟩

theorem ammCtorReachSenderHashMem
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
    (hle : 1000 ≤ liquidity.toNat) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨127⟩ [⟨32⟩, UInt256.sub liquidity ⟨1000⟩,
        UInt256.sub liquidity ⟨1000⟩, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner σ ⟨0⟩
          (UInt256.sub liquidity ⟨1000⟩)) k C := by
  obtain ⟨_, _, rd120⟩ := ammCtorReachSenderHashKey
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle
  have rd121 := rd120.mstore 0 (ammCtorSenderMem0 I t0 t1 liquidity)
    (UInt256.ofNat 7) (by amm_ctor_decode) mem_cost
    (by rfl) (by native_decide) (by simp)
  have rd126 := amm_ctor_run rd121 with [push1 ⟨32⟩, add, swap1, dup2]
  have rd127 := rd126.mstore 0 (ammCtorSenderMem1 I t0 t1 liquidity)
    (UInt256.ofNat 7) (by amm_ctor_decode) mem_cost
    (by rfl) (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd127⟩

theorem ammCtorReachSenderBalanceStored
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
    (hle : 1000 ≤ liquidity.toNat) :
    ∃ k C, RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨136⟩ [UInt256.sub liquidity ⟨1000⟩, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨0⟩
            (UInt256.sub liquidity ⟨1000⟩))
          (solcMappingSlot ⟨1⟩ (solcSourceWord I))
          (UInt256.sub liquidity ⟨1000⟩)) k C := by
  obtain ⟨_, _, rd127⟩ := ammCtorReachSenderHashMem
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle
  have rd131 := amm_ctor_run rd127 with [push1 ⟨32⟩, add, push0]
  have rd132 := rd131.keccak256 0
    (solcMappingSlot ⟨1⟩ (solcSourceWord I)) (UInt256.ofNat 7)
    (by amm_ctor_decode) mem_cost
    (by simpa using ammCtorSenderMem1_keccak I t0 t1 liquidity)
    (by native_decide) (by simp)
  have rd134 := amm_ctor_run rd132 with [dup2, swap1]
  obtain ⟨_, _, rd135⟩ := rd134.sstore hperm (by amm_ctor_decode) (by simp)
  have rd136 := amm_ctor_run rd135 with [pop]
  exact ⟨_, _, by simpa using rd136⟩

theorem ammCtorEqualTokensRevert
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
    (heq : t0 = t1) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  obtain ⟨_, _, rd136⟩ := ammCtorReachSenderBalanceStored
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle
  subst t1
  have rd184 := amm_ctor_run rd136 with [
    pop, dup2, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, sub]
  rw [u256_sub_self] at rd184
  have rd188 := amm_ctor_run rd184 with [
    push2 ⟨191⟩, jumpiNT (by decide)]
  exact rd188.revertStub (by amm_ctor_decode) (by amm_ctor_decode)
    (by amm_ctor_decode) (by simp)

theorem ammCtorReachDistinctTokens
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
      ⟨191⟩ [liquidity, EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨0⟩
            (UInt256.sub liquidity ⟨1000⟩))
          (solcMappingSlot ⟨1⟩ (solcSourceWord I))
          (UInt256.sub liquidity ⟨1000⟩)) k C := by
  obtain ⟨_, _, rd136⟩ := ammCtorReachSenderBalanceStored
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle
  have rd184 := amm_ctor_run rd136 with [
    pop, dup2, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, sub]
  have hclean0 : UInt256.land solcAddrMask (EVM.word t0) = EVM.word t0 :=
    solcAddrMask_clean_left (ammCtorAddressWord_canonical t0)
  have hclean1 : UInt256.land solcAddrMask (EVM.word t1) = EVM.word t1 :=
    solcAddrMask_clean_left (ammCtorAddressWord_canonical t1)
  rw [hclean0, hclean1] at rd184
  have hword : EVM.word t0 ≠ EVM.word t1 := by
    intro heq
    exact hne (ammCtorAddressWord_injective heq)
  have hsub : UInt256.sub (EVM.word t0) (EVM.word t1) ≠ ⟨0⟩ :=
    u256_sub_ne_zero_of_ne hword
  have rd191 := amm_ctor_run rd184 with [
    push2 ⟨191⟩, jumpiT hsub (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd191⟩

noncomputable def ammCtorSenderStorage (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩
      (UInt256.sub liquidity ⟨1000⟩))
    (solcMappingSlot ⟨1⟩ (solcSourceWord I))
    (UInt256.sub liquidity ⟨1000⟩)

noncomputable def ammCtorStorageWord (σ : AccountMap)
    (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD slot ⟨0⟩)

theorem ammCtorReachToken0Stored
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
      ⟨256⟩ [liquidity, EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (ammCtorSenderStorage I σ liquidity) ⟨3⟩
          (setAddressOffset0Word
            (ammCtorStorageWord (ammCtorSenderStorage I σ liquidity) I ⟨3⟩)
            (EVM.word t0))) k C := by
  obtain ⟨_, _, rd191⟩ := ammCtorReachDistinctTokens
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd201 := amm_ctor_run rd191 with [
    jumpdest, dup3, push1 ⟨3⟩, push0, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd202⟩ := rd201.sload (by amm_ctor_decode) (by simp)
  have rd227 := amm_ctor_run rd202 with [
    dup2, push20 solcAddrMask, mul, not, and]
  have rd253 := amm_ctor_run rd227 with [
    swap1, dup4, push20 solcAddrMask, and, mul, or, swap1]
  obtain ⟨k255, C255, rd255⟩ := rd253.sstore hperm (by amm_ctor_decode) (by simp)
  have rd256 := amm_ctor_run rd255 with [pop]
  have hpow : (⟨256⟩ : UInt256).exp ⟨0⟩ = ⟨1⟩ := by native_decide
  have hmul (w : UInt256) : UInt256.mul w ⟨1⟩ = w := by
    apply u256_inj
    rw [u256_mul_toNat]
    simp only [show (⟨1⟩ : UInt256).toNat = 1 by rfl, Nat.mul_one]
    exact Nat.mod_eq_of_lt w.val.isLt
  simp only [hpow, hmul] at rd256
  have hval :
      UInt256.lor
        (UInt256.land solcAddrMask (EVM.word t0))
        (UInt256.land (UInt256.lnot solcAddrMask)
          (ammCtorStorageWord (ammCtorSenderStorage I σ liquidity) I ⟨3⟩)) =
      setAddressOffset0Word
        (ammCtorStorageWord (ammCtorSenderStorage I σ liquidity) I ⟨3⟩)
        (EVM.word t0) := by
    unfold setAddressOffset0Word
    rw [u256_lor_comm, u256_land_comm solcAddrMask,
      u256_land_comm (UInt256.lnot solcAddrMask)]
  refine ⟨k255 + 1, C255 + 2, ?_⟩
  rw [← hval]
  simpa only [ammCtorSenderStorage, ammCtorStorageWord] using rd256

noncomputable def ammCtorToken0Storage (I : ExecutionEnv) (σ : AccountMap)
    (liquidity : UInt256) (t0 : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner (ammCtorSenderStorage I σ liquidity) ⟨3⟩
    (setAddressOffset0Word
      (ammCtorStorageWord (ammCtorSenderStorage I σ liquidity) I ⟨3⟩)
      (EVM.word t0))

theorem ammCtorReachToken1Stored
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
      ⟨320⟩ [liquidity, EVM.word t1, EVM.word t0]
      (ammCtorSenderMem1 I t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (ammCtorToken0Storage I σ liquidity t0) ⟨4⟩
          (setAddressOffset0Word
            (ammCtorStorageWord (ammCtorToken0Storage I σ liquidity t0) I ⟨4⟩)
            (EVM.word t1))) k C := by
  obtain ⟨_, _, rd256⟩ := ammCtorReachToken0Stored
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv hperm hle hne
  have rd265 := amm_ctor_run rd256 with [
    dup2, push1 ⟨4⟩, push0, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd266⟩ := rd265.sload (by amm_ctor_decode) (by simp)
  have rd291 := amm_ctor_run rd266 with [
    dup2, push20 solcAddrMask, mul, not, and]
  have rd317 := amm_ctor_run rd291 with [
    swap1, dup4, push20 solcAddrMask, and, mul, or, swap1]
  obtain ⟨k319, C319, rd319⟩ := rd317.sstore hperm (by amm_ctor_decode) (by simp)
  have rd320 := amm_ctor_run rd319 with [pop]
  have hpow : (⟨256⟩ : UInt256).exp ⟨0⟩ = ⟨1⟩ := by native_decide
  have hmul (w : UInt256) : UInt256.mul w ⟨1⟩ = w := by
    apply u256_inj
    rw [u256_mul_toNat]
    simp only [show (⟨1⟩ : UInt256).toNat = 1 by rfl, Nat.mul_one]
    exact Nat.mod_eq_of_lt w.val.isLt
  simp only [hpow, hmul] at rd320
  have hval :
      UInt256.lor
        (UInt256.land solcAddrMask (EVM.word t1))
        (UInt256.land (UInt256.lnot solcAddrMask)
          (ammCtorStorageWord (ammCtorToken0Storage I σ liquidity t0) I ⟨4⟩)) =
      setAddressOffset0Word
        (ammCtorStorageWord (ammCtorToken0Storage I σ liquidity t0) I ⟨4⟩)
        (EVM.word t1) := by
    unfold setAddressOffset0Word
    rw [u256_lor_comm, u256_land_comm solcAddrMask,
      u256_land_comm (UInt256.lnot solcAddrMask)]
  refine ⟨k319 + 1, C319 + 2, ?_⟩
  rw [← hval]
  simpa only [ammCtorToken0Storage, ammCtorStorageWord] using rd320

end Benchmarks.ActAmm
