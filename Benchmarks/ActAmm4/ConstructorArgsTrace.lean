import Benchmarks.ActAmm4.ConstructorTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 0
set_option maxRecDepth 2000000

theorem amm4CtorReachBeforeCopy
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨30⟩ [⟨128⟩, ⟨8188⟩, ⟨96⟩, ⟨96⟩, ⟨128⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σ) k C := by
  have rd17 : ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨17⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (createdAccounts, σ) k C := by
    simpa [amm4CtorCode] using
      (amm4CtorReachSetup (createdAccounts := createdAccounts)
        (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (amm4CtorArgTail t0 t1 liquidity) hcode hwv)
  obtain ⟨_, _, rd17⟩ := rd17
  have rd19 := amm4_ctor_run rd17 with [push1 ⟨64⟩]
  have rd20 := rd19.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by amm4_ctor_decode) mem_cost solcFreePtrMem_mload64
    (by native_decide) (by simp)
  have rd30 := amm4_ctor_run rd20 with [
    push2 ⟨8188⟩, codesize, sub, dup1, push2 ⟨8188⟩, dup4]
  have hsize : UInt256.ofNat (amm4CtorCode t0 t1 liquidity).size = ⟨8284⟩ := by
    rw [amm4CtorCode_size]
    decide
  have hsub : UInt256.sub ⟨8284⟩ ⟨8188⟩ = ⟨96⟩ := by decide
  exact ⟨_, _, by simpa [hsize, hsub] using rd30⟩

noncomputable def amm4CtorCopiedArgsMem (t0 t1 : AccountAddress)
    (liquidity : UInt256) : ByteArray :=
  (amm4CtorCode t0 t1 liquidity).write 8188 solcFreePtrMem 128 96

theorem amm4CtorWriteGap96 (src base : ByteArray) (srcAddr : ℕ)
    (hbase : base.size = 96) (hsrc : srcAddr + 96 ≤ src.size) :
    src.write srcAddr base 128 96 =
      base ++ ffi.ByteArray.zeroes 32 ++ src.extract srcAddr (srcAddr + 96) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ 96 = 0),
    if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hpr : min 96 (src.size - srcAddr) = 96 := by omega
  have hsp : min base.size (128 + 96) - (128 + 96) = 0 := by
    rw [hbase]
    decide
  have hdp : 128 - base.size = 32 := by rw [hbase]
  have hz0 : ffi.ByteArray.zeroes 0 = ByteArray.empty := zeroes_zero (by rfl)
  simp only [hpr, hsp, hdp, hz0, ByteArray.data_copySlice,
    ByteArray.data_append, ByteArray.data_extract,
    show (ByteArray.empty).data = (#[] : Array UInt8) from rfl,
    Array.append_empty]
  have hprefix : (base.data ++ (ffi.ByteArray.zeroes 32).data).size = 128 := by
    rw [Array.size_append]
    have hb : base.data.size = 96 := hbase
    rw [hb]
    have hz : (ffi.ByteArray.zeroes 32).data.size = 32 := by
      rw [show (ffi.ByteArray.zeroes 32).data.size =
          (ffi.ByteArray.zeroes 32).size from rfl, ByteArray_zeroes_size]
    omega
  simp [hpr, hprefix, Array.extract_eq_empty_of_le,
    Array.extract_eq_self_of_le, Array.append_assoc]

theorem amm4CtorCopiedArgsMem_eq (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    amm4CtorCopiedArgsMem t0 t1 liquidity =
      solcFreePtrMem ++ ffi.ByteArray.zeroes 32 ++
        amm4CtorArgTail t0 t1 liquidity := by
  rw [amm4CtorCopiedArgsMem]
  rw [amm4CtorWriteGap96 (hbase := solcFreePtrMem_size)
    (hsrc := by rw [amm4CtorCode_size])]
  rw [amm4CtorCode_tail_window]

theorem amm4CtorCopiedArgsMem_size (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorCopiedArgsMem t0 t1 liquidity).size = 224 := by
  rw [amm4CtorCopiedArgsMem_eq, ByteArray.size_append,
    ByteArray.size_append, solcFreePtrMem_size,
    ByteArray_zeroes_size, amm4CtorArgTail_size]

theorem amm4CtorCopiedArgsMem_read_window (t0 t1 : AccountAddress)
    (liquidity : UInt256) (i : ℕ) (hi : i + 32 ≤ 96) :
    (amm4CtorCopiedArgsMem t0 t1 liquidity).readWithPadding (128 + i) 32 =
      (amm4CtorCode t0 t1 liquidity).extract
        (8188 + i) (8188 + i + 32) := by
  rw [readWithPadding_eq_extract _ _ (by
    rw [amm4CtorCopiedArgsMem_size]
    omega)]
  rw [amm4CtorCopiedArgsMem_eq]
  let pfx := solcFreePtrMem ++ ffi.ByteArray.zeroes 32
  have hp : pfx.size = 128 := by
    simp [pfx, ByteArray.size_append, solcFreePtrMem_size,
      ByteArray_zeroes_size]
  change (pfx ++ amm4CtorArgTail t0 t1 liquidity).extract
    (128 + i) (128 + i + 32) = _
  rw [extract_append_right_window pfx (amm4CtorArgTail t0 t1 liquidity)
    (128 + i) (128 + i + 32) (by rw [hp]; omega)]
  rw [hp]
  have hsub0 : 128 + i - 128 = i := by omega
  have hsub1 : 128 + i + 32 - 128 = i + 32 := by omega
  rw [hsub0, hsub1, ← amm4CtorCode_tail_window,
    extract_extract_BA]
  have hmin : min (8188 + (i + 32)) (8188 + 96) = 8188 + i + 32 := by omega
  rw [hmin]

theorem amm4CtorReachAfterCopy
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨31⟩ [⟨96⟩, ⟨128⟩] (amm4CtorCopiedArgsMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd30⟩ := amm4CtorReachBeforeCopy
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd31 := rd30.codecopy 12 (amm4CtorCopiedArgsMem t0 t1 liquidity)
    (UInt256.ofNat 7) (by amm4_ctor_decode) mem_cost (by rfl)
    (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd31⟩

noncomputable def amm4CtorDecodedMem (t0 t1 : AccountAddress)
    (liquidity : UInt256) : ByteArray :=
  (UInt256.toByteArray ⟨224⟩).write 0
    (amm4CtorCopiedArgsMem t0 t1 liquidity) 64 32

theorem amm4CtorDecodedMem_size (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorDecodedMem t0 t1 liquidity).size = 224 := by
  unfold amm4CtorDecodedMem
  exact toByteArray_write32_size_of_le _ _ 64 224 224
    (amm4CtorCopiedArgsMem_size t0 t1 liquidity)
    (by rw [amm4CtorCopiedArgsMem_size]; decide) (by decide)

theorem amm4CtorDecodedMem_read_window (t0 t1 : AccountAddress)
    (liquidity : UInt256) (i : ℕ) (hi : i + 32 ≤ 96) :
    (amm4CtorDecodedMem t0 t1 liquidity).readWithPadding (128 + i) 32 =
      (amm4CtorCode t0 t1 liquidity).extract
        (8188 + i) (8188 + i + 32) := by
  unfold amm4CtorDecodedMem
  rw [write32_read_above _ _ 64 (128 + i)
    (by rw [toByteArray_size])
    (by rw [amm4CtorCopiedArgsMem_size]; omega)
    (by omega)
    (by rw [amm4CtorCopiedArgsMem_size]; omega)]
  exact amm4CtorCopiedArgsMem_read_window t0 t1 liquidity i hi

theorem amm4CtorDecodedMem_read0 (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorDecodedMem t0 t1 liquidity).readWithPadding 128 32 =
      UInt256.toByteArray (EVM.word t0) := by
  simpa [amm4CtorArg0_extract, word_toBytesBE_toByteArray_eq_toByteArray] using
    amm4CtorDecodedMem_read_window t0 t1 liquidity 0 (by omega)

theorem amm4CtorDecodedMem_read1 (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorDecodedMem t0 t1 liquidity).readWithPadding 160 32 =
      UInt256.toByteArray (EVM.word t1) := by
  simpa [amm4CtorArg1_extract, word_toBytesBE_toByteArray_eq_toByteArray] using
    amm4CtorDecodedMem_read_window t0 t1 liquidity 32 (by omega)

theorem amm4CtorDecodedMem_read2 (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (amm4CtorDecodedMem t0 t1 liquidity).readWithPadding 192 32 =
      UInt256.toByteArray liquidity := by
  simpa [amm4CtorArg2_extract, word_toBytesBE_toByteArray_eq_toByteArray] using
    amm4CtorDecodedMem_read_window t0 t1 liquidity 64 (by omega)

theorem amm4CtorDecodedMem_mload0 (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (if (⟨128⟩ : UInt256).toNat ≥ (amm4CtorDecodedMem t0 t1 liquidity).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((amm4CtorDecodedMem t0 t1 liquidity).readWithPadding 128 32))) =
      EVM.word t0 := by
  exact mloadWordValue_of_readWithPadding
    (by rw [amm4CtorDecodedMem_size]; decide) (by decide)
    (by simpa using amm4CtorDecodedMem_read0 t0 t1 liquidity)

theorem amm4CtorDecodedMem_mload1 (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (if (⟨160⟩ : UInt256).toNat ≥ (amm4CtorDecodedMem t0 t1 liquidity).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((amm4CtorDecodedMem t0 t1 liquidity).readWithPadding 160 32))) =
      EVM.word t1 := by
  exact mloadWordValue_of_readWithPadding
    (by rw [amm4CtorDecodedMem_size]; decide) (by decide)
    (by simpa using amm4CtorDecodedMem_read1 t0 t1 liquidity)

theorem amm4CtorDecodedMem_mload2 (t0 t1 : AccountAddress)
    (liquidity : UInt256) :
    (if (⟨192⟩ : UInt256).toNat ≥ (amm4CtorDecodedMem t0 t1 liquidity).size
        ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((amm4CtorDecodedMem t0 t1 liquidity).readWithPadding 192 32))) =
      liquidity := by
  exact mloadWordValue_of_readWithPadding
    (by rw [amm4CtorDecodedMem_size]; decide) (by decide)
    (by simpa using amm4CtorDecodedMem_read2 t0 t1 liquidity)

theorem amm4CtorAddressWord_canonical (a : AccountAddress) :
    (EVM.word a).toNat < EVM.addressModulus := by
  change a.val % EVM.twoPow 256 < EVM.addressModulus
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt (by decide))]
  exact a.isLt

theorem amm4CtorAddressWord_toNat (a : AccountAddress) :
    (EVM.word a).toNat = a.val := by
  change a.val % EVM.twoPow 256 = a.val
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt (by decide))

theorem amm4CtorAddressWord_injective :
    Function.Injective (fun a : AccountAddress => EVM.word a) := by
  intro a b h
  apply Fin.ext
  have hnat := congrArg UInt256.toNat h
  simpa [amm4CtorAddressWord_toNat] using hnat

theorem amm4CtorReachDecoder
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1401⟩ [⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd31⟩ := amm4CtorReachAfterCopy
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd36 := amm4_ctor_run rd31 with [dup2, dup2, add, push1 ⟨64⟩]
  have rd37 := rd36.mstore 0 (amm4CtorDecodedMem t0 t1 liquidity)
    (UInt256.ofNat 7) (by amm4_ctor_decode) mem_cost
    (by
      have h : (⟨96⟩ : UInt256) + ⟨128⟩ = ⟨224⟩ := by decide
      simp [amm4CtorDecodedMem, h,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    (by native_decide) (by simp)
  have rd45 := amm4_ctor_run rd37 with [
    dup2, add, swap1, push2 ⟨49⟩, swap2, swap1, push2 ⟨1401⟩]
  have rd1401 := rd45.jump (by amm4_ctor_decode) (by amm4_ctor_jd) (by evm_ov)
  exact ⟨_, _, by simpa using rd1401⟩

theorem amm4CtorReachDecoderChecked
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1424⟩ [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1401⟩ := amm4CtorReachDecoder
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1424 := amm4_ctor_run rd1401 with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7,
    sub, slt, iszero, push2 ⟨1424⟩,
    jumpiT (by native_decide) (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1424⟩

theorem amm4CtorReachAddr0Routine
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1330⟩ [⟨128⟩, ⟨224⟩, ⟨1437⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1424⟩ := amm4CtorReachDecoderChecked
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1330 := amm4_ctor_run rd1424 with [
    jumpdest, push0, push2 ⟨1437⟩, dup7, dup3, dup8, add,
    push2 ⟨1330⟩, jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1330⟩

theorem amm4CtorReachAddr0Validate
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1308⟩ [EVM.word t0, ⟨1344⟩, EVM.word t0, ⟨128⟩,
        ⟨224⟩, ⟨1437⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1330⟩ := amm4CtorReachAddr0Routine
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1333 := amm4_ctor_run rd1330 with [jumpdest, push0, dup2]
  have rd1334 := rd1333.mload 0 (EVM.word t0) (UInt256.ofNat 7)
    (by amm4_ctor_decode) mem_cost
    (amm4CtorDecodedMem_mload0 t0 t1 liquidity)
    (by native_decide) (by simp)
  have rd1308 := amm4_ctor_run rd1334 with [
    swap1, pop, push2 ⟨1344⟩, dup2, push2 ⟨1308⟩,
    jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1308⟩

theorem amm4CtorReachAddr0Validated
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1344⟩ [EVM.word t0, ⟨128⟩, ⟨224⟩, ⟨1437⟩,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1308⟩ := amm4CtorReachAddr0Validate
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have hclean : UInt256.land (EVM.word t0) solcAddrMask = EVM.word t0 :=
    solcAddrMask_clean (amm4CtorAddressWord_canonical t0)
  have rd1291 := amm4_ctor_run rd1308 with [
    jumpdest, push2 ⟨1317⟩, dup2, push2 ⟨1291⟩,
    jump (by amm4_ctor_jd)]
  have rd1260 := amm4_ctor_run rd1291 with [
    jumpdest, push0, push2 ⟨1301⟩, dup3, push2 ⟨1260⟩,
    jump (by amm4_ctor_jd)]
  have rd1301 := amm4_ctor_run rd1260 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and, swap1, pop,
    swap2, swap1, pop, jump (by amm4_ctor_jd)]
  have rd1317 := amm4_ctor_run rd1301 with [
    jumpdest, swap1, pop, swap2, swap1, pop,
    jump (by amm4_ctor_jd)]
  have rd1327 := amm4_ctor_run rd1317 with [
    jumpdest, dup2, eq, push2 ⟨1327⟩,
    jumpiT (by rw [hclean, u256_eq_refl]; decide) (by amm4_ctor_jd)]
  have rd1344 := amm4_ctor_run rd1327 with [
    jumpdest, pop, jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1344⟩

theorem amm4CtorReachAddr1Routine
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1330⟩ [⟨160⟩, ⟨224⟩, ⟨1454⟩, ⟨32⟩,
        ⟨0⟩, ⟨0⟩, EVM.word t0, ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1344⟩ := amm4CtorReachAddr0Validated
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1437 := amm4_ctor_run rd1344 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm4_ctor_jd)]
  have rd1330 := amm4_ctor_run rd1437 with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨1454⟩,
    dup7, dup3, dup8, add, push2 ⟨1330⟩,
    jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1330⟩

theorem amm4CtorReachAddr1Validated
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1344⟩ [EVM.word t1, ⟨160⟩, ⟨224⟩, ⟨1454⟩,
        ⟨32⟩, ⟨0⟩, ⟨0⟩, EVM.word t0, ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1330⟩ := amm4CtorReachAddr1Routine
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have hclean : UInt256.land (EVM.word t1) solcAddrMask = EVM.word t1 :=
    solcAddrMask_clean (amm4CtorAddressWord_canonical t1)
  have rd1333 := amm4_ctor_run rd1330 with [jumpdest, push0, dup2]
  have rd1334 := rd1333.mload 0 (EVM.word t1) (UInt256.ofNat 7)
    (by amm4_ctor_decode) mem_cost
    (amm4CtorDecodedMem_mload1 t0 t1 liquidity)
    (by native_decide) (by simp)
  have rd1308 := amm4_ctor_run rd1334 with [
    swap1, pop, push2 ⟨1344⟩, dup2, push2 ⟨1308⟩,
    jump (by amm4_ctor_jd)]
  have rd1291 := amm4_ctor_run rd1308 with [
    jumpdest, push2 ⟨1317⟩, dup2, push2 ⟨1291⟩,
    jump (by amm4_ctor_jd)]
  have rd1260 := amm4_ctor_run rd1291 with [
    jumpdest, push0, push2 ⟨1301⟩, dup3, push2 ⟨1260⟩,
    jump (by amm4_ctor_jd)]
  have rd1301 := amm4_ctor_run rd1260 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and, swap1, pop,
    swap2, swap1, pop, jump (by amm4_ctor_jd)]
  have rd1317 := amm4_ctor_run rd1301 with [
    jumpdest, swap1, pop, swap2, swap1, pop,
    jump (by amm4_ctor_jd)]
  have rd1327 := amm4_ctor_run rd1317 with [
    jumpdest, dup2, eq, push2 ⟨1327⟩,
    jumpiT (by rw [hclean, u256_eq_refl]; decide) (by amm4_ctor_jd)]
  have rd1344 := amm4_ctor_run rd1327 with [
    jumpdest, pop, jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1344⟩

theorem amm4CtorReachLiquidityRoutine
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1381⟩ [⟨192⟩, ⟨224⟩, ⟨1471⟩, ⟨64⟩, ⟨0⟩,
        EVM.word t1, EVM.word t0, ⟨128⟩, ⟨224⟩, ⟨49⟩]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1344⟩ := amm4CtorReachAddr1Validated
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1454 := amm4_ctor_run rd1344 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm4_ctor_jd)]
  have rd1381 := amm4_ctor_run rd1454 with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨1471⟩,
    dup7, dup3, dup8, add, push2 ⟨1381⟩,
    jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1381⟩

theorem amm4CtorReachBody
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (hcode : I.code = amm4CtorCode t0 t1 liquidity)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨49⟩ [liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorDecodedMem t0 t1 liquidity)
      (UInt256.ofNat 7) ByteArray.empty (createdAccounts, σ) k C := by
  obtain ⟨_, _, rd1381⟩ := amm4CtorReachLiquidityRoutine
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    t0 t1 liquidity hcode hwv
  have rd1384 := amm4_ctor_run rd1381 with [jumpdest, push0, dup2]
  have rd1385 := rd1384.mload 0 liquidity (UInt256.ofNat 7)
    (by amm4_ctor_decode) mem_cost
    (amm4CtorDecodedMem_mload2 t0 t1 liquidity)
    (by native_decide) (by simp)
  have rd1359 := amm4_ctor_run rd1385 with [
    swap1, pop, push2 ⟨1395⟩, dup2, push2 ⟨1359⟩,
    jump (by amm4_ctor_jd)]
  have rd1350 := amm4_ctor_run rd1359 with [
    jumpdest, push2 ⟨1368⟩, dup2, push2 ⟨1350⟩,
    jump (by amm4_ctor_jd)]
  have rd1368 := amm4_ctor_run rd1350 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by amm4_ctor_jd)]
  have rd1378 := amm4_ctor_run rd1368 with [
    jumpdest, dup2, eq, push2 ⟨1378⟩,
    jumpiT (by rw [u256_eq_refl]; decide) (by amm4_ctor_jd)]
  have rd1395 := amm4_ctor_run rd1378 with [
    jumpdest, pop, jump (by amm4_ctor_jd)]
  have rd1471 := amm4_ctor_run rd1395 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm4_ctor_jd)]
  have rd49 := amm4_ctor_run rd1471 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, pop,
    swap3, jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd49⟩

end Benchmarks.ActAmm4
