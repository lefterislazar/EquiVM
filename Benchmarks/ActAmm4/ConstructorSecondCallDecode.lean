import Benchmarks.ActAmm4.ConstructorSecondCall
import Benchmarks.ActAmm4.ConstructorDecodeRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorSecondCallSucceeded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 d0 d1 d2 : UInt256}
    {mem ret : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨575⟩ [⟨1⟩, d0, d1, d2,
        v1, liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨594⟩ [v1, liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k' C' := by
  exact ⟨_, _, amm4_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨589⟩,
    jumpiT (by decide) (by amm4_ctor_jd), jumpdest,
    pop, pop, pop, pop]⟩

theorem amm4CtorSecondCallPostCallMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hretsz2 : ret2.size < UInt256.size) :
    (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray (amm4CtorSecondCallFreePtr ret1) := by
  unfold amm4CtorSecondCallPostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret2.size)).toNat
  change (ret2.write 0 (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
    (amm4CtorSecondCallFreePtr ret1).toNat len).readWithPadding 64 32 = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
    exact amm4CtorSecondCallArgMem_read64 I t0 t1 liquidity ret1
      (by have h := hbound1; norm_num [UInt256.size] at *; omega) hbound1
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret2.size then 32 else ret2.size := by
      by_cases hlo : 32 ≤ ret2.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret2.size) (by decide) hlo hretsz2)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret2.size) (by decide) (by omega) hretsz2)
    have hsrc : len ≤ ret2.size := by rw [hlenEq]; split_ifs <;> omega
    rw [write_read_below_gen_extend ret2
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
      (amm4CtorSecondCallFreePtr ret1).toNat len 64 hzero hsrc
      (by have hsize := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1;
          omega)
      (by have hptr := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1;
          omega)]
    exact amm4CtorSecondCallArgMem_read64 I t0 t1 liquidity ret1
      (by have h := hbound1; norm_num [UInt256.size] at *; omega) hbound1

theorem amm4CtorSecondCallPostCallMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hretsz2 : ret2.size < UInt256.size) :
    (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2).size =
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).size := by
  unfold amm4CtorSecondCallPostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret2.size)).toNat
  change (ret2.write 0 (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
    (amm4CtorSecondCallFreePtr ret1).toNat len).size = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret2.size then 32 else ret2.size := by
      by_cases hlo : 32 ≤ ret2.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret2.size) (by decide) hlo hretsz2)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret2.size) (by decide) (by omega) hretsz2)
    have hlen : len ≤ 32 := by rw [hlenEq]; split_ifs <;> omega
    have hsrc : len ≤ ret2.size := by rw [hlenEq]; split_ifs <;> omega
    have hbase := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hin : (amm4CtorSecondCallFreePtr ret1).toNat + len ≤
        (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).size := by omega
    rw [write_eq_gen ret2
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
      (amm4CtorSecondCallFreePtr ret1).toNat len hzero hsrc hin,
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem amm4CtorSecondReturnFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret1 ret2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hretsz2 : ret2.size < UInt256.size)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨594⟩ [v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨597⟩ [amm4CtorSecondCallFreePtr ret1,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k' C' := by
  let aw := amm4CtorSecondCallArgWords ret1
  let fp := amm4CtorSecondCallFreePtr ret1
  have hmem : (⟨64⟩ : UInt256).toNat <
      (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2).size := by
    rw [amm4CtorSecondCallPostCallMem_size I t0 t1 liquidity ret1 ret2 hbound1 hretsz2]
    have hsize := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hptr := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    omega
  have haw := amm4CtorSecondCallArgWords_mload64_haw ret1 hlo1 hbound1
  have hsame := amm4CtorSecondCallArgWords_mload64_same ret1 hlo1 hbound1
  have rd596 := amm4_ctor_run rd with [push1 ⟨64⟩]
  have rd597 := RD.mload 0 fp aw rd596
    (by amm4_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4CtorSecondCallPostCallMem_read64 I t0 t1 liquidity ret1 ret2
          hbound1 hretsz2)))
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa only [fp, aw] using rd597⟩

abbrev amm4CtorAfterSecondReturnFreePtr (ret1 ret2 : ByteArray) : UInt256 :=
  amm4CtorSecondCallFreePtr ret1 + amm4MintReturndataRounded ret2

noncomputable def amm4CtorSecondCallDecodeMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (amm4CtorAfterSecondReturnFreePtr ret1 ret2)).write 0
    (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2) 64 32

theorem amm4CtorSecondCallReturnAlloc
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret1 ret2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨597⟩ [amm4CtorSecondCallFreePtr ret1,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallPostCallMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨612⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat ret2.size, amm4CtorSecondCallFreePtr ret1,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k' C' := by
  let aw := amm4CtorSecondCallArgWords ret1
  have hsame := amm4CtorSecondCallArgWords_mload64_same ret1 hlo1 hbound1
  have rd611 := amm4_ctor_run rd with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩,
    dup3, add, and, dup3, add, dup1, push1 ⟨64⟩]
  have rd612 := RD.mstore 0
    (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
    aw rd611 (by amm4_ctor_decode)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (by rfl) hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa only [aw, amm4CtorAfterSecondReturnFreePtr,
    amm4CtorSecondCallDecodeMem, amm4MintReturndataRounded] using rd612⟩

theorem amm4CtorSecondCallToDecoder
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret1 ret2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨612⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat ret2.size, amm4CtorSecondCallFreePtr ret1,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [amm4CtorSecondCallFreePtr ret1,
        amm4CtorSecondCallFreePtr ret1 + UInt256.ofNat ret2.size,
        ⟨625⟩, v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k' C' := by
  have rd1617 := amm4_ctor_run rd with [
    pop, dup2, add, swap1, push2 ⟨625⟩, swap2, swap1,
    push2 ⟨1617⟩, jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1617⟩

theorem amm4CtorSecondCallLenCheckShort
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hshort2 : ret2.size < 32) :
    UInt256.slt
      (UInt256.sub
        (amm4CtorSecondCallFreePtr ret1 + UInt256.ofNat ret2.size)
        (amm4CtorSecondCallFreePtr ret1)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (amm4CtorSecondCallFreePtr ret1).toNat)
    (len := ret2.size) (words := 1)
    (by simpa using hshort2)
    (amm4CtorSecondCallFreePtr ret1).val.isLt
    (by
      have hcap : 2 ^ 138 + 255 + 32 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4CtorSecondCallLenCheckOk
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (amm4CtorSecondCallFreePtr ret1 + UInt256.ofNat ret2.size)
        (amm4CtorSecondCallFreePtr ret1)) ⟨32⟩ = ⟨0⟩ := by
  have hptr := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).2
  have hcheck := solcReturnStaticLenCheckOk
    (base := (amm4CtorSecondCallFreePtr ret1).toNat)
    (len := ret2.size) (words := 1)
    (by simpa using hlo2)
    (by omega : ret2.size < 2 ^ 255)
    (amm4CtorSecondCallFreePtr ret1).val.isLt
    (by
      have hcap : 2 ^ 138 + 255 + 2 ^ 138 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4CtorSecondCallDecodeShortReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret1 ret2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hbound1 : ret1.size < 2 ^ 138) (hshort2 : ret2.size < 32)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [amm4CtorSecondCallFreePtr ret1,
        amm4CtorSecondCallFreePtr ret1 + UInt256.ofNat ret2.size,
        ⟨625⟩, v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k C) :
    RDrev (amm4CtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact amm4CtorDecodeShortReverts
    (amm4CtorSecondCallLenCheckShort ret1 ret2 hbound1 hshort2)
    (by simp only [List.length_cons, List.length_nil]; omega) rd

theorem amm4CtorSecondCallDecodeMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hretsz2 : ret2.size < UInt256.size) :
    (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size =
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).size := by
  unfold amm4CtorSecondCallDecodeMem
  have hpost := amm4CtorSecondCallPostCallMem_size I t0 t1 liquidity
    ret1 ret2 hbound1 hretsz2
  have hbase := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
  have hptr := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1
  rw [toByteArray_write32_size_of_le _ _ 64
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).size
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).size
    hpost
    (by rw [hpost]; omega)
    (by omega)]

theorem amm4CtorSecondCallDecodeMem_readReturn
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hretsz2 : ret2.size < UInt256.size) :
    (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (amm4CtorSecondCallFreePtr ret1).toNat 32 = ret2.extract 0 32 := by
  unfold amm4CtorSecondCallDecodeMem
  have hpost := amm4CtorSecondCallPostCallMem_size I t0 t1 liquidity
    ret1 ret2 hbound1 hretsz2
  have hbase := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
  have hptr := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1
  rw [write32_read_above _ _ 64 (amm4CtorSecondCallFreePtr ret1).toNat
    (by rw [toByteArray_size])
    (by rw [hpost]; omega)
    (by omega)
    (by rw [hpost]; omega)]
  unfold amm4CtorSecondCallPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ret2.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := ret2.size)
      (by decide) hlo2 hretsz2
  rw [hlen, write32_read_back ret2
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1)
    (amm4CtorSecondCallFreePtr ret1).toNat hlo2 (by omega)]

theorem amm4CtorSecondCallArgWords_ptr_haw (ret1 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138) :
    ¬ amm4CtorSecondCallFreePtr ret1 ≥ amm4CtorSecondCallArgWords ret1 * ⟨32⟩ := by
  have haw := amm4CtorSecondCallArgWords_toNat ret1 hlo1 hbound1
  have hptr := amm4CtorSecondCallFreePtr_toNat ret1 hbound1
  have hmul : (amm4CtorSecondCallArgWords ret1).toNat * 32 < UInt256.size := by
    have hle := Nat.div_le_self (ret1.size + 31) 32
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4CtorSecondCallArgWords ret1 * ⟨32⟩).toNat ≤
      (amm4CtorSecondCallFreePtr ret1).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw, hptr] at hle
  omega

theorem amm4CtorSecondCallDecodeWord
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret1 ret2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [amm4CtorSecondCallFreePtr ret1,
        amm4CtorSecondCallFreePtr ret1 + UInt256.ofNat ret2.size,
        ⟨625⟩, v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨625⟩ [UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32)),
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 acc k' C' := by
  let fp := amm4CtorSecondCallFreePtr ret1
  let aw := amm4CtorSecondCallArgWords ret1
  let v2 := UInt256.ofNat (fromByteArrayBigEndian (ret2.extract 0 32))
  have hretsz2 : ret2.size < UInt256.size := by
    have h := hbound2
    norm_num [UInt256.size] at *
    omega
  have hmem : fp.toNat <
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size := by
    rw [amm4CtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hretsz2]
    have hsize := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    change (amm4CtorSecondCallFreePtr ret1).toNat <
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret1).size
    omega
  have hvalue :
      (if fp.toNat ≥ (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).readWithPadding
           fp.toNat 32))) = v2 := by
    rw [mloadValue_eq_readWithPadding_of_lt_size
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2) aw fp
      (amm4CtorSecondCallDecodeMem I t0 t1 liquidity ret1 ret2).size
      rfl hmem (amm4CtorSecondCallArgWords_ptr_haw ret1 hlo1 hbound1)]
    rw [amm4CtorSecondCallDecodeMem_readReturn I t0 t1 liquidity ret1 ret2
      hbound1 hlo2 hretsz2]
  exact amm4CtorDecodeWord
    (amm4CtorSecondCallLenCheckOk ret1 ret2 hbound1 hlo2 hbound2)
    hvalue (amm4CtorSecondCallArgWords_call_same ret1 hlo1 hbound1)
    (by amm4_ctor_jd)
    (by simp only [List.length_cons, List.length_nil]; omega) rd

end Benchmarks.ActAmm4
