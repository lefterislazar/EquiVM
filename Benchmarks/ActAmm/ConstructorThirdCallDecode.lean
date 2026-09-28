import Benchmarks.ActAmm.ConstructorThirdCall
import Benchmarks.ActAmm.ConstructorDecodeRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorThirdCallSucceeded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress}
    {liquidity d0 d1 d2 : UInt256} {mem ret : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1033⟩ [⟨1⟩, d0, d1, d2,
        liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1052⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k' C' := by
  exact ⟨_, _, amm_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨1047⟩,
    jumpiT (by decide) (by amm_ctor_jd), jumpdest,
    pop, pop, pop, pop]⟩

theorem ammCtorThirdCallPostCallMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hretsz3 : ret3.size < UInt256.size) :
    (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      64 32 = UInt256.toByteArray
        (ammCtorAfterSecondReturnFreePtr ret1 ret2) := by
  unfold ammCtorThirdCallPostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret3.size)).toNat
  change (ret3.write 0 (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat len).readWithPadding
      64 32 = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
    exact ammCtorThirdCallArgMem_read64 I t0 t1 liquidity ret1 ret2
      hbound1 hbound2
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret3.size then 32 else ret3.size := by
      by_cases hlo : 32 ≤ ret3.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret3.size) (by decide) hlo hretsz3)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret3.size) (by decide) (by omega) hretsz3)
    have hsrc : len ≤ ret3.size := by rw [hlenEq]; split_ifs <;> omega
    rw [write_read_below_gen_extend ret3
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat len 64 hzero hsrc
      (by
        have hsize := ammCtorThirdCallArgMem_size I t0 t1 liquidity
          ret1 ret2 hbound1 hbound2
        omega)
      (by
        have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
          hbound1 hbound2).1
        omega)]
    exact ammCtorThirdCallArgMem_read64 I t0 t1 liquidity ret1 ret2
      hbound1 hbound2

theorem ammCtorThirdCallPostCallMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hretsz3 : ret3.size < UInt256.size) :
    (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3).size =
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by
  unfold ammCtorThirdCallPostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret3.size)).toNat
  change (ret3.write 0 (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat len).size = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret3.size then 32 else ret3.size := by
      by_cases hlo : 32 ≤ ret3.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret3.size) (by decide) hlo hretsz3)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret3.size) (by decide) (by omega) hretsz3)
    have hlen : len ≤ 32 := by rw [hlenEq]; split_ifs <;> omega
    have hsrc : len ≤ ret3.size := by rw [hlenEq]; split_ifs <;> omega
    have hbase := ammCtorThirdCallArgMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hbound2
    have hin : (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + len ≤
        (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by omega
    rw [write_eq_gen ret3
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat len hzero hsrc hin,
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem ammCtorThirdReturnFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hretsz3 : ret3.size < UInt256.size)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1052⟩ [liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1055⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k' C' := by
  let aw := ammCtorThirdCallArgWords ret1 ret2
  let fp := ammCtorAfterSecondReturnFreePtr ret1 ret2
  have hmem : (⟨64⟩ : UInt256).toNat <
      (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3).size := by
    rw [ammCtorThirdCallPostCallMem_size I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hretsz3]
    have hsize := ammCtorThirdCallArgMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hbound2
    have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    omega
  have haw := ammCtorThirdCallArgWords_mload64_haw ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hsame := ammCtorThirdCallArgWords_mload64_same ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have rd1054 := amm_ctor_run rd with [push1 ⟨64⟩]
  have rd1055 := RD.mload 0 fp aw rd1054
    (by amm_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammCtorThirdCallPostCallMem_read64 I t0 t1 liquidity
          ret1 ret2 ret3 hbound1 hbound2 hretsz3)))
    (by simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using hsame)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa only [fp, aw] using rd1055⟩

abbrev ammCtorAfterThirdReturnFreePtr (ret1 ret2 ret3 : ByteArray) : UInt256 :=
  ammCtorAfterSecondReturnFreePtr ret1 ret2 + ammMintReturndataRounded ret3

noncomputable def ammCtorThirdCallDecodeMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3)).write 0
    (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3) 64 32

theorem ammCtorThirdCallReturnAlloc
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1055⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1070⟩ [ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat ret3.size, ammCtorAfterSecondReturnFreePtr ret1 ret2,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k' C' := by
  let aw := ammCtorThirdCallArgWords ret1 ret2
  have hsame := ammCtorThirdCallArgWords_mload64_same ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have rd1069 := amm_ctor_run rd with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩,
    dup3, add, and, dup3, add, dup1, push1 ⟨64⟩]
  have rd1070 := RD.mstore 0
    (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
    aw rd1069 (by amm_ctor_decode)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (by rfl)
    (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using hsame)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa only [aw, ammCtorAfterThirdReturnFreePtr,
    ammCtorThirdCallDecodeMem, ammMintReturndataRounded] using rd1070⟩

theorem ammCtorThirdCallToDecoder
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1070⟩ [ammCtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat ret3.size, ammCtorAfterSecondReturnFreePtr ret1 ret2,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        ammCtorAfterSecondReturnFreePtr ret1 ret2 + UInt256.ofNat ret3.size,
        ⟨1083⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k' C' := by
  have rd1617 := amm_ctor_run rd with [
    pop, dup2, add, swap1, push2 ⟨1083⟩, swap2, swap1,
    push2 ⟨1617⟩, jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd1617⟩

theorem ammCtorThirdCallLenCheckShort (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hshort3 : ret3.size < 32) :
    UInt256.slt
      (UInt256.sub
        (ammCtorAfterSecondReturnFreePtr ret1 ret2 + UInt256.ofNat ret3.size)
        (ammCtorAfterSecondReturnFreePtr ret1 ret2)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
    hbound1 hbound2).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat)
    (len := ret3.size) (words := 1)
    (by simpa using hshort3)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).val.isLt
    (by
      have hcap : 2 ^ 141 + 32 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammCtorThirdCallLenCheckOk (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (ammCtorAfterSecondReturnFreePtr ret1 ret2 + UInt256.ofNat ret3.size)
        (ammCtorAfterSecondReturnFreePtr ret1 ret2)) ⟨32⟩ = ⟨0⟩ := by
  have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
    hbound1 hbound2).2
  have hcheck := solcReturnStaticLenCheckOk
    (base := (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat)
    (len := ret3.size) (words := 1)
    (by simpa using hlo3)
    (by omega : ret3.size < 2 ^ 255)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).val.isLt
    (by
      have hcap : 2 ^ 141 + 2 ^ 138 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammCtorThirdCallDecodeShortReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hshort3 : ret3.size < 32)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        ammCtorAfterSecondReturnFreePtr ret1 ret2 + UInt256.ofNat ret3.size,
        ⟨1083⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k C) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact ammCtorDecodeShortReverts
    (ammCtorThirdCallLenCheckShort ret1 ret2 ret3 hbound1 hbound2 hshort3)
    (by simp only [List.length_cons, List.length_nil]; omega) rd

theorem ammCtorThirdCallDecodeMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hretsz3 : ret3.size < UInt256.size) :
    (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size =
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by
  unfold ammCtorThirdCallDecodeMem
  have hpost := ammCtorThirdCallPostCallMem_size I t0 t1 liquidity
    ret1 ret2 ret3 hbound1 hbound2 hretsz3
  have hbase := ammCtorThirdCallArgMem_size I t0 t1 liquidity
    ret1 ret2 hbound1 hbound2
  have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
    hbound1 hbound2).1
  rw [toByteArray_write32_size_of_le _ _ 64
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size
    hpost
    (by rw [hpost]; omega)
    (by omega)]

theorem ammCtorThirdCallDecodeMem_readReturn
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hretsz3 : ret3.size < UInt256.size) :
    (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 32 =
        ret3.extract 0 32 := by
  unfold ammCtorThirdCallDecodeMem
  have hpost := ammCtorThirdCallPostCallMem_size I t0 t1 liquidity
    ret1 ret2 ret3 hbound1 hbound2 hretsz3
  have hbase := ammCtorThirdCallArgMem_size I t0 t1 liquidity
    ret1 ret2 hbound1 hbound2
  have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
    hbound1 hbound2).1
  rw [write32_read_above _ _ 64 (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat
    (by rw [toByteArray_size])
    (by rw [hpost]; omega)
    (by omega)
    (by rw [hpost]; omega)]
  unfold ammCtorThirdCallPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ret3.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := ret3.size)
      (by decide) hlo3 hretsz3
  rw [hlen, write32_read_back ret3
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat hlo3 (by omega)]

theorem ammCtorThirdCallArgWords_ptr_haw (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    ¬ ammCtorAfterSecondReturnFreePtr ret1 ret2 ≥
      ammCtorThirdCallArgWords ret1 ret2 * ⟨32⟩ := by
  have haw := ammCtorThirdCallArgWords_toNat ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hptr := ammCtorAfterSecondReturnFreePtr_toNat ret1 ret2
    hbound1 hbound2
  have hmul : (ammCtorThirdCallArgWords ret1 ret2).toNat * 32 <
      UInt256.size := by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : (2 ^ 138 + 2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (ammCtorThirdCallArgWords ret1 ret2 * ⟨32⟩).toNat ≤
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw, hptr] at hle
  omega

theorem ammCtorThirdCallDecodeWord
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        ammCtorAfterSecondReturnFreePtr ret1 ret2 + UInt256.ofNat ret3.size,
        ⟨1083⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1083⟩ [UInt256.ofNat (fromByteArrayBigEndian (ret3.extract 0 32)),
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (ammCtorThirdCallArgWords ret1 ret2) ret3 acc k' C' := by
  let fp := ammCtorAfterSecondReturnFreePtr ret1 ret2
  let aw := ammCtorThirdCallArgWords ret1 ret2
  let v3 := UInt256.ofNat (fromByteArrayBigEndian (ret3.extract 0 32))
  have hretsz3 : ret3.size < UInt256.size := by
    have h := hbound3
    norm_num [UInt256.size] at *
    omega
  have hmem : fp.toNat <
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size := by
    rw [ammCtorThirdCallDecodeMem_size I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hretsz3]
    have hsize := ammCtorThirdCallArgMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hbound2
    change (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat <
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size
    omega
  have hvalue :
      (if fp.toNat ≥
            (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
           fp.toNat 32))) = v3 := by
    rw [mloadValue_eq_readWithPadding_of_lt_size
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3) aw fp
      (ammCtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size
      rfl hmem (ammCtorThirdCallArgWords_ptr_haw ret1 ret2
        hlo1 hbound1 hlo2 hbound2)]
    rw [ammCtorThirdCallDecodeMem_readReturn I t0 t1 liquidity
      ret1 ret2 ret3 hbound1 hbound2 hlo3 hretsz3]
  exact ammCtorDecodeWord
    (ammCtorThirdCallLenCheckOk ret1 ret2 ret3
      hbound1 hbound2 hlo3 hbound3)
    hvalue
    (by
      rw [ammCtorThirdCallArgWords_call_nat_same ret1 ret2
        hlo1 hbound1 hlo2 hbound2 32 (Or.inl rfl)]
      exact u256_ofNat_toNat _)
    (by amm_ctor_jd)
    (by simp only [List.length_cons, List.length_nil]; omega) rd

end Benchmarks.ActAmm
