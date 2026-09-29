import Benchmarks.ActAmm4.ConstructorFourthCall
import Benchmarks.ActAmm4.ConstructorDecodeRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorFourthCallSucceeded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress}
    {liquidity d0 d1 d2 : UInt256} {mem ret : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1192⟩ [⟨1⟩, d0, d1, d2,
        liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1211⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k' C' := by
  exact ⟨_, _, amm4_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨1206⟩,
    jumpiT (by decide) (by amm4_ctor_jd), jumpdest,
    pop, pop, pop, pop]⟩

theorem amm4CtorFourthCallPostCallMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 ret4 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hretsz4 : ret4.size < UInt256.size) :
    (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4).readWithPadding
      64 32 = UInt256.toByteArray
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3) := by
  unfold amm4CtorFourthCallPostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret4.size)).toNat
  change (ret4.write 0
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat len).readWithPadding
      64 32 = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
    exact amm4CtorFourthCallArgMem_read64 I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hbound3
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret4.size then 32 else ret4.size := by
      by_cases hlo : 32 ≤ ret4.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret4.size) (by decide) hlo hretsz4)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret4.size) (by decide) (by omega) hretsz4)
    have hsrc : len ≤ ret4.size := by rw [hlenEq]; split_ifs <;> omega
    rw [write_read_below_gen_extend ret4
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat len 64 hzero hsrc
      (by
        have hsize := amm4CtorFourthCallArgMem_size I t0 t1 liquidity
          ret1 ret2 ret3 hbound1 hbound2 hbound3
        omega)
      (by
        have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
          hbound1 hbound2 hbound3).1
        omega)]
    exact amm4CtorFourthCallArgMem_read64 I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hbound3

theorem amm4CtorFourthCallPostCallMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 ret4 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hretsz4 : ret4.size < UInt256.size) :
    (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4).size =
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size := by
  unfold amm4CtorFourthCallPostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret4.size)).toNat
  change (ret4.write 0
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat len).size = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret4.size then 32 else ret4.size := by
      by_cases hlo : 32 ≤ ret4.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret4.size) (by decide) hlo hretsz4)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret4.size) (by decide) (by omega) hretsz4)
    have hlen : len ≤ 32 := by rw [hlenEq]; split_ifs <;> omega
    have hsrc : len ≤ ret4.size := by rw [hlenEq]; split_ifs <;> omega
    have hbase := amm4CtorFourthCallArgMem_size I t0 t1 liquidity
      ret1 ret2 ret3 hbound1 hbound2 hbound3
    have hin : (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + len ≤
        (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size := by
      omega
    rw [write_eq_gen ret4
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat len hzero hsrc hin,
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem amm4CtorFourthReturnFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 ret4 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (hretsz4 : ret4.size < UInt256.size)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1211⟩ [liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1214⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k' C' := by
  let aw := amm4CtorFourthCallArgWords ret1 ret2 ret3
  let fp := amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3
  have hmem : (⟨64⟩ : UInt256).toNat <
      (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4).size := by
    rw [amm4CtorFourthCallPostCallMem_size I t0 t1 liquidity
      ret1 ret2 ret3 ret4 hbound1 hbound2 hbound3 hretsz4]
    have hsize := amm4CtorFourthCallArgMem_size I t0 t1 liquidity
      ret1 ret2 ret3 hbound1 hbound2 hbound3
    have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
      hbound1 hbound2 hbound3).1
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    omega
  have haw := amm4CtorFourthCallArgWords_mload64_haw ret1 ret2 ret3
    hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  have hsame := amm4CtorFourthCallArgWords_mload64_same ret1 ret2 ret3
    hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  have rd1213 := amm4_ctor_run rd with [push1 ⟨64⟩]
  have rd1214 := RD.mload 0 fp aw rd1213
    (by amm4_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4CtorFourthCallPostCallMem_read64 I t0 t1 liquidity
          ret1 ret2 ret3 ret4 hbound1 hbound2 hbound3 hretsz4)))
    (by simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using hsame)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa only [fp, aw] using rd1214⟩

abbrev amm4CtorAfterFourthReturnFreePtr
    (ret1 ret2 ret3 ret4 : ByteArray) : UInt256 :=
  amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + amm4MintReturndataRounded ret4

noncomputable def amm4CtorFourthCallDecodeMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 ret4 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (amm4CtorAfterFourthReturnFreePtr ret1 ret2 ret3 ret4)).write 0
    (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4) 64 32

theorem amm4CtorFourthCallReturnAlloc
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 ret4 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1214⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallPostCallMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1229⟩ [amm4CtorAfterFourthReturnFreePtr ret1 ret2 ret3 ret4,
        UInt256.ofNat ret4.size, amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k' C' := by
  let aw := amm4CtorFourthCallArgWords ret1 ret2 ret3
  have hsame := amm4CtorFourthCallArgWords_mload64_same ret1 ret2 ret3
    hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  have rd1228 := amm4_ctor_run rd with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩,
    dup3, add, and, dup3, add, dup1, push1 ⟨64⟩]
  have rd1229 := RD.mstore 0
    (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
    aw rd1228 (by amm4_ctor_decode)
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
  exact ⟨_, _, by simpa only [aw, amm4CtorAfterFourthReturnFreePtr,
    amm4CtorFourthCallDecodeMem, amm4MintReturndataRounded] using rd1229⟩

theorem amm4CtorFourthCallToDecoder
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 ret4 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1229⟩ [amm4CtorAfterFourthReturnFreePtr ret1 ret2 ret3 ret4,
        UInt256.ofNat ret4.size, amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + UInt256.ofNat ret4.size,
        ⟨1242⟩, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k' C' := by
  have rd1617 := amm4_ctor_run rd with [
    pop, dup2, add, swap1, push2 ⟨1242⟩, swap2, swap1,
    push2 ⟨1617⟩, jump (by amm4_ctor_jd)]
  exact ⟨_, _, by simpa using rd1617⟩

theorem amm4CtorFourthCallLenCheckShort
    (ret1 ret2 ret3 ret4 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hshort4 : ret4.size < 32) :
    UInt256.slt
      (UInt256.sub
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + UInt256.ofNat ret4.size)
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
    hbound1 hbound2 hbound3).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat)
    (len := ret4.size) (words := 1)
    (by simpa using hshort4)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).val.isLt
    (by
      have hcap : 2 ^ 141 + 32 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4CtorFourthCallLenCheckOk
    (ret1 ret2 ret3 ret4 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hlo4 : 32 ≤ ret4.size) (hbound4 : ret4.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + UInt256.ofNat ret4.size)
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3)) ⟨32⟩ = ⟨0⟩ := by
  have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
    hbound1 hbound2 hbound3).2
  have hcheck := solcReturnStaticLenCheckOk
    (base := (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat)
    (len := ret4.size) (words := 1)
    (by simpa using hlo4)
    (by omega : ret4.size < 2 ^ 255)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).val.isLt
    (by
      have hcap : 2 ^ 141 + 2 ^ 138 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4CtorFourthCallDecodeShortReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 ret4 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hshort4 : ret4.size < 32)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + UInt256.ofNat ret4.size,
        ⟨1242⟩, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k C) :
    RDrev (amm4CtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  exact amm4CtorDecodeShortReverts
    (amm4CtorFourthCallLenCheckShort ret1 ret2 ret3 ret4
      hbound1 hbound2 hbound3 hshort4)
    (by simp only [List.length_cons, List.length_nil]; omega) rd

theorem amm4CtorFourthCallDecodeMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 ret4 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hretsz4 : ret4.size < UInt256.size) :
    (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4).size =
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size := by
  unfold amm4CtorFourthCallDecodeMem
  have hpost := amm4CtorFourthCallPostCallMem_size I t0 t1 liquidity
    ret1 ret2 ret3 ret4 hbound1 hbound2 hbound3 hretsz4
  have hbase := amm4CtorFourthCallArgMem_size I t0 t1 liquidity
    ret1 ret2 ret3 hbound1 hbound2 hbound3
  have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
    hbound1 hbound2 hbound3).1
  rw [toByteArray_write32_size_of_le _ _ 64
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size
    hpost
    (by rw [hpost]; omega)
    (by omega)]

theorem amm4CtorFourthCallDecodeMem_readReturn
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 ret4 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138) (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138)
    (hlo4 : 32 ≤ ret4.size) (hretsz4 : ret4.size < UInt256.size) :
    (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4).readWithPadding
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 32 =
        ret4.extract 0 32 := by
  unfold amm4CtorFourthCallDecodeMem
  have hpost := amm4CtorFourthCallPostCallMem_size I t0 t1 liquidity
    ret1 ret2 ret3 ret4 hbound1 hbound2 hbound3 hretsz4
  have hbase := amm4CtorFourthCallArgMem_size I t0 t1 liquidity
    ret1 ret2 ret3 hbound1 hbound2 hbound3
  have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
    hbound1 hbound2 hbound3).1
  rw [write32_read_above _ _ 64
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat
    (by rw [toByteArray_size])
    (by rw [hpost]; omega)
    (by omega)
    (by rw [hpost]; omega)]
  unfold amm4CtorFourthCallPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ret4.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := ret4.size)
      (by decide) hlo4 hretsz4
  rw [hlen, write32_read_back ret4
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat hlo4 (by omega)]

theorem amm4CtorFourthCallArgWords_ptr_haw (ret1 ret2 ret3 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138) :
    ¬ amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 ≥
      amm4CtorFourthCallArgWords ret1 ret2 ret3 * ⟨32⟩ := by
  have haw := amm4CtorFourthCallArgWords_toNat ret1 ret2 ret3
    hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  have hptr := amm4CtorAfterThirdReturnFreePtr_toNat ret1 ret2 ret3
    hbound1 hbound2 hbound3
  have hmul : (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat * 32 <
      UInt256.size := by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hle3 := Nat.div_le_self (ret3.size + 31) 32
    have hcap : (3 * 2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4CtorFourthCallArgWords ret1 ret2 ret3 * ⟨32⟩).toNat ≤
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw, hptr] at hle
  omega

theorem amm4CtorFourthCallDecodeWord
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 ret4 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (hlo4 : 32 ≤ ret4.size) (hbound4 : ret4.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + UInt256.ofNat ret4.size,
        ⟨1242⟩, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1242⟩ [UInt256.ofNat (fromByteArrayBigEndian (ret4.extract 0 32)),
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret4 acc k' C' := by
  let fp := amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3
  let aw := amm4CtorFourthCallArgWords ret1 ret2 ret3
  let v4 := UInt256.ofNat (fromByteArrayBigEndian (ret4.extract 0 32))
  have hretsz4 : ret4.size < UInt256.size := by
    have h := hbound4
    norm_num [UInt256.size] at *
    omega
  have hmem : fp.toNat <
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4).size := by
    rw [amm4CtorFourthCallDecodeMem_size I t0 t1 liquidity ret1 ret2 ret3 ret4
      hbound1 hbound2 hbound3 hretsz4]
    have hsize := amm4CtorFourthCallArgMem_size I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hbound3
    change (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat <
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size
    omega
  have hvalue :
      (if fp.toNat ≥
            (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4).readWithPadding
           fp.toNat 32))) = v4 := by
    rw [mloadValue_eq_readWithPadding_of_lt_size
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4) aw fp
      (amm4CtorFourthCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3 ret4).size
      rfl hmem (amm4CtorFourthCallArgWords_ptr_haw ret1 ret2 ret3
        hlo1 hbound1 hlo2 hbound2 hlo3 hbound3)]
    rw [amm4CtorFourthCallDecodeMem_readReturn I t0 t1 liquidity
      ret1 ret2 ret3 ret4 hbound1 hbound2 hbound3 hlo4 hretsz4]
  exact amm4CtorDecodeWord
    (amm4CtorFourthCallLenCheckOk ret1 ret2 ret3 ret4
      hbound1 hbound2 hbound3 hlo4 hbound4)
    hvalue
    (by
      rw [amm4CtorFourthCallArgWords_call_nat_same ret1 ret2 ret3
        hlo1 hbound1 hlo2 hbound2 hlo3 hbound3 32 (Or.inl rfl)]
      exact u256_ofNat_toNat _)
    (by amm4_ctor_jd)
    (by simp only [List.length_cons, List.length_nil]; omega) rd

end Benchmarks.ActAmm4
