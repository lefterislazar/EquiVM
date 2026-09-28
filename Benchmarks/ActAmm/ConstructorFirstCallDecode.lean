import Benchmarks.ActAmm.ConstructorFirstCall
import Benchmarks.ActAmm.MintTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorFirstCallSucceeded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {mem ret : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨422⟩ [⟨1⟩, ⟨260⟩, ⟨1889567281⟩,
        ammCtorInitialToken1Target I σ liquidity t0 t1,
        liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨441⟩ [liquidity, EVM.word t1, EVM.word t0]
      mem aw ret acc k' C' := by
  exact ⟨_, _, amm_ctor_run rd with [
    iszero, dup1, iszero, push2 ⟨436⟩,
    jumpiT (by decide) (by amm_ctor_jd), jumpdest,
    pop, pop, pop, pop]⟩

theorem ammCtorInitialToken1PostCallMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hretsz : ret.size < UInt256.size) :
    (ammCtorInitialToken1PostCallMem I t0 t1 liquidity ret).readWithPadding
      64 32 = UInt256.toByteArray ⟨224⟩ := by
  unfold ammCtorInitialToken1PostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat
  change (ret.write 0 (ammCtorInitialToken1ArgMem I t0 t1 liquidity)
    224 len).readWithPadding 64 32 = _
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero]
    exact ammCtorInitialToken1ArgMem_read64 I t0 t1 liquidity
  · rw [write_read_below_gen_extend ret
      (ammCtorInitialToken1ArgMem I t0 t1 liquidity) 224 len 64
      hzero ?_ ?_ (by decide)]
    · exact ammCtorInitialToken1ArgMem_read64 I t0 t1 liquidity
    · by_cases hlo : 32 ≤ ret.size
      · have hlen := umin_ofNat_right_toNat_of_ge
          (c := 32) (n := ret.size) (by decide) hlo hretsz
        change len ≤ ret.size
        rw [show len = 32 by simpa only [len] using hlen]
        exact hlo
      · have hlen := umin_ofNat_right_toNat_of_lt
          (c := 32) (n := ret.size) (by decide) (by omega) hretsz
        change len ≤ ret.size
        rw [show len = ret.size by simpa only [len] using hlen]
    · rw [ammCtorInitialToken1ArgMem_size]
      decide

theorem ammCtorInitialToken1PostCallMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hretsz : ret.size < UInt256.size) :
    (ammCtorInitialToken1PostCallMem I t0 t1 liquidity ret).size = 260 := by
  unfold ammCtorInitialToken1PostCallMem
  let len := (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat
  change (ret.write 0 (ammCtorInitialToken1ArgMem I t0 t1 liquidity)
    224 len).size = 260
  by_cases hzero : len = 0
  · rw [hzero, byteArray_write_len_zero, ammCtorInitialToken1ArgMem_size]
  · have h32 : (⟨32⟩ : UInt256) = UInt256.ofNat 32 := by decide
    have hlenEq : len = if 32 ≤ ret.size then 32 else ret.size := by
      by_cases hlo : 32 ≤ ret.size
      · simp only [if_pos hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_ge
            (c := 32) (n := ret.size) (by decide) hlo hretsz)
      · simp only [if_neg hlo]
        simpa only [len, h32] using
          (umin_ofNat_right_toNat_of_lt
            (c := 32) (n := ret.size) (by decide) (by omega) hretsz)
    have hlen : len ≤ 32 := by rw [hlenEq]; split_ifs <;> omega
    have hsrc : len ≤ ret.size := by rw [hlenEq]; split_ifs <;> omega
    rw [write_eq_gen ret (ammCtorInitialToken1ArgMem I t0 t1 liquidity)
      224 len hzero hsrc (by rw [ammCtorInitialToken1ArgMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, ammCtorInitialToken1ArgMem_size]
    omega

theorem ammCtorFirstCallFreePtr
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hretsz : ret.size < UInt256.size)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨441⟩ [liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1PostCallMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨444⟩ [⟨224⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1PostCallMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k' C' := by
  have rd443 := amm_ctor_run rd with [push1 ⟨64⟩]
  have rd444 := rd443.mload 0 ⟨224⟩ (UInt256.ofNat 9)
    (by amm_ctor_decode) mem_cost
    (mloadWordValue_of_readWithPadding
      (by rw [ammCtorInitialToken1PostCallMem_size I t0 t1 liquidity ret hretsz]; decide)
      (by native_decide)
      (ammCtorInitialToken1PostCallMem_read64 I t0 t1 liquidity ret hretsz))
    (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd444⟩

noncomputable def ammCtorInitialToken1DecodeMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) (ret : ByteArray) : ByteArray :=
  (UInt256.toByteArray (⟨224⟩ + ammMintReturndataRounded ret)).write 0
    (ammCtorInitialToken1PostCallMem I t0 t1 liquidity ret) 64 32

theorem ammCtorFirstCallReturnAlloc
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨444⟩ [⟨224⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1PostCallMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨459⟩ [⟨224⟩ + ammMintReturndataRounded ret,
        UInt256.ofNat ret.size, ⟨224⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k' C' := by
  have rd458 := amm_ctor_run rd with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩,
    dup3, add, and, dup3, add, dup1, push1 ⟨64⟩]
  have rd459 := RD.mstore 0
    (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
    (UInt256.ofNat 9) rd458
    (by amm_ctor_decode)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (UInt256.ofNat 9).toNat (⟨64⟩ : UInt256).toNat 32) =
          UInt256.ofNat 9 from by native_decide]
      omega)
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa only [ammMintReturndataRounded,
    ammCtorInitialToken1DecodeMem] using rd459⟩

theorem ammCtorFirstCallToDecoder
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨459⟩ [⟨224⟩ + ammMintReturndataRounded ret,
        UInt256.ofNat ret.size, ⟨224⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [⟨224⟩, ⟨224⟩ + UInt256.ofNat ret.size,
        ⟨472⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k' C' := by
  have rd1617 := amm_ctor_run rd with [
    pop, dup2, add, swap1, push2 ⟨472⟩, swap2, swap1,
    push2 ⟨1617⟩, jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd1617⟩

theorem ammCtorFirstCallDecodeShortReverts
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hshort : ret.size < 32)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [⟨224⟩, ⟨224⟩ + UInt256.ofNat ret.size,
        ⟨472⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k C) :
    RDrev (ammCtorCode t0 t1 liquidity) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have hcheck : UInt256.slt
      (UInt256.sub (⟨224⟩ + UInt256.ofNat ret.size) ⟨224⟩) ⟨32⟩ = ⟨1⟩ := by
    exact solcReturnStaticLenCheckShort (base := 224) (len := ret.size)
      (words := 1) (by simpa using hshort)
      (by norm_num [UInt256.size])
      (by have h := hshort; norm_num [UInt256.size] at *; omega)
      (by norm_num)
  have rd1626 := amm_ctor_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  rw [hcheck] at rd1626
  have rd1630 := amm_ctor_run rd1626 with [
    push2 ⟨1638⟩, jumpiNT (by decide)]
  have rd1256 := amm_ctor_run rd1630 with [
    push2 ⟨1637⟩, push2 ⟨1256⟩, jump (by amm_ctor_jd)]
  have rd1257 := amm_ctor_run rd1256 with [jumpdest]
  exact rd1257.revertStub (by amm_ctor_decode)
    (by amm_ctor_decode) (by amm_ctor_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammCtorInitialToken1DecodeMem_read224
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hlo : 32 ≤ ret.size)
    (hretsz : ret.size < UInt256.size) :
    (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret).readWithPadding
      224 32 = ret.extract 0 32 := by
  unfold ammCtorInitialToken1DecodeMem
  rw [write32_read_above _ _ 64 224
    (by rw [toByteArray_size])
    (by rw [ammCtorInitialToken1PostCallMem_size I t0 t1 liquidity ret hretsz]; decide)
    (by decide)
    (by rw [ammCtorInitialToken1PostCallMem_size I t0 t1 liquidity ret hretsz]; decide)]
  unfold ammCtorInitialToken1PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := ret.size)
      (by decide) hlo hretsz
  rw [hlen, write32_read_back ret
    (ammCtorInitialToken1ArgMem I t0 t1 liquidity) 224 hlo
    (by rw [ammCtorInitialToken1ArgMem_size]; decide)]

theorem ammCtorFirstCallDecodeToWordLoad
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1617⟩ [⟨224⟩, ⟨224⟩ + UInt256.ofNat ret.size,
        ⟨472⟩, liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1381⟩ [⟨224⟩, ⟨224⟩ + UInt256.ofNat ret.size,
        ⟨1651⟩, ⟨0⟩, ⟨0⟩, ⟨224⟩,
        ⟨224⟩ + UInt256.ofNat ret.size, ⟨472⟩,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k' C' := by
  have hcheck : UInt256.slt
      (UInt256.sub (⟨224⟩ + UInt256.ofNat ret.size) ⟨224⟩) ⟨32⟩ = ⟨0⟩ := by
    exact solcReturnStaticLenCheckOk (base := 224) (len := ret.size)
      (words := 1) (by simpa using hlo) (by omega)
      (by norm_num [UInt256.size])
      (by have h := hbound; norm_num [UInt256.size] at *; omega)
  have rd1638 := amm_ctor_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨1638⟩, jumpiT (by rw [hcheck]; decide) (by amm_ctor_jd)]
  have rd1381 := amm_ctor_run rd1638 with [
    jumpdest, push0, push2 ⟨1651⟩, dup5, dup3, dup6, add,
    push2 ⟨1381⟩, jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa using rd1381⟩

theorem ammCtorInitialToken1DecodeMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hretsz : ret.size < UInt256.size) :
    (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret).size = 260 := by
  unfold ammCtorInitialToken1DecodeMem
  exact toByteArray_write32_size_of_le _ _ 64 260 260
    (ammCtorInitialToken1PostCallMem_size I t0 t1 liquidity ret hretsz)
    (by rw [ammCtorInitialToken1PostCallMem_size I t0 t1 liquidity ret hretsz]; decide)
    (by decide)

theorem ammCtorFirstCallDecodeWord
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity : UInt256}
    {ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ ret.size) (hretsz : ret.size < UInt256.size)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨1381⟩ [⟨224⟩, ⟨224⟩ + UInt256.ofNat ret.size,
        ⟨1651⟩, ⟨0⟩, ⟨0⟩, ⟨224⟩,
        ⟨224⟩ + UInt256.ofNat ret.size, ⟨472⟩,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      ⟨472⟩ [UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret acc k' C' := by
  let v := UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32))
  have hvalue :
      (if (⟨224⟩ : UInt256).toNat ≥
          (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret).size ∨
          (⟨224⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret).readWithPadding
           (⟨224⟩ : UInt256).toNat 32))) = v := by
    rw [mloadValue_eq_readWithPadding_of_lt_size
      (ammCtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ⟨224⟩ 260
      (ammCtorInitialToken1DecodeMem_size I t0 t1 liquidity ret hretsz)
      (by decide) (by native_decide)]
    rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide,
      ammCtorInitialToken1DecodeMem_read224 I t0 t1 liquidity ret hlo hretsz]
  have rd1384 := amm_ctor_run rd with [jumpdest, push0, dup2]
  have rd1385 := RD.mload 0 v (UInt256.ofNat 9) rd1384
    (by amm_ctor_decode) mem_cost hvalue
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1359 := amm_ctor_run rd1385 with [
    swap1, pop, push2 ⟨1395⟩, dup2, push2 ⟨1359⟩,
    jump (by amm_ctor_jd)]
  have rd1350 := amm_ctor_run rd1359 with [
    jumpdest, push2 ⟨1368⟩, dup2, push2 ⟨1350⟩,
    jump (by amm_ctor_jd)]
  have rd1368 := amm_ctor_run rd1350 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop,
    jump (by amm_ctor_jd)]
  have rd1378 := amm_ctor_run rd1368 with [
    jumpdest, dup2, eq, push2 ⟨1378⟩,
    jumpiT (by rw [uInt256_eq_self]; decide) (by amm_ctor_jd)]
  have rd1395 := amm_ctor_run rd1378 with [
    jumpdest, pop, jump (by amm_ctor_jd)]
  have rd1651 := amm_ctor_run rd1395 with [
    jumpdest, swap3, swap2, pop, pop, jump (by amm_ctor_jd)]
  have rd472 := amm_ctor_run rd1651 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by amm_ctor_jd)]
  exact ⟨_, _, by simpa only [v] using rd472⟩

end Benchmarks.ActAmm
