import Benchmarks.ActAmm4.ConstructorFourthCallTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorFourthCallSelectorMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).write 0
    (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 32

abbrev amm4CtorFourthCallSelectorWords (ret1 ret2 ret3 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4CtorThirdCallArgWords ret1 ret2).toNat
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 32)

theorem amm4CtorFourthCallSelectorStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1155⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorThirdCallArgWords ret1 ret2) ret3 (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1167⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorFourthCallSelectorWords ret1 ret2 ret3) ret3 (cA, σ) k' C' := by
  have rd1166 := amm4_ctor_run rd with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselector : UInt256.land ⟨4294967295⟩ ⟨1889567281⟩ =
      ⟨1889567281⟩ := by native_decide
  rw [hselector] at rd1166
  have rd1167 := rd1166.mstore
    (Cₘ (amm4CtorFourthCallSelectorWords ret1 ret2 ret3) -
      Cₘ (amm4CtorThirdCallArgWords ret1 ret2))
    (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorFourthCallSelectorWords ret1 ret2 ret3)
    (by amm4_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        amm4CtorFourthCallSelectorWords])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4CtorFourthCallSelectorMem,
    amm4CtorFourthCallSelectorWords] using rd1167⟩

noncomputable def amm4CtorFourthCallArgMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val))).write 0
    (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat 32

abbrev amm4CtorFourthCallArgWords (ret1 ret2 ret3 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (amm4CtorFourthCallSelectorWords ret1 ret2 ret3).toNat
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat 32)

theorem amm4CtorFourthCallEncoded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1167⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorFinalToken1Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorFourthCallSelectorWords ret1 ret2 ret3) ret3 (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1179⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorFinalToken1Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret3 (cA, σ) k' C' := by
  have rd1592 := amm4_ctor_run rd with [
    push1 ⟨4⟩, add, push2 ⟨1179⟩, swap2, swap1,
    push2 ⟨1592⟩, jump (by amm4_ctor_jd)]
  rw [u256_add_comm ⟨4⟩
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3)] at rd1592
  obtain ⟨_, _, rd1179⟩ := RD.amm4CtorEncodeAddressArg rd1592
    (by amm4_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have hend :
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩) + ⟨32⟩ =
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨36⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [hend] at rd1179
  exact ⟨_, _, by simpa only [amm4CtorFourthCallArgMem,
    amm4CtorFourthCallArgWords] using rd1179⟩

theorem amm4CtorAfterThirdReturnFreePtr_toNat
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat =
      224 + 32 * ((ret1.size + 31) / 32) +
        32 * ((ret2.size + 31) / 32) +
        32 * ((ret3.size + 31) / 32) := by
  unfold amm4CtorAfterThirdReturnFreePtr
  rw [uadd_toNat,
    amm4CtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2,
    amm4MintReturndataRounded_toNat ret3 hbound3]
  rw [Nat.mod_eq_of_lt]
  have hdiv1 := Nat.div_le_self (ret1.size + 31) 32
  have hdiv2 := Nat.div_le_self (ret2.size + 31) 32
  have hdiv3 := Nat.div_le_self (ret3.size + 31) 32
  norm_num [UInt256.size] at *
  omega

theorem amm4CtorAfterThirdReturnFreePtr_bounds
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    224 ≤ (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat ∧
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat < 2 ^ 141 := by
  rw [amm4CtorAfterThirdReturnFreePtr_toNat ret1 ret2 ret3
    hbound1 hbound2 hbound3]
  have hdiv1 := Nat.div_le_self (ret1.size + 31) 32
  have hdiv2 := Nat.div_le_self (ret2.size + 31) 32
  have hdiv3 := Nat.div_le_self (ret3.size + 31) 32
  omega

theorem amm4CtorAfterThirdReturnFreePtr_add4_toNat
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat =
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt]
  have hptr := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
    hbound1 hbound2 hbound3).2
  norm_num [UInt256.size] at *
  omega

theorem amm4CtorFourthCallSelectorMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray) :
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 32 ≤
      (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3).size := by
  unfold amm4CtorFourthCallSelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4CtorFourthCallSelectorMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray) :
    (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 4 =
        balanceOfSelector := by
  unfold amm4CtorFourthCallSelectorMem
  have h := toByteArray_write_read_window_no_gap
    (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)
    (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3)
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword :
      (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).extract 0 4 =
        balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4CtorFourthCallArgMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 36 ≤
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size := by
  unfold amm4CtorFourthCallArgMem
  rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
    hbound1 hbound2 hbound3]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4CtorFourthCallArgMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 4 =
        balanceOfSelector := by
  unfold amm4CtorFourthCallArgMem
  have hdest :
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat ≤
        (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3).size := by
    rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
      hbound1 hbound2 hbound3]
    have hsize := amm4CtorFourthCallSelectorMem_size I t0 t1 liquidity
      ret1 ret2 ret3
    omega
  have hbelow : (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 4 ≤
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat := by
    rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
      hbound1 hbound2 hbound3]
  have hin : (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 4 ≤
      (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3).size := by
    have hsize := amm4CtorFourthCallSelectorMem_size I t0 t1 liquidity
      ret1 ret2 ret3
    omega
  have hpres := write32_read_below_len
    (src := UInt256.toByteArray
      (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val)))
    (base := amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3)
    (dest := (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat)
    (read := (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat)
    (len := 4)
    (by rw [toByteArray_size]) hdest hbelow hin
    (by norm_num) (by norm_num)
  rw [hpres]
  exact amm4CtorFourthCallSelectorMem_read4 I t0 t1 liquidity ret1 ret2 ret3

theorem amm4CtorFourthCallArgMem_read32 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat 32 =
        UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold amm4CtorFourthCallArgMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
      hbound1 hbound2 hbound3]
    exact le_trans (by omega)
      (amm4CtorFourthCallSelectorMem_size I t0 t1 liquidity ret1 ret2 ret3))]
  have hcanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus :=
    amm4CtorAddressWord_canonical I.codeOwner
  rw [solcAddrMask_clean_left hcanon]
  rw [toByteArray_extract_all]

theorem amm4CtorFourthCallArgMem_read36 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 36 =
        balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  rw [byteArray_readWithPadding_split _
    (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (amm4CtorFourthCallArgMem_size I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hbound3)]
  rw [amm4CtorFourthCallArgMem_read4 I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hbound3,
    ← amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
      hbound1 hbound2 hbound3,
    amm4CtorFourthCallArgMem_read32 I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 hbound3]

theorem amm4CtorFourthCallArgMem_encode (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 36) := by
  rw [amm4CtorFourthCallArgMem_read36 I t0 t1 liquidity ret1 ret2 ret3
    hbound1 hbound2 hbound3]
  have hword : EVM.word (↑I.codeOwner.val) = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem amm4CtorFourthCallSelectorMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallSelectorMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      64 32 = UInt256.toByteArray
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3) := by
  unfold amm4CtorFourthCallSelectorMem
  have hbase : 96 ≤
      (amm4CtorThirdCallDecodeMem I t0 t1 liquidity ret1 ret2 ret3).size := by
    rw [amm4CtorThirdCallDecodeMem_size I t0 t1 liquidity ret1 ret2 ret3
      hbound1 hbound2 (by
        have hb := hbound3
        norm_num [UInt256.size] at *
        omega)]
    have hs := amm4CtorThirdCallArgMem_size I t0 t1 liquidity
      ret1 ret2 hbound1 hbound2
    have hp := (amm4CtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    omega
  rw [toByteArray_write_read_below_no_gap _ _ _ 64 hbase (by
    have hp := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
      hbound1 hbound2 hbound3).1
    omega)]
  exact amm4CtorThirdCallDecodeMem_read64 I t0 t1 liquidity ret1 ret2 ret3
    hbound1 hbound2 (by
      have hb := hbound3
      norm_num [UInt256.size] at *
      omega)

theorem amm4CtorFourthCallArgMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 ret3 : ByteArray)
    (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138)
    (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).readWithPadding
      64 32 = UInt256.toByteArray
        (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3) := by
  unfold amm4CtorFourthCallArgMem
  rw [write32_read_below _ _ _ 64
    (by rw [toByteArray_size])
    (by
      rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
        hbound1 hbound2 hbound3]
      have hsize := amm4CtorFourthCallSelectorMem_size I t0 t1 liquidity
        ret1 ret2 ret3
      omega)
    (by
      rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
        hbound1 hbound2 hbound3]
      have hp := (amm4CtorAfterThirdReturnFreePtr_bounds ret1 ret2 ret3
        hbound1 hbound2 hbound3).1
      omega)]
  exact amm4CtorFourthCallSelectorMem_read64 I t0 t1 liquidity ret1 ret2 ret3
    hbound1 hbound2 hbound3

theorem amm4CtorFourthCallSelectorWords_toNat (ret1 ret2 ret3 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallSelectorWords ret1 ret2 ret3).toNat =
      8 + (ret1.size + 31) / 32 + (ret2.size + 31) / 32 +
        (ret3.size + 31) / 32 := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  let n3 := (ret3.size + 31) / 32
  have hn3 : 1 ≤ n3 := by dsimp [n3]; omega
  have hptr : (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat =
      224 + 32 * n1 + 32 * n2 + 32 * n3 := by
    simpa only [n1, n2, n3] using
      amm4CtorAfterThirdReturnFreePtr_toNat ret1 ret2 ret3
        hbound1 hbound2 hbound3
  have haw : (amm4CtorThirdCallArgWords ret1 ret2).toNat =
      9 + n1 + n2 := by
    simpa only [n1, n2] using
      amm4CtorThirdCallArgWords_toNat ret1 ret2
        hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M (amm4CtorThirdCallArgWords ret1 ret2).toNat
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat 32 =
        8 + n1 + n2 + n3 := by
    change max (amm4CtorThirdCallArgWords ret1 ret2).toNat
      (((amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  unfold amm4CtorFourthCallSelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hle3 := Nat.div_le_self (ret3.size + 31) 32
    have hcap : 3 * 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem amm4CtorFourthCallArgWords_toNat (ret1 ret2 ret3 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138) :
    (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat =
      9 + (ret1.size + 31) / 32 + (ret2.size + 31) / 32 +
        (ret3.size + 31) / 32 := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  let n3 := (ret3.size + 31) / 32
  have hptr : (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat =
      228 + 32 * n1 + 32 * n2 + 32 * n3 := by
    rw [amm4CtorAfterThirdReturnFreePtr_add4_toNat ret1 ret2 ret3
      hbound1 hbound2 hbound3,
      amm4CtorAfterThirdReturnFreePtr_toNat ret1 ret2 ret3
        hbound1 hbound2 hbound3]
    omega
  have haw : (amm4CtorFourthCallSelectorWords ret1 ret2 ret3).toNat =
      8 + n1 + n2 + n3 := by
    simpa only [n1, n2, n3] using
      amm4CtorFourthCallSelectorWords_toNat ret1 ret2 ret3
        hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  have hM : MachineState.M
      (amm4CtorFourthCallSelectorWords ret1 ret2 ret3).toNat
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat 32 =
        9 + n1 + n2 + n3 := by
    change max (amm4CtorFourthCallSelectorWords ret1 ret2 ret3).toNat
      (((amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨4⟩).toNat +
        32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  unfold amm4CtorFourthCallArgWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hle3 := Nat.div_le_self (ret3.size + 31) 32
    have hcap : 3 * 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem amm4CtorFourthCallArgWords_mload64_same (ret1 ret2 ret3 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat 64 32) =
        amm4CtorFourthCallArgWords ret1 ret2 ret3 := by
  have haw := amm4CtorFourthCallArgWords_toNat ret1 ret2 ret3
    hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  have hM : MachineState.M
      (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat 64 32 =
      (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat := by
    change max (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat
      ((64 + 32 + 31) / 32) = _
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4CtorFourthCallArgWords_mload64_haw (ret1 ret2 ret3 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥
      amm4CtorFourthCallArgWords ret1 ret2 ret3 * ⟨32⟩ := by
  have haw := amm4CtorFourthCallArgWords_toNat ret1 ret2 ret3
    hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
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
      64 := by
    simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw] at hle
  omega

theorem amm4CtorFourthCallStaticcallFrame
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 ret3 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1179⟩ [amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorFinalToken1Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret3 (cA, σ) k C) :
    ∃ gasWord k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1191⟩ [gasWord, amm4CtorFinalToken1Target I σ,
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3, ⟨36⟩,
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3, ⟨32⟩,
        amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3 + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorFinalToken1Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3)
      (amm4CtorFourthCallArgWords ret1 ret2 ret3) ret3 (cA, σ) k' C' := by
  let fp := amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3
  let aw := amm4CtorFourthCallArgWords ret1 ret2 ret3
  have hmem : (⟨64⟩ : UInt256).toNat <
      (amm4CtorFourthCallArgMem I t0 t1 liquidity ret1 ret2 ret3).size := by
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
  have rd1184 := amm4_ctor_run rd with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1185 := RD.mload 0 fp aw rd1184
    (by amm4_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4CtorFourthCallArgMem_read64 I t0 t1 liquidity
          ret1 ret2 ret3 hbound1 hbound2 hbound3)))
    (by simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using hsame)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1190 := amm4_ctor_run rd1185 with [dup1, dup4, sub, dup2, dup7]
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  rw [hsub] at rd1190
  obtain ⟨gasWord, rd1191⟩ := rd1190.gas (by amm4_ctor_decode) (by simp)
  exact ⟨gasWord, _, _, by simpa only [fp, aw] using rd1191⟩

theorem amm4CtorFourthCallArgWords_call_nat_same
    (ret1 ret2 ret3 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (hlo3 : 32 ≤ ret3.size) (hbound3 : ret3.size < 2 ^ 138)
    (n : Nat) (hn : n = 32 ∨ n = 36) :
    MachineState.M (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat
      (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat n =
        (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  let n3 := (ret3.size + 31) / 32
  have hptr : (amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat =
      224 + 32 * n1 + 32 * n2 + 32 * n3 := by
    simpa only [n1, n2, n3] using
      amm4CtorAfterThirdReturnFreePtr_toNat ret1 ret2 ret3
        hbound1 hbound2 hbound3
  have haw : (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat =
      9 + n1 + n2 + n3 := by
    simpa only [n1, n2, n3] using
      amm4CtorFourthCallArgWords_toNat ret1 ret2 ret3
        hlo1 hbound1 hlo2 hbound2 hlo3 hbound3
  rcases hn with rfl | rfl
  · change max (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat
      (((amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  · change max (amm4CtorFourthCallArgWords ret1 ret2 ret3).toNat
      (((amm4CtorAfterThirdReturnFreePtr ret1 ret2 ret3).toNat + 36 + 31) / 32) = _
    rw [hptr, haw]
    omega

end Benchmarks.ActAmm4
