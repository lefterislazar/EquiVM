import Benchmarks.ActAmm4.ConstructorThirdCallTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorThirdCallSelectorMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).write 0
    (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2)
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 32

abbrev amm4CtorThirdCallSelectorWords (ret1 ret2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4CtorSecondCallArgWords ret1).toNat
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 32)

theorem amm4CtorThirdCallSelectorStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨996⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorSecondCallArgWords ret1) ret2 (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1008⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorThirdCallSelectorWords ret1 ret2) ret2 (cA, σ) k' C' := by
  have rd1007 := amm4_ctor_run rd with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselector : UInt256.land ⟨4294967295⟩ ⟨1889567281⟩ =
      ⟨1889567281⟩ := by native_decide
  rw [hselector] at rd1007
  have rd1008 := rd1007.mstore
    (Cₘ (amm4CtorThirdCallSelectorWords ret1 ret2) -
      Cₘ (amm4CtorSecondCallArgWords ret1))
    (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
    (amm4CtorThirdCallSelectorWords ret1 ret2)
    (by amm4_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        amm4CtorThirdCallSelectorWords])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4CtorThirdCallSelectorMem,
    amm4CtorThirdCallSelectorWords] using rd1008⟩

noncomputable def amm4CtorThirdCallArgMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val))).write 0
    (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32

abbrev amm4CtorThirdCallArgWords (ret1 ret2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4CtorThirdCallSelectorWords ret1 ret2).toNat
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32)

theorem amm4CtorThirdCallEncoded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1008⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorThirdCallSelectorWords ret1 ret2) ret2 (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1020⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k' C' := by
  have rd1592 := amm4_ctor_run rd with [
    push1 ⟨4⟩, add, push2 ⟨1020⟩, swap2, swap1,
    push2 ⟨1592⟩, jump (by amm4_ctor_jd)]
  rw [u256_add_comm ⟨4⟩ (amm4CtorAfterSecondReturnFreePtr ret1 ret2)] at rd1592
  obtain ⟨_, _, rd1020⟩ := RD.amm4CtorEncodeAddressArg rd1592
    (by amm4_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have hend : (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩) + ⟨32⟩ =
      amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [hend] at rd1020
  exact ⟨_, _, by simpa only [amm4CtorThirdCallArgMem,
    amm4CtorThirdCallArgWords] using rd1020⟩

theorem amm4CtorAfterSecondReturnFreePtr_add4_toNat
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat =
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt]
  have hptr := (amm4CtorAfterSecondReturnFreePtr_bounds ret1 ret2
    hbound1 hbound2).2
  norm_num [UInt256.size] at *
  omega

theorem amm4CtorThirdCallSelectorMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) :
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 32 ≤
      (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).size := by
  unfold amm4CtorThirdCallSelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4CtorThirdCallSelectorMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) :
    (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 4 =
        balanceOfSelector := by
  unfold amm4CtorThirdCallSelectorMem
  have h := toByteArray_write_read_window_no_gap
    (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)
    (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2)
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword :
      (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).extract 0 4 =
        balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4CtorThirdCallArgMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 36 ≤
      (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by
  unfold amm4CtorThirdCallArgMem
  rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4CtorThirdCallArgMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 4 =
        balanceOfSelector := by
  unfold amm4CtorThirdCallArgMem
  have hdest : (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat ≤
      (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).size := by
    rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
    have hsize := amm4CtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2
    omega
  have hbelow : (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 4 ≤
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat := by
    rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
  have hin : (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 4 ≤
      (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).size := by
    have hsize := amm4CtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2
    omega
  have hpres := write32_read_below_len
    (src := UInt256.toByteArray
      (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val)))
    (base := amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
    (dest := (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat)
    (read := (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat)
    (len := 4)
    (by rw [toByteArray_size]) hdest hbelow hin
    (by norm_num) (by norm_num)
  rw [hpres]
  exact amm4CtorThirdCallSelectorMem_read4 I t0 t1 liquidity ret1 ret2

theorem amm4CtorThirdCallArgMem_read32 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32 =
        UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold amm4CtorThirdCallArgMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
    exact le_trans (by omega)
      (amm4CtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2))]
  have hcanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus :=
    amm4CtorAddressWord_canonical I.codeOwner
  rw [solcAddrMask_clean_left hcanon]
  rw [toByteArray_extract_all]

theorem amm4CtorThirdCallArgMem_read36 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 36 =
        balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  rw [byteArray_readWithPadding_split _
    (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (amm4CtorThirdCallArgMem_size I t0 t1 liquidity ret1 ret2 hbound1 hbound2)]
  rw [amm4CtorThirdCallArgMem_read4 I t0 t1 liquidity ret1 ret2 hbound1 hbound2,
    ← amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2,
    amm4CtorThirdCallArgMem_read32 I t0 t1 liquidity ret1 ret2 hbound1 hbound2]

theorem amm4CtorThirdCallArgMem_encode (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
        (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 36) := by
  rw [amm4CtorThirdCallArgMem_read36 I t0 t1 liquidity ret1 ret2 hbound1 hbound2]
  have hword : EVM.word (↑I.codeOwner.val) = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem amm4CtorThirdCallSelectorMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray
        (amm4CtorAfterSecondReturnFreePtr ret1 ret2) := by
  unfold amm4CtorThirdCallSelectorMem
  have hbase : 96 ≤ (amm4CtorPostGuardMem I t0 t1 liquidity ret1 ret2).size := by
    rw [amm4CtorPostGuardMem_baseSize I t0 t1 liquidity ret1 ret2
      hbound1 hbound2]
    rw [amm4CtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 (by
        have hb := hbound2
        norm_num [UInt256.size] at *
        omega)]
    have hs := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (amm4CtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega
  rw [toByteArray_write_read_below_no_gap _ _ _ 64 hbase (by
    have hp := (amm4CtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    omega)]
  exact amm4CtorPostGuardMem_read64 I t0 t1 liquidity ret1 ret2
    hbound1 hbound2

theorem amm4CtorThirdCallArgMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray
        (amm4CtorAfterSecondReturnFreePtr ret1 ret2) := by
  unfold amm4CtorThirdCallArgMem
  rw [write32_read_below _ _ _ 64
    (by rw [toByteArray_size])
    (by
      rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
      have hsize := amm4CtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2
      omega)
    (by
      rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
      have hp := (amm4CtorAfterSecondReturnFreePtr_bounds ret1 ret2
        hbound1 hbound2).1
      omega)]
  exact amm4CtorThirdCallSelectorMem_read64 I t0 t1 liquidity ret1 ret2
    hbound1 hbound2

theorem amm4CtorThirdCallSelectorWords_toNat (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallSelectorWords ret1 ret2).toNat =
      8 + (ret1.size + 31) / 32 + (ret2.size + 31) / 32 := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  have hn2 : 1 ≤ n2 := by dsimp [n2]; omega
  have hptr : (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat =
      224 + 32 * n1 + 32 * n2 := by
    simpa only [n1, n2] using
      amm4CtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2
  have haw : (amm4CtorSecondCallArgWords ret1).toNat = 9 + n1 := by
    simpa only [n1] using
      amm4CtorSecondCallArgWords_toNat ret1 hlo1 hbound1
  have hM : MachineState.M (amm4CtorSecondCallArgWords ret1).toNat
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat 32 = 8 + n1 + n2 := by
    change max (amm4CtorSecondCallArgWords ret1).toNat
      (((amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  unfold amm4CtorThirdCallSelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : 2 ^ 138 + 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem amm4CtorThirdCallArgWords_toNat (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    (amm4CtorThirdCallArgWords ret1 ret2).toNat =
      9 + (ret1.size + 31) / 32 + (ret2.size + 31) / 32 := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  have hptr : (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat =
      228 + 32 * n1 + 32 * n2 := by
    rw [amm4CtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2,
      amm4CtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2]
    omega
  have haw : (amm4CtorThirdCallSelectorWords ret1 ret2).toNat =
      8 + n1 + n2 := by
    simpa only [n1, n2] using
      amm4CtorThirdCallSelectorWords_toNat ret1 ret2
        hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M (amm4CtorThirdCallSelectorWords ret1 ret2).toNat
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32 =
        9 + n1 + n2 := by
    change max (amm4CtorThirdCallSelectorWords ret1 ret2).toNat
      (((amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  unfold amm4CtorThirdCallArgWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : 2 ^ 138 + 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem amm4CtorThirdCallArgWords_mload64_same (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4CtorThirdCallArgWords ret1 ret2).toNat
      64 32) = amm4CtorThirdCallArgWords ret1 ret2 := by
  have haw := amm4CtorThirdCallArgWords_toNat ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M (amm4CtorThirdCallArgWords ret1 ret2).toNat 64 32 =
      (amm4CtorThirdCallArgWords ret1 ret2).toNat := by
    change max (amm4CtorThirdCallArgWords ret1 ret2).toNat
      ((64 + 32 + 31) / 32) = _
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4CtorThirdCallArgWords_mload64_haw (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥ amm4CtorThirdCallArgWords ret1 ret2 * ⟨32⟩ := by
  have haw := amm4CtorThirdCallArgWords_toNat ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hmul : (amm4CtorThirdCallArgWords ret1 ret2).toNat * 32 <
      UInt256.size := by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : (2 ^ 138 + 2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4CtorThirdCallArgWords ret1 ret2 * ⟨32⟩).toNat ≤ 64 := by
    simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw] at hle
  omega

theorem amm4CtorThirdCallStaticcallFrame
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1020⟩ [amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k C) :
    ∃ gasWord k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1032⟩ [gasWord, amm4CtorInitialToken0Target I σ,
        amm4CtorAfterSecondReturnFreePtr ret1 ret2, ⟨36⟩,
        amm4CtorAfterSecondReturnFreePtr ret1 ret2, ⟨32⟩,
        amm4CtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (amm4CtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k' C' := by
  let fp := amm4CtorAfterSecondReturnFreePtr ret1 ret2
  let aw := amm4CtorThirdCallArgWords ret1 ret2
  have hmem : (⟨64⟩ : UInt256).toNat <
      (amm4CtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by
    have hsize := amm4CtorThirdCallArgMem_size I t0 t1 liquidity ret1 ret2
      hbound1 hbound2
    have hptr := (amm4CtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    omega
  have haw := amm4CtorThirdCallArgWords_mload64_haw ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hsame := amm4CtorThirdCallArgWords_mload64_same ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have rd1025 := amm4_ctor_run rd with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1026 := RD.mload 0 fp aw rd1025
    (by amm4_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4CtorThirdCallArgMem_read64 I t0 t1 liquidity ret1 ret2
          hbound1 hbound2)))
    (by simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using hsame)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1031 := amm4_ctor_run rd1026 with [dup1, dup4, sub, dup2, dup7]
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  rw [hsub] at rd1031
  obtain ⟨gasWord, rd1032⟩ := rd1031.gas (by amm4_ctor_decode) (by simp)
  exact ⟨gasWord, _, _, by simpa only [fp, aw] using rd1032⟩

theorem amm4CtorThirdCallArgWords_call_nat_same (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (n : Nat) (hn : n = 32 ∨ n = 36) :
    MachineState.M (amm4CtorThirdCallArgWords ret1 ret2).toNat
      (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat n =
        (amm4CtorThirdCallArgWords ret1 ret2).toNat := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  have hptr : (amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat =
      224 + 32 * n1 + 32 * n2 := by
    simpa only [n1, n2] using
      amm4CtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2
  have haw : (amm4CtorThirdCallArgWords ret1 ret2).toNat =
      9 + n1 + n2 := by
    simpa only [n1, n2] using
      amm4CtorThirdCallArgWords_toNat ret1 ret2
        hlo1 hbound1 hlo2 hbound2
  rcases hn with rfl | rfl
  · change max (amm4CtorThirdCallArgWords ret1 ret2).toNat
      (((amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  · change max (amm4CtorThirdCallArgWords ret1 ret2).toNat
      (((amm4CtorAfterSecondReturnFreePtr ret1 ret2).toNat + 36 + 31) / 32) = _
    rw [hptr, haw]
    omega

end Benchmarks.ActAmm4
