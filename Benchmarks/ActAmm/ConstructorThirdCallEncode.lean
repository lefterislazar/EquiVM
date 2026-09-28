import Benchmarks.ActAmm.ConstructorThirdCallTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def ammCtorThirdCallSelectorMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).write 0
    (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 32

abbrev ammCtorThirdCallSelectorWords (ret1 ret2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammCtorSecondCallArgWords ret1).toNat
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 32)

theorem ammCtorThirdCallSelectorStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨996⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2)
      (ammCtorSecondCallArgWords ret1) ret2 (cA, σ) k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1008⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
      (ammCtorThirdCallSelectorWords ret1 ret2) ret2 (cA, σ) k' C' := by
  have rd1007 := amm_ctor_run rd with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselector : UInt256.land ⟨4294967295⟩ ⟨1889567281⟩ =
      ⟨1889567281⟩ := by native_decide
  rw [hselector] at rd1007
  have rd1008 := rd1007.mstore
    (Cₘ (ammCtorThirdCallSelectorWords ret1 ret2) -
      Cₘ (ammCtorSecondCallArgWords ret1))
    (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
    (ammCtorThirdCallSelectorWords ret1 ret2)
    (by amm_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        ammCtorThirdCallSelectorWords])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [ammCtorThirdCallSelectorMem,
    ammCtorThirdCallSelectorWords] using rd1008⟩

noncomputable def ammCtorThirdCallArgMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val))).write 0
    (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32

abbrev ammCtorThirdCallArgWords (ret1 ret2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammCtorThirdCallSelectorWords ret1 ret2).toNat
    (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32)

theorem ammCtorThirdCallEncoded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1008⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        ammCtorInitialToken0Target I σ, liquidity,
        EVM.word t1, EVM.word t0]
      (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
      (ammCtorThirdCallSelectorWords ret1 ret2) ret2 (cA, σ) k C) :
    ∃ k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1020⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
        ⟨1889567281⟩, ammCtorInitialToken0Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (ammCtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k' C' := by
  have rd1592 := amm_ctor_run rd with [
    push1 ⟨4⟩, add, push2 ⟨1020⟩, swap2, swap1,
    push2 ⟨1592⟩, jump (by amm_ctor_jd)]
  rw [u256_add_comm ⟨4⟩ (ammCtorAfterSecondReturnFreePtr ret1 ret2)] at rd1592
  obtain ⟨_, _, rd1020⟩ := RD.ammCtorEncodeAddressArg rd1592
    (by amm_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have hend : (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩) + ⟨32⟩ =
      ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [hend] at rd1020
  exact ⟨_, _, by simpa only [ammCtorThirdCallArgMem,
    ammCtorThirdCallArgWords] using rd1020⟩

theorem ammCtorAfterSecondReturnFreePtr_add4_toNat
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat =
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt]
  have hptr := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
    hbound1 hbound2).2
  norm_num [UInt256.size] at *
  omega

theorem ammCtorThirdCallSelectorMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) :
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 32 ≤
      (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).size := by
  unfold ammCtorThirdCallSelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammCtorThirdCallSelectorMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) :
    (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 4 =
        balanceOfSelector := by
  unfold ammCtorThirdCallSelectorMem
  have h := toByteArray_write_read_window_no_gap
    (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)
    (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword :
      (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).extract 0 4 =
        balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammCtorThirdCallArgMem_size (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 36 ≤
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by
  unfold ammCtorThirdCallArgMem
  rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammCtorThirdCallArgMem_read4 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 4 =
        balanceOfSelector := by
  unfold ammCtorThirdCallArgMem
  have hdest : (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat ≤
      (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).size := by
    rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
    have hsize := ammCtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2
    omega
  have hbelow : (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 4 ≤
      (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat := by
    rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
  have hin : (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 4 ≤
      (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).size := by
    have hsize := ammCtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2
    omega
  have hpres := write32_read_below_len
    (src := UInt256.toByteArray
      (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val)))
    (base := ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2)
    (dest := (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat)
    (read := (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat)
    (len := 4)
    (by rw [toByteArray_size]) hdest hbelow hin
    (by norm_num) (by norm_num)
  rw [hpres]
  exact ammCtorThirdCallSelectorMem_read4 I t0 t1 liquidity ret1 ret2

theorem ammCtorThirdCallArgMem_read32 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32 =
        UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold ammCtorThirdCallArgMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
    exact le_trans (by omega)
      (ammCtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2))]
  have hcanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus :=
    ammCtorAddressWord_canonical I.codeOwner
  rw [solcAddrMask_clean_left hcanon]
  rw [toByteArray_extract_all]

theorem ammCtorThirdCallArgMem_read36 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 36 =
        balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  rw [byteArray_readWithPadding_split _
    (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ammCtorThirdCallArgMem_size I t0 t1 liquidity ret1 ret2 hbound1 hbound2)]
  rw [ammCtorThirdCallArgMem_read4 I t0 t1 liquidity ret1 ret2 hbound1 hbound2,
    ← ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2,
    ammCtorThirdCallArgMem_read32 I t0 t1 liquidity ret1 ret2 hbound1 hbound2]

theorem ammCtorThirdCallArgMem_encode (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
        (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 36) := by
  rw [ammCtorThirdCallArgMem_read36 I t0 t1 liquidity ret1 ret2 hbound1 hbound2]
  have hword : EVM.word (↑I.codeOwner.val) = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem ammCtorThirdCallSelectorMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallSelectorMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray
        (ammCtorAfterSecondReturnFreePtr ret1 ret2) := by
  unfold ammCtorThirdCallSelectorMem
  have hbase : 96 ≤ (ammCtorPostGuardMem I t0 t1 liquidity ret1 ret2).size := by
    rw [ammCtorPostGuardMem_baseSize I t0 t1 liquidity ret1 ret2
      hbound1 hbound2]
    rw [ammCtorSecondCallDecodeMem_size I t0 t1 liquidity ret1 ret2
      hbound1 (by
        have hb := hbound2
        norm_num [UInt256.size] at *
        omega)]
    have hs := ammCtorSecondCallArgMem_size I t0 t1 liquidity ret1 hbound1
    have hp := (ammCtorSecondCallFreePtr_bounds ret1 hbound1).1
    omega
  rw [toByteArray_write_read_below_no_gap _ _ _ 64 hbase (by
    have hp := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
      hbound1 hbound2).1
    omega)]
  exact ammCtorPostGuardMem_read64 I t0 t1 liquidity ret1 ret2
    hbound1 hbound2

theorem ammCtorThirdCallArgMem_read64 (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret1 ret2 : ByteArray) (hbound1 : ret1.size < 2 ^ 138)
    (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).readWithPadding
      64 32 = UInt256.toByteArray
        (ammCtorAfterSecondReturnFreePtr ret1 ret2) := by
  unfold ammCtorThirdCallArgMem
  rw [write32_read_below _ _ _ 64
    (by rw [toByteArray_size])
    (by
      rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
      have hsize := ammCtorThirdCallSelectorMem_size I t0 t1 liquidity ret1 ret2
      omega)
    (by
      rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2]
      have hp := (ammCtorAfterSecondReturnFreePtr_bounds ret1 ret2
        hbound1 hbound2).1
      omega)]
  exact ammCtorThirdCallSelectorMem_read64 I t0 t1 liquidity ret1 ret2
    hbound1 hbound2

theorem ammCtorThirdCallSelectorWords_toNat (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallSelectorWords ret1 ret2).toNat =
      8 + (ret1.size + 31) / 32 + (ret2.size + 31) / 32 := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  have hn2 : 1 ≤ n2 := by dsimp [n2]; omega
  have hptr : (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat =
      224 + 32 * n1 + 32 * n2 := by
    simpa only [n1, n2] using
      ammCtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2
  have haw : (ammCtorSecondCallArgWords ret1).toNat = 9 + n1 := by
    simpa only [n1] using
      ammCtorSecondCallArgWords_toNat ret1 hlo1 hbound1
  have hM : MachineState.M (ammCtorSecondCallArgWords ret1).toNat
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat 32 = 8 + n1 + n2 := by
    change max (ammCtorSecondCallArgWords ret1).toNat
      (((ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  unfold ammCtorThirdCallSelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : 2 ^ 138 + 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem ammCtorThirdCallArgWords_toNat (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    (ammCtorThirdCallArgWords ret1 ret2).toNat =
      9 + (ret1.size + 31) / 32 + (ret2.size + 31) / 32 := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  have hptr : (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat =
      228 + 32 * n1 + 32 * n2 := by
    rw [ammCtorAfterSecondReturnFreePtr_add4_toNat ret1 ret2 hbound1 hbound2,
      ammCtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2]
    omega
  have haw : (ammCtorThirdCallSelectorWords ret1 ret2).toNat =
      8 + n1 + n2 := by
    simpa only [n1, n2] using
      ammCtorThirdCallSelectorWords_toNat ret1 ret2
        hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M (ammCtorThirdCallSelectorWords ret1 ret2).toNat
      (ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat 32 =
        9 + n1 + n2 := by
    change max (ammCtorThirdCallSelectorWords ret1 ret2).toNat
      (((ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨4⟩).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  unfold ammCtorThirdCallArgWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : 2 ^ 138 + 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem ammCtorThirdCallArgWords_mload64_same (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (ammCtorThirdCallArgWords ret1 ret2).toNat
      64 32) = ammCtorThirdCallArgWords ret1 ret2 := by
  have haw := ammCtorThirdCallArgWords_toNat ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M (ammCtorThirdCallArgWords ret1 ret2).toNat 64 32 =
      (ammCtorThirdCallArgWords ret1 ret2).toNat := by
    change max (ammCtorThirdCallArgWords ret1 ret2).toNat
      ((64 + 32 + 31) / 32) = _
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammCtorThirdCallArgWords_mload64_haw (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥ ammCtorThirdCallArgWords ret1 ret2 * ⟨32⟩ := by
  have haw := ammCtorThirdCallArgWords_toNat ret1 ret2
    hlo1 hbound1 hlo2 hbound2
  have hmul : (ammCtorThirdCallArgWords ret1 ret2).toNat * 32 <
      UInt256.size := by
    have hle1 := Nat.div_le_self (ret1.size + 31) 32
    have hle2 := Nat.div_le_self (ret2.size + 31) 32
    have hcap : (2 ^ 138 + 2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (ammCtorThirdCallArgWords ret1 ret2 * ⟨32⟩).toNat ≤ 64 := by
    simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw] at hle
  omega

theorem ammCtorThirdCallStaticcallFrame
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : Sat256} {t0 t1 : AccountAddress} {liquidity : UInt256}
    {ret1 ret2 : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {k C : Nat}
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (rd : RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1020⟩ [ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
        ⟨1889567281⟩, ammCtorInitialToken0Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (ammCtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k C) :
    ∃ gasWord k' C', RD (ammCtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨1032⟩ [gasWord, ammCtorInitialToken0Target I σ,
        ammCtorAfterSecondReturnFreePtr ret1 ret2, ⟨36⟩,
        ammCtorAfterSecondReturnFreePtr ret1 ret2, ⟨32⟩,
        ammCtorAfterSecondReturnFreePtr ret1 ret2 + ⟨36⟩,
        ⟨1889567281⟩, ammCtorInitialToken0Target I σ,
        liquidity, EVM.word t1, EVM.word t0]
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2)
      (ammCtorThirdCallArgWords ret1 ret2) ret2 (cA, σ) k' C' := by
  let fp := ammCtorAfterSecondReturnFreePtr ret1 ret2
  let aw := ammCtorThirdCallArgWords ret1 ret2
  have hmem : (⟨64⟩ : UInt256).toNat <
      (ammCtorThirdCallArgMem I t0 t1 liquidity ret1 ret2).size := by
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
  have rd1025 := amm_ctor_run rd with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1026 := RD.mload 0 fp aw rd1025
    (by amm_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammCtorThirdCallArgMem_read64 I t0 t1 liquidity ret1 ret2
          hbound1 hbound2)))
    (by simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using hsame)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1031 := amm_ctor_run rd1026 with [dup1, dup4, sub, dup2, dup7]
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  rw [hsub] at rd1031
  obtain ⟨gasWord, rd1032⟩ := rd1031.gas (by amm_ctor_decode) (by simp)
  exact ⟨gasWord, _, _, by simpa only [fp, aw] using rd1032⟩

theorem ammCtorThirdCallArgWords_call_nat_same (ret1 ret2 : ByteArray)
    (hlo1 : 32 ≤ ret1.size) (hbound1 : ret1.size < 2 ^ 138)
    (hlo2 : 32 ≤ ret2.size) (hbound2 : ret2.size < 2 ^ 138)
    (n : Nat) (hn : n = 32 ∨ n = 36) :
    MachineState.M (ammCtorThirdCallArgWords ret1 ret2).toNat
      (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat n =
        (ammCtorThirdCallArgWords ret1 ret2).toNat := by
  let n1 := (ret1.size + 31) / 32
  let n2 := (ret2.size + 31) / 32
  have hptr : (ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat =
      224 + 32 * n1 + 32 * n2 := by
    simpa only [n1, n2] using
      ammCtorAfterSecondReturnFreePtr_toNat ret1 ret2 hbound1 hbound2
  have haw : (ammCtorThirdCallArgWords ret1 ret2).toNat =
      9 + n1 + n2 := by
    simpa only [n1, n2] using
      ammCtorThirdCallArgWords_toNat ret1 ret2
        hlo1 hbound1 hlo2 hbound2
  rcases hn with rfl | rfl
  · change max (ammCtorThirdCallArgWords ret1 ret2).toNat
      (((ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  · change max (ammCtorThirdCallArgWords ret1 ret2).toNat
      (((ammCtorAfterSecondReturnFreePtr ret1 ret2).toNat + 36 + 31) / 32) = _
    rw [hptr, haw]
    omega

end Benchmarks.ActAmm
