import Benchmarks.ActAmm4.ConstructorFirstCallDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

noncomputable def amm4CtorInitialToken0Target (I : ExecutionEnv)
    (σ : AccountMap) : UInt256 :=
  UInt256.land (amm4CtorStorageWord σ I ⟨3⟩) solcAddrMask

theorem amm4CtorInitialToken0Target_eq_doubleMask
    (I : ExecutionEnv) (σ : AccountMap) :
    UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div (amm4CtorStorageWord σ I ⟨3⟩)
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      amm4CtorInitialToken0Target I σ := by
  let w := amm4CtorStorageWord σ I ⟨3⟩
  have hpow : UInt256.exp ⟨256⟩ ⟨0⟩ = ⟨1⟩ := by native_decide
  have hdiv : UInt256.div w (UInt256.exp ⟨256⟩ ⟨0⟩) = w := by
    rw [hpow]
    apply u256_inj
    rw [udiv_toNat]
    change w.toNat / 1 = w.toNat
    simp
  have hmask : UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land w solcAddrMask := by
    rw [u256_land_comm solcAddrMask w]
    exact solcAddrMask_clean_left (solcAddrMask_result_canonical w)
  unfold amm4CtorInitialToken0Target
  simp only [w, hdiv, hmask]

theorem amm4CtorSecondCallTarget
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨472⟩ [v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨529⟩ [amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret (cA, σ) k' C' := by
  have rd477 := amm4_ctor_run rd with [
    jumpdest, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd478⟩ := rd477.sload (by amm4_ctor_decode) (by simp)
  have rd529 := amm4_ctor_run rd478 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have htop : UInt256.land solcAddrMask
      (UInt256.land solcAddrMask
        (UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩))
          (UInt256.exp ⟨256⟩ ⟨0⟩))) =
      amm4CtorInitialToken0Target I σ := by
    simpa only [amm4CtorStorageWord] using
      amm4CtorInitialToken0Target_eq_doubleMask I σ
  rw [htop] at rd529
  exact ⟨_, _, by simpa using rd529⟩

abbrev amm4CtorSecondCallFreePtr (ret : ByteArray) : UInt256 :=
  ⟨224⟩ + amm4MintReturndataRounded ret

theorem amm4CtorInitialToken1DecodeMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hretsz : ret.size < UInt256.size) :
    (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret).readWithPadding
      64 32 = UInt256.toByteArray (amm4CtorSecondCallFreePtr ret) := by
  unfold amm4CtorInitialToken1DecodeMem amm4CtorSecondCallFreePtr
  exact toByteArray_write32_read_back _ _ 64 (by
    rw [amm4CtorInitialToken1PostCallMem_size I t0 t1 liquidity ret hretsz]
    decide)

theorem amm4CtorSecondCallFreePtrLoaded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (hretsz : ret.size < UInt256.size)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨529⟩ [amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨538⟩ [amm4CtorSecondCallFreePtr ret,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret (cA, σ) k' C' := by
  have rd537 := amm4_ctor_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd538 := rd537.mload 0 (amm4CtorSecondCallFreePtr ret) (UInt256.ofNat 9)
    (by amm4_ctor_decode) mem_cost
    (mloadWordValue_of_readWithPadding
      (by rw [amm4CtorInitialToken1DecodeMem_size I t0 t1 liquidity ret hretsz]; decide)
      (by native_decide)
      (amm4CtorInitialToken1DecodeMem_read64 I t0 t1 liquidity ret hretsz))
    (by native_decide) (by simp)
  exact ⟨_, _, by simpa using rd538⟩

noncomputable def amm4CtorSecondCallSelectorMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) (ret : ByteArray) : ByteArray :=
  (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).write 0
    (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
    (amm4CtorSecondCallFreePtr ret).toNat 32

abbrev amm4CtorSecondCallSelectorWords (ret : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 9 (amm4CtorSecondCallFreePtr ret).toNat 32)

theorem amm4CtorSecondCallSelectorStored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨538⟩ [amm4CtorSecondCallFreePtr ret,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
      (UInt256.ofNat 9) ret (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨550⟩ [amm4CtorSecondCallFreePtr ret,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret)
      (amm4CtorSecondCallSelectorWords ret) ret (cA, σ) k' C' := by
  have rd549 := amm4_ctor_run rd with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have hselector : UInt256.land ⟨4294967295⟩ ⟨1889567281⟩ =
      ⟨1889567281⟩ := by native_decide
  rw [hselector] at rd549
  have rd550 := rd549.mstore
    (Cₘ (amm4CtorSecondCallSelectorWords ret) - Cₘ (UInt256.ofNat 9))
    (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret)
    (amm4CtorSecondCallSelectorWords ret)
    (by amm4_ctor_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        amm4CtorSecondCallSelectorWords,
        show (UInt256.ofNat 9).toNat = 9 from by decide])
    (by rfl) (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4CtorSecondCallSelectorMem,
    amm4CtorSecondCallSelectorWords] using rd550⟩

theorem amm4CtorSecondCallFreePtr_toNat (ret : ByteArray)
    (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallFreePtr ret).toNat =
      224 + 32 * ((ret.size + 31) / 32) := by
  unfold amm4CtorSecondCallFreePtr
  rw [uadd_toNat, amm4MintReturndataRounded_toNat ret hbound]
  rw [show (⟨224⟩ : UInt256).toNat = 224 from by decide,
    Nat.mod_eq_of_lt]
  have hdiv := Nat.div_le_self (ret.size + 31) 32
  norm_num [UInt256.size] at *
  omega

theorem amm4CtorSecondCallFreePtr_bounds (ret : ByteArray)
    (hbound : ret.size < 2 ^ 138) :
    224 ≤ (amm4CtorSecondCallFreePtr ret).toNat ∧
      (amm4CtorSecondCallFreePtr ret).toNat ≤ ret.size + 255 := by
  rw [amm4CtorSecondCallFreePtr_toNat ret hbound]
  have hround := Nat.mul_div_le (ret.size + 31) 32
  omega

theorem amm4CtorSecondCallFreePtr_add4_toNat (ret : ByteArray)
    (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat =
      (amm4CtorSecondCallFreePtr ret).toNat + 4 := by
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt]
  have hptr := (amm4CtorSecondCallFreePtr_bounds ret hbound).2
  norm_num [UInt256.size] at *
  omega

theorem amm4CtorSecondCallSelectorMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) :
    (amm4CtorSecondCallFreePtr ret).toNat + 32 ≤
      (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret).size := by
  unfold amm4CtorSecondCallSelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4CtorSecondCallSelectorMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hretsz : ret.size < UInt256.size)
    (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret).readWithPadding
      64 32 = UInt256.toByteArray (amm4CtorSecondCallFreePtr ret) := by
  unfold amm4CtorSecondCallSelectorMem
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [amm4CtorInitialToken1DecodeMem_size I t0 t1 liquidity ret hretsz]; decide)
    (by have h := (amm4CtorSecondCallFreePtr_bounds ret hbound).1; omega)]
  exact amm4CtorInitialToken1DecodeMem_read64 I t0 t1 liquidity ret hretsz

theorem amm4CtorSecondCallSelectorMem_read4
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) :
    (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret).readWithPadding
      (amm4CtorSecondCallFreePtr ret).toNat 4 = balanceOfSelector := by
  unfold amm4CtorSecondCallSelectorMem
  have h := toByteArray_write_read_window_no_gap
    (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)
    (amm4CtorInitialToken1DecodeMem I t0 t1 liquidity ret)
    (amm4CtorSecondCallFreePtr ret).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword :
      (UInt256.toByteArray (UInt256.shiftLeft ⟨1889567281⟩ ⟨224⟩)).extract 0 4 =
        balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

noncomputable def amm4CtorSecondCallArgMem (I : ExecutionEnv)
    (t0 t1 : AccountAddress) (liquidity : UInt256) (ret : ByteArray) : ByteArray :=
  (UInt256.toByteArray
    (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val))).write 0
    (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret)
    (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat 32

abbrev amm4CtorSecondCallArgWords (ret : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4CtorSecondCallSelectorWords ret).toNat
    (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat 32)

theorem amm4CtorSecondCallEncoded
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨550⟩ [amm4CtorSecondCallFreePtr ret,
        UInt256.ofNat I.codeOwner.val, ⟨1889567281⟩,
        amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret)
      (amm4CtorSecondCallSelectorWords ret) ret (cA, σ) k C) :
    ∃ k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨562⟩ [amm4CtorSecondCallFreePtr ret + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret)
      (amm4CtorSecondCallArgWords ret) ret (cA, σ) k' C' := by
  have rd1592 := amm4_ctor_run rd with [
    push1 ⟨4⟩, add, push2 ⟨562⟩, swap2, swap1,
    push2 ⟨1592⟩, jump (by amm4_ctor_jd)]
  rw [u256_add_comm ⟨4⟩ (amm4CtorSecondCallFreePtr ret)] at rd1592
  obtain ⟨_, _, rd562⟩ := RD.amm4CtorEncodeAddressArg rd1592
    (by amm4_ctor_jd) (by simp only [List.length_cons, List.length_nil]; omega)
  have hend : (amm4CtorSecondCallFreePtr ret + ⟨4⟩) + ⟨32⟩ =
      amm4CtorSecondCallFreePtr ret + ⟨36⟩ := by
    rw [u256_add_assoc]
    congr 1
  rw [hend] at rd562
  exact ⟨_, _, by simpa only [amm4CtorSecondCallArgMem,
    amm4CtorSecondCallArgWords] using rd562⟩

theorem amm4CtorSecondCallArgMem_size
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallFreePtr ret).toNat + 36 ≤
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret).size := by
  unfold amm4CtorSecondCallArgMem
  rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4CtorSecondCallArgMem_read64
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hretsz : ret.size < UInt256.size)
    (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret).readWithPadding
      64 32 = UInt256.toByteArray (amm4CtorSecondCallFreePtr ret) := by
  unfold amm4CtorSecondCallArgMem
  rw [write32_read_below _ _ _ 64
    (by rw [toByteArray_size])
    (by rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound];
        exact le_trans (by omega)
          (amm4CtorSecondCallSelectorMem_size I t0 t1 liquidity ret))
    (by rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound];
        have h := (amm4CtorSecondCallFreePtr_bounds ret hbound).1
        omega)]
  exact amm4CtorSecondCallSelectorMem_read64 I t0 t1 liquidity ret hretsz hbound

theorem amm4CtorSecondCallArgMem_read4
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret).readWithPadding
      (amm4CtorSecondCallFreePtr ret).toNat 4 = balanceOfSelector := by
  unfold amm4CtorSecondCallArgMem
  have hdest : (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat ≤
      (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret).size := by
    rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound]
    have hsize := amm4CtorSecondCallSelectorMem_size I t0 t1 liquidity ret
    omega
  have hbelow : (amm4CtorSecondCallFreePtr ret).toNat + 4 ≤
      (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat := by
    rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound]
  have hin : (amm4CtorSecondCallFreePtr ret).toNat + 4 ≤
      (amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret).size := by
    have hsize := amm4CtorSecondCallSelectorMem_size I t0 t1 liquidity ret
    omega
  have hpres := write32_read_below_len
    (src := UInt256.toByteArray
      (UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val)))
    (base := amm4CtorSecondCallSelectorMem I t0 t1 liquidity ret)
    (dest := (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat)
    (read := (amm4CtorSecondCallFreePtr ret).toNat)
    (len := 4)
    (by rw [toByteArray_size]) hdest hbelow hin
    (by norm_num) (by norm_num)
  rw [hpres]
  exact amm4CtorSecondCallSelectorMem_read4 I t0 t1 liquidity ret

theorem amm4CtorSecondCallArgMem_read32
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret).readWithPadding
      (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  unfold amm4CtorSecondCallArgMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound]
    exact le_trans (by omega)
      (amm4CtorSecondCallSelectorMem_size I t0 t1 liquidity ret))]
  have hcanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus :=
    amm4CtorAddressWord_canonical I.codeOwner
  rw [solcAddrMask_clean_left hcanon]
  rw [toByteArray_extract_all]

theorem amm4CtorSecondCallArgMem_read36
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallArgMem I t0 t1 liquidity ret).readWithPadding
      (amm4CtorSecondCallFreePtr ret).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner.val) := by
  rw [byteArray_readWithPadding_split _
    (amm4CtorSecondCallFreePtr ret).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret hbound)]
  rw [amm4CtorSecondCallArgMem_read4 I t0 t1 liquidity ret hbound,
    ← amm4CtorSecondCallFreePtr_add4_toNat ret hbound,
    amm4CtorSecondCallArgMem_read32 I t0 t1 liquidity ret hbound]

theorem amm4CtorSecondCallArgMem_encode
    (I : ExecutionEnv) (t0 t1 : AccountAddress) (liquidity : UInt256)
    (ret : ByteArray) (hbound : ret.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4CtorSecondCallArgMem I t0 t1 liquidity ret).readWithPadding
        (amm4CtorSecondCallFreePtr ret).toNat 36) := by
  rw [amm4CtorSecondCallArgMem_read36 I t0 t1 liquidity ret hbound]
  have hword : EVM.word (↑I.codeOwner.val) = UInt256.ofNat I.codeOwner := rfl
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, balanceOfSelector, selectorBytes, hword,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem amm4CtorSecondCallSelectorWords_toNat (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallSelectorWords ret).toNat =
      8 + (ret.size + 31) / 32 := by
  let n := (ret.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (amm4CtorSecondCallFreePtr ret).toNat = 224 + 32 * n := by
    simpa only [n] using amm4CtorSecondCallFreePtr_toNat ret hbound
  have hM : MachineState.M 9 (amm4CtorSecondCallFreePtr ret).toNat 32 =
      8 + n := by
    change max 9 (((amm4CtorSecondCallFreePtr ret).toNat + 32 + 31) / 32) = 8 + n
    rw [hptr]
    omega
  unfold amm4CtorSecondCallSelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle := Nat.div_le_self (ret.size + 31) 32
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega)]

theorem amm4CtorSecondCallArgWords_toNat (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    (amm4CtorSecondCallArgWords ret).toNat =
      9 + (ret.size + 31) / 32 := by
  let n := (ret.size + 31) / 32
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hptr : (amm4CtorSecondCallFreePtr ret).toNat = 224 + 32 * n := by
    simpa only [n] using amm4CtorSecondCallFreePtr_toNat ret hbound
  have harg : (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat =
      228 + 32 * n := by
    rw [amm4CtorSecondCallFreePtr_add4_toNat ret hbound, hptr]
    omega
  have haw : (amm4CtorSecondCallSelectorWords ret).toNat = 8 + n := by
    simpa only [n] using amm4CtorSecondCallSelectorWords_toNat ret hlo hbound
  have hM : MachineState.M (amm4CtorSecondCallSelectorWords ret).toNat
      (amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat 32 = 9 + n := by
    change max (amm4CtorSecondCallSelectorWords ret).toNat
      (((amm4CtorSecondCallFreePtr ret + ⟨4⟩).toNat + 32 + 31) / 32) = 9 + n
    rw [harg, haw]
    omega
  unfold amm4CtorSecondCallArgWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle := Nat.div_le_self (ret.size + 31) 32
    have hcap : 2 ^ 138 + 40 < UInt256.size := by norm_num [UInt256.size]
    omega)]

theorem amm4CtorSecondCallArgWords_mload64_same (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4CtorSecondCallArgWords ret).toNat 64 32) =
      amm4CtorSecondCallArgWords ret := by
  have haw := amm4CtorSecondCallArgWords_toNat ret hlo hbound
  have hM : MachineState.M (amm4CtorSecondCallArgWords ret).toNat 64 32 =
      (amm4CtorSecondCallArgWords ret).toNat := by
    change max (amm4CtorSecondCallArgWords ret).toNat ((64 + 32 + 31) / 32) = _
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4CtorSecondCallArgWords_mload64_haw (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    ¬ (⟨64⟩ : UInt256) ≥ amm4CtorSecondCallArgWords ret * ⟨32⟩ := by
  have haw := amm4CtorSecondCallArgWords_toNat ret hlo hbound
  have hmul : (amm4CtorSecondCallArgWords ret).toNat * 32 < UInt256.size := by
    have hle := Nat.div_le_self (ret.size + 31) 32
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4CtorSecondCallArgWords ret * ⟨32⟩).toNat ≤ 64 := by
    simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, haw] at hle
  omega

theorem amm4CtorSecondCallStaticcallFrame
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    {t0 t1 : AccountAddress}
    {liquidity v1 : UInt256}
    {ret : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare}
    {k C : Nat}
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138)
    (rd : RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨562⟩ [amm4CtorSecondCallFreePtr ret + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret)
      (amm4CtorSecondCallArgWords ret) ret (cA, σ) k C) :
    ∃ gasWord k' C', RD (amm4CtorCode t0 t1 liquidity) I g
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀ g A I)
      ⟨574⟩ [gasWord, amm4CtorInitialToken0Target I σ,
        amm4CtorSecondCallFreePtr ret, ⟨36⟩,
        amm4CtorSecondCallFreePtr ret, ⟨32⟩,
        amm4CtorSecondCallFreePtr ret + ⟨36⟩,
        ⟨1889567281⟩, amm4CtorInitialToken0Target I σ,
        v1, liquidity, EVM.word t1, EVM.word t0]
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret)
      (amm4CtorSecondCallArgWords ret) ret (cA, σ) k' C' := by
  let fp := amm4CtorSecondCallFreePtr ret
  let aw := amm4CtorSecondCallArgWords ret
  have hretsz : ret.size < UInt256.size := by
    have h := hbound
    norm_num [UInt256.size] at *
    omega
  have hmem : (⟨64⟩ : UInt256).toNat <
      (amm4CtorSecondCallArgMem I t0 t1 liquidity ret).size := by
    have hsize := amm4CtorSecondCallArgMem_size I t0 t1 liquidity ret hbound
    have hptr := (amm4CtorSecondCallFreePtr_bounds ret hbound).1
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
    omega
  have haw := amm4CtorSecondCallArgWords_mload64_haw ret hlo hbound
  have hsame := amm4CtorSecondCallArgWords_mload64_same ret hlo hbound
  have rd567 := amm4_ctor_run rd with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd568 := RD.mload 0 fp aw rd567
    (by amm4_ctor_decode)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hsame]
      omega)
    (mloadWordValue_of_readWithPadding hmem haw
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using amm4CtorSecondCallArgMem_read64 I t0 t1 liquidity ret hretsz hbound))
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd573 := amm4_ctor_run rd568 with [dup1, dup4, sub, dup2, dup7]
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  rw [hsub] at rd573
  obtain ⟨gasWord, rd574⟩ := rd573.gas (by amm4_ctor_decode) (by simp)
  exact ⟨gasWord, _, _, by simpa only [fp, aw] using rd574⟩

theorem amm4CtorSecondCallArgWords_call_same (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4CtorSecondCallArgWords ret).toNat
      (amm4CtorSecondCallFreePtr ret).toNat 32) =
      amm4CtorSecondCallArgWords ret := by
  let n := (ret.size + 31) / 32
  have hptr : (amm4CtorSecondCallFreePtr ret).toNat = 224 + 32 * n := by
    simpa only [n] using amm4CtorSecondCallFreePtr_toNat ret hbound
  have haw : (amm4CtorSecondCallArgWords ret).toNat = 9 + n := by
    simpa only [n] using amm4CtorSecondCallArgWords_toNat ret hlo hbound
  have hM : MachineState.M (amm4CtorSecondCallArgWords ret).toNat
      (amm4CtorSecondCallFreePtr ret).toNat 32 =
      (amm4CtorSecondCallArgWords ret).toNat := by
    change max (amm4CtorSecondCallArgWords ret).toNat
      (((amm4CtorSecondCallFreePtr ret).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4CtorSecondCallArgWords_callInput_same (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4CtorSecondCallArgWords ret).toNat
      (amm4CtorSecondCallFreePtr ret).toNat 36) =
      amm4CtorSecondCallArgWords ret := by
  let n := (ret.size + 31) / 32
  have hptr : (amm4CtorSecondCallFreePtr ret).toNat = 224 + 32 * n := by
    simpa only [n] using amm4CtorSecondCallFreePtr_toNat ret hbound
  have haw : (amm4CtorSecondCallArgWords ret).toNat = 9 + n := by
    simpa only [n] using amm4CtorSecondCallArgWords_toNat ret hlo hbound
  have hM : MachineState.M (amm4CtorSecondCallArgWords ret).toNat
      (amm4CtorSecondCallFreePtr ret).toNat 36 =
      (amm4CtorSecondCallArgWords ret).toNat := by
    change max (amm4CtorSecondCallArgWords ret).toNat
      (((amm4CtorSecondCallFreePtr ret).toNat + 36 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4CtorSecondCallArgWords_callInput_nat_same (ret : ByteArray)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138) :
    MachineState.M (amm4CtorSecondCallArgWords ret).toNat
      (amm4CtorSecondCallFreePtr ret).toNat 36 =
      (amm4CtorSecondCallArgWords ret).toNat := by
  let n := (ret.size + 31) / 32
  have hptr : (amm4CtorSecondCallFreePtr ret).toNat = 224 + 32 * n := by
    simpa only [n] using amm4CtorSecondCallFreePtr_toNat ret hbound
  have haw : (amm4CtorSecondCallArgWords ret).toNat = 9 + n := by
    simpa only [n] using amm4CtorSecondCallArgWords_toNat ret hlo hbound
  change max (amm4CtorSecondCallArgWords ret).toNat
    (((amm4CtorSecondCallFreePtr ret).toNat + 36 + 31) / 32) = _
  rw [hptr, haw]
  omega

end Benchmarks.ActAmm4
