import Benchmarks.ActAmm.Swap1TransferSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_balance0Address
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3088⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferDecodeMem I out) (UInt256.ofNat 7)
      out acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3145⟩
      [ammMintToken0Word acc.2 I, ⟨0⟩, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferDecodeMem I out) (UInt256.ofNat 7)
      out acc k' C' := by
  have rd1280 := evm_run rd with [
    push0, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd1281⟩ := rd1280.sload
    (by native_decide) (by evm_ov)
  have rd1332 := evm_run rd1281 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken0Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd1332⟩

theorem ammSwap1TransferDecodeMem_read64 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hhi : out.size < UInt256.size) :
    (ammSwap1TransferDecodeMem I out).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr out) := by
  unfold ammSwap1TransferDecodeMem
  exact toByteArray_write32_read_back _ _ _ (by
    rw [ammSwap1TransferPostCallMem_size_long I hlo hhi]
    omega)

noncomputable def ammSwap1Balance0SelectorMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  ammMintBalanceSelectorWord.toByteArray.write 0
    (ammSwap1TransferDecodeMem I out)
    (ammMintToken0FreePtr out).toNat 32

def ammSwap1Balance0SelectorWords (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (UInt256.ofNat 7).toNat
    (ammMintToken0FreePtr out).toNat 32)

theorem ammSwap1X_balance0SelectorMem
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3145⟩
      [ammMintToken0Word acc.2 I, ⟨0⟩, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferDecodeMem I out) (UInt256.ofNat 7)
      out acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3166⟩
      [ammMintToken0FreePtr out, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken0Word acc.2 I, ⟨0⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0SelectorMem I out)
      (ammSwap1Balance0SelectorWords out) out acc k' C' := by
  let fp := ammMintToken0FreePtr out
  let aw := ammSwap1Balance0SelectorWords out
  have hmem : 64 < (ammSwap1TransferDecodeMem I out).size := by
    rw [ammSwap1TransferDecodeMem_size I
      (lt_trans hbound (by norm_num [UInt256.size]))]
    omega
  have hawlo : 3 ≤ (UInt256.ofNat 7).toNat := by decide
  have hawfit : (UInt256.ofNat 7).toNat * 32 < UInt256.size := by
    native_decide
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammSwap1TransferDecodeMem I out).size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 7) * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap1TransferDecodeMem I out).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 _ hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammSwap1TransferDecodeMem_read64 I hlo
          (lt_trans hbound (by norm_num [UInt256.size]))))
  have rd1340 := evm_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd1341 := evm_run rd1340 with [
    raw mload 0 fp (UInt256.ofNat 7) (by native_decide)
      mem_cost hval (by decide) (by evm_ov)]
  have rd1352 := evm_run rd1341 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd1353 := RD.mstore
    (Cₘ aw - Cₘ (UInt256.ofNat 7))
    (ammSwap1Balance0SelectorMem I out) aw rd1352
    (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        aw, fp, ammSwap1Balance0SelectorWords])
    (by unfold ammSwap1Balance0SelectorMem; rfl)
    (by simp [aw, fp, ammSwap1Balance0SelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [fp, aw, ammSwap1Balance0SelectorMem,
      ammSwap1Balance0SelectorWords, ammMintBalanceSelectorWord]
      using rd1353⟩

noncomputable def ammSwap1Balance0CalldataMem
    (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (ammSwap1Balance0SelectorMem I out)
    (ammMintToken0FreePtr out + ⟨4⟩).toNat 32

def ammSwap1Balance0CalldataWords (out : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (ammSwap1Balance0SelectorWords out).toNat
    (ammMintToken0FreePtr out + ⟨4⟩).toNat 32)

theorem ammSwap1Balance0SelectorMem_size (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammMintToken0FreePtr out).toNat + 32 ≤
      (ammSwap1Balance0SelectorMem I out).size := by
  unfold ammSwap1Balance0SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammSwap1Balance0SelectorMem_read64 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0SelectorMem I out).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr out) := by
  unfold ammSwap1Balance0SelectorMem
  have hptr : 160 ≤ (ammMintToken0FreePtr out).toNat := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds out hlo hbound).1
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [ammSwap1TransferDecodeMem_size I
      (lt_trans hbound (by norm_num [UInt256.size]))]; omega)
    (by omega)]
  exact ammSwap1TransferDecodeMem_read64 I hlo
    (lt_trans hbound (by norm_num [UInt256.size]))

theorem ammSwap1Balance0SelectorMem_read4 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0SelectorMem I out).readWithPadding
      (ammMintToken0FreePtr out).toNat 4 = balanceOfSelector := by
  unfold ammSwap1Balance0SelectorMem
  have h := toByteArray_write_read_window_no_gap ammMintBalanceSelectorWord
    (ammSwap1TransferDecodeMem I out)
    (ammMintToken0FreePtr out).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : ammMintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammSwap1Balance0CalldataMem_size (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammMintToken0FreePtr out).toNat + 36 ≤
      (ammSwap1Balance0CalldataMem I out).size := by
  unfold ammSwap1Balance0CalldataMem
  rw [ammMintToken0FreePtr_add4_toNat out hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammSwap1Balance0CalldataMem_read64 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0CalldataMem I out).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr out) := by
  unfold ammSwap1Balance0CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by rw [ammMintToken0FreePtr_add4_toNat out hlo hbound];
        exact le_trans (by omega)
          (ammSwap1Balance0SelectorMem_size I hlo hbound))
    (by rw [ammMintToken0FreePtr_add4_toNat out hlo hbound];
        have h := (ammMintToken0FreePtr_bounds out hlo hbound).1
        change 160 ≤ (ammMintToken0FreePtr out).toNat at h
        omega)]
  exact ammSwap1Balance0SelectorMem_read64 I hlo hbound

theorem ammSwap1Balance0CalldataMem_read4 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0CalldataMem I out).readWithPadding
      (ammMintToken0FreePtr out).toNat 4 = balanceOfSelector := by
  unfold ammSwap1Balance0CalldataMem
  rw [write32_read_below_len _ _ _ (ammMintToken0FreePtr out).toNat 4
    (by rw [toByteArray_size])
    (by rw [ammMintToken0FreePtr_add4_toNat out hlo hbound];
        exact le_trans (by omega)
          (ammSwap1Balance0SelectorMem_size I hlo hbound))
    (by rw [ammMintToken0FreePtr_add4_toNat out hlo hbound])
    (by have h := ammSwap1Balance0SelectorMem_size I hlo hbound
        omega)
    (by norm_num) (by norm_num)]
  exact ammSwap1Balance0SelectorMem_read4 I hlo hbound

theorem ammSwap1Balance0CalldataMem_read32 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0CalldataMem I out).readWithPadding
      (ammMintToken0FreePtr out + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold ammSwap1Balance0CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [ammMintToken0FreePtr_add4_toNat out hlo hbound]
    exact le_trans (by omega)
      (ammSwap1Balance0SelectorMem_size I hlo hbound))]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammSwap1Balance0CalldataMem_read36 (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0CalldataMem I out).readWithPadding
      (ammMintToken0FreePtr out).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _
    (ammMintToken0FreePtr out).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by exact ammSwap1Balance0CalldataMem_size I hlo hbound)]
  rw [ammSwap1Balance0CalldataMem_read4 I hlo hbound,
    ← ammMintToken0FreePtr_add4_toNat out hlo hbound,
    ammSwap1Balance0CalldataMem_read32 I hlo hbound]

theorem ammSwap1Balance0CalldataMem_encode (I : ExecutionEnv)
    {out : ByteArray} (hlo : 32 ≤ out.size)
    (hbound : out.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammSwap1Balance0CalldataMem I out).readWithPadding
        (ammMintToken0FreePtr out).toNat 36) := by
  rw [ammSwap1Balance0CalldataMem_read36 I hlo hbound,
    ← ammMintBalanceCalldataMem_read I]
  exact ammMintBalanceEncode_eq I

theorem ammSwap1X_balance0ArgMem
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3166⟩
      [ammMintToken0FreePtr out, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken0Word acc.2 I, ⟨0⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0SelectorMem I out)
      (ammSwap1Balance0SelectorWords out) out acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3178⟩
      [ammMintToken0FreePtr out + ⟨36⟩, ⟨1889567281⟩,
        ammMintToken0Word acc.2 I, ⟨0⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0CalldataMem I out)
      (ammSwap1Balance0CalldataWords out) out acc k' C' := by
  let fp := ammMintToken0FreePtr out
  let awSel := ammSwap1Balance0SelectorWords out
  let awArg := ammSwap1Balance0CalldataWords out
  have rd6408 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨3178⟩, swap2, swap1,
    push2 ⟨6408⟩, jump (by jump_dest)]
  have rd6269 := evm_run rd6408 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨6427⟩, push0, dup4, add, dup5, push2 ⟨6269⟩,
    jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩,
    jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩,
    jump (by jump_dest)]
  have rd5441 := evm_run rd5400 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd6278 := evm_run rd5441 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have hcanon : (UInt256.ofNat I.codeOwner).toNat <
      EVM.addressModulus := by
    have h2 : (UInt256.ofNat I.codeOwner).toNat = I.codeOwner.val := by
      apply UInt256.toNat_ofNat_of_lt
      exact lt_of_lt_of_le I.codeOwner.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide)
    rw [h2]
    change I.codeOwner.val < AccountAddress.size
    exact I.codeOwner.isLt
  have hclean : UInt256.land (UInt256.ofNat I.codeOwner)
      solcAddrMask = UInt256.ofNat I.codeOwner :=
    solcAddrMask_clean hcanon
  have rd6278' := rd6278
  rw [hclean] at rd6278'
  rw [show (⟨4⟩ : UInt256) + ammMintToken0FreePtr out =
    ammMintToken0FreePtr out + ⟨4⟩ from
      u256_add_comm _ _] at rd6278'
  have hzero :
      (ammMintToken0FreePtr out + ⟨4⟩) + (⟨0⟩ : UInt256) =
        ammMintToken0FreePtr out + ⟨4⟩ := by
    calc
      _ = (⟨0⟩ : UInt256) + (ammMintToken0FreePtr out + ⟨4⟩) :=
        u256_add_comm _ _
      _ = _ := u256_zero_add _
  rw [hzero] at rd6278'
  have rd6427 := RD.mstore
    (Cₘ awArg - Cₘ awSel)
    (ammSwap1Balance0CalldataMem I out) awArg
    (evm_run rd6278' with [jumpdest, dup3])
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, awArg, awSel,
        ammSwap1Balance0CalldataWords])
    (by unfold ammSwap1Balance0CalldataMem; rfl)
    (by simp [awArg, awSel, fp, ammSwap1Balance0CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6427' := evm_run rd6427 with [pop, pop, jump (by jump_dest)]
  have rd1365 := evm_run rd6427' with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa only [awArg,
      u256_add_assoc (ammMintToken0FreePtr out) ⟨4⟩ ⟨32⟩,
      show (⟨4⟩ : UInt256) + ⟨32⟩ = ⟨36⟩ from by decide]
      using rd1365⟩

theorem ammSwap1Balance0SelectorWords_toNat (out : ByteArray)
    (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0SelectorWords out).toNat =
      max 7 (5 + (out.size + 31) / 32) := by
  let n := (out.size + 31) / 32
  have hptr : (ammMintToken0FreePtr out).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using
      ammMintToken0FreePtr_toNat out hbound
  have hM : MachineState.M (UInt256.ofNat 7).toNat
      (ammMintToken0FreePtr out).toNat 32 = max 7 (5 + n) := by
    change max (UInt256.ofNat 7).toNat
      (((ammMintToken0FreePtr out).toNat + 32 + 31) / 32) = _
    rw [hptr, show (UInt256.ofNat 7).toNat = 7 from by decide]
    omega
  unfold ammSwap1Balance0SelectorWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle : n ≤ out.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem ammSwap1Balance0CalldataWords_toNat (out : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    (ammSwap1Balance0CalldataWords out).toNat =
      max 7 (6 + (out.size + 31) / 32) := by
  let n := (out.size + 31) / 32
  have hptr : (ammMintToken0FreePtr out).toNat = 128 + 32 * n := by
    simpa only [ammMintToken0FreePtr, n] using
      ammMintToken0FreePtr_toNat out hbound
  have harg : (ammMintToken0FreePtr out + ⟨4⟩).toNat =
      132 + 32 * n := by
    rw [ammMintToken0FreePtr_add4_toNat out hlo hbound, hptr]
    omega
  have haw : (ammSwap1Balance0SelectorWords out).toNat =
      max 7 (5 + n) := by
    simpa only [n] using ammSwap1Balance0SelectorWords_toNat out hbound
  have hM : MachineState.M
      (ammSwap1Balance0SelectorWords out).toNat
      (ammMintToken0FreePtr out + ⟨4⟩).toNat 32 =
      max 7 (6 + n) := by
    change max (ammSwap1Balance0SelectorWords out).toNat
      (((ammMintToken0FreePtr out + ⟨4⟩).toNat + 32 + 31) / 32) = _
    rw [harg, haw]
    omega
  unfold ammSwap1Balance0CalldataWords
  rw [hM, UInt256.toNat_ofNat_of_lt (by
    have hle : n ≤ out.size + 31 := Nat.div_le_self _ _
    have hcap : 2 ^ 138 + 40 < UInt256.size := by
      norm_num [UInt256.size]
    omega)]

theorem ammSwap1Balance0CalldataWords_mload64_same (out : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (ammSwap1Balance0CalldataWords out).toNat 64 32) =
      ammSwap1Balance0CalldataWords out := by
  have haw := ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hM : MachineState.M
      (ammSwap1Balance0CalldataWords out).toNat 64 32 =
      (ammSwap1Balance0CalldataWords out).toNat := by
    change max (ammSwap1Balance0CalldataWords out).toNat
      ((64 + 32 + 31) / 32) = _
    rw [haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammSwap1X_balance0CallFrame
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3178⟩
      [ammMintToken0FreePtr out + ⟨36⟩, ⟨1889567281⟩,
        ammMintToken0Word acc.2 I, ⟨0⟩,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1Balance0CalldataMem I out)
      (ammSwap1Balance0CalldataWords out) out acc k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat),
      RD ammBytecode I g
        (initState cAstart gh bl σstart σ₀ g A I) ⟨3190⟩
        [gasWord, ammMintToken0Word acc.2 I,
          ammMintToken0FreePtr out, ⟨36⟩,
          ammMintToken0FreePtr out, ⟨32⟩,
          ammMintToken0FreePtr out + ⟨36⟩, ⟨1889567281⟩,
          ammMintToken0Word acc.2 I, ⟨0⟩,
          ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
        (ammSwap1Balance0CalldataMem I out)
        (ammSwap1Balance0CalldataWords out) out acc k' C' := by
  let fp := ammMintToken0FreePtr out
  let aw := ammSwap1Balance0CalldataWords out
  have hptr : 160 ≤ fp.toNat := by
    simpa only [fp, ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds out hlo hbound).1
  have hmem : 64 < (ammSwap1Balance0CalldataMem I out).size := by
    have hsize := ammSwap1Balance0CalldataMem_size I hlo hbound
    change 160 ≤ (ammMintToken0FreePtr out).toNat at hptr
    omega
  have haw := ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hawlo : 3 ≤ aw.toNat := by
    change 3 ≤ (ammSwap1Balance0CalldataWords out).toNat
    rw [haw]
    omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [show aw.toNat = max 7 (6 + (out.size + 31) / 32) from by
      simpa only [aw] using haw]
    have hle : (out.size + 31) / 32 ≤ out.size + 31 :=
      Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hsame : UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
    simpa only [aw] using
      ammSwap1Balance0CalldataWords_mload64_same out hlo hbound
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammSwap1Balance0CalldataMem I out).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap1Balance0CalldataMem I out).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using ammSwap1Balance0CalldataMem_read64 I hlo hbound)
  have rd1371 := evm_run rd with [
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1372 := RD.mload 0 fp aw rd1371 (by native_decide)
    (by
      intro s haw' hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw',
        hstk, List.getElem!_cons_zero]
      rw [show UInt256.ofNat (MachineState.M
        (ammSwap1Balance0CalldataWords out).toNat
        (⟨64⟩ : UInt256).toNat 32) =
        ammSwap1Balance0CalldataWords out from by
          simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1377 := evm_run rd1372 with [
    dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd1377'⟩ := rd1377
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd1377'⟩

noncomputable def ammSwap1Balance0PostCallMem
    (I : ExecutionEnv) (out ret : ByteArray) : ByteArray :=
  ret.write 0 (ammSwap1Balance0CalldataMem I out)
    (ammMintToken0FreePtr out).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat ret.size)).toNat

theorem ammSwap1Balance0CallWords_same (out : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammSwap1Balance0CalldataWords out).toNat
          (ammMintToken0FreePtr out).toNat 36)
        (ammMintToken0FreePtr out).toNat 32) =
      ammSwap1Balance0CalldataWords out := by
  let n := (out.size + 31) / 32
  let fp := ammMintToken0FreePtr out
  let aw := ammSwap1Balance0CalldataWords out
  have hfp : fp.toNat = 128 + 32 * n := by
    simpa only [fp, n, ammMintToken0FreePtr] using
      ammMintToken0FreePtr_toNat out hbound
  have haw : aw.toNat = max 7 (6 + n) := by
    simpa only [aw, n] using
      ammSwap1Balance0CalldataWords_toNat out hlo hbound
  have hM : MachineState.M
      (MachineState.M aw.toNat fp.toNat 36)
      fp.toNat 32 = aw.toNat := by
    change max (max aw.toNat ((fp.toNat + 36 + 31) / 32))
      ((fp.toNat + 32 + 31) / 32) = _
    rw [hfp, haw]
    omega
  simpa only [fp, aw, hM] using (u256_ofNat_toNat aw)

end Benchmarks.ActAmm
