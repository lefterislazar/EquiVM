import Benchmarks.ActAmm.BurnBalance0Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammBurnBalance1FreePtr (o0 o1 o2 : ByteArray) : UInt256 :=
  UInt256.add (ammBurnBalance0FreePtr o0 o1) (ammMintReturndataRounded o2)

theorem ammBurnBalance1FreePtr_toNat (o0 o1 o2 : ByteArray)
    (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1FreePtr o0 o1 o2).toNat =
      128 + 32 * ((o0.size + 31) / 32 + (o1.size + 31) / 32 +
        (o2.size + 31) / 32) := by
  have hfp := ammBurnBalance0FreePtr_toNat o0 o1 hbound0 hbound1
  have hround := ammMintReturndataRounded_toNat o2 hbound2
  have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
    Nat.div_le_self _ _
  have hle2 : (o2.size + 31) / 32 ≤ o2.size + 31 :=
    Nat.div_le_self _ _
  have hfit : (ammBurnBalance0FreePtr o0 o1).toNat +
      (ammMintReturndataRounded o2).toNat < UInt256.size := by
    rw [hfp, hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31 + 2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  change (ammBurnBalance0FreePtr o0 o1 +
    ammMintReturndataRounded o2).toNat = _
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit, hfp, hround]
  omega

theorem ammBurnBalance1FreePtr_bounds (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    160 ≤ (ammBurnBalance1FreePtr o0 o1 o2).toNat ∧
    (ammBurnBalance1FreePtr o0 o1 o2).toNat + 36 < UInt256.size := by
  have hptr := ammBurnBalance1FreePtr_toNat o0 o1 o2
    hbound0 hbound1 hbound2
  have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
    Nat.div_le_self _ _
  have hle2 : (o2.size + 31) / 32 ≤ o2.size + 31 :=
    Nat.div_le_self _ _
  have hn0 : 1 ≤ (o0.size + 31) / 32 := by omega
  have hcap : 128 + 32 *
      (2 ^ 138 + 31 + 2 ^ 138 + 31 + 2 ^ 138 + 31) + 36 <
      UInt256.size := by norm_num [UInt256.size]
  constructor <;> omega

theorem ammBurnBalance0DecodeMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) :
    (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (ammBurnBalance1FreePtr o0 o1 o2) := by
  unfold ammBurnBalance0DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _

theorem ammBurnX_balance1Address
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5232⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2)
      (ammBurnBalance0CalldataWords o0 o1) o2 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5288⟩
      [ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2)
      (ammBurnBalance0CalldataWords o0 o1) o2 (cA, σ) k' C' := by
  have rd5236 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd5237⟩ := rd5236.sload
    (by native_decide) (by evm_ov)
  have rd5288 := evm_run rd5237 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken1Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd5288⟩

noncomputable def ammBurnBalance1SelectorMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  ammMintBalanceSelectorWord.toByteArray.write 0
    (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2)
    (ammBurnBalance1FreePtr o0 o1 o2).toNat 32

def ammBurnBalance1SelectorWords (o0 o1 o2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (ammBurnBalance0CalldataWords o0 o1).toNat
    (ammBurnBalance1FreePtr o0 o1 o2).toNat 32)

theorem ammBurnX_balance1SelectorMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5288⟩
      [ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2)
      (ammBurnBalance0CalldataWords o0 o1) o2 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5309⟩
      [ammBurnBalance1FreePtr o0 o1 o2, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1SelectorWords o0 o1 o2)
      o2 (cA, σ) k' C' := by
  let aw := ammBurnBalance0CalldataWords o0 o1
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  have hmem : 64 <
      (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2).size := by
    have hsz := ammBurnBalance0DecodeMem_size_ge I q0 q1
      hlo0 hbound0 hbound1
      (lt_trans hbound2 (by norm_num [UInt256.size]))
    have hfp := (ammMintFinalFreePtr_bounds o0 o1
      hlo0 hbound0 hbound1).1
    change 160 ≤ (ammBurnBalance0FreePtr o0 o1).toNat at hfp
    omega
  have haw : aw.toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 := by
    simpa only [aw] using ammBurnBalance0CalldataWords_toNat o0 o1
      hlo0 hbound0 hlo1 hbound1
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
      Nat.div_le_self _ _
    have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
      Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 <
      UInt256.size := by norm_num [UInt256.size]
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using ammBurnBalance0DecodeMem_read64 I q0 q1 o0 o1 o2)
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd5296 := evm_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd5297 := RD.mload 0 fp aw rd5296 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammBurnBalance0CalldataWords o0 o1).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammBurnBalance0CalldataWords o0 o1 from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5308 := evm_run rd5297 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := ammBurnBalance1SelectorWords o0 o1 o2
  have rd5309 := RD.mstore (Cₘ awSel - Cₘ aw)
    (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2) awSel
    rd5308 (by native_decide)
    (by
      intro s hawS hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        awSel, aw, fp, ammBurnBalance1SelectorWords])
    (by unfold ammBurnBalance1SelectorMem; rfl)
    (by simp [awSel, aw, fp, ammBurnBalance1SelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [ammMintBalanceSelectorWord, fp, awSel]
    using rd5309⟩

noncomputable def ammBurnBalance1CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2)
    (ammBurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat 32

def ammBurnBalance1CalldataWords (o0 o1 o2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (ammBurnBalance1SelectorWords o0 o1 o2).toNat
    (ammBurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat 32)

theorem ammBurnBalance1CalldataWords_toNat (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1CalldataWords o0 o1 o2).toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 +
        (o2.size + 31) / 32 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let n2 := (o2.size + 31) / 32
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  let aw0 := ammBurnBalance0CalldataWords o0 o1
  have hfp : fp.toNat = 128 + 32 * (n0 + n1 + n2) := by
    simpa only [fp, n0, n1, n2] using
      ammBurnBalance1FreePtr_toNat o0 o1 o2
        hbound0 hbound1 hbound2
  have haw0 : aw0.toNat = 6 + n0 + n1 := by
    simpa only [aw0, n0, n1] using
      ammBurnBalance0CalldataWords_toNat o0 o1
        hlo0 hbound0 hlo1 hbound1
  have hfit := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).2
  change fp.toNat + 36 < UInt256.size at hfit
  have hfp4 : (fp + ⟨4⟩).toNat = fp.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hSel : (ammBurnBalance1SelectorWords o0 o1 o2).toNat =
      5 + n0 + n1 + n2 := by
    unfold ammBurnBalance1SelectorWords
    rw [hfp, haw0]
    change (UInt256.ofNat
      (max (6 + n0 + n1)
        ((128 + 32 * (n0 + n1 + n2) + 32 + 31) / 32))).toNat = _
    have hle0 : n0 ≤ o0.size + 31 := Nat.div_le_self _ _
    have hle1 : n1 ≤ o1.size + 31 := Nat.div_le_self _ _
    have hle2 : n2 ≤ o2.size + 31 := Nat.div_le_self _ _
    have hcap : 6 + 2 ^ 138 + 31 + 2 ^ 138 + 31 +
      2 ^ 138 + 31 < UInt256.size := by norm_num [UInt256.size]
    have hn2 : 1 ≤ n2 := by dsimp [n2]; omega
    rw [show max (6 + n0 + n1)
        ((128 + 32 * (n0 + n1 + n2) + 32 + 31) / 32) =
        5 + n0 + n1 + n2 by omega,
      UInt256.toNat_ofNat_of_lt (by omega)]
  unfold ammBurnBalance1CalldataWords
  rw [hfp4, hfp, hSel]
  change (UInt256.ofNat
    (max (5 + n0 + n1 + n2)
      ((128 + 32 * (n0 + n1 + n2) + 4 + 32 + 31) / 32))).toNat = _
  have hle0 : n0 ≤ o0.size + 31 := Nat.div_le_self _ _
  have hle1 : n1 ≤ o1.size + 31 := Nat.div_le_self _ _
  have hle2 : n2 ≤ o2.size + 31 := Nat.div_le_self _ _
  have hcap : 6 + 2 ^ 138 + 31 + 2 ^ 138 + 31 +
    2 ^ 138 + 31 < UInt256.size := by norm_num [UInt256.size]
  rw [show max (5 + n0 + n1 + n2)
      ((128 + 32 * (n0 + n1 + n2) + 4 + 32 + 31) / 32) =
      6 + n0 + n1 + n2 by omega,
    UInt256.toNat_ofNat_of_lt (by omega)]

theorem ammBurnBalance1FreePtr_add4_toNat (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat =
      (ammBurnBalance1FreePtr o0 o1 o2).toNat + 4 := by
  have hfit := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).2
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt (by omega)]

theorem ammBurnBalance1SelectorMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) :
    (ammBurnBalance1FreePtr o0 o1 o2).toNat + 32 ≤
      (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2).size := by
  unfold ammBurnBalance1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnBalance1SelectorMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (ammBurnBalance1FreePtr o0 o1 o2) := by
  unfold ammBurnBalance1SelectorMem
  have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).1
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by
      have hsz := ammBurnBalance0DecodeMem_size_ge I q0 q1
        hlo0 hbound0 hbound1
        (lt_trans hbound2 (by norm_num [UInt256.size]))
      have hfp0 := (ammMintFinalFreePtr_bounds o0 o1
        hlo0 hbound0 hbound1).1
      change 160 ≤ (ammBurnBalance0FreePtr o0 o1).toNat at hfp0
      omega)
    (by omega)]
  exact ammBurnBalance0DecodeMem_read64 I q0 q1 o0 o1 o2

theorem ammBurnBalance1CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1FreePtr o0 o1 o2).toNat + 36 ≤
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).size := by
  unfold ammBurnBalance1CalldataMem
  rw [ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
    hlo0 hbound0 hbound1 hbound2]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnBalance1CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (ammBurnBalance1FreePtr o0 o1 o2) := by
  unfold ammBurnBalance1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      rw [ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
        hlo0 hbound0 hbound1 hbound2]
      have hsz := ammBurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
      omega)
    (by
      rw [ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
        hlo0 hbound0 hbound1 hbound2]
      have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
        hlo0 hbound0 hbound1 hbound2).1
      omega)]
  exact ammBurnBalance1SelectorMem_read64 I q0 q1
    hlo0 hbound0 hbound1 hbound2

theorem ammBurnBalance1SelectorMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) :
    (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2).readWithPadding
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 4 =
      balanceOfSelector := by
  unfold ammBurnBalance1SelectorMem
  have h := toByteArray_write_read_window_no_gap
    ammMintBalanceSelectorWord
    (ammBurnBalance0DecodeMem I q0 q1 o0 o1 o2)
    (ammBurnBalance1FreePtr o0 o1 o2).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : ammMintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammBurnBalance1CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 4 =
      balanceOfSelector := by
  unfold ammBurnBalance1CalldataMem
  rw [write32_read_below_len _ _ _
    (ammBurnBalance1FreePtr o0 o1 o2).toNat 4
    (by rw [toByteArray_size])
    (by
      rw [ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
        hlo0 hbound0 hbound1 hbound2]
      have hsz := ammBurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
      omega)
    (by rw [ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
      hlo0 hbound0 hbound1 hbound2])
    (by
      have hsz := ammBurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
      omega)
    (by norm_num) (by norm_num)]
  exact ammBurnBalance1SelectorMem_read4 I q0 q1 o0 o1 o2

theorem ammBurnBalance1CalldataMem_read32 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      (ammBurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold ammBurnBalance1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
      hlo0 hbound0 hbound1 hbound2]
    have hsz := ammBurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
    omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammBurnBalance1CalldataMem_read36 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _
    (ammBurnBalance1FreePtr o0 o1 o2).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have hsz := ammBurnBalance1CalldataMem_size I q0 q1
        hlo0 hbound0 hbound1 hbound2
      omega)]
  rw [ammBurnBalance1CalldataMem_read4 I q0 q1
    hlo0 hbound0 hbound1 hbound2,
    ← ammBurnBalance1FreePtr_add4_toNat o0 o1 o2
      hlo0 hbound0 hbound1 hbound2,
    ammBurnBalance1CalldataMem_read32 I q0 q1
      hlo0 hbound0 hbound1 hbound2]

theorem ammBurnBalance1CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
        (ammBurnBalance1FreePtr o0 o1 o2).toNat 36) := by
  rw [ammBurnBalance1CalldataMem_read36 I q0 q1
    hlo0 hbound0 hbound1 hbound2,
    ← ammMintBalanceCalldataMem_read I]
  exact ammMintBalanceEncode_eq I

theorem ammBurnX_balance1ArgMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5309⟩
      [ammBurnBalance1FreePtr o0 o1 o2, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1SelectorMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1SelectorWords o0 o1 o2)
      o2 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5321⟩
      [ammBurnBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o2 (cA, σ) k' C' := by
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  have rd6408 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨5321⟩, swap2, swap1,
    push2 ⟨6408⟩, jump (by jump_dest)]
  have rd6269 := evm_run rd6408 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨6427⟩, push0, dup4, add, dup5, push2 ⟨6269⟩,
    jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩, jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩,
    jump (by jump_dest)]
  have rd5441 := evm_run rd5400 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd6278 := evm_run rd5441 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have hcanon : (UInt256.ofNat I.codeOwner).toNat < EVM.addressModulus := by
    have h2 : (UInt256.ofNat I.codeOwner).toNat = I.codeOwner.val := by
      apply UInt256.toNat_ofNat_of_lt
      exact lt_of_lt_of_le I.codeOwner.isLt
        (show AccountAddress.size ≤ UInt256.size from by decide)
    rw [h2]
    change I.codeOwner.val < AccountAddress.size
    exact I.codeOwner.isLt
  have hclean : UInt256.land (UInt256.ofNat I.codeOwner) solcAddrMask =
      UInt256.ofNat I.codeOwner := solcAddrMask_clean hcanon
  have rd6278' := rd6278
  rw [hclean] at rd6278'
  have rd6427pre := evm_run rd6278' with [jumpdest, dup3]
  have hoff : (⟨4⟩ : UInt256) + fp + ⟨0⟩ = fp + ⟨4⟩ := by
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) fp]
  have rd6427pre' := rd6427pre
  rw [hoff] at rd6427pre'
  let awArg := ammBurnBalance1CalldataWords o0 o1 o2
  have rd6427 := RD.mstore
    (Cₘ awArg - Cₘ (ammBurnBalance1SelectorWords o0 o1 o2))
    (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2) awArg
    rd6427pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awArg, fp, ammBurnBalance1CalldataWords])
    (by unfold ammBurnBalance1CalldataMem; rfl)
    (by simp [awArg, fp, ammBurnBalance1CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5321 := evm_run rd6427 with [
    pop, pop, jump (by jump_dest), jumpdest,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp, u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, awArg, hend] using rd5321⟩

theorem ammBurnX_balance1CallFrame
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5321⟩
      [ammBurnBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o2 (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5333⟩
      [gasWord, ammMintToken1Word σ I,
        ammBurnBalance1FreePtr o0 o1 o2, ⟨36⟩,
        ammBurnBalance1FreePtr o0 o1 o2, ⟨32⟩,
        ammBurnBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o2 (cA, σ) k' C' := by
  let aw := ammBurnBalance1CalldataWords o0 o1 o2
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  have haw : aw.toNat = 6 + (o0.size + 31) / 32 +
      (o1.size + 31) / 32 + (o2.size + 31) / 32 := by
    simpa only [aw] using ammBurnBalance1CalldataWords_toNat o0 o1 o2
      hlo0 hbound0 hlo1 hbound1 hlo2 hbound2
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
      Nat.div_le_self _ _
    have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
      Nat.div_le_self _ _
    have hle2 : (o2.size + 31) / 32 ≤ o2.size + 31 :=
      Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31 +
      2 ^ 138 + 31) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hmem : 64 <
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).size := by
    have hsz := ammBurnBalance1CalldataMem_size I q0 q1
      hlo0 hbound0 hbound1 hbound2
    have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
      hlo0 hbound0 hbound1 hbound2).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammBurnBalance1CalldataMem_read64 I q0 q1
          (o0 := o0) (o1 := o1) (o2 := o2)
          hlo0 hbound0 hbound1 hbound2))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd5326 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd5327 := RD.mload 0 fp aw rd5326 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammBurnBalance1CalldataWords o0 o1 o2).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammBurnBalance1CalldataWords o0 o1 o2 from by
          simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5333 := evm_run rd5327 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd5333'⟩ := rd5333
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd5333'⟩

noncomputable def ammBurnBalance1PostCallMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 o3 : ByteArray) : ByteArray :=
  o3.write 0 (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
    (ammBurnBalance1FreePtr o0 o1 o2).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat

theorem ammBurnBalance1CallWords_same (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammBurnBalance1CalldataWords o0 o1 o2).toNat
          (ammBurnBalance1FreePtr o0 o1 o2).toNat 36)
        (ammBurnBalance1FreePtr o0 o1 o2).toNat 32) =
      ammBurnBalance1CalldataWords o0 o1 o2 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let n2 := (o2.size + 31) / 32
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  let aw := ammBurnBalance1CalldataWords o0 o1 o2
  have hfp : fp.toNat = 128 + 32 * (n0 + n1 + n2) := by
    simpa only [fp, n0, n1, n2] using
      ammBurnBalance1FreePtr_toNat o0 o1 o2
        hbound0 hbound1 hbound2
  have haw : aw.toNat = 6 + n0 + n1 + n2 := by
    simpa only [aw, n0, n1, n2] using
      ammBurnBalance1CalldataWords_toNat o0 o1 o2
        hlo0 hbound0 hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M
      (MachineState.M aw.toNat fp.toNat 36)
      fp.toNat 32 = aw.toNat := by
    change max (max aw.toNat ((fp.toNat + 36 + 31) / 32))
      ((fp.toNat + 32 + 31) / 32) = _
    rw [hfp, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

end Benchmarks.ActAmm
