import Benchmarks.ActAmm4.BurnBalance0Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4BurnBalance1FreePtr (o0 o1 o2 : ByteArray) : UInt256 :=
  UInt256.add (amm4BurnBalance0FreePtr o0 o1) (amm4MintReturndataRounded o2)

theorem amm4BurnBalance1FreePtr_toNat (o0 o1 o2 : ByteArray)
    (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat =
      128 + 32 * ((o0.size + 31) / 32 + (o1.size + 31) / 32 +
        (o2.size + 31) / 32) := by
  have hfp := amm4BurnBalance0FreePtr_toNat o0 o1 hbound0 hbound1
  have hround := amm4MintReturndataRounded_toNat o2 hbound2
  have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
    Nat.div_le_self _ _
  have hle2 : (o2.size + 31) / 32 ≤ o2.size + 31 :=
    Nat.div_le_self _ _
  have hfit : (amm4BurnBalance0FreePtr o0 o1).toNat +
      (amm4MintReturndataRounded o2).toNat < UInt256.size := by
    rw [hfp, hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31 + 2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  change (amm4BurnBalance0FreePtr o0 o1 +
    amm4MintReturndataRounded o2).toNat = _
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit, hfp, hround]
  omega

theorem amm4BurnBalance1FreePtr_bounds (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    160 ≤ (amm4BurnBalance1FreePtr o0 o1 o2).toNat ∧
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat + 36 < UInt256.size := by
  have hptr := amm4BurnBalance1FreePtr_toNat o0 o1 o2
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

theorem amm4BurnBalance0DecodeMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) :
    (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (amm4BurnBalance1FreePtr o0 o1 o2) := by
  unfold amm4BurnBalance0DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _

theorem amm4BurnX_balance1Address
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4419⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance0CalldataWords o0 o1) o2 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4475⟩
      [amm4MintToken1Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance0CalldataWords o0 o1) o2 (cA, σ) k' C' := by
  have rd4423 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd4424⟩ := rd4423.sload
    (by native_decide) (by evm_ov)
  have rd4475 := evm_run rd4424 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken1Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd4475⟩

noncomputable def amm4BurnBalance1SelectorMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  amm4MintBalanceSelectorWord.toByteArray.write 0
    (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2)
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat 32

def amm4BurnBalance1SelectorWords (o0 o1 o2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (amm4BurnBalance0CalldataWords o0 o1).toNat
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat 32)

theorem amm4BurnX_balance1SelectorMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4475⟩
      [amm4MintToken1Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance0CalldataWords o0 o1) o2 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4496⟩
      [amm4BurnBalance1FreePtr o0 o1 o2, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance1SelectorWords o0 o1 o2)
      o2 (cA, σ) k' C' := by
  let aw := amm4BurnBalance0CalldataWords o0 o1
  let fp := amm4BurnBalance1FreePtr o0 o1 o2
  have hmem : 64 <
      (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2).size := by
    have hsz := amm4BurnBalance0DecodeMem_size_ge I q0 q1
      hlo0 hbound0 hbound1
      (lt_trans hbound2 (by norm_num [UInt256.size]))
    have hfp := (amm4MintFinalFreePtr_bounds o0 o1
      hlo0 hbound0 hbound1).1
    change 160 ≤ (amm4BurnBalance0FreePtr o0 o1).toNat at hfp
    omega
  have haw : aw.toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 := by
    simpa only [aw] using amm4BurnBalance0CalldataWords_toNat o0 o1
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
          (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (amm4ActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using amm4BurnBalance0DecodeMem_read64 I q0 q1 o0 o1 o2)
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd4483 := evm_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd4484 := RD.mload 0 fp aw rd4483 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4BurnBalance0CalldataWords o0 o1).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            amm4BurnBalance0CalldataWords o0 o1 from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4495 := evm_run rd4484 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := amm4BurnBalance1SelectorWords o0 o1 o2
  have rd4496 := RD.mstore (Cₘ awSel - Cₘ aw)
    (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2) awSel
    rd4495 (by native_decide)
    (by
      intro s hawS hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        awSel, aw, fp, amm4BurnBalance1SelectorWords])
    (by unfold amm4BurnBalance1SelectorMem; rfl)
    (by simp [awSel, aw, fp, amm4BurnBalance1SelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4MintBalanceSelectorWord, fp, awSel]
    using rd4496⟩

noncomputable def amm4BurnBalance1CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2)
    (amm4BurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat 32

def amm4BurnBalance1CalldataWords (o0 o1 o2 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (amm4BurnBalance1SelectorWords o0 o1 o2).toNat
    (amm4BurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat 32)

theorem amm4BurnBalance1CalldataWords_toNat (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1CalldataWords o0 o1 o2).toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 +
        (o2.size + 31) / 32 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let n2 := (o2.size + 31) / 32
  let fp := amm4BurnBalance1FreePtr o0 o1 o2
  let aw0 := amm4BurnBalance0CalldataWords o0 o1
  have hfp : fp.toNat = 128 + 32 * (n0 + n1 + n2) := by
    simpa only [fp, n0, n1, n2] using
      amm4BurnBalance1FreePtr_toNat o0 o1 o2
        hbound0 hbound1 hbound2
  have haw0 : aw0.toNat = 6 + n0 + n1 := by
    simpa only [aw0, n0, n1] using
      amm4BurnBalance0CalldataWords_toNat o0 o1
        hlo0 hbound0 hlo1 hbound1
  have hfit := (amm4BurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).2
  change fp.toNat + 36 < UInt256.size at hfit
  have hfp4 : (fp + ⟨4⟩).toNat = fp.toNat + 4 := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hSel : (amm4BurnBalance1SelectorWords o0 o1 o2).toNat =
      5 + n0 + n1 + n2 := by
    unfold amm4BurnBalance1SelectorWords
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
  unfold amm4BurnBalance1CalldataWords
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

theorem amm4BurnBalance1FreePtr_add4_toNat (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat =
      (amm4BurnBalance1FreePtr o0 o1 o2).toNat + 4 := by
  have hfit := (amm4BurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).2
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt (by omega)]

theorem amm4BurnBalance1SelectorMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) :
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat + 32 ≤
      (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2).size := by
  unfold amm4BurnBalance1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4BurnBalance1SelectorMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (amm4BurnBalance1FreePtr o0 o1 o2) := by
  unfold amm4BurnBalance1SelectorMem
  have hptr := (amm4BurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).1
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by
      have hsz := amm4BurnBalance0DecodeMem_size_ge I q0 q1
        hlo0 hbound0 hbound1
        (lt_trans hbound2 (by norm_num [UInt256.size]))
      have hfp0 := (amm4MintFinalFreePtr_bounds o0 o1
        hlo0 hbound0 hbound1).1
      change 160 ≤ (amm4BurnBalance0FreePtr o0 o1).toNat at hfp0
      omega)
    (by omega)]
  exact amm4BurnBalance0DecodeMem_read64 I q0 q1 o0 o1 o2

theorem amm4BurnBalance1CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat + 36 ≤
      (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).size := by
  unfold amm4BurnBalance1CalldataMem
  rw [amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
    hlo0 hbound0 hbound1 hbound2]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4BurnBalance1CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (amm4BurnBalance1FreePtr o0 o1 o2) := by
  unfold amm4BurnBalance1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      rw [amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
        hlo0 hbound0 hbound1 hbound2]
      have hsz := amm4BurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
      omega)
    (by
      rw [amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
        hlo0 hbound0 hbound1 hbound2]
      have hptr := (amm4BurnBalance1FreePtr_bounds o0 o1 o2
        hlo0 hbound0 hbound1 hbound2).1
      omega)]
  exact amm4BurnBalance1SelectorMem_read64 I q0 q1
    hlo0 hbound0 hbound1 hbound2

theorem amm4BurnBalance1SelectorMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) :
    (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2).readWithPadding
      (amm4BurnBalance1FreePtr o0 o1 o2).toNat 4 =
      balanceOfSelector := by
  unfold amm4BurnBalance1SelectorMem
  have h := toByteArray_write_read_window_no_gap
    amm4MintBalanceSelectorWord
    (amm4BurnBalance0DecodeMem I q0 q1 o0 o1 o2)
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : amm4MintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4BurnBalance1CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      (amm4BurnBalance1FreePtr o0 o1 o2).toNat 4 =
      balanceOfSelector := by
  unfold amm4BurnBalance1CalldataMem
  rw [write32_read_below_len _ _ _
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat 4
    (by rw [toByteArray_size])
    (by
      rw [amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
        hlo0 hbound0 hbound1 hbound2]
      have hsz := amm4BurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
      omega)
    (by rw [amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
      hlo0 hbound0 hbound1 hbound2])
    (by
      have hsz := amm4BurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
      omega)
    (by norm_num) (by norm_num)]
  exact amm4BurnBalance1SelectorMem_read4 I q0 q1 o0 o1 o2

theorem amm4BurnBalance1CalldataMem_read32 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      (amm4BurnBalance1FreePtr o0 o1 o2 + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold amm4BurnBalance1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
      hlo0 hbound0 hbound1 hbound2]
    have hsz := amm4BurnBalance1SelectorMem_size I q0 q1 o0 o1 o2
    omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4BurnBalance1CalldataMem_read36 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
      (amm4BurnBalance1FreePtr o0 o1 o2).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have hsz := amm4BurnBalance1CalldataMem_size I q0 q1
        hlo0 hbound0 hbound1 hbound2
      omega)]
  rw [amm4BurnBalance1CalldataMem_read4 I q0 q1
    hlo0 hbound0 hbound1 hbound2,
    ← amm4BurnBalance1FreePtr_add4_toNat o0 o1 o2
      hlo0 hbound0 hbound1 hbound2,
    amm4BurnBalance1CalldataMem_read32 I q0 q1
      hlo0 hbound0 hbound1 hbound2]

theorem amm4BurnBalance1CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
        (amm4BurnBalance1FreePtr o0 o1 o2).toNat 36) := by
  rw [amm4BurnBalance1CalldataMem_read36 I q0 q1
    hlo0 hbound0 hbound1 hbound2,
    ← amm4MintBalanceCalldataMem_read I]
  exact amm4MintBalanceEncode_eq I

theorem amm4BurnX_balance1ArgMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4496⟩
      [amm4BurnBalance1FreePtr o0 o1 o2, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance1SelectorMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance1SelectorWords o0 o1 o2)
      o2 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4508⟩
      [amm4BurnBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance1CalldataWords o0 o1 o2)
      o2 (cA, σ) k' C' := by
  let fp := amm4BurnBalance1FreePtr o0 o1 o2
  have rd5370 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨4508⟩, swap2, swap1,
    push2 ⟨5370⟩, jump (by jump_dest)]
  have rd5355 := evm_run rd5370 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push2 ⟨5389⟩, push0, dup4, add, dup5, push2 ⟨5355⟩,
    jump (by jump_dest)]
  have rd4618 := evm_run rd5355 with [
    jumpdest, push2 ⟨5364⟩, dup2, push2 ⟨4618⟩, jump (by jump_dest)]
  have rd4587 := evm_run rd4618 with [
    jumpdest, push0, push2 ⟨4628⟩, dup3, push2 ⟨4587⟩,
    jump (by jump_dest)]
  have rd4628 := evm_run rd4587 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd5364 := evm_run rd4628 with [
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
  have rd5364' := rd5364
  rw [hclean] at rd5364'
  have rd5389pre := evm_run rd5364' with [jumpdest, dup3]
  have hoff : (⟨4⟩ : UInt256) + fp + ⟨0⟩ = fp + ⟨4⟩ := by
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) fp]
  have rd5389pre' := rd5389pre
  rw [hoff] at rd5389pre'
  let awArg := amm4BurnBalance1CalldataWords o0 o1 o2
  have rd5389 := RD.mstore
    (Cₘ awArg - Cₘ (amm4BurnBalance1SelectorWords o0 o1 o2))
    (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2) awArg
    rd5389pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awArg, fp, amm4BurnBalance1CalldataWords])
    (by unfold amm4BurnBalance1CalldataMem; rfl)
    (by simp [awArg, fp, amm4BurnBalance1CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4508 := evm_run rd5389 with [
    pop, pop, jump (by jump_dest), jumpdest,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp, u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, awArg, hend] using rd4508⟩

theorem amm4BurnX_balance1CallFrame
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 : ByteArray} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4508⟩
      [amm4BurnBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance1CalldataWords o0 o1 o2)
      o2 (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4520⟩
      [gasWord, amm4MintToken1Word σ I,
        amm4BurnBalance1FreePtr o0 o1 o2, ⟨36⟩,
        amm4BurnBalance1FreePtr o0 o1 o2, ⟨32⟩,
        amm4BurnBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (amm4BurnBalance1CalldataWords o0 o1 o2)
      o2 (cA, σ) k' C' := by
  let aw := amm4BurnBalance1CalldataWords o0 o1 o2
  let fp := amm4BurnBalance1FreePtr o0 o1 o2
  have haw : aw.toNat = 6 + (o0.size + 31) / 32 +
      (o1.size + 31) / 32 + (o2.size + 31) / 32 := by
    simpa only [aw] using amm4BurnBalance1CalldataWords_toNat o0 o1 o2
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
      (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).size := by
    have hsz := amm4BurnBalance1CalldataMem_size I q0 q1
      hlo0 hbound0 hbound1 hbound2
    have hptr := (amm4BurnBalance1FreePtr_bounds o0 o1 o2
      hlo0 hbound0 hbound1 hbound2).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (amm4ActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4BurnBalance1CalldataMem_read64 I q0 q1
          (o0 := o0) (o1 := o1) (o2 := o2)
          hlo0 hbound0 hbound1 hbound2))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd4513 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd4514 := RD.mload 0 fp aw rd4513 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4BurnBalance1CalldataWords o0 o1 o2).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            amm4BurnBalance1CalldataWords o0 o1 o2 from by
          simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4520 := evm_run rd4514 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd4520'⟩ := rd4520
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd4520'⟩

noncomputable def amm4BurnBalance1PostCallMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 o3 : ByteArray) : ByteArray :=
  o3.write 0 (amm4BurnBalance1CalldataMem I q0 q1 o0 o1 o2)
    (amm4BurnBalance1FreePtr o0 o1 o2).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat

theorem amm4BurnBalance1CallWords_same (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (amm4BurnBalance1CalldataWords o0 o1 o2).toNat
          (amm4BurnBalance1FreePtr o0 o1 o2).toNat 36)
        (amm4BurnBalance1FreePtr o0 o1 o2).toNat 32) =
      amm4BurnBalance1CalldataWords o0 o1 o2 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let n2 := (o2.size + 31) / 32
  let fp := amm4BurnBalance1FreePtr o0 o1 o2
  let aw := amm4BurnBalance1CalldataWords o0 o1 o2
  have hfp : fp.toNat = 128 + 32 * (n0 + n1 + n2) := by
    simpa only [fp, n0, n1, n2] using
      amm4BurnBalance1FreePtr_toNat o0 o1 o2
        hbound0 hbound1 hbound2
  have haw : aw.toNat = 6 + n0 + n1 + n2 := by
    simpa only [aw, n0, n1, n2] using
      amm4BurnBalance1CalldataWords_toNat o0 o1 o2
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

end Benchmarks.ActAmm4
