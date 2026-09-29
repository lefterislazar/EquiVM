import Benchmarks.ActAmm4.SwapTransfer1Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev amm4SwapBalance0FreePtr (o0 o1 : ByteArray) : UInt256 :=
  UInt256.add (amm4MintToken0FreePtr o0) (amm4MintReturndataRounded o1)

theorem amm4SwapBalance0FreePtr_toNat (o0 o1 : ByteArray)
    (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0FreePtr o0 o1).toNat =
      128 + 32 * ((o0.size + 31) / 32 + (o1.size + 31) / 32) := by
  have hfp0 := amm4MintToken0FreePtr_toNat o0 hbound0
  have hround := amm4MintReturndataRounded_toNat o1 hbound1
  have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
    Nat.div_le_self _ _
  have hfit : (amm4MintToken0FreePtr o0).toNat +
      (amm4MintReturndataRounded o1).toNat < UInt256.size := by
    rw [show (amm4MintToken0FreePtr o0).toNat =
      128 + 32 * ((o0.size + 31) / 32) from by
        simpa only [amm4MintToken0FreePtr] using hfp0,
      hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  change (amm4MintToken0FreePtr o0 + amm4MintReturndataRounded o1).toNat = _
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit,
    show (amm4MintToken0FreePtr o0).toNat =
      128 + 32 * ((o0.size + 31) / 32) from by
        simpa only [amm4MintToken0FreePtr] using hfp0,
    hround]
  omega

theorem amm4SwapTransfer1DecodeMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) :
    (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (amm4SwapBalance0FreePtr o0 o1) := by
  unfold amm4SwapTransfer1DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _

theorem amm4SwapX_balance0Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2816⟩
      [amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2873⟩
      [amm4MintToken0Word σ I, ⟨0⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 (cA, σ) k' C' := by
  have rd4264 := evm_run rd with [push0, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd4265⟩ := rd4264.sload (by native_decide) (by evm_ov)
  have rd4316 := evm_run rd4265 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken0Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd4316⟩

noncomputable def amm4SwapBalance0SelectorMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) : ByteArray :=
  amm4MintBalanceSelectorWord.toByteArray.write 0
    (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
    (amm4SwapBalance0FreePtr o0 o1).toNat 32

def amm4SwapBalance0SelectorWords (o0 o1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4SwapTransfer1CalldataWords o0).toNat
    (amm4SwapBalance0FreePtr o0 o1).toNat 32)

theorem amm4SwapX_balance0SelectorMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2873⟩
      [amm4MintToken0Word σ I, ⟨0⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2894⟩
      [amm4SwapBalance0FreePtr o0 o1, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, amm4MintToken0Word σ I, ⟨0⟩,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0SelectorMem I q0 q1 o0 o1)
      (amm4SwapBalance0SelectorWords o0 o1)
      o1 (cA, σ) k' C' := by
  let aw := amm4SwapTransfer1CalldataWords o0
  let fp := amm4SwapBalance0FreePtr o0 o1
  have hmem : 64 < (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).size := by
    have hsz := amm4SwapTransfer1DecodeMem_size_ge I q0 q1
      hlo0 hbound0 (lt_trans hbound1 (by norm_num [UInt256.size]))
    have hfp0 := (amm4MintToken0FreePtr_bounds o0 hlo0 hbound0).1
    have hfp0' : 160 ≤ (amm4MintToken0FreePtr o0).toNat := by
      simpa only [amm4MintToken0FreePtr] using hfp0
    omega
  have hawlo : 3 ≤ aw.toNat := by
    have hn : 1 ≤ (o0.size + 31) / 32 := by omega
    simpa only [aw, amm4SwapTransfer1CalldataWords_toNat o0 hlo0 hbound0]
      using (show 3 ≤ 7 + (o0.size + 31) / 32 by omega)
  have hawfit : aw.toNat * 32 < UInt256.size := by
    have hle : (o0.size + 31) / 32 ≤ o0.size + 31 :=
      Nat.div_le_self _ _
    rw [show aw.toNat = 7 + (o0.size + 31) / 32 from by
      simpa only [aw] using
        amm4SwapTransfer1CalldataWords_toNat o0 hlo0 hbound0]
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (amm4ActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using amm4SwapTransfer1DecodeMem_read64 I q0 q1 o0 o1)
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using amm4SwapTransfer1CalldataWords_mload64_same o0 hlo0 hbound0
  have rd4324 := evm_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd4325 := RD.mload 0 fp aw rd4324 (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4SwapTransfer1CalldataWords o0).toNat
          (⟨64⟩ : UInt256).toNat 32) = amm4SwapTransfer1CalldataWords o0 from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4336 := evm_run rd4325 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := amm4SwapBalance0SelectorWords o0 o1
  have rd4337 := RD.mstore
    (Cₘ awSel - Cₘ aw)
    (amm4SwapBalance0SelectorMem I q0 q1 o0 o1) awSel rd4336
    (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awSel, aw, fp, amm4SwapBalance0SelectorWords])
    (by unfold amm4SwapBalance0SelectorMem; rfl)
    (by simp [awSel, aw, fp, amm4SwapBalance0SelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4MintBalanceSelectorWord, fp, awSel] using rd4337⟩

noncomputable def amm4SwapBalance0CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (amm4SwapBalance0SelectorMem I q0 q1 o0 o1)
    (amm4SwapBalance0FreePtr o0 o1 + ⟨4⟩).toNat 32

def amm4SwapBalance0CalldataWords (o0 o1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (amm4SwapBalance0SelectorWords o0 o1).toNat
    (amm4SwapBalance0FreePtr o0 o1 + ⟨4⟩).toNat 32)

theorem amm4SwapBalance0CalldataWords_toNat (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0CalldataWords o0 o1).toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let fp := amm4SwapBalance0FreePtr o0 o1
  have hn0 : 1 ≤ n0 := by dsimp [n0]; omega
  have hn1 : 1 ≤ n1 := by dsimp [n1]; omega
  have hle0 : n0 ≤ o0.size + 31 := Nat.div_le_self _ _
  have hle1 : n1 ≤ o1.size + 31 := Nat.div_le_self _ _
  have hfp0 : (amm4MintToken0FreePtr o0).toNat = 128 + 32 * n0 := by
    simpa only [amm4MintToken0FreePtr, n0] using
      amm4MintToken0FreePtr_toNat o0 hbound0
  have hround : (amm4MintReturndataRounded o1).toNat = 32 * n1 := by
    simpa only [n1] using amm4MintReturndataRounded_toNat o1 hbound1
  have hfit : (amm4MintToken0FreePtr o0).toNat +
      (amm4MintReturndataRounded o1).toNat < UInt256.size := by
    rw [hfp0, hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hfp : fp.toNat = 128 + 32 * (n0 + n1) := by
    change (amm4MintToken0FreePtr o0 + amm4MintReturndataRounded o1).toNat = _
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit, hfp0, hround]
    omega
  have hfp4 : (fp + ⟨4⟩).toNat = 132 + 32 * (n0 + n1) := by
    rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      Nat.mod_eq_of_lt]
    · rw [hfp]
      omega
    · rw [hfp]
      have hcap : 132 + 32 * (2 ^ 138 + 31) +
        32 * (2 ^ 138 + 31) < UInt256.size := by
        norm_num [UInt256.size]
      omega
  have haw0 : (amm4SwapTransfer1CalldataWords o0).toNat = 7 + n0 := by
    simpa only [n0] using
      amm4SwapTransfer1CalldataWords_toNat o0 hlo0 hbound0
  have hMsel : MachineState.M (amm4SwapTransfer1CalldataWords o0).toNat
      fp.toNat 32 = max (7 + n0) (5 + n0 + n1) := by
    change max (amm4SwapTransfer1CalldataWords o0).toNat
      ((fp.toNat + 32 + 31) / 32) = _
    rw [haw0, hfp]
    omega
  have hawSel : (amm4SwapBalance0SelectorWords o0 o1).toNat =
      max (7 + n0) (5 + n0 + n1) := by
    unfold amm4SwapBalance0SelectorWords
    rw [hMsel, UInt256.toNat_ofNat_of_lt]
    have hcap : 7 + (2 ^ 138 + 31) + (2 ^ 138 + 31) <
        UInt256.size := by norm_num [UInt256.size]
    omega
  have hMarg : MachineState.M (amm4SwapBalance0SelectorWords o0 o1).toNat
      (fp + ⟨4⟩).toNat 32 = 6 + n0 + n1 := by
    change max (amm4SwapBalance0SelectorWords o0 o1).toNat
      (((fp + ⟨4⟩).toNat + 32 + 31) / 32) = _
    rw [hawSel, hfp4]
    omega
  unfold amm4SwapBalance0CalldataWords
  rw [hMarg, UInt256.toNat_ofNat_of_lt]
  have hcap : 6 + (2 ^ 138 + 31) + (2 ^ 138 + 31) <
      UInt256.size := by norm_num [UInt256.size]
  omega

theorem amm4SwapBalance0FreePtr_add4_toNat (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0FreePtr o0 o1 + ⟨4⟩).toNat =
      (amm4SwapBalance0FreePtr o0 o1).toNat + 4 := by
  have hfit := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).2.1
  change (amm4SwapBalance0FreePtr o0 o1).toNat + 32 <
    UInt256.size at hfit
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt (by omega)]

theorem amm4SwapBalance0SelectorMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) :
    (amm4SwapBalance0FreePtr o0 o1).toNat + 32 ≤
      (amm4SwapBalance0SelectorMem I q0 q1 o0 o1).size := by
  unfold amm4SwapBalance0SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4SwapBalance0SelectorMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0SelectorMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (amm4SwapBalance0FreePtr o0 o1) := by
  unfold amm4SwapBalance0SelectorMem
  have hptr := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).1
  change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by
      have hsz := amm4SwapTransfer1DecodeMem_size_ge I q0 q1
        hlo0 hbound0 (lt_trans hbound1 (by norm_num [UInt256.size]))
      have hfp0 := (amm4MintToken0FreePtr_bounds o0 hlo0 hbound0).1
      have hfp0' : 160 ≤ (amm4MintToken0FreePtr o0).toNat := by
        simpa only [amm4MintToken0FreePtr] using hfp0
      omega)
    (by omega)]
  exact amm4SwapTransfer1DecodeMem_read64 I q0 q1 o0 o1

theorem amm4SwapBalance0CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0FreePtr o0 o1).toNat + 36 ≤
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).size := by
  unfold amm4SwapBalance0CalldataMem
  rw [amm4SwapBalance0FreePtr_add4_toNat o0 o1 hlo0 hbound0 hbound1]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4SwapBalance0CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (amm4SwapBalance0FreePtr o0 o1) := by
  unfold amm4SwapBalance0CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      rw [amm4SwapBalance0FreePtr_add4_toNat o0 o1
        hlo0 hbound0 hbound1]
      have hsz := amm4SwapBalance0SelectorMem_size I q0 q1 o0 o1
      omega)
    (by
      rw [amm4SwapBalance0FreePtr_add4_toNat o0 o1
        hlo0 hbound0 hbound1]
      have hptr := (amm4MintFinalFreePtr_bounds o0 o1
        hlo0 hbound0 hbound1).1
      change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
      omega)]
  exact amm4SwapBalance0SelectorMem_read64 I q0 q1
    hlo0 hbound0 hbound1

theorem amm4SwapBalance0SelectorMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) :
    (amm4SwapBalance0SelectorMem I q0 q1 o0 o1).readWithPadding
      (amm4SwapBalance0FreePtr o0 o1).toNat 4 = balanceOfSelector := by
  unfold amm4SwapBalance0SelectorMem
  have h := toByteArray_write_read_window_no_gap
    amm4MintBalanceSelectorWord
    (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
    (amm4SwapBalance0FreePtr o0 o1).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : amm4MintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4SwapBalance0CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
      (amm4SwapBalance0FreePtr o0 o1).toNat 4 = balanceOfSelector := by
  unfold amm4SwapBalance0CalldataMem
  rw [write32_read_below_len _ _ _
    (amm4SwapBalance0FreePtr o0 o1).toNat 4
    (by rw [toByteArray_size])
    (by
      rw [amm4SwapBalance0FreePtr_add4_toNat o0 o1
        hlo0 hbound0 hbound1]
      have hsz := amm4SwapBalance0SelectorMem_size I q0 q1 o0 o1
      omega)
    (by rw [amm4SwapBalance0FreePtr_add4_toNat o0 o1
      hlo0 hbound0 hbound1])
    (by
      have hsz := amm4SwapBalance0SelectorMem_size I q0 q1 o0 o1
      omega)
    (by norm_num) (by norm_num)]
  exact amm4SwapBalance0SelectorMem_read4 I q0 q1 o0 o1

theorem amm4SwapBalance0CalldataMem_read32 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
      (amm4SwapBalance0FreePtr o0 o1 + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold amm4SwapBalance0CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [amm4SwapBalance0FreePtr_add4_toNat o0 o1 hlo0 hbound0 hbound1]
    have hsz := amm4SwapBalance0SelectorMem_size I q0 q1 o0 o1
    omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4SwapBalance0CalldataMem_read36 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
      (amm4SwapBalance0FreePtr o0 o1).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _
    (amm4SwapBalance0FreePtr o0 o1).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have hsz := amm4SwapBalance0CalldataMem_size I q0 q1
        hlo0 hbound0 hbound1
      omega)]
  rw [amm4SwapBalance0CalldataMem_read4 I q0 q1
    hlo0 hbound0 hbound1,
    ← amm4SwapBalance0FreePtr_add4_toNat o0 o1
      hlo0 hbound0 hbound1,
    amm4SwapBalance0CalldataMem_read32 I q0 q1
      hlo0 hbound0 hbound1]

theorem amm4SwapBalance0CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
        (amm4SwapBalance0FreePtr o0 o1).toNat 36) := by
  rw [amm4SwapBalance0CalldataMem_read36 I q0 q1 hlo0 hbound0 hbound1,
    ← amm4MintBalanceCalldataMem_read I]
  exact amm4MintBalanceEncode_eq I

theorem amm4SwapX_balance0ArgMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2894⟩
      [amm4SwapBalance0FreePtr o0 o1, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, amm4MintToken0Word σ I, ⟨0⟩,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0SelectorMem I q0 q1 o0 o1)
      (amm4SwapBalance0SelectorWords o0 o1)
      o1 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2906⟩
      [amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σ I, ⟨0⟩,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0CalldataWords o0 o1)
      o1 (cA, σ) k' C' := by
  let fp := amm4SwapBalance0FreePtr o0 o1
  have rd5370 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨2906⟩, swap2, swap1,
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
  let awArg := amm4SwapBalance0CalldataWords o0 o1
  have rd5389 := RD.mstore
    (Cₘ awArg - Cₘ (amm4SwapBalance0SelectorWords o0 o1))
    (amm4SwapBalance0CalldataMem I q0 q1 o0 o1) awArg
    rd5389pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awArg, fp, amm4SwapBalance0CalldataWords])
    (by unfold amm4SwapBalance0CalldataMem; rfl)
    (by simp [awArg, fp, amm4SwapBalance0CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4349 := evm_run rd5389 with [
    pop, pop, jump (by jump_dest), jumpdest,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp, u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, awArg, hend] using rd4349⟩

theorem amm4SwapX_balance0CallFrame
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2906⟩
      [amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σ I, ⟨0⟩,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0CalldataWords o0 o1)
      o1 (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2918⟩
      [gasWord, amm4MintToken0Word σ I, amm4SwapBalance0FreePtr o0 o1,
        ⟨36⟩, amm4SwapBalance0FreePtr o0 o1, ⟨32⟩,
        amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σ I, ⟨0⟩,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0CalldataWords o0 o1)
      o1 (cA, σ) k' C' := by
  let aw := amm4SwapBalance0CalldataWords o0 o1
  let fp := amm4SwapBalance0FreePtr o0 o1
  have haw : aw.toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 := by
    simpa only [aw] using amm4SwapBalance0CalldataWords_toNat o0 o1
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
  have hmem : 64 < (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).size := by
    have hsz := amm4SwapBalance0CalldataMem_size I q0 q1
      hlo0 hbound0 hbound1
    have hptr := (amm4MintFinalFreePtr_bounds o0 o1
      hlo0 hbound0 hbound1).1
    change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (amm4SwapBalance0CalldataMem I q0 q1 o0 o1).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4SwapBalance0CalldataMem I q0 q1 o0 o1).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (amm4ActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4SwapBalance0CalldataMem_read64 I q0 q1
          (o0 := o0) (o1 := o1) hlo0 hbound0 hbound1))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd4354 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd4355 := RD.mload 0 fp aw rd4354 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4SwapBalance0CalldataWords o0 o1).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            amm4SwapBalance0CalldataWords o0 o1 from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4361 := evm_run rd4355 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd4361'⟩ := rd4361
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd4361'⟩

noncomputable def amm4SwapBalance0PostCallMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  o2.write 0 (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
    (amm4SwapBalance0FreePtr o0 o1).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat

theorem amm4SwapBalance0CallWords_same (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (amm4SwapBalance0CalldataWords o0 o1).toNat
          (amm4SwapBalance0FreePtr o0 o1).toNat 36)
        (amm4SwapBalance0FreePtr o0 o1).toNat 32) =
      amm4SwapBalance0CalldataWords o0 o1 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let fp := amm4SwapBalance0FreePtr o0 o1
  let aw := amm4SwapBalance0CalldataWords o0 o1
  have hfp : fp.toNat = 128 + 32 * (n0 + n1) := by
    simpa only [fp, n0, n1] using
      amm4SwapBalance0FreePtr_toNat o0 o1 hbound0 hbound1
  have haw : aw.toNat = 6 + n0 + n1 := by
    simpa only [aw, n0, n1] using
      amm4SwapBalance0CalldataWords_toNat o0 o1
        hlo0 hbound0 hlo1 hbound1
  have hM : MachineState.M
      (MachineState.M aw.toNat fp.toNat 36)
      fp.toNat 32 = aw.toNat := by
    change max (max aw.toNat ((fp.toNat + 36 + 31) / 32))
      ((fp.toNat + 32 + 31) / 32) = _
    rw [hfp, haw]
    omega
  simpa only [fp, aw, hM] using (u256_ofNat_toNat aw)

end Benchmarks.ActAmm4
