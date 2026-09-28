import Benchmarks.ActAmm.BurnTransfer1Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev ammBurnBalance0FreePtr (o0 o1 : ByteArray) : UInt256 :=
  UInt256.add (ammMintToken0FreePtr o0) (ammMintReturndataRounded o1)

theorem ammBurnBalance0FreePtr_toNat (o0 o1 : ByteArray)
    (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0FreePtr o0 o1).toNat =
      128 + 32 * ((o0.size + 31) / 32 + (o1.size + 31) / 32) := by
  have hfp0 := ammMintToken0FreePtr_toNat o0 hbound0
  have hround := ammMintReturndataRounded_toNat o1 hbound1
  have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
    Nat.div_le_self _ _
  have hfit : (ammMintToken0FreePtr o0).toNat +
      (ammMintReturndataRounded o1).toNat < UInt256.size := by
    rw [show (ammMintToken0FreePtr o0).toNat =
      128 + 32 * ((o0.size + 31) / 32) from by
        simpa only [ammMintToken0FreePtr] using hfp0,
      hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  change (ammMintToken0FreePtr o0 + ammMintReturndataRounded o1).toNat = _
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit,
    show (ammMintToken0FreePtr o0).toNat =
      128 + 32 * ((o0.size + 31) / 32) from by
        simpa only [ammMintToken0FreePtr] using hfp0,
    hround]
  omega

theorem ammBurnToken1DecodeMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) :
    (ammBurnToken1DecodeMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (ammBurnBalance0FreePtr o0 o1) := by
  unfold ammBurnToken1DecodeMem
  rw [toByteArray_write_read_window_no_gap _ _ 64 0 32
    (by omega) (by omega) (by norm_num)]
  exact toByteArray_extract_all _

theorem ammBurnX_balance0Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5073⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1DecodeMem I q0 q1 o0 o1)
      (ammBurnToken1CalldataWords o0) o1 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5129⟩
      [ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1DecodeMem I q0 q1 o0 o1)
      (ammBurnToken1CalldataWords o0) o1 (cA, σ) k' C' := by
  have rd5077 := evm_run rd with [push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd5078⟩ := rd5077.sload (by native_decide) (by evm_ov)
  have rd5129 := evm_run rd5078 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken0Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd5129⟩

noncomputable def ammBurnBalance0SelectorMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) : ByteArray :=
  ammMintBalanceSelectorWord.toByteArray.write 0
    (ammBurnToken1DecodeMem I q0 q1 o0 o1)
    (ammBurnBalance0FreePtr o0 o1).toNat 32

def ammBurnBalance0SelectorWords (o0 o1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammBurnToken1CalldataWords o0).toNat
    (ammBurnBalance0FreePtr o0 o1).toNat 32)

theorem ammBurnX_balance0SelectorMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5129⟩
      [ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1DecodeMem I q0 q1 o0 o1)
      (ammBurnToken1CalldataWords o0) o1 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5150⟩
      [ammBurnBalance0FreePtr o0 o1, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0SelectorMem I q0 q1 o0 o1)
      (ammBurnBalance0SelectorWords o0 o1)
      o1 (cA, σ) k' C' := by
  let aw := ammBurnToken1CalldataWords o0
  let fp := ammBurnBalance0FreePtr o0 o1
  have hmem : 64 < (ammBurnToken1DecodeMem I q0 q1 o0 o1).size := by
    have hsz := ammBurnToken1DecodeMem_size_ge I q0 q1
      hlo0 hbound0 (lt_trans hbound1 (by norm_num [UInt256.size]))
    have hfp0 := (ammMintToken0FreePtr_bounds o0 hlo0 hbound0).1
    have hfp0' : 160 ≤ (ammMintToken0FreePtr o0).toNat := by
      simpa only [ammMintToken0FreePtr] using hfp0
    omega
  have hawlo : 3 ≤ aw.toNat := by
    have hn : 1 ≤ (o0.size + 31) / 32 := by omega
    simpa only [aw, ammBurnToken1CalldataWords_toNat o0 hlo0 hbound0]
      using (show 3 ≤ 7 + (o0.size + 31) / 32 by omega)
  have hawfit : aw.toNat * 32 < UInt256.size := by
    have hle : (o0.size + 31) / 32 ≤ o0.size + 31 :=
      Nat.div_le_self _ _
    rw [show aw.toNat = 7 + (o0.size + 31) / 32 from by
      simpa only [aw] using
        ammBurnToken1CalldataWords_toNat o0 hlo0 hbound0]
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammBurnToken1DecodeMem I q0 q1 o0 o1).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnToken1DecodeMem I q0 q1 o0 o1).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using ammBurnToken1DecodeMem_read64 I q0 q1 o0 o1)
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      using ammBurnToken1CalldataWords_mload64_same o0 hlo0 hbound0
  have rd5137 := evm_run rd with [
    push4 ⟨1889567281⟩, address, push1 ⟨64⟩]
  have rd5138 := RD.mload 0 fp aw rd5137 (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammBurnToken1CalldataWords o0).toNat
          (⟨64⟩ : UInt256).toNat 32) = ammBurnToken1CalldataWords o0 from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5149 := evm_run rd5138 with [
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := ammBurnBalance0SelectorWords o0 o1
  have rd5150 := RD.mstore
    (Cₘ awSel - Cₘ aw)
    (ammBurnBalance0SelectorMem I q0 q1 o0 o1) awSel rd5149
    (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awSel, aw, fp, ammBurnBalance0SelectorWords])
    (by unfold ammBurnBalance0SelectorMem; rfl)
    (by simp [awSel, aw, fp, ammBurnBalance0SelectorWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [ammMintBalanceSelectorWord, fp, awSel] using rd5150⟩

noncomputable def ammBurnBalance0CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner).toByteArray.write 0
    (ammBurnBalance0SelectorMem I q0 q1 o0 o1)
    (ammBurnBalance0FreePtr o0 o1 + ⟨4⟩).toNat 32

def ammBurnBalance0CalldataWords (o0 o1 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M
    (ammBurnBalance0SelectorWords o0 o1).toNat
    (ammBurnBalance0FreePtr o0 o1 + ⟨4⟩).toNat 32)

theorem ammBurnBalance0CalldataWords_toNat (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0CalldataWords o0 o1).toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let fp := ammBurnBalance0FreePtr o0 o1
  have hn0 : 1 ≤ n0 := by dsimp [n0]; omega
  have hn1 : 1 ≤ n1 := by dsimp [n1]; omega
  have hle0 : n0 ≤ o0.size + 31 := Nat.div_le_self _ _
  have hle1 : n1 ≤ o1.size + 31 := Nat.div_le_self _ _
  have hfp0 : (ammMintToken0FreePtr o0).toNat = 128 + 32 * n0 := by
    simpa only [ammMintToken0FreePtr, n0] using
      ammMintToken0FreePtr_toNat o0 hbound0
  have hround : (ammMintReturndataRounded o1).toNat = 32 * n1 := by
    simpa only [n1] using ammMintReturndataRounded_toNat o1 hbound1
  have hfit : (ammMintToken0FreePtr o0).toNat +
      (ammMintReturndataRounded o1).toNat < UInt256.size := by
    rw [hfp0, hround]
    have hcap : 128 + 32 * (2 ^ 138 + 31) +
      32 * (2 ^ 138 + 31) < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hfp : fp.toNat = 128 + 32 * (n0 + n1) := by
    change (ammMintToken0FreePtr o0 + ammMintReturndataRounded o1).toNat = _
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
  have haw0 : (ammBurnToken1CalldataWords o0).toNat = 7 + n0 := by
    simpa only [n0] using
      ammBurnToken1CalldataWords_toNat o0 hlo0 hbound0
  have hMsel : MachineState.M (ammBurnToken1CalldataWords o0).toNat
      fp.toNat 32 = max (7 + n0) (5 + n0 + n1) := by
    change max (ammBurnToken1CalldataWords o0).toNat
      ((fp.toNat + 32 + 31) / 32) = _
    rw [haw0, hfp]
    omega
  have hawSel : (ammBurnBalance0SelectorWords o0 o1).toNat =
      max (7 + n0) (5 + n0 + n1) := by
    unfold ammBurnBalance0SelectorWords
    rw [hMsel, UInt256.toNat_ofNat_of_lt]
    have hcap : 7 + (2 ^ 138 + 31) + (2 ^ 138 + 31) <
        UInt256.size := by norm_num [UInt256.size]
    omega
  have hMarg : MachineState.M (ammBurnBalance0SelectorWords o0 o1).toNat
      (fp + ⟨4⟩).toNat 32 = 6 + n0 + n1 := by
    change max (ammBurnBalance0SelectorWords o0 o1).toNat
      (((fp + ⟨4⟩).toNat + 32 + 31) / 32) = _
    rw [hawSel, hfp4]
    omega
  unfold ammBurnBalance0CalldataWords
  rw [hMarg, UInt256.toNat_ofNat_of_lt]
  have hcap : 6 + (2 ^ 138 + 31) + (2 ^ 138 + 31) <
      UInt256.size := by norm_num [UInt256.size]
  omega

theorem ammBurnBalance0FreePtr_add4_toNat (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0FreePtr o0 o1 + ⟨4⟩).toNat =
      (ammBurnBalance0FreePtr o0 o1).toNat + 4 := by
  have hfit := (ammMintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).2.1
  change (ammBurnBalance0FreePtr o0 o1).toNat + 32 <
    UInt256.size at hfit
  rw [uadd_toNat, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    Nat.mod_eq_of_lt (by omega)]

theorem ammBurnBalance0SelectorMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) :
    (ammBurnBalance0FreePtr o0 o1).toNat + 32 ≤
      (ammBurnBalance0SelectorMem I q0 q1 o0 o1).size := by
  unfold ammBurnBalance0SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnBalance0SelectorMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0SelectorMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (ammBurnBalance0FreePtr o0 o1) := by
  unfold ammBurnBalance0SelectorMem
  have hptr := (ammMintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).1
  change 160 ≤ (ammBurnBalance0FreePtr o0 o1).toNat at hptr
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by
      have hsz := ammBurnToken1DecodeMem_size_ge I q0 q1
        hlo0 hbound0 (lt_trans hbound1 (by norm_num [UInt256.size]))
      have hfp0 := (ammMintToken0FreePtr_bounds o0 hlo0 hbound0).1
      have hfp0' : 160 ≤ (ammMintToken0FreePtr o0).toNat := by
        simpa only [ammMintToken0FreePtr] using hfp0
      omega)
    (by omega)]
  exact ammBurnToken1DecodeMem_read64 I q0 q1 o0 o1

theorem ammBurnBalance0CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0FreePtr o0 o1).toNat + 36 ≤
      (ammBurnBalance0CalldataMem I q0 q1 o0 o1).size := by
  unfold ammBurnBalance0CalldataMem
  rw [ammBurnBalance0FreePtr_add4_toNat o0 o1 hlo0 hbound0 hbound1]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnBalance0CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0CalldataMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (ammBurnBalance0FreePtr o0 o1) := by
  unfold ammBurnBalance0CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      rw [ammBurnBalance0FreePtr_add4_toNat o0 o1
        hlo0 hbound0 hbound1]
      have hsz := ammBurnBalance0SelectorMem_size I q0 q1 o0 o1
      omega)
    (by
      rw [ammBurnBalance0FreePtr_add4_toNat o0 o1
        hlo0 hbound0 hbound1]
      have hptr := (ammMintFinalFreePtr_bounds o0 o1
        hlo0 hbound0 hbound1).1
      change 160 ≤ (ammBurnBalance0FreePtr o0 o1).toNat at hptr
      omega)]
  exact ammBurnBalance0SelectorMem_read64 I q0 q1
    hlo0 hbound0 hbound1

theorem ammBurnBalance0SelectorMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) :
    (ammBurnBalance0SelectorMem I q0 q1 o0 o1).readWithPadding
      (ammBurnBalance0FreePtr o0 o1).toNat 4 = balanceOfSelector := by
  unfold ammBurnBalance0SelectorMem
  have h := toByteArray_write_read_window_no_gap
    ammMintBalanceSelectorWord
    (ammBurnToken1DecodeMem I q0 q1 o0 o1)
    (ammBurnBalance0FreePtr o0 o1).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : ammMintBalanceSelectorWord.toByteArray.extract 0 4 =
      balanceOfSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammBurnBalance0CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
      (ammBurnBalance0FreePtr o0 o1).toNat 4 = balanceOfSelector := by
  unfold ammBurnBalance0CalldataMem
  rw [write32_read_below_len _ _ _
    (ammBurnBalance0FreePtr o0 o1).toNat 4
    (by rw [toByteArray_size])
    (by
      rw [ammBurnBalance0FreePtr_add4_toNat o0 o1
        hlo0 hbound0 hbound1]
      have hsz := ammBurnBalance0SelectorMem_size I q0 q1 o0 o1
      omega)
    (by rw [ammBurnBalance0FreePtr_add4_toNat o0 o1
      hlo0 hbound0 hbound1])
    (by
      have hsz := ammBurnBalance0SelectorMem_size I q0 q1 o0 o1
      omega)
    (by norm_num) (by norm_num)]
  exact ammBurnBalance0SelectorMem_read4 I q0 q1 o0 o1

theorem ammBurnBalance0CalldataMem_read32 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
      (ammBurnBalance0FreePtr o0 o1 + ⟨4⟩).toNat 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  unfold ammBurnBalance0CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
    rw [ammBurnBalance0FreePtr_add4_toNat o0 o1 hlo0 hbound0 hbound1]
    have hsz := ammBurnBalance0SelectorMem_size I q0 q1 o0 o1
    omega)]
  rw [show (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).extract 0 32 =
      UInt256.toByteArray (UInt256.ofNat I.codeOwner) by
    rw [show 32 = (UInt256.toByteArray (UInt256.ofNat I.codeOwner)).size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammBurnBalance0CalldataMem_read36 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    (ammBurnBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
      (ammBurnBalance0FreePtr o0 o1).toNat 36 =
      balanceOfSelector ++ UInt256.toByteArray (UInt256.ofNat I.codeOwner) := by
  rw [byteArray_readWithPadding_split _
    (ammBurnBalance0FreePtr o0 o1).toNat 4 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by
      have hsz := ammBurnBalance0CalldataMem_size I q0 q1
        hlo0 hbound0 hbound1
      omega)]
  rw [ammBurnBalance0CalldataMem_read4 I q0 q1
    hlo0 hbound0 hbound1,
    ← ammBurnBalance0FreePtr_add4_toNat o0 o1
      hlo0 hbound0 hbound1,
    ammBurnBalance0CalldataMem_read32 I q0 q1
      hlo0 hbound0 hbound1]

theorem ammBurnBalance0CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((ammBurnBalance0CalldataMem I q0 q1 o0 o1).readWithPadding
        (ammBurnBalance0FreePtr o0 o1).toNat 36) := by
  rw [ammBurnBalance0CalldataMem_read36 I q0 q1 hlo0 hbound0 hbound1,
    ← ammMintBalanceCalldataMem_read I]
  exact ammMintBalanceEncode_eq I

theorem ammBurnX_balance0ArgMem
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5150⟩
      [ammBurnBalance0FreePtr o0 o1, UInt256.ofNat I.codeOwner,
        ⟨1889567281⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0SelectorMem I q0 q1 o0 o1)
      (ammBurnBalance0SelectorWords o0 o1)
      o1 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5162⟩
      [ammBurnBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0CalldataMem I q0 q1 o0 o1)
      (ammBurnBalance0CalldataWords o0 o1)
      o1 (cA, σ) k' C' := by
  let fp := ammBurnBalance0FreePtr o0 o1
  have rd6408 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨5162⟩, swap2, swap1,
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
  let awArg := ammBurnBalance0CalldataWords o0 o1
  have rd6427 := RD.mstore
    (Cₘ awArg - Cₘ (ammBurnBalance0SelectorWords o0 o1))
    (ammBurnBalance0CalldataMem I q0 q1 o0 o1) awArg
    rd6427pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awArg, fp, ammBurnBalance0CalldataWords])
    (by unfold ammBurnBalance0CalldataMem; rfl)
    (by simp [awArg, fp, ammBurnBalance0CalldataWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5162 := evm_run rd6427 with [
    pop, pop, jump (by jump_dest), jumpdest,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp, u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, awArg, hend] using rd5162⟩

theorem ammBurnX_balance0CallFrame
    {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5162⟩
      [ammBurnBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0CalldataMem I q0 q1 o0 o1)
      (ammBurnBalance0CalldataWords o0 o1)
      o1 (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5174⟩
      [gasWord, ammMintToken0Word σ I, ammBurnBalance0FreePtr o0 o1,
        ⟨36⟩, ammBurnBalance0FreePtr o0 o1, ⟨32⟩,
        ammBurnBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance0CalldataMem I q0 q1 o0 o1)
      (ammBurnBalance0CalldataWords o0 o1)
      o1 (cA, σ) k' C' := by
  let aw := ammBurnBalance0CalldataWords o0 o1
  let fp := ammBurnBalance0FreePtr o0 o1
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
  have hmem : 64 < (ammBurnBalance0CalldataMem I q0 q1 o0 o1).size := by
    have hsz := ammBurnBalance0CalldataMem_size I q0 q1
      hlo0 hbound0 hbound1
    have hptr := (ammMintFinalFreePtr_bounds o0 o1
      hlo0 hbound0 hbound1).1
    change 160 ≤ (ammBurnBalance0FreePtr o0 o1).toNat at hptr
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammBurnBalance0CalldataMem I q0 q1 o0 o1).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnBalance0CalldataMem I q0 q1 o0 o1).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammBurnBalance0CalldataMem_read64 I q0 q1
          (o0 := o0) (o1 := o1) hlo0 hbound0 hbound1))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd5167 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd5168 := RD.mload 0 fp aw rd5167 (by native_decide)
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
  have rd5174 := evm_run rd5168 with [dup1, dup4, sub, dup2, dup7, gas]
  obtain ⟨gasWord, rd5174'⟩ := rd5174
  have hsub : UInt256.sub (fp + ⟨36⟩) fp = ⟨36⟩ := by
    simpa only [fp, u256_ofNat_toNat] using
      (usub_uadd_lit_cancel_mod (base := fp.toNat) (n := 36)
        fp.val.isLt (by decide))
  exact ⟨gasWord, _, _, by simpa only [fp, aw, hsub] using rd5174'⟩

noncomputable def ammBurnBalance0PostCallMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  o2.write 0 (ammBurnBalance0CalldataMem I q0 q1 o0 o1)
    (ammBurnBalance0FreePtr o0 o1).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat

theorem ammBurnBalance0CallWords_same (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138) :
    UInt256.ofNat
      (MachineState.M
        (MachineState.M (ammBurnBalance0CalldataWords o0 o1).toNat
          (ammBurnBalance0FreePtr o0 o1).toNat 36)
        (ammBurnBalance0FreePtr o0 o1).toNat 32) =
      ammBurnBalance0CalldataWords o0 o1 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let fp := ammBurnBalance0FreePtr o0 o1
  let aw := ammBurnBalance0CalldataWords o0 o1
  have hfp : fp.toNat = 128 + 32 * (n0 + n1) := by
    simpa only [fp, n0, n1] using
      ammBurnBalance0FreePtr_toNat o0 o1 hbound0 hbound1
  have haw : aw.toNat = 6 + n0 + n1 := by
    simpa only [aw, n0, n1] using
      ammBurnBalance0CalldataWords_toNat o0 o1
        hlo0 hbound0 hlo1 hbound1
  have hM : MachineState.M
      (MachineState.M aw.toNat fp.toNat 36)
      fp.toNat 32 = aw.toNat := by
    change max (max aw.toNat ((fp.toNat + 36 + 31) / 32))
      ((fp.toNat + 32 + 31) / 32) = _
    rw [hfp, haw]
    omega
  simpa only [fp, aw, hM] using (u256_ofNat_toNat aw)

end Benchmarks.ActAmm
