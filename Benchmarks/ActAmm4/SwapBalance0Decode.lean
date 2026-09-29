import Benchmarks.ActAmm4.SwapBalance0Call

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapBalance0PostCallMem_size_ge (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (amm4SwapBalance0FreePtr o0 o1).toNat + 36 ≤
      (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2).size := by
  unfold amm4SwapBalance0PostCallMem
  have hbase := amm4SwapBalance0CalldataMem_size I q0 q1
    hlo0 hbound0 hbound1
  by_cases hshort : o2.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat =
        o2.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o2.size)
        (by decide) hshort hsize2
    rw [hlen]
    by_cases hzero : o2.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen o2 (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
        (amm4SwapBalance0FreePtr o0 o1).toNat o2.size hzero le_rfl
        (by omega), ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ o2.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
        (by decide) hlong hsize2
    rw [hlen]
    rw [write_eq_gen o2 (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0FreePtr o0 o1).toNat 32
      (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem amm4SwapBalance0PostCallMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2).readWithPadding
      64 32 = UInt256.toByteArray (amm4SwapBalance0FreePtr o0 o1) := by
  unfold amm4SwapBalance0PostCallMem
  have hbase := amm4SwapBalance0CalldataMem_size I q0 q1
    hlo0 hbound0 hbound1
  have hptr := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).1
  change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
  by_cases hshort : o2.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat =
        o2.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o2.size)
        (by decide) hshort hsize2
    rw [hlen]
    by_cases hzero : o2.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact amm4SwapBalance0CalldataMem_read64 I q0 q1
        hlo0 hbound0 hbound1
    · rw [write_read_below_gen o2
        (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
        (amm4SwapBalance0FreePtr o0 o1).toNat o2.size 64 hzero le_rfl
        (by omega) (by omega)]
      exact amm4SwapBalance0CalldataMem_read64 I q0 q1
        hlo0 hbound0 hbound1
  · have hlong : 32 ≤ o2.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
        (by decide) hlong hsize2
    rw [hlen]
    rw [write32_read_below o2
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0FreePtr o0 o1).toNat 64 hlong
      (by omega) (by omega)]
    exact amm4SwapBalance0CalldataMem_read64 I q0 q1
      hlo0 hbound0 hbound1

theorem amm4SwapBalance0PostCallMem_readPtr (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hsize2 : o2.size < UInt256.size) :
    (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2).readWithPadding
      (amm4SwapBalance0FreePtr o0 o1).toNat 32 = o2.extract 0 32 := by
  unfold amm4SwapBalance0PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o2.size)).toNat =
      32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o2.size)
      (by decide) hlo2 hsize2
  rw [hlen]
  exact write32_read_back o2 (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
    (amm4SwapBalance0FreePtr o0 o1).toNat hlo2 (by
      have h := amm4SwapBalance0CalldataMem_size I q0 q1
        hlo0 hbound0 hbound1
      omega)

noncomputable def amm4SwapBalance0DecodeMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 : ByteArray) : ByteArray :=
  (UInt256.add (amm4SwapBalance0FreePtr o0 o1)
    (amm4MintReturndataRounded o2)).toByteArray.write 0
    (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2) 64 32

theorem amm4SwapBalance0DecodeMem_size_ge (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size) :
    (amm4SwapBalance0FreePtr o0 o1).toNat + 36 ≤
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2).size := by
  unfold amm4SwapBalance0DecodeMem
  let base := amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2
  have hbase : (amm4SwapBalance0FreePtr o0 o1).toNat + 36 ≤
      base.size :=
    amm4SwapBalance0PostCallMem_size_ge I q0 q1
      hlo0 hbound0 hbound1 hsize2
  have hptr := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).1
  change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
  have hsz : ((UInt256.add (amm4SwapBalance0FreePtr o0 o1)
      (amm4MintReturndataRounded o2)).toByteArray.write 0 base 64 32).size =
      base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem amm4SwapBalance0DecodeMem_readPtr (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hsize2 : o2.size < UInt256.size) :
    (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2).readWithPadding
      (amm4SwapBalance0FreePtr o0 o1).toNat 32 = o2.extract 0 32 := by
  unfold amm4SwapBalance0DecodeMem
  have hbase := amm4SwapBalance0PostCallMem_size_ge I q0 q1
    hlo0 hbound0 hbound1 hsize2
  have hptr := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).1
  change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
  rw [write32_read_above _ _ 64 (amm4SwapBalance0FreePtr o0 o1).toNat
    (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
  exact amm4SwapBalance0PostCallMem_readPtr I q0 q1
    hlo0 hbound0 hbound1 hlo2 hsize2

theorem amm4SwapX_balance0ToDecoder {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hsize2 : o2.size < UInt256.size)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2938⟩
      [⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5415⟩
      [amm4SwapBalance0FreePtr o0 o1,
        UInt256.add (amm4SwapBalance0FreePtr o0 o1)
          (UInt256.ofNat o2.size),
        ⟨2969⟩, ⟨0⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k' C' := by
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
  have hmem : 64 <
      (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2).size := by
    have hsz := amm4SwapBalance0PostCallMem_size_ge I q0 q1
      hlo0 hbound0 hbound1 hsize2
    have hptr := (amm4MintFinalFreePtr_bounds o0 o1
      hlo0 hbound0 hbound1).1
    change 160 ≤ (amm4SwapBalance0FreePtr o0 o1).toNat at hptr
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (amm4ActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (amm4SwapBalance0PostCallMem_read64 I q0 q1
          (o0 := o0) (o1 := o1) (o2 := o2)
          hlo0 hbound0 hbound1 hsize2))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd4383 := evm_run rd with [push1 ⟨64⟩]
  have rd4384 := RD.mload 0 fp aw rd4383 (by native_decide)
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
  have rd4398 := evm_run rd4384 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd4399 := RD.mstore 0
    (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2) aw rd4398
    (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4SwapBalance0CalldataWords o0 o1).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            amm4SwapBalance0CalldataWords o0 o1 from by
        simpa only [aw] using hsame]
      simp only [aw]
      omega)
    (by unfold amm4SwapBalance0DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5415 := evm_run rd4399 with [
    pop, dup2, add, swap1, push2 ⟨2969⟩, swap2, swap1,
    push2 ⟨5415⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, amm4MintReturndataRounded]
    using rd5415⟩

theorem amm4SwapBalance0LenCheckShort (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hshort2 : o2.size < 32) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (amm4SwapBalance0FreePtr o0 o1)
          (UInt256.ofNat o2.size))
        (amm4SwapBalance0FreePtr o0 o1)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).2.1
  change (amm4SwapBalance0FreePtr o0 o1).toNat + 32 <
    UInt256.size at hptr
  have hcheck := solcReturnStaticLenCheckShort
    (base := (amm4SwapBalance0FreePtr o0 o1).toNat)
    (len := o2.size) (words := 1)
    (by simpa using hshort2)
    (amm4SwapBalance0FreePtr o0 o1).val.isLt
    (by omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4SwapBalance0LenCheckOk (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (amm4SwapBalance0FreePtr o0 o1)
          (UInt256.ofNat o2.size))
        (amm4SwapBalance0FreePtr o0 o1)) ⟨32⟩ = ⟨0⟩ := by
  have hptr := (amm4MintFinalFreePtr_bounds o0 o1
    hlo0 hbound0 hbound1).2.2
  change (amm4SwapBalance0FreePtr o0 o1).toNat < 2 ^ 140 at hptr
  have hcheck := solcReturnStaticLenCheckOk
    (base := (amm4SwapBalance0FreePtr o0 o1).toNat)
    (len := o2.size) (words := 1)
    (by simpa using hlo2)
    (by omega : o2.size < 2 ^ 255)
    (amm4SwapBalance0FreePtr o0 o1).val.isLt
    (by
      have hcap : 2 ^ 140 + 2 ^ 138 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem amm4SwapX_balance0DecodeShortReverts
    {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hshort2 : o2.size < 32)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5415⟩
      [amm4SwapBalance0FreePtr o0 o1,
        UInt256.add (amm4SwapBalance0FreePtr o0 o1)
          (UInt256.ofNat o2.size),
        ⟨2969⟩, ⟨0⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := amm4SwapBalance0LenCheckShort o0 o1 o2
    hlo0 hbound0 hbound1 hshort2
  have rd5424 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd4583 := evm_run rd5424 with [
    push2 ⟨5436⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨5435⟩, push2 ⟨4583⟩, jump (by jump_dest)]
  exact evm_run rd4583 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem amm4SwapBalance0CalldataWords_ptr_haw (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138) :
    ¬ amm4SwapBalance0FreePtr o0 o1 ≥
      amm4SwapBalance0CalldataWords o0 o1 * ⟨32⟩ := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  have hptr : (amm4SwapBalance0FreePtr o0 o1).toNat =
      128 + 32 * (n0 + n1) := by
    simpa only [n0, n1] using
      amm4SwapBalance0FreePtr_toNat o0 o1 hbound0 hbound1
  have haw : (amm4SwapBalance0CalldataWords o0 o1).toNat =
      6 + n0 + n1 := by
    simpa only [n0, n1] using
      amm4SwapBalance0CalldataWords_toNat o0 o1
        hlo0 hbound0 hlo1 hbound1
  have hmul : (amm4SwapBalance0CalldataWords o0 o1).toNat * 32 <
      UInt256.size := by
    have hle0 : n0 ≤ o0.size + 31 := Nat.div_le_self _ _
    have hle1 : n1 ≤ o1.size + 31 := Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 <
        UInt256.size := by norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4SwapBalance0CalldataWords o0 o1 * ⟨32⟩).toNat ≤
      (amm4SwapBalance0FreePtr o0 o1).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem amm4SwapBalance0CalldataWords_mloadPtr_same (o0 o1 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (amm4SwapBalance0CalldataWords o0 o1).toNat
      (amm4SwapBalance0FreePtr o0 o1).toNat 32) =
      amm4SwapBalance0CalldataWords o0 o1 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  have hptr : (amm4SwapBalance0FreePtr o0 o1).toNat =
      128 + 32 * (n0 + n1) := by
    simpa only [n0, n1] using
      amm4SwapBalance0FreePtr_toNat o0 o1 hbound0 hbound1
  have haw : (amm4SwapBalance0CalldataWords o0 o1).toNat =
      6 + n0 + n1 := by
    simpa only [n0, n1] using
      amm4SwapBalance0CalldataWords_toNat o0 o1
        hlo0 hbound0 hlo1 hbound1
  have hM : MachineState.M (amm4SwapBalance0CalldataWords o0 o1).toNat
      (amm4SwapBalance0FreePtr o0 o1).toNat 32 =
      (amm4SwapBalance0CalldataWords o0 o1).toNat := by
    change max (amm4SwapBalance0CalldataWords o0 o1).toNat
      (((amm4SwapBalance0FreePtr o0 o1).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4SwapX_balance0DecodeOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {o0 o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5415⟩
      [amm4SwapBalance0FreePtr o0 o1,
        UInt256.add (amm4SwapBalance0FreePtr o0 o1)
          (UInt256.ofNat o2.size),
        ⟨2969⟩, ⟨0⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2969⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        ⟨0⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k' C' := by
  let aw := amm4SwapBalance0CalldataWords o0 o1
  let fp := amm4SwapBalance0FreePtr o0 o1
  let v2 : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (o2.extract 0 32))
  have hcheck := amm4SwapBalance0LenCheckOk o0 o1 o2
    hlo0 hbound0 hbound1 hlo2 hbound2
  have rd5436 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨5436⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd5395 := evm_run rd5436 with [
    jumpdest, push0, push2 ⟨5449⟩, dup5, dup3, dup6, add,
    push2 ⟨5395⟩, jump (by jump_dest)]
  have hmem : fp.toNat <
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2).size := by
    have hsz := amm4SwapBalance0DecodeMem_size_ge I q0 q1
      hlo0 hbound0 hbound1
      (by exact lt_trans hbound2 (by norm_num [UInt256.size]))
    dsimp [fp]
    omega
  have hval :
      (if fp.toNat ≥ (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2).readWithPadding
           fp.toNat 32))) = v2 := by
    have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
      simpa only [fp, aw] using
        amm4SwapBalance0CalldataWords_ptr_haw o0 o1
          hlo0 hbound0 hlo1 hbound1
    rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
      amm4SwapBalance0DecodeMem_readPtr I q0 q1
        hlo0 hbound0 hbound1 hlo2
        (by exact lt_trans hbound2 (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      amm4SwapBalance0CalldataWords_mloadPtr_same o0 o1
        hlo0 hbound0 hlo1 hbound1
  have rd5398 := evm_run rd5395 with [jumpdest, push0, dup2]
  have hzero : amm4SwapBalance0FreePtr o0 o1 + ⟨0⟩ =
      amm4SwapBalance0FreePtr o0 o1 := by
    rw [u256_add_comm, u256_zero_add]
  have rd5398' := rd5398
  rw [hzero] at rd5398'
  have rd5399 := RD.mload 0 v2 aw rd5398' (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4SwapBalance0CalldataWords o0 o1).toNat
          (amm4SwapBalance0FreePtr o0 o1).toNat 32) =
            amm4SwapBalance0CalldataWords o0 o1 from by
          simpa only [aw, fp] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4686 := evm_run rd5399 with [
    swap1, pop, push2 ⟨5409⟩, dup2, push2 ⟨4686⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd5409⟩ := RD.amm4CheckUint256Identity rd4686
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5449 := evm_run rd5409 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd4412 := evm_run rd5449 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v2, aw, fp] using rd4412⟩

theorem amm4SwapX_balance0Continue
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 v0 : UInt256} {o0 o1 o2 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2969⟩
      [v0, ⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2972⟩
      [v0, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0DecodeMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1) o2 acc k' C' := by
  exact ⟨_, _, evm_run rd with [jumpdest, swap1, pop]⟩

end Benchmarks.ActAmm4
