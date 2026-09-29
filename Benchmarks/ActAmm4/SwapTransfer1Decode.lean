import Benchmarks.ActAmm4.SwapTransfer1Call

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapTransfer1PostCallMem_size_ge (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hsize1 : o1.size < UInt256.size) :
    (amm4MintToken0FreePtr o0).toNat + 68 ≤
      (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).size := by
  unfold amm4SwapTransfer1PostCallMem
  have hbase := amm4SwapTransfer1CalldataMem_size I q0 q1 o0 hlo0 hbound0
  by_cases hshort : o1.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o1.size)).toNat =
        o1.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o1.size)
        (by decide) hshort hsize1
    rw [hlen]
    by_cases hzero : o1.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen o1 (amm4SwapTransfer1CalldataMem I q0 q1 o0)
        (amm4MintToken0FreePtr o0).toNat o1.size hzero le_rfl
        (by omega), ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ o1.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o1.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o1.size)
        (by decide) hlong hsize1
    rw [hlen]
    rw [write_eq_gen o1 (amm4SwapTransfer1CalldataMem I q0 q1 o0)
      (amm4MintToken0FreePtr o0).toNat 32 (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem amm4SwapTransfer1PostCallMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hsize1 : o1.size < UInt256.size) :
    (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o0) := by
  unfold amm4SwapTransfer1PostCallMem
  have hbase := amm4SwapTransfer1CalldataMem_size I q0 q1 o0 hlo0 hbound0
  have hptr : 160 ≤ (amm4MintToken0FreePtr o0).toNat := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o0 hlo0 hbound0).1
  by_cases hshort : o1.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o1.size)).toNat =
        o1.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o1.size)
        (by decide) hshort hsize1
    rw [hlen]
    by_cases hzero : o1.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact amm4SwapTransfer1CalldataMem_read64 I q0 q1 hlo0 hbound0
    · rw [write_read_below_gen o1 (amm4SwapTransfer1CalldataMem I q0 q1 o0)
        (amm4MintToken0FreePtr o0).toNat o1.size 64 hzero le_rfl
        (by omega) (by omega)]
      exact amm4SwapTransfer1CalldataMem_read64 I q0 q1 hlo0 hbound0
  · have hlong : 32 ≤ o1.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o1.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o1.size)
        (by decide) hlong hsize1
    rw [hlen]
    rw [write32_read_below o1 (amm4SwapTransfer1CalldataMem I q0 q1 o0)
      (amm4MintToken0FreePtr o0).toNat 64 hlong (by omega) (by omega)]
    exact amm4SwapTransfer1CalldataMem_read64 I q0 q1 hlo0 hbound0

theorem amm4SwapTransfer1PostCallMem_readPtr (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hsize1 : o1.size < UInt256.size) :
    (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 32 = o1.extract 0 32 := by
  unfold amm4SwapTransfer1PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o1.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o1.size)
      (by decide) hlo1 hsize1
  rw [hlen]
  exact write32_read_back o1 (amm4SwapTransfer1CalldataMem I q0 q1 o0)
    (amm4MintToken0FreePtr o0).toNat hlo1 (by
      have h := amm4SwapTransfer1CalldataMem_size I q0 q1 o0 hlo0 hbound0
      omega)

noncomputable def amm4SwapTransfer1DecodeMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 : ByteArray) : ByteArray :=
  (UInt256.add (amm4MintToken0FreePtr o0)
    (amm4MintReturndataRounded o1)).toByteArray.write 0
    (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1) 64 32

theorem amm4SwapTransfer1DecodeMem_size_ge (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hsize1 : o1.size < UInt256.size) :
    (amm4MintToken0FreePtr o0).toNat + 68 ≤
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).size := by
  unfold amm4SwapTransfer1DecodeMem
  let base := amm4SwapTransfer1PostCallMem I q0 q1 o0 o1
  have hbase : (amm4MintToken0FreePtr o0).toNat + 68 ≤ base.size :=
    amm4SwapTransfer1PostCallMem_size_ge I q0 q1 hlo0 hbound0 hsize1
  have hptr : 160 ≤ (amm4MintToken0FreePtr o0).toNat := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o0 hlo0 hbound0).1
  have hsz : ((UInt256.add (amm4MintToken0FreePtr o0)
      (amm4MintReturndataRounded o1)).toByteArray.write 0 base 64 32).size =
      base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem amm4SwapTransfer1DecodeMem_readPtr (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hsize1 : o1.size < UInt256.size) :
    (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 32 = o1.extract 0 32 := by
  unfold amm4SwapTransfer1DecodeMem
  have hbase := amm4SwapTransfer1PostCallMem_size_ge I q0 q1 hlo0 hbound0 hsize1
  have hptr : 160 ≤ (amm4MintToken0FreePtr o0).toNat := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o0 hlo0 hbound0).1
  rw [write32_read_above _ _ 64 (amm4MintToken0FreePtr o0).toNat
    (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
  exact amm4SwapTransfer1PostCallMem_readPtr I q0 q1 hlo0 hbound0 hlo1 hsize1

theorem amm4SwapX_transfer1ToDecoder {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hsize1 : o1.size < UInt256.size)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2783⟩
      [amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨2814⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k' C' := by
  let aw := amm4SwapTransfer1CalldataWords o0
  let fp := amm4MintToken0FreePtr o0
  have hmem : 64 < (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).size := by
    have hsz : fp.toNat + 68 ≤
        (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).size :=
      amm4SwapTransfer1PostCallMem_size_ge I q0 q1 hlo0 hbound0 hsize1
    have hfp : 160 ≤ fp.toNat := by
      simpa only [fp, amm4MintToken0FreePtr] using
        (amm4MintToken0FreePtr_bounds o0 hlo0 hbound0).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4SwapTransfer1PostCallMem I q0 q1 o0 o1).readWithPadding 64 32))) =
        fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem)
      (by simpa only [aw] using
        amm4SwapTransfer1CalldataWords_mload64_haw o0 hlo0 hbound0)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using amm4SwapTransfer1PostCallMem_read64 I q0 q1 hlo0 hbound0 hsize1)
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    simpa only [aw, show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      amm4SwapTransfer1CalldataWords_mload64_same o0 hlo0 hbound0
  have rd4229 := evm_run rd with [push1 ⟨64⟩]
  have rd4230 := RD.mload 0 fp aw rd4229 (by native_decide)
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
  have rd4244 := evm_run rd4230 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd4245 := RD.mstore 0
    (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1) aw rd4244
    (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4SwapTransfer1CalldataWords o0).toNat
          (⟨64⟩ : UInt256).toNat 32) = amm4SwapTransfer1CalldataWords o0 from by
        simpa only [aw] using hsame]
      simp only [aw]
      omega)
    (by unfold amm4SwapTransfer1DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6025 := evm_run rd4245 with [
    pop, dup2, add, swap1, push2 ⟨2814⟩, swap2, swap1,
    push2 ⟨6025⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, amm4MintReturndataRounded] using rd6025⟩

theorem amm4SwapX_transfer1DecodeShortReverts {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hshort1 : o1.size < 32)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨2814⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := amm4MintToken1LenCheckShort o0 o1 hlo0 hbound0 hshort1
  have rd6034 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd4583 := evm_run rd6034 with [
    push2 ⟨6046⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6045⟩, push2 ⟨4583⟩, jump (by jump_dest)]
  exact evm_run rd4583 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem amm4SwapTransfer1CalldataWords_ptr_haw (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    ¬ amm4MintToken0FreePtr o ≥ amm4SwapTransfer1CalldataWords o * ⟨32⟩ := by
  let n := (o.size + 31) / 32
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using
      amm4MintToken0FreePtr_toNat o hbound
  have haw : (amm4SwapTransfer1CalldataWords o).toNat = 7 + n := by
    simpa only [n] using amm4SwapTransfer1CalldataWords_toNat o hlo hbound
  have hmul : (amm4SwapTransfer1CalldataWords o).toNat * 32 < UInt256.size := by
    have hle : n ≤ o.size + 31 := Nat.div_le_self _ _
    have hcap : (2 ^ 138 + 40) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (amm4SwapTransfer1CalldataWords o * ⟨32⟩).toNat ≤
      (amm4MintToken0FreePtr o).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem amm4SwapTransfer1CalldataWords_mloadPtr_same (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M (amm4SwapTransfer1CalldataWords o).toNat
      (amm4MintToken0FreePtr o).toNat 32) =
      amm4SwapTransfer1CalldataWords o := by
  let n := (o.size + 31) / 32
  have hptr : (amm4MintToken0FreePtr o).toNat = 128 + 32 * n := by
    simpa only [amm4MintToken0FreePtr, n] using
      amm4MintToken0FreePtr_toNat o hbound
  have haw : (amm4SwapTransfer1CalldataWords o).toNat = 7 + n := by
    simpa only [n] using amm4SwapTransfer1CalldataWords_toNat o hlo hbound
  have hM : MachineState.M (amm4SwapTransfer1CalldataWords o).toNat
      (amm4MintToken0FreePtr o).toNat 32 =
      (amm4SwapTransfer1CalldataWords o).toNat := by
    change max (amm4SwapTransfer1CalldataWords o).toNat
      (((amm4MintToken0FreePtr o).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem amm4SwapX_transfer1DecodeWord {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨2814⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
        amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨6059⟩, ⟨0⟩, ⟨0⟩, amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨2814⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k' C' := by
  let aw := amm4SwapTransfer1CalldataWords o0
  let fp := amm4MintToken0FreePtr o0
  let v : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (o1.extract 0 32))
  have hcheck := amm4MintToken1LenCheckOk o0 o1
    hlo0 hbound0 hlo1 hbound1
  have rd6046 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6046⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6005 := evm_run rd6046 with [
    jumpdest, push0, push2 ⟨6059⟩, dup5, dup3, dup6, add,
    push2 ⟨6005⟩, jump (by jump_dest)]
  have hmem : fp.toNat < (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).size := by
    have hsz : fp.toNat + 68 ≤
        (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).size :=
      amm4SwapTransfer1DecodeMem_size_ge I q0 q1 hlo0 hbound0
        (lt_trans hbound1 (by norm_num [UInt256.size]))
    omega
  have hval :
      (if fp.toNat ≥ (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4SwapTransfer1DecodeMem I q0 q1 o0 o1).readWithPadding
           fp.toNat 32))) = v := by
    have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
      simpa only [fp, aw] using
        amm4SwapTransfer1CalldataWords_ptr_haw o0 hlo0 hbound0
    rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
      amm4SwapTransfer1DecodeMem_readPtr I q0 q1 hlo0 hbound0 hlo1
        (lt_trans hbound1 (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      amm4SwapTransfer1CalldataWords_mloadPtr_same o0 hlo0 hbound0
  have rd6008 := evm_run rd6005 with [jumpdest, push0, dup2]
  have hzero : fp + ⟨0⟩ = fp := by
    rw [u256_add_comm, u256_zero_add]
  have rd6008' := rd6008
  rw [hzero] at rd6008'
  have rd6009 := RD.mload 0 v aw rd6008' (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (amm4SwapTransfer1CalldataWords o0).toNat
          (amm4MintToken0FreePtr o0).toNat 32) =
            amm4SwapTransfer1CalldataWords o0 from by
        simpa only [aw, fp] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5983 := evm_run rd6009 with [
    swap1, pop, push2 ⟨6019⟩, dup2, push2 ⟨5983⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v, fp, aw] using rd5983⟩

theorem amm4SwapX_transfer1DecodeInvalidReverts
    {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hbad : UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)) ≠
      UInt256.isZero (UInt256.isZero
        (UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))))
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
        amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨6059⟩, ⟨0⟩, ⟨0⟩, amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨2814⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  exact RD.amm4BurnBoolCheckInvalid rd hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4SwapX_transfer1DecodeOk {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcanon : UInt256.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32)) = ⟨1⟩)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32)),
        amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨6059⟩, ⟨0⟩, ⟨0⟩, amm4MintToken0FreePtr o0,
        UInt256.add (amm4MintToken0FreePtr o0) (UInt256.ofNat o1.size),
        ⟨2814⟩, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2816⟩
      [amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapTransfer1DecodeMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0) o1 acc k' C' := by
  obtain ⟨_, _, rd6019⟩ := RD.amm4BurnBoolCheckOk rd hcanon
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6059 := evm_run rd6019 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd4258 := evm_run rd6059 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd4258 with [jumpdest, pop]⟩

end Benchmarks.ActAmm4
