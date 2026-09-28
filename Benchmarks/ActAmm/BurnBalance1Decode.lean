import Benchmarks.ActAmm.BurnBalance1Call

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammBurnBalance1PostCallMem_size_ge (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 o3 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hsize3 : o3.size < UInt256.size) :
    (ammBurnBalance1FreePtr o0 o1 o2).toNat + 36 ≤
      (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3).size := by
  unfold ammBurnBalance1PostCallMem
  have hbase := ammBurnBalance1CalldataMem_size I q0 q1
    hlo0 hbound0 hbound1 hbound2
  by_cases hshort : o3.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat =
        o3.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o3.size)
        (by decide) hshort hsize3
    rw [hlen]
    by_cases hzero : o3.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen o3
        (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
        (ammBurnBalance1FreePtr o0 o1 o2).toNat o3.size hzero le_rfl
        (by omega), ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ o3.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o3.size)
        (by decide) hlong hsize3
    rw [hlen]
    rw [write_eq_gen o3
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 32
      (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem ammBurnBalance1PostCallMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 o3 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hsize3 : o3.size < UInt256.size) :
    (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3).readWithPadding
      64 32 = UInt256.toByteArray
        (ammBurnBalance1FreePtr o0 o1 o2) := by
  unfold ammBurnBalance1PostCallMem
  have hbase := ammBurnBalance1CalldataMem_size I q0 q1
    hlo0 hbound0 hbound1 hbound2
  have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).1
  by_cases hshort : o3.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat =
        o3.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o3.size)
        (by decide) hshort hsize3
    rw [hlen]
    by_cases hzero : o3.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact ammBurnBalance1CalldataMem_read64 I q0 q1
        hlo0 hbound0 hbound1 hbound2
    · rw [write_read_below_gen o3
        (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
        (ammBurnBalance1FreePtr o0 o1 o2).toNat o3.size 64
        hzero le_rfl (by omega) (by omega)]
      exact ammBurnBalance1CalldataMem_read64 I q0 q1
        hlo0 hbound0 hbound1 hbound2
  · have hlong : 32 ≤ o3.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o3.size)
        (by decide) hlong hsize3
    rw [hlen]
    rw [write32_read_below o3
      (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 64 hlong
      (by omega) (by omega)]
    exact ammBurnBalance1CalldataMem_read64 I q0 q1
      hlo0 hbound0 hbound1 hbound2

theorem ammBurnBalance1PostCallMem_readPtr (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 o3 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hlo3 : 32 ≤ o3.size) (hsize3 : o3.size < UInt256.size) :
    (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3).readWithPadding
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 32 =
      o3.extract 0 32 := by
  unfold ammBurnBalance1PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o3.size)).toNat =
      32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o3.size)
      (by decide) hlo3 hsize3
  rw [hlen]
  exact write32_read_back o3
    (ammBurnBalance1CalldataMem I q0 q1 o0 o1 o2)
    (ammBurnBalance1FreePtr o0 o1 o2).toNat hlo3 (by
      have h := ammBurnBalance1CalldataMem_size I q0 q1
        hlo0 hbound0 hbound1 hbound2
      omega)

noncomputable def ammBurnBalance1DecodeMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 o1 o2 o3 : ByteArray) : ByteArray :=
  (UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
    (ammMintReturndataRounded o3)).toByteArray.write 0
    (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3) 64 32

theorem ammBurnBalance1DecodeMem_size_ge (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 o3 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hsize3 : o3.size < UInt256.size) :
    (ammBurnBalance1FreePtr o0 o1 o2).toNat + 36 ≤
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3).size := by
  unfold ammBurnBalance1DecodeMem
  let base := ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3
  have hbase : (ammBurnBalance1FreePtr o0 o1 o2).toNat + 36 ≤
      base.size :=
    ammBurnBalance1PostCallMem_size_ge I q0 q1
      hlo0 hbound0 hbound1 hbound2 hsize3
  have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).1
  have hsz : ((UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
      (ammMintReturndataRounded o3)).toByteArray.write 0 base 64 32).size =
      base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem ammBurnBalance1DecodeMem_readPtr (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 o1 o2 o3 : ByteArray}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hlo3 : 32 ≤ o3.size) (hsize3 : o3.size < UInt256.size) :
    (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3).readWithPadding
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 32 =
      o3.extract 0 32 := by
  unfold ammBurnBalance1DecodeMem
  have hbase := ammBurnBalance1PostCallMem_size_ge I q0 q1
    hlo0 hbound0 hbound1 hbound2 hsize3
  have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).1
  rw [write32_read_above _ _ 64
    (ammBurnBalance1FreePtr o0 o1 o2).toNat
    (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
  exact ammBurnBalance1PostCallMem_readPtr I q0 q1
    hlo0 hbound0 hbound1 hbound2 hlo3 hsize3

theorem ammBurnX_balance1ToDecoder
    {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 o3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (hsize3 : o3.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5353⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammBurnBalance1FreePtr o0 o1 o2,
        UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
          (UInt256.ofNat o3.size),
        ⟨5384⟩, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 acc k' C' := by
  let aw := ammBurnBalance1CalldataWords o0 o1 o2
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  have haw : aw.toNat =
      6 + (o0.size + 31) / 32 + (o1.size + 31) / 32 +
      (o2.size + 31) / 32 := by
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
      (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3).size := by
    have hsz := ammBurnBalance1PostCallMem_size_ge I q0 q1
      hlo0 hbound0 hbound1 hbound2 hsize3
    have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
      hlo0 hbound0 hbound1 hbound2).1
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnBalance1PostCallMem I q0 q1 o0 o1 o2 o3).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammBurnBalance1PostCallMem_read64 I q0 q1
          (o0 := o0) (o1 := o1) (o2 := o2) (o3 := o3)
          hlo0 hbound0 hbound1 hbound2 hsize3))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd5355 := evm_run rd with [push1 ⟨64⟩]
  have rd5356 := RD.mload 0 fp aw rd5355 (by native_decide)
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
  have rd5370 := evm_run rd5356 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd5371 := RD.mstore 0
    (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3) aw rd5370
    (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammBurnBalance1CalldataWords o0 o1 o2).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammBurnBalance1CalldataWords o0 o1 o2 from by
          simpa only [aw] using hsame]
      simp only [aw]
      omega)
    (by unfold ammBurnBalance1DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6453 := evm_run rd5371 with [
    pop, dup2, add, swap1, push2 ⟨5384⟩, swap2, swap1,
    push2 ⟨6453⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, ammMintReturndataRounded]
    using rd6453⟩

theorem ammBurnBalance1LenCheckShort (o0 o1 o2 o3 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hshort3 : o3.size < 32) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
          (UInt256.ofNat o3.size))
        (ammBurnBalance1FreePtr o0 o1 o2)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (ammBurnBalance1FreePtr_bounds o0 o1 o2
    hlo0 hbound0 hbound1 hbound2).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (ammBurnBalance1FreePtr o0 o1 o2).toNat)
    (len := o3.size) (words := 1)
    (by simpa using hshort3)
    (ammBurnBalance1FreePtr o0 o1 o2).val.isLt
    (by omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammBurnBalance1LenCheckOk (o0 o1 o2 o3 : ByteArray)
    (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hlo3 : 32 ≤ o3.size) (hbound3 : o3.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
          (UInt256.ofNat o3.size))
        (ammBurnBalance1FreePtr o0 o1 o2)) ⟨32⟩ = ⟨0⟩ := by
  have hptr := ammBurnBalance1FreePtr_toNat o0 o1 o2
    hbound0 hbound1 hbound2
  have hle0 : (o0.size + 31) / 32 ≤ o0.size + 31 :=
    Nat.div_le_self _ _
  have hle1 : (o1.size + 31) / 32 ≤ o1.size + 31 :=
    Nat.div_le_self _ _
  have hle2 : (o2.size + 31) / 32 ≤ o2.size + 31 :=
    Nat.div_le_self _ _
  have hcap : 128 + 32 *
      (2 ^ 138 + 31 + 2 ^ 138 + 31 + 2 ^ 138 + 31) +
      2 ^ 138 < UInt256.size := by norm_num [UInt256.size]
  have hcheck := solcReturnStaticLenCheckOk
    (base := (ammBurnBalance1FreePtr o0 o1 o2).toNat)
    (len := o3.size) (words := 1)
    (by simpa using hlo3)
    (by omega : o3.size < 2 ^ 255)
    (ammBurnBalance1FreePtr o0 o1 o2).val.isLt
    (by omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammBurnX_balance1DecodeShortReverts
    {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {o0 o1 o2 o3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hbound1 : o1.size < 2 ^ 138)
    (hbound2 : o2.size < 2 ^ 138)
    (hshort3 : o3.size < 32)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammBurnBalance1FreePtr o0 o1 o2,
        UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
          (UInt256.ofNat o3.size),
        ⟨5384⟩, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 acc k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := ammBurnBalance1LenCheckShort o0 o1 o2 o3
    hlo0 hbound0 hbound1 hbound2 hshort3
  have rd6462 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd5396 := evm_run rd6462 with [
    push2 ⟨6474⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6473⟩, push2 ⟨5396⟩, jump (by jump_dest)]
  exact evm_run rd5396 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammBurnBalance1CalldataWords_ptr_haw (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    ¬ ammBurnBalance1FreePtr o0 o1 o2 ≥
      ammBurnBalance1CalldataWords o0 o1 o2 * ⟨32⟩ := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let n2 := (o2.size + 31) / 32
  have hptr : (ammBurnBalance1FreePtr o0 o1 o2).toNat =
      128 + 32 * (n0 + n1 + n2) := by
    simpa only [n0, n1, n2] using
      ammBurnBalance1FreePtr_toNat o0 o1 o2
        hbound0 hbound1 hbound2
  have haw : (ammBurnBalance1CalldataWords o0 o1 o2).toNat =
      6 + n0 + n1 + n2 := by
    simpa only [n0, n1, n2] using
      ammBurnBalance1CalldataWords_toNat o0 o1 o2
        hlo0 hbound0 hlo1 hbound1 hlo2 hbound2
  have hmul : (ammBurnBalance1CalldataWords o0 o1 o2).toNat * 32 <
      UInt256.size := by
    have hle0 : n0 ≤ o0.size + 31 := Nat.div_le_self _ _
    have hle1 : n1 ≤ o1.size + 31 := Nat.div_le_self _ _
    have hle2 : n2 ≤ o2.size + 31 := Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31 +
      2 ^ 138 + 31) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  intro h
  have hle : (ammBurnBalance1CalldataWords o0 o1 o2 * ⟨32⟩).toNat ≤
      (ammBurnBalance1FreePtr o0 o1 o2).toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem ammBurnBalance1CalldataWords_mloadPtr_same
    (o0 o1 o2 : ByteArray)
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (ammBurnBalance1CalldataWords o0 o1 o2).toNat
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 32) =
      ammBurnBalance1CalldataWords o0 o1 o2 := by
  let n0 := (o0.size + 31) / 32
  let n1 := (o1.size + 31) / 32
  let n2 := (o2.size + 31) / 32
  have hptr : (ammBurnBalance1FreePtr o0 o1 o2).toNat =
      128 + 32 * (n0 + n1 + n2) := by
    simpa only [n0, n1, n2] using
      ammBurnBalance1FreePtr_toNat o0 o1 o2
        hbound0 hbound1 hbound2
  have haw : (ammBurnBalance1CalldataWords o0 o1 o2).toNat =
      6 + n0 + n1 + n2 := by
    simpa only [n0, n1, n2] using
      ammBurnBalance1CalldataWords_toNat o0 o1 o2
        hlo0 hbound0 hlo1 hbound1 hlo2 hbound2
  have hM : MachineState.M
      (ammBurnBalance1CalldataWords o0 o1 o2).toNat
      (ammBurnBalance1FreePtr o0 o1 o2).toNat 32 =
      (ammBurnBalance1CalldataWords o0 o1 o2).toNat := by
    change max (ammBurnBalance1CalldataWords o0 o1 o2).toNat
      (((ammBurnBalance1FreePtr o0 o1 o2).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammBurnX_balance1DecodeOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {o0 o1 o2 o3 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (hlo3 : 32 ≤ o3.size) (hbound3 : o3.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammBurnBalance1FreePtr o0 o1 o2,
        UInt256.add (ammBurnBalance1FreePtr o0 o1 o2)
          (UInt256.ofNat o3.size),
        ⟨5384⟩, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5384⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o3.extract 0 32)),
        q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 acc k' C' := by
  let aw := ammBurnBalance1CalldataWords o0 o1 o2
  let fp := ammBurnBalance1FreePtr o0 o1 o2
  let v3 : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (o3.extract 0 32))
  have hcheck := ammBurnBalance1LenCheckOk o0 o1 o2 o3
    hbound0 hbound1 hbound2 hlo3 hbound3
  have rd6474 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6474⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6433 := evm_run rd6474 with [
    jumpdest, push0, push2 ⟨6487⟩, dup5, dup3, dup6, add,
    push2 ⟨6433⟩, jump (by jump_dest)]
  have hmem : fp.toNat <
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3).size := by
    have hsz := ammBurnBalance1DecodeMem_size_ge I q0 q1
      hlo0 hbound0 hbound1 hbound2
      (lt_trans hbound3 (by norm_num [UInt256.size]))
    dsimp [fp]
    omega
  have hval :
      (if fp.toNat ≥
          (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3).readWithPadding
           fp.toNat 32))) = v3 := by
    have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
      simpa only [fp, aw] using
        ammBurnBalance1CalldataWords_ptr_haw o0 o1 o2
          hlo0 hbound0 hlo1 hbound1 hlo2 hbound2
    rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
      ammBurnBalance1DecodeMem_readPtr I q0 q1
        hlo0 hbound0 hbound1 hbound2 hlo3
        (lt_trans hbound3 (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      ammBurnBalance1CalldataWords_mloadPtr_same o0 o1 o2
        hlo0 hbound0 hlo1 hbound1 hlo2 hbound2
  have rd6436 := evm_run rd6433 with [jumpdest, push0, dup2]
  have hzero : ammBurnBalance1FreePtr o0 o1 o2 + ⟨0⟩ =
      ammBurnBalance1FreePtr o0 o1 o2 := by
    rw [u256_add_comm, u256_zero_add]
  have rd6436' := rd6436
  rw [hzero] at rd6436'
  have rd6437 := RD.mload 0 v3 aw rd6436' (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammBurnBalance1CalldataWords o0 o1 o2).toNat
          (ammBurnBalance1FreePtr o0 o1 o2).toNat 32) =
            ammBurnBalance1CalldataWords o0 o1 o2 from by
          simpa only [aw, fp] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5499 := evm_run rd6437 with [
    swap1, pop, push2 ⟨6447⟩, dup2, push2 ⟨5499⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd6447⟩ := RD.ammCheckUint256Identity rd5499
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6487 := evm_run rd6447 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd5384 := evm_run rd6487 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v3, aw, fp] using rd5384⟩

theorem ammBurnX_balance1ReserveStored
    {cAstart cA gh bl σstart σ σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {o0 o1 o2 o3 : ByteArray}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5384⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o3.extract 0 32)),
        q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5395⟩
      [⟨560⟩, sel]
      (ammBurnBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (ammBurnBalance1CalldataWords o0 o1 o2)
      o3 (cA, sstoreAccountMap I.codeOwner σ ⟨6⟩
        (UInt256.ofNat (fromByteArrayBigEndian (o3.extract 0 32))))
      k' C' := by
  have rd5389 := evm_run rd with [jumpdest, push1 ⟨6⟩, dup2, swap1]
  obtain ⟨_, _, rd5390⟩ := rd5389.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd5390 with [pop, pop, pop, pop, pop]⟩

theorem ammBurnX_returnAfterBalances
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5395⟩
      [⟨560⟩, sel] mem aw rdata acc k C) :
    RDret ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I)
      acc ByteArray.empty := by
  have rd560 := evm_run rd with [jump (by jump_dest), jumpdest]
  exact rd560.stop (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.ActAmm
