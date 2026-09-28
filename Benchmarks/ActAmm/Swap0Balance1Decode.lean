import Benchmarks.ActAmm.Swap0Balance1Failure
import Benchmarks.ActAmm.Swap0Balance0Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0Balance1PostCallMem_size_ge (I : ExecutionEnv)
    {out ret ret1 : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hretSize : ret1.size < UInt256.size) :
    (ammSwap0Balance1FreePtr out ret).toNat + 36 ≤
      (ammSwap0Balance1PostCallMem I out ret ret1).size := by
  unfold ammSwap0Balance1PostCallMem
  have hbase := ammSwap0Balance1CalldataMem_size I hlo hbound hretBound
  by_cases hshort : ret1.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret1.size)).toNat =
        ret1.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := ret1.size)
        (by decide) hshort hretSize
    rw [hlen]
    by_cases hzero : ret1.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact hbase
    · rw [write_eq_gen ret1 (ammSwap0Balance1CalldataMem I out ret)
        (ammSwap0Balance1FreePtr out ret).toNat ret1.size hzero le_rfl
        (by omega), ByteArray.size_append, ByteArray.size_append,
        ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract]
      omega
  · have hlong : 32 ≤ ret1.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret1.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := ret1.size)
        (by decide) hlong hretSize
    rw [hlen]
    rw [write_eq_gen ret1 (ammSwap0Balance1CalldataMem I out ret)
      (ammSwap0Balance1FreePtr out ret).toNat 32
      (by omega) hlong (by omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract]
    omega

theorem ammSwap0Balance1PostCallMem_read64 (I : ExecutionEnv)
    {out ret ret1 : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hretSize : ret1.size < UInt256.size) :
    (ammSwap0Balance1PostCallMem I out ret ret1).readWithPadding 64 32 =
      UInt256.toByteArray (ammSwap0Balance1FreePtr out ret) := by
  unfold ammSwap0Balance1PostCallMem
  have hbase := ammSwap0Balance1CalldataMem_size I hlo hbound hretBound
  have hptr := (ammSwap0Balance1FreePtr_bounds out ret hlo hbound hretBound).1
  change 160 ≤ (ammSwap0Balance1FreePtr out ret).toNat at hptr
  by_cases hshort : ret1.size < 32
  · have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret1.size)).toNat =
        ret1.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := ret1.size)
        (by decide) hshort hretSize
    rw [hlen]
    by_cases hzero : ret1.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact ammSwap0Balance1CalldataMem_read64 I hlo hbound hretBound
    · rw [write_read_below_gen ret1
        (ammSwap0Balance1CalldataMem I out ret)
        (ammSwap0Balance1FreePtr out ret).toNat ret1.size 64 hzero le_rfl
        (by omega) (by omega)]
      exact ammSwap0Balance1CalldataMem_read64 I hlo hbound hretBound
  · have hlong : 32 ≤ ret1.size := by omega
    have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret1.size)).toNat =
        32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := ret1.size)
        (by decide) hlong hretSize
    rw [hlen]
    rw [write32_read_below ret1
      (ammSwap0Balance1CalldataMem I out ret)
      (ammSwap0Balance1FreePtr out ret).toNat 64 hlong
      (by omega) (by omega)]
    exact ammSwap0Balance1CalldataMem_read64 I hlo hbound hretBound

theorem ammSwap0Balance1PostCallMem_readPtr (I : ExecutionEnv)
    {out ret ret1 : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hretLo : 32 ≤ ret1.size) (hretSize : ret1.size < UInt256.size) :
    (ammSwap0Balance1PostCallMem I out ret ret1).readWithPadding
      (ammSwap0Balance1FreePtr out ret).toNat 32 = ret1.extract 0 32 := by
  unfold ammSwap0Balance1PostCallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat ret1.size)).toNat =
      32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := ret1.size)
      (by decide) hretLo hretSize
  rw [hlen]
  exact write32_read_back ret1 (ammSwap0Balance1CalldataMem I out ret)
    (ammSwap0Balance1FreePtr out ret).toNat hretLo (by
      have h := ammSwap0Balance1CalldataMem_size I hlo hbound hretBound
      omega)

noncomputable def ammSwap0Balance1DecodeMem
    (I : ExecutionEnv) (out ret ret1 : ByteArray) : ByteArray :=
  (UInt256.add (ammSwap0Balance1FreePtr out ret)
    (ammMintReturndataRounded ret1)).toByteArray.write 0
    (ammSwap0Balance1PostCallMem I out ret ret1) 64 32

theorem ammSwap0Balance1DecodeMem_size_ge (I : ExecutionEnv)
    {out ret ret1 : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hretSize : ret1.size < UInt256.size) :
    (ammSwap0Balance1FreePtr out ret).toNat + 36 ≤
      (ammSwap0Balance1DecodeMem I out ret ret1).size := by
  unfold ammSwap0Balance1DecodeMem
  let base := ammSwap0Balance1PostCallMem I out ret ret1
  have hbase : (ammSwap0Balance1FreePtr out ret).toNat + 36 ≤ base.size :=
    ammSwap0Balance1PostCallMem_size_ge I hlo hbound hretBound hretSize
  have hptr := (ammSwap0Balance1FreePtr_bounds out ret hlo hbound hretBound).1
  change 160 ≤ (ammSwap0Balance1FreePtr out ret).toNat at hptr
  have hsz : ((UInt256.add (ammSwap0Balance1FreePtr out ret)
      (ammMintReturndataRounded ret1)).toByteArray.write 0 base 64 32).size =
      base.size :=
    toByteArray_write32_size_of_le base _ 64 base.size base.size rfl
      (by omega) (by omega)
  rw [hsz]
  exact hbase

theorem ammSwap0Balance1DecodeMem_readPtr (I : ExecutionEnv)
    {out ret ret1 : ByteArray}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hretLo : 32 ≤ ret1.size) (hretSize : ret1.size < UInt256.size) :
    (ammSwap0Balance1DecodeMem I out ret ret1).readWithPadding
      (ammSwap0Balance1FreePtr out ret).toNat 32 = ret1.extract 0 32 := by
  unfold ammSwap0Balance1DecodeMem
  have hbase := ammSwap0Balance1PostCallMem_size_ge I
    hlo hbound hretBound hretSize
  have hptr := (ammSwap0Balance1FreePtr_bounds out ret hlo hbound hretBound).1
  change 160 ≤ (ammSwap0Balance1FreePtr out ret).toNat at hptr
  rw [write32_read_above _ _ 64 (ammSwap0Balance1FreePtr out ret).toNat
    (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]
  exact ammSwap0Balance1PostCallMem_readPtr I
    hlo hbound hretBound hretLo hretSize


theorem ammSwap0X_balance1ToDecoder
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret ret1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hretSize : ret1.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1553⟩
      [⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)), ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1PostCallMem I out ret ret1)
      (ammSwap0Balance1CalldataWords out ret) ret1 acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammSwap0Balance1FreePtr out ret,
        UInt256.add (ammSwap0Balance1FreePtr out ret)
          (UInt256.ofNat ret1.size),
        ⟨1584⟩, ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)), ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1DecodeMem I out ret ret1)
      (ammSwap0Balance1CalldataWords out ret) ret1 acc k' C' := by
  let aw := ammSwap0Balance1CalldataWords out ret
  let fp := ammSwap0Balance1FreePtr out ret
  have haw : aw.toNat = 6 + (out.size + 31) / 32 + (ret.size + 31) / 32 := by
    simpa only [aw] using
      ammSwap0Balance1CalldataWords_toNat out ret hlo hbound hretLo hretBound
  have hawlo : 3 ≤ aw.toNat := by rw [haw]; omega
  have hawfit : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    have hle : (out.size + 31) / 32 ≤ out.size + 31 := Nat.div_le_self _ _
    have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 := Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hmem : 64 <
      (ammSwap0Balance1PostCallMem I out ret ret1).size := by
    have hsz := ammSwap0Balance1PostCallMem_size_ge I
      hlo hbound hretBound hretSize
    have hptr := (ammSwap0Balance1FreePtr_bounds out ret
      hlo hbound hretBound).1
    change 160 ≤ (ammSwap0Balance1FreePtr out ret).toNat at hptr
    omega
  have hval :
      (if (⟨64⟩ : UInt256).toNat ≥
          (ammSwap0Balance1PostCallMem I out ret ret1).size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap0Balance1PostCallMem I out ret ret1).readWithPadding
           64 32))) = fp :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := aw) (v := fp)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using hmem)
      (ammActiveWords64 aw hawlo hawfit)
      (by simpa only [fp, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using (ammSwap0Balance1PostCallMem_read64 I
          (out := out) (ret := ret) (ret1 := ret1)
          hlo hbound hretBound hretSize))
  have hsame : UInt256.ofNat
      (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32) = aw := by
    have hM : MachineState.M aw.toNat 64 32 = aw.toNat := by
      change max aw.toNat ((64 + 32 + 31) / 32) = _
      omega
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, hM]
    exact u256_ofNat_toNat _
  have rd1555 := evm_run rd with [push1 ⟨64⟩]
  have rd1556 := RD.mload 0 fp aw rd1555 (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap0Balance1CalldataWords out ret).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammSwap0Balance1CalldataWords out ret from by
        simpa only [aw] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1570 := evm_run rd1556 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd1571 := RD.mstore 0
    (ammSwap0Balance1DecodeMem I out ret ret1) aw rd1570
    (by native_decide)
    (by
      intro s hawS hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap0Balance1CalldataWords out ret).toNat
          (⟨64⟩ : UInt256).toNat 32) =
            ammSwap0Balance1CalldataWords out ret from by
        simpa only [aw] using hsame]
      simp only [aw]
      omega)
    (by unfold ammSwap0Balance1DecodeMem; rfl)
    hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6453 := evm_run rd1571 with [
    pop, dup2, add, swap1, push2 ⟨1584⟩, swap2, swap1,
    push2 ⟨6453⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa only [fp, aw, ammMintReturndataRounded]
    using rd6453⟩

theorem ammSwap0Balance1LenCheckShort
    (out ret ret1 : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hshort : ret1.size < 32) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammSwap0Balance1FreePtr out ret)
          (UInt256.ofNat ret1.size))
        (ammSwap0Balance1FreePtr out ret)) ⟨32⟩ = ⟨1⟩ := by
  have hptr := (ammSwap0Balance1FreePtr_bounds out ret
    hlo hbound hretBound).2
  have hcheck := solcReturnStaticLenCheckShort
    (base := (ammSwap0Balance1FreePtr out ret).toNat)
    (len := ret1.size) (words := 1)
    (by simpa using hshort)
    (ammSwap0Balance1FreePtr out ret).val.isLt
    (by omega)
    (by norm_num)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammSwap0X_balance1DecodeShortReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret ret1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hshort : ret1.size < 32)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammSwap0Balance1FreePtr out ret,
        UInt256.add (ammSwap0Balance1FreePtr out ret)
          (UInt256.ofNat ret1.size),
        ⟨1584⟩, ⟨0⟩,
        UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1DecodeMem I out ret ret1)
      (ammSwap0Balance1CalldataWords out ret) ret1 acc k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := ammSwap0Balance1LenCheckShort out ret ret1
    hlo hbound hretBound hshort
  have rd6462 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd5396 := evm_run rd6462 with [
    push2 ⟨6474⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6473⟩, push2 ⟨5396⟩, jump (by jump_dest)]
  exact evm_run rd5396 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]


theorem ammSwap0Balance1LenCheckOk
    (out ret ret1 : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretBound : ret.size < 2 ^ 138)
    (hret1Lo : 32 ≤ ret1.size) (hret1Bound : ret1.size < 2 ^ 138) :
    UInt256.slt
      (UInt256.sub
        (UInt256.add (ammSwap0Balance1FreePtr out ret)
          (UInt256.ofNat ret1.size))
        (ammSwap0Balance1FreePtr out ret)) ⟨32⟩ = ⟨0⟩ := by
  have hptr0 := ammSwap0Balance1FreePtr_toNat out ret
    hbound hretBound
  have hptr : (ammSwap0Balance1FreePtr out ret).toNat < 2 ^ 141 := by
    have hle0 : (out.size + 31) / 32 ≤ out.size + 31 :=
      Nat.div_le_self _ _
    have hle1 : (ret.size + 31) / 32 ≤ ret.size + 31 :=
      Nat.div_le_self _ _
    rw [hptr0]
    omega
  have hcheck := solcReturnStaticLenCheckOk
    (base := (ammSwap0Balance1FreePtr out ret).toNat)
    (len := ret1.size) (words := 1)
    (by simpa using hret1Lo)
    (by omega : ret1.size < 2 ^ 255)
    (ammSwap0Balance1FreePtr out ret).val.isLt
    (by
      have hcap : 2 ^ 141 + 2 ^ 138 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  simpa only [u256_ofNat_toNat,
    show UInt256.ofNat (32 * 1) = (⟨32⟩ : UInt256) from by decide]
    using hcheck

theorem ammSwap0Balance1CalldataWords_ptr_haw (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138) :
    ¬ ammSwap0Balance1FreePtr out ret ≥
      ammSwap0Balance1CalldataWords out ret * ⟨32⟩ := by
  let n0 := (out.size + 31) / 32
  let n1 := (ret.size + 31) / 32
  have hptr : (ammSwap0Balance1FreePtr out ret).toNat =
      128 + 32 * (n0 + n1) := by
    simpa only [n0, n1] using
      ammSwap0Balance1FreePtr_toNat out ret hbound hretBound
  have haw : (ammSwap0Balance1CalldataWords out ret).toNat =
      6 + n0 + n1 := by
    simpa only [n0, n1] using
      ammSwap0Balance1CalldataWords_toNat out ret
        hlo hbound hretLo hretBound
  have hmul : (ammSwap0Balance1CalldataWords out ret).toNat * 32 <
      UInt256.size := by
    have hle0 : n0 ≤ out.size + 31 := Nat.div_le_self _ _
    have hle1 : n1 ≤ ret.size + 31 := Nat.div_le_self _ _
    have hcap : (6 + 2 ^ 138 + 31 + 2 ^ 138 + 31) * 32 <
      UInt256.size := by norm_num [UInt256.size]
    rw [haw]
    omega
  intro h
  have hle : (ammSwap0Balance1CalldataWords out ret * ⟨32⟩).toNat ≤
      (ammSwap0Balance1FreePtr out ret).toNat := h
  rw [u256_mul_op_toNat,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt hmul, hptr, haw] at hle
  omega

theorem ammSwap0Balance1CalldataWords_mloadPtr_same
    (out ret : ByteArray)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138) :
    UInt256.ofNat (MachineState.M
      (ammSwap0Balance1CalldataWords out ret).toNat
      (ammSwap0Balance1FreePtr out ret).toNat 32) =
      ammSwap0Balance1CalldataWords out ret := by
  let n0 := (out.size + 31) / 32
  let n1 := (ret.size + 31) / 32
  have hptr : (ammSwap0Balance1FreePtr out ret).toNat =
      128 + 32 * (n0 + n1) := by
    simpa only [n0, n1] using
      ammSwap0Balance1FreePtr_toNat out ret hbound hretBound
  have haw : (ammSwap0Balance1CalldataWords out ret).toNat =
      6 + n0 + n1 := by
    simpa only [n0, n1] using
      ammSwap0Balance1CalldataWords_toNat out ret
        hlo hbound hretLo hretBound
  have hM : MachineState.M (ammSwap0Balance1CalldataWords out ret).toNat
      (ammSwap0Balance1FreePtr out ret).toNat 32 =
      (ammSwap0Balance1CalldataWords out ret).toNat := by
    change max (ammSwap0Balance1CalldataWords out ret).toNat
      (((ammSwap0Balance1FreePtr out ret).toNat + 32 + 31) / 32) = _
    rw [hptr, haw]
    omega
  rw [hM]
  exact u256_ofNat_toNat _

theorem ammSwap0X_balance1DecodeOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {out ret ret1 : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138)
    (hretLo : 32 ≤ ret.size) (hretBound : ret.size < 2 ^ 138)
    (hret1Lo : 32 ≤ ret1.size) (hret1Bound : ret1.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6453⟩
      [ammSwap0Balance1FreePtr out ret,
        UInt256.add (ammSwap0Balance1FreePtr out ret)
          (UInt256.ofNat ret1.size),
        ⟨1584⟩, ⟨0⟩,
        UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap0ToWord I,
        ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1DecodeMem I out ret ret1)
      (ammSwap0Balance1CalldataWords out ret) ret1 acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1587⟩
      [UInt256.ofNat (fromByteArrayBigEndian (ret1.extract 0 32)),
        UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)),
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0Balance1DecodeMem I out ret ret1)
      (ammSwap0Balance1CalldataWords out ret) ret1 acc k' C' := by
  let aw := ammSwap0Balance1CalldataWords out ret
  let fp := ammSwap0Balance1FreePtr out ret
  let v : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (ret1.extract 0 32))
  have hcheck := ammSwap0Balance1LenCheckOk out ret ret1
    hlo hbound hretBound hret1Lo hret1Bound
  have rd6474 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6474⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6433 := evm_run rd6474 with [
    jumpdest, push0, push2 ⟨6487⟩, dup5, dup3, dup6, add,
    push2 ⟨6433⟩, jump (by jump_dest)]
  have hmem : fp.toNat <
      (ammSwap0Balance1DecodeMem I out ret ret1).size := by
    have hsz := ammSwap0Balance1DecodeMem_size_ge I
      hlo hbound hretBound
      (lt_trans hret1Bound (by norm_num [UInt256.size]))
    dsimp [fp]
    omega
  have hval :
      (if fp.toNat ≥ (ammSwap0Balance1DecodeMem I out ret ret1).size
          ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammSwap0Balance1DecodeMem I out ret ret1).readWithPadding
           fp.toNat 32))) = v := by
    have hbelow : ¬ fp ≥ aw * ⟨32⟩ := by
      simpa only [fp, aw] using
        ammSwap0Balance1CalldataWords_ptr_haw out ret hlo hbound hretLo hretBound
    rw [if_neg (not_or.mpr ⟨by omega, hbelow⟩),
      ammSwap0Balance1DecodeMem_readPtr I
        hlo hbound hretBound hret1Lo
        (lt_trans hret1Bound (by norm_num [UInt256.size]))]
  have hsame : UInt256.ofNat (MachineState.M aw.toNat fp.toNat 32) = aw := by
    simpa only [aw, fp] using
      ammSwap0Balance1CalldataWords_mloadPtr_same out ret hlo hbound hretLo hretBound
  have rd6436 := evm_run rd6433 with [jumpdest, push0, dup2]
  have hzero : ammSwap0Balance1FreePtr out ret + ⟨0⟩ =
      ammSwap0Balance1FreePtr out ret := by
    rw [u256_add_comm, u256_zero_add]
  have rd6436' := rd6436
  rw [hzero] at rd6436'
  have rd6437 := RD.mload 0 v aw rd6436' (by native_decide)
    (by
      intro s haw hstk
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero]
      rw [show UInt256.ofNat
        (MachineState.M (ammSwap0Balance1CalldataWords out ret).toNat
          (ammSwap0Balance1FreePtr out ret).toNat 32) =
            ammSwap0Balance1CalldataWords out ret from by
          simpa only [aw, fp] using hsame]
      omega)
    hval hsame
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5499 := evm_run rd6437 with [
    swap1, pop, push2 ⟨6447⟩, dup2, push2 ⟨5499⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd6447⟩ := RD.ammCheckUint256Identity rd5499
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6487 := evm_run rd6447 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1584 := evm_run rd6487 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  have rd1587 := evm_run rd1584 with [jumpdest, swap1, pop]
  exact ⟨_, _, by simpa only [v, aw, fp] using rd1587⟩

end Benchmarks.ActAmm
