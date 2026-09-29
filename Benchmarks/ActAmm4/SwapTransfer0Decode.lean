import Benchmarks.ActAmm4.SwapTransfer0Call
import Benchmarks.ActAmm4.BurnTransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

noncomputable def amm4SwapTransfer0PostCallMem
    (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  o.write 0 (amm4SwapTransfer0CalldataMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem amm4SwapTransfer0PostCallMem_size_short (I : ExecutionEnv)
    {o : ByteArray} (hshort : o.size < 32) :
    (amm4SwapTransfer0PostCallMem I o).size = 196 := by
  unfold amm4SwapTransfer0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size)
      (by decide) hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero,
      amm4SwapTransfer0CalldataMem_size]
  · rw [write_eq_gen o (amm4SwapTransfer0CalldataMem I) 128 o.size
      hzero le_rfl
      (by rw [amm4SwapTransfer0CalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, amm4SwapTransfer0CalldataMem_size]
    omega

theorem amm4SwapTransfer0PostCallMem_size_long (I : ExecutionEnv)
    {o : ByteArray} (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size) :
    (amm4SwapTransfer0PostCallMem I o).size = 196 := by
  unfold amm4SwapTransfer0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
      (by decide) hlo hhi
  rw [hlen]
  rw [write_eq_gen o (amm4SwapTransfer0CalldataMem I) 128 32
    (by omega) hlo (by rw [amm4SwapTransfer0CalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, amm4SwapTransfer0CalldataMem_size]
  omega

theorem amm4SwapTransfer0PostCallMem_read64 (I : ExecutionEnv)
    {o : ByteArray} (hhi : o.size < UInt256.size) :
    (amm4SwapTransfer0PostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  by_cases hshort : o.size < 32
  · unfold amm4SwapTransfer0PostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat =
          o.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size)
        (by decide) hshort (by omega)
    rw [hlen]
    by_cases hzero : o.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact amm4SwapTransfer0CalldataMem_read64 I
    · rw [write_read_below_gen_extend o
        (amm4SwapTransfer0CalldataMem I)
        128 o.size 64 hzero le_rfl
        (by rw [amm4SwapTransfer0CalldataMem_size]; omega)
        (by omega)]
      exact amm4SwapTransfer0CalldataMem_read64 I
  · have hlo : 32 ≤ o.size := by omega
    unfold amm4SwapTransfer0PostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
        (by decide) hlo hhi
    rw [hlen]
    rw [write_read_below_gen_extend o
      (amm4SwapTransfer0CalldataMem I)
      128 32 64 (by omega) hlo
      (by rw [amm4SwapTransfer0CalldataMem_size]; omega) (by omega)]
    exact amm4SwapTransfer0CalldataMem_read64 I

theorem amm4SwapTransfer0PostCallMem_read128 (I : ExecutionEnv)
    {o : ByteArray} (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size) :
    (amm4SwapTransfer0PostCallMem I o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold amm4SwapTransfer0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
      (by decide) hlo hhi
  rw [hlen]
  exact write32_read_back o (amm4SwapTransfer0CalldataMem I) 128
    (by omega) (by rw [amm4SwapTransfer0CalldataMem_size]; omega)

noncomputable def amm4SwapTransfer0DecodeMem
    (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)).toByteArray.write 0
    (amm4SwapTransfer0PostCallMem I o) 64 32

theorem amm4SwapTransfer0DecodeMem_size (I : ExecutionEnv)
    {o : ByteArray} (hhi : o.size < UInt256.size) :
    (amm4SwapTransfer0DecodeMem I o).size = 196 := by
  have hbase : (amm4SwapTransfer0PostCallMem I o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact amm4SwapTransfer0PostCallMem_size_short I hshort
    · exact amm4SwapTransfer0PostCallMem_size_long I (by omega) hhi
  unfold amm4SwapTransfer0DecodeMem
  exact toByteArray_write32_size_of_le
    (amm4SwapTransfer0PostCallMem I o)
    (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o))
    64 196 196 hbase (by rw [hbase]; omega) (by omega)

theorem amm4SwapTransfer0DecodeMem_read128 (I : ExecutionEnv)
    {o : ByteArray} (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size) :
    (amm4SwapTransfer0DecodeMem I o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold amm4SwapTransfer0DecodeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [amm4SwapTransfer0PostCallMem_size_long I hlo hhi]; omega)
    (by omega)
    (by rw [amm4SwapTransfer0PostCallMem_size_long I hlo hhi]; omega)]
  exact amm4SwapTransfer0PostCallMem_read128 I hlo hhi

theorem amm4SwapX_transfer0ToDecoder
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hhi : o.size < UInt256.size)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2626⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0PostCallMem I o) (UInt256.ofNat 7)
      o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨2657⟩,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k' C' := by
  have hmemSize : (amm4SwapTransfer0PostCallMem I o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact amm4SwapTransfer0PostCallMem_size_short I hshort
    · exact amm4SwapTransfer0PostCallMem_size_long I (by omega) hhi
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4SwapTransfer0PostCallMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4SwapTransfer0PostCallMem I o).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide)
      (amm4SwapTransfer0PostCallMem_read64 I hhi)
  have rd1244 := evm_run rd with [push1 ⟨64⟩]
  have rd1245 := evm_run rd1244 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1259 := evm_run rd1245 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd1260 := evm_run rd1259 with [
    raw mstore 0 (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd6025 := evm_run rd1260 with [
    pop, dup2, add, swap1, push2 ⟨2657⟩, swap2, swap1,
    push2 ⟨6025⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [amm4SwapTransfer0DecodeMem, amm4MintReturndataRounded]
      using rd6025⟩

theorem amm4SwapX_transfer0DecodeShortReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hshort : o.size < 32)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨2657⟩,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := solcDecodeEndLenCheckShort_128_32 hshort
  have rd6034 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd4583 := evm_run rd6034 with [
    push2 ⟨6046⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6045⟩, push2 ⟨4583⟩, jump (by jump_dest)]
  exact evm_run rd4583 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem amm4SwapX_transfer0DecodeWord
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨2657⟩,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6059⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨2657⟩,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k' C' := by
  have hhi : o.size < UInt256.size :=
    lt_trans hbound (by norm_num [UInt256.size])
  have hcheck := solcDecodeEndLenCheckOk_128_32 hlo
    (by omega : o.size < 2 ^ 255)
  have rd6046 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6046⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6005 := evm_run rd6046 with [
    jumpdest, push0, push2 ⟨6059⟩, dup5, dup3, dup6, add,
    push2 ⟨6005⟩, jump (by jump_dest)]
  let v : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (o.extract 0 32))
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (amm4SwapTransfer0DecodeMem I o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4SwapTransfer0DecodeMem I o).readWithPadding 128 32))) =
        v := by
    simpa only [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      amm4SwapTransfer0DecodeMem_read128 I hlo hhi, v] using
      (mloadValue_eq_readWithPadding_of_lt_size
        (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7) ⟨128⟩ 196
        (amm4SwapTransfer0DecodeMem_size I hhi)
        (by decide) (by decide))
  have rd6008 := evm_run rd6005 with [jumpdest, push0, dup2]
  have rd6009 := evm_run rd6008 with [
    raw mload 0 v (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  have rd5983 := evm_run rd6009 with [
    swap1, pop, push2 ⟨6019⟩, dup2, push2 ⟨5983⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v] using rd5983⟩

theorem amm4SwapX_transfer0DecodeInvalidReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hbad : UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ≠
      UInt256.isZero (UInt256.isZero
        (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))))
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6059⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨2657⟩,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  exact RD.amm4BurnBoolCheckInvalid rd hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4SwapX_transfer0DecodeOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcanon : UInt256.ofNat
        (fromByteArrayBigEndian (o.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat
        (fromByteArrayBigEndian (o.extract 0 32)) = ⟨1⟩)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6059⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨2657⟩,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2659⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o) (UInt256.ofNat 7)
      o acc k' C' := by
  obtain ⟨_, _, rd6019⟩ := RD.amm4BurnBoolCheckOk rd hcanon
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6059 := evm_run rd6019 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1273 := evm_run rd6059 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd1273 with [jumpdest, pop]⟩

end Benchmarks.ActAmm4
