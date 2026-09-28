import Benchmarks.ActAmm.Swap0TransferFailure

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

noncomputable def ammSwap0TransferPostCallMem
    (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  o.write 0 (ammSwap0TransferCalldataMem I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem ammSwap0TransferPostCallMem_size_short (I : ExecutionEnv)
    {o : ByteArray} (hshort : o.size < 32) :
    (ammSwap0TransferPostCallMem I o).size = 196 := by
  unfold ammSwap0TransferPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size)
      (by decide) hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero,
      ammSwap0TransferCalldataMem_size]
  · rw [write_eq_gen o (ammSwap0TransferCalldataMem I) 128 o.size
      hzero le_rfl
      (by rw [ammSwap0TransferCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, ammSwap0TransferCalldataMem_size]
    omega

theorem ammSwap0TransferPostCallMem_size_long (I : ExecutionEnv)
    {o : ByteArray} (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size) :
    (ammSwap0TransferPostCallMem I o).size = 196 := by
  unfold ammSwap0TransferPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
      (by decide) hlo hhi
  rw [hlen]
  rw [write_eq_gen o (ammSwap0TransferCalldataMem I) 128 32
    (by omega) hlo (by rw [ammSwap0TransferCalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, ammSwap0TransferCalldataMem_size]
  omega

theorem ammSwap0TransferPostCallMem_read64 (I : ExecutionEnv)
    {o : ByteArray} (hhi : o.size < UInt256.size) :
    (ammSwap0TransferPostCallMem I o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  by_cases hshort : o.size < 32
  · unfold ammSwap0TransferPostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat =
          o.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size)
        (by decide) hshort (by omega)
    rw [hlen]
    by_cases hzero : o.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact ammSwap0TransferCalldataMem_read64 I
    · rw [write_read_below_gen_extend o
        (ammSwap0TransferCalldataMem I)
        128 o.size 64 hzero le_rfl
        (by rw [ammSwap0TransferCalldataMem_size]; omega)
        (by omega)]
      exact ammSwap0TransferCalldataMem_read64 I
  · have hlo : 32 ≤ o.size := by omega
    unfold ammSwap0TransferPostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
        (by decide) hlo hhi
    rw [hlen]
    rw [write_read_below_gen_extend o
      (ammSwap0TransferCalldataMem I)
      128 32 64 (by omega) hlo
      (by rw [ammSwap0TransferCalldataMem_size]; omega) (by omega)]
    exact ammSwap0TransferCalldataMem_read64 I

theorem ammSwap0TransferPostCallMem_read128 (I : ExecutionEnv)
    {o : ByteArray} (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size) :
    (ammSwap0TransferPostCallMem I o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold ammSwap0TransferPostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
      (by decide) hlo hhi
  rw [hlen]
  exact write32_read_back o (ammSwap0TransferCalldataMem I) 128
    (by omega) (by rw [ammSwap0TransferCalldataMem_size]; omega)

noncomputable def ammSwap0TransferDecodeMem
    (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)).toByteArray.write 0
    (ammSwap0TransferPostCallMem I o) 64 32

theorem ammSwap0TransferDecodeMem_size (I : ExecutionEnv)
    {o : ByteArray} (hhi : o.size < UInt256.size) :
    (ammSwap0TransferDecodeMem I o).size = 196 := by
  have hbase : (ammSwap0TransferPostCallMem I o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact ammSwap0TransferPostCallMem_size_short I hshort
    · exact ammSwap0TransferPostCallMem_size_long I (by omega) hhi
  unfold ammSwap0TransferDecodeMem
  exact toByteArray_write32_size_of_le
    (ammSwap0TransferPostCallMem I o)
    (UInt256.add ⟨128⟩ (ammMintReturndataRounded o))
    64 196 196 hbase (by rw [hbase]; omega) (by omega)

theorem ammSwap0TransferDecodeMem_read128 (I : ExecutionEnv)
    {o : ByteArray} (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size) :
    (ammSwap0TransferDecodeMem I o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold ammSwap0TransferDecodeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [ammSwap0TransferPostCallMem_size_long I hlo hhi]; omega)
    (by omega)
    (by rw [ammSwap0TransferPostCallMem_size_long I hlo hhi]; omega)]
  exact ammSwap0TransferPostCallMem_read128 I hlo hhi

theorem ammSwap0X_transferToDecoder
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hhi : o.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1242⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferPostCallMem I o) (UInt256.ofNat 7)
      o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6365⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1273⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k' C' := by
  have hmemSize : (ammSwap0TransferPostCallMem I o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact ammSwap0TransferPostCallMem_size_short I hshort
    · exact ammSwap0TransferPostCallMem_size_long I (by omega) hhi
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammSwap0TransferPostCallMem I o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammSwap0TransferPostCallMem I o).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide)
      (ammSwap0TransferPostCallMem_read64 I hhi)
  have rd1244 := evm_run rd with [push1 ⟨64⟩]
  have rd1245 := evm_run rd1244 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1259 := evm_run rd1245 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd1260 := evm_run rd1259 with [
    raw mstore 0 (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd6365 := evm_run rd1260 with [
    pop, dup2, add, swap1, push2 ⟨1273⟩, swap2, swap1,
    push2 ⟨6365⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [ammSwap0TransferDecodeMem, ammMintReturndataRounded]
      using rd6365⟩

theorem ammSwap0X_transferDecodeShortReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hshort : o.size < 32)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6365⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1273⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  have hcheck := solcDecodeEndLenCheckShort_128_32 hshort
  have rd6374 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero]
  have rd5396 := evm_run rd6374 with [
    push2 ⟨6386⟩, jumpiNT (by rw [hcheck]; decide),
    push2 ⟨6385⟩, push2 ⟨5396⟩, jump (by jump_dest)]
  exact evm_run rd5396 with [
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammSwap0X_transferDecodeWord
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6365⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1273⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6323⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6359⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6399⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1273⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k' C' := by
  have hhi : o.size < UInt256.size :=
    lt_trans hbound (by norm_num [UInt256.size])
  have hcheck := solcDecodeEndLenCheckOk_128_32 hlo
    (by omega : o.size < 2 ^ 255)
  have rd6386 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6386⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6345 := evm_run rd6386 with [
    jumpdest, push0, push2 ⟨6399⟩, dup5, dup3, dup6, add,
    push2 ⟨6345⟩, jump (by jump_dest)]
  let v : UInt256 := UInt256.ofNat
    (fromByteArrayBigEndian (o.extract 0 32))
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (ammSwap0TransferDecodeMem I o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammSwap0TransferDecodeMem I o).readWithPadding 128 32))) =
        v := by
    simpa only [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      ammSwap0TransferDecodeMem_read128 I hlo hhi, v] using
      (mloadValue_eq_readWithPadding_of_lt_size
        (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7) ⟨128⟩ 196
        (ammSwap0TransferDecodeMem_size I hhi)
        (by decide) (by decide))
  have rd6348 := evm_run rd6345 with [jumpdest, push0, dup2]
  have rd6349 := evm_run rd6348 with [
    raw mload 0 v (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  have rd6323 := evm_run rd6349 with [
    swap1, pop, push2 ⟨6359⟩, dup2, push2 ⟨6323⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v] using rd6323⟩

theorem ammSwap0X_transferDecodeInvalidReverts
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hbad : UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) ≠
      UInt256.isZero (UInt256.isZero
        (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))))
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6323⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6359⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6399⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1273⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  exact RD.ammBurnBoolCheckInvalid rd hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammSwap0X_transferDecodeOk
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcanon : UInt256.ofNat
        (fromByteArrayBigEndian (o.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat
        (fromByteArrayBigEndian (o.extract 0 32)) = ⟨1⟩)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6323⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6359⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6399⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨1273⟩,
        ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨1275⟩
      [ammSwap0ToWord I, ammSwap0AmountWord I, ⟨234⟩, sel]
      (ammSwap0TransferDecodeMem I o) (UInt256.ofNat 7)
      o acc k' C' := by
  obtain ⟨_, _, rd6359⟩ := RD.ammBurnBoolCheckOk rd hcanon
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6399 := evm_run rd6359 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1273 := evm_run rd6399 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd1273 with [jumpdest, pop]⟩

end Benchmarks.ActAmm
