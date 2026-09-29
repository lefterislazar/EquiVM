import Benchmarks.ActAmm4.SwapGuardTrace
import Benchmarks.ActAmm4.BurnTransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_transfer0TokenAddress
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2501⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2558⟩
      [amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have rd1122 := evm_run rd with [
    jumpdest, push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd1123⟩ := rd1122.sload
    (by native_decide) (by evm_ov)
  have rd1174 := evm_run rd1123 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken0Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd1174⟩

theorem amm4SwapX_transfer0SelectorMem
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2558⟩
      [amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2580⟩
      [⟨128⟩, amm4SwapToWord I, amm4SwapAmount0Word I,
        ⟨3077966991⟩, amm4MintToken0Word σ I,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      amm4BurnTransferSelectorMem (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k' C' := by
  have rd1183 := evm_run rd with [
    push4 ⟨3077966991⟩, dup5, dup4, push1 ⟨64⟩]
  have rd1184 := evm_run rd1183 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue
        (by rw [solcFreePtrMem_size]; decide)
        (by decide) solcFreePtrMem_read64)
      (by decide) (by evm_ov)]
  have rd1195 := evm_run rd1184 with [
    dup4, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd1196 := evm_run rd1195 with [
    raw mstore 6
      (amm4BurnTransferSelectorWord.toByteArray.write 0
        solcFreePtrMem 128 32)
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [amm4BurnTransferSelectorMem, amm4BurnTransferSelectorWord]
      using rd1196⟩

noncomputable def amm4SwapTransfer0CalldataMem (I : ExecutionEnv) : ByteArray :=
  (amm4SwapToWord I).toByteArray.write 0
    ((amm4SwapAmount0Word I).toByteArray.write 0
      amm4BurnTransferSelectorMem 132 32) 164 32

theorem amm4SwapTransfer0Arg0Mem_size (I : ExecutionEnv) :
    ((amm4SwapAmount0Word I).toByteArray.write 0
      amm4BurnTransferSelectorMem 132 32).size = 164 := by
  exact toByteArray_write32_size_of_le amm4BurnTransferSelectorMem
    (amm4SwapAmount0Word I) 132 160 164
    amm4BurnTransferSelectorMem_size
    (by rw [amm4BurnTransferSelectorMem_size]; omega) (by omega)

theorem amm4SwapTransfer0CalldataMem_size (I : ExecutionEnv) :
    (amm4SwapTransfer0CalldataMem I).size = 196 := by
  unfold amm4SwapTransfer0CalldataMem
  exact toByteArray_write32_size_of_le
    ((amm4SwapAmount0Word I).toByteArray.write 0
      amm4BurnTransferSelectorMem 132 32)
    (amm4SwapToWord I) 164 164 196
    (amm4SwapTransfer0Arg0Mem_size I)
    (by rw [amm4SwapTransfer0Arg0Mem_size]) (by omega)

theorem amm4SwapTransfer0CalldataMem_read64 (I : ExecutionEnv) :
    (amm4SwapTransfer0CalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4SwapTransfer0CalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [amm4SwapTransfer0Arg0Mem_size]) (by omega)]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [amm4BurnTransferSelectorMem_size]; omega) (by omega)]
  unfold amm4BurnTransferSelectorMem
  rw [toByteArray_write_read_below_of_gap amm4BurnTransferSelectorWord
    solcFreePtrMem 128 64 (by rw [solcFreePtrMem_size])
    (by omega) (by rw [solcFreePtrMem_size]; native_decide)]
  exact solcFreePtrMem_read64

theorem amm4BurnTransferSelectorMem_selector :
    amm4BurnTransferSelectorMem.extract 128 132 = transferSelector := by
  unfold amm4BurnTransferSelectorMem
  have hbase : solcFreePtrMem.size = 96 := solcFreePtrMem_size
  have hgap : 128 - solcFreePtrMem.size < USize.size := by
    rw [hbase]
    native_decide
  rw [toByteArray_write_eq amm4BurnTransferSelectorWord _ 128
    (by rw [hbase]; omega) hgap]
  have hprefix :
      (solcFreePtrMem ++
        ffi.ByteArray.zeroes (128 - solcFreePtrMem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hbase]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]),
    hprefix, show 128 - 128 = 0 from rfl,
    show 132 - 128 = 4 from rfl, toByteArray_eq_toBytesBE]
  native_decide

theorem amm4SwapTransfer0CalldataMem_read4 (I : ExecutionEnv) :
    (amm4SwapTransfer0CalldataMem I).readWithPadding 128 4 =
      transferSelector := by
  unfold amm4SwapTransfer0CalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [amm4SwapTransfer0Arg0Mem_size]) (by omega)
    (by rw [amm4SwapTransfer0Arg0Mem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [amm4BurnTransferSelectorMem_size]; omega) (by omega)
    (by rw [amm4BurnTransferSelectorMem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [readWithPadding_eq_extract' _ 128 4
    (by norm_num) (by norm_num)
    (by rw [amm4BurnTransferSelectorMem_size]; omega)]
  exact amm4BurnTransferSelectorMem_selector

theorem amm4SwapTransfer0CalldataMem_readAmount (I : ExecutionEnv) :
    (amm4SwapTransfer0CalldataMem I).readWithPadding 132 32 =
      (amm4SwapAmount0Word I).toByteArray := by
  unfold amm4SwapTransfer0CalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [amm4SwapTransfer0Arg0Mem_size]) (by omega)]
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [amm4BurnTransferSelectorMem_size]; omega)]
  rw [show (amm4SwapAmount0Word I).toByteArray.extract 0 32 =
      (amm4SwapAmount0Word I).toByteArray by
    rw [show 32 = (amm4SwapAmount0Word I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4SwapTransfer0CalldataMem_readTo (I : ExecutionEnv) :
    (amm4SwapTransfer0CalldataMem I).readWithPadding 164 32 =
      (amm4SwapToWord I).toByteArray := by
  unfold amm4SwapTransfer0CalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [amm4SwapTransfer0Arg0Mem_size])]
  rw [show (amm4SwapToWord I).toByteArray.extract 0 32 =
      (amm4SwapToWord I).toByteArray by
    rw [show 32 = (amm4SwapToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4SwapTransfer0CalldataMem_read (I : ExecutionEnv) :
    (amm4SwapTransfer0CalldataMem I).readWithPadding 128 68 =
      transferSelector ++ (amm4SwapAmount0Word I).toByteArray ++
        (amm4SwapToWord I).toByteArray := by
  rw [byteArray_readWithPadding_split _ 128 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [amm4SwapTransfer0CalldataMem_size])]
  rw [amm4SwapTransfer0CalldataMem_read4]
  rw [byteArray_readWithPadding_split _ 132 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [amm4SwapTransfer0CalldataMem_size])]
  rw [amm4SwapTransfer0CalldataMem_readAmount,
    amm4SwapTransfer0CalldataMem_readTo]
  exact ByteArray.append_assoc.symm

theorem amm4SwapTransfer0CalldataMem_encode (I : ExecutionEnv)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))] =
      some ((amm4SwapTransfer0CalldataMem I).readWithPadding 128 68) := by
  rw [amm4SwapTransfer0CalldataMem_read]
  have hq : EVM.word (amm4SwapAmount0Word I).toNat =
      amm4SwapAmount0Word I := u256_ofNat_toNat _
  have ht : EVM.word ↑(AccountAddress.ofUInt256 (amm4SwapToWord I)) =
      amm4SwapToWord I := by
    have h := valueToWord_address_ofNat_canonical
      (amm4SwapToWord I) hcanon
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat] at h
    simpa [valueToWord] using h
  simp [config, externalABI, ABI.encodeCallWithSelector?,
    ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
    ABI.encodeABIWord?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, uint256, uint256Int, addr, transferSelector,
    selectorBytes, hq, ht]
  have hlt : (amm4SwapAmount0Word I).toNat < EVM.twoPow 256 := by
    change (amm4SwapAmount0Word I).toNat < UInt256.size
    exact (amm4SwapAmount0Word I).val.isLt
  simp only [hlt, ite_true, Option.bind, bind]
  have hbytes :
      (EVM.Word.toBytesBE (amm4SwapAmount0Word I) ++
        EVM.Word.toBytesBE (amm4SwapToWord I)).toByteArray =
      (amm4SwapAmount0Word I).toByteArray ++
        (amm4SwapToWord I).toByteArray := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray (amm4SwapAmount0Word I),
      ← word_toBytesBE_toByteArray_eq_toByteArray (amm4SwapToWord I)]
    exact list_toByteArray_append _ _
  rw [hbytes]
  exact congrArg some ByteArray.append_assoc.symm

theorem amm4SwapX_transfer0Args
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2580⟩
      [⟨128⟩, amm4SwapToWord I, amm4SwapAmount0Word I,
        ⟨3077966991⟩, amm4MintToken0Word σ I,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      amm4BurnTransferSelectorMem (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2593⟩
      [⟨196⟩, ⟨3077966991⟩, amm4MintToken0Word σ I,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0CalldataMem I)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  let mem0 := amm4BurnTransferSelectorMem
  let mem1 := (amm4SwapAmount0Word I).toByteArray.write 0 mem0 132 32
  let mem2 := (amm4SwapToWord I).toByteArray.write 0 mem1 164 32
  have rd5944 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨2593⟩, swap3, swap2, swap1,
    push2 ⟨5944⟩, jump (by jump_dest)]
  have rd4841 := evm_run rd5944 with [
    jumpdest, push0, push1 ⟨64⟩, dup3, add, swap1, pop,
    push2 ⟨5963⟩, push0, dup4, add, dup6, push2 ⟨4841⟩,
    jump (by jump_dest), jumpdest, push2 ⟨4850⟩, dup2,
    push2 ⟨4677⟩, jump (by jump_dest)]
  have rd4850 := evm_run rd4841 with [
    raw amm4RoutineCleanupUint256 (by jump_dest) (by evm_ov)]
  have rd5963 := evm_run rd4850 with [
    jumpdest, dup3,
    raw mstore 3 mem1 (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd5355 := evm_run rd5963 with [
    jumpdest, push2 ⟨5976⟩, push1 ⟨32⟩, dup4, add,
    dup5, push2 ⟨5355⟩, jump (by jump_dest)]
  have rd4618 := evm_run rd5355 with [
    jumpdest, push2 ⟨5364⟩, dup2, push2 ⟨4618⟩,
    jump (by jump_dest)]
  have rd4587 := evm_run rd4618 with [
    jumpdest, push0, push2 ⟨4628⟩, dup3, push2 ⟨4587⟩,
    jump (by jump_dest)]
  have rd4628 := evm_run rd4587 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd5364 := evm_run rd4628 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd5364' := rd5364
  rw [solcAddrMask_clean hcanon] at rd5364'
  have rd5976 := evm_run rd5364' with [
    jumpdest, dup3,
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd1209 := evm_run rd5976 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [mem0, mem1, mem2, amm4SwapTransfer0CalldataMem]
      using rd1209⟩

theorem amm4SwapX_transfer0CallFrame
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2593⟩
      [⟨196⟩, ⟨3077966991⟩, amm4MintToken0Word σ I,
        amm4SwapToWord I, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0CalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2606⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0CalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4SwapTransfer0CalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4SwapTransfer0CalldataMem I).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [amm4SwapTransfer0CalldataMem_size]; decide)
      (by decide) (amm4SwapTransfer0CalldataMem_read64 I)
  have rd1215 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd1216 := evm_run rd1215 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd1222 := evm_run rd1216 with [
    dup1, dup4, sub, dup2, push0, dup8, gas]
  obtain ⟨gasWord, rd1222'⟩ := rd1222
  exact ⟨gasWord, _, _, by
    simpa only [show (⟨196⟩ : UInt256) - ⟨128⟩ = ⟨68⟩
      from by decide] using rd1222'⟩

end Benchmarks.ActAmm4
