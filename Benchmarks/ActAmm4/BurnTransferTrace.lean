import Benchmarks.ActAmm4.BurnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

/-- The first transfer uses the token address read after both storage debits. -/
theorem amm4BurnX_token0Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3946⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4002⟩
      [amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3950 := evm_run rd with [push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd3951⟩ := rd3950.sload (by native_decide) (by evm_ov)
  have rd4002 := evm_run rd3951 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken0Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd4002⟩

abbrev amm4BurnTransferSelectorWord : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (⟨4294967295⟩ : UInt256) ⟨3077966991⟩) ⟨224⟩

noncomputable def amm4BurnTransferSelectorMem : ByteArray :=
  amm4BurnTransferSelectorWord.toByteArray.write 0 solcFreePtrMem 128 32

theorem amm4BurnTransferSelectorMem_size :
    amm4BurnTransferSelectorMem.size = 160 := by
  unfold amm4BurnTransferSelectorMem
  exact toByteArray_write32_size_of_ge solcFreePtrMem
    amm4BurnTransferSelectorWord 128 96 160 solcFreePtrMem_size
    (by omega) (by native_decide) (by omega)

noncomputable def amm4BurnToken0SelectorMem (I : ExecutionEnv) : ByteArray :=
  amm4BurnTransferSelectorWord.toByteArray.write 0
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) 128 32

noncomputable def amm4BurnToken0CalldataMem (I : ExecutionEnv) (q0 : UInt256) :
    ByteArray :=
  (amm4BurnToWord I).toByteArray.write 0
    (q0.toByteArray.write 0 (amm4BurnToken0SelectorMem I) 132 32) 164 32

theorem amm4BurnToken0SelectorMem_size (I : ExecutionEnv) :
    (amm4BurnToken0SelectorMem I).size = 160 := by
  unfold amm4BurnToken0SelectorMem
  exact toByteArray_write32_size_of_ge
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
    amm4BurnTransferSelectorWord 128 96 160
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (by omega) (by native_decide) (by omega)

theorem amm4BurnToken0Arg0Mem_size (I : ExecutionEnv) (q0 : UInt256) :
    (q0.toByteArray.write 0 (amm4BurnToken0SelectorMem I) 132 32).size = 164 := by
  exact toByteArray_write32_size_of_le (amm4BurnToken0SelectorMem I) q0
    132 160 164 (amm4BurnToken0SelectorMem_size I)
    (by rw [amm4BurnToken0SelectorMem_size]; omega) (by omega)

theorem amm4BurnToken0CalldataMem_size (I : ExecutionEnv) (q0 : UInt256) :
    (amm4BurnToken0CalldataMem I q0).size = 196 := by
  unfold amm4BurnToken0CalldataMem
  exact toByteArray_write32_size_of_le
    (q0.toByteArray.write 0 (amm4BurnToken0SelectorMem I) 132 32)
    (amm4BurnToWord I) 164 164 196
    (amm4BurnToken0Arg0Mem_size I q0)
    (by rw [amm4BurnToken0Arg0Mem_size]) (by omega)

theorem amm4BurnToken0CalldataMem_read64 (I : ExecutionEnv) (q0 : UInt256) :
    (amm4BurnToken0CalldataMem I q0).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4BurnToken0CalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0Arg0Mem_size]) (by omega)]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0SelectorMem_size]; omega) (by omega)]
  unfold amm4BurnToken0SelectorMem
  rw [toByteArray_write_read_below_of_gap amm4BurnTransferSelectorWord
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
    128 64 (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size])
    (by omega) (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size]; native_decide)]
  exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem amm4BurnToken0SelectorMem_selector (I : ExecutionEnv) :
    (amm4BurnToken0SelectorMem I).extract 128 132 = transferSelector := by
  unfold amm4BurnToken0SelectorMem
  have hbase :
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hgap :
      128 - (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size <
        USize.size := by
    rw [hbase]
    native_decide
  rw [toByteArray_write_eq amm4BurnTransferSelectorWord _ 128
    (by rw [hbase]; omega) hgap]
  have hprefix :
      ((twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) ++
        ffi.ByteArray.zeroes
          (128 - (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size)).size =
        128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hbase]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem amm4BurnToken0CalldataMem_read4 (I : ExecutionEnv) (q0 : UInt256) :
    (amm4BurnToken0CalldataMem I q0).readWithPadding 128 4 =
      transferSelector := by
  unfold amm4BurnToken0CalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0Arg0Mem_size]) (by omega)
    (by rw [amm4BurnToken0Arg0Mem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0SelectorMem_size]; omega) (by omega)
    (by rw [amm4BurnToken0SelectorMem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
    (by rw [amm4BurnToken0SelectorMem_size]; omega)]
  exact amm4BurnToken0SelectorMem_selector I

theorem amm4BurnToken0CalldataMem_readAmount (I : ExecutionEnv)
    (q0 : UInt256) :
    (amm4BurnToken0CalldataMem I q0).readWithPadding 132 32 =
      q0.toByteArray := by
  unfold amm4BurnToken0CalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0Arg0Mem_size]) (by omega)]
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0SelectorMem_size]; omega)]
  rw [show q0.toByteArray.extract 0 32 = q0.toByteArray by
    rw [show 32 = q0.toByteArray.size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4BurnToken0CalldataMem_readTo (I : ExecutionEnv)
    (q0 : UInt256) :
    (amm4BurnToken0CalldataMem I q0).readWithPadding 164 32 =
      (amm4BurnToWord I).toByteArray := by
  unfold amm4BurnToken0CalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0Arg0Mem_size])]
  rw [show (amm4BurnToWord I).toByteArray.extract 0 32 =
      (amm4BurnToWord I).toByteArray by
    rw [show 32 = (amm4BurnToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4BurnToken0CalldataMem_read (I : ExecutionEnv) (q0 : UInt256) :
    (amm4BurnToken0CalldataMem I q0).readWithPadding 128 68 =
      transferSelector ++ q0.toByteArray ++ (amm4BurnToWord I).toByteArray := by
  rw [byteArray_readWithPadding_split _ 128 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [amm4BurnToken0CalldataMem_size])]
  rw [amm4BurnToken0CalldataMem_read4]
  rw [byteArray_readWithPadding_split _ 132 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [amm4BurnToken0CalldataMem_size])]
  rw [amm4BurnToken0CalldataMem_readAmount,
    amm4BurnToken0CalldataMem_readTo]
  exact ByteArray.append_assoc.symm

theorem amm4BurnToken0CalldataMem_encode (I : ExecutionEnv) (q0 : UInt256)
    (hamount : q0.toNat < UInt256.size)
    (hto : (amm4BurnToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat q0.toNat), .address (AccountAddress.ofUInt256
        (amm4BurnToWord I))] =
      some ((amm4BurnToken0CalldataMem I q0).readWithPadding 128 68) := by
  rw [amm4BurnToken0CalldataMem_read]
  have hq : EVM.word q0.toNat = q0 := u256_ofNat_toNat q0
  have ht : EVM.word ↑(AccountAddress.ofUInt256 (amm4BurnToWord I)) =
      amm4BurnToWord I := by
    have h := valueToWord_address_ofNat_canonical (amm4BurnToWord I) hto
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat] at h
    simpa [valueToWord] using h
  simp [config, externalABI, ABI.encodeCallWithSelector?,
    ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
    ABI.encodeABIWord?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, uint256, uint256Int, addr, transferSelector,
    selectorBytes, hq, ht]
  have hlt : q0.toNat < EVM.twoPow 256 := by
    change q0.toNat < EVM.twoPow 256 at hamount
    exact hamount
  simp only [hlt, ite_true]
  simp only [Option.bind, bind]
  have hbytes :
      (EVM.Word.toBytesBE q0 ++
        EVM.Word.toBytesBE (amm4BurnToWord I)).toByteArray =
      q0.toByteArray ++ (amm4BurnToWord I).toByteArray := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray q0,
      ← word_toBytesBE_toByteArray_eq_toByteArray (amm4BurnToWord I)]
    exact list_toByteArray_append _ _
  rw [hbytes]
  exact congrArg some (ByteArray.append_assoc.symm)

theorem amm4BurnX_token0SelectorMem {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4002⟩
      [amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4024⟩
      [⟨128⟩, amm4BurnToWord I, q0, ⟨3077966991⟩,
        amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0SelectorMem I)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  have rd4012 := evm_run rd with [
    push4 ⟨3077966991⟩, dup4, dup6, push1 ⟨64⟩]
  have hmemSize :
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hmemRead :
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have rd4013 := evm_run rd4012 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hmemSize]; decide)
        (by decide) hmemRead) (by decide) (by evm_ov)]
  have rd4023 := evm_run rd4013 with [
    dup4, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd4024 := evm_run rd4023 with [
    raw mstore 6
      (amm4BurnTransferSelectorWord.toByteArray.write 0
        (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) 128 32)
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [amm4BurnToken0SelectorMem, amm4BurnTransferSelectorWord] using rd4024⟩

theorem amm4BurnX_token0TransferArgs {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4024⟩
      [⟨128⟩, amm4BurnToWord I, q0, ⟨3077966991⟩,
        amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0SelectorMem I)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hcanon : (amm4BurnToWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4037⟩
      [⟨196⟩, ⟨3077966991⟩, amm4MintToken0Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0CalldataMem I q0)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  let mem0 := amm4BurnTransferSelectorWord.toByteArray.write 0
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) 128 32
  let mem1 := q0.toByteArray.write 0 mem0 132 32
  let mem2 := (amm4BurnToWord I).toByteArray.write 0 mem1 164 32
  have rd5944 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨4037⟩, swap3, swap2, swap1,
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
  have hclean := solcAddrMask_clean hcanon
  have rd5364' := rd5364
  rw [hclean] at rd5364'
  have rd5976 := evm_run rd5364' with [
    jumpdest, dup3,
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd4037 := evm_run rd5976 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [mem0, mem1, mem2, amm4BurnToken0CalldataMem,
      amm4BurnToken0SelectorMem] using rd4037⟩

/-- The first `CALL` sends 68 ABI bytes and requests a 32-byte return. -/
theorem amm4BurnX_token0CallFrame {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4037⟩
      [⟨196⟩, ⟨3077966991⟩, amm4MintToken0Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4050⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4BurnToken0CalldataMem I q0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4BurnToken0CalldataMem I q0).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [amm4BurnToken0CalldataMem_size]; decide)
      (by decide) (amm4BurnToken0CalldataMem_read64 I q0)
  have rd4041 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd4042 := evm_run rd4041 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4050 := evm_run rd4042 with [
    dup1, dup4, sub, dup2, push0, dup8, gas]
  obtain ⟨gasWord, rd4050'⟩ := rd4050
  exact ⟨gasWord, _, _, by
    simpa only [show (⟨196⟩ : UInt256) - ⟨128⟩ = ⟨68⟩ from by decide]
      using rd4050'⟩

/-- The EVM transfer and the Solm transfer use the same external-call witness. -/
theorem amm4BurnX_token0Call {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hto : (amm4BurnToWord I).toNat < EVM.addressModulus)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4050⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : Nat),
      RD amm4Bytecode I g (initState cAstart gh bl σstart σ₀ g A I) ⟨4051⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨3077966991⟩ ::
          amm4MintToken0Word σ I :: q1 :: q0 :: amm4BurnToWord I ::
          amm4BurnLiquidityWord I :: ⟨521⟩ :: [sel])
        (o.write 0 (amm4BurnToken0CalldataMem I q0) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 7) o (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with accountMap := σ }
        (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))
        "transfer" 0
        [.int (Int.ofNat q0.toNat),
          .address (AccountAddress.ofUInt256 (amm4BurnToWord I))]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o)
        true ∧
      o.size < UInt256.size ∧ o.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd4050⟩ := hframe
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd4051, hosz⟩ :=
    RD.call rd4050 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68) 128 32) =
        UInt256.ofNat 7 := by native_decide
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [haw] using rd4051
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := amm4MintToken0Word σ I)
      (mem := amm4BurnToken0CalldataMem I q0)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (amm4BurnToken0CalldataMem_encode I q0 q0.val.isLt hto) ?_
    simpa [initState, hperm] using hΘ
  · have hinputSize :
        ((amm4BurnToken0CalldataMem I q0).readWithPadding 128 68).size = 68 := by
      rw [readWithPadding_eq_extract' _ 128 68 (by norm_num) (by norm_num)
        (by rw [amm4BurnToken0CalldataMem_size])]
      rw [ByteArray.size_extract, amm4BurnToken0CalldataMem_size]
      omega
    have hbound :
        ((amm4BurnToken0CalldataMem I q0).readWithPadding 128 68).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (amm4MintToken0Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (amm4MintToken0Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((amm4BurnToken0CalldataMem I q0).readWithPadding 128 68)
      (I.depth + 1) I.header true (by simpa [initState, hperm] using hΘ) hbound

/-- A failed first token transfer bubbles its return data and reverts. -/
theorem amm4BurnX_token0CallFailed {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4051⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd4058 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨4065⟩, jumpiNT (by decide)]
  have rd4061 := evm_run rd4058 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd4062 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd4061 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd4064 := evm_run rd4062 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd4064 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem amm4BurnX_token0DepthRevert {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 gasWord : UInt256} {k C : Nat}
    (hdepth : I.depth = 1024)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4050⟩
      [gasWord, amm4MintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  obtain ⟨_, _, rd4051⟩ := RD.callDepthLimit rd
    (by native_decide) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68) 128 32) =
        UInt256.ofNat 7 := by native_decide
  have rd4051' := rd4051
  simpa [haw, byteArray_write_len_zero] using
    (amm4BurnX_token0CallFailed rd4051'
      (by decide)
      (by simp only [List.length_cons, List.length_nil]; omega))

theorem amm4BurnX_token0CallSucceeded {cAstart gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {mem o : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4051⟩
      [⟨1⟩, ⟨196⟩, ⟨3077966991⟩, amm4MintToken0Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      mem aw o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4070⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨4065⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

noncomputable def amm4BurnToken0PostCallMem (I : ExecutionEnv)
    (q0 : UInt256) (o : ByteArray) : ByteArray :=
  o.write 0 (amm4BurnToken0CalldataMem I q0) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem amm4BurnToken0PostCallMem_size_short (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hshort : o.size < 32) :
    (amm4BurnToken0PostCallMem I q0 o).size = 196 := by
  unfold amm4BurnToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide)
      hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero, amm4BurnToken0CalldataMem_size]
  · rw [write_eq_gen o (amm4BurnToken0CalldataMem I q0) 128 o.size
      hzero le_rfl (by rw [amm4BurnToken0CalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, amm4BurnToken0CalldataMem_size]
    omega

theorem amm4BurnToken0PostCallMem_size_long (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4BurnToken0PostCallMem I q0 o).size = 196 := by
  unfold amm4BurnToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  rw [write_eq_gen o (amm4BurnToken0CalldataMem I q0) 128 32
    (by omega) hlo (by rw [amm4BurnToken0CalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, amm4BurnToken0CalldataMem_size]
  omega

theorem amm4BurnToken0PostCallMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hhi : o.size < UInt256.size) :
    (amm4BurnToken0PostCallMem I q0 o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  by_cases hshort : o.size < 32
  · unfold amm4BurnToken0PostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size)
        (by decide) hshort (by omega)
    rw [hlen]
    by_cases hzero : o.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact amm4BurnToken0CalldataMem_read64 I q0
    · rw [write_read_below_gen_extend o (amm4BurnToken0CalldataMem I q0)
        128 o.size 64 hzero le_rfl
        (by rw [amm4BurnToken0CalldataMem_size]; omega) (by omega)]
      exact amm4BurnToken0CalldataMem_read64 I q0
  · have hlo : 32 ≤ o.size := by omega
    unfold amm4BurnToken0PostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
        (by decide) hlo hhi
    rw [hlen]
    rw [write_read_below_gen_extend o (amm4BurnToken0CalldataMem I q0)
      128 32 64 (by omega) hlo
      (by rw [amm4BurnToken0CalldataMem_size]; omega) (by omega)]
    exact amm4BurnToken0CalldataMem_read64 I q0

theorem amm4BurnToken0PostCallMem_read128 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4BurnToken0PostCallMem I q0 o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold amm4BurnToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  exact write32_read_back o (amm4BurnToken0CalldataMem I q0) 128
    (by omega) (by rw [amm4BurnToken0CalldataMem_size]; omega)

noncomputable def amm4BurnToken0DecodeMem (I : ExecutionEnv)
    (q0 : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o)).toByteArray.write 0
    (amm4BurnToken0PostCallMem I q0 o) 64 32

theorem amm4BurnToken0DecodeMem_size (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hhi : o.size < UInt256.size) :
    (amm4BurnToken0DecodeMem I q0 o).size = 196 := by
  have hbase : (amm4BurnToken0PostCallMem I q0 o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact amm4BurnToken0PostCallMem_size_short I q0 hshort
    · exact amm4BurnToken0PostCallMem_size_long I q0 (by omega) hhi
  unfold amm4BurnToken0DecodeMem
  exact toByteArray_write32_size_of_le
    (amm4BurnToken0PostCallMem I q0 o)
    (UInt256.add ⟨128⟩ (amm4MintReturndataRounded o))
    64 196 196 hbase (by rw [hbase]; omega) (by omega)

theorem amm4BurnToken0DecodeMem_read128 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (amm4BurnToken0DecodeMem I q0 o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold amm4BurnToken0DecodeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [amm4BurnToken0PostCallMem_size_long I q0 hlo hhi]; omega)
    (by omega)
    (by rw [amm4BurnToken0PostCallMem_size_long I q0 hlo hhi]; omega)]
  exact amm4BurnToken0PostCallMem_read128 I q0 hlo hhi

theorem amm4BurnX_token0ToDecoder {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hhi : o.size < UInt256.size)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4070⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0PostCallMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4101⟩,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k' C' := by
  have hmemSize : (amm4BurnToken0PostCallMem I q0 o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact amm4BurnToken0PostCallMem_size_short I q0 hshort
    · exact amm4BurnToken0PostCallMem_size_long I q0 (by omega) hhi
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4BurnToken0PostCallMem I q0 o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4BurnToken0PostCallMem I q0 o).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide)
      (amm4BurnToken0PostCallMem_read64 I q0 hhi)
  have rd4072 := evm_run rd with [push1 ⟨64⟩]
  have rd4073 := evm_run rd4072 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4087 := evm_run rd4073 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd4088 := evm_run rd4087 with [
    raw mstore 0 (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd6025 := evm_run rd4088 with [
    pop, dup2, add, swap1, push2 ⟨4101⟩, swap2, swap1,
    push2 ⟨6025⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [amm4BurnToken0DecodeMem, amm4MintReturndataRounded] using rd6025⟩

theorem amm4BurnX_token0DecodeShortReverts {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hshort : o.size < 32)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4101⟩,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
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

theorem amm4BurnX_token0DecodeWord {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6025⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4101⟩,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6059⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4101⟩,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k' C' := by
  have hhi : o.size < UInt256.size := lt_trans hbound (by norm_num [UInt256.size])
  have hcheck := solcDecodeEndLenCheckOk_128_32 hlo (by omega : o.size < 2 ^ 255)
  have rd6046 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6046⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6005 := evm_run rd6046 with [
    jumpdest, push0, push2 ⟨6059⟩, dup5, dup3, dup6, add,
    push2 ⟨6005⟩, jump (by jump_dest)]
  let v : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (amm4BurnToken0DecodeMem I q0 o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4BurnToken0DecodeMem I q0 o).readWithPadding 128 32))) =
        v := by
    simpa only [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      amm4BurnToken0DecodeMem_read128 I q0 hlo hhi, v] using
      (mloadValue_eq_readWithPadding_of_lt_size
        (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) ⟨128⟩ 196
        (amm4BurnToken0DecodeMem_size I q0 hhi) (by decide) (by decide))
  have rd6008 := evm_run rd6005 with [jumpdest, push0, dup2]
  have rd6009 := evm_run rd6008 with [
    raw mload 0 v (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  have rd5983 := evm_run rd6009 with [
    swap1, pop, push2 ⟨6019⟩, dup2, push2 ⟨5983⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v] using rd5983⟩

/-- Shared ABI bool cleanup, followed by Solidity's canonicality comparison. -/
theorem RD.amm4BurnBoolCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {v ret : UInt256} {R : List UInt256}
    {mem o : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode ee g s0 ⟨5983⟩ (v :: ret :: R)
      mem aw o acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ⟨5995⟩
      (UInt256.eq v (UInt256.isZero (UInt256.isZero v)) :: v :: ret :: R)
      mem aw o acc k' C' := by
  have rd4790 := evm_run rd with [
    jumpdest, push2 ⟨5992⟩, dup2, push2 ⟨4790⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd5992⟩ := RD.amm4RoutineBoolCleanup rd4790
    (by jump_dest) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd5992 with [jumpdest, dup2, eq]⟩

theorem RD.amm4BurnBoolCheckInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {v ret : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode ee g s0 ⟨5983⟩ (v :: ret :: R)
      mem aw o acc k C)
    (hbad : v ≠ UInt256.isZero (UInt256.isZero v))
    (hov : R.length + 10 ≤ 1024) :
    RDrev amm4Bytecode g s0 := by
  obtain ⟨_, _, rd5995⟩ := RD.amm4BurnBoolCheck rd hov
  have hneq : UInt256.eq v (UInt256.isZero (UInt256.isZero v)) = ⟨0⟩ :=
    u256_eq_of_ne hbad
  exact evm_run rd5995 with [
    push2 ⟨6002⟩, jumpiNT (by rw [hneq]),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem RD.amm4BurnBoolCheckOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {v ret : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD amm4Bytecode ee g s0 ⟨5983⟩ (v :: ret :: R)
      mem aw o acc k C)
    (hcanon : v = ⟨0⟩ ∨ v = ⟨1⟩)
    (hret : (D_J amm4Bytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD amm4Bytecode ee g s0 ret R mem aw o acc k' C' := by
  obtain ⟨_, _, rd5995⟩ := RD.amm4BurnBoolCheck rd hov
  have hnorm : v = UInt256.isZero (UInt256.isZero v) := by
    rcases hcanon with hzero | hone
    · subst v
      decide
    · subst v
      decide
  have heq : UInt256.eq v (UInt256.isZero (UInt256.isZero v)) = ⟨1⟩ := by
    rw [← hnorm]
    exact u256_eq_refl v
  exact ⟨_, _, evm_run rd5995 with [
    push2 ⟨6002⟩, jumpiT (by rw [heq]; decide) (by jump_dest),
    jumpdest, pop, jump hret]⟩

theorem amm4BoolNormalized_canonical (v : UInt256) :
    v = UInt256.isZero (UInt256.isZero v) ↔ v = ⟨0⟩ ∨ v = ⟨1⟩ := by
  constructor
  · intro hnorm
    by_cases hz : v = ⟨0⟩
    · exact Or.inl hz
    · right
      have hiz : UInt256.isZero v = ⟨0⟩ := isZero_eq_zero_of_ne hz
      rw [hiz] at hnorm
      simpa using hnorm
  · intro hcanon
    rcases hcanon with hz | ho
    · subst v
      decide
    · subst v
      decide

theorem amm4BurnX_token0DecodeInvalidReverts {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
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
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4101⟩,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    RDrev amm4Bytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  exact RD.amm4BurnBoolCheckInvalid rd hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem amm4BurnX_token0DecodeOk {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcanon : UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) = ⟨1⟩)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5983⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6019⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6059⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4101⟩,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4103⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k' C' := by
  obtain ⟨_, _, rd6019⟩ := RD.amm4BurnBoolCheckOk rd hcanon
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6059 := evm_run rd6019 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd4101 := evm_run rd6059 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd4101 with [jumpdest, pop]⟩

/-- The second transfer reads token1 after the first external call. -/
theorem amm4BurnX_token1Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4103⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      mem aw o (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4159⟩
      [amm4MintToken1Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      mem aw o (cA, σ) k' C' := by
  have rd4107 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd4108⟩ := rd4107.sload (by native_decide) (by evm_ov)
  have rd4159 := evm_run rd4108 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken1Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd4159⟩

theorem amm4BurnToken0DecodeMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hhi : o.size < UInt256.size) :
    (amm4BurnToken0DecodeMem I q0 o).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o) := by
  unfold amm4BurnToken0DecodeMem
  exact toByteArray_write32_read_back _ _ _ (by
    by_cases hshort : o.size < 32
    · rw [amm4BurnToken0PostCallMem_size_short I q0 hshort]
      omega
    · rw [amm4BurnToken0PostCallMem_size_long I q0 (by omega) hhi]
      omega)

noncomputable def amm4BurnToken1SelectorMem (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) : ByteArray :=
  amm4BurnTransferSelectorWord.toByteArray.write 0
    (amm4BurnToken0DecodeMem I q0 o0)
    (amm4MintToken0FreePtr o0).toNat 32

def amm4BurnToken1SelectorWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 7 (amm4MintToken0FreePtr o0).toNat 32)

theorem amm4BurnToken1SelectorMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4BurnToken1SelectorMem I q0 o0).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o0) := by
  unfold amm4BurnToken1SelectorMem
  have hptr : 160 ≤ (amm4MintToken0FreePtr o0).toNat :=
    (amm4MintToken0FreePtr_bounds o0 hlo hbound).1
  have hhi : o0.size < UInt256.size := lt_trans hbound
    (by norm_num [UInt256.size])
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [amm4BurnToken0DecodeMem_size I q0 hhi]; omega)
    (by omega)]
  exact amm4BurnToken0DecodeMem_read64 I q0 hhi

theorem amm4BurnX_token1SelectorMem {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4159⟩
      [amm4MintToken1Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken0DecodeMem I q0 o0) (UInt256.ofNat 7)
      o0 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4181⟩
      [amm4MintToken0FreePtr o0, amm4BurnToWord I, q1,
        ⟨3077966991⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken1SelectorMem I q0 o0)
      (amm4BurnToken1SelectorWords o0) o0 (cA, σ) k' C' := by
  have hhi : o0.size < UInt256.size :=
    lt_trans hbound (by norm_num [UInt256.size])
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4BurnToken0DecodeMem I q0 o0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4BurnToken0DecodeMem I q0 o0).readWithPadding 64 32))) =
        amm4MintToken0FreePtr o0 :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7)
      (v := amm4MintToken0FreePtr o0)
      (by rw [amm4BurnToken0DecodeMem_size I q0 hhi]; decide)
      (by decide)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using amm4BurnToken0DecodeMem_read64 I q0 hhi)
  have rd4168 := evm_run rd with [
    push4 ⟨3077966991⟩, dup3, dup6, push1 ⟨64⟩]
  have rd4169 := evm_run rd4168 with [
    raw mload 0 (amm4MintToken0FreePtr o0) (UInt256.ofNat 7)
      (by native_decide) mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4180 := evm_run rd4169 with [
    dup4, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := amm4BurnToken1SelectorWords o0
  have rd4181 := RD.mstore
    (Cₘ awSel - Cₘ (UInt256.ofNat 7))
    (amm4BurnToken1SelectorMem I q0 o0) awSel rd4180 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awSel, amm4BurnToken1SelectorWords,
        show (UInt256.ofNat 7).toNat = 7 from by decide])
    (by unfold amm4BurnToken1SelectorMem; rfl)
    (by simp [awSel, amm4BurnToken1SelectorWords,
      show (UInt256.ofNat 7).toNat = 7 from by decide])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4BurnTransferSelectorWord] using rd4181⟩

theorem amm4BurnToken0FreePtr_add36_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o + ⟨36⟩).toNat =
      (amm4MintToken0FreePtr o).toNat + 36 := by
  rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    Nat.mod_eq_of_lt]
  have hptr : (amm4MintToken0FreePtr o).toNat ≤ o.size + 159 := by
    simpa only [amm4MintToken0FreePtr] using
      (amm4MintToken0FreePtr_bounds o hlo hbound).2
  have hcap : 2 ^ 138 + 195 < UInt256.size := by norm_num [UInt256.size]
  omega

noncomputable def amm4BurnToken1AmountMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray) : ByteArray :=
  q1.toByteArray.write 0 (amm4BurnToken1SelectorMem I q0 o0)
    (amm4MintToken0FreePtr o0 + ⟨4⟩).toNat 32

noncomputable def amm4BurnToken1CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray) : ByteArray :=
  (amm4BurnToWord I).toByteArray.write 0
    (amm4BurnToken1AmountMem I q0 q1 o0)
    (amm4MintToken0FreePtr o0 + ⟨36⟩).toNat 32

def amm4BurnToken1AmountWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4BurnToken1SelectorWords o0).toNat
    (amm4MintToken0FreePtr o0 + ⟨4⟩).toNat 32)

def amm4BurnToken1CalldataWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4BurnToken1AmountWords o0).toNat
    (amm4MintToken0FreePtr o0 + ⟨36⟩).toNat 32)

theorem amm4BurnToken1SelectorMem_size (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) :
    (amm4MintToken0FreePtr o0).toNat + 32 ≤
      (amm4BurnToken1SelectorMem I q0 o0).size := by
  unfold amm4BurnToken1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4BurnToken1AmountMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o0).toNat + 36 ≤
      (amm4BurnToken1AmountMem I q0 q1 o0).size := by
  unfold amm4BurnToken1AmountMem
  rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4BurnToken1CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o0).toNat + 68 ≤
      (amm4BurnToken1CalldataMem I q0 q1 o0).size := by
  unfold amm4BurnToken1CalldataMem
  rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4BurnToken1SelectorMem_read4 (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) :
    (amm4BurnToken1SelectorMem I q0 o0).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 4 = transferSelector := by
  unfold amm4BurnToken1SelectorMem
  have h := toByteArray_write_read_window_no_gap amm4BurnTransferSelectorWord
    (amm4BurnToken0DecodeMem I q0 o0)
    (amm4MintToken0FreePtr o0).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : amm4BurnTransferSelectorWord.toByteArray.extract 0 4 =
      transferSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4BurnToken1CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4BurnToken1CalldataMem I q0 q1 o0).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o0) := by
  have hptr := (amm4MintToken0FreePtr_bounds o0 hlo hbound).1
  change 160 ≤ (amm4MintToken0FreePtr o0).toNat at hptr
  unfold amm4BurnToken1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]; omega)]
  unfold amm4BurnToken1AmountMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1SelectorMem_size I q0 o0
      rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)
    (by rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]; omega)]
  exact amm4BurnToken1SelectorMem_read64 I q0 hlo hbound

theorem amm4BurnToken1CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4BurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 4 = transferSelector := by
  have hptr := (amm4MintToken0FreePtr_bounds o0 hlo hbound).1
  change 160 ≤ (amm4MintToken0FreePtr o0).toNat at hptr
  unfold amm4BurnToken1CalldataMem
  rw [write32_read_below_len _ _ _ _ 4 (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]; omega)
    (by
      have hs := amm4BurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      omega)
    (by norm_num) (by norm_num)]
  unfold amm4BurnToken1AmountMem
  rw [write32_read_below_len _ _ _ _ 4 (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1SelectorMem_size I q0 o0
      rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)
    (by rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound])
    (by
      have hs := amm4BurnToken1SelectorMem_size I q0 o0
      omega)
    (by norm_num) (by norm_num)]
  exact amm4BurnToken1SelectorMem_read4 I q0 o0

theorem amm4BurnToken1CalldataMem_readAmount (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4BurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0 + ⟨4⟩).toNat 32 =
      q1.toByteArray := by
  unfold amm4BurnToken1CalldataMem
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound,
      amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound])]
  unfold amm4BurnToken1AmountMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1SelectorMem_size I q0 o0
      rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)]
  rw [show q1.toByteArray.extract 0 32 = q1.toByteArray by
    rw [show 32 = q1.toByteArray.size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4BurnToken1CalldataMem_readTo (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4BurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0 + ⟨36⟩).toNat 32 =
      (amm4BurnToWord I).toByteArray := by
  unfold amm4BurnToken1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      have hs := amm4BurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)]
  rw [show (amm4BurnToWord I).toByteArray.extract 0 32 =
      (amm4BurnToWord I).toByteArray by
    rw [show 32 = (amm4BurnToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4BurnToken1CalldataMem_read (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4BurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 68 =
      transferSelector ++ q1.toByteArray ++
        (amm4BurnToWord I).toByteArray := by
  have hsize := amm4BurnToken1CalldataMem_size I q0 q1 o0 hlo hbound
  rw [byteArray_readWithPadding_split _ _ 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)]
  rw [amm4BurnToken1CalldataMem_read4 I q0 q1 hlo hbound]
  rw [byteArray_readWithPadding_split _ _ 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)]
  have hsum : (amm4MintToken0FreePtr o0).toNat + 4 + 32 =
      (amm4MintToken0FreePtr o0).toNat + 36 := by omega
  rw [hsum, ← amm4MintToken0FreePtr_add4_toNat o0 hlo hbound,
    ← amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound,
    amm4BurnToken1CalldataMem_readAmount I q0 q1 hlo hbound,
    amm4BurnToken1CalldataMem_readTo I q0 q1 hlo hbound]
  exact ByteArray.append_assoc.symm

theorem amm4BurnToken1CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hto : (amm4BurnToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat q1.toNat),
        .address (AccountAddress.ofUInt256 (amm4BurnToWord I))] =
      some ((amm4BurnToken1CalldataMem I q0 q1 o0).readWithPadding
        (amm4MintToken0FreePtr o0).toNat 68) := by
  rw [amm4BurnToken1CalldataMem_read I q0 q1 hlo hbound,
    ← amm4BurnToken0CalldataMem_read I q1]
  exact amm4BurnToken0CalldataMem_encode I q1 q1.val.isLt hto

theorem amm4BurnX_token1TransferArgs {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hcanon : (amm4BurnToWord I).toNat < EVM.addressModulus)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4181⟩
      [amm4MintToken0FreePtr o0, amm4BurnToWord I, q1,
        ⟨3077966991⟩, amm4MintToken1Word σ I,
        q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken1SelectorMem I q0 o0)
      (amm4BurnToken1SelectorWords o0) o0 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4194⟩
      [amm4MintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        amm4MintToken1Word σ I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (amm4BurnToken1CalldataMem I q0 q1 o0)
      (amm4BurnToken1CalldataWords o0) o0 (cA, σ) k' C' := by
  let fp := amm4MintToken0FreePtr o0
  let awSel := amm4BurnToken1SelectorWords o0
  let awAmount := amm4BurnToken1AmountWords o0
  let awFinal := amm4BurnToken1CalldataWords o0
  have rd5944 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨4194⟩, swap3, swap2, swap1,
    push2 ⟨5944⟩, jump (by jump_dest)]
  have rd4841 := evm_run rd5944 with [
    jumpdest, push0, push1 ⟨64⟩, dup3, add, swap1, pop,
    push2 ⟨5963⟩, push0, dup4, add, dup6, push2 ⟨4841⟩,
    jump (by jump_dest), jumpdest, push2 ⟨4850⟩, dup2,
    push2 ⟨4677⟩, jump (by jump_dest)]
  have rd4850 := evm_run rd4841 with [
    raw amm4RoutineCleanupUint256 (by jump_dest) (by evm_ov)]
  have rd5963pre := evm_run rd4850 with [jumpdest, dup3]
  have hoff : (⟨4⟩ : UInt256) + fp + ⟨0⟩ = fp + ⟨4⟩ := by
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) fp]
  have rd5963pre' := rd5963pre
  rw [hoff] at rd5963pre'
  have rd5963 := RD.mstore
    (Cₘ awAmount - Cₘ awSel)
    (amm4BurnToken1AmountMem I q0 q1 o0) awAmount
    rd5963pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awAmount, awSel, fp, amm4BurnToken1AmountWords])
    (by unfold amm4BurnToken1AmountMem; rfl)
    (by simp [awAmount, fp, amm4BurnToken1AmountWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5963done := evm_run rd5963 with [
    pop, pop, jump (by jump_dest)]
  have rd5355 := evm_run rd5963done with [
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
  have hclean := solcAddrMask_clean hcanon
  have rd5364' := rd5364
  rw [hclean] at rd5364'
  have rd5976pre := evm_run rd5364' with [jumpdest, dup3]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp]
    rw [u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  have rd5976pre' := rd5976pre
  rw [hend] at rd5976pre'
  have rd5976 := RD.mstore
    (Cₘ awFinal - Cₘ awAmount)
    (amm4BurnToken1CalldataMem I q0 q1 o0) awFinal
    rd5976pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awFinal, awAmount, fp, amm4BurnToken1CalldataWords])
    (by unfold amm4BurnToken1CalldataMem; rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5976done := evm_run rd5976 with [
    pop, pop, jump (by jump_dest)]
  have rd4194 := evm_run rd5976done with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  have hend2 : (⟨4⟩ : UInt256) + fp + ⟨64⟩ = fp + ⟨68⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp]
    rw [u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, hend2] using rd4194⟩

end Benchmarks.ActAmm4
