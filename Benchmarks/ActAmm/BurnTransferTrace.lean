import Benchmarks.ActAmm.BurnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

/-- The first transfer uses the token address read after both storage debits. -/
theorem ammBurnX_token0Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4759⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4815⟩
      [ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4763 := evm_run rd with [push1 ⟨3⟩, push0, swap1]
  obtain ⟨_, _, rd4764⟩ := rd4763.sload (by native_decide) (by evm_ov)
  have rd4815 := evm_run rd4764 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken0Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd4815⟩

abbrev ammBurnTransferSelectorWord : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (⟨4294967295⟩ : UInt256) ⟨3077966991⟩) ⟨224⟩

noncomputable def ammBurnTransferSelectorMem : ByteArray :=
  ammBurnTransferSelectorWord.toByteArray.write 0 solcFreePtrMem 128 32

theorem ammBurnTransferSelectorMem_size :
    ammBurnTransferSelectorMem.size = 160 := by
  unfold ammBurnTransferSelectorMem
  exact toByteArray_write32_size_of_ge solcFreePtrMem
    ammBurnTransferSelectorWord 128 96 160 solcFreePtrMem_size
    (by omega) (by native_decide) (by omega)

noncomputable def ammBurnToken0SelectorMem (I : ExecutionEnv) : ByteArray :=
  ammBurnTransferSelectorWord.toByteArray.write 0
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) 128 32

noncomputable def ammBurnToken0CalldataMem (I : ExecutionEnv) (q0 : UInt256) :
    ByteArray :=
  (ammBurnToWord I).toByteArray.write 0
    (q0.toByteArray.write 0 (ammBurnToken0SelectorMem I) 132 32) 164 32

theorem ammBurnToken0SelectorMem_size (I : ExecutionEnv) :
    (ammBurnToken0SelectorMem I).size = 160 := by
  unfold ammBurnToken0SelectorMem
  exact toByteArray_write32_size_of_ge
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
    ammBurnTransferSelectorWord 128 96 160
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (by omega) (by native_decide) (by omega)

theorem ammBurnToken0Arg0Mem_size (I : ExecutionEnv) (q0 : UInt256) :
    (q0.toByteArray.write 0 (ammBurnToken0SelectorMem I) 132 32).size = 164 := by
  exact toByteArray_write32_size_of_le (ammBurnToken0SelectorMem I) q0
    132 160 164 (ammBurnToken0SelectorMem_size I)
    (by rw [ammBurnToken0SelectorMem_size]; omega) (by omega)

theorem ammBurnToken0CalldataMem_size (I : ExecutionEnv) (q0 : UInt256) :
    (ammBurnToken0CalldataMem I q0).size = 196 := by
  unfold ammBurnToken0CalldataMem
  exact toByteArray_write32_size_of_le
    (q0.toByteArray.write 0 (ammBurnToken0SelectorMem I) 132 32)
    (ammBurnToWord I) 164 164 196
    (ammBurnToken0Arg0Mem_size I q0)
    (by rw [ammBurnToken0Arg0Mem_size]) (by omega)

theorem ammBurnToken0CalldataMem_read64 (I : ExecutionEnv) (q0 : UInt256) :
    (ammBurnToken0CalldataMem I q0).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammBurnToken0CalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [ammBurnToken0Arg0Mem_size]) (by omega)]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [ammBurnToken0SelectorMem_size]; omega) (by omega)]
  unfold ammBurnToken0SelectorMem
  rw [toByteArray_write_read_below_of_gap ammBurnTransferSelectorWord
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
    128 64 (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size])
    (by omega) (by rw [twoWordHashMem_size_96 _ _ solcFreePtrMem_size]; native_decide)]
  exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem ammBurnToken0SelectorMem_selector (I : ExecutionEnv) :
    (ammBurnToken0SelectorMem I).extract 128 132 = transferSelector := by
  unfold ammBurnToken0SelectorMem
  have hbase :
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hgap :
      128 - (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size <
        USize.size := by
    rw [hbase]
    native_decide
  rw [toByteArray_write_eq ammBurnTransferSelectorWord _ 128
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

theorem ammBurnToken0CalldataMem_read4 (I : ExecutionEnv) (q0 : UInt256) :
    (ammBurnToken0CalldataMem I q0).readWithPadding 128 4 =
      transferSelector := by
  unfold ammBurnToken0CalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [ammBurnToken0Arg0Mem_size]) (by omega)
    (by rw [ammBurnToken0Arg0Mem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [ammBurnToken0SelectorMem_size]; omega) (by omega)
    (by rw [ammBurnToken0SelectorMem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
    (by rw [ammBurnToken0SelectorMem_size]; omega)]
  exact ammBurnToken0SelectorMem_selector I

theorem ammBurnToken0CalldataMem_readAmount (I : ExecutionEnv)
    (q0 : UInt256) :
    (ammBurnToken0CalldataMem I q0).readWithPadding 132 32 =
      q0.toByteArray := by
  unfold ammBurnToken0CalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [ammBurnToken0Arg0Mem_size]) (by omega)]
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [ammBurnToken0SelectorMem_size]; omega)]
  rw [show q0.toByteArray.extract 0 32 = q0.toByteArray by
    rw [show 32 = q0.toByteArray.size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammBurnToken0CalldataMem_readTo (I : ExecutionEnv)
    (q0 : UInt256) :
    (ammBurnToken0CalldataMem I q0).readWithPadding 164 32 =
      (ammBurnToWord I).toByteArray := by
  unfold ammBurnToken0CalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [ammBurnToken0Arg0Mem_size])]
  rw [show (ammBurnToWord I).toByteArray.extract 0 32 =
      (ammBurnToWord I).toByteArray by
    rw [show 32 = (ammBurnToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammBurnToken0CalldataMem_read (I : ExecutionEnv) (q0 : UInt256) :
    (ammBurnToken0CalldataMem I q0).readWithPadding 128 68 =
      transferSelector ++ q0.toByteArray ++ (ammBurnToWord I).toByteArray := by
  rw [byteArray_readWithPadding_split _ 128 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [ammBurnToken0CalldataMem_size])]
  rw [ammBurnToken0CalldataMem_read4]
  rw [byteArray_readWithPadding_split _ 132 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [ammBurnToken0CalldataMem_size])]
  rw [ammBurnToken0CalldataMem_readAmount,
    ammBurnToken0CalldataMem_readTo]
  exact ByteArray.append_assoc.symm

theorem ammBurnToken0CalldataMem_encode (I : ExecutionEnv) (q0 : UInt256)
    (hamount : q0.toNat < UInt256.size)
    (hto : (ammBurnToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat q0.toNat), .address (AccountAddress.ofUInt256
        (ammBurnToWord I))] =
      some ((ammBurnToken0CalldataMem I q0).readWithPadding 128 68) := by
  rw [ammBurnToken0CalldataMem_read]
  have hq : EVM.word q0.toNat = q0 := u256_ofNat_toNat q0
  have ht : EVM.word ↑(AccountAddress.ofUInt256 (ammBurnToWord I)) =
      ammBurnToWord I := by
    have h := valueToWord_address_ofNat_canonical (ammBurnToWord I) hto
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
        EVM.Word.toBytesBE (ammBurnToWord I)).toByteArray =
      q0.toByteArray ++ (ammBurnToWord I).toByteArray := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray q0,
      ← word_toBytesBE_toByteArray_eq_toByteArray (ammBurnToWord I)]
    exact list_toByteArray_append _ _
  rw [hbytes]
  exact congrArg some (ByteArray.append_assoc.symm)

theorem ammBurnX_token0SelectorMem {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4815⟩
      [ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4837⟩
      [⟨128⟩, ammBurnToWord I, q0, ⟨3077966991⟩,
        ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0SelectorMem I)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k' C' := by
  have rd4825 := evm_run rd with [
    push4 ⟨3077966991⟩, dup4, dup6, push1 ⟨64⟩]
  have hmemSize :
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  have hmemRead :
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  have rd4826 := evm_run rd4825 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hmemSize]; decide)
        (by decide) hmemRead) (by decide) (by evm_ov)]
  have rd4836 := evm_run rd4826 with [
    dup4, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  have rd4837 := evm_run rd4836 with [
    raw mstore 6
      (ammBurnTransferSelectorWord.toByteArray.write 0
        (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) 128 32)
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [ammBurnToken0SelectorMem, ammBurnTransferSelectorWord] using rd4837⟩

theorem ammBurnX_token0TransferArgs {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4837⟩
      [⟨128⟩, ammBurnToWord I, q0, ⟨3077966991⟩,
        ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0SelectorMem I)
      (UInt256.ofNat 5) ByteArray.empty (cA, σ) k C)
    (hcanon : (ammBurnToWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4850⟩
      [⟨196⟩, ⟨3077966991⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0CalldataMem I q0)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  let mem0 := ammBurnTransferSelectorWord.toByteArray.write 0
    (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem) 128 32
  let mem1 := q0.toByteArray.write 0 mem0 132 32
  let mem2 := (ammBurnToWord I).toByteArray.write 0 mem1 164 32
  have rd6284 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨4850⟩, swap3, swap2, swap1,
    push2 ⟨6284⟩, jump (by jump_dest)]
  have rd5716 := evm_run rd6284 with [
    jumpdest, push0, push1 ⟨64⟩, dup3, add, swap1, pop,
    push2 ⟨6303⟩, push0, dup4, add, dup6, push2 ⟨5716⟩,
    jump (by jump_dest), jumpdest, push2 ⟨5725⟩, dup2,
    push2 ⟨5490⟩, jump (by jump_dest)]
  have rd5725 := evm_run rd5716 with [
    raw ammRoutineCleanupUint256 (by jump_dest) (by evm_ov)]
  have rd6303 := evm_run rd5725 with [
    jumpdest, dup3,
    raw mstore 3 mem1 (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd6269 := evm_run rd6303 with [
    jumpdest, push2 ⟨6316⟩, push1 ⟨32⟩, dup4, add,
    dup5, push2 ⟨6269⟩, jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩,
    jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩,
    jump (by jump_dest)]
  have rd5441 := evm_run rd5400 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd6278 := evm_run rd5441 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have hclean := solcAddrMask_clean hcanon
  have rd6278' := rd6278
  rw [hclean] at rd6278'
  have rd6316 := evm_run rd6278' with [
    jumpdest, dup3,
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd4850 := evm_run rd6316 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [mem0, mem1, mem2, ammBurnToken0CalldataMem,
      ammBurnToken0SelectorMem] using rd4850⟩

/-- The first `CALL` sends 68 ABI bytes and requests a 32-byte return. -/
theorem ammBurnX_token0CallFrame {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4850⟩
      [⟨196⟩, ⟨3077966991⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4863⟩
      [gasWord, ammMintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammBurnToken0CalldataMem I q0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammBurnToken0CalldataMem I q0).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [ammBurnToken0CalldataMem_size]; decide)
      (by decide) (ammBurnToken0CalldataMem_read64 I q0)
  have rd4854 := evm_run rd with [jumpdest, push1 ⟨32⟩, push1 ⟨64⟩]
  have rd4855 := evm_run rd4854 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4863 := evm_run rd4855 with [
    dup1, dup4, sub, dup2, push0, dup8, gas]
  obtain ⟨gasWord, rd4863'⟩ := rd4863
  exact ⟨gasWord, _, _, by
    simpa only [show (⟨196⟩ : UInt256) - ⟨128⟩ = ⟨68⟩ from by decide]
      using rd4863'⟩

/-- The EVM transfer and the Solm transfer use the same external-call witness. -/
theorem ammBurnX_token0Call {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hto : (ammBurnToWord I).toNat < EVM.addressModulus)
    (hframe : ∃ (gasWord : UInt256) (k C : Nat), RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4863⟩
      [gasWord, ammMintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A' : Substate) (k' C' : Nat),
      RD ammBytecode I g (initState cAstart gh bl σstart σ₀ g A I) ⟨4864⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨3077966991⟩ ::
          ammMintToken0Word σ I :: q1 :: q0 :: ammBurnToWord I ::
          ammBurnLiquidityWord I :: ⟨560⟩ :: [sel])
        (o.write 0 (ammBurnToken0CalldataMem I q0) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 7) o (cA', σ') k' C' ∧
      typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with accountMap := σ }
        (AccountAddress.ofUInt256 (ammMintToken0Word σ I))
        "transfer" 0
        [.int (Int.ofNat q0.toNat),
          .address (AccountAddress.ofUInt256 (ammBurnToWord I))]
        (z, { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, o)
        true ∧
      o.size < UInt256.size ∧ o.size < 2 ^ 138 := by
  obtain ⟨_, _, _, rd4863⟩ := hframe
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘpack, rd4864, hosz⟩ :=
    RD.call rd4863 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68) 128 32) =
        UInt256.ofNat 7 := by native_decide
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz, ?_⟩
  · simpa [haw] using rd4864
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := ammMintToken0Word σ I)
      (mem := ammBurnToken0CalldataMem I q0)
      (inOff := ⟨128⟩) (inSize := ⟨68⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl (ammBurnToken0CalldataMem_encode I q0 q0.val.isLt hto) ?_
    simpa [initState, hperm] using hΘ
  · have hinputSize :
        ((ammBurnToken0CalldataMem I q0).readWithPadding 128 68).size = 68 := by
      rw [readWithPadding_eq_extract' _ 128 68 (by norm_num) (by norm_num)
        (by rw [ammBurnToken0CalldataMem_size])]
      rw [ByteArray.size_extract, ammBurnToken0CalldataMem_size]
      omega
    have hbound :
        ((ammBurnToken0CalldataMem I q0).readWithPadding 128 68).size ≤
          Ethereum.EVM.maxReturnDataSizeByGas := by
      rw [hinputSize]
      norm_num [Ethereum.EVM.maxReturnDataSizeByGas,
        Ethereum.EVM.maxReturnDataWordsByGas]
    exact Theta_returnData_size_lt_2pow138_of_eq
      I.blobVersionedHashes cA gh bl σ σ₀ A_in
      (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
      (AccountAddress.ofUInt256 (ammMintToken0Word σ I))
      (toExecute σ (AccountAddress.ofUInt256 (ammMintToken0Word σ I)))
      callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
      ((ammBurnToken0CalldataMem I q0).readWithPadding 128 68)
      (I.depth + 1) I.header true (by simpa [initState, hperm] using hΘ) hbound

/-- A failed first token transfer bubbles its return data and reverts. -/
theorem ammBurnX_token0CallFailed {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {R : List UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I)
      ⟨4864⟩ (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 5 ≤ 1024) :
    RDrev ammBytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd4871 := evm_run rd with [
    iszero, dup1, iszero, push2 ⟨4878⟩, jumpiNT (by decide)]
  have rd4874 := evm_run rd4871 with [returndatasize, push0, push0]
  let len := UInt256.ofNat o.size
  let memout := o.write 0 mem 0 len.toNat
  let awout := UInt256.ofNat (MachineState.M aw.toNat 0 len.toNat)
  have rd4875 := RD.returndatacopy
    (Cₘ awout - Cₘ aw) memout awout rd4874 (by native_decide)
    (by
      change 0 + len.toNat ≤ o.size
      dsimp [len]
      rw [ulit_toNat' o.size hosz]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, len, awout])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd4877 := evm_run rd4875 with [returndatasize, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M awout.toNat 0 len.toNat)) - Cₘ awout)
    rd4877 (by native_decide)
    (fun s haw hstk => by
      simpa [awout, len, haw] using memExpRevertZeroOff s hstk)
    (by simp only [List.length_cons]; omega)

theorem ammBurnX_token0DepthRevert {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 gasWord : UInt256} {k C : Nat}
    (hdepth : I.depth = 1024)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4863⟩
      [gasWord, ammMintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0CalldataMem I q0) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  obtain ⟨_, _, rd4864⟩ := RD.callDepthLimit rd
    (by native_decide) hdepth
    (by simp only [List.length_cons, List.length_nil]; omega)
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat 128 68) 128 32) =
        UInt256.ofNat 7 := by native_decide
  have rd4864' := rd4864
  simpa [haw, byteArray_write_len_zero] using
    (ammBurnX_token0CallFailed rd4864'
      (by decide)
      (by simp only [List.length_cons, List.length_nil]; omega))

theorem ammBurnX_token0CallSucceeded {cAstart gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {mem o : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4864⟩
      [⟨1⟩, ⟨196⟩, ⟨3077966991⟩, ammMintToken0Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      mem aw o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4883⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      mem aw o acc k' C' := by
  exact ⟨_, _, evm_run rd with [
    iszero, dup1, iszero, push2 ⟨4878⟩,
    jumpiT (by decide) (by jump_dest), jumpdest,
    pop, pop, pop, pop]⟩

noncomputable def ammBurnToken0PostCallMem (I : ExecutionEnv)
    (q0 : UInt256) (o : ByteArray) : ByteArray :=
  o.write 0 (ammBurnToken0CalldataMem I q0) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem ammBurnToken0PostCallMem_size_short (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hshort : o.size < 32) :
    (ammBurnToken0PostCallMem I q0 o).size = 196 := by
  unfold ammBurnToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide)
      hshort (by exact lt_trans hshort (by decide))
  rw [hlen]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero, ammBurnToken0CalldataMem_size]
  · rw [write_eq_gen o (ammBurnToken0CalldataMem I q0) 128 o.size
      hzero le_rfl (by rw [ammBurnToken0CalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, ammBurnToken0CalldataMem_size]
    omega

theorem ammBurnToken0PostCallMem_size_long (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammBurnToken0PostCallMem I q0 o).size = 196 := by
  unfold ammBurnToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  rw [write_eq_gen o (ammBurnToken0CalldataMem I q0) 128 32
    (by omega) hlo (by rw [ammBurnToken0CalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append,
    ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, ammBurnToken0CalldataMem_size]
  omega

theorem ammBurnToken0PostCallMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hhi : o.size < UInt256.size) :
    (ammBurnToken0PostCallMem I q0 o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  by_cases hshort : o.size < 32
  · unfold ammBurnToken0PostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
      umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size)
        (by decide) hshort (by omega)
    rw [hlen]
    by_cases hzero : o.size = 0
    · rw [hzero, byteArray_write_len_zero]
      exact ammBurnToken0CalldataMem_read64 I q0
    · rw [write_read_below_gen_extend o (ammBurnToken0CalldataMem I q0)
        128 o.size 64 hzero le_rfl
        (by rw [ammBurnToken0CalldataMem_size]; omega) (by omega)]
      exact ammBurnToken0CalldataMem_read64 I q0
  · have hlo : 32 ≤ o.size := by omega
    unfold ammBurnToken0PostCallMem
    have hlen :
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size)
        (by decide) hlo hhi
    rw [hlen]
    rw [write_read_below_gen_extend o (ammBurnToken0CalldataMem I q0)
      128 32 64 (by omega) hlo
      (by rw [ammBurnToken0CalldataMem_size]; omega) (by omega)]
    exact ammBurnToken0CalldataMem_read64 I q0

theorem ammBurnToken0PostCallMem_read128 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammBurnToken0PostCallMem I q0 o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold ammBurnToken0PostCallMem
  have hlen :
      (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi
  rw [hlen]
  exact write32_read_back o (ammBurnToken0CalldataMem I q0) 128
    (by omega) (by rw [ammBurnToken0CalldataMem_size]; omega)

noncomputable def ammBurnToken0DecodeMem (I : ExecutionEnv)
    (q0 : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (ammMintReturndataRounded o)).toByteArray.write 0
    (ammBurnToken0PostCallMem I q0 o) 64 32

theorem ammBurnToken0DecodeMem_size (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hhi : o.size < UInt256.size) :
    (ammBurnToken0DecodeMem I q0 o).size = 196 := by
  have hbase : (ammBurnToken0PostCallMem I q0 o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact ammBurnToken0PostCallMem_size_short I q0 hshort
    · exact ammBurnToken0PostCallMem_size_long I q0 (by omega) hhi
  unfold ammBurnToken0DecodeMem
  exact toByteArray_write32_size_of_le
    (ammBurnToken0PostCallMem I q0 o)
    (UInt256.add ⟨128⟩ (ammMintReturndataRounded o))
    64 196 196 hbase (by rw [hbase]; omega) (by omega)

theorem ammBurnToken0DecodeMem_read128 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray}
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (ammBurnToken0DecodeMem I q0 o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold ammBurnToken0DecodeMem
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
    (by rw [ammBurnToken0PostCallMem_size_long I q0 hlo hhi]; omega)
    (by omega)
    (by rw [ammBurnToken0PostCallMem_size_long I q0 hlo hhi]; omega)]
  exact ammBurnToken0PostCallMem_read128 I q0 hlo hhi

theorem ammBurnX_token0ToDecoder {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hhi : o.size < UInt256.size)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4883⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0PostCallMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6365⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4914⟩,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k' C' := by
  have hmemSize : (ammBurnToken0PostCallMem I q0 o).size = 196 := by
    by_cases hshort : o.size < 32
    · exact ammBurnToken0PostCallMem_size_short I q0 hshort
    · exact ammBurnToken0PostCallMem_size_long I q0 (by omega) hhi
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammBurnToken0PostCallMem I q0 o).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammBurnToken0PostCallMem I q0 o).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide)
      (ammBurnToken0PostCallMem_read64 I q0 hhi)
  have rd4885 := evm_run rd with [push1 ⟨64⟩]
  have rd4886 := evm_run rd4885 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4900 := evm_run rd4886 with [
    returndatasize, push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and,
    dup3, add, dup1, push1 ⟨64⟩]
  have rd4901 := evm_run rd4900 with [
    raw mstore 0 (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd6365 := evm_run rd4901 with [
    pop, dup2, add, swap1, push2 ⟨4914⟩, swap2, swap1,
    push2 ⟨6365⟩, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [ammBurnToken0DecodeMem, ammMintReturndataRounded] using rd6365⟩

theorem ammBurnX_token0DecodeShortReverts {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hshort : o.size < 32)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6365⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4914⟩,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
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

theorem ammBurnX_token0DecodeWord {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6365⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4914⟩,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6323⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6359⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6399⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4914⟩,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k' C' := by
  have hhi : o.size < UInt256.size := lt_trans hbound (by norm_num [UInt256.size])
  have hcheck := solcDecodeEndLenCheckOk_128_32 hlo (by omega : o.size < 2 ^ 255)
  have rd6386 := evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero,
    push2 ⟨6386⟩, jumpiT (by rw [hcheck]; decide) (by jump_dest)]
  have rd6345 := evm_run rd6386 with [
    jumpdest, push0, push2 ⟨6399⟩, dup5, dup3, dup6, add,
    push2 ⟨6345⟩, jump (by jump_dest)]
  let v : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (ammBurnToken0DecodeMem I q0 o).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammBurnToken0DecodeMem I q0 o).readWithPadding 128 32))) =
        v := by
    simpa only [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      ammBurnToken0DecodeMem_read128 I q0 hlo hhi, v] using
      (mloadValue_eq_readWithPadding_of_lt_size
        (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) ⟨128⟩ 196
        (ammBurnToken0DecodeMem_size I q0 hhi) (by decide) (by decide))
  have rd6348 := evm_run rd6345 with [jumpdest, push0, dup2]
  have rd6349 := evm_run rd6348 with [
    raw mload 0 v (UInt256.ofNat 7) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  have rd6323 := evm_run rd6349 with [
    swap1, pop, push2 ⟨6359⟩, dup2, push2 ⟨6323⟩,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa only [v] using rd6323⟩

/-- Shared ABI bool cleanup, followed by Solidity's canonicality comparison. -/
theorem RD.ammBurnBoolCheck {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {v ret : UInt256} {R : List UInt256}
    {mem o : ByteArray}
    {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode ee g s0 ⟨6323⟩ (v :: ret :: R)
      mem aw o acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ⟨6335⟩
      (UInt256.eq v (UInt256.isZero (UInt256.isZero v)) :: v :: ret :: R)
      mem aw o acc k' C' := by
  have rd5603 := evm_run rd with [
    jumpdest, push2 ⟨6332⟩, dup2, push2 ⟨5603⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd6332⟩ := RD.ammRoutineBoolCleanup rd5603
    (by jump_dest) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd6332 with [jumpdest, dup2, eq]⟩

theorem RD.ammBurnBoolCheckInvalid {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {v ret : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode ee g s0 ⟨6323⟩ (v :: ret :: R)
      mem aw o acc k C)
    (hbad : v ≠ UInt256.isZero (UInt256.isZero v))
    (hov : R.length + 10 ≤ 1024) :
    RDrev ammBytecode g s0 := by
  obtain ⟨_, _, rd6335⟩ := RD.ammBurnBoolCheck rd hov
  have hneq : UInt256.eq v (UInt256.isZero (UInt256.isZero v)) = ⟨0⟩ :=
    u256_eq_of_ne hbad
  exact evm_run rd6335 with [
    push2 ⟨6342⟩, jumpiNT (by rw [hneq]),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem RD.ammBurnBoolCheckOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {v ret : UInt256} {R : List UInt256}
    {mem o : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (rd : RD ammBytecode ee g s0 ⟨6323⟩ (v :: ret :: R)
      mem aw o acc k C)
    (hcanon : v = ⟨0⟩ ∨ v = ⟨1⟩)
    (hret : (D_J ammBytecode 0).contains ret = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD ammBytecode ee g s0 ret R mem aw o acc k' C' := by
  obtain ⟨_, _, rd6335⟩ := RD.ammBurnBoolCheck rd hov
  have hnorm : v = UInt256.isZero (UInt256.isZero v) := by
    rcases hcanon with hzero | hone
    · subst v
      decide
    · subst v
      decide
  have heq : UInt256.eq v (UInt256.isZero (UInt256.isZero v)) = ⟨1⟩ := by
    rw [← hnorm]
    exact u256_eq_refl v
  exact ⟨_, _, evm_run rd6335 with [
    push2 ⟨6342⟩, jumpiT (by rw [heq]; decide) (by jump_dest),
    jumpdest, pop, jump hret]⟩

theorem ammBoolNormalized_canonical (v : UInt256) :
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

theorem ammBurnX_token0DecodeInvalidReverts {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
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
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4914⟩,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    RDrev ammBytecode g
      (initState cAstart gh bl σstart σ₀ g A I) := by
  exact RD.ammBurnBoolCheckInvalid rd hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem ammBurnX_token0DecodeOk {cAstart gh bl σstart σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat}
    (hcanon : UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) = ⟨1⟩)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨6323⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨6359⟩,
        UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)),
        ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨6399⟩,
        ⟨0⟩, ⟨0⟩, ⟨128⟩,
        UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨4914⟩,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4916⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o) (UInt256.ofNat 7) o acc k' C' := by
  obtain ⟨_, _, rd6359⟩ := RD.ammBurnBoolCheckOk rd hcanon
    (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6399 := evm_run rd6359 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd4914 := evm_run rd6399 with [
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  exact ⟨_, _, evm_run rd4914 with [jumpdest, pop]⟩

/-- The second transfer reads token1 after the first external call. -/
theorem ammBurnX_token1Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4916⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      mem aw o (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4972⟩
      [ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      mem aw o (cA, σ) k' C' := by
  have rd4920 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd4921⟩ := rd4920.sload (by native_decide) (by evm_ov)
  have rd4972 := evm_run rd4921 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [ammMintToken1Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd4972⟩

theorem ammBurnToken0DecodeMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o : ByteArray} (hhi : o.size < UInt256.size) :
    (ammBurnToken0DecodeMem I q0 o).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr o) := by
  unfold ammBurnToken0DecodeMem
  exact toByteArray_write32_read_back _ _ _ (by
    by_cases hshort : o.size < 32
    · rw [ammBurnToken0PostCallMem_size_short I q0 hshort]
      omega
    · rw [ammBurnToken0PostCallMem_size_long I q0 (by omega) hhi]
      omega)

noncomputable def ammBurnToken1SelectorMem (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) : ByteArray :=
  ammBurnTransferSelectorWord.toByteArray.write 0
    (ammBurnToken0DecodeMem I q0 o0)
    (ammMintToken0FreePtr o0).toNat 32

def ammBurnToken1SelectorWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 7 (ammMintToken0FreePtr o0).toNat 32)

theorem ammBurnToken1SelectorMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammBurnToken1SelectorMem I q0 o0).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr o0) := by
  unfold ammBurnToken1SelectorMem
  have hptr : 160 ≤ (ammMintToken0FreePtr o0).toNat :=
    (ammMintToken0FreePtr_bounds o0 hlo hbound).1
  have hhi : o0.size < UInt256.size := lt_trans hbound
    (by norm_num [UInt256.size])
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [ammBurnToken0DecodeMem_size I q0 hhi]; omega)
    (by omega)]
  exact ammBurnToken0DecodeMem_read64 I q0 hhi

theorem ammBurnX_token1SelectorMem {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4972⟩
      [ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken0DecodeMem I q0 o0) (UInt256.ofNat 7)
      o0 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4994⟩
      [ammMintToken0FreePtr o0, ammBurnToWord I, q1,
        ⟨3077966991⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1SelectorMem I q0 o0)
      (ammBurnToken1SelectorWords o0) o0 (cA, σ) k' C' := by
  have hhi : o0.size < UInt256.size :=
    lt_trans hbound (by norm_num [UInt256.size])
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammBurnToken0DecodeMem I q0 o0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammBurnToken0DecodeMem I q0 o0).readWithPadding 64 32))) =
        ammMintToken0FreePtr o0 :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7)
      (v := ammMintToken0FreePtr o0)
      (by rw [ammBurnToken0DecodeMem_size I q0 hhi]; decide)
      (by decide)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using ammBurnToken0DecodeMem_read64 I q0 hhi)
  have rd4981 := evm_run rd with [
    push4 ⟨3077966991⟩, dup3, dup6, push1 ⟨64⟩]
  have rd4982 := evm_run rd4981 with [
    raw mload 0 (ammMintToken0FreePtr o0) (UInt256.ofNat 7)
      (by native_decide) mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4993 := evm_run rd4982 with [
    dup4, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := ammBurnToken1SelectorWords o0
  have rd4994 := RD.mstore
    (Cₘ awSel - Cₘ (UInt256.ofNat 7))
    (ammBurnToken1SelectorMem I q0 o0) awSel rd4993 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awSel, ammBurnToken1SelectorWords,
        show (UInt256.ofNat 7).toNat = 7 from by decide])
    (by unfold ammBurnToken1SelectorMem; rfl)
    (by simp [awSel, ammBurnToken1SelectorWords,
      show (UInt256.ofNat 7).toNat = 7 from by decide])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [ammBurnTransferSelectorWord] using rd4994⟩

theorem ammBurnToken0FreePtr_add36_toNat (o : ByteArray)
    (hlo : 32 ≤ o.size) (hbound : o.size < 2 ^ 138) :
    (ammMintToken0FreePtr o + ⟨36⟩).toNat =
      (ammMintToken0FreePtr o).toNat + 36 := by
  rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    Nat.mod_eq_of_lt]
  have hptr : (ammMintToken0FreePtr o).toNat ≤ o.size + 159 := by
    simpa only [ammMintToken0FreePtr] using
      (ammMintToken0FreePtr_bounds o hlo hbound).2
  have hcap : 2 ^ 138 + 195 < UInt256.size := by norm_num [UInt256.size]
  omega

noncomputable def ammBurnToken1AmountMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray) : ByteArray :=
  q1.toByteArray.write 0 (ammBurnToken1SelectorMem I q0 o0)
    (ammMintToken0FreePtr o0 + ⟨4⟩).toNat 32

noncomputable def ammBurnToken1CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray) : ByteArray :=
  (ammBurnToWord I).toByteArray.write 0
    (ammBurnToken1AmountMem I q0 q1 o0)
    (ammMintToken0FreePtr o0 + ⟨36⟩).toNat 32

def ammBurnToken1AmountWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammBurnToken1SelectorWords o0).toNat
    (ammMintToken0FreePtr o0 + ⟨4⟩).toNat 32)

def ammBurnToken1CalldataWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (ammBurnToken1AmountWords o0).toNat
    (ammMintToken0FreePtr o0 + ⟨36⟩).toNat 32)

theorem ammBurnToken1SelectorMem_size (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) :
    (ammMintToken0FreePtr o0).toNat + 32 ≤
      (ammBurnToken1SelectorMem I q0 o0).size := by
  unfold ammBurnToken1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnToken1AmountMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammMintToken0FreePtr o0).toNat + 36 ≤
      (ammBurnToken1AmountMem I q0 q1 o0).size := by
  unfold ammBurnToken1AmountMem
  rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnToken1CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammMintToken0FreePtr o0).toNat + 68 ≤
      (ammBurnToken1CalldataMem I q0 q1 o0).size := by
  unfold ammBurnToken1CalldataMem
  rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem ammBurnToken1SelectorMem_read4 (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) :
    (ammBurnToken1SelectorMem I q0 o0).readWithPadding
      (ammMintToken0FreePtr o0).toNat 4 = transferSelector := by
  unfold ammBurnToken1SelectorMem
  have h := toByteArray_write_read_window_no_gap ammBurnTransferSelectorWord
    (ammBurnToken0DecodeMem I q0 o0)
    (ammMintToken0FreePtr o0).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : ammBurnTransferSelectorWord.toByteArray.extract 0 4 =
      transferSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem ammBurnToken1CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding 64 32 =
      UInt256.toByteArray (ammMintToken0FreePtr o0) := by
  have hptr := (ammMintToken0FreePtr_bounds o0 hlo hbound).1
  change 160 ≤ (ammMintToken0FreePtr o0).toNat at hptr
  unfold ammBurnToken1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]; omega)]
  unfold ammBurnToken1AmountMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1SelectorMem_size I q0 o0
      rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)
    (by rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound]; omega)]
  exact ammBurnToken1SelectorMem_read64 I q0 hlo hbound

theorem ammBurnToken1CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (ammMintToken0FreePtr o0).toNat 4 = transferSelector := by
  have hptr := (ammMintToken0FreePtr_bounds o0 hlo hbound).1
  change 160 ≤ (ammMintToken0FreePtr o0).toNat at hptr
  unfold ammBurnToken1CalldataMem
  rw [write32_read_below_len _ _ _ _ 4 (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]; omega)
    (by
      have hs := ammBurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      omega)
    (by norm_num) (by norm_num)]
  unfold ammBurnToken1AmountMem
  rw [write32_read_below_len _ _ _ _ 4 (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1SelectorMem_size I q0 o0
      rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)
    (by rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound])
    (by
      have hs := ammBurnToken1SelectorMem_size I q0 o0
      omega)
    (by norm_num) (by norm_num)]
  exact ammBurnToken1SelectorMem_read4 I q0 o0

theorem ammBurnToken1CalldataMem_readAmount (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (ammMintToken0FreePtr o0 + ⟨4⟩).toNat 32 =
      q1.toByteArray := by
  unfold ammBurnToken1CalldataMem
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound,
      ammBurnToken0FreePtr_add36_toNat o0 hlo hbound])]
  unfold ammBurnToken1AmountMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1SelectorMem_size I q0 o0
      rw [ammMintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)]
  rw [show q1.toByteArray.extract 0 32 = q1.toByteArray by
    rw [show 32 = q1.toByteArray.size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammBurnToken1CalldataMem_readTo (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (ammMintToken0FreePtr o0 + ⟨36⟩).toNat 32 =
      (ammBurnToWord I).toByteArray := by
  unfold ammBurnToken1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      have hs := ammBurnToken1AmountMem_size I q0 q1 o0 hlo hbound
      rw [ammBurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)]
  rw [show (ammBurnToWord I).toByteArray.extract 0 32 =
      (ammBurnToWord I).toByteArray by
    rw [show 32 = (ammBurnToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammBurnToken1CalldataMem_read (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
      (ammMintToken0FreePtr o0).toNat 68 =
      transferSelector ++ q1.toByteArray ++
        (ammBurnToWord I).toByteArray := by
  have hsize := ammBurnToken1CalldataMem_size I q0 q1 o0 hlo hbound
  rw [byteArray_readWithPadding_split _ _ 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)]
  rw [ammBurnToken1CalldataMem_read4 I q0 q1 hlo hbound]
  rw [byteArray_readWithPadding_split _ _ 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)]
  have hsum : (ammMintToken0FreePtr o0).toNat + 4 + 32 =
      (ammMintToken0FreePtr o0).toNat + 36 := by omega
  rw [hsum, ← ammMintToken0FreePtr_add4_toNat o0 hlo hbound,
    ← ammBurnToken0FreePtr_add36_toNat o0 hlo hbound,
    ammBurnToken1CalldataMem_readAmount I q0 q1 hlo hbound,
    ammBurnToken1CalldataMem_readTo I q0 q1 hlo hbound]
  exact ByteArray.append_assoc.symm

theorem ammBurnToken1CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hto : (ammBurnToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat q1.toNat),
        .address (AccountAddress.ofUInt256 (ammBurnToWord I))] =
      some ((ammBurnToken1CalldataMem I q0 q1 o0).readWithPadding
        (ammMintToken0FreePtr o0).toNat 68) := by
  rw [ammBurnToken1CalldataMem_read I q0 q1 hlo hbound,
    ← ammBurnToken0CalldataMem_read I q1]
  exact ammBurnToken0CalldataMem_encode I q1 q1.val.isLt hto

theorem ammBurnX_token1TransferArgs {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hcanon : (ammBurnToWord I).toNat < EVM.addressModulus)
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4994⟩
      [ammMintToken0FreePtr o0, ammBurnToWord I, q1,
        ⟨3077966991⟩, ammMintToken1Word σ I,
        q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1SelectorMem I q0 o0)
      (ammBurnToken1SelectorWords o0) o0 (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨5007⟩
      [ammMintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        ammMintToken1Word σ I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (ammBurnToken1CalldataMem I q0 q1 o0)
      (ammBurnToken1CalldataWords o0) o0 (cA, σ) k' C' := by
  let fp := ammMintToken0FreePtr o0
  let awSel := ammBurnToken1SelectorWords o0
  let awAmount := ammBurnToken1AmountWords o0
  let awFinal := ammBurnToken1CalldataWords o0
  have rd6284 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨5007⟩, swap3, swap2, swap1,
    push2 ⟨6284⟩, jump (by jump_dest)]
  have rd5716 := evm_run rd6284 with [
    jumpdest, push0, push1 ⟨64⟩, dup3, add, swap1, pop,
    push2 ⟨6303⟩, push0, dup4, add, dup6, push2 ⟨5716⟩,
    jump (by jump_dest), jumpdest, push2 ⟨5725⟩, dup2,
    push2 ⟨5490⟩, jump (by jump_dest)]
  have rd5725 := evm_run rd5716 with [
    raw ammRoutineCleanupUint256 (by jump_dest) (by evm_ov)]
  have rd6303pre := evm_run rd5725 with [jumpdest, dup3]
  have hoff : (⟨4⟩ : UInt256) + fp + ⟨0⟩ = fp + ⟨4⟩ := by
    rw [u256_add_comm _ ⟨0⟩, u256_zero_add,
      u256_add_comm (⟨4⟩ : UInt256) fp]
  have rd6303pre' := rd6303pre
  rw [hoff] at rd6303pre'
  have rd6303 := RD.mstore
    (Cₘ awAmount - Cₘ awSel)
    (ammBurnToken1AmountMem I q0 q1 o0) awAmount
    rd6303pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awAmount, awSel, fp, ammBurnToken1AmountWords])
    (by unfold ammBurnToken1AmountMem; rfl)
    (by simp [awAmount, fp, ammBurnToken1AmountWords])
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6303done := evm_run rd6303 with [
    pop, pop, jump (by jump_dest)]
  have rd6269 := evm_run rd6303done with [
    jumpdest, push2 ⟨6316⟩, push1 ⟨32⟩, dup4, add,
    dup5, push2 ⟨6269⟩, jump (by jump_dest)]
  have rd5431 := evm_run rd6269 with [
    jumpdest, push2 ⟨6278⟩, dup2, push2 ⟨5431⟩,
    jump (by jump_dest)]
  have rd5400 := evm_run rd5431 with [
    jumpdest, push0, push2 ⟨5441⟩, dup3, push2 ⟨5400⟩,
    jump (by jump_dest)]
  have rd5441 := evm_run rd5400 with [
    jumpdest, push0, push20 solcAddrMask, dup3, and,
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd6278 := evm_run rd5441 with [
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have hclean := solcAddrMask_clean hcanon
  have rd6278' := rd6278
  rw [hclean] at rd6278'
  have rd6316pre := evm_run rd6278' with [jumpdest, dup3]
  have hend : (⟨4⟩ : UInt256) + fp + ⟨32⟩ = fp + ⟨36⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp]
    rw [u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  have rd6316pre' := rd6316pre
  rw [hend] at rd6316pre'
  have rd6316 := RD.mstore
    (Cₘ awFinal - Cₘ awAmount)
    (ammBurnToken1CalldataMem I q0 q1 o0) awFinal
    rd6316pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awFinal, awAmount, fp, ammBurnToken1CalldataWords])
    (by unfold ammBurnToken1CalldataMem; rfl)
    (by rfl)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6316done := evm_run rd6316 with [
    pop, pop, jump (by jump_dest)]
  have rd5007 := evm_run rd6316done with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  have hend2 : (⟨4⟩ : UInt256) + fp + ⟨64⟩ = fp + ⟨68⟩ := by
    rw [u256_add_comm (⟨4⟩ : UInt256) fp]
    rw [u256_add_assoc]
    exact congrArg (fun x : UInt256 => fp + x) (by decide)
  exact ⟨_, _, by simpa only [fp, hend2] using rd5007⟩

end Benchmarks.ActAmm
