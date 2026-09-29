import Benchmarks.ActAmm4.SwapTransfer0Decode
import Benchmarks.ActAmm4.BurnTransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

/-- The second transfer reads token1 after the first external call. -/
theorem amm4SwapX_transfer1Address {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256}
    {mem o : ByteArray} {aw : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2659⟩
      [amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      mem aw o (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2715⟩
      [amm4MintToken1Word σ I, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      mem aw o (cA, σ) k' C' := by
  have rd4107 := evm_run rd with [push1 ⟨4⟩, push0, swap1]
  obtain ⟨_, _, rd4108⟩ := rd4107.sload (by native_decide) (by evm_ov)
  have rd4159 := evm_run rd4108 with [
    swap1, push2 ⟨256⟩, exp, swap1, div,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  exact ⟨_, _, by
    simpa only [amm4MintToken1Word, solcSlotWord, amm4MintDivPow0,
      amm4MintMaskTwice] using rd4159⟩

theorem amm4SwapTransfer0DecodeMem_read64 (I : ExecutionEnv)
    {o : ByteArray} (hhi : o.size < UInt256.size) :
    (amm4SwapTransfer0DecodeMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o) := by
  unfold amm4SwapTransfer0DecodeMem amm4MintToken0FreePtr
  exact toByteArray_write32_read_back _ _ _ (by
    by_cases hshort : o.size < 32
    · rw [amm4SwapTransfer0PostCallMem_size_short I hshort]
      omega
    · rw [amm4SwapTransfer0PostCallMem_size_long I (by omega) hhi]
      omega)

noncomputable def amm4SwapTransfer1SelectorMem (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) : ByteArray :=
  amm4BurnTransferSelectorWord.toByteArray.write 0
    (amm4SwapTransfer0DecodeMem I o0)
    (amm4MintToken0FreePtr o0).toNat 32

def amm4SwapTransfer1SelectorWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M 7 (amm4MintToken0FreePtr o0).toNat 32)

theorem amm4SwapTransfer1SelectorMem_read64 (I : ExecutionEnv)
    (q0 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4SwapTransfer1SelectorMem I q0 o0).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o0) := by
  unfold amm4SwapTransfer1SelectorMem
  have hptr : 160 ≤ (amm4MintToken0FreePtr o0).toNat :=
    (amm4MintToken0FreePtr_bounds o0 hlo hbound).1
  have hhi : o0.size < UInt256.size := lt_trans hbound
    (by norm_num [UInt256.size])
  rw [toByteArray_write_read_below_no_gap _ _ _ 64
    (by rw [amm4SwapTransfer0DecodeMem_size I hhi]; omega)
    (by omega)]
  exact amm4SwapTransfer0DecodeMem_read64 I hhi

theorem amm4SwapX_transfer1SelectorMem {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2715⟩
      [amm4MintToken1Word σ I, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer0DecodeMem I o0) (UInt256.ofNat 7)
      o0 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2737⟩
      [amm4MintToken0FreePtr o0, amm4SwapToWord I, q1,
        ⟨3077966991⟩, amm4MintToken1Word σ I,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapTransfer1SelectorMem I q0 o0)
      (amm4SwapTransfer1SelectorWords o0) o0 (cA, σ) k' C' := by
  have hhi : o0.size < UInt256.size :=
    lt_trans hbound (by norm_num [UInt256.size])
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4SwapTransfer0DecodeMem I o0).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((amm4SwapTransfer0DecodeMem I o0).readWithPadding 64 32))) =
        amm4MintToken0FreePtr o0 :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7)
      (v := amm4MintToken0FreePtr o0)
      (by rw [amm4SwapTransfer0DecodeMem_size I hhi]; decide)
      (by decide)
      (by simpa only [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using amm4SwapTransfer0DecodeMem_read64 I hhi)
  have rd4168 := evm_run rd with [
    push4 ⟨3077966991⟩, dup4, dup4, push1 ⟨64⟩]
  have rd4169 := evm_run rd4168 with [
    raw mload 0 (amm4MintToken0FreePtr o0) (UInt256.ofNat 7)
      (by native_decide) mem_cost hmload64 (by decide) (by evm_ov)]
  have rd4180 := evm_run rd4169 with [
    dup4, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2]
  let awSel := amm4SwapTransfer1SelectorWords o0
  have rd4181 := RD.mstore
    (Cₘ awSel - Cₘ (UInt256.ofNat 7))
    (amm4SwapTransfer1SelectorMem I q0 o0) awSel rd4180 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awSel, amm4SwapTransfer1SelectorWords,
        show (UInt256.ofNat 7).toNat = 7 from by decide])
    (by unfold amm4SwapTransfer1SelectorMem; rfl)
    (by simp [awSel, amm4SwapTransfer1SelectorWords,
      show (UInt256.ofNat 7).toNat = 7 from by decide])
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [amm4BurnTransferSelectorWord] using rd4181⟩

noncomputable def amm4SwapTransfer1AmountMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray) : ByteArray :=
  q1.toByteArray.write 0 (amm4SwapTransfer1SelectorMem I q0 o0)
    (amm4MintToken0FreePtr o0 + ⟨4⟩).toNat 32

noncomputable def amm4SwapTransfer1CalldataMem (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray) : ByteArray :=
  (amm4SwapToWord I).toByteArray.write 0
    (amm4SwapTransfer1AmountMem I q0 q1 o0)
    (amm4MintToken0FreePtr o0 + ⟨36⟩).toNat 32

def amm4SwapTransfer1AmountWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4SwapTransfer1SelectorWords o0).toNat
    (amm4MintToken0FreePtr o0 + ⟨4⟩).toNat 32)

def amm4SwapTransfer1CalldataWords (o0 : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (amm4SwapTransfer1AmountWords o0).toNat
    (amm4MintToken0FreePtr o0 + ⟨36⟩).toNat 32)

theorem amm4SwapTransfer1SelectorMem_size (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) :
    (amm4MintToken0FreePtr o0).toNat + 32 ≤
      (amm4SwapTransfer1SelectorMem I q0 o0).size := by
  unfold amm4SwapTransfer1SelectorMem
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4SwapTransfer1AmountMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o0).toNat + 36 ≤
      (amm4SwapTransfer1AmountMem I q0 q1 o0).size := by
  unfold amm4SwapTransfer1AmountMem
  rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4SwapTransfer1CalldataMem_size (I : ExecutionEnv)
    (q0 q1 : UInt256) (o0 : ByteArray)
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4MintToken0FreePtr o0).toNat + 68 ≤
      (amm4SwapTransfer1CalldataMem I q0 q1 o0).size := by
  unfold amm4SwapTransfer1CalldataMem
  rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
  exact toByteArray_write_size_ge_off_add32_no_gap _ _ _

theorem amm4SwapTransfer1SelectorMem_read4 (I : ExecutionEnv)
    (q0 : UInt256) (o0 : ByteArray) :
    (amm4SwapTransfer1SelectorMem I q0 o0).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 4 = transferSelector := by
  unfold amm4SwapTransfer1SelectorMem
  have h := toByteArray_write_read_window_no_gap amm4BurnTransferSelectorWord
    (amm4SwapTransfer0DecodeMem I o0)
    (amm4MintToken0FreePtr o0).toNat 0 4
    (by norm_num) (by norm_num) (by norm_num)
  have hword : amm4BurnTransferSelectorWord.toByteArray.extract 0 4 =
      transferSelector := by
    rw [toByteArray_eq_toBytesBE]
    native_decide
  simpa only [Nat.add_zero, hword] using h

theorem amm4SwapTransfer1CalldataMem_read64 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4SwapTransfer1CalldataMem I q0 q1 o0).readWithPadding 64 32 =
      UInt256.toByteArray (amm4MintToken0FreePtr o0) := by
  have hptr := (amm4MintToken0FreePtr_bounds o0 hlo hbound).1
  change 160 ≤ (amm4MintToken0FreePtr o0).toNat at hptr
  unfold amm4SwapTransfer1CalldataMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]; omega)]
  unfold amm4SwapTransfer1AmountMem
  rw [write32_read_below _ _ _ 64 (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1SelectorMem_size I q0 o0
      rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)
    (by rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]; omega)]
  exact amm4SwapTransfer1SelectorMem_read64 I q0 hlo hbound

theorem amm4SwapTransfer1CalldataMem_read4 (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4SwapTransfer1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 4 = transferSelector := by
  have hptr := (amm4MintToken0FreePtr_bounds o0 hlo hbound).1
  change 160 ≤ (amm4MintToken0FreePtr o0).toNat at hptr
  unfold amm4SwapTransfer1CalldataMem
  rw [write32_read_below_len _ _ _ _ 4 (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]; omega)
    (by
      have hs := amm4SwapTransfer1AmountMem_size I q0 q1 o0 hlo hbound
      omega)
    (by norm_num) (by norm_num)]
  unfold amm4SwapTransfer1AmountMem
  rw [write32_read_below_len _ _ _ _ 4 (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1SelectorMem_size I q0 o0
      rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)
    (by rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound])
    (by
      have hs := amm4SwapTransfer1SelectorMem_size I q0 o0
      omega)
    (by norm_num) (by norm_num)]
  exact amm4SwapTransfer1SelectorMem_read4 I q0 o0

theorem amm4SwapTransfer1CalldataMem_readAmount (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4SwapTransfer1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0 + ⟨4⟩).toNat 32 =
      q1.toByteArray := by
  unfold amm4SwapTransfer1CalldataMem
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)
    (by rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound,
      amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound])]
  unfold amm4SwapTransfer1AmountMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1SelectorMem_size I q0 o0
      rw [amm4MintToken0FreePtr_add4_toNat o0 hlo hbound]
      omega)]
  rw [show q1.toByteArray.extract 0 32 = q1.toByteArray by
    rw [show 32 = q1.toByteArray.size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4SwapTransfer1CalldataMem_readTo (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4SwapTransfer1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0 + ⟨36⟩).toNat 32 =
      (amm4SwapToWord I).toByteArray := by
  unfold amm4SwapTransfer1CalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by
      have hs := amm4SwapTransfer1AmountMem_size I q0 q1 o0 hlo hbound
      rw [amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound]
      omega)]
  rw [show (amm4SwapToWord I).toByteArray.extract 0 32 =
      (amm4SwapToWord I).toByteArray by
    rw [show 32 = (amm4SwapToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem amm4SwapTransfer1CalldataMem_read (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138) :
    (amm4SwapTransfer1CalldataMem I q0 q1 o0).readWithPadding
      (amm4MintToken0FreePtr o0).toNat 68 =
      transferSelector ++ q1.toByteArray ++
        (amm4SwapToWord I).toByteArray := by
  have hsize := amm4SwapTransfer1CalldataMem_size I q0 q1 o0 hlo hbound
  rw [byteArray_readWithPadding_split _ _ 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)]
  rw [amm4SwapTransfer1CalldataMem_read4 I q0 q1 hlo hbound]
  rw [byteArray_readWithPadding_split _ _ 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega)]
  have hsum : (amm4MintToken0FreePtr o0).toNat + 4 + 32 =
      (amm4MintToken0FreePtr o0).toNat + 36 := by omega
  rw [hsum, ← amm4MintToken0FreePtr_add4_toNat o0 hlo hbound,
    ← amm4BurnToken0FreePtr_add36_toNat o0 hlo hbound,
    amm4SwapTransfer1CalldataMem_readAmount I q0 q1 hlo hbound,
    amm4SwapTransfer1CalldataMem_readTo I q0 q1 hlo hbound]
  exact ByteArray.append_assoc.symm

theorem amm4SwapTransfer1CalldataMem_encode (I : ExecutionEnv)
    (q0 q1 : UInt256) {o0 : ByteArray}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hto : (amm4SwapToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat q1.toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))] =
      some ((amm4SwapTransfer1CalldataMem I q0 q1 o0).readWithPadding
        (amm4MintToken0FreePtr o0).toNat 68) := by
  rw [amm4SwapTransfer1CalldataMem_read I q0 q1 hlo hbound]
  have hq : EVM.word q1.toNat = q1 := u256_ofNat_toNat _
  have ht : EVM.word ↑(AccountAddress.ofUInt256 (amm4SwapToWord I)) =
      amm4SwapToWord I := by
    have h := valueToWord_address_ofNat_canonical
      (amm4SwapToWord I) hto
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat] at h
    simpa [valueToWord] using h
  simp [config, externalABI, ABI.encodeCallWithSelector?,
    ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
    ABI.encodeABIWord?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, uint256, uint256Int, addr, transferSelector,
    selectorBytes, hq, ht]
  have hlt : q1.toNat < EVM.twoPow 256 := by
    change q1.toNat < UInt256.size
    exact q1.val.isLt
  simp only [hlt, ite_true, Option.bind, bind]
  have hbytes :
      (EVM.Word.toBytesBE q1 ++
        EVM.Word.toBytesBE (amm4SwapToWord I)).toByteArray =
      q1.toByteArray ++ (amm4SwapToWord I).toByteArray := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray q1,
      ← word_toBytesBE_toByteArray_eq_toByteArray (amm4SwapToWord I)]
    exact list_toByteArray_append _ _
  rw [hbytes]
  exact congrArg some ByteArray.append_assoc.symm

theorem amm4SwapX_transfer1TransferArgs {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {o0 : ByteArray}
    {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hcanon : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2737⟩
      [amm4MintToken0FreePtr o0, amm4SwapToWord I, q1,
        ⟨3077966991⟩, amm4MintToken1Word σ I,
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapTransfer1SelectorMem I q0 o0)
      (amm4SwapTransfer1SelectorWords o0) o0 (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2750⟩
      [amm4MintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        amm4MintToken1Word σ I, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1CalldataMem I q0 q1 o0)
      (amm4SwapTransfer1CalldataWords o0) o0 (cA, σ) k' C' := by
  let fp := amm4MintToken0FreePtr o0
  let awSel := amm4SwapTransfer1SelectorWords o0
  let awAmount := amm4SwapTransfer1AmountWords o0
  let awFinal := amm4SwapTransfer1CalldataWords o0
  have rd5944 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨2750⟩, swap3, swap2, swap1,
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
    (amm4SwapTransfer1AmountMem I q0 q1 o0) awAmount
    rd5963pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awAmount, awSel, fp, amm4SwapTransfer1AmountWords])
    (by unfold amm4SwapTransfer1AmountMem; rfl)
    (by simp [awAmount, fp, amm4SwapTransfer1AmountWords])
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
    (amm4SwapTransfer1CalldataMem I q0 q1 o0) awFinal
    rd5976pre' (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        awFinal, awAmount, fp, amm4SwapTransfer1CalldataWords])
    (by unfold amm4SwapTransfer1CalldataMem; rfl)
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
