import Benchmarks.ActAmm.Swap0TransferTrace
import Benchmarks.ActAmm.Swap1RecipientRevert

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_transferTokenAddress
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2930⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2987⟩
      [ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
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
    simpa only [ammMintToken0Word, solcSlotWord, ammMintDivPow0,
      ammMintMaskTwice] using rd1174⟩

theorem ammSwap1X_transferSelectorMem
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2987⟩
      [ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3009⟩
      [⟨128⟩, ammSwap1ToWord I, ammSwap1AmountWord I,
        ⟨3077966991⟩, ammMintToken0Word σ I,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      ammBurnTransferSelectorMem (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k' C' := by
  have rd1183 := evm_run rd with [
    push4 ⟨3077966991⟩, dup4, dup4, push1 ⟨64⟩]
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
      (ammBurnTransferSelectorWord.toByteArray.write 0
        solcFreePtrMem 128 32)
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [ammBurnTransferSelectorMem, ammBurnTransferSelectorWord]
      using rd1196⟩

noncomputable def ammSwap1TransferCalldataMem (I : ExecutionEnv) : ByteArray :=
  (ammSwap1ToWord I).toByteArray.write 0
    ((ammSwap1AmountWord I).toByteArray.write 0
      ammBurnTransferSelectorMem 132 32) 164 32

theorem ammSwap1TransferArg0Mem_size (I : ExecutionEnv) :
    ((ammSwap1AmountWord I).toByteArray.write 0
      ammBurnTransferSelectorMem 132 32).size = 164 := by
  exact toByteArray_write32_size_of_le ammBurnTransferSelectorMem
    (ammSwap1AmountWord I) 132 160 164
    ammBurnTransferSelectorMem_size
    (by rw [ammBurnTransferSelectorMem_size]; omega) (by omega)

theorem ammSwap1TransferCalldataMem_size (I : ExecutionEnv) :
    (ammSwap1TransferCalldataMem I).size = 196 := by
  unfold ammSwap1TransferCalldataMem
  exact toByteArray_write32_size_of_le
    ((ammSwap1AmountWord I).toByteArray.write 0
      ammBurnTransferSelectorMem 132 32)
    (ammSwap1ToWord I) 164 164 196
    (ammSwap1TransferArg0Mem_size I)
    (by rw [ammSwap1TransferArg0Mem_size]) (by omega)

theorem ammSwap1TransferCalldataMem_read64 (I : ExecutionEnv) :
    (ammSwap1TransferCalldataMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammSwap1TransferCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [ammSwap1TransferArg0Mem_size]) (by omega)]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [ammBurnTransferSelectorMem_size]; omega) (by omega)]
  unfold ammBurnTransferSelectorMem
  rw [toByteArray_write_read_below_of_gap ammBurnTransferSelectorWord
    solcFreePtrMem 128 64 (by rw [solcFreePtrMem_size])
    (by omega) (by rw [solcFreePtrMem_size]; native_decide)]
  exact solcFreePtrMem_read64

theorem ammSwap1TransferCalldataMem_read4 (I : ExecutionEnv) :
    (ammSwap1TransferCalldataMem I).readWithPadding 128 4 =
      transferSelector := by
  unfold ammSwap1TransferCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (by rw [ammSwap1TransferArg0Mem_size]) (by omega)
    (by rw [ammSwap1TransferArg0Mem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by rw [ammBurnTransferSelectorMem_size]; omega) (by omega)
    (by rw [ammBurnTransferSelectorMem_size]; omega)
    (by norm_num) (by norm_num)]
  rw [readWithPadding_eq_extract' _ 128 4
    (by norm_num) (by norm_num)
    (by rw [ammBurnTransferSelectorMem_size]; omega)]
  exact ammBurnTransferSelectorMem_selector

theorem ammSwap1TransferCalldataMem_readAmount (I : ExecutionEnv) :
    (ammSwap1TransferCalldataMem I).readWithPadding 132 32 =
      (ammSwap1AmountWord I).toByteArray := by
  unfold ammSwap1TransferCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
    (by rw [ammSwap1TransferArg0Mem_size]) (by omega)]
  rw [write32_read_back _ _ 132 (by rw [toByteArray_size])
    (by rw [ammBurnTransferSelectorMem_size]; omega)]
  rw [show (ammSwap1AmountWord I).toByteArray.extract 0 32 =
      (ammSwap1AmountWord I).toByteArray by
    rw [show 32 = (ammSwap1AmountWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammSwap1TransferCalldataMem_readTo (I : ExecutionEnv) :
    (ammSwap1TransferCalldataMem I).readWithPadding 164 32 =
      (ammSwap1ToWord I).toByteArray := by
  unfold ammSwap1TransferCalldataMem
  rw [write32_read_back _ _ 164 (by rw [toByteArray_size])
    (by rw [ammSwap1TransferArg0Mem_size])]
  rw [show (ammSwap1ToWord I).toByteArray.extract 0 32 =
      (ammSwap1ToWord I).toByteArray by
    rw [show 32 = (ammSwap1ToWord I).toByteArray.size by
      rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem ammSwap1TransferCalldataMem_read (I : ExecutionEnv) :
    (ammSwap1TransferCalldataMem I).readWithPadding 128 68 =
      transferSelector ++ (ammSwap1AmountWord I).toByteArray ++
        (ammSwap1ToWord I).toByteArray := by
  rw [byteArray_readWithPadding_split _ 128 4 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [ammSwap1TransferCalldataMem_size])]
  rw [ammSwap1TransferCalldataMem_read4]
  rw [byteArray_readWithPadding_split _ 132 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [ammSwap1TransferCalldataMem_size])]
  rw [ammSwap1TransferCalldataMem_readAmount,
    ammSwap1TransferCalldataMem_readTo]
  exact ByteArray.append_assoc.symm

theorem ammSwap1TransferCalldataMem_encode (I : ExecutionEnv)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus) :
    config.externalABI.encode? "transfer"
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))] =
      some ((ammSwap1TransferCalldataMem I).readWithPadding 128 68) := by
  rw [ammSwap1TransferCalldataMem_read]
  have hq : EVM.word (ammSwap1AmountWord I).toNat =
      ammSwap1AmountWord I := u256_ofNat_toNat _
  have ht : EVM.word ↑(AccountAddress.ofUInt256 (ammSwap1ToWord I)) =
      ammSwap1ToWord I := by
    have h := valueToWord_address_ofNat_canonical
      (ammSwap1ToWord I) hcanon
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat] at h
    simpa [valueToWord] using h
  simp [config, externalABI, ABI.encodeCallWithSelector?,
    ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, ABI.encodeABIValue?,
    ABI.encodeABIWord?, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, uint256, uint256Int, addr, transferSelector,
    selectorBytes, hq, ht]
  have hlt : (ammSwap1AmountWord I).toNat < EVM.twoPow 256 := by
    change (ammSwap1AmountWord I).toNat < UInt256.size
    exact (ammSwap1AmountWord I).val.isLt
  simp only [hlt, ite_true, Option.bind, bind]
  have hbytes :
      (EVM.Word.toBytesBE (ammSwap1AmountWord I) ++
        EVM.Word.toBytesBE (ammSwap1ToWord I)).toByteArray =
      (ammSwap1AmountWord I).toByteArray ++
        (ammSwap1ToWord I).toByteArray := by
    rw [← word_toBytesBE_toByteArray_eq_toByteArray (ammSwap1AmountWord I),
      ← word_toBytesBE_toByteArray_eq_toByteArray (ammSwap1ToWord I)]
    exact list_toByteArray_append _ _
  rw [hbytes]
  exact congrArg some ByteArray.append_assoc.symm

theorem ammSwap1X_transferArgs
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3009⟩
      [⟨128⟩, ammSwap1ToWord I, ammSwap1AmountWord I,
        ⟨3077966991⟩, ammMintToken0Word σ I,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      ammBurnTransferSelectorMem (UInt256.ofNat 5) ByteArray.empty
      (cA, σ) k C)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus) :
    ∃ k' C', RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3022⟩
      [⟨196⟩, ⟨3077966991⟩, ammMintToken0Word σ I,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferCalldataMem I)
      (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
  let mem0 := ammBurnTransferSelectorMem
  let mem1 := (ammSwap1AmountWord I).toByteArray.write 0 mem0 132 32
  let mem2 := (ammSwap1ToWord I).toByteArray.write 0 mem1 164 32
  have rd6284 := evm_run rd with [
    push1 ⟨4⟩, add, push2 ⟨3022⟩, swap3, swap2, swap1,
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
  have rd6278' := rd6278
  rw [solcAddrMask_clean hcanon] at rd6278'
  have rd6316 := evm_run rd6278' with [
    jumpdest, dup3,
    raw mstore 3 mem2 (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd1209 := evm_run rd6316 with [
    jumpdest, swap4, swap3, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [mem0, mem1, mem2, ammSwap1TransferCalldataMem]
      using rd1209⟩

theorem ammSwap1X_transferCallFrame
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3022⟩
      [⟨196⟩, ⟨3077966991⟩, ammMintToken0Word σ I,
        ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferCalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k C) :
    ∃ (gasWord : UInt256) (k' C' : Nat), RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨3035⟩
      [gasWord, ammMintToken0Word σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩,
        ⟨128⟩, ⟨32⟩, ⟨196⟩, ⟨3077966991⟩,
        ammMintToken0Word σ I, ammSwap1ToWord I,
        ammSwap1AmountWord I, ⟨340⟩, sel]
      (ammSwap1TransferCalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammSwap1TransferCalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((ammSwap1TransferCalldataMem I).readWithPadding 64 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [ammSwap1TransferCalldataMem_size]; decide)
      (by decide) (ammSwap1TransferCalldataMem_read64 I)
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

end Benchmarks.ActAmm
