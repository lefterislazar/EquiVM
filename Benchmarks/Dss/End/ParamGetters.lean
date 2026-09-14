import Benchmarks.Dss.End.Dispatcher65
import Benchmarks.Dss.End.Dispatcher114
import Benchmarks.Dss.End.Dispatcher174223
import Benchmarks.Dss.End.Dispatcher294343
import Benchmarks.Dss.End.RuntimeBlocks_003
import Benchmarks.Dss.End.RuntimeBlocks_004
import Benchmarks.Dss.End.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## Shared calldata and storage helpers for public mapping getters -/

abbrev endArg0Word (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev endArg1Word (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev endArg0AddressWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endArg0Word I)

abbrev endArg1AddressWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endArg1Word I)

abbrev endArg1AddressValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (endArg1Word I).toNat)

abbrev endArg1AddressKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (endArg1Word I).toNat)

abbrev endArg0AddressValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (endArg0Word I).toNat)

abbrev endArg0AddressKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (endArg0Word I).toNat)

abbrev endArg0AddressStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (endArg0AddressValue I)

abbrev endArg0Bytes32Value (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev endArg0Bytes32Key (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)

abbrev endArg0Bytes32Store (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (endArg0Bytes32Value I)

abbrev endOutStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "arg0" (endArg0Bytes32Value I)).insert "arg1" (endArg1AddressValue I)

def endMappingWord (σ : AccountMap) (I : ExecutionEnv) (baseSlot key : UInt256) : UInt256 :=
  solcSlotWord σ I (solcMappingSlot baseSlot key)

def endNestedMappingWord (σ : AccountMap) (I : ExecutionEnv)
    (baseSlot owner spender : UInt256) : UInt256 :=
  solcSlotWord σ I (solcMappingSlot (solcMappingSlot baseSlot owner) spender)

theorem endSolcDecodeLenCheckShortUnsigned_4_32 {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsize : I.calldata.size < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
  apply ult_one
  rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
  change I.calldata.size - 4 < 32
  omega

theorem endSolcDecodeLenCheckOkUnsigned_4_32 {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨32⟩ : UInt256))
    (by simpa using hsz36) hsize

theorem endSolcDecodeLenCheckShortUnsigned_4_64 {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
  apply ult_one
  rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
  change I.calldata.size - 4 < 64
  omega

theorem endSolcDecodeLenCheckOkUnsigned_4_64 {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ := by
  exact solcDecodeLenCheckOkUnsigned
    (head := (⟨4⟩ : UInt256)) (need := (⟨64⟩ : UInt256))
    (by simpa using hsz68) hsize

theorem endDecode_legacyBytes32_arg0_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata =
      some (endArg0Bytes32Store I) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, isDynamicABIType]
  have hnotShort : ¬ (I.calldata.toList.drop 4).length < 32 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32] = some 32 by native_decide]
  simp only [Option.bind, bind]
  rw [if_neg hnotShort]
  rw [show decodeABIValues? [bytes32] (I.calldata.toList.drop 4) 0 0 32 32
        DecodeMode.legacySolc05 = some ([endArg0Bytes32Value I], 32) by
    simp only [decodeABIValues?]
    rw [show isDynamicABIType bytes32 = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? bytes32 = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval :
        decodeABIValue? bytes32 (I.calldata.toList.drop 4) 0 DecodeMode.legacySolc05 =
          some (endArg0Bytes32Value I, 32) := by
      simp [bytes32, bytes32Width, endArg0Bytes32Value, decodeABIValue?, readBytes?, htake4]
    rw [hval]
    simp]
  simp [decodeCalldata.insertValues, endArg0Bytes32Store]

theorem endDecode_legacyBytes32_arg0_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [bytes32] I.calldata = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32].any isDynamicABIType = true ∧ 2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, isDynamicABIType]
  have hshortArgs : (I.calldata.toList.drop 4).length < 32 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32] = some 32 by native_decide]
  simp only [Option.bind, bind]
  rw [if_pos hshortArgs]

theorem endDecode_legacyAddress_arg0_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [addr] I.calldata =
      some (endArg0AddressStore I) := by
  simpa [addr, endArg0AddressStore, endArg0AddressValue, endArg0Word] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem endDecode_legacyAddress_arg0_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [addr] I.calldata = none := by
  simpa [addr] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort)

theorem endDecode_legacyBytes32_address_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0", "arg1"] [bytes32, addr] I.calldata =
      some (endOutStore I) := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
      calldataWord I.calldata 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32, addr].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, addr, isDynamicABIType]
  have hnotShort : ¬ (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_neg hnotShort]
  rw [show decodeABIValues? [bytes32, addr] (I.calldata.toList.drop 4) 0 0 64 64
        DecodeMode.legacySolc05 =
        some ([endArg0Bytes32Value I, endArg1AddressValue I], 64) by
    simp only [decodeABIValues?]
    rw [show isDynamicABIType bytes32 = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? bytes32 = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval0 :
        decodeABIValue? bytes32 (I.calldata.toList.drop 4) 0 DecodeMode.legacySolc05 =
          some (endArg0Bytes32Value I, 32) := by
      simp [bytes32, bytes32Width, endArg0Bytes32Value, decodeABIValue?, readBytes?, htake4]
    rw [hval0]
    simp only [Nat.reduceAdd, beq_self_eq_true, if_true]
    rw [show isDynamicABIType addr = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? addr = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval1 :
        decodeABIValue? addr (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
          some (endArg1AddressValue I, 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := addr) (bytes := I.calldata.toList.drop 4) (start := 32) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiAddress
          (I.calldata.toList.drop 4) 32 = some (endArg1AddressValue I, 64)
      rw [decodeScalarWord_legacyAddress_ok (bytes := I.calldata.toList.drop 4)
        (start := 32) htake36]
      rw [hword36]
    rw [hval1]
    simp]
  simp [decodeCalldata.insertValues, endOutStore]

theorem endDecode_legacyBytes32_address_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0", "arg1"] [bytes32, addr] I.calldata =
      none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32, addr].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, addr, isDynamicABIType]
  have hshortArgs : (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, addr] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_pos hshortArgs]

@[simp] theorem endConfig_storage_tag (ilk : KeyValue) :
    config.storage.layout { base := "tag", steps := [.mindex ilk] } =
      fun _ => some (wordLoc (tagSlot ilk)) :=
  rfl

@[simp] theorem endConfig_storage_wards (usr : KeyValue) :
    config.storage.layout { base := "wards", steps := [.mindex usr] } =
      fun _ => some (wordLoc (wardsSlot usr)) :=
  rfl

@[simp] theorem endConfig_storage_gap (ilk : KeyValue) :
    config.storage.layout { base := "gap", steps := [.mindex ilk] } =
      fun _ => some (wordLoc (gapSlot ilk)) :=
  rfl

@[simp] theorem endConfig_storage_Art (ilk : KeyValue) :
    config.storage.layout { base := "Art", steps := [.mindex ilk] } =
      fun _ => some (wordLoc (ArtSlot ilk)) :=
  rfl

@[simp] theorem endConfig_storage_fix (ilk : KeyValue) :
    config.storage.layout { base := "fix", steps := [.mindex ilk] } =
      fun _ => some (wordLoc (fixSlot ilk)) :=
  rfl

@[simp] theorem endConfig_storage_bag (usr : KeyValue) :
    config.storage.layout { base := "bag", steps := [.mindex usr] } =
      fun _ => some (wordLoc (bagSlot usr)) :=
  rfl

@[simp] theorem endConfig_storage_out (ilk usr : KeyValue) :
    config.storage.layout { base := "out", steps := [.mindex ilk, .mindex usr] } =
      fun _ => some (wordLoc (outSlot ilk usr)) :=
  rfl

theorem endArg0Bytes32_key_word (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (endArg0Bytes32Key I) = endArg0Word I := by
  have hword : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hbytes :
      EVM.Word.toBytesBE (endArg0Word I) = (I.calldata.toList.drop 4).take 32 := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length hlen
  change keyValueToWord (.fixedBytes bytes32Width ((I.calldata.toList.drop 4).take 32)) =
    endArg0Word I
  rw [← hbytes]
  simpa [endArg0Bytes32Key, bytes32Width] using
    (keyValueToWord_fixedBytes32 (endArg0Word I))

theorem endTagSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    tagSlot (endArg0Bytes32Key I) = solcMappingSlot ⟨12⟩ (endArg0Word I) := by
  rw [tagSlot, mapSlot, solcMappingSlot, endArg0Bytes32_key_word I hsz36]

theorem endGapSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    gapSlot (endArg0Bytes32Key I) = solcMappingSlot ⟨13⟩ (endArg0Word I) := by
  rw [gapSlot, mapSlot, solcMappingSlot, endArg0Bytes32_key_word I hsz36]

theorem endArtSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    ArtSlot (endArg0Bytes32Key I) = solcMappingSlot ⟨14⟩ (endArg0Word I) := by
  rw [ArtSlot, mapSlot, solcMappingSlot, endArg0Bytes32_key_word I hsz36]

theorem endFixSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    fixSlot (endArg0Bytes32Key I) = solcMappingSlot ⟨15⟩ (endArg0Word I) := by
  rw [fixSlot, mapSlot, solcMappingSlot, endArg0Bytes32_key_word I hsz36]

theorem endArg0Address_key_word (I : ExecutionEnv) :
    keyValueToWord (endArg0AddressKey I) = endArg0AddressWord I := by
  simpa [endArg0AddressKey, endArg0AddressWord, endArg0Word] using
    (keyValueToWord_address_ofNat_mask (endArg0Word I))

theorem endArg1Address_key_word (I : ExecutionEnv) :
    keyValueToWord (endArg1AddressKey I) = endArg1AddressWord I := by
  simpa [endArg1AddressKey, endArg1AddressWord, endArg1Word] using
    (keyValueToWord_address_ofNat_mask (endArg1Word I))

theorem endWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (endArg0AddressKey I) = solcMappingSlot ⟨0⟩ (endArg0AddressWord I) := by
  rw [wardsSlot, mapSlot, solcMappingSlot, endArg0Address_key_word I]

theorem endBagSlot_eq (I : ExecutionEnv) :
    bagSlot (endArg0AddressKey I) = solcMappingSlot ⟨16⟩ (endArg0AddressWord I) := by
  rw [bagSlot, mapSlot, solcMappingSlot, endArg0Address_key_word I]

theorem endOutSlot_eq (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    outSlot (endArg0Bytes32Key I) (endArg1AddressKey I) =
      solcMappingSlot (solcMappingSlot ⟨17⟩ (endArg0Word I)) (endArg1AddressWord I) := by
  have hsz36 : 36 ≤ I.calldata.size := by omega
  simp [outSlot, outIlkSlot, mapSlot, solcMappingSlot, endArg0Bytes32_key_word I hsz36,
    endArg1Address_key_word I]

theorem endTagBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract evm (endArg0Bytes32Store I) tagTransition.body
      (.returned { contract := contract, locals := endArg0Bytes32Store I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (tagSlot (endArg0Bytes32Key I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
        have htlen : I.calldata.toList.length = I.calldata.size := by
          rw [byteArray_toList_eq, Array.length_toList]
          rfl
        rw [List.length_take, List.length_drop, htlen]
        omega
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endArg0Bytes32Store, tagRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, tagRef, endArg0Bytes32Store,
            endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_tag (endArg0Bytes32Key I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endGapBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract evm (endArg0Bytes32Store I) gapTransition.body
      (.returned { contract := contract, locals := endArg0Bytes32Store I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (gapSlot (endArg0Bytes32Key I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
        have htlen : I.calldata.toList.length = I.calldata.size := by
          rw [byteArray_toList_eq, Array.length_toList]
          rfl
        rw [List.length_take, List.length_drop, htlen]
        omega
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endArg0Bytes32Store, gapRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, gapRef, endArg0Bytes32Store,
            endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_gap (endArg0Bytes32Key I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endArtBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract evm (endArg0Bytes32Store I) ArtTransition.body
      (.returned { contract := contract, locals := endArg0Bytes32Store I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (ArtSlot (endArg0Bytes32Key I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
        have htlen : I.calldata.toList.length = I.calldata.size := by
          rw [byteArray_toList_eq, Array.length_toList]
          rfl
        rw [List.length_take, List.length_drop, htlen]
        omega
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endArg0Bytes32Store, ArtRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, ArtRef, endArg0Bytes32Store,
            endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_Art (endArg0Bytes32Key I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endFixBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract evm (endArg0Bytes32Store I) fixTransition.body
      (.returned { contract := contract, locals := endArg0Bytes32Store I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (fixSlot (endArg0Bytes32Key I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
        have htlen : I.calldata.toList.length = I.calldata.size := by
          rw [byteArray_toList_eq, Array.length_toList]
          rfl
        rw [List.length_take, List.length_drop, htlen]
        omega
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endArg0Bytes32Store, fixRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, fixRef, endArg0Bytes32Store,
            endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_fix (endArg0Bytes32Key I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endWardsBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (endArg0AddressStore I) wardsTransition.body
      (.returned { contract := contract, locals := endArg0AddressStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (wardsSlot (endArg0AddressKey I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endArg0AddressStore, wardsRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, wardsRef, endArg0AddressStore,
            endArg0AddressValue, endArg0AddressKey, valueToKey?,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_wards (endArg0AddressKey I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endBagBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (endArg0AddressStore I) bagTransition.body
      (.returned { contract := contract, locals := endArg0AddressStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (bagSlot (endArg0AddressKey I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endArg0AddressStore, bagRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, bagRef, endArg0AddressStore,
            endArg0AddressValue, endArg0AddressKey, valueToKey?,
            EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_bag (endArg0AddressKey I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endOutBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size) :
    ExecTransitionBody config contract evm (endOutStore I) outTransition.body
      (.returned { contract := contract, locals := endOutStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (outSlot (endArg0Bytes32Key I) (endArg1AddressKey I))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
        have htlen : I.calldata.toList.length = I.calldata.size := by
          rw [byteArray_toList_eq, Array.length_toList]
          rfl
        rw [List.length_take, List.length_drop, htlen]
        omega
      have hlenKey : ((I.calldata.toList.drop 4).take 32).length = bytes32Width.val + 1 := by
        simpa [bytes32Width] using hlen
      have harg0 : (endOutStore I).get? "arg0" = some (endArg0Bytes32Value I) := by
        change ((((∅ : Store).insert "arg0" (endArg0Bytes32Value I)).insert "arg1"
          (endArg1AddressValue I)).get? "arg0") = some (endArg0Bytes32Value I)
        rw [store_get_ne ((∅ : Store).insert "arg0" (endArg0Bytes32Value I))
          (k := "arg1") (a := "arg0") (endArg1AddressValue I) (by native_decide)]
        simp
      have harg1 : (endOutStore I).get? "arg1" = some (endArg1AddressValue I) := by
        simp [endOutStore]
      have harg0' : (endOutStore I)["arg0"] = some (endArg0Bytes32Value I) := by
        simpa [Std.HashMap.get?_eq_getElem?] using harg0
      have harg1' : (endOutStore I)["arg1"] = some (endArg1AddressValue I) := by
        simpa [Std.HashMap.get?_eq_getElem?] using harg1
      rw [evalExpr_storage_scalar (t := .int uint256Int)
        (hbase := by simp [endOutStore, outRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, outRef, harg0', harg1',
            endArg0Bytes32Value, endArg0Bytes32Key, endArg1AddressValue,
            endArg1AddressKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
            bind, pure, evalExpr?, bytes32Width, hlenKey])
        (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
        (hloc := endConfig_storage_out (endArg0Bytes32Key I) (endArg1AddressKey I))]
      simp [endRuntimeStorageLocLoad_uint256])

theorem endX_singleMappingFromRoutine {cA gh bl σ σ₀ A I} {g : Sat256} {sel baseSlot key routine : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) routine
      [key, ⟨509⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : solcSingleMappingGetterWf endBytecode routine baseSlot) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I baseSlot key)) := by
  obtain ⟨_, _, rdRoutine⟩ := hreach
  obtain ⟨_, _, rdReturn⟩ := RD.solcSingleMappingGetter
    (baseSlot := baseSlot) (key := key) (ret := ⟨509⟩) (R := [sel])
    rdRoutine hwf (by jump_dest) (by simp)
  simpa [endMappingWord] using
    (RD.solcReturnWordFromMem (pc := ⟨509⟩)
      (val := solcSlotWord σ I (solcMappingSlot baseSlot key))
      (ret := ⟨509⟩) (R := [sel]) rdReturn
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide)
      (solcMappingHashMem_mload64 baseSlot key)
      (by rfl)
      (solcScratchReturnMem_mload64
        (solcSlotWord σ I (solcMappingSlot baseSlot key))
        (solcMappingHashMem_size baseSlot key)
        (solcMappingHashMem_read64 baseSlot key))
      (solcScratchReturnMem_read128
        (solcSlotWord σ I (solcMappingSlot baseSlot key))
        (solcMappingHashMem_size baseSlot key))
      (by simp))

theorem endX_singleMappingReturn {cA gh bl σ σ₀ A I} {g : Sat256} {sel baseSlot key : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [solcSlotWord σ I (solcMappingSlot baseSlot key), ⟨509⟩, sel]
      (solcMappingHashMem baseSlot key) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I baseSlot key)) := by
  obtain ⟨_, _, rdReturn⟩ := hreach
  simpa [endMappingWord] using
    (RD.solcReturnWordFromMem (pc := ⟨509⟩)
      (val := solcSlotWord σ I (solcMappingSlot baseSlot key))
      (ret := ⟨509⟩) (R := [sel]) rdReturn
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide)
      (solcMappingHashMem_mload64 baseSlot key)
      (by rfl)
      (solcScratchReturnMem_mload64
        (solcSlotWord σ I (solcMappingSlot baseSlot key))
        (solcMappingHashMem_size baseSlot key)
        (solcMappingHashMem_read64 baseSlot key))
      (solcScratchReturnMem_read128
        (solcSlotWord σ I (solcMappingSlot baseSlot key))
        (solcMappingHashMem_size baseSlot key))
      (by simp))

theorem endX_nestedMappingReturn {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel baseSlot owner spender : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [solcSlotWord σ I (solcMappingSlot (solcMappingSlot baseSlot owner) spender),
        ⟨509⟩, sel]
      (solcNestedMappingHashMem baseSlot owner spender) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endNestedMappingWord σ I baseSlot owner spender)) := by
  obtain ⟨_, _, rdReturn⟩ := hreach
  simpa [endNestedMappingWord] using
    (RD.solcReturnWordFromMem (pc := ⟨509⟩)
      (val := solcSlotWord σ I (solcMappingSlot (solcMappingSlot baseSlot owner) spender))
      (ret := ⟨509⟩) (R := [sel]) rdReturn
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide)
      (solcNestedMappingHashMem_mload64 baseSlot owner spender)
      (by rfl)
      (solcScratchReturnMem_mload64
        (solcSlotWord σ I (solcMappingSlot (solcMappingSlot baseSlot owner) spender))
        (solcNestedMappingHashMem_size baseSlot owner spender)
        (solcNestedMappingHashMem_read64 baseSlot owner spender))
      (solcScratchReturnMem_read128
        (solcSlotWord σ I (solcMappingSlot (solcMappingSlot baseSlot owner) spender))
        (solcNestedMappingHashMem_size baseSlot owner spender))
      (by simp))

theorem endReachTag {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 12)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1245⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 12 (by omega) hsel
  obtain ⟨_, _, h65⟩ := endReachFirstArm65 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm65Eq I hsz 0 (by omega))
        (by simpa [endArm65Index] using
          endSelectorMiss_of_match 2 12 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm65Eq I hsz 1 (by omega))
        (by simpa [endArm65Index] using
          endSelectorMiss_of_match 13 12 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm65Eq I hsz 2 (by omega))
      (by simpa [endArm65Index] using hsel)
  exact RD.dispatchTo ⟨1245⟩ 2 h65
    (fun j hj => endArms65WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachGap {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 13)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 13 (by omega) hsel
  obtain ⟨_, _, h65⟩ := endReachFirstArm65 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm65Eq I hsz 0 (by omega))
      (by simpa [endArm65Index] using
        endSelectorMiss_of_match 2 13 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm65Eq I hsz 1 (by omega))
      (by simpa [endArm65Index] using hsel)
  exact RD.dispatchTo ⟨1216⟩ 1 h65
    (fun j hj => endArms65WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachArt {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 14)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1142⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 14 (by omega) hsel
  obtain ⟨_, _, h114⟩ := endReachFirstArm114 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm114Eq I hsz 0 (by omega))
      (by simpa [endArm114Index] using
        endSelectorMiss_of_match 20 14 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm114Eq I hsz 1 (by omega))
      (by simpa [endArm114Index] using hsel)
  exact RD.dispatchTo ⟨1142⟩ 1 h114
    (fun j hj => endArms114WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachFix {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 15)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨723⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 15 (by omega) hsel
  obtain ⟨_, _, h343⟩ := endReachFirstArm343 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm343Eq I hsz 0 (by omega))
      (by simpa [endArm343Index] using
        endSelectorMiss_of_match 4 15 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm343Eq I hsz 1 (by omega))
      (by simpa [endArm343Index] using hsel)
  exact RD.dispatchTo ⟨723⟩ 1 h343
    (fun j hj => endArms343WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachWards {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 0)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 0 (by omega) hsel
  obtain ⟨_, _, h174⟩ := endReachFirstArm174 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm174Eq I hsz 0 (by omega))
      (by simpa [endArm174Index] using hsel)
  exact RD.dispatchTo ⟨979⟩ 0 h174
    (fun j hj => endArms174WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachOut {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 17)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1054⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 17 (by omega) hsel
  obtain ⟨_, _, h174⟩ := endReachFirstArm174 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm174Eq I hsz 0 (by omega))
        (by simpa [endArm174Index] using
          endSelectorMiss_of_match 0 17 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm174Eq I hsz 1 (by omega))
        (by simpa [endArm174Index] using
          endSelectorMiss_of_match 3 17 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm174Eq I hsz 2 (by omega))
        (by simpa [endArm174Index] using
          endSelectorMiss_of_match 23 17 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm174Eq I hsz 3 (by omega))
      (by simpa [endArm174Index] using hsel)
  exact RD.dispatchTo ⟨1054⟩ 3 h174
    (fun j hj => endArms174WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachBag {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 16)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨895⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 16 (by omega) hsel
  obtain ⟨_, _, h223⟩ := endReachFirstArm223 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm223Eq I hsz 0 (by omega))
      (by simpa [endArm223Index] using
        endSelectorMiss_of_match 26 16 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm223Eq I hsz 1 (by omega))
      (by simpa [endArm223Index] using hsel)
  exact RD.dispatchTo ⟨895⟩ 1 h223
    (fun j hj => endArms223WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endX_tag_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I ⟨12⟩ (endArg0Word I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1267 := endRuntimeBlocks.endRuntime_block_1245_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd9591 := endRuntimeBlocks.endRuntime_block_1267
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1245_taken_stack] using rd1267)
  exact endX_singleMappingFromRoutine
    (baseSlot := ⟨12⟩) (key := endArg0Word I) (routine := ⟨9591⟩)
    (by
      exact ⟨_, _, by
        simpa [endRuntimeBlocks.endRuntime_block_1267_stack, endArg0Word, calldataWord] using rd9591⟩)
    (by dsimp [solcSingleMappingGetterWf]; repeat' first | apply And.intro | native_decide)

theorem endX_tag_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1263 := endRuntimeBlocks.endRuntime_block_1245_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1263 (R :=
      endRuntimeBlocks.endRuntime_block_1245_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1245_fallthrough_stack]) (by simpa using rd1263)

theorem endX_gap_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I ⟨13⟩ (endArg0Word I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1238 := endRuntimeBlocks.endRuntime_block_1216_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd9573 := endRuntimeBlocks.endRuntime_block_1238
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1216_taken_stack] using rd1238)
  exact endX_singleMappingFromRoutine
    (baseSlot := ⟨13⟩) (key := endArg0Word I) (routine := ⟨9573⟩)
    (by
      exact ⟨_, _, by
        simpa [endRuntimeBlocks.endRuntime_block_1238_stack, endArg0Word, calldataWord] using rd9573⟩)
    (by dsimp [solcSingleMappingGetterWf]; repeat' first | apply And.intro | native_decide)

theorem endX_gap_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1234 := endRuntimeBlocks.endRuntime_block_1216_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1234 (R :=
      endRuntimeBlocks.endRuntime_block_1216_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1216_fallthrough_stack]) (by simpa using rd1234)

theorem endX_art_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1142⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I ⟨14⟩ (endArg0Word I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1164 := endRuntimeBlocks.endRuntime_block_1142_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd8814 := endRuntimeBlocks.endRuntime_block_1164
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1142_taken_stack] using rd1164)
  exact endX_singleMappingFromRoutine
    (baseSlot := ⟨14⟩) (key := endArg0Word I) (routine := ⟨8814⟩)
    (by
      exact ⟨_, _, by
        simpa [endRuntimeBlocks.endRuntime_block_1164_stack, endArg0Word, calldataWord] using rd8814⟩)
    (by dsimp [solcSingleMappingGetterWf]; repeat' first | apply And.intro | native_decide)

theorem endX_art_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1142⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1160 := endRuntimeBlocks.endRuntime_block_1142_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1160 (R :=
      endRuntimeBlocks.endRuntime_block_1142_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1142_fallthrough_stack]) (by simpa using rd1160)

theorem endX_fix_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨723⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I ⟨15⟩ (endArg0Word I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd745 := endRuntimeBlocks.endRuntime_block_723_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd5251 := endRuntimeBlocks.endRuntime_block_745
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_723_taken_stack] using rd745)
  exact endX_singleMappingFromRoutine
    (baseSlot := ⟨15⟩) (key := endArg0Word I) (routine := ⟨5251⟩)
    (by
      exact ⟨_, _, by
        simpa [endRuntimeBlocks.endRuntime_block_745_stack, endArg0Word, calldataWord] using rd5251⟩)
    (by dsimp [solcSingleMappingGetterWf]; repeat' first | apply And.intro | native_decide)

theorem endX_fix_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨723⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd741 := endRuntimeBlocks.endRuntime_block_723_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_741 (R :=
      endRuntimeBlocks.endRuntime_block_723_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_723_fallthrough_stack]) (by simpa using rd741)

theorem endX_wards_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I ⟨0⟩ (endArg0AddressWord I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1001 := endRuntimeBlocks.endRuntime_block_979_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd7657 := endRuntimeBlocks.endRuntime_block_1001
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_979_taken_stack] using rd1001)
  have hrd7657Key :
      ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7657⟩
        [endArg0AddressWord I, ⟨509⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    have hmask :
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1) = solcAddrMask := by
      native_decide
    exact ⟨_, _, by
      simpa [endRuntimeBlocks.endRuntime_block_1001_stack, endArg0AddressWord,
        endArg0Word, calldataWord, hmask] using rd7657⟩
  obtain ⟨_, _, rd7657Key⟩ := hrd7657Key
  obtain ⟨_, _, rd509⟩ := endRuntimeBlocks.endRuntime_block_7657
    (x0 := endArg0AddressWord I) (x1 := ⟨509⟩) (R := [sel])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (by simp) (by jump_dest) rd7657Key
  exact endX_singleMappingReturn
    (baseSlot := ⟨0⟩) (key := endArg0AddressWord I) (sel := sel)
    (by
      have hmem :
          endRuntimeBlocks.endRuntime_block_7657_memory
              (mem := solcFreePtrMem) (x0 := endArg0AddressWord I) =
            solcMappingHashMem ⟨0⟩ (endArg0AddressWord I) := by
        rfl
      have hslot :
          keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((endArg0AddressWord I).toByteArray.write 0
                ((UInt256.ofNat 0).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 32).toNat 32)
                (UInt256.ofNat 0).toNat 32) =
            solcMappingSlot ⟨0⟩ (endArg0AddressWord I) := by
        change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            (solcMappingHashMem ⟨0⟩ (endArg0AddressWord I)) =
          solcMappingSlot ⟨0⟩ (endArg0AddressWord I)
        unfold keccakWord
        simpa using solcMappingKeccakSlot ⟨0⟩ (endArg0AddressWord I)
      have haw :
          M (M (M (UInt256.ofNat 3) (UInt256.ofNat 32) (⟨32⟩ : UInt256))
              (UInt256.ofNat 0) (⟨32⟩ : UInt256))
            (UInt256.ofNat 0) (UInt256.ofNat 64) = UInt256.ofNat 3 := by
        native_decide
      exact ⟨_, _, by
        simpa [endRuntimeBlocks.endRuntime_block_7657_stack, hmem, hslot,
          storageRead, solcSlotWord, haw] using rd509⟩)

theorem endX_wards_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd997 := endRuntimeBlocks.endRuntime_block_979_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_997 (R :=
      endRuntimeBlocks.endRuntime_block_979_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_979_fallthrough_stack]) (by simpa using rd997)

theorem endX_bag_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨895⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endMappingWord σ I ⟨16⟩ (endArg0AddressWord I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd917 := endRuntimeBlocks.endRuntime_block_895_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd7476 := endRuntimeBlocks.endRuntime_block_917
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_895_taken_stack] using rd917)
  exact endX_singleMappingFromRoutine
    (baseSlot := ⟨16⟩) (key := endArg0AddressWord I) (routine := ⟨7476⟩)
    (by
      have hmask :
          UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1) = solcAddrMask := by
        native_decide
      exact ⟨_, _, by
        simpa [endRuntimeBlocks.endRuntime_block_917_stack, endArg0AddressWord,
          endArg0Word, calldataWord, hmask] using rd7476⟩)
    (by dsimp [solcSingleMappingGetterWf]; repeat' first | apply And.intro | native_decide)

theorem endX_bag_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨895⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd913 := endRuntimeBlocks.endRuntime_block_895_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_913 (R :=
      endRuntimeBlocks.endRuntime_block_895_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_895_fallthrough_stack]) (by simpa using rd913)

theorem endX_out_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1054⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (endNestedMappingWord σ I ⟨17⟩ (endArg0Word I) (endArg1AddressWord I))) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1076 := endRuntimeBlocks.endRuntime_block_1054_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd8239 := endRuntimeBlocks.endRuntime_block_1076
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨509⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1054_taken_stack] using rd1076)
  have hrd8239 :
      ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8239⟩
        [endArg1AddressWord I, endArg0Word I, ⟨509⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    have hmask :
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1) = solcAddrMask := by
      native_decide
    have hoff : ((UInt256.ofNat 32) + (⟨4⟩ : UInt256)).toNat = 36 := by
      native_decide
    exact ⟨_, _, by
      simpa [endRuntimeBlocks.endRuntime_block_1076_stack, endArg1AddressWord,
        endArg1Word, endArg0Word, calldataWord, hmask, hoff] using rd8239⟩
  obtain ⟨_, _, rd8239Args⟩ := hrd8239
  have hwf : solcNestedMappingGetterWf endBytecode ⟨8239⟩ ⟨17⟩ := by
    dsimp [solcNestedMappingGetterWf]
    repeat' first | apply And.intro | native_decide
  obtain ⟨_, _, rdInner⟩ := RD.solcNestedMappingInnerHash
    (pc := ⟨8239⟩) (baseSlot := ⟨17⟩) (owner := endArg0Word I)
    (spender := endArg1AddressWord I) (ret := ⟨509⟩) (R := [sel])
    rd8239Args hwf (by simp)
  obtain ⟨_, _, rdOuter⟩ := RD.solcNestedMappingOuterHash
    (pc := ⟨8239⟩) (baseSlot := ⟨17⟩) (owner := endArg0Word I)
    (spender := endArg1AddressWord I) (ret := ⟨509⟩) (R := [sel])
    rdInner hwf (by simp)
  obtain ⟨_, _, rdLoad⟩ := RD.solcNestedMappingLoadAndJump
    (pc := ⟨8239⟩) (baseSlot := ⟨17⟩)
    (slot := solcMappingSlot (solcMappingSlot ⟨17⟩ (endArg0Word I)) (endArg1AddressWord I))
    (ret := ⟨509⟩) (R := [sel])
    rdOuter hwf (by jump_dest) (by simp)
  exact endX_nestedMappingReturn
    (baseSlot := ⟨17⟩) (owner := endArg0Word I) (spender := endArg1AddressWord I)
    (sel := sel)
    (by exact ⟨_, _, by simpa using rdLoad⟩)

theorem endX_out_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1054⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1072 := endRuntimeBlocks.endRuntime_block_1054_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1072 (R :=
      endRuntimeBlocks.endRuntime_block_1054_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1054_fallthrough_stack]) (by simpa using rd1072)

theorem endTagBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 12))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1245⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 12 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some tagTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 12 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (tagTransition.params.map Param.name) (transitionSignature tagTransition).paramTypes
        I.calldata = some (endArg0Bytes32Store I) := by
      simpa [config, tagTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_ok (I := I) hsz36
    have hslot := endTagSlot_eq I hsz36
    have hword : endMappingWord σ_evm I ⟨12⟩ (endArg0Word I) =
        endMappingWord σ_solm I ⟨12⟩ (endArg0Word I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot ⟨12⟩ (endArg0Word I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endArg0Bytes32Store I) tagTransition.body
          (.returned { contract := contract, locals := endArg0Bytes32Store I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endMappingWord σ_solm I ⟨12⟩ (endArg0Word I)).toNat))])) := by
      simpa [endMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        hslot] using
        endTagBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv) hsz36
    exact (endX_tag_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding (endMappingWord σ_evm I ⟨12⟩ (endArg0Word I))))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (tagTransition.params.map Param.name) (transitionSignature tagTransition).paramTypes
        I.calldata = none := by
      simpa [config, tagTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_none_short (I := I) hsz4 hshort
    exact (endX_tag_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endGapBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 13))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 13 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some gapTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 13 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (gapTransition.params.map Param.name) (transitionSignature gapTransition).paramTypes
        I.calldata = some (endArg0Bytes32Store I) := by
      simpa [config, gapTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_ok (I := I) hsz36
    have hslot := endGapSlot_eq I hsz36
    have hword : endMappingWord σ_evm I ⟨13⟩ (endArg0Word I) =
        endMappingWord σ_solm I ⟨13⟩ (endArg0Word I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot ⟨13⟩ (endArg0Word I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endArg0Bytes32Store I) gapTransition.body
          (.returned { contract := contract, locals := endArg0Bytes32Store I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endMappingWord σ_solm I ⟨13⟩ (endArg0Word I)).toNat))])) := by
      simpa [endMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        hslot] using
        endGapBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv) hsz36
    exact (endX_gap_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding (endMappingWord σ_evm I ⟨13⟩ (endArg0Word I))))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (gapTransition.params.map Param.name) (transitionSignature gapTransition).paramTypes
        I.calldata = none := by
      simpa [config, gapTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_none_short (I := I) hsz4 hshort
    exact (endX_gap_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endArtBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 14))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1142⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 14 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some ArtTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 14 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (ArtTransition.params.map Param.name) (transitionSignature ArtTransition).paramTypes
        I.calldata = some (endArg0Bytes32Store I) := by
      simpa [config, ArtTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_ok (I := I) hsz36
    have hslot := endArtSlot_eq I hsz36
    have hword : endMappingWord σ_evm I ⟨14⟩ (endArg0Word I) =
        endMappingWord σ_solm I ⟨14⟩ (endArg0Word I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot ⟨14⟩ (endArg0Word I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endArg0Bytes32Store I) ArtTransition.body
          (.returned { contract := contract, locals := endArg0Bytes32Store I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endMappingWord σ_solm I ⟨14⟩ (endArg0Word I)).toNat))])) := by
      simpa [endMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        hslot] using
        endArtBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv) hsz36
    exact (endX_art_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding (endMappingWord σ_evm I ⟨14⟩ (endArg0Word I))))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (ArtTransition.params.map Param.name) (transitionSignature ArtTransition).paramTypes
        I.calldata = none := by
      simpa [config, ArtTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_none_short (I := I) hsz4 hshort
    exact (endX_art_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endFixBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 15))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨723⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 15 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some fixTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 15 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (fixTransition.params.map Param.name) (transitionSignature fixTransition).paramTypes
        I.calldata = some (endArg0Bytes32Store I) := by
      simpa [config, fixTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_ok (I := I) hsz36
    have hslot := endFixSlot_eq I hsz36
    have hword : endMappingWord σ_evm I ⟨15⟩ (endArg0Word I) =
        endMappingWord σ_solm I ⟨15⟩ (endArg0Word I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot ⟨15⟩ (endArg0Word I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endArg0Bytes32Store I) fixTransition.body
          (.returned { contract := contract, locals := endArg0Bytes32Store I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endMappingWord σ_solm I ⟨15⟩ (endArg0Word I)).toNat))])) := by
      simpa [endMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        hslot] using
        endFixBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv) hsz36
    exact (endX_fix_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding (endMappingWord σ_evm I ⟨15⟩ (endArg0Word I))))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (fixTransition.params.map Param.name) (transitionSignature fixTransition).paramTypes
        I.calldata = none := by
      simpa [config, fixTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_arg0_none_short (I := I) hsz4 hshort
    exact (endX_fix_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endWardsBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 0))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨979⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 0 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some wardsTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 0 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (wardsTransition.params.map Param.name) (transitionSignature wardsTransition).paramTypes
        I.calldata = some (endArg0AddressStore I) := by
      simpa [config, wardsTransition, transitionSignature, addr] using
        endDecode_legacyAddress_arg0_ok (I := I) hsz36
    have hslot := endWardsSlot_eq I
    have hword : endMappingWord σ_evm I ⟨0⟩ (endArg0AddressWord I) =
        endMappingWord σ_solm I ⟨0⟩ (endArg0AddressWord I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot ⟨0⟩ (endArg0AddressWord I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endArg0AddressStore I) wardsTransition.body
          (.returned { contract := contract, locals := endArg0AddressStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endMappingWord σ_solm I ⟨0⟩ (endArg0AddressWord I)).toNat))])) := by
      simpa [endMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        hslot] using
        endWardsBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    exact (endX_wards_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding (endMappingWord σ_evm I ⟨0⟩ (endArg0AddressWord I))))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (wardsTransition.params.map Param.name) (transitionSignature wardsTransition).paramTypes
        I.calldata = none := by
      simpa [config, wardsTransition, transitionSignature, addr] using
        endDecode_legacyAddress_arg0_none_short (I := I) hsz4 hshort
    exact (endX_wards_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endBagBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 16))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨895⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 16 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some bagTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 16 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (bagTransition.params.map Param.name) (transitionSignature bagTransition).paramTypes
        I.calldata = some (endArg0AddressStore I) := by
      simpa [config, bagTransition, transitionSignature, addr] using
        endDecode_legacyAddress_arg0_ok (I := I) hsz36
    have hslot := endBagSlot_eq I
    have hword : endMappingWord σ_evm I ⟨16⟩ (endArg0AddressWord I) =
        endMappingWord σ_solm I ⟨16⟩ (endArg0AddressWord I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot ⟨16⟩ (endArg0AddressWord I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endArg0AddressStore I) bagTransition.body
          (.returned { contract := contract, locals := endArg0AddressStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endMappingWord σ_solm I ⟨16⟩ (endArg0AddressWord I)).toNat))])) := by
      simpa [endMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount,
        hslot] using
        endBagBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    exact (endX_bag_ok (g := Sat256.ofUInt256 g) hsz36 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding (endMappingWord σ_evm I ⟨16⟩ (endArg0AddressWord I))))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (bagTransition.params.map Param.name) (transitionSignature bagTransition).paramTypes
        I.calldata = none := by
      simpa [config, bagTransition, transitionSignature, addr] using
        endDecode_legacyAddress_arg0_none_short (I := I) hsz4 hshort
    exact (endX_bag_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endOutBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 17))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1054⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 17 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some outTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 17 (by omega) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (outTransition.params.map Param.name) (transitionSignature outTransition).paramTypes
        I.calldata = some (endOutStore I) := by
      simpa [config, outTransition, transitionSignature, bytes32, addr] using
        endDecode_legacyBytes32_address_ok (I := I) hsz68
    have hslot := endOutSlot_eq I hsz68
    have hword : endNestedMappingWord σ_evm I ⟨17⟩ (endArg0Word I) (endArg1AddressWord I) =
        endNestedMappingWord σ_solm I ⟨17⟩ (endArg0Word I) (endArg1AddressWord I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot (solcMappingSlot ⟨17⟩ (endArg0Word I)) (endArg1AddressWord I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (endOutStore I) outTransition.body
          (.returned { contract := contract, locals := endOutStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat
              (endNestedMappingWord σ_solm I ⟨17⟩ (endArg0Word I)
                (endArg1AddressWord I)).toNat))])) := by
      simpa [endNestedMappingWord, solcSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount, hslot] using
        endOutBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv) hsz68
    exact (endX_out_ok (g := Sat256.ofUInt256 g) hsz68 hsize hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simpa [hword])
        hAccounts
        (returnEquiv_of_encode
          (endUint256ReturnEncoding
            (endNestedMappingWord σ_evm I ⟨17⟩ (endArg0Word I) (endArg1AddressWord I))))
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (outTransition.params.map Param.name) (transitionSignature outTransition).paramTypes
        I.calldata = none := by
      simpa [config, outTransition, transitionSignature, bytes32, addr] using
        endDecode_legacyBytes32_address_none_short (I := I) hsz4 hshort
    exact (endX_out_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
