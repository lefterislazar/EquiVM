import Benchmarks.Dss.End.FileUint
import Benchmarks.Dss.End.RuntimeBlocks_012
import Benchmarks.Dss.End.RuntimeBlocks_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Benchmarks.Dss.End

/-! ## `file(bytes32,address)` -/

abbrev endFileAddressStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (endArg1AddressValue I)

abbrev endVatBytes : List UInt8 :=
  [118, 97, 116] ++ List.replicate 29 0

abbrev endCatBytes : List UInt8 :=
  [99, 97, 116] ++ List.replicate 29 0

abbrev endDogBytes : List UInt8 :=
  [100, 111, 103] ++ List.replicate 29 0

abbrev endVowBytes : List UInt8 :=
  [118, 111, 119] ++ List.replicate 29 0

abbrev endPotBytes : List UInt8 :=
  [112, 111, 116] ++ List.replicate 29 0

abbrev endSpotBytes : List UInt8 :=
  [115, 112, 111, 116] ++ List.replicate 28 0

abbrev endCureBytes : List UInt8 :=
  [99, 117, 114, 101] ++ List.replicate 28 0

abbrev endVatWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1939549) (UInt256.ofNat 234)

abbrev endCatWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1628253) (UInt256.ofNat 234)

abbrev endDogWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 6582119) (UInt256.ofNat 232)

abbrev endVowWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 7761783) (UInt256.ofNat 232)

abbrev endPotWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1842141) (UInt256.ofNat 234)

abbrev endSpotWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 484187101) (UInt256.ofNat 226)

abbrev endCureWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1668641381) (UInt256.ofNat 224)

abbrev endAddressSlotWriteWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    UInt256 :=
  setAddressOffset0Word (solcSlotWord σ I slot) (endArg1AddressWord I)

theorem endVatWord_eq : ABI.bytesToWord endVatBytes = endVatWord := by
  native_decide

theorem endCatWord_eq : ABI.bytesToWord endCatBytes = endCatWord := by
  native_decide

theorem endDogWord_eq : ABI.bytesToWord endDogBytes = endDogWord := by
  native_decide

theorem endVowWord_eq : ABI.bytesToWord endVowBytes = endVowWord := by
  native_decide

theorem endPotWord_eq : ABI.bytesToWord endPotBytes = endPotWord := by
  native_decide

theorem endSpotWord_eq : ABI.bytesToWord endSpotBytes = endSpotWord := by
  native_decide

theorem endCureWord_eq : ABI.bytesToWord endCureBytes = endCureWord := by
  native_decide

theorem endVatBytes_len : endVatBytes.length = 32 := by
  native_decide

theorem endCatBytes_len : endCatBytes.length = 32 := by
  native_decide

theorem endDogBytes_len : endDogBytes.length = 32 := by
  native_decide

theorem endVowBytes_len : endVowBytes.length = 32 := by
  native_decide

theorem endPotBytes_len : endPotBytes.length = 32 := by
  native_decide

theorem endSpotBytes_len : endSpotBytes.length = 32 := by
  native_decide

theorem endCureBytes_len : endCureBytes.length = 32 := by
  native_decide

theorem endArg0Word_eq_of_bytes {I : ExecutionEnv} {bs : List UInt8} {w : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hlen : bs.length = 32)
    (hword : ABI.bytesToWord bs = w)
    (hbytes : (I.calldata.toList.drop 4).take 32 = bs) :
    endArg0Word I = w := by
  have hdecoded :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [hbytes, hword] at hdecoded
  exact hdecoded.symm

theorem endArg0Word_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8} {w : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hlen : bs.length = 32)
    (hword : ABI.bytesToWord bs = w)
    (hbytes : (I.calldata.toList.drop 4).take 32 ≠ bs) :
    endArg0Word I ≠ w := by
  intro hwordEq
  have hdecoded :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hleft :
      EVM.Word.toBytesBE (endArg0Word I) = (I.calldata.toList.drop 4).take 32 := by
    rw [← hdecoded]
    exact toBytesBE_bytesToWord_of_length (endArg0Bytes_len hsz36)
  have hright : EVM.Word.toBytesBE w = bs := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length hlen
  exact hbytes (by
    rw [← hleft, hwordEq, hright])

theorem endAccountAddress_ofNat_mask (w : UInt256) :
    AccountAddress.ofNat w.toNat =
      AccountAddress.ofNat (UInt256.land solcAddrMask w).toNat := by
  apply Fin.ext
  change w.toNat % AccountAddress.size =
    (UInt256.land solcAddrMask w).toNat % AccountAddress.size
  rw [u256_land_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  change w.toNat % AccountAddress.size =
    w.toNat % AccountAddress.size % UInt256.size % AccountAddress.size
  have hltAddr : w.toNat % AccountAddress.size < AccountAddress.size :=
    Nat.mod_lt _ (by native_decide)
  have hltWord : w.toNat % AccountAddress.size < UInt256.size :=
    lt_trans hltAddr (by native_decide)
  rw [Nat.mod_eq_of_lt hltWord, Nat.mod_eq_of_lt hltAddr]

theorem endArg1AddressValue_masked (I : ExecutionEnv) :
    endArg1AddressValue I =
      .address (AccountAddress.ofNat (endArg1AddressWord I).toNat) := by
  change Value.address (AccountAddress.ofNat (endArg1Word I).toNat) =
    Value.address (AccountAddress.ofNat (UInt256.land solcAddrMask (endArg1Word I)).toNat)
  rw [endAccountAddress_ofNat_mask]

theorem endArg1AddressWord_canonical (I : ExecutionEnv) :
    (endArg1AddressWord I).toNat < EVM.addressModulus := by
  simpa [endArg1AddressWord, u256_land_comm solcAddrMask (endArg1Word I)] using
    solcAddrMask_result_canonical (endArg1Word I)

theorem endAddressStoreWord_eq (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    UInt256.lor
        (UInt256.land (endArg1AddressWord I)
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)))
        (UInt256.land
          (UInt256.lnot
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1)))
          (storageRead I.codeOwner σ slot)) =
      endAddressSlotWriteWord σ I slot := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endAddressSlotWriteWord setAddressOffset0Word
  rw [hmask, storageRead_eq]
  rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ I slot)]
  rw [u256_lor_comm]

theorem endDecode_legacyBytes32_address_file_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["what", "data"] [bytes32, addr]
        I.calldata =
      some (endFileAddressStore I) := by
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
  simp [decodeCalldata.insertValues, endFileAddressStore]

theorem endDecode_legacyBytes32_address_file_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["what", "data"] [bytes32, addr]
        I.calldata = none := by
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

theorem endFileAddressStore_get_what (I : ExecutionEnv) :
    (endFileAddressStore I).get? "what" = some (endArg0Bytes32Value I) := by
  change ((((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (endArg1AddressValue I)).get? "what") = some (endArg0Bytes32Value I)
  rw [store_get_ne ((∅ : Store).insert "what" (endArg0Bytes32Value I))
    (k := "data") (a := "what") (endArg1AddressValue I) (by decide)]
  exact store_get_self (∅ : Store) "what" (endArg0Bytes32Value I)

theorem endFileAddressStore_get_data (I : ExecutionEnv) :
    (endFileAddressStore I).get? "data" = some (endArg1AddressValue I) := by
  simp [endFileAddressStore, store_get_self]

theorem endFileAddressStore_get_none (I : ExecutionEnv) (name : String)
    (hwhat : name ≠ "what") (hdata : name ≠ "data") :
    (endFileAddressStore I).get? name = none := by
  have hwhatBeq : ("what" == name) = false := by
    by_cases h : "what" = name
    · exact False.elim (hwhat h.symm)
    · simp [h]
  have hdataBeq : ("data" == name) = false := by
    by_cases h : "data" = name
    · exact False.elim (hdata h.symm)
    · simp [h]
  change ((((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (endArg1AddressValue I)).get? name) = none
  rw [store_get_ne ((∅ : Store).insert "what" (endArg0Bytes32Value I))
    (k := "data") (a := name) (endArg1AddressValue I) hdataBeq]
  rw [store_get_ne (∅ : Store) (k := "what") (a := name)
    (endArg0Bytes32Value I) hwhatBeq]
  simp

theorem endEvalAuthStorage_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
        (.storage (wardsRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (wardsSlot (.address evm.executionEnv.source))).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endFileAddressStore_get_none I "wards" (by decide) (by decide))
    (her := by
      simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_wards (.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalAuthGuard_fileAddress_true (evm : EVM.State) (I : ExecutionEnv)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage_fileAddress evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat = 1 := by
    rw [hauth]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalAuthGuard_fileAddress_false (evm : EVM.State) (I : ExecutionEnv)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage_fileAddress evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat ≠ 1 := by
    intro hnat
    exact hauth (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalLiveStorage_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
        (.storage liveRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endFileAddressStore_get_none I "live" (by decide) (by decide))
    (her := by
      simp [evalStorageRef, evalStorageRefStep, liveRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_live)]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalLiveGuard_fileAddress_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_fileAddress evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat = 1 := by
    rw [hlive]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalLiveGuard_fileAddress_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_fileAddress evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat ≠ 1 := by
    intro hnat
    exact hlive (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalWhat_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.var "what") =
      .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endFileAddressStore_get_what I]
  rfl

theorem endEvalData_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.var "data") =
      .ok (endArg1AddressValue I) := by
  rw [evalExpr?]
  rw [endFileAddressStore_get_data I]
  simp [EvalResult.ofOption]

theorem endEvalVatLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm vatLit =
      .ok (Value.fixedBytes bytes32Width endVatBytes) := by
  simp [evalExpr?, vatLit, strLit3, endVatBytes]
  rfl

theorem endEvalCatLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm catLit =
      .ok (Value.fixedBytes bytes32Width endCatBytes) := by
  simp [evalExpr?, catLit, strLit3, endCatBytes]
  rfl

theorem endEvalDogLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm dogLit =
      .ok (Value.fixedBytes bytes32Width endDogBytes) := by
  simp [evalExpr?, dogLit, strLit3, endDogBytes]
  rfl

theorem endEvalVowLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm vowLit =
      .ok (Value.fixedBytes bytes32Width endVowBytes) := by
  simp [evalExpr?, vowLit, strLit3, endVowBytes]
  rfl

theorem endEvalPotLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm potLit =
      .ok (Value.fixedBytes bytes32Width endPotBytes) := by
  simp [evalExpr?, potLit, strLit3, endPotBytes]
  rfl

theorem endEvalSpotLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm spotLit =
      .ok (Value.fixedBytes bytes32Width endSpotBytes) := by
  simp [evalExpr?, spotLit, strLit4, endSpotBytes]
  rfl

theorem endEvalCureLit_fileAddress (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm cureLit =
      .ok (Value.fixedBytes bytes32Width endCureBytes) := by
  simp [evalExpr?, cureLit, strLit4, endCureBytes]
  rfl

theorem endEvalWhatLit_true (evm : EVM.State) (I : ExecutionEnv) (lit : Expr)
    (bs : List UInt8)
    (hlit :
      evalExpr? config { contract := contract, locals := endFileAddressStore I } evm lit =
        .ok (Value.fixedBytes bytes32Width bs))
    (hwhat : (I.calldata.toList.drop 4).take 32 = bs) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") lit) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalWhat_fileAddress evm I]
  rw [hlit]
  change evalBinaryOp? BinaryOp.eq (endArg0Bytes32Value I)
      (Value.fixedBytes bytes32Width bs) = .ok (.bool true)
  simp [evalBinaryOp?, endArg0Bytes32Value, hwhat]

theorem endEvalWhatLit_false (evm : EVM.State) (I : ExecutionEnv) (lit : Expr)
    (bs : List UInt8)
    (hlit :
      evalExpr? config { contract := contract, locals := endFileAddressStore I } evm lit =
        .ok (Value.fixedBytes bytes32Width bs))
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ bs) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") lit) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalWhat_fileAddress evm I]
  rw [hlit]
  change evalBinaryOp? BinaryOp.eq (endArg0Bytes32Value I)
      (Value.fixedBytes bytes32Width bs) = .ok (.bool false)
  simp [evalBinaryOp?, endArg0Bytes32Value, hwhat]

theorem endEvalWhatVat_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endVatBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") vatLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I vatLit endVatBytes (endEvalVatLit_fileAddress evm I) hwhat

theorem endEvalWhatVat_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") vatLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I vatLit endVatBytes (endEvalVatLit_fileAddress evm I) hwhat

theorem endEvalWhatCat_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endCatBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") catLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I catLit endCatBytes (endEvalCatLit_fileAddress evm I) hwhat

theorem endEvalWhatCat_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") catLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I catLit endCatBytes (endEvalCatLit_fileAddress evm I) hwhat

theorem endEvalWhatDog_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endDogBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") dogLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I dogLit endDogBytes (endEvalDogLit_fileAddress evm I) hwhat

theorem endEvalWhatDog_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") dogLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I dogLit endDogBytes (endEvalDogLit_fileAddress evm I) hwhat

theorem endEvalWhatVow_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endVowBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") vowLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I vowLit endVowBytes (endEvalVowLit_fileAddress evm I) hwhat

theorem endEvalWhatVow_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") vowLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I vowLit endVowBytes (endEvalVowLit_fileAddress evm I) hwhat

theorem endEvalWhatPot_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endPotBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") potLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I potLit endPotBytes (endEvalPotLit_fileAddress evm I) hwhat

theorem endEvalWhatPot_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") potLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I potLit endPotBytes (endEvalPotLit_fileAddress evm I) hwhat

theorem endEvalWhatSpot_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endSpotBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") spotLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I spotLit endSpotBytes (endEvalSpotLit_fileAddress evm I) hwhat

theorem endEvalWhatSpot_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endSpotBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") spotLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I spotLit endSpotBytes (endEvalSpotLit_fileAddress evm I) hwhat

theorem endEvalWhatCure_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endCureBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") cureLit) =
      .ok (.bool true) :=
  endEvalWhatLit_true evm I cureLit endCureBytes (endEvalCureLit_fileAddress evm I) hwhat

theorem endEvalWhatCure_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endCureBytes) :
    evalExpr? config { contract := contract, locals := endFileAddressStore I } evm
      (.binary .eq (.var "what") cureLit) =
      .ok (.bool false) :=
  endEvalWhatLit_false evm I cureLit endCureBytes (endEvalCureLit_fileAddress evm I) hwhat

theorem endAssignAddressData (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256) (ref : StorageRef) (er : EvaledStorageRef)
    (hbase : (endFileAddressStore I).get? ref.base = none)
    (her :
      evalStorageRef config { contract := contract, locals := endFileAddressStore I } evm ref =
        .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage ref (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (endArg1AddressWord I))) := by
  rw [endArg1AddressValue_masked I]
  exact assignStorageRef_storage_scalar_value hbase her hty hloc (by trivial) (by
    simpa [addrLoc, addressOffset0Loc] using
      storageLocStore_address_offset0 evm slot (endArg1AddressWord I)
        (endArg1AddressWord_canonical I))

theorem endAssignVatData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage vatRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨1⟩ vatRef
    ({ base := "vat", steps := [] } : EvaledStorageRef)
    (by simpa [vatRef] using endFileAddressStore_get_none I "vat" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, vatRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_vat

theorem endAssignCatData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage catRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨2⟩ catRef
    ({ base := "cat", steps := [] } : EvaledStorageRef)
    (by simpa [catRef] using endFileAddressStore_get_none I "cat" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, catRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_cat

theorem endAssignDogData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage dogRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨3⟩ dogRef
    ({ base := "dog", steps := [] } : EvaledStorageRef)
    (by simpa [dogRef] using endFileAddressStore_get_none I "dog" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, dogRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_dog

theorem endAssignVowData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage vowRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨4⟩ vowRef
    ({ base := "vow", steps := [] } : EvaledStorageRef)
    (by simpa [vowRef] using endFileAddressStore_get_none I "vow" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, vowRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_vow

theorem endAssignPotData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage potRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨5⟩ potRef
    ({ base := "pot", steps := [] } : EvaledStorageRef)
    (by simpa [potRef] using endFileAddressStore_get_none I "pot" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, potRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_pot

theorem endAssignSpotData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage spotRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨6⟩ spotRef
    ({ base := "spot", steps := [] } : EvaledStorageRef)
    (by simpa [spotRef] using endFileAddressStore_get_none I "spot" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, spotRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_spot

theorem endAssignCureData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileAddressStore I } evm
        .storage cureRef (endArg1AddressValue I) =
      .ok ({ contract := contract, locals := endFileAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
            (endArg1AddressWord I))) := by
  exact endAssignAddressData evm I ⟨7⟩ cureRef
    ({ base := "cure", steps := [] } : EvaledStorageRef)
    (by simpa [cureRef] using endFileAddressStore_get_none I "cure" (by decide) (by decide))
    (by simp [evalStorageRef, evalStorageRefStep, cureRef, EvalResult.bind,
      EvalResult.ofOption, bind, pure, evalExpr?])
    (by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, addrSt])
    endConfig_storage_cure

theorem endFileAddressBodyAuthFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (endFileAddressStore I)
      fileAddressTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalAuthGuard_fileAddress_false evm I hauth)))

theorem endFileAddressBodyLiveFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (endFileAddressStore I)
      fileAddressTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalLiveGuard_fileAddress_false evm I hlive)))

theorem endFileAddressBodyVatOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 = endVatBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteTrue (endEvalWhatVat_true evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.assign (endEvalData_fileAddress evm I) (endAssignVatData evm I))
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodyCatOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 = endCatBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.iteTrue (endEvalWhatCat_true evm I hcat) <|
              ExecBlock.consNormal
                (ExecStmt.assign (endEvalData_fileAddress evm I) (endAssignCatData evm I))
                ExecBlock.nil)
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodyDogOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 = endDogBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.iteFalse (endEvalWhatCat_false evm I hcat) <|
              ExecBlock.consNormal
                (ExecStmt.iteTrue (endEvalWhatDog_true evm I hdog) <|
                  ExecBlock.consNormal
                    (ExecStmt.assign (endEvalData_fileAddress evm I) (endAssignDogData evm I))
                    ExecBlock.nil)
                ExecBlock.nil)
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodyVowOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 = endVowBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.iteFalse (endEvalWhatCat_false evm I hcat) <|
              ExecBlock.consNormal
                (ExecStmt.iteFalse (endEvalWhatDog_false evm I hdog) <|
                  ExecBlock.consNormal
                    (ExecStmt.iteTrue (endEvalWhatVow_true evm I hvow) <|
                      ExecBlock.consNormal
                        (ExecStmt.assign (endEvalData_fileAddress evm I) (endAssignVowData evm I))
                        ExecBlock.nil)
                    ExecBlock.nil)
                ExecBlock.nil)
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodyPotOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 = endPotBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.iteFalse (endEvalWhatCat_false evm I hcat) <|
              ExecBlock.consNormal
                (ExecStmt.iteFalse (endEvalWhatDog_false evm I hdog) <|
                  ExecBlock.consNormal
                    (ExecStmt.iteFalse (endEvalWhatVow_false evm I hvow) <|
                      ExecBlock.consNormal
                        (ExecStmt.iteTrue (endEvalWhatPot_true evm I hpot) <|
                          ExecBlock.consNormal
                            (ExecStmt.assign (endEvalData_fileAddress evm I)
                              (endAssignPotData evm I))
                            ExecBlock.nil)
                        ExecBlock.nil)
                    ExecBlock.nil)
                ExecBlock.nil)
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodySpotOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes)
    (hspot : (I.calldata.toList.drop 4).take 32 = endSpotBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.iteFalse (endEvalWhatCat_false evm I hcat) <|
              ExecBlock.consNormal
                (ExecStmt.iteFalse (endEvalWhatDog_false evm I hdog) <|
                  ExecBlock.consNormal
                    (ExecStmt.iteFalse (endEvalWhatVow_false evm I hvow) <|
                      ExecBlock.consNormal
                        (ExecStmt.iteFalse (endEvalWhatPot_false evm I hpot) <|
                          ExecBlock.consNormal
                            (ExecStmt.iteTrue (endEvalWhatSpot_true evm I hspot) <|
                              ExecBlock.consNormal
                                (ExecStmt.assign (endEvalData_fileAddress evm I)
                                  (endAssignSpotData evm I))
                                ExecBlock.nil)
                            ExecBlock.nil)
                        ExecBlock.nil)
                    ExecBlock.nil)
                ExecBlock.nil)
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodyCureOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes)
    (hspot : (I.calldata.toList.drop 4).take 32 ≠ endSpotBytes)
    (hcure : (I.calldata.toList.drop 4).take 32 = endCureBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I) fileAddressTransition.body
      (.returned { contract := contract, locals := endFileAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
            (endArg1AddressWord I)))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consNormal
            (ExecStmt.iteFalse (endEvalWhatCat_false evm I hcat) <|
              ExecBlock.consNormal
                (ExecStmt.iteFalse (endEvalWhatDog_false evm I hdog) <|
                  ExecBlock.consNormal
                    (ExecStmt.iteFalse (endEvalWhatVow_false evm I hvow) <|
                      ExecBlock.consNormal
                        (ExecStmt.iteFalse (endEvalWhatPot_false evm I hpot) <|
                          ExecBlock.consNormal
                            (ExecStmt.iteFalse (endEvalWhatSpot_false evm I hspot) <|
                              ExecBlock.consNormal
                                (ExecStmt.iteTrue (endEvalWhatCure_true evm I hcure) <|
                                  ExecBlock.consNormal
                                    (ExecStmt.assign (endEvalData_fileAddress evm I)
                                      (endAssignCureData evm I))
                                    ExecBlock.nil)
                                ExecBlock.nil)
                            ExecBlock.nil)
                        ExecBlock.nil)
                    ExecBlock.nil)
                ExecBlock.nil)
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileAddressBodyWhatFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes)
    (hspot : (I.calldata.toList.drop 4).take 32 ≠ endSpotBytes)
    (hcure : (I.calldata.toList.drop 4).take 32 ≠ endCureBytes) :
    ExecTransitionBody config contract evm (endFileAddressStore I)
      fileAddressTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileAddress_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileAddress_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.iteFalse (endEvalWhatVat_false evm I hvat) <|
          ExecBlock.consRevert
            (ExecStmt.iteFalse (endEvalWhatCat_false evm I hcat) <|
              ExecBlock.consRevert
                (ExecStmt.iteFalse (endEvalWhatDog_false evm I hdog) <|
                  ExecBlock.consRevert
                    (ExecStmt.iteFalse (endEvalWhatVow_false evm I hvow) <|
                      ExecBlock.consRevert
                        (ExecStmt.iteFalse (endEvalWhatPot_false evm I hpot) <|
                          ExecBlock.consRevert
                            (ExecStmt.iteFalse (endEvalWhatSpot_false evm I hspot) <|
                              ExecBlock.consRevert
                                (ExecStmt.iteFalse (endEvalWhatCure_false evm I hcure) <|
                                  ExecBlock.consRevert
                                    (ExecStmt.requireFalse (by simp [evalExpr?, pure]))))))))))

theorem endReachFileAddress {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 20)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 20 (by omega) hsel
  obtain ⟨_, _, h114⟩ := endReachFirstArm114 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide)
    (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm114Eq I hsz 0 (by omega))
      (by simpa [endArm114Index] using hsel)
  exact RD.dispatchTo ⟨1098⟩ 0 h114
    (fun j hj => endArms114WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endX_fileAddress_to_auth {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8268⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1120 := endRuntimeBlocks.endRuntime_block_1098_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd8268 := endRuntimeBlocks.endRuntime_block_1120
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨562⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1098_taken_stack] using rd1120)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hoff : ((UInt256.ofNat 32) + (⟨4⟩ : UInt256)).toNat = 36 := by
    native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_1120_stack, endArg1AddressWord,
      endArg1Word, endArg0Word, calldataWord, hmask, hoff] using rd8268⟩

theorem endX_fileAddress_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1116 := endRuntimeBlocks.endRuntime_block_1098_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1116 (R :=
      endRuntimeBlocks.endRuntime_block_1098_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1098_fallthrough_stack])
    (by simpa using rd1116)

theorem endX_fileAddress_auth_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileAddress_to_auth (g := g) hsz68 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) = (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem]
    exact uInt256_eq_zero_of_ne (by
      intro heq
      exact hauth (uInt256_eq_one_eq heq).symm)
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_8268_fallthrough
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth rdAuth
  exact endRuntimeBlocks.endRuntime_block_8292
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_fileAddress_live_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileAddress_to_auth (g := g) hsz68 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem, hauth]
    decide
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_8268_taken
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth
    (by jump_dest) rdAuth
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 8)) =
        (UInt256.ofNat 0) := by
    have hlive' : solcSlotWord σ I (UInt256.ofNat 8) ≠ ⟨1⟩ := by
      simpa using hlive
    rw [storageRead_eq]
    change UInt256.eq (UInt256.ofNat 1) (solcSlotWord σ I (UInt256.ofNat 8)) =
      (UInt256.ofNat 0)
    exact uInt256_eq_zero_of_ne (by
      intro heq
      exact hlive' (uInt256_eq_one_eq heq).symm)
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_8357_fallthrough
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondLive rdLive
  exact endRuntimeBlocks.endRuntime_block_8368
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_fileAddress_to_tests {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ mem aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8427⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileAddress_to_auth (g := g) hsz68 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem, hauth]
    decide
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_8268_taken
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth
    (by jump_dest) rdAuth
  have hcondLive :
      UInt256.eq (UInt256.ofNat 1) (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠
        (UInt256.ofNat 0) := by
    have hlive' : solcSlotWord σ I (UInt256.ofNat 8) = ⟨1⟩ := by
      simpa using hlive
    rw [storageRead_eq]
    change UInt256.eq (UInt256.ofNat 1) (solcSlotWord σ I (UInt256.ofNat 8)) ≠
      (UInt256.ofNat 0)
    rw [hlive']
    decide
  obtain ⟨_, _, rdTests⟩ := endRuntimeBlocks.endRuntime_block_8357_taken
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondLive
    (by jump_dest) rdLive
  exact ⟨_, _, _, _, rdTests⟩

theorem endX_fileAddress_tail {cA gh bl σ σ' σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8747⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw rdata (cA, σ') k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ') ByteArray.empty := by
  have rdStop := endRuntimeBlocks.endRuntime_block_8747
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (x2 := ⟨562⟩) (R := [sel])
    (by simp) hperm (by jump_dest) hreach
  exact endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_8747_stack] using rdStop)

theorem endX_fileAddress_store_vat {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8442⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨1⟩ (endAddressSlotWriteWord σ I ⟨1⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8442
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨1⟩
      (endAddressSlotWriteWord σ I ⟨1⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨1⟩]
  exact rdLog

theorem endX_fileAddress_store_cat {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8488⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨2⟩ (endAddressSlotWriteWord σ I ⟨2⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8488
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨2⟩
      (endAddressSlotWriteWord σ I ⟨2⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨2⟩]
  exact rdLog

theorem endX_fileAddress_store_dog {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8534⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨3⟩ (endAddressSlotWriteWord σ I ⟨3⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8534
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨3⟩
      (endAddressSlotWriteWord σ I ⟨3⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨3⟩]
  exact rdLog

theorem endX_fileAddress_store_vow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8580⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨4⟩ (endAddressSlotWriteWord σ I ⟨4⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8580
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨4⟩
      (endAddressSlotWriteWord σ I ⟨4⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨4⟩]
  exact rdLog

theorem endX_fileAddress_store_pot {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8626⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨5⟩ (endAddressSlotWriteWord σ I ⟨5⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8626
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨5⟩
      (endAddressSlotWriteWord σ I ⟨5⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨5⟩]
  exact rdLog

theorem endX_fileAddress_store_spot {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8673⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨6⟩ (endAddressSlotWriteWord σ I ⟨6⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8673
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨6⟩
      (endAddressSlotWriteWord σ I ⟨6⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨6⟩]
  exact rdLog

theorem endX_fileAddress_store_cure {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hperm : I.perm = true)
    (hreach : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8720⟩
      [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel] mem aw ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨7⟩ (endAddressSlotWriteWord σ I ⟨7⟩))
      ByteArray.empty := by
  obtain ⟨kLog, CLog, rdLog⟩ := endRuntimeBlocks.endRuntime_block_8720
    (x0 := endArg1AddressWord I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm hreach
  refine endX_fileAddress_tail (g := g) (σ := σ) (σ' := storageWrite I.codeOwner σ ⟨7⟩
      (endAddressSlotWriteWord σ I ⟨7⟩)) (sel := sel) (mem := mem) (aw := aw)
      (rdata := ByteArray.empty) (k := kLog) (C := CLog) hperm
    ?_
  rw [← endAddressStoreWord_eq σ I ⟨7⟩]
  exact rdLog

theorem endFileAddressCondEq {I : ExecutionEnv} {w : UInt256}
    (hword : endArg0Word I = w) :
    UInt256.isZero (UInt256.eq w (endArg0Word I)) = ⟨0⟩ := by
  rw [hword]
  rw [uInt256_eq_self]
  rfl

theorem endFileAddressCondNe {I : ExecutionEnv} {w : UInt256}
    (hne : w ≠ endArg0Word I) :
    UInt256.isZero (UInt256.eq w (endArg0Word I)) ≠ ⟨0⟩ := by
  have hnotEqOne : ¬ UInt256.eq w (endArg0Word I) = ⟨1⟩ := by
    intro heq
    exact hne (uInt256_eq_one_eq heq)
  rw [uInt256_eq_zero_of_ne hnotEqOne]
  decide

theorem endFileAddressCondEqOfBytes {I : ExecutionEnv} {bs : List UInt8} {w : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hlen : bs.length = 32)
    (hword : ABI.bytesToWord bs = w)
    (hbytes : (I.calldata.toList.drop 4).take 32 = bs) :
    UInt256.isZero (UInt256.eq w (endArg0Word I)) = ⟨0⟩ :=
  endFileAddressCondEq (I := I) (w := w)
    (endArg0Word_eq_of_bytes (I := I) (by omega) hlen hword hbytes)

theorem endFileAddressCondNeOfBytes {I : ExecutionEnv} {bs : List UInt8} {w : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hlen : bs.length = 32)
    (hword : ABI.bytesToWord bs = w)
    (hbytes : (I.calldata.toList.drop 4).take 32 ≠ bs) :
    UInt256.isZero (UInt256.eq w (endArg0Word I)) ≠ ⟨0⟩ := by
  have hneWord : w ≠ endArg0Word I := by
    intro h
    exact endArg0Word_ne_of_bytes_ne (I := I) (by omega) hlen hword hbytes h.symm
  exact endFileAddressCondNe (I := I) (w := w) hneWord

theorem endX_fileAddress_vat_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 = endVatBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨1⟩ (endAddressSlotWriteWord σ I ⟨1⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdStore := endRuntimeBlocks.endRuntime_block_8427_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat rdTests
  exact endX_fileAddress_store_vat (g := g) hperm rdStore

theorem endX_fileAddress_cat_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 = endCatBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨2⟩ (endAddressSlotWriteWord σ I ⟨2⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdStore := endRuntimeBlocks.endRuntime_block_8473_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat rdCat
  exact endX_fileAddress_store_cat (g := g) hperm rdStore

theorem endX_fileAddress_dog_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 = endDogBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨3⟩ (endAddressSlotWriteWord σ I ⟨3⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdDog := endRuntimeBlocks.endRuntime_block_8473_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat (by jump_dest) rdCat
  have hcondDog :
      UInt256.isZero (UInt256.eq endDogWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endDogBytes_len endDogWord_eq hdog
  have rdStore := endRuntimeBlocks.endRuntime_block_8519_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondDog rdDog
  exact endX_fileAddress_store_dog (g := g) hperm rdStore

theorem endX_fileAddress_vow_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 = endVowBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨4⟩ (endAddressSlotWriteWord σ I ⟨4⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdDog := endRuntimeBlocks.endRuntime_block_8473_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat (by jump_dest) rdCat
  have hcondDog :
      UInt256.isZero (UInt256.eq endDogWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endDogBytes_len endDogWord_eq hdog
  have rdVow := endRuntimeBlocks.endRuntime_block_8519_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondDog (by jump_dest) rdDog
  have hcondVow :
      UInt256.isZero (UInt256.eq endVowWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endVowBytes_len endVowWord_eq hvow
  have rdStore := endRuntimeBlocks.endRuntime_block_8565_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVow rdVow
  exact endX_fileAddress_store_vow (g := g) hperm rdStore

theorem endX_fileAddress_pot_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 = endPotBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨5⟩ (endAddressSlotWriteWord σ I ⟨5⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdDog := endRuntimeBlocks.endRuntime_block_8473_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat (by jump_dest) rdCat
  have hcondDog :
      UInt256.isZero (UInt256.eq endDogWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endDogBytes_len endDogWord_eq hdog
  have rdVow := endRuntimeBlocks.endRuntime_block_8519_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondDog (by jump_dest) rdDog
  have hcondVow :
      UInt256.isZero (UInt256.eq endVowWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVowBytes_len endVowWord_eq hvow
  have rdPot := endRuntimeBlocks.endRuntime_block_8565_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVow (by jump_dest) rdVow
  have hcondPot :
      UInt256.isZero (UInt256.eq endPotWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endPotBytes_len endPotWord_eq hpot
  have rdStore := endRuntimeBlocks.endRuntime_block_8611_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondPot rdPot
  exact endX_fileAddress_store_pot (g := g) hperm rdStore

theorem endX_fileAddress_spot_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes)
    (hspot : (I.calldata.toList.drop 4).take 32 = endSpotBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨6⟩ (endAddressSlotWriteWord σ I ⟨6⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdDog := endRuntimeBlocks.endRuntime_block_8473_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat (by jump_dest) rdCat
  have hcondDog :
      UInt256.isZero (UInt256.eq endDogWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endDogBytes_len endDogWord_eq hdog
  have rdVow := endRuntimeBlocks.endRuntime_block_8519_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondDog (by jump_dest) rdDog
  have hcondVow :
      UInt256.isZero (UInt256.eq endVowWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVowBytes_len endVowWord_eq hvow
  have rdPot := endRuntimeBlocks.endRuntime_block_8565_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVow (by jump_dest) rdVow
  have hcondPot :
      UInt256.isZero (UInt256.eq endPotWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endPotBytes_len endPotWord_eq hpot
  have rdSpot := endRuntimeBlocks.endRuntime_block_8611_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondPot (by jump_dest) rdPot
  have hcondSpot :
      UInt256.isZero (UInt256.eq endSpotWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endSpotBytes_len endSpotWord_eq hspot
  have rdStore := endRuntimeBlocks.endRuntime_block_8657_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondSpot rdSpot
  exact endX_fileAddress_store_spot (g := g) hperm rdStore

theorem endX_fileAddress_cure_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes)
    (hspot : (I.calldata.toList.drop 4).take 32 ≠ endSpotBytes)
    (hcure : (I.calldata.toList.drop 4).take 32 = endCureBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨7⟩ (endAddressSlotWriteWord σ I ⟨7⟩))
      ByteArray.empty := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdDog := endRuntimeBlocks.endRuntime_block_8473_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat (by jump_dest) rdCat
  have hcondDog :
      UInt256.isZero (UInt256.eq endDogWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endDogBytes_len endDogWord_eq hdog
  have rdVow := endRuntimeBlocks.endRuntime_block_8519_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondDog (by jump_dest) rdDog
  have hcondVow :
      UInt256.isZero (UInt256.eq endVowWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVowBytes_len endVowWord_eq hvow
  have rdPot := endRuntimeBlocks.endRuntime_block_8565_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVow (by jump_dest) rdVow
  have hcondPot :
      UInt256.isZero (UInt256.eq endPotWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endPotBytes_len endPotWord_eq hpot
  have rdSpot := endRuntimeBlocks.endRuntime_block_8611_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondPot (by jump_dest) rdPot
  have hcondSpot :
      UInt256.isZero (UInt256.eq endSpotWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endSpotBytes_len endSpotWord_eq hspot
  have rdCure := endRuntimeBlocks.endRuntime_block_8657_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondSpot (by jump_dest) rdSpot
  have hcondCure :
      UInt256.isZero (UInt256.eq endCureWord (endArg0Word I)) = ⟨0⟩ :=
    endFileAddressCondEqOfBytes (I := I) hsz68 endCureBytes_len endCureWord_eq hcure
  have rdStore := endRuntimeBlocks.endRuntime_block_8704_fallthrough
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCure rdCure
  exact endX_fileAddress_store_cure (g := g) hperm rdStore

theorem endX_fileAddress_what_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hvat : (I.calldata.toList.drop 4).take 32 ≠ endVatBytes)
    (hcat : (I.calldata.toList.drop 4).take 32 ≠ endCatBytes)
    (hdog : (I.calldata.toList.drop 4).take 32 ≠ endDogBytes)
    (hvow : (I.calldata.toList.drop 4).take 32 ≠ endVowBytes)
    (hpot : (I.calldata.toList.drop 4).take 32 ≠ endPotBytes)
    (hspot : (I.calldata.toList.drop 4).take 32 ≠ endSpotBytes)
    (hcure : (I.calldata.toList.drop 4).take 32 ≠ endCureBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨mem, aw, _, _, rdTests⟩ :=
    endX_fileAddress_to_tests (g := g) hsz68 hsize hauth hlive hreach
  have hcondVat :
      UInt256.isZero (UInt256.eq endVatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVatBytes_len endVatWord_eq hvat
  have rdCat := endRuntimeBlocks.endRuntime_block_8427_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVat (by jump_dest) rdTests
  have hcondCat :
      UInt256.isZero (UInt256.eq endCatWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCatBytes_len endCatWord_eq hcat
  have rdDog := endRuntimeBlocks.endRuntime_block_8473_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCat (by jump_dest) rdCat
  have hcondDog :
      UInt256.isZero (UInt256.eq endDogWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endDogBytes_len endDogWord_eq hdog
  have rdVow := endRuntimeBlocks.endRuntime_block_8519_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondDog (by jump_dest) rdDog
  have hcondVow :
      UInt256.isZero (UInt256.eq endVowWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endVowBytes_len endVowWord_eq hvow
  have rdPot := endRuntimeBlocks.endRuntime_block_8565_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondVow (by jump_dest) rdVow
  have hcondPot :
      UInt256.isZero (UInt256.eq endPotWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endPotBytes_len endPotWord_eq hpot
  have rdSpot := endRuntimeBlocks.endRuntime_block_8611_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondPot (by jump_dest) rdPot
  have hcondSpot :
      UInt256.isZero (UInt256.eq endSpotWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endSpotBytes_len endSpotWord_eq hspot
  have rdCure := endRuntimeBlocks.endRuntime_block_8657_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondSpot (by jump_dest) rdSpot
  have hcondCure :
      UInt256.isZero (UInt256.eq endCureWord (endArg0Word I)) ≠ ⟨0⟩ :=
    endFileAddressCondNeOfBytes (I := I) hsz68 endCureBytes_len endCureWord_eq hcure
  have rdRevertEntry := endRuntimeBlocks.endRuntime_block_8704_taken
    (x0 := endArg1AddressWord I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondCure (by jump_dest) rdCure
  exact endRuntimeBlocks.endRuntime_block_1499
    (R := [endArg1AddressWord I, endArg0Word I, ⟨562⟩, sel]) (by simp)
    (by simpa using rdRevertEntry)

theorem endStorageLoad_init_codeOwner_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) (slot : UInt256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
        (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner slot =
      solcSlotWord σ I slot := by
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
    Account.lookupStorage, Batteries.RBMap.findD]

theorem endAddressStorageStore_init_eq
    (cA gh bl σ_evm σ_solm σ₀ A I) (g : Sat256) (slot : UInt256)
    (hOldSlot : solcSlotWord σ_evm I slot = solcSlotWord σ_solm I slot) :
    Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
            (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner slot)
          (endArg1AddressWord I)) =
      Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner slot (endAddressSlotWriteWord σ_evm I slot) := by
  rw [endStorageLoad_init_codeOwner_eq]
  simp only [initState, endAddressSlotWriteWord]
  rw [hOldSlot.symm]

theorem endFileAddressBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 20))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 20 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some fileAddressTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 20 (by omega) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (fileAddressTransition.params.map Param.name) (transitionSignature fileAddressTransition).paramTypes
        I.calldata = some (endFileAddressStore I) := by
      simpa [config, fileAddressTransition, transitionSignature, bytes32, addr] using
        endDecode_legacyBytes32_address_file_ok (I := I) hsz68
    have hAuthWord :
        solcSlotWord σ_evm I (endAuthSlot I) = solcSlotWord σ_solm I (endAuthSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endAuthSlot I) ⟨0⟩
    by_cases hauthSolm : solcSlotWord σ_solm I (endAuthSlot I) = ⟨1⟩
    · have hauthEvm : solcSlotWord σ_evm I (endAuthSlot I) = ⟨1⟩ :=
        hAuthWord.trans hauthSolm
      have hauthSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (wardsSlot (.address I.source)) = ⟨1⟩ := by
        rw [endAuthStorageLoad_init_eq]
        exact hauthSolm
      have hLiveWord :
          solcSlotWord σ_evm I ⟨8⟩ = solcSlotWord σ_solm I ⟨8⟩ :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
      by_cases hliveSolm : solcSlotWord σ_solm I ⟨8⟩ = ⟨1⟩
      · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ = ⟨1⟩ :=
          hLiveWord.trans hliveSolm
        have hliveSrc :
            Solm.EVM.storageLoad
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner ⟨8⟩ = ⟨1⟩ := by
          rw [endStorageLoad_init_eq]
          exact hliveSolm
        by_cases hvat : (I.calldata.toList.drop 4).take 32 = endVatBytes
        · have hOldSlot :
              solcSlotWord σ_evm I ⟨1⟩ = solcSlotWord σ_solm I ⟨1⟩ :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
          have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endFileAddressStore I) fileAddressTransition.body
              (.returned { contract := contract, locals := endFileAddressStore I }
                (Solm.EVM.storageStore
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  I.codeOwner ⟨1⟩ (endAddressSlotWriteWord σ_evm I ⟨1⟩))
                none) := by
            simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
              (Sat256.ofUInt256 g) ⟨1⟩ hOldSlot] using
              endFileAddressBodyVatOk
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat
          exact (endX_fileAddress_vat_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
              hauthEvm hliveEvm hvat hreach)
            |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
              (by rw [storageStore_createdAccounts]; rfl)
              (by
                simpa [initState, storageWrite_eq, storageStore_accountMap] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩
                    (endAddressSlotWriteWord σ_evm I ⟨1⟩) hAccounts)
              (by
                exact returnEquiv.fallthrough (dvs := []) rfl
                  (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
        · by_cases hcat : (I.calldata.toList.drop 4).take 32 = endCatBytes
          · have hOldSlot :
                solcSlotWord σ_evm I ⟨2⟩ = solcSlotWord σ_solm I ⟨2⟩ :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
            have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (endFileAddressStore I) fileAddressTransition.body
                (.returned { contract := contract, locals := endFileAddressStore I }
                  (Solm.EVM.storageStore
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    I.codeOwner ⟨2⟩ (endAddressSlotWriteWord σ_evm I ⟨2⟩))
                  none) := by
              simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
                (Sat256.ofUInt256 g) ⟨2⟩ hOldSlot] using
                endFileAddressBodyCatOk
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                  (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat
            exact (endX_fileAddress_cat_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
                hauthEvm hliveEvm hvat hcat hreach)
              |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                (by rw [storageStore_createdAccounts]; rfl)
                (by
                  simpa [initState, storageWrite_eq, storageStore_accountMap] using
                    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
                      (endAddressSlotWriteWord σ_evm I ⟨2⟩) hAccounts)
                (by
                  exact returnEquiv.fallthrough (dvs := []) rfl
                    (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
          · by_cases hdog : (I.calldata.toList.drop 4).take 32 = endDogBytes
            · have hOldSlot :
                  solcSlotWord σ_evm I ⟨3⟩ = solcSlotWord σ_solm I ⟨3⟩ :=
                accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
              have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (endFileAddressStore I) fileAddressTransition.body
                  (.returned { contract := contract, locals := endFileAddressStore I }
                    (Solm.EVM.storageStore
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      I.codeOwner ⟨3⟩ (endAddressSlotWriteWord σ_evm I ⟨3⟩))
                    none) := by
                simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
                  (Sat256.ofUInt256 g) ⟨3⟩ hOldSlot] using
                  endFileAddressBodyDogOk
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                    (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat hdog
              exact (endX_fileAddress_dog_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
                  hauthEvm hliveEvm hvat hcat hdog hreach)
                |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                  (by rw [storageStore_createdAccounts]; rfl)
                  (by
                    simpa [initState, storageWrite_eq, storageStore_accountMap] using
                      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩
                        (endAddressSlotWriteWord σ_evm I ⟨3⟩) hAccounts)
                  (by
                    exact returnEquiv.fallthrough (dvs := []) rfl
                      (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
            · by_cases hvow : (I.calldata.toList.drop 4).take 32 = endVowBytes
              · have hOldSlot :
                    solcSlotWord σ_evm I ⟨4⟩ = solcSlotWord σ_solm I ⟨4⟩ :=
                  accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
                have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (endFileAddressStore I) fileAddressTransition.body
                    (.returned { contract := contract, locals := endFileAddressStore I }
                      (Solm.EVM.storageStore
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        I.codeOwner ⟨4⟩ (endAddressSlotWriteWord σ_evm I ⟨4⟩))
                      none) := by
                  simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
                    (Sat256.ofUInt256 g) ⟨4⟩ hOldSlot] using
                    endFileAddressBodyVowOk
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                      (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat hdog hvow
                exact (endX_fileAddress_vow_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
                    hauthEvm hliveEvm hvat hcat hdog hvow hreach)
                  |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                    (by rw [storageStore_createdAccounts]; rfl)
                    (by
                      simpa [initState, storageWrite_eq, storageStore_accountMap] using
                        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩
                          (endAddressSlotWriteWord σ_evm I ⟨4⟩) hAccounts)
                    (by
                      exact returnEquiv.fallthrough (dvs := []) rfl
                        (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
              · by_cases hpot : (I.calldata.toList.drop 4).take 32 = endPotBytes
                · have hOldSlot :
                      solcSlotWord σ_evm I ⟨5⟩ = solcSlotWord σ_solm I ⟨5⟩ :=
                    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
                  have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                      (endFileAddressStore I) fileAddressTransition.body
                      (.returned { contract := contract, locals := endFileAddressStore I }
                        (Solm.EVM.storageStore
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          I.codeOwner ⟨5⟩ (endAddressSlotWriteWord σ_evm I ⟨5⟩))
                        none) := by
                    simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
                      (Sat256.ofUInt256 g) ⟨5⟩ hOldSlot] using
                      endFileAddressBodyPotOk
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                        (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat hdog hvow hpot
                  exact (endX_fileAddress_pot_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
                      hauthEvm hliveEvm hvat hcat hdog hvow hpot hreach)
                    |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                      (by rw [storageStore_createdAccounts]; rfl)
                      (by
                        simpa [initState, storageWrite_eq, storageStore_accountMap] using
                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩
                            (endAddressSlotWriteWord σ_evm I ⟨5⟩) hAccounts)
                      (by
                        exact returnEquiv.fallthrough (dvs := []) rfl
                          (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
                · by_cases hspot : (I.calldata.toList.drop 4).take 32 = endSpotBytes
                  · have hOldSlot :
                        solcSlotWord σ_evm I ⟨6⟩ = solcSlotWord σ_solm I ⟨6⟩ :=
                      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
                    have hbody :
                      ExecTransitionBody config contract
                        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                        (endFileAddressStore I) fileAddressTransition.body
                        (.returned { contract := contract, locals := endFileAddressStore I }
                          (Solm.EVM.storageStore
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            I.codeOwner ⟨6⟩ (endAddressSlotWriteWord σ_evm I ⟨6⟩))
                          none) := by
                      simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
                        (Sat256.ofUInt256 g) ⟨6⟩ hOldSlot] using
                        endFileAddressBodySpotOk
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                          (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat hdog
                          hvow hpot hspot
                    exact (endX_fileAddress_spot_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
                        hauthEvm hliveEvm hvat hcat hdog hvow hpot hspot hreach)
                      |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                        (by rw [storageStore_createdAccounts]; rfl)
                        (by
                          simpa [initState, storageWrite_eq, storageStore_accountMap] using
                            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩
                              (endAddressSlotWriteWord σ_evm I ⟨6⟩) hAccounts)
                        (by
                          exact returnEquiv.fallthrough (dvs := []) rfl
                            (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
                  · by_cases hcure : (I.calldata.toList.drop 4).take 32 = endCureBytes
                    · have hOldSlot :
                          solcSlotWord σ_evm I ⟨7⟩ = solcSlotWord σ_solm I ⟨7⟩ :=
                        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
                      have hbody :
                        ExecTransitionBody config contract
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (endFileAddressStore I) fileAddressTransition.body
                          (.returned { contract := contract, locals := endFileAddressStore I }
                            (Solm.EVM.storageStore
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              I.codeOwner ⟨7⟩ (endAddressSlotWriteWord σ_evm I ⟨7⟩))
                            none) := by
                        simpa [endAddressStorageStore_init_eq cA gh bl σ_evm σ_solm σ₀ A I
                          (Sat256.ofUInt256 g) ⟨7⟩ hOldSlot] using
                          endFileAddressBodyCureOk
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                            (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat hdog
                            hvow hpot hspot hcure
                      exact (endX_fileAddress_cure_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
                          hauthEvm hliveEvm hvat hcat hdog hvow hpot hspot hcure hreach)
                        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
                          (by rw [storageStore_createdAccounts]; rfl)
                          (by
                            simpa [initState, storageWrite_eq, storageStore_accountMap] using
                              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩
                                (endAddressSlotWriteWord σ_evm I ⟨7⟩) hAccounts)
                          (by
                            exact returnEquiv.fallthrough (dvs := []) rfl
                              (by simp [fileAddressTransition]) (by simp [fileAddressTransition]))
                    · have hbody :
                        ExecTransitionBody config contract
                          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                          (endFileAddressStore I) fileAddressTransition.body .reverted := by
                        simpa [initState] using
                          endFileAddressBodyWhatFail
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                            (by simp only [initState]; exact hwv) hauthSrc hliveSrc hvat hcat hdog
                            hvow hpot hspot hcure
                      exact (endX_fileAddress_what_fail (g := Sat256.ofUInt256 g) hsz68 hsize
                          hauthEvm hliveEvm hvat hcat hdog hvow hpot hspot hcure hreach)
                        |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ ≠ ⟨1⟩ := by
          intro hbad
          exact hliveSolm (hLiveWord.symm.trans hbad)
        have hliveSrc :
            Solm.EVM.storageLoad
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner ⟨8⟩ ≠ ⟨1⟩ := by
          rw [endStorageLoad_init_eq]
          exact hliveSolm
        have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endFileAddressStore I) fileAddressTransition.body .reverted := by
          simpa [initState] using
            endFileAddressBodyLiveFail
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hauthSrc hliveSrc
        exact (endX_fileAddress_live_fail (g := Sat256.ofUInt256 g) hsz68 hsize
            hauthEvm hliveEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hauthEvm : solcSlotWord σ_evm I (endAuthSlot I) ≠ ⟨1⟩ := by
        intro hbad
        exact hauthSolm (hAuthWord.symm.trans hbad)
      have hauthSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (wardsSlot (.address I.source)) ≠ ⟨1⟩ := by
        rw [endAuthStorageLoad_init_eq]
        exact hauthSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endFileAddressStore I) fileAddressTransition.body .reverted := by
        simpa [initState] using
          endFileAddressBodyAuthFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hauthSrc
      exact (endX_fileAddress_auth_fail (g := Sat256.ofUInt256 g) hsz68 hsize hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (fileAddressTransition.params.map Param.name) (transitionSignature fileAddressTransition).paramTypes
        I.calldata = none := by
      simpa [config, fileAddressTransition, transitionSignature, bytes32, addr] using
        endDecode_legacyBytes32_address_file_none_short (I := I) hsz4 hshort
    exact (endX_fileAddress_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
