import Benchmarks.Dss.End.Admin
import Benchmarks.Dss.End.SimpleGetters
import Benchmarks.Dss.End.RuntimeBlocks_002

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `file(bytes32,uint256)` -/

abbrev endFileUintStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (.int (Int.ofNat (endArg1Word I).toNat))

abbrev endWaitBytes : List UInt8 :=
  [119, 97, 105, 116] ++ List.replicate 28 0

abbrev endWaitWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 500718173) (UInt256.ofNat 226)

theorem endWaitWord_eq : ABI.bytesToWord endWaitBytes = endWaitWord := by
  native_decide

theorem endArg0Bytes_len {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ((I.calldata.toList.drop 4).take 32).length = 32 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [List.length_take, List.length_drop, htlen]
  omega

theorem endWaitBytes_len : endWaitBytes.length = 32 := by
  native_decide

theorem endArg0Word_eq_waitWord_of_bytes {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hbytes : (I.calldata.toList.drop 4).take 32 = endWaitBytes) :
    endArg0Word I = endWaitWord := by
  have hword :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [hbytes, endWaitWord_eq] at hword
  exact hword.symm

theorem endArg0Word_ne_waitWord_of_bytes_ne {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hbytes : (I.calldata.toList.drop 4).take 32 ≠ endWaitBytes) :
    endArg0Word I ≠ endWaitWord := by
  intro hwordEq
  have hword :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hleft :
      EVM.Word.toBytesBE (endArg0Word I) = (I.calldata.toList.drop 4).take 32 := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length (endArg0Bytes_len hsz36)
  have hright : EVM.Word.toBytesBE endWaitWord = endWaitBytes := by
    rw [← endWaitWord_eq]
    exact toBytesBE_bytesToWord_of_length endWaitBytes_len
  exact hbytes (by
    rw [← hleft, hwordEq, hright])

theorem endDecode_legacyBytes32_uint256_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["what", "data"] [bytes32, uint256]
        I.calldata =
      some (endFileUintStore I) := by
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
      ¬ ([bytes32, uint256].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, uint256, isDynamicABIType]
  have hnotShort : ¬ (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_neg hnotShort]
  rw [show decodeABIValues? [bytes32, uint256] (I.calldata.toList.drop 4) 0 0 64 64
        DecodeMode.legacySolc05 =
        some ([endArg0Bytes32Value I, .int (Int.ofNat (endArg1Word I).toNat)], 64) by
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
    rw [show isDynamicABIType uint256 = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? uint256 = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval1 :
        decodeABIValue? uint256 (I.calldata.toList.drop 4) 32 DecodeMode.legacySolc05 =
          some (.int (Int.ofNat (endArg1Word I).toNat), 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := uint256) (bytes := I.calldata.toList.drop 4) (start := 32) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256
          (I.calldata.toList.drop 4) 32 =
        some (.int (Int.ofNat (endArg1Word I).toNat), 64)
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := I.calldata.toList.drop 4) (start := 32) htake36]
      rw [hword36]
    rw [hval1]
    simp]
  simp [decodeCalldata.insertValues, endFileUintStore]

theorem endDecode_legacyBytes32_uint256_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["what", "data"] [bytes32, uint256]
        I.calldata = none := by
  unfold decodeCalldataWithMode decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hnot4 : ¬ I.calldata.toList.length < 4 := by
    rw [htlen]
    omega
  have hnotDyn :
      ¬ ([bytes32, uint256].any isDynamicABIType = true ∧
        2 ^ 255 ≤ I.calldata.toList.length) := by
    simp [bytes32, uint256, isDynamicABIType]
  have hshortArgs : (I.calldata.toList.drop 4).length < 64 := by
    rw [List.length_drop, htlen]
    omega
  rw [if_neg hnot4]
  rw [if_neg hnotDyn]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [if_pos hshortArgs]

theorem endFileUintStore_get_what (I : ExecutionEnv) :
    (endFileUintStore I).get? "what" = some (endArg0Bytes32Value I) := by
  change ((((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (.int (Int.ofNat (endArg1Word I).toNat))).get? "what") =
      some (endArg0Bytes32Value I)
  rw [store_get_ne ((∅ : Store).insert "what" (endArg0Bytes32Value I))
    (k := "data") (a := "what") (.int (Int.ofNat (endArg1Word I).toNat)) (by decide)]
  exact store_get_self (∅ : Store) "what" (endArg0Bytes32Value I)

theorem endFileUintStore_get_data (I : ExecutionEnv) :
    (endFileUintStore I).get? "data" =
      some (.int (Int.ofNat (endArg1Word I).toNat)) := by
  simp [endFileUintStore, store_get_self]

theorem endFileUintStore_getElem_what (I : ExecutionEnv) :
    (endFileUintStore I)["what"] = endArg0Bytes32Value I := by
  have hopt : (endFileUintStore I)["what"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endFileUintStore_get_what I
  have hmem : "what" ∈ endFileUintStore I := by
    simp [endFileUintStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endFileUintStore I) "what" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endFileUintStore_getElem_data (I : ExecutionEnv) :
    (endFileUintStore I)["data"] =
      .int (Int.ofNat (endArg1Word I).toNat) := by
  have hopt : (endFileUintStore I)["data"]? =
      some (.int (Int.ofNat (endArg1Word I).toNat)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endFileUintStore_get_data I
  have hmem : "data" ∈ endFileUintStore I := by
    simp [endFileUintStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endFileUintStore I) "data" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endFileUintStore_get_wards_none (I : ExecutionEnv) :
    (endFileUintStore I).get? "wards" = none := by
  change ((((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (.int (Int.ofNat (endArg1Word I).toNat))).get? "wards") = none
  rw [store_get_ne ((∅ : Store).insert "what" (endArg0Bytes32Value I))
    (k := "data") (a := "wards") (.int (Int.ofNat (endArg1Word I).toNat)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "what") (a := "wards")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endFileUintStore_get_live_none (I : ExecutionEnv) :
    (endFileUintStore I).get? "live" = none := by
  change ((((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (.int (Int.ofNat (endArg1Word I).toNat))).get? "live") = none
  rw [store_get_ne ((∅ : Store).insert "what" (endArg0Bytes32Value I))
    (k := "data") (a := "live") (.int (Int.ofNat (endArg1Word I).toNat)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "what") (a := "live")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endFileUintStore_get_wait_none (I : ExecutionEnv) :
    (endFileUintStore I).get? "wait" = none := by
  change ((((∅ : Store).insert "what" (endArg0Bytes32Value I)).insert "data"
    (.int (Int.ofNat (endArg1Word I).toNat))).get? "wait") = none
  rw [store_get_ne ((∅ : Store).insert "what" (endArg0Bytes32Value I))
    (k := "data") (a := "wait") (.int (Int.ofNat (endArg1Word I).toNat)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "what") (a := "wait")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalAuthStorage_fileUint (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
        (.storage (wardsRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (wardsSlot (.address evm.executionEnv.source))).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endFileUintStore_get_wards_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_wards (.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalAuthGuard_fileUint_true (evm : EVM.State) (I : ExecutionEnv)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage_fileUint evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat = 1 := by
    rw [hauth]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalAuthGuard_fileUint_false (evm : EVM.State) (I : ExecutionEnv)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage_fileUint evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat ≠ 1 := by
    intro hnat
    exact hauth (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalLiveStorage_fileUint (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
        (.storage liveRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endFileUintStore_get_live_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, liveRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_live)]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalLiveGuard_fileUint_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_fileUint evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat = 1 := by
    rw [hlive]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalLiveGuard_fileUint_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_fileUint evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat ≠ 1 := by
    intro hnat
    exact hlive (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalWhat_fileUint (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.var "what") =
      .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endFileUintStore_get_what I]
  rfl

theorem endEvalData_fileUint (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.var "data") =
      .ok (.int (Int.ofNat (endArg1Word I).toNat)) := by
  rw [evalExpr?]
  rw [endFileUintStore_get_data I]
  simp [EvalResult.ofOption]

theorem endEvalWaitLit_fileUint (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm waitLit =
      .ok (Value.fixedBytes bytes32Width endWaitBytes) := by
  simp [evalExpr?, waitLit, strLit4, endWaitBytes]
  rfl

theorem endEvalWhatWait_true (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endWaitBytes) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.binary .eq (.var "what") waitLit) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalWhat_fileUint evm I]
  rw [endEvalWaitLit_fileUint evm I]
  change evalBinaryOp? BinaryOp.eq (endArg0Bytes32Value I)
      (Value.fixedBytes bytes32Width endWaitBytes) = .ok (.bool true)
  simp [evalBinaryOp?, endArg0Bytes32Value, endWaitBytes, hwhat]

theorem endEvalWhatWait_false (evm : EVM.State) (I : ExecutionEnv)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endWaitBytes) :
    evalExpr? config { contract := contract, locals := endFileUintStore I } evm
      (.binary .eq (.var "what") waitLit) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalWhat_fileUint evm I]
  rw [endEvalWaitLit_fileUint evm I]
  change evalBinaryOp? BinaryOp.eq (endArg0Bytes32Value I)
      (Value.fixedBytes bytes32Width endWaitBytes) = .ok (.bool false)
  simp [evalBinaryOp?, endArg0Bytes32Value, endWaitBytes, hwhat]
  simpa [endWaitBytes] using hwhat

theorem endAssignWaitData (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := endFileUintStore I } evm
        .storage waitRef (.int (Int.ofNat (endArg1Word I).toNat)) =
      .ok ({ contract := contract, locals := endFileUintStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩ (endArg1Word I)) := by
  rw [assignStorageRef_storage_scalar
    (slot := waitRef)
    (er := { base := "wait", steps := [] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc ⟨10⟩)
    (n := Int.ofNat (endArg1Word I).toNat)
    (hbase := endFileUintStore_get_wait_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, waitRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_wait)
    (hstore := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm ⟨10⟩ (endArg1Word I))]

theorem endFileUintBodyOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endWaitBytes) :
    ExecTransitionBody config contract evm (endFileUintStore I) fileUintTransition.body
      (.returned { contract := contract, locals := endFileUintStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩ (endArg1Word I))
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [fileUintTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileUint_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileUint_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.iteTrue (endEvalWhatWait_true evm I hwhat) <|
          ExecBlock.consNormal
            (ExecStmt.assign (endEvalData_fileUint evm I) (endAssignWaitData evm I))
            ExecBlock.nil)
        ExecBlock.nil)

theorem endFileUintBodyAuthFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (endFileUintStore I)
      fileUintTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileUintTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalAuthGuard_fileUint_false evm I hauth)))

theorem endFileUintBodyLiveFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (endFileUintStore I)
      fileUintTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileUintTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileUint_true evm I hauth)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalLiveGuard_fileUint_false evm I hlive)))

theorem endFileUintBodyWhatFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endWaitBytes) :
    ExecTransitionBody config contract evm (endFileUintStore I)
      fileUintTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileUintTransition, nonpayable, auth] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAuthGuard_fileUint_true evm I hauth)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_fileUint_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.iteFalse (endEvalWhatWait_false evm I hwhat) <|
          ExecBlock.consRevert (ExecStmt.requireFalse (by simp [evalExpr?, pure]))))

theorem endStorageLoad_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) (slot : UInt256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner slot =
      solcSlotWord σ I slot := by
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
    Account.lookupStorage, Batteries.RBMap.findD]

theorem endReachFileUint {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 21)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 21 (by omega) hsel
  obtain ⟨_, _, h452⟩ := endReachFirstArm452 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm452Eq I hsz 0 (by omega))
      (by simpa [endArm452Index] using
        endSelectorMiss_of_match 11 21 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm452Eq I hsz 1 (by omega))
      (by simpa [endArm452Index] using hsel)
  exact RD.dispatchTo ⟨527⟩ 1 h452
    (fun j hj => endArms452WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endX_fileUint_to_auth {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1315⟩
      [endArg1Word I, endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd549 := endRuntimeBlocks.endRuntime_block_527_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd1315 := endRuntimeBlocks.endRuntime_block_549
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨562⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_527_taken_stack] using rd549)
  have hoff : ((UInt256.ofNat 32 + (⟨4⟩ : UInt256)).toNat) = 36 := by
    native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_549_stack, endArg1Word, endArg0Word,
      calldataWord, hoff] using rd1315⟩

theorem endX_fileUint_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd545 := endRuntimeBlocks.endRuntime_block_527_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_545 (R :=
      endRuntimeBlocks.endRuntime_block_527_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_527_fallthrough_stack]) (by simpa using rd545)

theorem endX_fileUint_auth_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileUint_to_auth (g := g) hsz68 hsize hreach
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
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_1315_fallthrough
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth rdAuth
  exact endRuntimeBlocks.endRuntime_block_1339
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_fileUint_live_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileUint_to_auth (g := g) hsz68 hsize hreach
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
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_1315_taken
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth
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
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_1404_fallthrough
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondLive rdLive
  exact endRuntimeBlocks.endRuntime_block_1415
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_fileUint_what_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hwhat : (I.calldata.toList.drop 4).take 32 ≠ endWaitBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileUint_to_auth (g := g) hsz68 hsize hreach
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
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_1315_taken
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth
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
  obtain ⟨_, _, rdWhat⟩ := endRuntimeBlocks.endRuntime_block_1404_taken
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondLive
    (by jump_dest) rdLive
  have hwordNe : endWaitWord ≠ endArg0Word I := by
    exact fun h => endArg0Word_ne_waitWord_of_bytes_ne (I := I) (by omega) hwhat h.symm
  have hcondWhat :
      UInt256.isZero (UInt256.eq endWaitWord (endArg0Word I)) ≠ (UInt256.ofNat 0) := by
    have hnotEqOne : ¬ UInt256.eq endWaitWord (endArg0Word I) = ⟨1⟩ := by
      intro heq
      exact hwordNe (uInt256_eq_one_eq heq)
    rw [uInt256_eq_zero_of_ne hnotEqOne]
    decide
  have rdRevertEntry := endRuntimeBlocks.endRuntime_block_1474_taken
    (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondWhat (by jump_dest) rdWhat
  exact endRuntimeBlocks.endRuntime_block_1499
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_fileUint_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨1⟩)
    (hwhat : (I.calldata.toList.drop 4).take 32 = endWaitBytes)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ ⟨10⟩ (endArg1Word I))
      ByteArray.empty := by
  obtain ⟨_, _, rdAuth⟩ := endX_fileUint_to_auth (g := g) hsz68 hsize hreach
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
  obtain ⟨_, _, rdLive⟩ := endRuntimeBlocks.endRuntime_block_1315_taken
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondAuth
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
  obtain ⟨_, _, rdWhat⟩ := endRuntimeBlocks.endRuntime_block_1404_taken
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) hcondLive
    (by jump_dest) rdLive
  have hword : endArg0Word I = endWaitWord :=
    endArg0Word_eq_waitWord_of_bytes (I := I) (by omega) hwhat
  have hcondWhat :
      UInt256.isZero (UInt256.eq endWaitWord (endArg0Word I)) = (UInt256.ofNat 0) := by
    rw [hword]
    decide
  have rdStoreEntry := endRuntimeBlocks.endRuntime_block_1474_fallthrough
    (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) hcondWhat rdWhat
  obtain ⟨_, _, rdLog⟩ := endRuntimeBlocks.endRuntime_block_1490
    (x0 := endArg1Word I) (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) hperm (by jump_dest) rdStoreEntry
  have rdStop := endRuntimeBlocks.endRuntime_block_1576
    (x0 := endArg1Word I) (x1 := endArg0Word I) (x2 := ⟨562⟩) (R := [sel])
    (by simp) hperm (by jump_dest) rdLog
  exact endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_1576_stack] using rdStop)

theorem endFileUintBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 21))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 21 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some fileUintTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 21 (by omega) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (fileUintTransition.params.map Param.name) (transitionSignature fileUintTransition).paramTypes
        I.calldata = some (endFileUintStore I) := by
      simpa [config, fileUintTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_ok (I := I) hsz68
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
        by_cases hwhat : (I.calldata.toList.drop 4).take 32 = endWaitBytes
        · have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endFileUintStore I) fileUintTransition.body
              (.returned { contract := contract, locals := endFileUintStore I }
                (Solm.EVM.storageStore
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  I.codeOwner ⟨10⟩ (endArg1Word I))
                none) := by
            simpa [initState] using
              endFileUintBodyOk
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hauthSrc hliveSrc hwhat
          exact (endX_fileUint_ok (g := Sat256.ofUInt256 g) hsz68 hsize hperm
              hauthEvm hliveEvm hwhat hreach)
            |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
              (by rw [storageStore_createdAccounts]; rfl)
              (by
                simpa [initState, storageWrite_eq, storageStore_accountMap] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ (endArg1Word I) hAccounts)
              (by
                exact returnEquiv.fallthrough (dvs := []) rfl
                  (by simp [fileUintTransition]) (by simp [fileUintTransition]))
        · have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endFileUintStore I) fileUintTransition.body .reverted := by
            simpa [initState] using
              endFileUintBodyWhatFail
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hauthSrc hliveSrc hwhat
          exact (endX_fileUint_what_fail (g := Sat256.ofUInt256 g) hsz68 hsize
              hauthEvm hliveEvm hwhat hreach)
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
            (endFileUintStore I) fileUintTransition.body .reverted := by
          simpa [initState] using
            endFileUintBodyLiveFail
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hauthSrc hliveSrc
        exact (endX_fileUint_live_fail (g := Sat256.ofUInt256 g) hsz68 hsize
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
            (endFileUintStore I) fileUintTransition.body .reverted := by
        simpa [initState] using
          endFileUintBodyAuthFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hauthSrc
      exact (endX_fileUint_auth_fail (g := Sat256.ofUInt256 g) hsz68 hsize hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (fileUintTransition.params.map Param.name) (transitionSignature fileUintTransition).paramTypes
        I.calldata = none := by
      simpa [config, fileUintTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_none_short (I := I) hsz4 hshort
    exact (endX_fileUint_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
