import Benchmarks.Dss.End.Pack
import Benchmarks.Dss.End.RuntimeBlocks_002
import Benchmarks.Dss.End.RuntimeBlocks_003
import Benchmarks.Dss.End.RuntimeBlocks_004
import Benchmarks.Dss.End.RuntimeBlocks_011
import Benchmarks.Dss.End.RuntimeBlocks_012
import Reasoning.CallMemory
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `free(bytes32)` -/

abbrev endFreeStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (endArg0Bytes32Value I)

theorem endDecode_legacyBytes32_ilk_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk"] [bytes32] I.calldata =
      some (endFreeStore I) := by
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
  simp [decodeCalldata.insertValues, endFreeStore]

theorem endDecode_legacyBytes32_ilk_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk"] [bytes32] I.calldata = none := by
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

theorem endFreeStore_get_ilk (I : ExecutionEnv) :
    (endFreeStore I).get? "ilk" = some (endArg0Bytes32Value I) := by
  exact store_get_self (∅ : Store) "ilk" (endArg0Bytes32Value I)

theorem endFreeStore_getElem?_ilk (I : ExecutionEnv) :
    (endFreeStore I)["ilk"]? = some (endArg0Bytes32Value I) := by
  rw [← Std.HashMap.get?_eq_getElem?]
  exact endFreeStore_get_ilk I

theorem endFreeStore_getElem_ilk (I : ExecutionEnv) :
    (endFreeStore I)["ilk"] = endArg0Bytes32Value I := by
  have hopt : (endFreeStore I)["ilk"]? = some (endArg0Bytes32Value I) :=
    endFreeStore_getElem?_ilk I
  have hmem : "ilk" ∈ endFreeStore I := by
    simp [endFreeStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endFreeStore I) "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endFreeStore_get_live_none (I : ExecutionEnv) :
    (endFreeStore I).get? "live" = none := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).get? "live") = none
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "live")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endFreeStore_get_vat_none (I : ExecutionEnv) :
    (endFreeStore I).get? "vat" = none := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).get? "vat") = none
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "vat")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalLiveStorage_free (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
        (.storage liveRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endFreeStore_get_live_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, liveRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_live)]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalLiveGuard_free_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_free evm I, hlive]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalLiveGuard_free_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_free evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat ≠ 0 := by
    intro hnat
    exact hlive (uint256_toNat_eq_zero hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endEvalVatAddress_free (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endFreeStore I } evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endFreeStore_get_vat_none I) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_free (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_free evm I]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_free_false (evm : EVM.State) (I : ExecutionEnv)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_free evm I, hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_free_true (evm : EVM.State) (I : ExecutionEnv)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFreeStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_free evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endFreeBodyLiveFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (endFreeStore I)
      freeTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [freeTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalLiveGuard_free_false evm I hlive)))

theorem endFreeBodyVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endFreeStore I)
      freeTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [freeTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_free_true evm I hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_free_false evm I hvatNoCode)))

theorem endFreeBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨0⟩)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endFreeStore I } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endFreeStore I } evm) := by
  simpa [nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveGuard_free_true evm I hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_free_true evm I hvatCode)) <|
      ExecBlock.nil)

abbrev endFreeUrnsSelectorWord : UInt256 := UInt256.ofNat 606387804

def endFreeUrnsPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg0Word I) ++
    EVM.Word.toBytesBE (UInt256.ofNat I.source.val)

def endFreeUrnsEncodedCall (I : ExecutionEnv) : ByteArray :=
  urnsSelector ++ ⟨(endFreeUrnsPayloadBytes I).toArray⟩

theorem endEncodeBytes32_arg0 (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    encodeABIValue? bytes32 (endArg0Bytes32Value I) =
      some (EVM.Word.toBytesBE (endArg0Word I)) := by
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hdecodeWord :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hword : EVM.Word.toBytesBE (endArg0Word I) =
      (I.calldata.toList.drop 4).take 32 := by
    rw [← hdecodeWord]
    exact toBytesBE_bytesToWord_of_length hlen
  rw [ABI.encodeABIValue?.eq_def]
  unfold bytes32 endArg0Bytes32Value
  change (if bytes32Width = bytes32Width ∧
        ((I.calldata.toList.drop 4).take 32).length = bytes32Width.val + 1 then
      some (((I.calldata.toList.drop 4).take 32) ++ zeroBytes (32 - (bytes32Width.val + 1)))
    else none) =
      some (EVM.Word.toBytesBE (endArg0Word I))
  rw [if_pos (by simp [bytes32Width, hlen])]
  rw [hword]
  simp [bytes32Width, zeroBytes]

theorem endEncodeABIValues_urns (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    encodeABIValues? [bytes32, addr] [endArg0Bytes32Value I, .address I.source] =
      some (endFreeUrnsPayloadBytes I) := by
  have hhead : abiTupleHeadSize? [bytes32, addr] = some 64 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I hsz36, hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_source I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp [endFreeUrnsPayloadBytes]

theorem endEncodeCallWithSelector_urns (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    ABI.encodeCallWithSelector? urnsSelector [bytes32, addr]
      [endArg0Bytes32Value I, .address I.source] =
      some (endFreeUrnsEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_urns I hsz36]
  simp [endFreeUrnsEncodedCall, endFreeUrnsPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_urns_branch (args : List Value) :
    config.externalABI.encode? "urns" args =
      ABI.encodeCallWithSelector? urnsSelector [bytes32, addr] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "urns" = "cage")]
  rw [if_neg (by decide : ¬ "urns" = "vatIlks")]
  rw [if_neg (by decide : ¬ "urns" = "catIlks")]
  rw [if_neg (by decide : ¬ "urns" = "dogIlks")]
  rw [if_neg (by decide : ¬ "urns" = "spotIlks")]
  rw [if_pos (by decide : "urns" = "urns")]

theorem endExternalEncode_urns (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "urns" [endArg0Bytes32Value I, .address I.source] =
      some (endFreeUrnsEncodedCall I) := by
  rw [endExternalEncode_urns_branch]
  exact endEncodeCallWithSelector_urns I hsz36

abbrev endFreeUrnsInkWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endFreeUrnsArtWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endFreeUrnsValues (out : ByteArray) : List Value :=
  [.int (Int.ofNat (endFreeUrnsInkWord out).toNat),
    .int (Int.ofNat (endFreeUrnsArtWord out).toNat)]

theorem endDecodeReturnValues_legacy_uint256_uint256_ok {out : ByteArray}
    (h64 : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out =
      some (endFreeUrnsValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (out.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  rw [show abiTupleHeadSize? [uint256, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  rw [show decodeABIValues? [uint256, uint256] out.toList 0 0 64 64
        DecodeMode.legacySolc05 = some (endFreeUrnsValues out, 64) by
    simp only [decodeABIValues?]
    rw [show isDynamicABIType uint256 = false by native_decide]
    simp only [Bool.false_eq_true, if_false]
    rw [show staticABIEncodedSize? uint256 = some 32 by native_decide]
    simp only [Option.bind, bind]
    have hval0 :
        decodeABIValue? uint256 out.toList 0 DecodeMode.legacySolc05 =
          some (.int (Int.ofNat (endFreeUrnsInkWord out).toNat), 32) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := uint256) (bytes := out.toList) (start := 0) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 out.toList 0 =
        some (.int (Int.ofNat (endFreeUrnsInkWord out).toNat), 32)
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) (by simpa using htake0)]
      simp [endFreeUrnsInkWord]
    rw [hval0]
    simp only [Nat.reduceAdd, if_true]
    have hval1 :
        decodeABIValue? uint256 out.toList 32 DecodeMode.legacySolc05 =
          some (.int (Int.ofNat (endFreeUrnsArtWord out).toNat), 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := uint256) (bytes := out.toList) (start := 32) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 out.toList 32 =
        some (.int (Int.ofNat (endFreeUrnsArtWord out).toNat), 64)
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32]
    rw [hval1]
    simp [endFreeUrnsValues]]

theorem endDecodeReturnValues_legacy_uint256_uint256_none_short {out : ByteArray}
    (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out = none := by
  unfold ABI.decodeReturnValuesWithMode?
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show abiTupleHeadSize? [uint256, uint256] = some 64 by native_decide]
  simp only [Option.bind, bind]
  by_cases h32 : 32 ≤ out.size
  · have htake0 : (out.toList.take 32).length = 32 := by
      rw [List.length_take, hlen]
      omega
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    rw [show decodeABIValues? [uint256, uint256] out.toList 0 0 64 64
          DecodeMode.legacySolc05 = none by
      simp only [decodeABIValues?]
      rw [show isDynamicABIType uint256 = false by native_decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show staticABIEncodedSize? uint256 = some 32 by native_decide]
      simp only [Option.bind, bind]
      have hval0 :
          decodeABIValue? uint256 out.toList 0 DecodeMode.legacySolc05 =
            some (.int (Int.ofNat (endFreeUrnsInkWord out).toNat), 32) := by
        rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
          (ty := uint256) (bytes := out.toList) (start := 0) (by decide)]
        change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256 out.toList 0 =
          some (.int (Int.ofNat (endFreeUrnsInkWord out).toNat), 32)
        rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) (by simpa using htake0)]
        simp [endFreeUrnsInkWord]
      rw [hval0]
      simp only [Nat.reduceAdd, if_true]
      have hval1 :
          decodeABIValue? uint256 out.toList 32 DecodeMode.legacySolc05 = none := by
        rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
          (ty := uint256) (bytes := out.toList) (start := 32) (by decide)]
        simpa [uint256, uint256Int, abiUInt256] using
          (decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (bytes := out.toList) (start := 32) htake32n)
      rw [hval1]]
  · have htake0n : ¬ (out.toList.take 32).length = 32 := by
      rw [List.length_take, hlen]
      omega
    rw [show decodeABIValues? [uint256, uint256] out.toList 0 0 64 64
          DecodeMode.legacySolc05 = none by
      simp only [decodeABIValues?]
      rw [show isDynamicABIType uint256 = false by native_decide]
      simp only [Bool.false_eq_true, if_false]
      rw [show staticABIEncodedSize? uint256 = some 32 by native_decide]
      simp only [Option.bind, bind]
      have hval0 :
          decodeABIValue? uint256 out.toList 0 DecodeMode.legacySolc05 = none := by
        rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
          (ty := uint256) (bytes := out.toList) (start := 0) (by decide)]
        simpa [uint256, uint256Int, abiUInt256] using
          (decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (bytes := out.toList) (start := 0)
            (by simpa using htake0n))
      rw [hval0]]

theorem endExternalDecode_urns_ok {out : ByteArray} (h64 : 64 ≤ out.size) :
    config.externalABI.decode? "urns" out = some (endFreeUrnsValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "urns" = "cage")]
  rw [if_neg (by decide : ¬ "urns" = "vatIlks")]
  rw [if_neg (by decide : ¬ "urns" = "catIlks")]
  rw [if_neg (by decide : ¬ "urns" = "dogIlks")]
  rw [if_neg (by decide : ¬ "urns" = "spotIlks")]
  rw [if_pos (by decide : "urns" = "urns")]
  exact endDecodeReturnValues_legacy_uint256_uint256_ok h64

theorem endExternalDecode_urns_none_short {out : ByteArray} (hshort : out.size < 64) :
    config.externalABI.decode? "urns" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "urns" = "cage")]
  rw [if_neg (by decide : ¬ "urns" = "vatIlks")]
  rw [if_neg (by decide : ¬ "urns" = "catIlks")]
  rw [if_neg (by decide : ¬ "urns" = "dogIlks")]
  rw [if_neg (by decide : ¬ "urns" = "spotIlks")]
  rw [if_pos (by decide : "urns" = "urns")]
  exact endDecodeReturnValues_legacy_uint256_uint256_none_short hshort

abbrev endFreeUrnsCallMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_7760_taken_memory
    (ee := I) (mem := solcFreePtrMem) (x0 := endArg0Word I)

abbrev endFreeUrnsSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)

abbrev endFreeUrnsMemSel : ByteArray :=
  endFreeUrnsSelectorEncodedWord.toByteArray.write 0 solcFreePtrMem 128 32

abbrev endFreeUrnsMemIlk (I : ExecutionEnv) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 endFreeUrnsMemSel 132 32

abbrev endFreeUrnsMemFull (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.source.val).toByteArray.write 0 (endFreeUrnsMemIlk I) 164 32

theorem endFreeUrnsCallMem_eq_full (I : ExecutionEnv) :
    endFreeUrnsCallMem I = endFreeUrnsMemFull I := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  unfold endFreeUrnsCallMem endFreeUrnsMemFull endFreeUrnsMemIlk endFreeUrnsMemSel
    endFreeUrnsSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_7760_taken_memory]
  rw [hload]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 36)).toNat = 164 from by native_decide]

theorem endFreeUrnsMemSel_size_ge160 : 160 ≤ endFreeUrnsMemSel.size := by
  exact toByteArray_write_size_ge_off_add32_unbounded endFreeUrnsSelectorEncodedWord
    solcFreePtrMem 128

theorem endFreeUrnsMemIlk_size_ge164 (I : ExecutionEnv) :
    164 ≤ (endFreeUrnsMemIlk I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I) endFreeUrnsMemSel 132

theorem endFreeUrnsCallMem_size_ge196 (I : ExecutionEnv) :
    196 ≤ (endFreeUrnsCallMem I).size := by
  rw [endFreeUrnsCallMem_eq_full I]
  exact toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.source.val)
    (endFreeUrnsMemIlk I) 164

theorem endFreeUrnsSelectorEncodedWord_prefix :
    (endFreeUrnsSelectorEncodedWord.toByteArray).extract 0 4 = urnsSelector := by
  native_decide

theorem endFreeUrnsCallMem_read64 (I : ExecutionEnv) :
    (endFreeUrnsCallMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endFreeUrnsCallMem_eq_full I]
  change (((UInt256.ofNat I.source.val).toByteArray.write 0
      (endFreeUrnsMemIlk I) 164 32).readWithPadding 64 32) =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.ofNat I.source.val) (endFreeUrnsMemIlk I) 164 64
    (by have := endFreeUrnsMemIlk_size_ge164 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I) endFreeUrnsMemSel 132 64
    (by have := endFreeUrnsMemSel_size_ge160; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endFreeUrnsSelectorEncodedWord solcFreePtrMem 128 64
    (by rw [solcFreePtrMem_size]) (by omega)]
  exact solcFreePtrMem_read64

theorem endFreeUrnsCallMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endFreeUrnsCallMem I) = ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥ (endFreeUrnsCallMem I).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((endFreeUrnsCallMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endFreeUrnsCallMem I)
    (by have := endFreeUrnsCallMem_size_ge196 I; omega)
    (by exact endFreeUrnsCallMem_read64 I)

theorem endFreeUrnsCallMem_readSelector (I : ExecutionEnv) :
    (endFreeUrnsCallMem I).readWithPadding 128 4 = urnsSelector := by
  rw [endFreeUrnsCallMem_eq_full I]
  change (((UInt256.ofNat I.source.val).toByteArray.write 0
      (endFreeUrnsMemIlk I) 164 32).readWithPadding 128 4) = urnsSelector
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endFreeUrnsMemIlk_size_ge164 I) (by omega)
    (by have := endFreeUrnsMemIlk_size_ge164 I; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endFreeUrnsMemSel_size_ge160; omega) (by omega)
    (by have := endFreeUrnsMemSel_size_ge160; omega) (by decide) (by decide)]
  change ((endFreeUrnsSelectorEncodedWord.toByteArray.write 0
      solcFreePtrMem 128 32).readWithPadding 128 4) = urnsSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endFreeUrnsSelectorEncodedWord solcFreePtrMem 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFreeUrnsSelectorEncodedWord_prefix]

theorem endFreeUrnsCallMem_readIlk (I : ExecutionEnv) :
    (endFreeUrnsCallMem I).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endFreeUrnsCallMem_eq_full I]
  change (((UInt256.ofNat I.source.val).toByteArray.write 0
      (endFreeUrnsMemIlk I) 164 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.ofNat I.source.val) (endFreeUrnsMemIlk I) 164 132
    (by have := endFreeUrnsMemIlk_size_ge164 I; omega) (by omega)]
  change (((endArg0Word I).toByteArray.write 0
      endFreeUrnsMemSel 132 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg0Word I) endFreeUrnsMemSel 132

theorem endFreeUrnsCallMem_readSource (I : ExecutionEnv) :
    (endFreeUrnsCallMem I).readWithPadding 164 32 =
      (UInt256.ofNat I.source.val).toByteArray := by
  rw [endFreeUrnsCallMem_eq_full I]
  change (((UInt256.ofNat I.source.val).toByteArray.write 0
      (endFreeUrnsMemIlk I) 164 32).readWithPadding 164 32) =
    (UInt256.ofNat I.source.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.ofNat I.source.val) (endFreeUrnsMemIlk I) 164

theorem endFreeUrnsCallMem_readCallData (I : ExecutionEnv) :
    (endFreeUrnsCallMem I).readWithPadding 128 68 =
      endFreeUrnsEncodedCall I := by
  have hsize := endFreeUrnsCallMem_size_ge196 I
  rw [show 68 = 4 + 64 from rfl]
  rw [byteArray_readWithPadding_split (endFreeUrnsCallMem I) 128 4 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endFreeUrnsCallMem I) 132 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [endFreeUrnsCallMem_readSelector I, endFreeUrnsCallMem_readIlk I,
    endFreeUrnsCallMem_readSource I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endFreeUrnsEncodedCall, endFreeUrnsPayloadBytes, toByteArray_eq_toBytesBE]

theorem endEvalFreeUrnsArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endFreeStore I } evm
      [.var "ilk", sender] =
      .ok [endArg0Bytes32Value I, .address evm.executionEnv.source] := by
  simp [evalExprs?, evalExpr?, sender, envValue, EvalResult.ofOption, EvalResult.bind,
    bind, pure, endFreeStore_get_ilk]

theorem endX_free_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1043 := endRuntimeBlocks.endRuntime_block_1025_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1043
    (R := endRuntimeBlocks.endRuntime_block_1025_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1025_fallthrough_stack])
    (by simpa using rd1043)

theorem endX_free_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7690⟩
      [endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1047 := endRuntimeBlocks.endRuntime_block_1025_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd7690 := endRuntimeBlocks.endRuntime_block_1047
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1025_taken_stack] using rd1047)
  have hoff : (UInt256.ofNat 4).toNat = 4 := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_1047_stack, endArg0Word, calldataWord, hoff]
      using rd7690⟩

theorem endX_free_live_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_free_to_body (g := g) hsz36 hsize hreach
  have hcond :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) = UInt256.ofNat 0 := by
    rw [storageRead_eq]
    exact Reasoning.Theory.isZero_eq_zero_of_ne (by simpa using hlive)
  obtain ⟨_, _, rd7699⟩ := endRuntimeBlocks.endRuntime_block_7690_fallthrough
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcond rdBody
  exact endRuntimeBlocks.endRuntime_block_7699
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) rd7699

theorem endX_free_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_free_to_body (g := g) hsz36 hsize hreach
  have hliveCond :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hraw : storageRead I.codeOwner σ (UInt256.ofNat 8) = UInt256.ofNat 0 := by
      rw [storageRead_eq]
      simpa [solcSlotWord] using hlive
    rw [hraw]
    decide
  obtain ⟨_, _, rd7760⟩ := endRuntimeBlocks.endRuntime_block_7690_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hliveCond (by jump_dest) rdBody
  have hcond :
      UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) =
        UInt256.ofNat 0 := by
    rw [hvatNoCode]
    decide
  obtain ⟨_, _, rd7839⟩ := endRuntimeBlocks.endRuntime_block_7760_fallthrough
    (x0 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) (by
      simpa [endPackVatTarget, endPackCallAddrMask_eq_solc, u256_land_comm] using hcond) rd7760
  exact endRuntimeBlocks.endRuntime_block_7839
    (R := endRuntimeBlocks.endRuntime_block_7760_fallthrough_stack
      (ee := I) (mem := solcFreePtrMem) (σ := σ) (x0 := endArg0Word I)
      (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_7760_fallthrough_stack])
    rd7839

theorem endX_free_to_urns_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : solcSlotWord σ I ⟨8⟩ = ⟨0⟩)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7845⟩
      [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩, ⟨128⟩, ⟨64⟩,
        ⟨196⟩, endFreeUrnsSelectorWord, endPackVatTarget σ I, ⟨0⟩, ⟨0⟩,
        endArg0Word I, ⟨562⟩, sel]
      (endFreeUrnsCallMem I) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_free_to_body (g := g) hsz36 hsize hreach
  have hliveCond :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hraw : storageRead I.codeOwner σ (UInt256.ofNat 8) = UInt256.ofNat 0 := by
      rw [storageRead_eq]
      simpa [solcSlotWord] using hlive
    rw [hraw]
    decide
  obtain ⟨_, _, rd7760⟩ := endRuntimeBlocks.endRuntime_block_7690_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hliveCond (by jump_dest) rdBody
  have hcondCode :
      UInt256.isZero (UInt256.isZero
          (extCodeSizeWord σ (UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
            solcAddrMask))) ≠ UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ (UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
          solcAddrMask) ≠ UInt256.ofNat 0 := by
      simpa [endPackVatTarget, u256_land_comm] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw7843, k7843, C7843, rd7843⟩ :=
    endRuntimeBlocks.endRuntime_block_7760_taken_packed
      (x0 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest) rd7760
  have hfreeOrig : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  have hfreeCall : memLoad (UInt256.ofNat 64) (endFreeUrnsCallMem I) = ⟨128⟩ :=
    endFreeUrnsCallMem_mload64 I
  have hfreeCallRaw := hfreeCall
  dsimp [endFreeUrnsCallMem, endRuntimeBlocks.endRuntime_block_7760_taken_memory] at hfreeCallRaw
  rw [hfreeOrig] at hfreeCallRaw
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 68 = ⟨68⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 68 = ⟨196⟩ := by
    native_decide
  have rd7843' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7843⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩, ⟨128⟩, ⟨64⟩,
            ⟨196⟩, endFreeUrnsSelectorWord, endPackVatTarget σ I, ⟨0⟩, ⟨0⟩,
            endArg0Word I, ⟨562⟩, sel])
        (endFreeUrnsCallMem I) aw7843 ByteArray.empty (cA, σ) k7843 C7843 := by
    dsimp [endRuntimeBlocks.endRuntime_block_7760_taken_stack,
      endRuntimeBlocks.endRuntime_block_7760_taken_memory] at rd7843
    rw [hfreeOrig] at rd7843
    rw [hfreeCallRaw] at rd7843
    rw [hlen] at rd7843
    rw [hend] at rd7843
    simpa [endFreeUrnsCallMem, endFreeUrnsSelectorWord, endPackVatTarget,
      endRuntimeBlocks.endRuntime_block_7760_taken_memory, hfreeOrig,
      endPackCallAddrMask_eq_solc, u256_land_comm] using rd7843
  have rd7845 := endRuntimeBlocks.endRuntime_block_7843
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩, ⟨128⟩, ⟨64⟩,
      ⟨196⟩, endFreeUrnsSelectorWord, endPackVatTarget σ I, ⟨0⟩, ⟨0⟩,
      endArg0Word I, ⟨562⟩, sel])
    (by simp) rd7843'
  exact ⟨aw7843, _, _, by simpa [endRuntimeBlocks.endRuntime_block_7843_stack] using rd7845⟩

abbrev endFreeUrnsCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨196⟩, endFreeUrnsSelectorWord, endPackVatTarget σ I, ⟨0⟩, ⟨0⟩,
    endArg0Word I, ⟨562⟩, sel]

abbrev endFreeUrnsCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨68⟩, ⟨128⟩, ⟨64⟩] ++
    endFreeUrnsCallRest σ I sel

abbrev endFreeUrnsCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨7845⟩, stack := endFreeUrnsCallStack σ I sel,
    mem := endFreeUrnsCallMem I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endFreeUrnsCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨68⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat)

abbrev endFreeUrnsReturnMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endFreeUrnsCallMem I) 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev endFreeAfterUrnsAw (aw : UInt256) : UInt256 :=
  M (endFreeUrnsCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endFreeAfterUrnsFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFreeStore I).insert "vatUrn" (collapseReturns (endFreeUrnsValues out)) }

abbrev endFreeAfterUrnsCursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨7885⟩,
    stack := [UInt256.ofNat out.size, ⟨128⟩, ⟨0⟩, ⟨0⟩, endArg0Word I, ⟨562⟩, sel],
    mem := endFreeUrnsReturnMem I out,
    aw := endFreeAfterUrnsAw aw,
    rdata := out,
    world := world }

theorem bytesToWord_drop32_take32_eq_extract32_64 {returndata : ByteArray} :
    ABI.bytesToWord ((returndata.toList.drop 32).take 32) =
      UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 32 64)) := by
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (returndata.extract 32 64), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  rw [byteArray_toList_eq]

theorem endFreeUrnsReturnMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) :
    (endFreeUrnsReturnMem I out).size = (endFreeUrnsCallMem I).size := by
  have hfacts := callOutputFacts (endFreeUrnsCallMem I) out (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) hout (by
      change 128 + 64 ≤ (endFreeUrnsCallMem I).size
      have hsize := endFreeUrnsCallMem_size_ge196 I
      omega)
  simpa [endFreeUrnsReturnMem] using hfacts.size

theorem endFreeUrnsReturnMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endFreeUrnsReturnMem I out) = ⟨128⟩ := by
  have hfacts := callOutputFacts (endFreeUrnsCallMem I) out (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) hout (by
      change 128 + 64 ≤ (endFreeUrnsCallMem I).size
      have hsize := endFreeUrnsCallMem_size_ge196 I
      omega)
  have hread :
      (endFreeUrnsReturnMem I out).readWithPadding 64 32 =
        (endFreeUrnsCallMem I).readWithPadding 64 32 := by
    simpa [endFreeUrnsReturnMem] using hfacts.readBelow 64 (by native_decide)
  have hbase := endFreeUrnsCallMem_mload64 I
  unfold memLoad at hbase ⊢
  rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide] at hbase ⊢
  rw [if_neg (by
    rw [endFreeUrnsReturnMem_size I out hout]
    have hsize := endFreeUrnsCallMem_size_ge196 I
    omega)]
  rw [hread]
  rw [if_neg (by
    have hsize := endFreeUrnsCallMem_size_ge196 I
    omega)] at hbase
  exact hbase

theorem endFreeUrnsReturnMem_read128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h64 : 64 ≤ out.size) :
    (endFreeUrnsReturnMem I out).readWithPadding 128 32 =
      out.extract 0 32 := by
  have hfacts := callOutputFacts (endFreeUrnsCallMem I) out (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) hout (by
      change 128 + 64 ≤ (endFreeUrnsCallMem I).size
      have hsize := endFreeUrnsCallMem_size_ge196 I
      omega)
  simpa [endFreeUrnsReturnMem] using hfacts.readWord (by decide) (by omega)

theorem endFreeUrnsReturnMem_read160 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h64 : 64 ≤ out.size) :
    (endFreeUrnsReturnMem I out).readWithPadding 160 32 =
      out.extract 32 64 := by
  have hcopy :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 := by
    rw [callCopyLength_toNat out (⟨64⟩ : UInt256) hout]
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by native_decide]
    exact Nat.min_eq_left h64
  unfold endFreeUrnsReturnMem
  rw [hcopy]
  rw [write_eq_gen out (endFreeUrnsCallMem I) 128 64 (by decide) (by omega) (by
    have hsize := endFreeUrnsCallMem_size_ge196 I
    omega)]
  have hpre : ((endFreeUrnsCallMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    have hsize := endFreeUrnsCallMem_size_ge196 I
    omega
  have hcopySize : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 160 (by
    rw [ByteArray.size_append, ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hpre, hcopySize])]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]
    omega), hpre]
  rw [show 160 - 128 = 32 by omega, show 160 + 32 - 128 = 64 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 32 = 32 by omega, show min (0 + 64) 64 = 64 by omega]

theorem endFreeUrnsReturnMem_mload128 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h64 : 64 ≤ out.size) :
    memLoad (UInt256.ofNat 128) (endFreeUrnsReturnMem I out) =
      endFreeUrnsInkWord out := by
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [endFreeUrnsReturnMem_size I out hout]
    have hsize := endFreeUrnsCallMem_size_ge196 I
    omega)]
  rw [endFreeUrnsReturnMem_read128 I out hout h64]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) =
    ABI.bytesToWord (out.toList.take 32)
  rw [← bytesToWord_take32_eq_extract0_32]

theorem endFreeUrnsReturnMem_mload160 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h64 : 64 ≤ out.size) :
    memLoad (UInt256.ofNat 160) (endFreeUrnsReturnMem I out) =
      endFreeUrnsArtWord out := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endFreeUrnsReturnMem_size I out hout]
    have hsize := endFreeUrnsCallMem_size_ge196 I
    omega)]
  rw [endFreeUrnsReturnMem_read160 I out hout h64]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64)) =
    ABI.bytesToWord ((out.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

abbrev endFreeInkValue (out : ByteArray) : Value :=
  .int (Int.ofNat (endFreeUrnsInkWord out).toNat)

abbrev endFreeArtValue (out : ByteArray) : Value :=
  .int (Int.ofNat (endFreeUrnsArtWord out).toNat)

abbrev endFreeAfterInkFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFreeAfterUrnsFrame I out).locals.insert "ink" (endFreeInkValue out) }

abbrev endFreeAfterArtFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFreeAfterInkFrame I out).locals.insert "art" (endFreeArtValue out) }

abbrev endFreeInt256LimitWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)

theorem endFreeInt256Limit_eq :
    int256Limit = Int.ofNat endFreeInt256LimitWord.toNat := by
  native_decide

def endFreePostUrnsGuardStmts : List Stmt :=
  [ .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
    .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
    .require (.binary .eq (.var "art") (.intLit 0)),
    .require (.binary .le (.var "ink") (.intLit int256Limit)) ]

theorem endFreeAfterUrnsFrame_get_vatUrn (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterUrnsFrame I out).locals.get? "vatUrn" =
      some (collapseReturns (endFreeUrnsValues out)) := by
  exact store_get_self (endFreeStore I) "vatUrn" (collapseReturns (endFreeUrnsValues out))

theorem endFreeAfterInkFrame_get_vatUrn (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterInkFrame I out).locals.get? "vatUrn" =
      some (collapseReturns (endFreeUrnsValues out)) := by
  change (((endFreeAfterUrnsFrame I out).locals.insert "ink" (endFreeInkValue out)).get?
    "vatUrn") = some (collapseReturns (endFreeUrnsValues out))
  rw [store_get_ne (endFreeAfterUrnsFrame I out).locals (k := "ink") (a := "vatUrn")
    (endFreeInkValue out) (by decide)]
  exact endFreeAfterUrnsFrame_get_vatUrn I out

theorem endFreeAfterArtFrame_get_ink (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterArtFrame I out).locals.get? "ink" = some (endFreeInkValue out) := by
  change (((endFreeAfterInkFrame I out).locals.insert "art" (endFreeArtValue out)).get?
    "ink") = some (endFreeInkValue out)
  rw [store_get_ne (endFreeAfterInkFrame I out).locals (k := "art") (a := "ink")
    (endFreeArtValue out) (by decide)]
  exact store_get_self (endFreeAfterUrnsFrame I out).locals "ink" (endFreeInkValue out)

theorem endFreeAfterArtFrame_get_art (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterArtFrame I out).locals.get? "art" = some (endFreeArtValue out) := by
  exact store_get_self (endFreeAfterInkFrame I out).locals "art" (endFreeArtValue out)

theorem endEvalFreeVatUrnVarAfterUrns (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterUrnsFrame I out) evm (.var "vatUrn") =
      .ok (collapseReturns (endFreeUrnsValues out)) := by
  simpa [evalExpr?, EvalResult.ofOption] using endFreeAfterUrnsFrame_get_vatUrn I out

theorem endEvalFreeVatUrnVarAfterInk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterInkFrame I out) evm (.var "vatUrn") =
      .ok (collapseReturns (endFreeUrnsValues out)) := by
  simpa [evalExpr?, EvalResult.ofOption] using endFreeAfterInkFrame_get_vatUrn I out

theorem endEvalFreeInkVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm (.var "ink") =
      .ok (endFreeInkValue out) := by
  simpa [evalExpr?, EvalResult.ofOption] using endFreeAfterArtFrame_get_ink I out

theorem endEvalFreeArtVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm (.var "art") =
      .ok (endFreeArtValue out) := by
  simpa [evalExpr?, EvalResult.ofOption] using endFreeAfterArtFrame_get_art I out

theorem endEvalFreeInkFromUrn (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config (endFreeAfterUrnsFrame I out) evm
      (.tupleGet (.var "vatUrn") 0) = .ok (endFreeInkValue out) := by
  rw [evalExpr?]
  rw [endEvalFreeVatUrnVarAfterUrns evm I out]
  simp [tupleGetValue?, collapseReturns, endFreeUrnsValues, endFreeInkValue,
    EvalResult.bind, bind]

theorem endEvalFreeArtFromUrn (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config (endFreeAfterInkFrame I out) evm
      (.tupleGet (.var "vatUrn") 1) = .ok (endFreeArtValue out) := by
  rw [evalExpr?]
  rw [endEvalFreeVatUrnVarAfterInk evm I out]
  simp [tupleGetValue?, collapseReturns, endFreeUrnsValues, endFreeArtValue,
    EvalResult.bind, bind]

theorem endEvalFreeArtGuard_true (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hart : endFreeUrnsArtWord out = ⟨0⟩) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool true) := by
  have hnat : (endFreeUrnsArtWord out).toNat = 0 := by
    rw [hart]
    rfl
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFreeArtVarAfterArt evm I out]
  simp [evalExpr?, evalBinaryOp?, endFreeArtValue, hnat, EvalResult.bind, bind, pure]

theorem endEvalFreeArtGuard_false (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hart : endFreeUrnsArtWord out ≠ ⟨0⟩) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.binary .eq (.var "art") (.intLit 0)) = .ok (.bool false) := by
  have hnat : (endFreeUrnsArtWord out).toNat ≠ 0 := by
    intro hzero
    exact hart (uint256_toNat_eq_zero hzero)
  have hint : Int.ofNat (endFreeUrnsArtWord out).toNat ≠ 0 := by
    intro hzero
    have hnatZero : (endFreeUrnsArtWord out).toNat = 0 := by
      exact Int.ofNat_eq_zero.mp hzero
    exact hnat hnatZero
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFreeArtVarAfterArt evm I out]
  simp [evalExpr?, evalBinaryOp?, endFreeArtValue, hint, EvalResult.bind, bind, pure]
  exact hnat

theorem endEvalFreeInkGuard_true (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool true) := by
  have hle : Int.ofNat (endFreeUrnsInkWord out).toNat ≤ int256Limit := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_le.mpr hink
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFreeInkVarAfterArt evm I out]
  simp [evalExpr?, evalBinaryOp?, endFreeInkValue, EvalResult.bind, bind, pure]
  exact hle

theorem endEvalFreeInkGuard_false (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hink : endFreeInt256LimitWord.toNat < (endFreeUrnsInkWord out).toNat) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.binary .le (.var "ink") (.intLit int256Limit)) = .ok (.bool false) := by
  have hlt : int256Limit < Int.ofNat (endFreeUrnsInkWord out).toNat := by
    rw [endFreeInt256Limit_eq]
    exact Int.ofNat_lt.mpr hink
  have hnot : ¬ Int.ofNat (endFreeUrnsInkWord out).toNat ≤ int256Limit :=
    not_le.mpr hlt
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFreeInkVarAfterArt evm I out]
  simp [evalExpr?, evalBinaryOp?, endFreeInkValue, EvalResult.bind, bind, pure]
  exact hlt

theorem endFreePostUrnsGuardOk (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hart : endFreeUrnsArtWord out = ⟨0⟩)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    ExecBlock config (endFreeAfterUrnsFrame I out) evm
      endFreePostUrnsGuardStmts (.ok (endFreeAfterArtFrame I out) evm) := by
  simp [endFreePostUrnsGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.letDecl
      (name := "ink") (ty := some uint256)
      (expr := .tupleGet (.var "vatUrn") 0)
      (value := endFreeInkValue out)
      (endEvalFreeInkFromUrn evm I out)) <|
    ExecBlock.consNormal
      (ExecStmt.letDecl
        (name := "art") (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := endFreeArtValue out)
        (endEvalFreeArtFromUrn evm I out)) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue (endEvalFreeArtGuard_true evm I out hart)) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue (endEvalFreeInkGuard_true evm I out hink)) <|
    ExecBlock.nil

theorem endFreePostUrnsGuardArtRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hart : endFreeUrnsArtWord out ≠ ⟨0⟩) :
    ExecBlock config (endFreeAfterUrnsFrame I out) evm
      endFreePostUrnsGuardStmts .reverted := by
  simp [endFreePostUrnsGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.letDecl
      (name := "ink") (ty := some uint256)
      (expr := .tupleGet (.var "vatUrn") 0)
      (value := endFreeInkValue out)
      (endEvalFreeInkFromUrn evm I out)) <|
    ExecBlock.consNormal
      (ExecStmt.letDecl
        (name := "art") (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := endFreeArtValue out)
        (endEvalFreeArtFromUrn evm I out)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse (endEvalFreeArtGuard_false evm I out hart))

theorem endFreePostUrnsGuardInkRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hart : endFreeUrnsArtWord out = ⟨0⟩)
    (hink : endFreeInt256LimitWord.toNat < (endFreeUrnsInkWord out).toNat) :
    ExecBlock config (endFreeAfterUrnsFrame I out) evm
      endFreePostUrnsGuardStmts .reverted := by
  simp [endFreePostUrnsGuardStmts]
  exact ExecBlock.consNormal
    (ExecStmt.letDecl
      (name := "ink") (ty := some uint256)
      (expr := .tupleGet (.var "vatUrn") 0)
      (value := endFreeInkValue out)
      (endEvalFreeInkFromUrn evm I out)) <|
    ExecBlock.consNormal
      (ExecStmt.letDecl
        (name := "art") (ty := some uint256)
        (expr := .tupleGet (.var "vatUrn") 1)
        (value := endFreeArtValue out)
        (endEvalFreeArtFromUrn evm I out)) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue (endEvalFreeArtGuard_true evm I out hart)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse (endEvalFreeInkGuard_false evm I out hink))

abbrev endFreeAfterGuardsAw (aw : UInt256) : UInt256 :=
  M (M (endFreeAfterUrnsAw aw) (UInt256.ofNat 128) (⟨32⟩ : UInt256))
    (UInt256.ofNat 160) (⟨32⟩ : UInt256)

abbrev endFreeAfterGuardsCursor (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) :
    Cursor :=
  { pc := ⟨8041⟩,
    stack := [⟨0⟩, endFreeUrnsInkWord out, endArg0Word I, ⟨562⟩, sel],
    mem := endFreeUrnsReturnMem I out,
    aw := endFreeAfterGuardsAw aw,
    rdata := out,
    world := world }

theorem endFreePostUrnsGuardsRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨7885⟩
      (fun cur frame e =>
        frame = endFreeAfterUrnsFrame I cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        64 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
            endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endFreeUrnsReturnMem I cur.rdata ∧
        cur.aw = endFreeAfterUrnsAw aw)
      endFreePostUrnsGuardStmts
      (sequenceExit ⟨8041⟩
        (fun cur frame e =>
          frame = endFreeAfterArtFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          64 ≤ cur.rdata.size ∧
          endFreeUrnsArtWord cur.rdata = ⟨0⟩ ∧
          (endFreeUrnsInkWord cur.rdata).toNat ≤ endFreeInt256LimitWord.toNat ∧
          cur.stack = [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endFreeUrnsReturnMem I cur.rdata ∧
          cur.aw = endFreeAfterGuardsAw aw)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hout, h64, hstack, hmem, haw⟩
  cases hframe
  have hloadInk := endFreeUrnsReturnMem_mload128 I cur.rdata hout h64
  have hloadArt := endFreeUrnsReturnMem_mload160 I cur.rdata hout h64
  have hloadInk128 :
      memLoad (⟨128⟩ : UInt256) (endFreeUrnsReturnMem I cur.rdata) =
        endFreeUrnsInkWord cur.rdata := by
    simpa using hloadInk
  have hoff : (⟨128⟩ : UInt256) + UInt256.ofNat 32 = UInt256.ofNat 160 := by
    native_decide
  have rd7885 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7885⟩
        [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          endArg0Word I, ⟨562⟩, sel]
        (endFreeUrnsReturnMem I cur.rdata) cur.aw cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem] using rd
  by_cases hart : endFreeUrnsArtWord cur.rdata = ⟨0⟩
  · have hArtCond :
        UInt256.isZero
            (memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 32)
              (endFreeUrnsReturnMem I cur.rdata)) ≠ UInt256.ofNat 0 := by
      rw [hoff, hloadArt, hart]
      decide
    have rd7969 := endRuntimeBlocks.endRuntime_block_7885_taken
      (x0 := UInt256.ofNat cur.rdata.size) (x1 := (⟨128⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hArtCond (by jump_dest) rd7885
    have rd7969' :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7969⟩
          [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel]
          (endFreeUrnsReturnMem I cur.rdata)
          (M (M cur.aw (UInt256.ofNat 128) (⟨32⟩ : UInt256))
            (UInt256.ofNat 160) (⟨32⟩ : UInt256))
          cur.rdata cur.world (k + 18)
          (C + (56 + memExpansionCost cur.aw (UInt256.ofNat 128) (⟨32⟩ : UInt256) +
            memExpansionCost (M cur.aw (UInt256.ofNat 128) (⟨32⟩ : UInt256))
              ((⟨128⟩ : UInt256) + UInt256.ofNat 32) (⟨32⟩ : UInt256))) := by
      simpa [endRuntimeBlocks.endRuntime_block_7885_taken_stack, hoff, hloadInk128, hloadArt,
        hart] using rd7969
    by_cases hink :
        (endFreeUrnsInkWord cur.rdata).toNat ≤ endFreeInt256LimitWord.toNat
    · have hgt :
          UInt256.gt (endFreeUrnsInkWord cur.rdata) endFreeInt256LimitWord = ⟨0⟩ := by
        exact Reasoning.Theory.ugt_zero hink
      have hInkCond :
          UInt256.isZero
              (UInt256.gt (endFreeUrnsInkWord cur.rdata)
                (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) ≠
            UInt256.ofNat 0 := by
        change UInt256.isZero
              (UInt256.gt (endFreeUrnsInkWord cur.rdata) endFreeInt256LimitWord) ≠
            UInt256.ofNat 0
        rw [hgt]
        decide
      have rd8041 := endRuntimeBlocks.endRuntime_block_7969_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := endFreeUrnsInkWord cur.rdata)
        (R := [endArg0Word I, ⟨562⟩, sel])
        (by simp) hInkCond (by jump_dest) rd7969'
      have hsource := endFreePostUrnsGuardOk evm I cur.rdata hart hink
      refine ⟨.ok (endFreeAfterArtFrame I cur.rdata) evm,
        Endpoint.reached (endFreeAfterGuardsCursor I sel aw cur.rdata cur.world),
        hsource, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endFreeAfterGuardsCursor, endFreeAfterGuardsAw, haw] using rd8041⟩
      · exact ⟨rfl, rfl, hrel, hout, h64, hart, hink, rfl, rfl, rfl⟩
    · have hInkGt : endFreeInt256LimitWord.toNat < (endFreeUrnsInkWord cur.rdata).toNat := by
        omega
      have hgt :
          UInt256.gt (endFreeUrnsInkWord cur.rdata) endFreeInt256LimitWord = ⟨1⟩ := by
        exact Reasoning.Theory.ugt_one hInkGt
      have hInkCond :
          UInt256.isZero
              (UInt256.gt (endFreeUrnsInkWord cur.rdata)
                (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255))) =
            UInt256.ofNat 0 := by
        change UInt256.isZero
              (UInt256.gt (endFreeUrnsInkWord cur.rdata) endFreeInt256LimitWord) =
            UInt256.ofNat 0
        rw [hgt]
        decide
      have rd7982 := endRuntimeBlocks.endRuntime_block_7969_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := endFreeUrnsInkWord cur.rdata)
        (R := [endArg0Word I, ⟨562⟩, sel])
        (by simp) hInkCond rd7969'
      have hrev := endRuntimeBlocks.endRuntime_block_7982
        (R := [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel])
        (by simp) rd7982
      have hsource := endFreePostUrnsGuardInkRevert evm I cur.rdata hart hInkGt
      exact ⟨.reverted, .reverted, hsource, hrev, by
        change True
        trivial⟩
  · have hArtCond :
        UInt256.isZero
            (memLoad ((⟨128⟩ : UInt256) + UInt256.ofNat 32)
              (endFreeUrnsReturnMem I cur.rdata)) = UInt256.ofNat 0 := by
      rw [hoff, hloadArt]
      exact Reasoning.Theory.isZero_eq_zero_of_ne hart
    have rd7906 := endRuntimeBlocks.endRuntime_block_7885_fallthrough
      (x0 := UInt256.ofNat cur.rdata.size) (x1 := (⟨128⟩ : UInt256))
      (x2 := (⟨0⟩ : UInt256)) (x3 := (⟨0⟩ : UInt256))
      (R := [endArg0Word I, ⟨562⟩, sel])
      (by simp) hArtCond rd7885
    have hrev := endRuntimeBlocks.endRuntime_block_7906
        (R := endRuntimeBlocks.endRuntime_block_7885_fallthrough_stack
          (mem := endFreeUrnsReturnMem I cur.rdata) (x1 := (⟨128⟩ : UInt256))
          (R := [endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_7885_fallthrough_stack])
        rd7906
    have hsource := endFreePostUrnsGuardArtRevert evm I cur.rdata hart
    exact ⟨.reverted, .reverted, hsource, hrev, by
      change True
      trivial⟩

theorem endFreeUrnsExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endFreeUrnsCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endFreeStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "urns" (.intLit 0) [.var "ilk", sender] "vatUrn" ]
      (sequenceExit ⟨7885⟩
        (fun cur frame e =>
          frame = endFreeAfterUrnsFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          64 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
              endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endFreeUrnsReturnMem I cur.rdata ∧
          cur.aw = endFreeAfterUrnsAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨7845⟩ = some (.GAS, .none); decide)
    (by simp [endFreeUrnsCallStack, endFreeUrnsCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I, .address I.source])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨7846⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endFreeUrnsCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_free]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat (endPackVatTarget σ I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro h
    rw [endEvalFreeUrnsArgs]
    rw [h.env]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_urns I hsz36]
    change some (endFreeUrnsEncodedCall I) =
      some ((endFreeUrnsCallMem I).readWithPadding 128 68)
    rw [endFreeUrnsCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h64 : 64 ≤ out.size
    · rw [endExternalDecode_urns_ok h64]
      intro rd hrel
      have rd7847 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
            ((⟨1⟩ : UInt256) :: endFreeUrnsCallRest σ I sel)
            (endFreeUrnsReturnMem I out) (endFreeUrnsCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endFreeUrnsCallStack, endFreeUrnsCallRest,
          endFreeUrnsCallAw, endFreeUrnsReturnMem] using rd
      have rd7863 := endRuntimeBlocks.endRuntime_block_7847_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endFreeUrnsCallRest σ I sel)
        (by simp [endFreeUrnsCallRest]) (by native_decide) (by jump_dest) rd7847
      have rd7863' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7863⟩
            [⟨0⟩, ⟨196⟩, endFreeUrnsSelectorWord, endPackVatTarget σ I,
              ⟨0⟩, ⟨0⟩, endArg0Word I, ⟨562⟩, sel]
            (endFreeUrnsReturnMem I out) (endFreeUrnsCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_7847_taken_stack,
          endFreeUrnsCallRest] using rd7863
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide,
          ulit_toNat' out.size hout]
        exact h64
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd7885 := endRuntimeBlocks.endRuntime_block_7863_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨196⟩)
        (x2 := endFreeUrnsSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨0⟩, ⟨0⟩, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd7863'
      have hmem64 := endFreeUrnsReturnMem_mload64 I out hout
      refine ⟨.ok (endFreeAfterUrnsFrame I out) evm',
        Endpoint.reached (endFreeAfterUrnsCursor σ I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endFreeAfterUrnsCursor, endFreeAfterUrnsAw,
            endRuntimeBlocks.endRuntime_block_7863_taken_stack, hmem64] using rd7885⟩
      · exact ⟨rfl, rfl, hrel, hout, h64, rfl, rfl, rfl⟩
    · have hshort : out.size < 64 := by omega
      rw [endExternalDecode_urns_none_short hshort]
      intro rd
      have rd7847 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
            ((⟨1⟩ : UInt256) :: endFreeUrnsCallRest σ I sel)
            (endFreeUrnsReturnMem I out) (endFreeUrnsCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endFreeUrnsCallStack, endFreeUrnsCallRest,
          endFreeUrnsCallAw, endFreeUrnsReturnMem] using rd
      have rd7863 := endRuntimeBlocks.endRuntime_block_7847_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endFreeUrnsCallRest σ I sel)
        (by simp [endFreeUrnsCallRest]) (by native_decide) (by jump_dest) rd7847
      have rd7863' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7863⟩
            [⟨0⟩, ⟨196⟩, endFreeUrnsSelectorWord, endPackVatTarget σ I,
              ⟨0⟩, ⟨0⟩, endArg0Word I, ⟨562⟩, sel]
            (endFreeUrnsReturnMem I out) (endFreeUrnsCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_7847_taken_stack,
          endFreeUrnsCallRest] using rd7863
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 64)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd7881 := endRuntimeBlocks.endRuntime_block_7863_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨196⟩)
        (x2 := endFreeUrnsSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨0⟩, ⟨0⟩, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd7863'
      exact endRuntimeBlocks.endRuntime_block_7881
        (R := endRuntimeBlocks.endRuntime_block_7863_fallthrough_stack
          (mem := endFreeUrnsReturnMem I out) (rdata := out)
          (R := [⟨0⟩, ⟨0⟩, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_7863_fallthrough_stack])
        rd7881
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd7847 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7847⟩
          ((⟨0⟩ : UInt256) :: endFreeUrnsCallRest σ I sel)
          (endFreeUrnsReturnMem I out) (endFreeUrnsCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endFreeUrnsCallStack, endFreeUrnsCallRest,
        endFreeUrnsCallAw, endFreeUrnsReturnMem] using rd
    have rd7854 := endRuntimeBlocks.endRuntime_block_7847_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endFreeUrnsCallRest σ I sel)
      (by simp [endFreeUrnsCallRest]) (by native_decide) rd7847
    exact endRuntimeBlocks.endRuntime_block_7854
      (R := endRuntimeBlocks.endRuntime_block_7847_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endFreeUrnsCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_7847_fallthrough_stack,
        endFreeUrnsCallRest])
      rd7854

/-! ### Final `vat.grab` call for `free(bytes32)` -/

abbrev endFreeGrabSelectorWord : UInt256 := UInt256.ofNat 2074820416

theorem endFreeStore_get_vow_none (I : ExecutionEnv) :
    (endFreeStore I).get? "vow" = none := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).get? "vow") = none
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "vow")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endFreeAfterUrnsFrame_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterUrnsFrame I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endFreeStore I).insert "vatUrn" (collapseReturns (endFreeUrnsValues out))).get?
    "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endFreeStore I) (k := "vatUrn") (a := "ilk")
    (collapseReturns (endFreeUrnsValues out)) (by decide)]
  exact endFreeStore_get_ilk I

theorem endFreeAfterInkFrame_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterInkFrame I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endFreeAfterUrnsFrame I out).locals.insert "ink" (endFreeInkValue out)).get?
    "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endFreeAfterUrnsFrame I out).locals (k := "ink") (a := "ilk")
    (endFreeInkValue out) (by decide)]
  exact endFreeAfterUrnsFrame_get_ilk I out

theorem endFreeAfterArtFrame_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterArtFrame I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endFreeAfterInkFrame I out).locals.insert "art" (endFreeArtValue out)).get?
    "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne (endFreeAfterInkFrame I out).locals (k := "art") (a := "ilk")
    (endFreeArtValue out) (by decide)]
  exact endFreeAfterInkFrame_get_ilk I out

theorem endFreeAfterArtFrame_get_vat_none (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterArtFrame I out).locals.get? "vat" = none := by
  change (((endFreeAfterInkFrame I out).locals.insert "art" (endFreeArtValue out)).get?
    "vat") = none
  rw [store_get_ne (endFreeAfterInkFrame I out).locals (k := "art") (a := "vat")
    (endFreeArtValue out) (by decide)]
  change (((endFreeAfterUrnsFrame I out).locals.insert "ink" (endFreeInkValue out)).get?
    "vat") = none
  rw [store_get_ne (endFreeAfterUrnsFrame I out).locals (k := "ink") (a := "vat")
    (endFreeInkValue out) (by decide)]
  change (((endFreeStore I).insert "vatUrn" (collapseReturns (endFreeUrnsValues out))).get?
    "vat") = none
  rw [store_get_ne (endFreeStore I) (k := "vatUrn") (a := "vat")
    (collapseReturns (endFreeUrnsValues out)) (by decide)]
  exact endFreeStore_get_vat_none I

theorem endFreeAfterArtFrame_get_vow_none (I : ExecutionEnv) (out : ByteArray) :
    (endFreeAfterArtFrame I out).locals.get? "vow" = none := by
  change (((endFreeAfterInkFrame I out).locals.insert "art" (endFreeArtValue out)).get?
    "vow") = none
  rw [store_get_ne (endFreeAfterInkFrame I out).locals (k := "art") (a := "vow")
    (endFreeArtValue out) (by decide)]
  change (((endFreeAfterUrnsFrame I out).locals.insert "ink" (endFreeInkValue out)).get?
    "vow") = none
  rw [store_get_ne (endFreeAfterUrnsFrame I out).locals (k := "ink") (a := "vow")
    (endFreeInkValue out) (by decide)]
  change (((endFreeStore I).insert "vatUrn" (collapseReturns (endFreeUrnsValues out))).get?
    "vow") = none
  rw [store_get_ne (endFreeStore I) (k := "vatUrn") (a := "vow")
    (collapseReturns (endFreeUrnsValues out)) (by decide)]
  exact endFreeStore_get_vow_none I

theorem endEvalFreeIlkVarAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
  simpa [evalExpr?, EvalResult.ofOption] using endFreeAfterArtFrame_get_ilk I out

theorem endEvalVatAddress_free_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (endFreeAfterArtFrame I out) evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endFreeAfterArtFrame_get_vat_none I out) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVowAddress_free_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (endFreeAfterArtFrame I out) evm
      vowRef = .ok { base := "vow", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vow", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  unfold vowAddr
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endFreeAfterArtFrame_get_vow_none I out) (her := her)
    (hty := hty) (hloc := endConfig_storage_vow),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_free_afterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_free_afterArt evm I out]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_free_afterArt_false (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_free_afterArt evm I out, hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_free_afterArt_true (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_free_afterArt evm I out]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalFreeNegInkAfterArt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFreeAfterArtFrame I out) evm
      (.unary .neg (asInt256 (.var "ink"))) =
      .ok (.int (-(Int.ofNat (endFreeUrnsInkWord out).toNat))) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endFreeAfterArtFrame I out) evm
        (Expr.cast (.var "ink") int256St)
      EvalResult.ofOption EvalError.typeError (evalUnaryOp? UnaryOp.neg value)) =
    .ok (.int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)))
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← (do
        let value ← evalExpr? config (endFreeAfterArtFrame I out) evm (.var "ink")
        EvalResult.ofOption EvalError.typeError (castValue? value int256St))
      EvalResult.ofOption EvalError.typeError (evalUnaryOp? UnaryOp.neg value)) =
    .ok (.int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)))
  rw [endEvalFreeInkVarAfterArt evm I out]
  simp [int256St, castValue?, evalUnaryOp?, EvalResult.bind, EvalResult.ofOption,
    bind, pure]

theorem endEvalFreeGrabArgs (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExprs? config (endFreeAfterArtFrame I out) evm
      [.var "ilk", sender, sender, vowAddr, .unary .neg (asInt256 (.var "ink")), .intLit 0] =
    .ok [endArg0Bytes32Value I, .address evm.executionEnv.source,
      .address evm.executionEnv.source,
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat),
      .int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)), .int 0] := by
  simp [evalExprs?, evalExpr?, sender, envValue, EvalResult.ofOption, EvalResult.bind, bind,
    pure, endEvalFreeIlkVarAfterArt, endEvalVowAddress_free_afterArt,
    endEvalFreeNegInkAfterArt]

theorem endWordOfInt_neg_ofNat_toNat (w : UInt256) :
    EVM.wordOfInt (-(Int.ofNat w.toNat)) = UInt256.sub (⟨0⟩ : UInt256) w := by
  by_cases hzero : w.toNat = 0
  · have hw : w = ⟨0⟩ := uint256_toNat_eq_zero hzero
    subst w
    native_decide
  · have hpos : 0 < w.toNat := Nat.pos_of_ne_zero hzero
    have hsize : EVM.wordModulus = UInt256.size := by
      native_decide
    have hmod : w.toNat % EVM.wordModulus = w.toNat := by
      rw [hsize]
      exact Nat.mod_eq_of_lt w.val.isLt
    have hnatAbs : (Int.ofNat w.toNat).natAbs = w.toNat := by
      simp
    have hneg : -(Int.ofNat w.toNat) < 0 := by
      have hposInt : (0 : Int) < Int.ofNat w.toNat := by
        exact Int.natCast_pos.mpr hpos
      omega
    rw [EVM.wordOfInt, if_pos hneg]
    simp only [Int.natAbs_neg, hnatAbs, hmod, if_neg hzero]
    apply u256_inj
    rw [usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos]
    change (UInt256.ofNat (EVM.wordModulus - w.toNat)).toNat =
      UInt256.size + (⟨0⟩ : UInt256).toNat - w.toNat
    rw [hsize]
    rw [ulit_toNat' (UInt256.size - w.toNat) (by
      have hlt := w.val.isLt
      omega)]
    simp

theorem endFreeInt256LimitWord_toNat :
    endFreeInt256LimitWord.toNat = EVM.twoPow 255 := by
  native_decide

theorem endEncodeABIWord_int256_negInk (out : ByteArray)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    encodeABIWord? int256
      (.int (-(Int.ofNat (endFreeUrnsInkWord out).toNat))) =
      some (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out)) := by
  unfold int256 int256Int
  change (if (⟨256, by decide⟩ : BitWidth).val = 0 then none else
      (let positiveLimit := Int.ofNat (EVM.twoPow ((⟨256, by decide⟩ : BitWidth).val - 1))
       if -positiveLimit ≤ -(Int.ofNat (endFreeUrnsInkWord out).toNat) ∧
            -(Int.ofNat (endFreeUrnsInkWord out).toNat) < positiveLimit then
         some (EVM.wordOfInt (-(Int.ofNat (endFreeUrnsInkWord out).toNat)))
       else none)) =
    some (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
  rw [if_neg (by decide : ¬ (⟨256, by decide⟩ : BitWidth).val = 0)]
  change (if
      -Int.ofNat (EVM.twoPow 255) ≤
          -(Int.ofNat (endFreeUrnsInkWord out).toNat) ∧
        -(Int.ofNat (endFreeUrnsInkWord out).toNat) <
          Int.ofNat (EVM.twoPow 255) then
      some (EVM.wordOfInt (-(Int.ofNat (endFreeUrnsInkWord out).toNat)))
    else none) =
    some (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
  have hrange :
      -Int.ofNat (EVM.twoPow 255) ≤
          -(Int.ofNat (endFreeUrnsInkWord out).toNat) ∧
        -(Int.ofNat (endFreeUrnsInkWord out).toNat) <
          Int.ofNat (EVM.twoPow 255) := by
    constructor
    · rw [← endFreeInt256LimitWord_toNat]
      exact neg_le_neg (Int.ofNat_le.mpr hink)
    · have hpos : (0 : Int) < Int.ofNat (EVM.twoPow 255) := by
        norm_num [EVM.twoPow]
      exact lt_of_le_of_lt (neg_nonpos.mpr (Int.ofNat_nonneg _)) hpos
  rw [if_pos hrange]
  rw [endWordOfInt_neg_ofNat_toNat]

theorem endEncodeInt256_negInk (out : ByteArray)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    encodeABIValue? int256
      (.int (-(Int.ofNat (endFreeUrnsInkWord out).toNat))) =
      some (EVM.Word.toBytesBE (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? int256
        (.int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)))
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out)))
  rw [endEncodeABIWord_int256_negInk out hink]
  simp only [bind, Option.bind]

theorem endEncodeInt256_zero :
    encodeABIValue? int256 (.int 0) =
      some (EVM.Word.toBytesBE (⟨0⟩ : UInt256)) := by
  native_decide

def endFreeGrabPayloadBytes (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) :
    List UInt8 :=
  (((((EVM.Word.toBytesBE (endArg0Word I) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) ++
      EVM.Word.toBytesBE (endPackVowTarget σ I)) ++
      EVM.Word.toBytesBE (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))) ++
      EVM.Word.toBytesBE (⟨0⟩ : UInt256))

def endFreeGrabEncodedCall (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  grabSelector ++ ⟨(endFreeGrabPayloadBytes σ I out).toArray⟩

theorem endExternalEncode_grab_branch (args : List Value) :
    config.externalABI.encode? "grab" args =
      ABI.encodeCallWithSelector? grabSelector [bytes32, addr, addr, addr, int256, int256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "grab" = "cage")]
  rw [if_neg (by decide : ¬ "grab" = "vatIlks")]
  rw [if_neg (by decide : ¬ "grab" = "catIlks")]
  rw [if_neg (by decide : ¬ "grab" = "dogIlks")]
  rw [if_neg (by decide : ¬ "grab" = "spotIlks")]
  rw [if_neg (by decide : ¬ "grab" = "urns")]
  rw [if_neg (by decide : ¬ "grab" = "dai")]
  rw [if_neg (by decide : ¬ "grab" = "debt")]
  rw [if_neg (by decide : ¬ "grab" = "move")]
  rw [if_neg (by decide : ¬ "grab" = "hope")]
  rw [if_neg (by decide : ¬ "grab" = "flux")]
  rw [if_pos (by decide : "grab" = "grab")]

theorem endEncodeABIValues_grab (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    encodeABIValues? [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, .address I.source, .address I.source,
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)), .int 0] =
      some (endFreeGrabPayloadBytes σ I out) := by
  have hhead : abiTupleHeadSize? [bytes32, addr, addr, addr, int256, int256] =
      some 192 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynInt : isDynamicABIType int256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I hsz36, hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_source I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_source I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow σ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_negInk out hink, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_zero, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endFreeGrabPayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_grab (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    ABI.encodeCallWithSelector? grabSelector [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, .address I.source, .address I.source,
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)), .int 0] =
      some (endFreeGrabEncodedCall σ I out) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_grab σ I out hsz36 hink]
  simp [endFreeGrabEncodedCall, endFreeGrabPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_grab (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hink : (endFreeUrnsInkWord out).toNat ≤ endFreeInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
      [endArg0Bytes32Value I, .address I.source, .address I.source,
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .int (-(Int.ofNat (endFreeUrnsInkWord out).toNat)), .int 0] =
      some (endFreeGrabEncodedCall σ I out) := by
  rw [endExternalEncode_grab_branch]
  exact endEncodeCallWithSelector_grab σ I out hsz36 hink

theorem endExternalDecode_grab (out : ByteArray) :
    config.externalABI.decode? "grab" out = some [] := by
  rfl

abbrev endFreeGrabSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) endFreeGrabSelectorWord)
    (UInt256.ofNat 224)

abbrev endFreeGrabVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land endPackCallAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 4))

abbrev endFreeGrabMemSel (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endFreeGrabSelectorEncodedWord.toByteArray.write 0 (endFreeUrnsReturnMem I out) 128 32

abbrev endFreeGrabMemIlk (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endFreeGrabMemSel I out) 132 32

abbrev endFreeGrabMemSource1 (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.ofNat I.source.val).toByteArray.write 0 (endFreeGrabMemIlk I out) 164 32

abbrev endFreeGrabMemSource2 (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.ofNat I.source.val).toByteArray.write 0 (endFreeGrabMemSource1 I out) 196 32

abbrev endFreeGrabMemVow (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (endFreeGrabVowWord σ I).toByteArray.write 0 (endFreeGrabMemSource2 I out) 228 32

abbrev endFreeGrabMemInk (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out)).toByteArray.write 0
    (endFreeGrabMemVow σ I out) 260 32

abbrev endFreeGrabMemFull (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 (endFreeGrabMemInk σ I out) 292 32

abbrev endFreeGrabCallMem (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_8041_memory
    (ee := I) (mem := endFreeUrnsReturnMem I out) (σ := σ)
    (x1 := endFreeUrnsInkWord out) (x2 := endArg0Word I)

theorem endFreeGrabSelectorEncodedWord_generated :
    UInt256.shiftLeft (UInt256.ofNat 32419069) (UInt256.ofNat 230) =
      endFreeGrabSelectorEncodedWord := by
  native_decide

theorem endFreeGrabCallMem_eq_full (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) :
    endFreeGrabCallMem σ I out = endFreeGrabMemFull σ I out := by
  have hfreeCall : memLoad (UInt256.ofNat 64) (endFreeUrnsReturnMem I out) = ⟨128⟩ :=
    endFreeUrnsReturnMem_mload64 I out hout
  unfold endFreeGrabCallMem endFreeGrabMemFull endFreeGrabMemInk endFreeGrabMemVow
    endFreeGrabMemSource2 endFreeGrabMemSource1 endFreeGrabMemIlk endFreeGrabMemSel
    endFreeGrabSelectorEncodedWord endFreeGrabVowWord endPackCallAddrMask
  dsimp [endRuntimeBlocks.endRuntime_block_8041_memory]
  rw [hfreeCall]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
  rw [endFreeGrabSelectorEncodedWord_generated]
  rfl

theorem endFreeUrnsReturnMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) :
    (endFreeUrnsReturnMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hfacts := callOutputFacts (endFreeUrnsCallMem I) out (⟨128⟩ : UInt256)
    (⟨64⟩ : UInt256) hout (by
      change 128 + 64 ≤ (endFreeUrnsCallMem I).size
      have hsize := endFreeUrnsCallMem_size_ge196 I
      omega)
  have hread :
      (endFreeUrnsReturnMem I out).readWithPadding 64 32 =
        (endFreeUrnsCallMem I).readWithPadding 64 32 := by
    simpa [endFreeUrnsReturnMem] using hfacts.readBelow 64 (by native_decide)
  rw [hread, endFreeUrnsCallMem_read64 I]

theorem endFreeGrabMemSel_size_ge160 (I : ExecutionEnv) (out : ByteArray) :
    160 ≤ (endFreeGrabMemSel I out).size :=
  toByteArray_write_size_ge_off_add32_unbounded endFreeGrabSelectorEncodedWord
    (endFreeUrnsReturnMem I out) 128

theorem endFreeGrabMemIlk_size_ge164 (I : ExecutionEnv) (out : ByteArray) :
    164 ≤ (endFreeGrabMemIlk I out).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I)
    (endFreeGrabMemSel I out) 132

theorem endFreeGrabMemSource1_size_ge196 (I : ExecutionEnv) (out : ByteArray) :
    196 ≤ (endFreeGrabMemSource1 I out).size :=
  toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemIlk I out) 164

theorem endFreeGrabMemSource2_size_ge228 (I : ExecutionEnv) (out : ByteArray) :
    228 ≤ (endFreeGrabMemSource2 I out).size :=
  toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemSource1 I out) 196

theorem endFreeGrabMemVow_size_ge260 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    260 ≤ (endFreeGrabMemVow σ I out).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endFreeGrabVowWord σ I)
    (endFreeGrabMemSource2 I out) 228

theorem endFreeGrabMemInk_size_ge292 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) :
    292 ≤ (endFreeGrabMemInk σ I out).size :=
  toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260

theorem endFreeGrabCallMem_size_ge324 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    324 ≤ (endFreeGrabCallMem σ I out).size := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  exact toByteArray_write_size_ge_off_add32_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292

theorem endFreeGrabCallMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [toByteArray_write_read_below_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292 64
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260 64
    (by have := endFreeGrabMemVow_size_ge260 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endFreeGrabVowWord σ I)
    (endFreeGrabMemSource2 I out) 228 64
    (by have := endFreeGrabMemSource2_size_ge228 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemSource1 I out) 196 64
    (by have := endFreeGrabMemSource1_size_ge196 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemIlk I out) 164 64
    (by have := endFreeGrabMemIlk_size_ge164 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg0Word I)
    (endFreeGrabMemSel I out) 132 64
    (by have := endFreeGrabMemSel_size_ge160 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endFreeGrabSelectorEncodedWord
    (endFreeUrnsReturnMem I out) 128 64
    (by
      rw [endFreeUrnsReturnMem_size I out hout]
      have hsize := endFreeUrnsCallMem_size_ge196 I
      omega) (by omega)]
  exact endFreeUrnsReturnMem_read64 I out hout

theorem endFreeGrabCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endFreeGrabCallMem σ I out) = ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥ (endFreeGrabCallMem σ I out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((endFreeGrabCallMem σ I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endFreeGrabCallMem σ I out)
    (by
      have hge := endFreeGrabCallMem_size_ge324 σ I out hout
      change 64 < (endFreeGrabCallMem σ I out).size
      omega)
    (endFreeGrabCallMem_read64 σ I out hout)

theorem endFreeGrabSelectorEncodedWord_prefix :
    (endFreeGrabSelectorEncodedWord.toByteArray).extract 0 4 = grabSelector := by
  native_decide

theorem endFreeGrabCallMem_readSelector (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 128 4 = grabSelector := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [write32_read_below_len _ _ 292 128 4 (by rw [toByteArray_size])
    (endFreeGrabMemInk_size_ge292 σ I out) (by omega)
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 260 128 4 (by rw [toByteArray_size])
    (endFreeGrabMemVow_size_ge260 σ I out) (by omega)
    (by have := endFreeGrabMemVow_size_ge260 σ I out; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (endFreeGrabMemSource2_size_ge228 I out) (by omega)
    (by have := endFreeGrabMemSource2_size_ge228 I out; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (endFreeGrabMemSource1_size_ge196 I out) (by omega)
    (by have := endFreeGrabMemSource1_size_ge196 I out; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endFreeGrabMemIlk_size_ge164 I out) (by omega)
    (by have := endFreeGrabMemIlk_size_ge164 I out; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endFreeGrabMemSel_size_ge160 I out; omega) (by omega)
    (by have := endFreeGrabMemSel_size_ge160 I out; omega) (by decide) (by decide)]
  change ((endFreeGrabSelectorEncodedWord.toByteArray.write 0 (endFreeUrnsReturnMem I out)
      128 32).readWithPadding 128 4) = grabSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endFreeGrabSelectorEncodedWord (endFreeUrnsReturnMem I out) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFreeGrabSelectorEncodedWord_prefix]

theorem endFreeGrabCallMem_readIlk (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [toByteArray_write_read_below_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292 132
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260 132
    (by have := endFreeGrabMemVow_size_ge260 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endFreeGrabVowWord σ I)
    (endFreeGrabMemSource2 I out) 228 132
    (by have := endFreeGrabMemSource2_size_ge228 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemSource1 I out) 196 132
    (by have := endFreeGrabMemSource1_size_ge196 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemIlk I out) 164 132
    (by have := endFreeGrabMemIlk_size_ge164 I out; omega) (by omega)]
  change (((endArg0Word I).toByteArray.write 0
      (endFreeGrabMemSel I out) 132 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg0Word I)
    (endFreeGrabMemSel I out) 132

theorem endFreeGrabCallMem_readSource1 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 164 32 =
      (UInt256.ofNat I.source.val).toByteArray := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [toByteArray_write_read_below_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292 164
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260 164
    (by have := endFreeGrabMemVow_size_ge260 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endFreeGrabVowWord σ I)
    (endFreeGrabMemSource2 I out) 228 164
    (by have := endFreeGrabMemSource2_size_ge228 I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemSource1 I out) 196 164
    (by have := endFreeGrabMemSource1_size_ge196 I out; omega) (by omega)]
  change (((UInt256.ofNat I.source.val).toByteArray.write 0
      (endFreeGrabMemIlk I out) 164 32).readWithPadding 164 32) =
    (UInt256.ofNat I.source.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemIlk I out) 164

theorem endFreeGrabCallMem_readSource2 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 196 32 =
      (UInt256.ofNat I.source.val).toByteArray := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [toByteArray_write_read_below_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292 196
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260 196
    (by have := endFreeGrabMemVow_size_ge260 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endFreeGrabVowWord σ I)
    (endFreeGrabMemSource2 I out) 228 196
    (by have := endFreeGrabMemSource2_size_ge228 I out; omega) (by omega)]
  change ((UInt256.ofNat I.source.val).toByteArray.write 0
      (endFreeGrabMemSource1 I out) 196 32).readWithPadding 196 32 =
    (UInt256.ofNat I.source.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.source.val)
    (endFreeGrabMemSource1 I out) 196

theorem endFreeGrabCallMem_readVow (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 228 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [toByteArray_write_read_below_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292 228
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260 228
    (by have := endFreeGrabMemVow_size_ge260 σ I out; omega) (by omega)]
  change ((endFreeGrabVowWord σ I).toByteArray.write 0
      (endFreeGrabMemSource2 I out) 228 32).readWithPadding 228 32 =
    (endPackVowTarget σ I).toByteArray
  rw [toByteArray_write_read_back_of_gap_unbounded (endFreeGrabVowWord σ I)
    (endFreeGrabMemSource2 I out) 228]
  have hvow : endFreeGrabVowWord σ I = endPackVowTarget σ I := by
    simp [endFreeGrabVowWord, endPackVowTarget, endPackCallAddrMask_eq_solc]
  rw [hvow]

theorem endFreeGrabCallMem_readInk (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 260 32 =
      (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out)).toByteArray := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  rw [toByteArray_write_read_below_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292 260
    (by have := endFreeGrabMemInk_size_ge292 σ I out; omega) (by omega)]
  change ((UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out)).toByteArray.write 0
      (endFreeGrabMemVow σ I out) 260 32).readWithPadding 260 32 =
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out)).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.sub (⟨0⟩ : UInt256) (endFreeUrnsInkWord out))
    (endFreeGrabMemVow σ I out) 260

theorem endFreeGrabCallMem_readZero (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 292 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  rw [endFreeGrabCallMem_eq_full σ I out hout]
  change (((⟨0⟩ : UInt256).toByteArray.write 0
      (endFreeGrabMemInk σ I out) 292 32).readWithPadding 292 32) =
    (⟨0⟩ : UInt256).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (⟨0⟩ : UInt256)
    (endFreeGrabMemInk σ I out) 292

theorem endFreeGrabCallMem_readCallData (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endFreeGrabCallMem σ I out).readWithPadding 128 196 =
      endFreeGrabEncodedCall σ I out := by
  have hsize := endFreeGrabCallMem_size_ge324 σ I out hout
  rw [show 196 = 4 + 192 from rfl]
  rw [byteArray_readWithPadding_split (endFreeGrabCallMem σ I out) 128 4 192
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 192 = 32 + 160 from rfl]
  rw [byteArray_readWithPadding_split (endFreeGrabCallMem σ I out) 132 32 160
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 160 = 32 + 128 from rfl]
  rw [byteArray_readWithPadding_split (endFreeGrabCallMem σ I out) 164 32 128
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [show 128 = 32 + 96 from rfl]
  rw [byteArray_readWithPadding_split (endFreeGrabCallMem σ I out) 196 32 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 196 + 32 = 228 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split (endFreeGrabCallMem σ I out) 228 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 228 + 32 = 260 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endFreeGrabCallMem σ I out) 260 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 260 + 32 = 292 by norm_num]
  rw [endFreeGrabCallMem_readSelector σ I out hout,
    endFreeGrabCallMem_readIlk σ I out hout,
    endFreeGrabCallMem_readSource1 σ I out hout,
    endFreeGrabCallMem_readSource2 σ I out hout,
    endFreeGrabCallMem_readVow σ I out hout,
    endFreeGrabCallMem_readInk σ I out hout,
    endFreeGrabCallMem_readZero σ I out hout]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endFreeGrabEncodedCall, endFreeGrabPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endFreeGrabCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256)
    (out : ByteArray) : List UInt256 :=
  [⟨324⟩, endFreeGrabSelectorWord, endPackVatTarget σ I, ⟨0⟩,
    endFreeUrnsInkWord out, endArg0Word I, ⟨562⟩, sel]

abbrev endFreeGrabCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256)
    (out : ByteArray) : List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨196⟩, ⟨128⟩, ⟨0⟩] ++
    endFreeGrabCallRest σ I sel out

abbrev endFreeGrabCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (sel aw : UInt256) (out : ByteArray) : Cursor :=
  { pc := ⟨8157⟩, stack := endFreeGrabCallStack world.2 I sel out,
    mem := endFreeGrabCallMem world.2 I out, aw := aw, rdata := out,
    world := world }

abbrev endFreeGrabCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨196⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat
      (⟨0⟩ : UInt256).toNat)

abbrev endFreeAfterGrabFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFreeAfterArtFrame I out).locals.insert "_grab" (collapseReturns []) }

theorem endFreeGrabExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw outUrns k C evm}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (houtUrns : outUrns.size < UInt256.size)
    (hink : (endFreeUrnsInkWord outUrns).toNat ≤ endFreeInt256LimitWord.toNat) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endFreeGrabCallCursor world I sel aw outUrns)
      k C (endFreeAfterArtFrame I outUrns) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", sender, sender, vowAddr,
            .unary .neg (asInt256 (.var "ink")), .intLit 0] "_grab" ]
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨8157⟩ = some (.GAS, .none); decide)
    (by simp [endFreeGrabCallCursor, endFreeGrabCallStack, endFreeGrabCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I, .address I.source, .address I.source,
      .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .int (-(Int.ofNat (endFreeUrnsInkWord outUrns).toNat)), .int 0])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨8158⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endFreeGrabCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_free_afterArt]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endPackVatTarget world.2 I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 4)
    rw [h.env] at hload
    rw [endEvalFreeGrabArgs]
    rw [h.env]
    change EvalResult.ok
      [endArg0Bytes32Value I, Value.address I.source, Value.address I.source,
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        Value.int (-(Int.ofNat (endFreeUrnsInkWord outUrns).toNat)), Value.int 0] =
      EvalResult.ok
        [endArg0Bytes32Value I, Value.address I.source, Value.address I.source,
          Value.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          Value.int (-(Int.ofNat (endFreeUrnsInkWord outUrns).toNat)), Value.int 0]
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 4)) solcAddrMask]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_grab world.2 I outUrns hsz36 hink]
    change some (endFreeGrabEncodedCall world.2 I outUrns) =
      some ((endFreeGrabCallMem world.2 I outUrns).readWithPadding 128 196)
    rw [endFreeGrabCallMem_readCallData world.2 I outUrns houtUrns]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_grab out]
    intro rd hrel
    have rd8159 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8159⟩
          ((⟨1⟩ : UInt256) :: endFreeGrabCallRest world.2 I sel outUrns)
          (endFreeGrabCallMem world.2 I outUrns) (endFreeGrabCallAw aw)
          out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endFreeGrabCallCursor,
        endFreeGrabCallStack, endFreeGrabCallRest, endFreeGrabCallAw] using rd
    have rd8175 := endRuntimeBlocks.endRuntime_block_8159_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endFreeGrabCallRest world.2 I sel outUrns)
      (by simp [endFreeGrabCallRest]) (by native_decide) (by jump_dest) rd8159
    have rd562 := endRuntimeBlocks.endRuntime_block_8175
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨324⟩ : UInt256))
      (x2 := endFreeGrabSelectorWord) (x3 := endPackVatTarget world.2 I)
      (x4 := (⟨0⟩ : UInt256)) (x5 := endFreeUrnsInkWord outUrns)
      (x6 := endArg0Word I) (x7 := (⟨562⟩ : UInt256)) (R := [sel])
      (by simp) hperm (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_8159_taken_stack,
          endFreeGrabCallRest] using rd8175)
    have rdret := endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp) rd562
    exact BlockProgress.ofRDret ExecBlock.nil rdret
      (by simpa using hrel.created.symm)
      (by simpa using hrel.accounts)
      abiVoidFallthrough
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd8159 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8159⟩
          ((⟨0⟩ : UInt256) :: endFreeGrabCallRest world.2 I sel outUrns)
          (endFreeGrabCallMem world.2 I outUrns) (endFreeGrabCallAw aw)
          out world' k' C' := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endFreeGrabCallCursor,
        endFreeGrabCallStack, endFreeGrabCallRest, endFreeGrabCallAw] using rd
    have rd8166 := endRuntimeBlocks.endRuntime_block_8159_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endFreeGrabCallRest world.2 I sel outUrns)
      (by simp [endFreeGrabCallRest]) (by native_decide) rd8159
    exact endRuntimeBlocks.endRuntime_block_8166
      (R := endRuntimeBlocks.endRuntime_block_8159_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endFreeGrabCallRest world.2 I sel outUrns))
      (by simp [endRuntimeBlocks.endRuntime_block_8159_fallthrough_stack,
        endFreeGrabCallRest])
      rd8166

theorem endFreeGrabCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨8041⟩
      (fun cur frame e =>
        frame = endFreeAfterArtFrame I cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        64 ≤ cur.rdata.size ∧
        endFreeUrnsArtWord cur.rdata = ⟨0⟩ ∧
        (endFreeUrnsInkWord cur.rdata).toNat ≤ endFreeInt256LimitWord.toNat ∧
        cur.stack = [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endFreeUrnsReturnMem I cur.rdata ∧
        cur.aw = endFreeAfterGuardsAw aw)
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", sender, sender, vowAddr,
          .unary .neg (asInt256 (.var "ink")), .intLit 0]
        "_grab")
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hout, _h64, _hart, hink, hstack, hmem, haw⟩
  cases hframe
  have rd8041 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8041⟩
        [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel]
        (endFreeUrnsReturnMem I cur.rdata) (endFreeAfterGuardsAw aw)
        cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  obtain ⟨aw8122, k8122, C8122, rd8122⟩ :=
    endRuntimeBlocks.endRuntime_block_8041_packed
      (x0 := (⟨0⟩ : UInt256)) (x1 := endFreeUrnsInkWord cur.rdata)
      (x2 := endArg0Word I) (R := [⟨562⟩, sel]) (by simp) rd8041
  have hloadOld :
      memLoad (UInt256.ofNat 64) (endFreeUrnsReturnMem I cur.rdata) = ⟨128⟩ :=
    endFreeUrnsReturnMem_mload64 I cur.rdata hout
  have hloadNew :
      memLoad (UInt256.ofNat 64) (endFreeGrabCallMem cur.world.2 I cur.rdata) = ⟨128⟩ :=
    endFreeGrabCallMem_mload64 cur.world.2 I cur.rdata hout
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hloadNewRaw := hloadNew
  dsimp [endFreeGrabCallMem, endRuntimeBlocks.endRuntime_block_8041_memory] at hloadNewRaw
  rw [hloadOld, hmaskGenerated] at hloadNewRaw
  have rd8122' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8122⟩
        [⟨0⟩, ⟨128⟩, ⟨128⟩, endPackVatTarget cur.world.2 I,
          ⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel]
        (endFreeGrabCallMem cur.world.2 I cur.rdata) aw8122
        cur.rdata cur.world k8122 C8122 := by
    simpa [endRuntimeBlocks.endRuntime_block_8041_stack, endFreeGrabCallMem,
      endPackVatTarget, hmaskGenerated, u256_land_comm, hloadOld, hloadNewRaw] using rd8122
  have hslotVat := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
  rw [hrel.env] at hslotVat
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) := by
    rw [hrel.env]
    rw [hslotVat]
    have htarget :
        UInt256.land (storageRead I.codeOwner cur.world.2 (UInt256.ofNat 1)) solcAddrMask =
          endPackVatTarget cur.world.2 I := by
      simp [endPackVatTarget, u256_land_comm]
    rw [htarget]
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts (endPackVatTarget cur.world.2 I)).symm
  by_cases hvatNoCode :
      extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) = ⟨0⟩ := by
      rw [hsrcCodeEq, hvatNoCode]
    have hcond :
        UInt256.isZero
            (UInt256.isZero
              (extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I))) =
          UInt256.ofNat 0 := by
      rw [hvatNoCode]
      decide
    obtain ⟨k8151, C8151, rd8151⟩ :=
      endRuntimeBlocks.endRuntime_block_8122_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨128⟩ : UInt256))
        (x2 := (⟨128⟩ : UInt256)) (x3 := endPackVatTarget cur.world.2 I)
        (R := [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel])
        (by simp) hcond rd8122'
    have hrev := endRuntimeBlocks.endRuntime_block_8151
      (R := endRuntimeBlocks.endRuntime_block_8122_fallthrough_stack
        (σ := cur.world.2) (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨128⟩ : UInt256))
        (x2 := (⟨128⟩ : UInt256)) (x3 := endPackVatTarget cur.world.2 I)
        (R := [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel]))
      (by simp [endRuntimeBlocks.endRuntime_block_8122_fallthrough_stack])
      rd8151
    have hsource :
        ExecBlock config (endFreeAfterArtFrame I cur.rdata) evm
          (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
            [.var "ilk", sender, sender, vowAddr,
              .unary .neg (asInt256 (.var "ink")), .intLit 0]
            "_grab")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_free_afterArt_false evm I cur.rdata hsrcNoCode)))
    exact BlockProgress.ofRDrev hsource hrev
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hcond :
        UInt256.isZero
            (UInt256.isZero
              (extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I))) ≠
          UInt256.ofNat 0 := by
      rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatNoCode]
      native_decide
    obtain ⟨k8155, C8155, rd8155⟩ :=
      endRuntimeBlocks.endRuntime_block_8122_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨128⟩ : UInt256))
        (x2 := (⟨128⟩ : UInt256)) (x3 := endPackVatTarget cur.world.2 I)
        (R := [⟨0⟩, endFreeUrnsInkWord cur.rdata, endArg0Word I, ⟨562⟩, sel])
        (by simp) hcond (by jump_dest) rd8122'
    have rd8157 := endRuntimeBlocks.endRuntime_block_8155
      (x0 := UInt256.isZero
        (extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I)))
      (R := endFreeGrabCallStack cur.world.2 I sel cur.rdata)
      (by simp [endFreeGrabCallStack, endFreeGrabCallRest])
      (by
        simpa [endRuntimeBlocks.endRuntime_block_8122_taken_stack,
          endFreeGrabCallStack, endFreeGrabCallRest] using rd8155)
    have hrequire :
        ExecBlock config (endFreeAfterArtFrame I cur.rdata) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endFreeAfterArtFrame I cur.rdata) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_free_afterArt_true evm I cur.rdata hsrcCode))
        ExecBlock.nil
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endFreeGrabCallCursor cur.world I sel aw8122 cur.rdata)
          (k8155 + 2) (C8155 + 3)
          (endFreeAfterArtFrame I cur.rdata) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", sender, sender, vowAddr,
                .unary .neg (asInt256 (.var "ink")), .intLit 0] "_grab" ]
          (runtimeExit (.abi [])) :=
      endFreeGrabExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw8122)
        (outUrns := cur.rdata) (world := cur.world)
        (k := k8155 + 2) (C := C8155 + 3) (evm := evm)
        hperm hsz36 hout hink
    have hprogress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I)
          config (endFreeAfterArtFrame I cur.rdata) evm
          ([ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
            [ .externalCall (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", sender, sender, vowAddr,
                  .unary .neg (asInt256 (.var "ink")), .intLit 0] "_grab" ])
          (runtimeExit (.abi [])) :=
      BlockProgress.seqOfRD
        (R := fun cur _ e =>
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
        hrequire
        (by
          simpa [endFreeGrabCallCursor, endFreeGrabCallStack, endFreeGrabCallRest]
            using rd8157)
        (by simpa [endFreeGrabCallCursor] using hrel)
        htail
    simpa [checkedExternalCallStmts] using hprogress

theorem endFreeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 27))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1025⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 27 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some freeTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 27 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some freeTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (freeTransition.params.map Param.name) (transitionSignature freeTransition).paramTypes
        I.calldata = some (endFreeStore I) := by
      simpa [config, freeTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_ilk_ok (I := I) hsz36
    have hLiveWord :
        solcSlotWord σ_evm I ⟨8⟩ = solcSlotWord σ_solm I ⟨8⟩ :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hliveSolm : solcSlotWord σ_solm I ⟨8⟩ = ⟨0⟩
    · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ = ⟨0⟩ :=
        hLiveWord.trans hliveSolm
      have hliveSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨8⟩ = ⟨0⟩ := by
        rw [endPackStorageLoad_init_eq]
        exact hliveSolm
      have hCodeEq :
          extCodeSizeWord σ_evm (endPackVatTarget σ_evm I) =
            extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) :=
        endPackVatCodeSize_accountMapEquiv (I := I) hAccounts
      by_cases hvatNoCodeEvm :
          extCodeSizeWord σ_evm (endPackVatTarget σ_evm I) = ⟨0⟩
      · have hvatNoCodeSolm :
            extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) = ⟨0⟩ :=
          hCodeEq.symm.trans hvatNoCodeEvm
        have hvatNoCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨1⟩)
                solcAddrMask) = ⟨0⟩ := by
          rw [endPackVatTarget_init_eq]
          simpa [initState] using hvatNoCodeSolm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endFreeStore I) freeTransition.body .reverted := by
          simpa [initState] using
            endFreeBodyVatNoCode
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hliveSrc hvatNoCodeSrc
        exact (endX_free_vat_no_code (g := Sat256.ofUInt256 g)
            hsz36 hsize hliveEvm hvatNoCodeEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hvatCodeSolm :
            extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) ≠ ⟨0⟩ := by
          intro hzero
          exact hvatNoCodeEvm (hCodeEq.trans hzero)
        have hvatCodeSrc :
            extCodeSizeWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
              (UInt256.land
                (Solm.EVM.storageLoad
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                  ⟨1⟩)
                solcAddrMask) ≠ ⟨0⟩ := by
          rw [endPackVatTarget_init_eq]
          simpa [initState] using hvatCodeSolm
        obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
          endX_free_to_urns_call (g := Sat256.ofUInt256 g)
            hsz36 hsize hliveEvm hvatNoCodeEvm hreach
        have hprefix :
            ExecBlock config { contract := contract, locals := endFreeStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (nonpayable ++
                [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
              (.ok { contract := contract, locals := endFreeStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
          endFreeBodyPrefixOk
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hliveSrc hvatCodeSrc
        have hpostRel :
            CallStateRel
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
              (cA, σ_evm)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
          CallStateRel.initState hAccounts
        have hguardsThenGrab :
            StmtsRefine endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) config ⟨7885⟩
              (fun cur frame e =>
                frame = endFreeAfterUrnsFrame I cur.rdata ∧
                CallStateRel
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  I cur.world e ∧
                cur.rdata.size < UInt256.size ∧
                64 ≤ cur.rdata.size ∧
                cur.stack =
                  [UInt256.ofNat cur.rdata.size, ⟨128⟩, ⟨0⟩, ⟨0⟩,
                    endArg0Word I, ⟨562⟩, sel] ∧
                cur.mem = endFreeUrnsReturnMem I cur.rdata ∧
                cur.aw = endFreeAfterUrnsAw awCall)
              (endFreePostUrnsGuardStmts ++
                checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                  [.var "ilk", sender, sender, vowAddr,
                    .unary .neg (asInt256 (.var "ink")), .intLit 0]
                  "_grab")
              (runtimeExit (.abi [])) := by
          intro cur k C frame evm hpc rd hP
          exact BlockProgress.seqOrExit
            (endFreePostUrnsGuardsRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) cur k C frame evm hpc rd hP)
            (endFreeGrabCheckedCallRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) hperm hsz36)
        have htail :
            BlockRefinesFrom endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) config
              (endFreeUrnsCallCursor cA σ_evm I sel awCall ByteArray.empty)
              kCall CCall { contract := contract, locals := endFreeStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (fun cur _ e =>
                CallStateRel
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  I cur.world e)
              ([ .externalCall (.storage vatRef) "urns" (.intLit 0)
                  [.var "ilk", sender] "vatUrn" ] ++
                (endFreePostUrnsGuardStmts ++
                  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                    [.var "ilk", sender, sender, vowAddr,
                      .unary .neg (asInt256 (.var "ink")), .intLit 0]
                    "_grab"))
              (runtimeExit (.abi [])) := by
          refine BlockRefinesFrom.seqOrExit
            (endFreeUrnsExternalCallRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) (rdata := ByteArray.empty) (k := kCall) (C := CCall)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              hperm hsz36) ?_
          exact hguardsThenGrab
        have hprogress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endFreeStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ((nonpayable ++
                [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]) ++
                ([ .externalCall (.storage vatRef) "urns" (.intLit 0)
                    [.var "ilk", sender] "vatUrn" ] ++
                  (endFreePostUrnsGuardStmts ++
                    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
                      [.var "ilk", sender, sender, vowAddr,
                        .unary .neg (asInt256 (.var "ink")), .intLit 0]
                      "_grab")))
              (runtimeExit (.abi [])) :=
          BlockProgress.seqOfRD
            (R := fun cur _ e =>
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I cur.world e)
            hprefix
            (by simpa [endFreeUrnsCallCursor] using rdCall)
            hpostRel
            htail
        have hprogressBody :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endFreeStore I }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              freeTransition.body (runtimeExit (.abi [])) := by
          simpa [freeTransition, checkedExternalCallStmts, endFreePostUrnsGuardStmts,
            List.append_assoc] using hprogress
        simpa [Sat256.ofUInt256, Sat256.toUInt256] using
          (hprogressBody.toRuntimeEquivalenceFor hcode
            (convention := .abi [])
            (by
              intro result hfunc
              exact solmExec.intro hdispatchSel rfl hdec
                (by simp [initState, Sat256.ofUInt256, Sat256.toUInt256]) hfunc)
            (by
              intro result endpoint h
              exact h))
    · have hliveEvm : solcSlotWord σ_evm I ⟨8⟩ ≠ ⟨0⟩ := by
        intro hbad
        exact hliveSolm (hLiveWord.symm.trans hbad)
      have hliveSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨8⟩ ≠ ⟨0⟩ := by
        rw [endPackStorageLoad_init_eq]
        exact hliveSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endFreeStore I) freeTransition.body .reverted := by
        simpa [initState] using
          endFreeBodyLiveFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hliveSrc
      exact (endX_free_live_fail (g := Sat256.ofUInt256 g)
          hsz36 hsize hliveEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (freeTransition.params.map Param.name) (transitionSignature freeTransition).paramTypes
        I.calldata = none := by
      simpa [config, freeTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_ilk_none_short (I := I) hsz4 hshort
    exact (endX_free_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
