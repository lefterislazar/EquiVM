import Benchmarks.Dss.End.Free
import Benchmarks.Dss.End.Arithmetic
import Benchmarks.Dss.End.RuntimeBlocks_006
import Benchmarks.Dss.End.RuntimeBlocks_007
import Benchmarks.Dss.End.RuntimeBlocks_014
import Benchmarks.Dss.End.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `flow(bytes32)` -/

abbrev endFlowStore (I : ExecutionEnv) : Store :=
  endFreeStore I

abbrev endFlowDebtWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩

abbrev endFlowDebtWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ ⟨11⟩

abbrev endFlowFixSlot (I : ExecutionEnv) : UInt256 :=
  fixSlot (endArg0Bytes32Key I)

abbrev endFlowFixWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 15) (endArg0Word I)

abbrev endFlowFixWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endFlowFixSlot I)

abbrev endFlowFixWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endFlowFixWorldSlot I)

abbrev endFlowArtWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 14) (endArg0Word I)

abbrev endFlowTagWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 12) (endArg0Word I)

abbrev endFlowGapWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 13) (endArg0Word I)

abbrev endFlowArtWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ArtSlot (endArg0Bytes32Key I))

abbrev endFlowTagWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tagSlot (endArg0Bytes32Key I))

abbrev endFlowGapWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (gapSlot (endArg0Bytes32Key I))

abbrev endFlowArtWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endFlowArtWorldSlot I)

abbrev endFlowTagWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endFlowTagWorldSlot I)

abbrev endFlowGapWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endFlowGapWorldSlot I)

theorem endFlowStore_get_debt_none (I : ExecutionEnv) :
    (endFlowStore I).get? "debt" = none := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).get? "debt") = none
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "debt")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalDebt_flow (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage debtRef) =
      .ok (endUIntValue (endFlowDebtWord evm)) := by
  have her : evalStorageRef config { contract := contract, locals := endFlowStore I } evm
      debtRef = .ok { base := "debt", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "debt", steps := [] } : EvaledStorageRef)
      = some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (slot := debtRef)
    (er := { base := "debt", steps := [] })
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := endFlowStore_get_debt_none I)
    (her := her)
    (hty := hty)
    (hloc := endConfig_storage_debt),
    endRuntimeStorageLocLoad_uint256]

theorem endEvalDebtGuard_flow_false (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : endFlowDebtWord evm = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalDebt_flow evm I, hdebt]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endEvalDebtGuard_flow_true (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : endFlowDebtWord evm ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalDebt_flow evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : ¬ (endFlowDebtWord evm).toNat = 0 := by
    intro hzero
    exact hdebt (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endFlowStore_get_fix_none (I : ExecutionEnv) :
    (endFlowStore I).get? "fix" = none := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).get? "fix") = none
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "fix")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endEvalFix_flow (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
        (.storage (fixRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowFixWord evm I)) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [evalExpr_storage_scalar
    (er := { base := "fix", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (fixSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := endFlowStore_get_fix_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, fixRef,
        endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen,
        endFreeStore_getElem_ilk])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_fix (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endFlowFixWord, endFlowFixSlot]

theorem endEvalFixEqGuard_flow_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfix : endFlowFixWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFix_flow evm I hsz36]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : ¬ (endFlowFixWord evm I).toNat = 0 := by
    intro hzero
    exact hfix (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endEvalFixEqGuard_flow_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfix : endFlowFixWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endFlowStore I } evm
      (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFix_flow evm I hsz36, hfix]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endFlowBodyDebtFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdebt : endFlowDebtWord evm = ⟨0⟩) :
    ExecTransitionBody config contract evm (endFlowStore I)
      flowTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalDebtGuard_flow_false evm I hdebt)))

theorem endFlowBodyFixFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord evm ≠ ⟨0⟩)
    (hfix : endFlowFixWord evm I ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (endFlowStore I)
      flowTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtGuard_flow_true evm I hdebt)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalFixEqGuard_flow_false evm I hsz36 hfix)))

theorem endFlowBodyVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord evm ≠ ⟨0⟩)
    (hfix : endFlowFixWord evm I = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endFlowStore I)
      flowTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [flowTransition, checkedExternalCallStmts, nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtGuard_flow_true evm I hdebt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalFixEqGuard_flow_true evm I hsz36 hfix)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_free_false evm I hvatNoCode)))

theorem endFlowBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdebt : endFlowDebtWord evm ≠ ⟨0⟩)
    (hfix : endFlowFixWord evm I = ⟨0⟩)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endFlowStore I } evm
      (nonpayable ++
        [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
          .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endFlowStore I } evm) := by
  simpa [nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtGuard_flow_true evm I hdebt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalFixEqGuard_flow_true evm I hsz36 hfix)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_free_true evm I hvatCode)) <|
      ExecBlock.nil)

abbrev endFlowVatIlksSelectorWord : UInt256 := UInt256.ofNat 3647180086

def endFlowVatIlksPayloadBytes (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endArg0Word I)

def endFlowVatIlksEncodedCall (I : ExecutionEnv) : ByteArray :=
  ilksSelector ++ ⟨(endFlowVatIlksPayloadBytes I).toArray⟩

theorem endEncodeABIValues_vatIlks (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    encodeABIValues? [bytes32] [endArg0Bytes32Value I] =
      some (endFlowVatIlksPayloadBytes I) := by
  have hhead : abiTupleHeadSize? [bytes32] = some 32 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I hsz36, hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp [endFlowVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

theorem endEncodeCallWithSelector_vatIlks (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    ABI.encodeCallWithSelector? ilksSelector [bytes32] [endArg0Bytes32Value I] =
      some (endFlowVatIlksEncodedCall I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_vatIlks I hsz36]
  simp [endFlowVatIlksEncodedCall, endFlowVatIlksPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_vatIlks_branch (args : List Value) :
    config.externalABI.encode? "vatIlks" args =
      ABI.encodeCallWithSelector? ilksSelector [bytes32] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "vatIlks" = "cage")]
  rw [if_pos (by decide : "vatIlks" = "vatIlks")]
  rfl

theorem endExternalEncode_vatIlks (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "vatIlks" [endArg0Bytes32Value I] =
      some (endFlowVatIlksEncodedCall I) := by
  rw [endExternalEncode_vatIlks_branch]
  exact endEncodeCallWithSelector_vatIlks I hsz36

abbrev endFlowVatIlksWord0 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord (out.toList.take 32)

abbrev endFlowVatIlksRateWord (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 32).take 32)

abbrev endFlowVatIlksWord2 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 64).take 32)

abbrev endFlowVatIlksWord3 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 96).take 32)

abbrev endFlowVatIlksWord4 (out : ByteArray) : UInt256 :=
  ABI.bytesToWord ((out.toList.drop 128).take 32)

abbrev endFlowVatIlksValues (out : ByteArray) : List Value :=
  [endUIntValue (endFlowVatIlksWord0 out),
    endUIntValue (endFlowVatIlksRateWord out),
    endUIntValue (endFlowVatIlksWord2 out),
    endUIntValue (endFlowVatIlksWord3 out),
    endUIntValue (endFlowVatIlksWord4 out)]

theorem endDecodeScalarWordsWithMode_legacy_uint256x5_ok {out : ByteArray}
    (h160 : 160 ≤ out.size) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out.toList 0 =
      some (endFlowVatIlksValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake128 : ((out.toList.drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  simp only [decodeScalarWordsWithMode?]
  have hdec0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (endUIntValue (endFlowVatIlksWord0 out), 0 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord0, endUIntValue,
      List.drop_zero] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0)
  rw [hdec0]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
        some (endUIntValue (endFlowVatIlksRateWord out), 32 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksRateWord, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32)
  rw [hdec32]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
        some (endUIntValue (endFlowVatIlksWord2 out), 64 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord2, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64)
  rw [hdec64]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
        some (endUIntValue (endFlowVatIlksWord3 out), 96 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord3, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 96) htake96)
  rw [hdec96]
  simp only [Option.bind, bind, Nat.reduceAdd]
  have hdec128 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
        some (endUIntValue (endFlowVatIlksWord4 out), 128 + 32) := by
    simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord4, endUIntValue] using
      (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 128) htake128)
  rw [hdec128]

theorem endDecodeScalarWordsWithMode_legacy_uint256x5_none_short {out : ByteArray}
    (hshort : out.size < 160) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out.toList 0 = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : ((out.toList.drop 0).take 32).length = 32
  · have hdec0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          some (endUIntValue (endFlowVatIlksWord0 out), 0 + 32) := by
      simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord0, endUIntValue,
        List.drop_zero] using
        (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) h0)
    rw [hdec0]
    simp only [Option.bind, bind, Nat.reduceAdd]
    by_cases h32 : ((out.toList.drop 32).take 32).length = 32
    · have hdec32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (endUIntValue (endFlowVatIlksRateWord out), 32 + 32) := by
        simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksRateWord,
          endUIntValue] using
          (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) h32)
      rw [hdec32]
      simp only [Option.bind, bind]
      by_cases h64 : ((out.toList.drop 64).take 32).length = 32
      · have hdec64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              some (endUIntValue (endFlowVatIlksWord2 out), 64 + 32) := by
          simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord2,
            endUIntValue] using
            (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) h64)
        rw [hdec64]
        simp only [Option.bind, bind, Nat.reduceAdd]
        by_cases h96 : ((out.toList.drop 96).take 32).length = 32
        · have hdec96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
                some (endUIntValue (endFlowVatIlksWord3 out), 96 + 32) := by
            simpa [uint256, uint256Int, abiUInt256, endFlowVatIlksWord3,
              endUIntValue] using
              (decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 96) h96)
          rw [hdec96]
          simp only [Option.bind, bind, Nat.reduceAdd]
          have h128 : ¬ ((out.toList.drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hnone128 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
                none := by
            simpa [uint256, uint256Int, abiUInt256] using
              (decodeScalarWordWithMode_uint256_none_short
                (mode := DecodeMode.legacySolc05) (bytes := out.toList)
                (start := 128) h128)
          rw [hnone128]
        · have hnone96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
                none := by
            simpa [uint256, uint256Int, abiUInt256] using
              (decodeScalarWordWithMode_uint256_none_short
                (mode := DecodeMode.legacySolc05) (bytes := out.toList)
                (start := 96) h96)
          rw [hnone96]
      · have hnone64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              none := by
          simpa [uint256, uint256Int, abiUInt256] using
            (decodeScalarWordWithMode_uint256_none_short
              (mode := DecodeMode.legacySolc05) (bytes := out.toList)
              (start := 64) h64)
        rw [hnone64]
    · have hnone32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            none := by
        simpa [uint256, uint256Int, abiUInt256] using
          (decodeScalarWordWithMode_uint256_none_short
            (mode := DecodeMode.legacySolc05) (bytes := out.toList)
            (start := 32) h32)
      rw [hnone32]
  · have hnone0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
          none := by
      simpa [uint256, uint256Int, abiUInt256] using
        (decodeScalarWordWithMode_uint256_none_short
          (mode := DecodeMode.legacySolc05) (bytes := out.toList) (start := 0) h0)
    rw [hnone0]
    rfl

theorem endDecodeReturnValues_legacy_uint256x5_ok {out : ByteArray}
    (h160 : 160 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out =
      some (endFlowVatIlksValues out) := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, uint256, uint256] =
      some 160 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 160)
    (by decide) (by decide)]
  rw [endDecodeScalarWordsWithMode_legacy_uint256x5_ok h160]

theorem endDecodeReturnValues_legacy_uint256x5_none_short {out : ByteArray}
    (hshort : out.size < 160) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
        [uint256, uint256, uint256, uint256, uint256] out = none := by
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [uint256, uint256, uint256, uint256, uint256] =
      some 160 by native_decide]
  simp only [Option.bind, bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256])
    (bytes := out.toList) (cursor := 0) (total := 160)
    (by decide) (by decide)]
  rw [endDecodeScalarWordsWithMode_legacy_uint256x5_none_short hshort]

theorem endExternalDecode_vatIlks_ok {out : ByteArray} (h160 : 160 ≤ out.size) :
    config.externalABI.decode? "vatIlks" out = some (endFlowVatIlksValues out) := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "vatIlks" = "cage")]
  rw [if_pos (by decide : "vatIlks" = "vatIlks")]
  exact endDecodeReturnValues_legacy_uint256x5_ok h160

theorem endExternalDecode_vatIlks_none_short {out : ByteArray} (hshort : out.size < 160) :
    config.externalABI.decode? "vatIlks" out = none := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "vatIlks" = "cage")]
  rw [if_pos (by decide : "vatIlks" = "vatIlks")]
  exact endDecodeReturnValues_legacy_uint256x5_none_short hshort

abbrev endFlowVatIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_2786_taken_memory
    (mem := solcFreePtrMem) (x0 := endArg0Word I)

abbrev endFlowVatIlksCallMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_2883_taken_memory
    (mem := endFlowVatIlksBaseMem I) (x0 := endArg0Word I)

abbrev endFlowVatIlksSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)

abbrev endFlowVatIlksMemSel (I : ExecutionEnv) : ByteArray :=
  endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
    (endFlowVatIlksBaseMem I) 128 32

abbrev endFlowVatIlksMemFull (I : ExecutionEnv) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endFlowVatIlksMemSel I) 132 32

theorem endFlowVatIlksBaseMem_eq_hashMem (I : ExecutionEnv) :
    endFlowVatIlksBaseMem I =
      twoWordHashMem (endArg0Word I) (UInt256.ofNat 15) solcFreePtrMem := by
  unfold endFlowVatIlksBaseMem twoWordHashMem wordAt0Mem wordAt32Mem
  dsimp [endRuntimeBlocks.endRuntime_block_2786_taken_memory]
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem endFlowVatIlksBaseMem_size (I : ExecutionEnv) :
    (endFlowVatIlksBaseMem I).size = 96 := by
  rw [endFlowVatIlksBaseMem_eq_hashMem I]
  exact twoWordHashMem_size_96 (endArg0Word I) (UInt256.ofNat 15) solcFreePtrMem_size

theorem endFlowVatIlksBaseMem_read64 (I : ExecutionEnv) :
    (endFlowVatIlksBaseMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endFlowVatIlksBaseMem_eq_hashMem I]
  exact twoWordHashMem_read64 (endArg0Word I) (UInt256.ofNat 15)
    solcFreePtrMem_size solcFreePtrMem_read64

theorem endFlowVatIlksBaseMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endFlowVatIlksBaseMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endFlowVatIlksBaseMem I)
    (by rw [endFlowVatIlksBaseMem_size I]; omega)
    (endFlowVatIlksBaseMem_read64 I)

theorem endFlowVatIlksCallMem_eq_full (I : ExecutionEnv) :
    endFlowVatIlksCallMem I = endFlowVatIlksMemFull I := by
  unfold endFlowVatIlksCallMem endFlowVatIlksMemFull endFlowVatIlksMemSel
    endFlowVatIlksSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_2883_taken_memory]
  rw [endFlowVatIlksBaseMem_mload64 I]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]

theorem endFlowVatIlksMemSel_size_ge160 (I : ExecutionEnv) :
    160 ≤ (endFlowVatIlksMemSel I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endFlowVatIlksSelectorEncodedWord (endFlowVatIlksBaseMem I) 128

theorem endFlowVatIlksCallMem_size_ge164 (I : ExecutionEnv) :
    164 ≤ (endFlowVatIlksCallMem I).size := by
  rw [endFlowVatIlksCallMem_eq_full I]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endArg0Word I) (endFlowVatIlksMemSel I) 132

theorem endFlowVatIlksMemSel_size (I : ExecutionEnv) :
    (endFlowVatIlksMemSel I).size = 160 := by
  unfold endFlowVatIlksMemSel
  exact toByteArray_write32_size_of_ge (endFlowVatIlksBaseMem I)
    endFlowVatIlksSelectorEncodedWord 128 96 160
    (endFlowVatIlksBaseMem_size I) (by omega) (by native_decide) rfl

theorem endFlowVatIlksCallMem_size (I : ExecutionEnv) :
    (endFlowVatIlksCallMem I).size = 164 := by
  rw [endFlowVatIlksCallMem_eq_full I]
  unfold endFlowVatIlksMemFull
  exact toByteArray_write32_size_of_le (endFlowVatIlksMemSel I)
    (endArg0Word I) 132 160 164
    (endFlowVatIlksMemSel_size I)
    (by rw [endFlowVatIlksMemSel_size I]; omega)
    (by omega)

theorem endFlowVatIlksSelectorEncodedWord_prefix :
    (endFlowVatIlksSelectorEncodedWord.toByteArray).extract 0 4 = ilksSelector := by
  native_decide

theorem endFlowVatIlksCallMem_read64 (I : ExecutionEnv) :
    (endFlowVatIlksCallMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endFlowVatIlksCallMem_eq_full I]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endArg0Word I) (endFlowVatIlksMemSel I) 132 64
    (by have := endFlowVatIlksMemSel_size_ge160 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endFlowVatIlksBaseMem I) 128 64
    (by rw [endFlowVatIlksBaseMem_size I]) (by omega)]
  exact endFlowVatIlksBaseMem_read64 I

theorem endFlowVatIlksCallMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endFlowVatIlksCallMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endFlowVatIlksCallMem I)
    (by have := endFlowVatIlksCallMem_size_ge164 I; omega)
    (endFlowVatIlksCallMem_read64 I)

abbrev endFlowVatIlksReturnMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (endFlowVatIlksCallMem I) 128
    (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat

theorem endFlowVatIlksReturnMem_size (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endFlowVatIlksReturnMem I out).size = 288 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endFlowVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endFlowVatIlksCallMem I) 128 160
    (by decide) h160
    (by rw [endFlowVatIlksCallMem_size I]; omega)
    (by rw [endFlowVatIlksCallMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endFlowVatIlksCallMem_size I]
  omega

theorem endFlowVatIlksReturnMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I out) = ⟨128⟩ := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  have hread :
      (endFlowVatIlksReturnMem I out).readWithPadding 64 32 =
        (endFlowVatIlksCallMem I).readWithPadding 64 32 := by
    unfold endFlowVatIlksReturnMem
    rw [hcopy]
    exact write_read_below_gen_extend out (endFlowVatIlksCallMem I) 128 160 64
      (by decide) h160
      (by rw [endFlowVatIlksCallMem_size I]; omega)
      (by omega)
  have hbase := endFlowVatIlksCallMem_mload64 I
  unfold memLoad at hbase ⊢
  rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide] at hbase ⊢
  rw [if_neg (by
    rw [endFlowVatIlksReturnMem_size I out hout h160]
    omega)]
  rw [hread]
  rw [if_neg (by
    rw [endFlowVatIlksCallMem_size I]
    omega)] at hbase
  exact hbase

theorem endFlowVatIlksReturnMem_read160 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    (endFlowVatIlksReturnMem I out).readWithPadding 160 32 =
      out.extract 32 64 := by
  have hcopy :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 160 := by
    rw [callCopyLength_toNat out (⟨160⟩ : UInt256) hout]
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by native_decide]
    exact Nat.min_eq_left h160
  unfold endFlowVatIlksReturnMem
  rw [hcopy]
  rw [write_eq_gen_extend out (endFlowVatIlksCallMem I) 128 160
    (by decide) h160
    (by rw [endFlowVatIlksCallMem_size I]; omega)
    (by rw [endFlowVatIlksCallMem_size I]; omega)]
  have hpre : ((endFlowVatIlksCallMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endFlowVatIlksCallMem_size I]
    omega
  have hcopySize : (out.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract _ 160 (by
    rw [ByteArray.size_append, hpre, hcopySize]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by
    rw [hpre]
    omega), hpre]
  rw [show 160 - 128 = 32 by omega, show 160 + 32 - 128 = 64 by omega]
  rw [extract_extract_BA]
  rw [show 0 + 32 = 32 by omega, show min (0 + 64) 160 = 64 by omega]

theorem endFlowVatIlksReturnMem_mload160 (I : ExecutionEnv) (out : ByteArray)
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size) :
    memLoad (UInt256.ofNat 160) (endFlowVatIlksReturnMem I out) =
      endFlowVatIlksRateWord out := by
  unfold memLoad
  rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide]
  rw [if_neg (by
    rw [endFlowVatIlksReturnMem_size I out hout h160]
    omega)]
  rw [endFlowVatIlksReturnMem_read160 I out hout h160]
  change UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64)) =
    ABI.bytesToWord ((out.toList.drop 32).take 32)
  rw [← bytesToWord_drop32_take32_eq_extract32_64]

theorem endFlowVatIlksCallMem_readSelector (I : ExecutionEnv) :
    (endFlowVatIlksCallMem I).readWithPadding 128 4 = ilksSelector := by
  rw [endFlowVatIlksCallMem_eq_full I]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endFlowVatIlksMemSel_size_ge160 I; omega) (by omega)
    (by have := endFlowVatIlksMemSel_size_ge160 I; omega) (by decide) (by decide)]
  change ((endFlowVatIlksSelectorEncodedWord.toByteArray.write 0
      (endFlowVatIlksBaseMem I) 128 32).readWithPadding 128 4) = ilksSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endFlowVatIlksSelectorEncodedWord (endFlowVatIlksBaseMem I) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endFlowVatIlksSelectorEncodedWord_prefix]

theorem endFlowVatIlksCallMem_readIlk (I : ExecutionEnv) :
    (endFlowVatIlksCallMem I).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endFlowVatIlksCallMem_eq_full I]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endArg0Word I) (endFlowVatIlksMemSel I) 132

theorem endFlowVatIlksCallMem_readCallData (I : ExecutionEnv) :
    (endFlowVatIlksCallMem I).readWithPadding 128 36 =
      endFlowVatIlksEncodedCall I := by
  have hsize := endFlowVatIlksCallMem_size_ge164 I
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endFlowVatIlksCallMem I) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endFlowVatIlksCallMem_readSelector I, endFlowVatIlksCallMem_readIlk I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endFlowVatIlksEncodedCall, endFlowVatIlksPayloadBytes, toByteArray_eq_toBytesBE]

theorem endEvalFlowVatIlksArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endFlowStore I } evm
      [.var "ilk"] = .ok [endArg0Bytes32Value I] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endFlowStore, endFreeStore_get_ilk]

abbrev endFlowVatIlksCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I, ⟨0⟩,
    endArg0Word I, ⟨562⟩, sel]

abbrev endFlowVatIlksCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨160⟩] ++
    endFlowVatIlksCallRest σ I sel

abbrev endFlowVatIlksCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨2962⟩, stack := endFlowVatIlksCallStack σ I sel,
    mem := endFlowVatIlksCallMem I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endFlowVatIlksCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat)

abbrev endFlowAfterVatIlksAw (aw : UInt256) : UInt256 :=
  M (endFlowVatIlksCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endFlowAfterVatIlksFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowStore I).insert "vatIlk" (collapseReturns (endFlowVatIlksValues out)) }

abbrev endFlowAfterRateFrame (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterVatIlksFrame I out).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord out)) }

abbrev endFlowWad0Word (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  endGenericRmulResult (endFlowArtWord evm I) (endFlowVatIlksRateWord out)

abbrev endFlowWad0WorldWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  endGenericRmulResult (endFlowArtWorldWord σ I) (endFlowVatIlksRateWord out)

abbrev endFlowAfterWad0Frame (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterRateFrame I out).locals.insert "wad0"
      (endUIntValue (endFlowWad0Word evm I out)) }

abbrev endFlowWadWord (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  endGenericRmulResult (endFlowWad0Word evm I out) (endFlowTagWord evm I)

abbrev endFlowWadWorldWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  endGenericRmulResult (endFlowWad0WorldWord σ I out) (endFlowTagWorldWord σ I)

abbrev endFlowAfterWadFrame (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterWad0Frame evm I out).locals.insert "wad"
      (endUIntValue (endFlowWadWord evm I out)) }

abbrev endFlowNum0Word (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.sub (endFlowWadWord evm I out) (endFlowGapWord evm I)

abbrev endFlowNum0WorldWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.sub (endFlowWadWorldWord σ I out) (endFlowGapWorldWord σ I)

abbrev endFlowAfterNum0Frame (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterWadFrame evm I out).locals.insert "num0"
      (endUIntValue (endFlowNum0Word evm I out)) }

abbrev endFlowNumWord (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.mul (endFlowNum0Word evm I out) endRayWord

abbrev endFlowNumWorldWord (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.mul (endFlowNum0WorldWord σ I out) endRayWord

abbrev endFlowAfterNumFrame (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterNum0Frame evm I out).locals.insert "num"
      (endUIntValue (endFlowNumWord evm I out)) }

abbrev endFlowDenWord (evm : EVM.State) : UInt256 :=
  UInt256.div (endFlowDebtWord evm) endRayWord

abbrev endFlowDenWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (endFlowDebtWorldWord σ I) endRayWord

abbrev endFlowAfterDenFrame (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterNumFrame evm I out).locals.insert "den"
      (endUIntValue (endFlowDenWord evm)) }

abbrev endFlowFixValueWord (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : UInt256 :=
  UInt256.div (endFlowNumWord evm I out) (endFlowDenWord evm)

abbrev endFlowFixValueWorldWord (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : UInt256 :=
  UInt256.div (endFlowNumWorldWord σ I out) (endFlowDenWorldWord σ I)

abbrev endFlowAfterFixVFrame (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : Frame :=
  { contract := contract,
    locals := (endFlowAfterDenFrame evm I out).locals.insert "fixV"
      (endUIntValue (endFlowFixValueWord evm I out)) }

abbrev endFlowFinalState (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endFlowFixSlot I)
    (endFlowFixValueWord evm I out)

theorem endFlowStore_get_ilk (I : ExecutionEnv) :
    (endFlowStore I).get? "ilk" = some (endArg0Bytes32Value I) := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).get? "ilk") =
    some (endArg0Bytes32Value I)
  exact store_get_self (∅ : Store) "ilk" (endArg0Bytes32Value I)

theorem endFlowAfterVatIlksFrame_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (endFlowAfterVatIlksFrame I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "vatIlk") (a := "ilk")
    (collapseReturns (endFlowVatIlksValues out)) (by decide)]
  exact store_get_self (∅ : Store) "ilk" (endArg0Bytes32Value I)

theorem endFlowAfterRateFrame_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (endFlowAfterRateFrame I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues out))).insert "rate"
      (endUIntValue (endFlowVatIlksRateWord out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues out))) (k := "rate") (a := "ilk")
      (endUIntValue (endFlowVatIlksRateWord out)) (by decide)]
  exact endFlowAfterVatIlksFrame_get_ilk I out

theorem endFlowAfterWad0Frame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterWad0Frame evm I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endFlowAfterRateFrame I out).locals.insert "wad0"
      (endUIntValue (endFlowWad0Word evm I out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endFlowAfterRateFrame I out).locals (k := "wad0")
    (a := "ilk") (endUIntValue (endFlowWad0Word evm I out)) (by decide)]
  exact endFlowAfterRateFrame_get_ilk I out

theorem endFlowAfterWadFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterWadFrame evm I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endFlowAfterWad0Frame evm I out).locals.insert "wad"
      (endUIntValue (endFlowWadWord evm I out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endFlowAfterWad0Frame evm I out).locals (k := "wad")
    (a := "ilk") (endUIntValue (endFlowWadWord evm I out)) (by decide)]
  exact endFlowAfterWad0Frame_get_ilk evm I out

theorem endFlowAfterNum0Frame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterNum0Frame evm I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endFlowAfterWadFrame evm I out).locals.insert "num0"
      (endUIntValue (endFlowNum0Word evm I out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endFlowAfterWadFrame evm I out).locals (k := "num0")
    (a := "ilk") (endUIntValue (endFlowNum0Word evm I out)) (by decide)]
  exact endFlowAfterWadFrame_get_ilk evm I out

theorem endFlowAfterNumFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterNumFrame evm I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endFlowAfterNum0Frame evm I out).locals.insert "num"
      (endUIntValue (endFlowNumWord evm I out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endFlowAfterNum0Frame evm I out).locals (k := "num")
    (a := "ilk") (endUIntValue (endFlowNumWord evm I out)) (by decide)]
  exact endFlowAfterNum0Frame_get_ilk evm I out

theorem endFlowAfterDenFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterDenFrame evm I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endFlowAfterNumFrame evm I out).locals.insert "den"
      (endUIntValue (endFlowDenWord evm))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endFlowAfterNumFrame evm I out).locals (k := "den")
    (a := "ilk") (endUIntValue (endFlowDenWord evm)) (by decide)]
  exact endFlowAfterNumFrame_get_ilk evm I out

theorem endFlowAfterFixVFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterFixVFrame evm I out).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change ((endFlowAfterDenFrame evm I out).locals.insert "fixV"
      (endUIntValue (endFlowFixValueWord evm I out))).get? "ilk" =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endFlowAfterDenFrame evm I out).locals (k := "fixV")
    (a := "ilk") (endUIntValue (endFlowFixValueWord evm I out)) (by decide)]
  exact endFlowAfterDenFrame_get_ilk evm I out

theorem endFlowFrame_getElem_ilk {L : Store}
    (hget : L.get? "ilk" = some (endArg0Bytes32Value I)) (hmem : "ilk" ∈ L) :
    L["ilk"] = endArg0Bytes32Value I := by
  have hopt : L["ilk"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hget
  have hpos := getElem?_pos L "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endFlowArg0Drop32 (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    32 ≤ I.calldata.toList.length - 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  omega

theorem endEvalFlowRateFromVatIlk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFlowAfterVatIlksFrame I out) evm
      (.tupleGet (.var "vatIlk") 1) =
      .ok (endUIntValue (endFlowVatIlksRateWord out)) := by
  simp [evalExpr?, endFlowAfterVatIlksFrame, collapseReturns, tupleGetValue?,
    EvalResult.ofOption, EvalResult.bind, bind, endUIntValue]

theorem endEvalFlowArtAfterRate (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config (endFlowAfterRateFrame I out) evm
        (.storage (ArtRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowArtWord evm I)) := by
  have hdrop := endFlowArg0Drop32 I hsz36
  have hilk :
      ((Std.HashMap.insert (endFlowStore I) "vatIlk"
          (collapseReturns (endFlowVatIlksValues out))).insert "rate"
          (endUIntValue (endFlowVatIlksRateWord out)))["ilk"] =
        endArg0Bytes32Value I := by
    change (endFlowAfterRateFrame I out).locals["ilk"] = endArg0Bytes32Value I
    exact endFlowFrame_getElem_ilk (I := I) (endFlowAfterRateFrame_get_ilk I out) (by
      simp [endFlowAfterRateFrame, endFlowAfterVatIlksFrame, endFlowStore, endFreeStore,
        Std.HashMap.mem_insert])
  rw [evalExpr_storage_scalar
    (er := { base := "Art", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (ArtSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := by simp [endFlowAfterRateFrame, endFlowStore, endFreeStore, ArtRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, ArtRef, endArg0Bytes32Key,
        valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
        bytes32Width, hilk, hdrop])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_Art (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endFlowArtWord]

theorem endEvalFlowTagAfterWad0 (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config (endFlowAfterWad0Frame evm I out) evm
        (.storage (tagRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowTagWord evm I)) := by
  have hdrop := endFlowArg0Drop32 I hsz36
  have hilk :
      ((endFlowAfterRateFrame I out).locals.insert "wad0"
          (endUIntValue (endFlowWad0Word evm I out)))["ilk"] =
        endArg0Bytes32Value I := by
    change (endFlowAfterWad0Frame evm I out).locals["ilk"] = endArg0Bytes32Value I
    exact endFlowFrame_getElem_ilk (I := I) (endFlowAfterWad0Frame_get_ilk evm I out) (by
      simp [endFlowAfterWad0Frame, endFlowAfterRateFrame, endFlowAfterVatIlksFrame,
        endFlowStore, endFreeStore, Std.HashMap.mem_insert])
  rw [evalExpr_storage_scalar
    (er := { base := "tag", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (tagSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := by
      simp [endFlowAfterWad0Frame, endFlowAfterRateFrame, endFlowAfterVatIlksFrame,
        endFlowStore, endFreeStore, tagRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, tagRef, endArg0Bytes32Key,
        valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
        bytes32Width, hilk, hdrop])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_tag (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endFlowTagWord]

theorem endEvalFlowGapAfterWad (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config (endFlowAfterWadFrame evm I out) evm
        (.storage (gapRef (.var "ilk"))) =
      .ok (endUIntValue (endFlowGapWord evm I)) := by
  have hdrop := endFlowArg0Drop32 I hsz36
  have hilk :
      ((endFlowAfterWad0Frame evm I out).locals.insert "wad"
          (endUIntValue (endFlowWadWord evm I out)))["ilk"] =
        endArg0Bytes32Value I := by
    change (endFlowAfterWadFrame evm I out).locals["ilk"] = endArg0Bytes32Value I
    exact endFlowFrame_getElem_ilk (I := I) (endFlowAfterWadFrame_get_ilk evm I out) (by
      simp [endFlowAfterWadFrame, endFlowAfterWad0Frame, endFlowAfterRateFrame,
        endFlowAfterVatIlksFrame, endFlowStore, endFreeStore, Std.HashMap.mem_insert])
  rw [evalExpr_storage_scalar
    (er := { base := "gap", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (gapSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := by
      simp [endFlowAfterWadFrame, endFlowAfterWad0Frame, endFlowAfterRateFrame,
        endFlowAfterVatIlksFrame, endFlowStore, endFreeStore, gapRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, gapRef, endArg0Bytes32Key,
        valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
        bytes32Width, hilk, hdrop])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_gap (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endFlowGapWord]

theorem endEvalFlowDebtAfterNum (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFlowAfterNumFrame evm I out) evm (.storage debtRef) =
      .ok (endUIntValue (endFlowDebtWord evm)) := by
  have her : evalStorageRef config (endFlowAfterNumFrame evm I out) evm
      debtRef = .ok { base := "debt", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "debt", steps := [] } : EvaledStorageRef)
      = some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (slot := debtRef)
    (er := { base := "debt", steps := [] })
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := by
      simp [endFlowAfterNumFrame, endFlowAfterNum0Frame, endFlowAfterWadFrame,
        endFlowAfterWad0Frame, endFlowAfterRateFrame, endFlowAfterVatIlksFrame,
        endFlowStore, endFreeStore, debtRef])
    (her := her)
    (hty := hty)
    (hloc := endConfig_storage_debt),
    endRuntimeStorageLocLoad_uint256]

abbrev endGenericSubResult (x y : UInt256) : UInt256 :=
  UInt256.sub x y

abbrev endGenericSubZStore (x y : UInt256) : Store :=
  (endGenericMulStore x y).insert "z" (endUIntValue (endGenericSubResult x y))

theorem endGenericSubZStore_get_z (x y : UInt256) :
    (endGenericSubZStore x y).get? "z" =
      some (endUIntValue (endGenericSubResult x y)) := by
  exact store_get_self (endGenericMulStore x y) "z" (endUIntValue (endGenericSubResult x y))

theorem endGenericSubZStore_get_x (x y : UInt256) :
    (endGenericSubZStore x y).get? "x" = some (endUIntValue x) := by
  unfold endGenericSubZStore
  rw [store_get_ne (endGenericMulStore x y) (k := "z") (a := "x")
    (endUIntValue (endGenericSubResult x y)) (by decide)]
  exact endGenericMulStore_get_x x y

theorem endGenericSubZStore_get_y (x y : UInt256) :
    (endGenericSubZStore x y).get? "y" = some (endUIntValue y) := by
  unfold endGenericSubZStore
  rw [store_get_ne (endGenericMulStore x y) (k := "z") (a := "y")
    (endUIntValue (endGenericSubResult x y)) (by decide)]
  exact endGenericMulStore_get_y x y

theorem endEvalGenericSubExpr (evm : EVM.State) (x y : UInt256)
    (hle : y.toNat ≤ x.toNat) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (u256 (.binary .sub (.var "x") (.var "y"))) =
      .ok (endUIntValue (endGenericSubResult x y)) := by
  have hsub := usub_toNat (a := x) (b := y) hle
  have hdiffInt :
      Int.ofNat x.toNat - Int.ofNat y.toNat =
        Int.ofNat (x.toNat - y.toNat) := by
    exact (Int.ofNat_sub hle).symm
  have hnotHi :
      ¬ Int.ofNat (x.toNat - y.toNat) ≥ (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact lt_of_le_of_lt (Int.ofNat_le.mpr (Nat.sub_le x.toNat y.toNat))
      (by exact_mod_cast x.val.isLt)
  unfold u256
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int, endUIntValue]
  rw [hdiffInt]
  have hcond :
      (decide (Int.ofNat (x.toNat - y.toNat) < 0) ||
        decide (Int.ofNat (x.toNat - y.toNat) ≥ (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg : decide (Int.ofNat (x.toNat - y.toNat) < 0) = false :=
      decide_eq_false (show ¬ Int.ofNat (x.toNat - y.toNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat (x.toNat - y.toNat) ≥ (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [endGenericSubResult, hsub, endUIntValue]

theorem endEvalGenericSubExpr_revert (evm : EVM.State) (x y : UInt256)
    (hlt : x.toNat < y.toNat) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (u256 (.binary .sub (.var "x") (.var "y"))) =
      .revert := by
  have hneg :
      decide (Int.ofNat x.toNat - Int.ofNat y.toNat < 0) = true := by
    exact decide_eq_true (sub_neg_of_lt (Int.ofNat_lt.mpr hlt))
  unfold u256
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int, endUIntValue]
  rw [hneg]
  simp

theorem endEvalGenericSubGuard (evm : EVM.State) (x y : UInt256)
    (hle : y.toNat ≤ x.toNat) :
    evalExpr? config { contract := contract, locals := endGenericSubZStore x y } evm
      (.binary .le (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hsub := usub_toNat (a := x) (b := y) hle
  have hleNat : (endGenericSubResult x y).toNat ≤ x.toNat := by
    rw [endGenericSubResult, hsub]
    exact Nat.sub_le x.toNat y.toNat
  have hleInt :
      Int.ofNat (endGenericSubResult x y).toNat ≤ Int.ofNat x.toNat := by
    exact Int.ofNat_le.mpr hleNat
  simp only [evalExpr?, endGenericSubZStore_get_x, endGenericSubZStore_get_z,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  simp [hleNat, hleInt]

theorem endGenericSubFunctionOk (evm : EVM.State) (x y : UInt256)
    (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      subFunction.body
      (.returned { contract := contract, locals := endGenericSubZStore x y } evm
        (some [endUIntValue (endGenericSubResult x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [subFunction, endGenericSubZStore] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalGenericSubExpr evm x y hle)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalGenericSubGuard evm x y hle)) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.var "z"])
          (values := [endUIntValue (endGenericSubResult x y)])
          (by
            simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
              endGenericSubZStore_get_z])))

theorem endGenericSubFunctionRevert (evm : EVM.State) (x y : UInt256)
    (hlt : x.toNat < y.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      subFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [subFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalGenericSubExpr_revert evm x y hlt)))

theorem endFlowGenericMulSuccessCond (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) (hy : y ≠ ⟨0⟩) :
    UInt256.eq (UInt256.div (endGenericMulProduct x y) y) x ≠ ⟨0⟩ := by
  have hword : UInt256.div (endGenericMulProduct x y) y = x := by
    apply u256_inj
    rw [udiv_toNat, endGenericMulProduct_toNat x y hfit]
    have hyNat : 0 < y.toNat := by
      exact Nat.pos_of_ne_zero (by
        intro hzero
        exact hy (uint256_toNat_eq_zero hzero))
    have hdiv : (x.toNat * y.toNat) / y.toNat = x.toNat := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_right x.toNat hyNat
    exact hdiv
  rw [hword, uInt256_eq_self]
  decide

theorem endFlowGenericMulFailCond (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.eq (UInt256.div (endGenericMulProduct x y) y) x = UInt256.ofNat 0 := by
  exact u256_eq_of_ne (by
    simpa [endGenericMulProduct] using u256_mul_div_ne_of_overflow x y hover)

theorem endFlowSubSuccessCond (x y : UInt256) (hle : y.toNat ≤ x.toNat) :
    UInt256.isZero (UInt256.gt (UInt256.sub x y) x) ≠ UInt256.ofNat 0 := by
  have hsub := usub_toNat (a := x) (b := y) hle
  have hgt : UInt256.gt (UInt256.sub x y) x = ⟨0⟩ :=
    ugt_zero (by rw [hsub]; omega)
  rw [hgt]
  decide

theorem endFlowSubFailCond (x y : UInt256) (hlt : x.toNat < y.toNat) :
    UInt256.isZero (UInt256.gt (UInt256.sub x y) x) = UInt256.ofNat 0 := by
  have hsub := usub_toNat_underflow (a := x) (b := y) hlt
  have hylt : y.toNat < UInt256.size := y.val.isLt
  have hgt : UInt256.gt (UInt256.sub x y) x = ⟨1⟩ :=
    ugt_one (by rw [hsub]; omega)
  rw [hgt]
  decide

theorem endFlowAfterRateFrame_get_rate (I : ExecutionEnv) (out : ByteArray) :
    (endFlowAfterRateFrame I out).locals.get? "rate" =
      some (endUIntValue (endFlowVatIlksRateWord out)) := by
  exact store_get_self (endFlowAfterVatIlksFrame I out).locals "rate"
    (endUIntValue (endFlowVatIlksRateWord out))

theorem endFlowAfterWad0Frame_get_wad0 (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterWad0Frame evm I out).locals.get? "wad0" =
      some (endUIntValue (endFlowWad0Word evm I out)) := by
  exact store_get_self (endFlowAfterRateFrame I out).locals "wad0"
    (endUIntValue (endFlowWad0Word evm I out))

theorem endFlowAfterWadFrame_get_wad (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterWadFrame evm I out).locals.get? "wad" =
      some (endUIntValue (endFlowWadWord evm I out)) := by
  exact store_get_self (endFlowAfterWad0Frame evm I out).locals "wad"
    (endUIntValue (endFlowWadWord evm I out))

theorem endFlowAfterNum0Frame_get_num0 (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterNum0Frame evm I out).locals.get? "num0" =
      some (endUIntValue (endFlowNum0Word evm I out)) := by
  exact store_get_self (endFlowAfterWadFrame evm I out).locals "num0"
    (endUIntValue (endFlowNum0Word evm I out))

theorem endFlowAfterNumFrame_get_num (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterNumFrame evm I out).locals.get? "num" =
      some (endUIntValue (endFlowNumWord evm I out)) := by
  exact store_get_self (endFlowAfterNum0Frame evm I out).locals "num"
    (endUIntValue (endFlowNumWord evm I out))

theorem endFlowAfterDenFrame_get_num (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterDenFrame evm I out).locals.get? "num" =
      some (endUIntValue (endFlowNumWord evm I out)) := by
  change ((endFlowAfterNumFrame evm I out).locals.insert "den"
      (endUIntValue (endFlowDenWord evm))).get? "num" =
    some (endUIntValue (endFlowNumWord evm I out))
  rw [store_get_ne (endFlowAfterNumFrame evm I out).locals (k := "den")
    (a := "num") (endUIntValue (endFlowDenWord evm)) (by decide)]
  exact endFlowAfterNumFrame_get_num evm I out

theorem endFlowAfterDenFrame_get_den (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterDenFrame evm I out).locals.get? "den" =
      some (endUIntValue (endFlowDenWord evm)) := by
  exact store_get_self (endFlowAfterNumFrame evm I out).locals "den"
    (endUIntValue (endFlowDenWord evm))

theorem endEvalFlowNumAfterDen (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFlowAfterDenFrame evm I out) evm (.var "num") =
      .ok (endUIntValue (endFlowNumWord evm I out)) := by
  rw [evalExpr?]
  rw [endFlowAfterDenFrame_get_num]
  rfl

theorem endEvalFlowDenAfterDen (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFlowAfterDenFrame evm I out) evm (.var "den") =
      .ok (endUIntValue (endFlowDenWord evm)) := by
  rw [evalExpr?]
  rw [endFlowAfterDenFrame_get_den]
  rfl

theorem endFlowAfterFixVFrame_get_fixV (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterFixVFrame evm I out).locals.get? "fixV" =
      some (endUIntValue (endFlowFixValueWord evm I out)) := by
  exact store_get_self (endFlowAfterDenFrame evm I out).locals "fixV"
    (endUIntValue (endFlowFixValueWord evm I out))

theorem endEvalFlowRmulArtRateArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    evalExprs? config (endFlowAfterRateFrame I out) evm
      [.storage (ArtRef (.var "ilk")), .var "rate"] =
      .ok [endUIntValue (endFlowArtWord evm I),
        endUIntValue (endFlowVatIlksRateWord out)] := by
  rw [evalExprs?]
  rw [endEvalFlowArtAfterRate evm I out hsz36]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endFlowAfterRateFrame_get_rate I out]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_rmul_flow_art_rate (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    bindParams? rmulFunction.params
      [endUIntValue (endFlowArtWord evm I), endUIntValue (endFlowVatIlksRateWord out)] =
      some (endGenericMulStore (endFlowArtWord evm I) (endFlowVatIlksRateWord out)) := by
  simp [bindParams?, rmulFunction, endGenericMulStore, endUIntValue]

theorem endFlowInternalRmulArtRateOk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hfit : (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size) :
    ExecStmt config (endFlowAfterRateFrame I out) evm
      (.internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0")
      (.ok (endFlowAfterWad0Frame evm I out) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endFlowAfterWad0Frame,
    endFlowWad0Word] using
    internalCallFunctionReturn
      (cfg := config) (caller := endFlowAfterRateFrame I out)
      (evm := evm) (calleeEvm := evm) (name := "rmul") (retVar := "wad0")
      (args := [.storage (ArtRef (.var "ilk")), .var "rate"])
      (argVals := [endUIntValue (endFlowArtWord evm I),
        endUIntValue (endFlowVatIlksRateWord out)])
      (callee := rmulFunction)
      (locals := endGenericMulStore (endFlowArtWord evm I) (endFlowVatIlksRateWord out))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericRmulMStore (endFlowArtWord evm I) (endFlowVatIlksRateWord out) })
      (value := some [endUIntValue (endFlowWad0Word evm I out)])
      (endEvalFlowRmulArtRateArgs evm I out hsz36)
      (by
        change lookupCallable? contract "rmul" = some rmulFunction.toCallable
        rfl)
      (endBindParams_rmul_flow_art_rate evm I out)
      (by
        simpa [endFlowWad0Word] using
          endGenericRmulFunctionOk evm (endFlowArtWord evm I)
            (endFlowVatIlksRateWord out) hfit)

theorem endFlowInternalRmulArtRateRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat) :
    ExecStmt config (endFlowAfterRateFrame I out) evm
      (.internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endFlowAfterRateFrame I out) (evm := evm)
    (name := "rmul") (retVar := "wad0")
    (args := [.storage (ArtRef (.var "ilk")), .var "rate"])
    (argVals := [endUIntValue (endFlowArtWord evm I),
      endUIntValue (endFlowVatIlksRateWord out)])
    (callee := rmulFunction)
    (locals := endGenericMulStore (endFlowArtWord evm I) (endFlowVatIlksRateWord out))
    (endEvalFlowRmulArtRateArgs evm I out hsz36)
    (by
      change lookupCallable? contract "rmul" = some rmulFunction.toCallable
      rfl)
    (endBindParams_rmul_flow_art_rate evm I out)
    (endGenericRmulFunctionRevert evm (endFlowArtWord evm I)
      (endFlowVatIlksRateWord out) hover)

theorem endEvalFlowRmulWad0TagArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    evalExprs? config (endFlowAfterWad0Frame evm I out) evm
      [.var "wad0", .storage (tagRef (.var "ilk"))] =
      .ok [endUIntValue (endFlowWad0Word evm I out),
        endUIntValue (endFlowTagWord evm I)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endFlowAfterWad0Frame_get_wad0 evm I out]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalFlowTagAfterWad0 evm I out hsz36]
  simp [EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_rmul_flow_wad0_tag (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    bindParams? rmulFunction.params
      [endUIntValue (endFlowWad0Word evm I out), endUIntValue (endFlowTagWord evm I)] =
      some (endGenericMulStore (endFlowWad0Word evm I out) (endFlowTagWord evm I)) := by
  simp [bindParams?, rmulFunction, endGenericMulStore, endUIntValue]

theorem endFlowInternalRmulWad0TagOk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hfit : (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat < UInt256.size) :
    ExecStmt config (endFlowAfterWad0Frame evm I out) evm
      (.internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad")
      (.ok (endFlowAfterWadFrame evm I out) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endFlowAfterWadFrame,
    endFlowWadWord] using
    internalCallFunctionReturn
      (cfg := config) (caller := endFlowAfterWad0Frame evm I out)
      (evm := evm) (calleeEvm := evm) (name := "rmul") (retVar := "wad")
      (args := [.var "wad0", .storage (tagRef (.var "ilk"))])
      (argVals := [endUIntValue (endFlowWad0Word evm I out),
        endUIntValue (endFlowTagWord evm I)])
      (callee := rmulFunction)
      (locals := endGenericMulStore (endFlowWad0Word evm I out) (endFlowTagWord evm I))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericRmulMStore (endFlowWad0Word evm I out) (endFlowTagWord evm I) })
      (value := some [endUIntValue (endFlowWadWord evm I out)])
      (endEvalFlowRmulWad0TagArgs evm I out hsz36)
      (by
        change lookupCallable? contract "rmul" = some rmulFunction.toCallable
        rfl)
      (endBindParams_rmul_flow_wad0_tag evm I out)
      (by
        simpa [endFlowWadWord] using
          endGenericRmulFunctionOk evm (endFlowWad0Word evm I out)
            (endFlowTagWord evm I) hfit)

theorem endFlowInternalRmulWad0TagRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat) :
    ExecStmt config (endFlowAfterWad0Frame evm I out) evm
      (.internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endFlowAfterWad0Frame evm I out) (evm := evm)
    (name := "rmul") (retVar := "wad")
    (args := [.var "wad0", .storage (tagRef (.var "ilk"))])
    (argVals := [endUIntValue (endFlowWad0Word evm I out),
      endUIntValue (endFlowTagWord evm I)])
    (callee := rmulFunction)
    (locals := endGenericMulStore (endFlowWad0Word evm I out) (endFlowTagWord evm I))
    (endEvalFlowRmulWad0TagArgs evm I out hsz36)
    (by
      change lookupCallable? contract "rmul" = some rmulFunction.toCallable
      rfl)
    (endBindParams_rmul_flow_wad0_tag evm I out)
    (endGenericRmulFunctionRevert evm (endFlowWad0Word evm I out)
      (endFlowTagWord evm I) hover)

theorem endEvalFlowSubWadGapArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size) :
    evalExprs? config (endFlowAfterWadFrame evm I out) evm
      [.var "wad", .storage (gapRef (.var "ilk"))] =
      .ok [endUIntValue (endFlowWadWord evm I out),
        endUIntValue (endFlowGapWord evm I)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endFlowAfterWadFrame_get_wad evm I out]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalFlowGapAfterWad evm I out hsz36]
  simp [EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_sub_flow_wad_gap (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    bindParams? subFunction.params
      [endUIntValue (endFlowWadWord evm I out), endUIntValue (endFlowGapWord evm I)] =
      some (endGenericMulStore (endFlowWadWord evm I out) (endFlowGapWord evm I)) := by
  simp [bindParams?, subFunction, endGenericMulStore, endUIntValue]

theorem endFlowInternalSubWadGapOk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hle : (endFlowGapWord evm I).toNat ≤ (endFlowWadWord evm I out).toNat) :
    ExecStmt config (endFlowAfterWadFrame evm I out) evm
      (.internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0")
      (.ok (endFlowAfterNum0Frame evm I out) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endFlowAfterNum0Frame,
    endFlowNum0Word, endGenericSubResult] using
    internalCallFunctionReturn
      (cfg := config) (caller := endFlowAfterWadFrame evm I out)
      (evm := evm) (calleeEvm := evm) (name := "sub") (retVar := "num0")
      (args := [.var "wad", .storage (gapRef (.var "ilk"))])
      (argVals := [endUIntValue (endFlowWadWord evm I out),
        endUIntValue (endFlowGapWord evm I)])
      (callee := subFunction)
      (locals := endGenericMulStore (endFlowWadWord evm I out) (endFlowGapWord evm I))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericSubZStore (endFlowWadWord evm I out) (endFlowGapWord evm I) })
      (value := some [endUIntValue (endFlowNum0Word evm I out)])
      (endEvalFlowSubWadGapArgs evm I out hsz36)
      (by
        change lookupCallable? contract "sub" = some subFunction.toCallable
        rfl)
      (endBindParams_sub_flow_wad_gap evm I out)
      (by
        simpa [endFlowNum0Word, endGenericSubResult] using
          endGenericSubFunctionOk evm (endFlowWadWord evm I out)
            (endFlowGapWord evm I) hle)

theorem endFlowInternalSubWadGapRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hlt : (endFlowWadWord evm I out).toNat < (endFlowGapWord evm I).toNat) :
    ExecStmt config (endFlowAfterWadFrame evm I out) evm
      (.internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endFlowAfterWadFrame evm I out) (evm := evm)
    (name := "sub") (retVar := "num0")
    (args := [.var "wad", .storage (gapRef (.var "ilk"))])
    (argVals := [endUIntValue (endFlowWadWord evm I out),
      endUIntValue (endFlowGapWord evm I)])
    (callee := subFunction)
    (locals := endGenericMulStore (endFlowWadWord evm I out) (endFlowGapWord evm I))
    (endEvalFlowSubWadGapArgs evm I out hsz36)
    (by
      change lookupCallable? contract "sub" = some subFunction.toCallable
      rfl)
    (endBindParams_sub_flow_wad_gap evm I out)
    (endGenericSubFunctionRevert evm (endFlowWadWord evm I out)
      (endFlowGapWord evm I) hlt)

theorem endEvalFlowMulNum0RayArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExprs? config (endFlowAfterNum0Frame evm I out) evm
      [.var "num0", .intLit RAY] =
      .ok [endUIntValue (endFlowNum0Word evm I out), endUIntValue endRayWord] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endFlowAfterNum0Frame_get_num0 evm I out]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  simp [evalExpr?, EvalResult.bind, bind, pure, evalExprs?, endUIntValue,
    endRayWord_toNat, endRay_int_eq]

theorem endBindParams_mul_flow_num0_ray (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    bindParams? mulFunction.params
      [endUIntValue (endFlowNum0Word evm I out), endUIntValue endRayWord] =
      some (endGenericMulStore (endFlowNum0Word evm I out) endRayWord) := by
  simp [bindParams?, mulFunction, endGenericMulStore, endUIntValue]

theorem endFlowInternalMulNum0RayOk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hfit : (endFlowNum0Word evm I out).toNat * endRayNat < UInt256.size) :
    ExecStmt config (endFlowAfterNum0Frame evm I out) evm
      (.internalCall "mul" [.var "num0", .intLit RAY] "num")
      (.ok (endFlowAfterNumFrame evm I out) evm) := by
  have hfit' :
      (endFlowNum0Word evm I out).toNat * endRayWord.toNat < UInt256.size := by
    simpa [endRayWord_toNat] using hfit
  simpa [resumeAfterInternalCall, collapseReturns, endFlowAfterNumFrame,
    endFlowNumWord, endGenericMulProduct, endRayWord_toNat] using
    internalCallFunctionReturn
      (cfg := config) (caller := endFlowAfterNum0Frame evm I out)
      (evm := evm) (calleeEvm := evm) (name := "mul") (retVar := "num")
      (args := [.var "num0", .intLit RAY])
      (argVals := [endUIntValue (endFlowNum0Word evm I out), endUIntValue endRayWord])
      (callee := mulFunction)
      (locals := endGenericMulStore (endFlowNum0Word evm I out) endRayWord)
      (calleeSolm :=
        { contract := contract,
          locals := endGenericMulZStore (endFlowNum0Word evm I out) endRayWord })
      (value := some [endUIntValue (endFlowNumWord evm I out)])
      (endEvalFlowMulNum0RayArgs evm I out)
      (by
        change lookupCallable? contract "mul" = some mulFunction.toCallable
        rfl)
      (endBindParams_mul_flow_num0_ray evm I out)
      (by
        simpa [endFlowNumWord, endGenericMulProduct] using
          endGenericMulFunctionOk evm (endFlowNum0Word evm I out) endRayWord hfit')

theorem endFlowInternalMulNum0RayRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray)
    (hover : UInt256.size ≤ (endFlowNum0Word evm I out).toNat * endRayNat) :
    ExecStmt config (endFlowAfterNum0Frame evm I out) evm
      (.internalCall "mul" [.var "num0", .intLit RAY] "num") .reverted := by
  have hover' :
      UInt256.size ≤ (endFlowNum0Word evm I out).toNat * endRayWord.toNat := by
    simpa [endRayWord_toNat] using hover
  exact internalCallFunctionRevert
    (cfg := config) (caller := endFlowAfterNum0Frame evm I out) (evm := evm)
    (name := "mul") (retVar := "num")
    (args := [.var "num0", .intLit RAY])
    (argVals := [endUIntValue (endFlowNum0Word evm I out), endUIntValue endRayWord])
    (callee := mulFunction)
    (locals := endGenericMulStore (endFlowNum0Word evm I out) endRayWord)
    (endEvalFlowMulNum0RayArgs evm I out)
    (by
      change lookupCallable? contract "mul" = some mulFunction.toCallable
      rfl)
    (endBindParams_mul_flow_num0_ray evm I out)
    (endGenericMulFunctionRevert evm (endFlowNum0Word evm I out) endRayWord hover')

theorem endEvalFlowDen (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config (endFlowAfterNumFrame evm I out) evm
      (.binary .div (.storage debtRef) (.intLit RAY)) =
      .ok (endUIntValue (endFlowDenWord evm)) := by
  have hres :
      (endFlowDenWord evm).toNat = (endFlowDebtWord evm).toNat / endRayNat := by
    unfold endFlowDenWord
    rw [udiv_toNat, endRayWord_toNat]
  have hdiv :
      Int.ofNat (endFlowDebtWord evm).toNat / RAY =
        Int.ofNat (endFlowDenWord evm).toNat := by
    rw [endRay_int_eq, hres]
    change (((endFlowDebtWord evm).toNat : Nat) : Int) /
        ((endRayNat : Nat) : Int) =
      ((((endFlowDebtWord evm).toNat / endRayNat : Nat) : Int))
    rw [← Int.natCast_div]
  simp only [evalExpr?, endEvalFlowDebtAfterNum, EvalResult.bind, bind, pure,
    evalBinaryOp?, endUIntValue]
  rw [hdiv]
  have hrayNe : RAY ≠ 0 := by native_decide
  simp [hrayNe]

theorem endEvalFlowFixV (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hden : endFlowDenWord evm ≠ ⟨0⟩) :
    evalExpr? config (endFlowAfterDenFrame evm I out) evm
      (.binary .div (.var "num") (.var "den")) =
      .ok (endUIntValue (endFlowFixValueWord evm I out)) := by
  have hdenNatNe : (endFlowDenWord evm).toNat ≠ 0 := by
    intro hzero
    exact hden (uint256_toNat_eq_zero hzero)
  have hdenIntNe : Int.ofNat (endFlowDenWord evm).toNat ≠ 0 := by
    intro hzero
    exact hdenNatNe (Int.ofNat_eq_zero.mp hzero)
  have hres :
      (endFlowFixValueWord evm I out).toNat =
        (endFlowNumWord evm I out).toNat / (endFlowDenWord evm).toNat := by
    unfold endFlowFixValueWord
    rw [udiv_toNat]
  have hdiv :
      Int.ofNat (endFlowNumWord evm I out).toNat /
          Int.ofNat (endFlowDenWord evm).toNat =
        Int.ofNat (endFlowFixValueWord evm I out).toNat := by
    rw [hres]
    change (((endFlowNumWord evm I out).toNat : Nat) : Int) /
        (((endFlowDenWord evm).toNat : Nat) : Int) =
      ((((endFlowNumWord evm I out).toNat / (endFlowDenWord evm).toNat : Nat) : Int))
    rw [← Int.natCast_div]
  simp only [evalExpr?, endEvalFlowNumAfterDen, endEvalFlowDenAfterDen,
    EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  rw [hdiv]
  simp [hdenIntNe, hdenNatNe]

theorem endEvalFlowFixV_revert (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hden : endFlowDenWord evm = ⟨0⟩) :
    evalExpr? config (endFlowAfterDenFrame evm I out) evm
      (.binary .div (.var "num") (.var "den")) =
      .revert := by
  have hdenInt : Int.ofNat (endFlowDenWord evm).toNat = 0 := by
    rw [hden]
    decide
  have hdenNat : (endFlowDenWord evm).toNat = 0 := by
    rw [hden]
    decide
  simp only [evalExpr?, endEvalFlowNumAfterDen, endEvalFlowDenAfterDen,
    EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  simp [hdenInt, hdenNat]

theorem endEvalFlowFixVVar (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config (endFlowAfterFixVFrame evm I out) evm (.var "fixV") =
      .ok (endUIntValue (endFlowFixValueWord evm I out)) := by
  rw [evalExpr?]
  rw [endFlowAfterFixVFrame_get_fixV]
  rfl

theorem endEvalFlowIlkAfterFixV (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config (endFlowAfterFixVFrame evm I out) evm (.var "ilk") =
      .ok (endArg0Bytes32Value I) := by
  rw [evalExpr?]
  rw [endFlowAfterFixVFrame_get_ilk]
  rfl

theorem endFlowAfterFixVFrame_get_fix_none (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    (endFlowAfterFixVFrame evm I out).locals.get? "fix" = none := by
  change ((endFlowAfterDenFrame evm I out).locals.insert "fixV"
      (endUIntValue (endFlowFixValueWord evm I out))).get? "fix" = none
  rw [store_get_ne (endFlowAfterDenFrame evm I out).locals (k := "fixV")
    (a := "fix") (endUIntValue (endFlowFixValueWord evm I out)) (by decide)]
  change ((endFlowAfterNumFrame evm I out).locals.insert "den"
      (endUIntValue (endFlowDenWord evm))).get? "fix" = none
  rw [store_get_ne (endFlowAfterNumFrame evm I out).locals (k := "den")
    (a := "fix") (endUIntValue (endFlowDenWord evm)) (by decide)]
  change ((endFlowAfterNum0Frame evm I out).locals.insert "num"
      (endUIntValue (endFlowNumWord evm I out))).get? "fix" = none
  rw [store_get_ne (endFlowAfterNum0Frame evm I out).locals (k := "num")
    (a := "fix") (endUIntValue (endFlowNumWord evm I out)) (by decide)]
  change ((endFlowAfterWadFrame evm I out).locals.insert "num0"
      (endUIntValue (endFlowNum0Word evm I out))).get? "fix" = none
  rw [store_get_ne (endFlowAfterWadFrame evm I out).locals (k := "num0")
    (a := "fix") (endUIntValue (endFlowNum0Word evm I out)) (by decide)]
  change ((endFlowAfterWad0Frame evm I out).locals.insert "wad"
      (endUIntValue (endFlowWadWord evm I out))).get? "fix" = none
  rw [store_get_ne (endFlowAfterWad0Frame evm I out).locals (k := "wad")
    (a := "fix") (endUIntValue (endFlowWadWord evm I out)) (by decide)]
  change ((endFlowAfterRateFrame I out).locals.insert "wad0"
      (endUIntValue (endFlowWad0Word evm I out))).get? "fix" = none
  rw [store_get_ne (endFlowAfterRateFrame I out).locals (k := "wad0")
    (a := "fix") (endUIntValue (endFlowWad0Word evm I out)) (by decide)]
  change ((endFlowAfterVatIlksFrame I out).locals.insert "rate"
      (endUIntValue (endFlowVatIlksRateWord out))).get? "fix" = none
  rw [store_get_ne (endFlowAfterVatIlksFrame I out).locals (k := "rate")
    (a := "fix") (endUIntValue (endFlowVatIlksRateWord out)) (by decide)]
  change ((endFlowStore I).insert "vatIlk"
      (collapseReturns (endFlowVatIlksValues out))).get? "fix" = none
  rw [store_get_ne (endFlowStore I) (k := "vatIlk") (a := "fix")
    (collapseReturns (endFlowVatIlksValues out)) (by decide)]
  simp [endFlowStore, endFreeStore]

theorem endAssignFlowFix (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (henv : evm.executionEnv = I) (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config (endFlowAfterFixVFrame evm I out) evm
        .storage (fixRef (.var "ilk"))
        (endUIntValue (endFlowFixValueWord evm I out)) =
      .ok (endFlowAfterFixVFrame evm I out, endFlowFinalState evm I out) := by
  let er : EvaledStorageRef := { base := "fix", steps := [.mindex (endArg0Bytes32Key I)] }
  let loc : StorageLoc := wordLoc (fixSlot (endArg0Bytes32Key I))
  have hdrop := endFlowArg0Drop32 I hsz36
  have her : evalStorageRef config (endFlowAfterFixVFrame evm I out) evm
      (fixRef (.var "ilk")) = .ok er := by
    simp [er, evalStorageRef, evalStorageRefStep, fixRef, endArg0Bytes32Key,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
      endEvalFlowIlkAfterFixV, bytes32Width, hdrop]
  have hty :
      storageTypeAt? (endFlowAfterFixVFrame evm I out).contract.storage er =
        some (.elem (.int uint256Int)) := by
    simp [er, storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simpa [er, loc] using endConfig_storage_fix (endArg0Bytes32Key I)
  have hstore :
      storageLocStore evm loc (endUIntValue (endFlowFixValueWord evm I out)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (fixSlot (endArg0Bytes32Key I)) (endFlowFixValueWord evm I out)) := by
    simpa [loc, wordLoc, uint256Loc, endUIntValue] using
      storageLocStore_uint256 evm (fixSlot (endArg0Bytes32Key I))
        (endFlowFixValueWord evm I out)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endFlowAfterFixVFrame evm I out) (evm := evm)
    (slot := fixRef (.var "ilk")) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endFlowFixValueWord evm I out).toNat)
    (by
      exact endFlowAfterFixVFrame_get_fix_none evm I out)
    her hty hloc hstore
  have hstate :
      endFlowFinalState evm I out =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (fixSlot (endArg0Bytes32Key I)) (endFlowFixValueWord evm I out) := by
    rfl
  simpa [endUIntValue, hstate, loc] using hassign

theorem endFlowAfterVatIlksSuffixRmul1Revert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat) :
    ExecBlock config (endFlowAfterVatIlksFrame I out) evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (endEvalFlowRateFromVatIlk evm I out)) <|
    ExecBlock.consRevert
      (endFlowInternalRmulArtRateRevert evm I out hsz36 hover)

theorem endFlowAfterVatIlksSuffixRmul2Revert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hfit1 : (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hover2 : UInt256.size ≤ (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat) :
    ExecBlock config (endFlowAfterVatIlksFrame I out) evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (endEvalFlowRateFromVatIlk evm I out)) <|
    ExecBlock.consNormal
      (endFlowInternalRmulArtRateOk evm I out hsz36 hfit1) <|
    ExecBlock.consRevert
      (endFlowInternalRmulWad0TagRevert evm I out hsz36 hover2)

theorem endFlowAfterVatIlksSuffixSubRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hfit1 : (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat < UInt256.size)
    (hlt : (endFlowWadWord evm I out).toNat < (endFlowGapWord evm I).toNat) :
    ExecBlock config (endFlowAfterVatIlksFrame I out) evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (endEvalFlowRateFromVatIlk evm I out)) <|
    ExecBlock.consNormal
      (endFlowInternalRmulArtRateOk evm I out hsz36 hfit1) <|
    ExecBlock.consNormal
      (endFlowInternalRmulWad0TagOk evm I out hsz36 hfit2) <|
    ExecBlock.consRevert
      (endFlowInternalSubWadGapRevert evm I out hsz36 hlt)

theorem endFlowAfterVatIlksSuffixMulRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hfit1 : (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord evm I).toNat ≤ (endFlowWadWord evm I out).toNat)
    (hover3 : UInt256.size ≤ (endFlowNum0Word evm I out).toNat * endRayNat) :
    ExecBlock config (endFlowAfterVatIlksFrame I out) evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (endEvalFlowRateFromVatIlk evm I out)) <|
    ExecBlock.consNormal
      (endFlowInternalRmulArtRateOk evm I out hsz36 hfit1) <|
    ExecBlock.consNormal
      (endFlowInternalRmulWad0TagOk evm I out hsz36 hfit2) <|
    ExecBlock.consNormal
      (endFlowInternalSubWadGapOk evm I out hsz36 hleSub) <|
    ExecBlock.consRevert
      (endFlowInternalMulNum0RayRevert evm I out hover3)

theorem endFlowAfterVatIlksSuffixDenRevert (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (hsz36 : 36 ≤ I.calldata.size)
    (hfit1 : (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord evm I).toNat ≤ (endFlowWadWord evm I out).toNat)
    (hfit3 : (endFlowNum0Word evm I out).toNat * endRayNat < UInt256.size)
    (hden : endFlowDenWord evm = ⟨0⟩) :
    ExecBlock config (endFlowAfterVatIlksFrame I out) evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (endEvalFlowRateFromVatIlk evm I out)) <|
    ExecBlock.consNormal
      (endFlowInternalRmulArtRateOk evm I out hsz36 hfit1) <|
    ExecBlock.consNormal
      (endFlowInternalRmulWad0TagOk evm I out hsz36 hfit2) <|
    ExecBlock.consNormal
      (endFlowInternalSubWadGapOk evm I out hsz36 hleSub) <|
    ExecBlock.consNormal
      (endFlowInternalMulNum0RayOk evm I out hfit3) <|
    ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalFlowDen evm I out)) <|
    ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalFlowFixV_revert evm I out hden))

theorem endFlowAfterVatIlksSuffixOk (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (henv : evm.executionEnv = I)
    (hsz36 : 36 ≤ I.calldata.size)
    (hfit1 : (endFlowArtWord evm I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0Word evm I out).toNat *
        (endFlowTagWord evm I).toNat < UInt256.size)
    (hleSub : (endFlowGapWord evm I).toNat ≤ (endFlowWadWord evm I out).toNat)
    (hfit3 : (endFlowNum0Word evm I out).toNat * endRayNat < UInt256.size)
    (hden : endFlowDenWord evm ≠ ⟨0⟩) :
    ExecBlock config (endFlowAfterVatIlksFrame I out) evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      (.ok (endFlowAfterFixVFrame evm I out) (endFlowFinalState evm I out)) := by
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (endEvalFlowRateFromVatIlk evm I out)) <|
    ExecBlock.consNormal
      (endFlowInternalRmulArtRateOk evm I out hsz36 hfit1) <|
    ExecBlock.consNormal
      (endFlowInternalRmulWad0TagOk evm I out hsz36 hfit2) <|
    ExecBlock.consNormal
      (endFlowInternalSubWadGapOk evm I out hsz36 hleSub) <|
    ExecBlock.consNormal
      (endFlowInternalMulNum0RayOk evm I out hfit3) <|
    ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalFlowDen evm I out)) <|
    ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalFlowFixV evm I out hden)) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalFlowFixVVar evm I out)
        (endAssignFlowFix evm I out henv hsz36))
      ExecBlock.nil

abbrev endFlowAfterVatIlksCursor (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) :
    Cursor :=
  { pc := ⟨3002⟩,
    stack := [UInt256.ofNat out.size, memLoad (UInt256.ofNat 64)
        (endFlowVatIlksReturnMem I out), ⟨0⟩, endArg0Word I, ⟨562⟩, sel],
    mem := endFlowVatIlksReturnMem I out,
    aw := endFlowAfterVatIlksAw aw,
    rdata := out,
    world := world }

theorem endFlowFixSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowFixSlot I = endFlowFixWorldSlot I := by
  unfold endFlowFixSlot endFlowFixWorldSlot
  exact endFixSlot_eq I hsz36

theorem endFlowFixHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 15).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endFlowFixWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 15) mem) =
    endFlowFixWorldSlot I
  simp [endFlowFixWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endFlowArtHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 14).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endFlowArtWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 14) mem) =
    endFlowArtWorldSlot I
  simp [endFlowArtWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endFlowTagHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 12).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endFlowTagWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 12) mem) =
    endFlowTagWorldSlot I
  simp [endFlowTagWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endFlowGapHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 13).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endFlowGapWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 13) mem) =
    endFlowGapWorldSlot I
  simp [endFlowGapWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endFlowGapHashSlot_generated (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0)
        ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + (UInt256.ofNat 0)))
        ((UInt256.ofNat 13).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          ((UInt256.ofNat 32) + (UInt256.ofNat 0)).toNat 32)
      = endFlowGapWorldSlot I := by
  have hlen :
      (UInt256.ofNat 32) + ((UInt256.ofNat 32) + (UInt256.ofNat 0)) =
        (UInt256.ofNat 64) := by
    native_decide
  have hoff : ((UInt256.ofNat 32) + (UInt256.ofNat 0)).toNat = 32 := by
    native_decide
  rw [hlen, hoff]
  exact endFlowGapHashSlot mem I

theorem endX_flow_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd653 := endRuntimeBlocks.endRuntime_block_635_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_653
    (R := endRuntimeBlocks.endRuntime_block_635_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_635_fallthrough_stack])
    (by simpa using rd653)

theorem endX_flow_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2718⟩
      [endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd657 := endRuntimeBlocks.endRuntime_block_635_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd2718 := endRuntimeBlocks.endRuntime_block_657
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_635_taken_stack] using rd657)
  have hoff : (UInt256.ofNat 4).toNat = 4 := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_657_stack, endArg0Word, calldataWord, hoff]
      using rd2718⟩

theorem endX_flow_debt_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : endFlowDebtWorldWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_flow_to_body (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd2726⟩ := endRuntimeBlocks.endRuntime_block_2718_fallthrough
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hdebt rdBody
  exact endRuntimeBlocks.endRuntime_block_2726
    (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by simpa using rd2726)

theorem endX_flow_fix_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : endFlowDebtWorldWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWorldWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_flow_to_body (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd2786⟩ := endRuntimeBlocks.endRuntime_block_2718_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hdebt (by jump_dest) rdBody
  have hcondFix :
      UInt256.isZero
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 15).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) = UInt256.ofNat 0 := by
    rw [endFlowFixHashSlot solcFreePtrMem I]
    change UInt256.isZero (endFlowFixWorldWord σ I) = UInt256.ofNat 0
    exact Reasoning.Theory.isZero_eq_zero_of_ne hfix
  obtain ⟨_, _, rd2807⟩ := endRuntimeBlocks.endRuntime_block_2786_fallthrough
    (x0 := endArg0Word I) (R := [⟨562⟩, sel]) (by simp) hcondFix
    (by simpa using rd2786)
  exact endRuntimeBlocks.endRuntime_block_2807
    (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_2786_fallthrough_memory] using rd2807)

theorem endX_flow_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : endFlowDebtWorldWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWorldWord σ I = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_flow_to_body (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd2786⟩ := endRuntimeBlocks.endRuntime_block_2718_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hdebt (by jump_dest) rdBody
  have hcondFix :
      UInt256.isZero
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 15).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ UInt256.ofNat 0 := by
    rw [endFlowFixHashSlot solcFreePtrMem I]
    change UInt256.isZero (endFlowFixWorldWord σ I) ≠ UInt256.ofNat 0
    rw [hfix]
    native_decide
  obtain ⟨aw2883, k2883, C2883, rd2883⟩ :=
    endRuntimeBlocks.endRuntime_block_2786_taken_packed
      (x0 := endArg0Word I) (R := [⟨562⟩, sel]) (by simp) hcondFix
      (by jump_dest) (by simpa using rd2786)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondVat :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner σ (UInt256.ofNat 1))))) = UInt256.ofNat 0 := by
    rw [hmaskGenerated]
    change UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) =
      UInt256.ofNat 0
    rw [hvatNoCode]
    native_decide
  obtain ⟨_, _, _, rd2956⟩ :=
    endRuntimeBlocks.endRuntime_block_2883_fallthrough_packed
      (x0 := endArg0Word I) (R := [⟨562⟩, sel]) (by simp) hcondVat
      (by simpa [endRuntimeBlocks.endRuntime_block_2786_taken_memory] using rd2883)
  exact endRuntimeBlocks.endRuntime_block_2956
    (R := endRuntimeBlocks.endRuntime_block_2883_fallthrough_stack
      (mem := endRuntimeBlocks.endRuntime_block_2786_taken_memory
        (mem := solcFreePtrMem) (x0 := endArg0Word I))
      (σ := σ) (x0 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_2883_fallthrough_stack])
    rd2956

set_option maxHeartbeats 12000000 in
theorem endX_flow_to_vat_ilks_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : endFlowDebtWorldWord σ I ≠ ⟨0⟩)
    (hfix : endFlowFixWorldWord σ I = ⟨0⟩)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2962⟩
      (endFlowVatIlksCallStack σ I sel) (endFlowVatIlksCallMem I) aw ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_flow_to_body (g := g) hsz36 hsize hreach
  obtain ⟨_, _, rd2786⟩ := endRuntimeBlocks.endRuntime_block_2718_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hdebt (by jump_dest) rdBody
  have hcondFix :
      UInt256.isZero
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 15).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ UInt256.ofNat 0 := by
    rw [endFlowFixHashSlot solcFreePtrMem I]
    change UInt256.isZero (endFlowFixWorldWord σ I) ≠ UInt256.ofNat 0
    rw [hfix]
    native_decide
  obtain ⟨aw2883, k2883, C2883, rd2883⟩ :=
    endRuntimeBlocks.endRuntime_block_2786_taken_packed
      (x0 := endArg0Word I) (R := [⟨562⟩, sel]) (by simp) hcondFix
      (by jump_dest) (by simpa using rd2786)
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero
            (extCodeSizeWord σ
              (UInt256.land
                (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                  (UInt256.ofNat 1))
                (storageRead I.codeOwner σ (UInt256.ofNat 1))))) ≠ UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner σ (UInt256.ofNat 1))) ≠ UInt256.ofNat 0 := by
      rw [hmaskGenerated]
      simpa [endPackVatTarget] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw2960, k2960, C2960, rd2960⟩ :=
    endRuntimeBlocks.endRuntime_block_2883_taken_packed
      (mem := endFlowVatIlksBaseMem I) (x0 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) hcondCode
      (by jump_dest)
      (by simpa [endFlowVatIlksBaseMem] using rd2883)
  have hbase : memLoad (UInt256.ofNat 64) (endFlowVatIlksBaseMem I) = ⟨128⟩ :=
    endFlowVatIlksBaseMem_mload64 I
  have hcallRaw := endFlowVatIlksCallMem_mload64 I
  dsimp [endFlowVatIlksCallMem, endRuntimeBlocks.endRuntime_block_2883_taken_memory] at hcallRaw
  rw [hbase] at hcallRaw
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_2883_taken_stack (ee := I)
          (mem := endFlowVatIlksBaseMem I) (σ := σ) (x0 := endArg0Word I)
          (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endFlowVatIlksCallStack σ I sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_2883_taken_stack,
      endFlowVatIlksCallStack, endFlowVatIlksCallRest, endFlowVatIlksSelectorWord,
      endPackVatTarget]
    rw [hbase, hcallRaw, hlen, hend, hmaskGenerated]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide,
      show UInt256.ofNat 160 = (⟨160⟩ : UInt256) from by native_decide]
  have hmemTaken :
      endRuntimeBlocks.endRuntime_block_2883_taken_memory
          (mem := endFlowVatIlksBaseMem I) (x0 := endArg0Word I) =
        endFlowVatIlksCallMem I := by
    rfl
  have rd2960' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2960⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endFlowVatIlksCallStack σ I sel)
        (endFlowVatIlksCallMem I) aw2960 ByteArray.empty (cA, σ) k2960 C2960 := by
    rw [hstackTaken, hmemTaken] at rd2960
    exact rd2960
  have rd2962 := endRuntimeBlocks.endRuntime_block_2960
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := endFlowVatIlksCallStack σ I sel)
    (by simp [endFlowVatIlksCallStack, endFlowVatIlksCallRest])
    rd2960'
  exact ⟨aw2960, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_2960_stack] using rd2962⟩

set_option maxHeartbeats 12000000 in
theorem endFlowVatIlksExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endFlowVatIlksCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endFlowStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
      (sequenceExit ⟨3002⟩
        (fun cur frame e =>
          frame = endFlowAfterVatIlksFrame I cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          160 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I cur.rdata),
              ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
          cur.mem = endFlowVatIlksReturnMem I cur.rdata ∧
          cur.aw = endFlowAfterVatIlksAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨2962⟩ = some (.GAS, .none); decide)
    (by simp [endFlowVatIlksCallStack, endFlowVatIlksCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨2963⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endFlowVatIlksCallRest])
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
  · intro _
    exact endEvalFlowVatIlksArgs evm I
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_vatIlks I hsz36]
    change some (endFlowVatIlksEncodedCall I) =
      some ((endFlowVatIlksCallMem I).readWithPadding 128 36)
    rw [endFlowVatIlksCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h160 : 160 ≤ out.size
    · rw [endExternalDecode_vatIlks_ok h160]
      intro rd hrel
      have rd2964 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
            ((⟨1⟩ : UInt256) :: endFlowVatIlksCallRest σ I sel)
            (endFlowVatIlksReturnMem I out) (endFlowVatIlksCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endFlowVatIlksCallStack, endFlowVatIlksCallRest,
          endFlowVatIlksCallAw, endFlowVatIlksReturnMem] using rd
      have rd2980 := endRuntimeBlocks.endRuntime_block_2964_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endFlowVatIlksCallRest σ I sel)
        (by simp [endFlowVatIlksCallRest]) (by native_decide) (by jump_dest) rd2964
      have rd2980' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2980⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I,
              ⟨0⟩, endArg0Word I, ⟨562⟩, sel]
            (endFlowVatIlksReturnMem I out) (endFlowVatIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_2964_taken_stack,
          endFlowVatIlksCallRest] using rd2980
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide,
          ulit_toNat' out.size hout]
        exact h160
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd3002 := endRuntimeBlocks.endRuntime_block_2980_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨0⟩, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd2980'
      refine ⟨.ok (endFlowAfterVatIlksFrame I out) evm',
        Endpoint.reached (endFlowAfterVatIlksCursor I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endFlowAfterVatIlksCursor, endFlowAfterVatIlksAw,
            endRuntimeBlocks.endRuntime_block_2980_taken_stack] using rd3002⟩
      · exact ⟨rfl, rfl, hrel, hout, h160, rfl, rfl, rfl⟩
    · have hshort : out.size < 160 := by omega
      rw [endExternalDecode_vatIlks_none_short hshort]
      intro rd
      have rd2964 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
            ((⟨1⟩ : UInt256) :: endFlowVatIlksCallRest σ I sel)
            (endFlowVatIlksReturnMem I out) (endFlowVatIlksCallAw aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endFlowVatIlksCallStack, endFlowVatIlksCallRest,
          endFlowVatIlksCallAw, endFlowVatIlksReturnMem] using rd
      have rd2980 := endRuntimeBlocks.endRuntime_block_2964_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endFlowVatIlksCallRest σ I sel)
        (by simp [endFlowVatIlksCallRest]) (by native_decide) (by jump_dest) rd2964
      have rd2980' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2980⟩
            [⟨0⟩, ⟨164⟩, endFlowVatIlksSelectorWord, endPackVatTarget σ I,
              ⟨0⟩, endArg0Word I, ⟨562⟩, sel]
            (endFlowVatIlksReturnMem I out) (endFlowVatIlksCallAw aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_2964_taken_stack,
          endFlowVatIlksCallRest] using rd2980
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 160).toNat = 160 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 160)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd2998 := endRuntimeBlocks.endRuntime_block_2980_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endFlowVatIlksSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨0⟩, endArg0Word I, ⟨562⟩, sel])
        (by simp) hretcond rd2980'
      exact endRuntimeBlocks.endRuntime_block_2998
        (R := endRuntimeBlocks.endRuntime_block_2980_fallthrough_stack
          (mem := endFlowVatIlksReturnMem I out) (rdata := out)
          (R := [⟨0⟩, endArg0Word I, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_2980_fallthrough_stack])
        rd2998
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd2964 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2964⟩
          ((⟨0⟩ : UInt256) :: endFlowVatIlksCallRest σ I sel)
          (endFlowVatIlksReturnMem I out) (endFlowVatIlksCallAw aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endFlowVatIlksCallStack, endFlowVatIlksCallRest,
        endFlowVatIlksCallAw, endFlowVatIlksReturnMem] using rd
    have rd2971 := endRuntimeBlocks.endRuntime_block_2964_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endFlowVatIlksCallRest σ I sel)
      (by simp [endFlowVatIlksCallRest]) (by native_decide) rd2964
    exact endRuntimeBlocks.endRuntime_block_2971
      (R := endRuntimeBlocks.endRuntime_block_2964_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endFlowVatIlksCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_2964_fallthrough_stack,
        endFlowVatIlksCallRest])
      rd2971

theorem endX_flow_checkedMul_ok {ee g s0 mem aw rdata cA σ k C}
    {x y ret : UInt256} {R : List UInt256}
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hvalidRet : (D_J endBytecode 0).contains ret = true)
    (hstack : R.length + 9 ≤ 1024)
    (h : RD endBytecode ee g s0 ⟨10170⟩ (y :: x :: ret :: R) mem aw rdata
      (cA, σ) k C) :
    ∃ aw' k' C', RD endBytecode ee g s0 ret
      (endGenericMulProduct x y :: R) mem aw' rdata (cA, σ) k' C' := by
  by_cases hy : y = ⟨0⟩
  · have hcondY : UInt256.isZero y ≠ UInt256.ofNat 0 := by
      rw [hy]
      decide
    have rd10197 := endRuntimeBlocks.endRuntime_block_10170_taken
      (x0 := y) (R := x :: ret :: R)
      (by simp; omega) hcondY (by jump_dest) h
    have rd10108 := endRuntimeBlocks.endRuntime_block_10197_taken
      (x0 := UInt256.isZero y) (R := (⟨0⟩ : UInt256) :: y :: x :: ret :: R)
      (by simp; omega) hcondY (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10170_taken_stack] using rd10197)
    have rdRet := endRuntimeBlocks.endRuntime_block_10108
      (x0 := (⟨0⟩ : UInt256)) (x1 := y) (x2 := x) (x3 := ret) (R := R)
      (by simp; omega) hvalidRet
      (by simpa [endRuntimeBlocks.endRuntime_block_10197_taken_stack] using rd10108)
    have hprodZero : endGenericMulProduct x y = ⟨0⟩ := by
      apply u256_inj
      rw [endGenericMulProduct_toNat x y hfit, hy]
      simp
    exact ⟨_, _, _, by
      simpa [endRuntimeBlocks.endRuntime_block_10108_stack, hprodZero] using rdRet⟩
  · have hcondY : UInt256.isZero y = UInt256.ofNat 0 :=
      Reasoning.Theory.isZero_eq_zero_of_ne hy
    have rd10180 := endRuntimeBlocks.endRuntime_block_10170_fallthrough
      (x0 := y) (R := x :: ret :: R)
      (by simp; omega) hcondY h
    have rd10194 := endRuntimeBlocks.endRuntime_block_10180_taken
      (x0 := UInt256.isZero y) (x1 := (⟨0⟩ : UInt256))
      (x2 := y) (x3 := x) (R := ret :: R)
      (by simp; omega) hy (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10170_fallthrough_stack] using rd10180)
    have rd10197 := endRuntimeBlocks.endRuntime_block_10194
      (x0 := endGenericMulProduct x y) (x1 := y) (x2 := x)
      (R := endGenericMulProduct x y :: y :: x :: ret :: R)
      (by simp; omega)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10180_taken_stack,
          endGenericMulProduct] using rd10194)
    have hcondMul := endFlowGenericMulSuccessCond x y hfit hy
    have rd10108 := endRuntimeBlocks.endRuntime_block_10197_taken
      (x0 := UInt256.eq (UInt256.div (endGenericMulProduct x y) y) x)
      (R := endGenericMulProduct x y :: y :: x :: ret :: R)
      (by simp; omega) hcondMul (by jump_dest)
      (by simpa [endRuntimeBlocks.endRuntime_block_10194_stack] using rd10197)
    have rdRet := endRuntimeBlocks.endRuntime_block_10108
      (x0 := endGenericMulProduct x y) (x1 := y) (x2 := x) (x3 := ret)
      (R := R) (by simp; omega) hvalidRet
      (by simpa [endRuntimeBlocks.endRuntime_block_10197_taken_stack] using rd10108)
    exact ⟨_, _, _, by
      simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rdRet⟩

theorem endX_flow_checkedMul_fail {ee g s0 mem aw rdata cA σ k C}
    {x y ret : UInt256} {R : List UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (hstack : R.length + 9 ≤ 1024)
    (h : RD endBytecode ee g s0 ⟨10170⟩ (y :: x :: ret :: R) mem aw rdata
      (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hy : y ≠ ⟨0⟩ := by
    intro hy
    have hzero : x.toNat * y.toNat = 0 := by
      rw [hy]
      simp
    have hsizePos : 0 < UInt256.size := by native_decide
    omega
  have hcondY : UInt256.isZero y = UInt256.ofNat 0 :=
    Reasoning.Theory.isZero_eq_zero_of_ne hy
  have rd10180 := endRuntimeBlocks.endRuntime_block_10170_fallthrough
    (x0 := y) (R := x :: ret :: R)
    (by simp; omega) hcondY h
  have rd10194 := endRuntimeBlocks.endRuntime_block_10180_taken
    (x0 := UInt256.isZero y) (x1 := (⟨0⟩ : UInt256))
    (x2 := y) (x3 := x) (R := ret :: R)
    (by simp; omega) hy (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10170_fallthrough_stack] using rd10180)
  have rd10197 := endRuntimeBlocks.endRuntime_block_10194
    (x0 := endGenericMulProduct x y) (x1 := y) (x2 := x)
    (R := endGenericMulProduct x y :: y :: x :: ret :: R)
    (by simp; omega)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10180_taken_stack,
        endGenericMulProduct] using rd10194)
  have hcondMul := endFlowGenericMulFailCond x y hover
  have rd10202 := endRuntimeBlocks.endRuntime_block_10197_fallthrough
    (x0 := UInt256.eq (UInt256.div (endGenericMulProduct x y) y) x)
    (R := endGenericMulProduct x y :: y :: x :: ret :: R)
    (by simp; omega) hcondMul
    (by simpa [endRuntimeBlocks.endRuntime_block_10194_stack] using rd10197)
  exact endRuntimeBlocks.endRuntime_block_10202
    (R := endRuntimeBlocks.endRuntime_block_10197_fallthrough_stack
      (R := endGenericMulProduct x y :: y :: x :: ret :: R))
    (by simp [endRuntimeBlocks.endRuntime_block_10197_fallthrough_stack]; omega)
    rd10202

theorem endX_flow_rmul_ok {ee g s0 mem aw rdata cA σ k C}
    {x y ret : UInt256} {R : List UInt256}
    (hfit : x.toNat * y.toNat < UInt256.size)
    (hvalidRet : (D_J endBytecode 0).contains ret = true)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD endBytecode ee g s0 ⟨10114⟩ (y :: x :: ret :: R) mem aw rdata
      (cA, σ) k C) :
    ∃ aw' k' C', RD endBytecode ee g s0 ret
      (endGenericRmulResult x y :: R) mem aw' rdata (cA, σ) k' C' := by
  have rd10170 := endRuntimeBlocks.endRuntime_block_10114
    (x0 := y) (x1 := x) (R := ret :: R)
    (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, _, rd10139⟩ := endX_flow_checkedMul_ok
    (x := x) (y := y) (ret := (⟨10139⟩ : UInt256))
    (R := [endRayWord, ⟨0⟩, y, x, ret] ++ R)
    hfit (by jump_dest) (by simp; omega)
    (by simpa [endRuntimeBlocks.endRuntime_block_10114_stack, endRayWord] using rd10170)
  have hrayNe : endRayWord ≠ UInt256.ofNat 0 := by native_decide
  have rd10146 := endRuntimeBlocks.endRuntime_block_10139_taken
    (x0 := endGenericMulProduct x y) (x1 := endRayWord)
    (R := [⟨0⟩, y, x, ret] ++ R)
    (by simp; omega) hrayNe (by jump_dest)
    (by
      simpa [endGenericRmulResult, endGenericMulProduct] using rd10139)
  have rdRet := endRuntimeBlocks.endRuntime_block_10146
    (x0 := endGenericMulProduct x y) (x1 := endRayWord)
    (x2 := (⟨0⟩ : UInt256)) (x3 := y) (x4 := x) (x5 := ret) (R := R)
    (by simp; omega) hvalidRet
    (by simpa using rd10146)
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_10146_stack, endGenericRmulResult] using rdRet⟩

theorem endX_flow_rmul_fail {ee g s0 mem aw rdata cA σ k C}
    {x y ret : UInt256} {R : List UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD endBytecode ee g s0 ⟨10114⟩ (y :: x :: ret :: R) mem aw rdata
      (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd10170 := endRuntimeBlocks.endRuntime_block_10114
    (x0 := y) (x1 := x) (R := ret :: R)
    (by simp; omega) (by jump_dest) h
  exact endX_flow_checkedMul_fail
    (x := x) (y := y) (ret := (⟨10139⟩ : UInt256))
    (R := [endRayWord, ⟨0⟩, y, x, ret] ++ R)
    hover (by simp; omega)
    (by simpa [endRuntimeBlocks.endRuntime_block_10114_stack, endRayWord] using rd10170)

theorem endX_flow_sub_ok {ee g s0 mem aw rdata cA σ k C}
    {x y ret : UInt256} {R : List UInt256}
    (hle : y.toNat ≤ x.toNat)
    (hvalidRet : (D_J endBytecode 0).contains ret = true)
    (hstack : R.length + 6 ≤ 1024)
    (h : RD endBytecode ee g s0 ⟨10154⟩ (y :: x :: ret :: R) mem aw rdata
      (cA, σ) k C) :
    ∃ aw' k' C', RD endBytecode ee g s0 ret
      (UInt256.sub x y :: R) mem aw' rdata (cA, σ) k' C' := by
  have hcond := endFlowSubSuccessCond x y hle
  have rd10108 := endRuntimeBlocks.endRuntime_block_10154_taken
    (x0 := y) (x1 := x) (R := ret :: R)
    (by simp; omega) hcond (by jump_dest) h
  have rdRet := endRuntimeBlocks.endRuntime_block_10108
    (x0 := UInt256.sub x y) (x1 := y) (x2 := x) (x3 := ret) (R := R)
    (by simp; omega) hvalidRet
    (by simpa [endRuntimeBlocks.endRuntime_block_10154_taken_stack] using rd10108)
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rdRet⟩

theorem endX_flow_sub_fail {ee g s0 mem aw rdata cA σ k C}
    {x y ret : UInt256} {R : List UInt256}
    (hlt : x.toNat < y.toNat)
    (hstack : R.length + 6 ≤ 1024)
    (h : RD endBytecode ee g s0 ⟨10154⟩ (y :: x :: ret :: R) mem aw rdata
      (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hcond := endFlowSubFailCond x y hlt
  have rd10166 := endRuntimeBlocks.endRuntime_block_10154_fallthrough
    (x0 := y) (x1 := x) (R := ret :: R)
    (by simp; omega) hcond h
  exact endRuntimeBlocks.endRuntime_block_10166
    (R := endRuntimeBlocks.endRuntime_block_10154_fallthrough_stack
      (x0 := y) (x1 := x) (R := ret :: R))
    (by simp [endRuntimeBlocks.endRuntime_block_10154_fallthrough_stack]; omega)
    rd10166

abbrev endFlowArtHashMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_3002_memory
    (mem := endFlowVatIlksReturnMem I out) (x3 := endArg0Word I)

abbrev endFlowTagHashMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_3041_memory
    (mem := endFlowArtHashMem I out) (x4 := endArg0Word I)

abbrev endFlowGapHashMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_3086_memory
    (mem := endFlowTagHashMem I out) (x4 := endArg0Word I)

abbrev endFlowFixHashMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_3144_memory
    (mem := endFlowGapHashMem I out) (x4 := endArg0Word I)

abbrev endFlowFixStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (I : ExecutionEnv) (out : ByteArray) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 (endFlowFixWorldSlot I)
    (endFlowFixValueWorldWord world.2 I out))

theorem endX_flow_to_rmul1 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endFlowVatIlksRateWord out, endFlowArtWorldWord world.2 I,
        ⟨3041⟩, ⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out,
        endArg0Word I, ⟨562⟩, sel]
      (endFlowArtHashMem I out) aw' out world k' C' := by
  have hfree := endFlowVatIlksReturnMem_mload64 I out hout h160
  have hrate := endFlowVatIlksReturnMem_mload160 I out hout h160
  have hrateAddr :
      (UInt256.ofNat 32) +
          memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I out) =
        (⟨160⟩ : UInt256) := by
    rw [hfree]
    native_decide
  have hrate' :
      memLoad (⟨160⟩ : UInt256) (endFlowVatIlksReturnMem I out) =
        endFlowVatIlksRateWord out := by
    simpa using hrate
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endRuntimeBlocks.endRuntime_block_3002_packed
      (x0 := UInt256.ofNat out.size)
      (x1 := memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I out))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endFlowAfterVatIlksCursor] using rd)
  exact ⟨aw10114, k10114, C10114, by
    simpa [endRuntimeBlocks.endRuntime_block_3002_stack,
      endFlowArtHashMem, endFlowArtWorldWord, endFlowArtHashSlot, hrateAddr,
      hrate'] using rd10114⟩

theorem endX_flow_after_vat_ilks_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (hleSub : (endFlowGapWorldWord world.2 I).toNat ≤
        (endFlowWadWorldWord world.2 I out).toNat)
    (hfitMul : (endFlowNum0WorldWord world.2 I out).toNat * endRayNat <
        UInt256.size)
    (hden : endFlowDenWorldWord world.2 I ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (endFlowFixStoredWorld world I out) ByteArray.empty := by
  have hfree := endFlowVatIlksReturnMem_mload64 I out hout h160
  have hrate := endFlowVatIlksReturnMem_mload160 I out hout h160
  have hrateAddr :
      (UInt256.ofNat 32) +
          memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I out) =
        (⟨160⟩ : UInt256) := by
    rw [hfree]
    native_decide
  have hrate' :
      memLoad (⟨160⟩ : UInt256) (endFlowVatIlksReturnMem I out) =
        endFlowVatIlksRateWord out := by
    simpa using hrate
  obtain ⟨aw10114a, k10114a, C10114a, rd10114a⟩ :=
    endRuntimeBlocks.endRuntime_block_3002_packed
      (x0 := UInt256.ofNat out.size)
      (x1 := memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I out))
      (x2 := (⟨0⟩ : UInt256)) (x3 := endArg0Word I) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by simpa [endFlowAfterVatIlksCursor] using rd)
  have rd10114a' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
        [endFlowVatIlksRateWord out, endFlowArtWorldWord world.2 I,
          ⟨3041⟩, ⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out,
          endArg0Word I, ⟨562⟩, sel]
        (endFlowArtHashMem I out) aw10114a out world k10114a C10114a := by
    simpa [endRuntimeBlocks.endRuntime_block_3002_stack,
      endFlowArtHashMem, endFlowArtWorldWord, endFlowArtHashSlot, hrateAddr,
      hrate'] using rd10114a
  obtain ⟨aw3041, k3041, C3041, rd3041⟩ :=
    endX_flow_rmul_ok
      (x := endFlowArtWorldWord world.2 I)
      (y := endFlowVatIlksRateWord out)
      (ret := (⟨3041⟩ : UInt256))
      (R := [⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      hfit1 (by jump_dest) (by simp) rd10114a'
  obtain ⟨aw10114b, k10114b, C10114b, rd10114b⟩ :=
    endRuntimeBlocks.endRuntime_block_3041_packed
      (x0 := endFlowWad0WorldWord world.2 I out)
      (x1 := (⟨3061⟩ : UInt256)) (x2 := (⟨0⟩ : UInt256))
      (x3 := endFlowVatIlksRateWord out) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10146_stack,
          endFlowWad0WorldWord] using rd3041)
  have rd10114b' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
        [endFlowTagWorldWord world.2 I, endFlowWad0WorldWord world.2 I out,
          ⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel]
        (endFlowTagHashMem I out) aw10114b out world k10114b C10114b := by
    simpa [endRuntimeBlocks.endRuntime_block_3041_stack, endFlowTagHashMem,
      endFlowTagWorldWord, endFlowTagHashSlot] using rd10114b
  obtain ⟨aw3061, k3061, C3061, rd3061⟩ :=
    endX_flow_rmul_ok
      (x := endFlowWad0WorldWord world.2 I out)
      (y := endFlowTagWorldWord world.2 I)
      (ret := (⟨3061⟩ : UInt256))
      (R := [⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      hfit2 (by jump_dest) (by simp) rd10114b'
  have hrayNe : (UInt256.ofNat 1000000000000000000000000000) ≠ UInt256.ofNat 0 := by
    native_decide
  obtain ⟨aw3086, k3086, C3086, rd3086⟩ :=
    endRuntimeBlocks.endRuntime_block_3061_taken_packed
      (x0 := endFlowWadWorldWord world.2 I out) (x1 := (⟨0⟩ : UInt256))
      (R := [endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      (by simp) hrayNe (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10146_stack,
          endFlowWadWorldWord] using rd3061)
  have rd3086' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3086⟩
        [endFlowDebtWorldWord world.2 I, endRayWord,
          endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
          endArg0Word I, ⟨562⟩, sel]
        (endFlowTagHashMem I out) aw3086 out world k3086 C3086 := by
    simpa [endRuntimeBlocks.endRuntime_block_3061_taken_stack, endRayWord,
      endFlowDebtWorldWord] using rd3086
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endRuntimeBlocks.endRuntime_block_3086_packed
      (x0 := endFlowDebtWorldWord world.2 I) (x1 := endRayWord)
      (x2 := endFlowWadWorldWord world.2 I out)
      (x3 := endFlowVatIlksRateWord out) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd3086'
  have rd10154' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
        [endFlowGapWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
          ⟨3119⟩, ⟨3137⟩, endFlowDenWorldWord world.2 I,
          endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
          endArg0Word I, ⟨562⟩, sel]
        (endFlowGapHashMem I out) aw10154 out world k10154 C10154 := by
    simpa [endRuntimeBlocks.endRuntime_block_3086_stack, endFlowGapHashMem,
      endFlowGapWorldWord, endFlowGapHashSlot_generated, endFlowDenWorldWord,
      endRayWord] using rd10154
  obtain ⟨aw3119, k3119, C3119, rd3119⟩ :=
    endX_flow_sub_ok
      (x := endFlowWadWorldWord world.2 I out)
      (y := endFlowGapWorldWord world.2 I)
      (ret := (⟨3119⟩ : UInt256))
      (R := [⟨3137⟩, endFlowDenWorldWord world.2 I,
        endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
        endArg0Word I, ⟨562⟩, sel])
      hleSub (by jump_dest) (by simp) rd10154'
  have rd3119' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
        [endFlowNum0WorldWord world.2 I out, ⟨3137⟩,
          endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
          endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel]
        (endFlowGapHashMem I out) aw3119 out world k3119 C3119 := by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack,
      endFlowNum0WorldWord] using rd3119
  have hfitMul' :
      (endFlowNum0WorldWord world.2 I out).toNat * endRayWord.toNat <
        UInt256.size := by
    simpa [endRayWord_toNat] using hfitMul
  have rd10170 := endRuntimeBlocks.endRuntime_block_3119
    (R := [endFlowNum0WorldWord world.2 I out, ⟨3137⟩,
      endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
      endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest) rd3119'
  obtain ⟨aw3137, k3137, C3137, rd3137⟩ :=
    endX_flow_checkedMul_ok
      (x := endFlowNum0WorldWord world.2 I out) (y := endRayWord)
      (ret := (⟨3137⟩ : UInt256))
      (R := [endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
        endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      hfitMul' (by jump_dest) (by simp)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_3119_stack] using rd10170)
  have rd3137' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3137⟩
        [endFlowNumWorldWord world.2 I out, endFlowDenWorldWord world.2 I,
          endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
          endArg0Word I, ⟨562⟩, sel]
        (endFlowGapHashMem I out) aw3137 out world k3137 C3137 := by
    simpa [endFlowNumWorldWord, endRuntimeBlocks.endRuntime_block_10108_stack,
      endGenericMulProduct] using rd3137
  have rd3144 := endRuntimeBlocks.endRuntime_block_3137_taken
    (x0 := endFlowNumWorldWord world.2 I out)
    (x1 := endFlowDenWorldWord world.2 I)
    (R := [endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
      endArg0Word I, ⟨562⟩, sel])
    (by simp) hden (by jump_dest) rd3137'
  obtain ⟨aw562, k562, C562, rd562⟩ :=
    endRuntimeBlocks.endRuntime_block_3144_packed
      (x0 := endFlowNumWorldWord world.2 I out)
      (x1 := endFlowDenWorldWord world.2 I)
      (x2 := endFlowWadWorldWord world.2 I out)
      (x3 := endFlowVatIlksRateWord out) (x4 := endArg0Word I)
      (x5 := (⟨562⟩ : UInt256)) (R := [sel])
      (by simp) hperm (by jump_dest)
      (by simpa using rd3144)
  have rd562' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨562⟩ [sel]
        (endFlowFixHashMem I out) aw562 out (endFlowFixStoredWorld world I out)
        k562 C562 := by
    simpa [endFlowFixStoredWorld, endFlowFixHashMem,
      endRuntimeBlocks.endRuntime_block_3144_stack, endFlowFixHashSlot,
      endFlowFixValueWorldWord] using rd562
  exact endRuntimeBlocks.endRuntime_block_562
    (cA := (endFlowFixStoredWorld world I out).1)
    (σ := (endFlowFixStoredWorld world I out).2)
    (R := [sel]) (by simp) rd562'

theorem endX_flow_after_vat_ilks_rmul1_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hover1 : UInt256.size ≤ (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endX_flow_to_rmul1 (g := g) hout h160 rd
  exact endX_flow_rmul_fail
    (x := endFlowArtWorldWord world.2 I)
    (y := endFlowVatIlksRateWord out)
    (ret := (⟨3041⟩ : UInt256))
    (R := [⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
    hover1 (by simp) rd10114

theorem endX_flow_to_rmul2 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10114⟩
      [endFlowTagWorldWord world.2 I, endFlowWad0WorldWord world.2 I out,
        ⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel]
      (endFlowTagHashMem I out) aw' out world k' C' := by
  obtain ⟨aw10114a, k10114a, C10114a, rd10114a⟩ :=
    endX_flow_to_rmul1 (g := g) hout h160 rd
  obtain ⟨aw3041, k3041, C3041, rd3041⟩ :=
    endX_flow_rmul_ok
      (x := endFlowArtWorldWord world.2 I)
      (y := endFlowVatIlksRateWord out)
      (ret := (⟨3041⟩ : UInt256))
      (R := [⟨3061⟩, ⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      hfit1 (by jump_dest) (by simp) rd10114a
  obtain ⟨aw10114b, k10114b, C10114b, rd10114b⟩ :=
    endRuntimeBlocks.endRuntime_block_3041_packed
      (x0 := endFlowWad0WorldWord world.2 I out)
      (x1 := (⟨3061⟩ : UInt256)) (x2 := (⟨0⟩ : UInt256))
      (x3 := endFlowVatIlksRateWord out) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10146_stack,
          endFlowWad0WorldWord] using rd3041)
  exact ⟨aw10114b, k10114b, C10114b, by
    simpa [endRuntimeBlocks.endRuntime_block_3041_stack, endFlowTagHashMem,
      endFlowTagWorldWord, endFlowTagHashSlot] using rd10114b⟩

theorem endX_flow_after_vat_ilks_rmul2_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hover2 : UInt256.size ≤ (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10114, k10114, C10114, rd10114⟩ :=
    endX_flow_to_rmul2 (g := g) hout h160 hfit1 rd
  exact endX_flow_rmul_fail
    (x := endFlowWad0WorldWord world.2 I out)
    (y := endFlowTagWorldWord world.2 I)
    (ret := (⟨3061⟩ : UInt256))
    (R := [⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
    hover2 (by simp) rd10114

theorem endX_flow_to_sub {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
      [endFlowGapWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
        ⟨3119⟩, ⟨3137⟩, endFlowDenWorldWord world.2 I,
        endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
        endArg0Word I, ⟨562⟩, sel]
      (endFlowGapHashMem I out) aw' out world k' C' := by
  obtain ⟨aw10114b, k10114b, C10114b, rd10114b⟩ :=
    endX_flow_to_rmul2 (g := g) hout h160 hfit1 rd
  obtain ⟨aw3061, k3061, C3061, rd3061⟩ :=
    endX_flow_rmul_ok
      (x := endFlowWad0WorldWord world.2 I out)
      (y := endFlowTagWorldWord world.2 I)
      (ret := (⟨3061⟩ : UInt256))
      (R := [⟨0⟩, endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      hfit2 (by jump_dest) (by simp) rd10114b
  have hrayNe : (UInt256.ofNat 1000000000000000000000000000) ≠ UInt256.ofNat 0 := by
    native_decide
  obtain ⟨aw3086, k3086, C3086, rd3086⟩ :=
    endRuntimeBlocks.endRuntime_block_3061_taken_packed
      (x0 := endFlowWadWorldWord world.2 I out) (x1 := (⟨0⟩ : UInt256))
      (R := [endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      (by simp) hrayNe (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10146_stack,
          endFlowWadWorldWord] using rd3061)
  have rd3086' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3086⟩
        [endFlowDebtWorldWord world.2 I, endRayWord,
          endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
          endArg0Word I, ⟨562⟩, sel]
        (endFlowTagHashMem I out) aw3086 out world k3086 C3086 := by
    simpa [endRuntimeBlocks.endRuntime_block_3061_taken_stack, endRayWord,
      endFlowDebtWorldWord] using rd3086
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endRuntimeBlocks.endRuntime_block_3086_packed
      (x0 := endFlowDebtWorldWord world.2 I) (x1 := endRayWord)
      (x2 := endFlowWadWorldWord world.2 I out)
      (x3 := endFlowVatIlksRateWord out) (x4 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd3086'
  exact ⟨aw10154, k10154, C10154, by
    simpa [endRuntimeBlocks.endRuntime_block_3086_stack, endFlowGapHashMem,
      endFlowGapWorldWord, endFlowGapHashSlot_generated, endFlowDenWorldWord,
      endRayWord] using rd10154⟩

theorem endX_flow_after_vat_ilks_sub_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (hltSub : (endFlowWadWorldWord world.2 I out).toNat <
        (endFlowGapWorldWord world.2 I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endX_flow_to_sub (g := g) hout h160 hfit1 hfit2 rd
  exact endX_flow_sub_fail
    (x := endFlowWadWorldWord world.2 I out)
    (y := endFlowGapWorldWord world.2 I)
    (ret := (⟨3119⟩ : UInt256))
    (R := [⟨3137⟩, endFlowDenWorldWord world.2 I,
      endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
      endArg0Word I, ⟨562⟩, sel])
    hltSub (by simp) rd10154

theorem endX_flow_to_mul {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (hleSub : (endFlowGapWorldWord world.2 I).toNat ≤
        (endFlowWadWorldWord world.2 I out).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10170⟩
      [endRayWord, endFlowNum0WorldWord world.2 I out, ⟨3137⟩,
        endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
        endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel]
      (endFlowGapHashMem I out) aw' out world k' C' := by
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endX_flow_to_sub (g := g) hout h160 hfit1 hfit2 rd
  obtain ⟨aw3119, k3119, C3119, rd3119⟩ :=
    endX_flow_sub_ok
      (x := endFlowWadWorldWord world.2 I out)
      (y := endFlowGapWorldWord world.2 I)
      (ret := (⟨3119⟩ : UInt256))
      (R := [⟨3137⟩, endFlowDenWorldWord world.2 I,
        endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
        endArg0Word I, ⟨562⟩, sel])
      hleSub (by jump_dest) (by simp) rd10154
  have rd3119' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3119⟩
        [endFlowNum0WorldWord world.2 I out, ⟨3137⟩,
          endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
          endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel]
        (endFlowGapHashMem I out) aw3119 out world k3119 C3119 := by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack,
      endFlowNum0WorldWord] using rd3119
  have rd10170 := endRuntimeBlocks.endRuntime_block_3119
    (R := [endFlowNum0WorldWord world.2 I out, ⟨3137⟩,
      endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
      endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest) rd3119'
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_3119_stack] using rd10170⟩

theorem endX_flow_after_vat_ilks_mul_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (hleSub : (endFlowGapWorldWord world.2 I).toNat ≤
        (endFlowWadWorldWord world.2 I out).toNat)
    (hoverMul : UInt256.size ≤ (endFlowNum0WorldWord world.2 I out).toNat *
        endRayNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hoverMul' :
      UInt256.size ≤ (endFlowNum0WorldWord world.2 I out).toNat *
        endRayWord.toNat := by
    simpa [endRayWord_toNat] using hoverMul
  obtain ⟨aw10170, k10170, C10170, rd10170⟩ :=
    endX_flow_to_mul (g := g) hout h160 hfit1 hfit2 hleSub rd
  exact endX_flow_checkedMul_fail
    (x := endFlowNum0WorldWord world.2 I out) (y := endRayWord)
    (ret := (⟨3137⟩ : UInt256))
    (R := [endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
      endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
    hoverMul' (by simp)
    (by simpa using rd10170)

theorem endX_flow_to_dencheck {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (hleSub : (endFlowGapWorldWord world.2 I).toNat ≤
        (endFlowWadWorldWord world.2 I out).toNat)
    (hfitMul : (endFlowNum0WorldWord world.2 I out).toNat * endRayNat <
        UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3137⟩
      [endFlowNumWorldWord world.2 I out, endFlowDenWorldWord world.2 I,
        endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
        endArg0Word I, ⟨562⟩, sel]
      (endFlowGapHashMem I out) aw' out world k' C' := by
  have hfitMul' :
      (endFlowNum0WorldWord world.2 I out).toNat * endRayWord.toNat <
        UInt256.size := by
    simpa [endRayWord_toNat] using hfitMul
  obtain ⟨aw10170, k10170, C10170, rd10170⟩ :=
    endX_flow_to_mul (g := g) hout h160 hfit1 hfit2 hleSub rd
  obtain ⟨aw3137, k3137, C3137, rd3137⟩ :=
    endX_flow_checkedMul_ok
      (x := endFlowNum0WorldWord world.2 I out) (y := endRayWord)
      (ret := (⟨3137⟩ : UInt256))
      (R := [endFlowDenWorldWord world.2 I, endFlowWadWorldWord world.2 I out,
        endFlowVatIlksRateWord out, endArg0Word I, ⟨562⟩, sel])
      hfitMul' (by jump_dest) (by simp)
      (by simpa using rd10170)
  exact ⟨aw3137, k3137, C3137, by
    simpa [endFlowNumWorldWord, endRuntimeBlocks.endRuntime_block_10108_stack,
      endGenericMulProduct] using rd3137⟩

theorem endX_flow_after_vat_ilks_den_invalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw out k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hout : out.size < UInt256.size) (h160 : 160 ≤ out.size)
    (hfit1 : (endFlowArtWorldWord world.2 I).toNat *
        (endFlowVatIlksRateWord out).toNat < UInt256.size)
    (hfit2 : (endFlowWad0WorldWord world.2 I out).toNat *
        (endFlowTagWorldWord world.2 I).toNat < UInt256.size)
    (hleSub : (endFlowGapWorldWord world.2 I).toNat ≤
        (endFlowWadWorldWord world.2 I out).toNat)
    (hfitMul : (endFlowNum0WorldWord world.2 I out).toNat * endRayNat <
        UInt256.size)
    (hden : endFlowDenWorldWord world.2 I = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3002⟩
      (endFlowAfterVatIlksCursor I sel aw out world).stack
      (endFlowVatIlksReturnMem I out) (endFlowAfterVatIlksAw aw) out world k C) :
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw3137, k3137, C3137, rd3137⟩ :=
    endX_flow_to_dencheck (g := g) hout h160 hfit1 hfit2 hleSub hfitMul rd
  have rd3143 := endRuntimeBlocks.endRuntime_block_3137_fallthrough
    (x0 := endFlowNumWorldWord world.2 I out)
    (x1 := endFlowDenWorldWord world.2 I)
    (R := [endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
      endArg0Word I, ⟨562⟩, sel])
    (by simp) hden rd3137
  exact endRuntimeBlocks.endRuntime_block_3143
    (R := [endFlowNumWorldWord world.2 I out, endFlowDenWorldWord world.2 I,
      endFlowWadWorldWord world.2 I out, endFlowVatIlksRateWord out,
      endArg0Word I, ⟨562⟩, sel])
    rd3143

theorem endFlowDebtWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    endFlowDebtWord evm = endFlowDebtWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (UInt256.ofNat 11)
  unfold endFlowDebtWord endFlowDebtWorldWord
  exact hload

theorem endFlowFixWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowFixWord evm I = endFlowFixWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (endFlowFixSlot I)
  have hslot := endFlowFixSlot_eq I hsz36
  unfold endFlowFixWord endFlowFixWorldWord
  rw [hload, hslot]

theorem endFlowArtWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowArtWord evm I = endFlowArtWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (ArtSlot (endArg0Bytes32Key I))
  have hslot := endArtSlot_eq I hsz36
  have h14 : (⟨14⟩ : UInt256) = UInt256.ofNat 14 := by native_decide
  unfold endFlowArtWord endFlowArtWorldWord endFlowArtWorldSlot
  rw [hload, hslot]
  rw [h14]

theorem endFlowTagWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowTagWord evm I = endFlowTagWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (tagSlot (endArg0Bytes32Key I))
  have hslot := endTagSlot_eq I hsz36
  have h12 : (⟨12⟩ : UInt256) = UInt256.ofNat 12 := by native_decide
  unfold endFlowTagWord endFlowTagWorldWord endFlowTagWorldSlot
  rw [hload, hslot]
  rw [h12]

theorem endFlowGapWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowGapWord evm I = endFlowGapWorldWord world.2 I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (gapSlot (endArg0Bytes32Key I))
  have hslot := endGapSlot_eq I hsz36
  have h13 : (⟨13⟩ : UInt256) = UInt256.ofNat 13 := by native_decide
  unfold endFlowGapWord endFlowGapWorldWord endFlowGapWorldSlot
  rw [hload, hslot]
  rw [h13]

theorem endFlowWad0Word_eq_world_of_callRel {s0 world I evm out}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowWad0Word evm I out = endFlowWad0WorldWord world.2 I out := by
  have hArt := endFlowArtWord_eq_world_of_callRel h hsz36
  simp [endFlowWad0Word, endFlowWad0WorldWord, hArt]

theorem endFlowWadWord_eq_world_of_callRel {s0 world I evm out}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowWadWord evm I out = endFlowWadWorldWord world.2 I out := by
  have hWad0 := endFlowWad0Word_eq_world_of_callRel (out := out) h hsz36
  have hTag := endFlowTagWord_eq_world_of_callRel h hsz36
  simp [endFlowWadWord, endFlowWadWorldWord, hWad0, hTag]

theorem endFlowNum0Word_eq_world_of_callRel {s0 world I evm out}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowNum0Word evm I out = endFlowNum0WorldWord world.2 I out := by
  have hWad := endFlowWadWord_eq_world_of_callRel (out := out) h hsz36
  have hGap := endFlowGapWord_eq_world_of_callRel h hsz36
  simp [endFlowNum0Word, endFlowNum0WorldWord, hWad, hGap]

theorem endFlowNumWord_eq_world_of_callRel {s0 world I evm out}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowNumWord evm I out = endFlowNumWorldWord world.2 I out := by
  have hNum0 := endFlowNum0Word_eq_world_of_callRel (out := out) h hsz36
  simp [endFlowNumWord, endFlowNumWorldWord, hNum0]

theorem endFlowDenWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    endFlowDenWord evm = endFlowDenWorldWord world.2 I := by
  have hDebt := endFlowDebtWord_eq_world_of_callRel h
  simp [endFlowDenWord, endFlowDenWorldWord, hDebt]

theorem endFlowFixValueWord_eq_world_of_callRel {s0 world I evm out}
    (h : CallStateRel s0 I world evm) (hsz36 : 36 ≤ I.calldata.size) :
    endFlowFixValueWord evm I out =
      endFlowFixValueWorldWord world.2 I out := by
  have hNum := endFlowNumWord_eq_world_of_callRel (out := out) h hsz36
  have hDen := endFlowDenWord_eq_world_of_callRel h
  simp [endFlowFixValueWord, endFlowFixValueWorldWord, hNum, hDen]

theorem endFlowAfterVatIlksSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨3002⟩
      (fun cur frame e =>
        frame = endFlowAfterVatIlksFrame I cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        160 ≤ cur.rdata.size ∧
        endFlowDenWorldWord cur.world.2 I ≠ ⟨0⟩ ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I cur.rdata),
            ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
        cur.mem = endFlowVatIlksReturnMem I cur.rdata ∧
        cur.aw = endFlowAfterVatIlksAw aw)
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hout, h160, hden, hstack, hmem, haw⟩
  cases hframe
  have hArtEq := endFlowArtWord_eq_world_of_callRel hrel hsz36
  have hTagEq := endFlowTagWord_eq_world_of_callRel hrel hsz36
  have hGapEq := endFlowGapWord_eq_world_of_callRel hrel hsz36
  have hWad0Eq := endFlowWad0Word_eq_world_of_callRel (out := cur.rdata) hrel hsz36
  have hWadEq := endFlowWadWord_eq_world_of_callRel (out := cur.rdata) hrel hsz36
  have hNum0Eq := endFlowNum0Word_eq_world_of_callRel (out := cur.rdata) hrel hsz36
  have hDenEq := endFlowDenWord_eq_world_of_callRel hrel
  by_cases hfit1 :
      (endFlowArtWorldWord cur.world.2 I).toNat *
        (endFlowVatIlksRateWord cur.rdata).toNat < UInt256.size
  · have hfit1Source :
        (endFlowArtWord evm I).toNat *
          (endFlowVatIlksRateWord cur.rdata).toNat < UInt256.size := by
      simpa [hArtEq] using hfit1
    by_cases hfit2 :
        (endFlowWad0WorldWord cur.world.2 I cur.rdata).toNat *
          (endFlowTagWorldWord cur.world.2 I).toNat < UInt256.size
    · have hfit2Source :
          (endFlowWad0Word evm I cur.rdata).toNat *
            (endFlowTagWord evm I).toNat < UInt256.size := by
        simpa [hWad0Eq, hTagEq] using hfit2
      by_cases hleSub :
          (endFlowGapWorldWord cur.world.2 I).toNat ≤
            (endFlowWadWorldWord cur.world.2 I cur.rdata).toNat
      · have hleSubSource :
            (endFlowGapWord evm I).toNat ≤
              (endFlowWadWord evm I cur.rdata).toNat := by
          simpa [hGapEq, hWadEq] using hleSub
        by_cases hfitMul :
            (endFlowNum0WorldWord cur.world.2 I cur.rdata).toNat * endRayNat <
              UInt256.size
        · have hfitMulSource :
              (endFlowNum0Word evm I cur.rdata).toNat * endRayNat < UInt256.size := by
            simpa [hNum0Eq] using hfitMul
          have hdenSource : endFlowDenWord evm ≠ ⟨0⟩ := by
            simpa [hDenEq] using hden
          have hsource := endFlowAfterVatIlksSuffixOk evm I cur.rdata
            hrel.env hsz36 hfit1Source hfit2Source hleSubSource hfitMulSource hdenSource
          have rdret := endX_flow_after_vat_ilks_ok
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
            (k := k) (C := C) (world := cur.world)
            hout h160 hfit1 hfit2 hleSub hfitMul hden hperm
            (by
              simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
          have hvalue := endFlowFixValueWord_eq_world_of_callRel
            (out := cur.rdata) hrel hsz36
          have hstored :=
            hrel.storageStore_codeOwner (endFlowFixSlot I)
              (endFlowFixValueWord evm I cur.rdata)
          exact BlockProgress.ofRDret hsource rdret
            (by
              simpa [endFlowFixStoredWorld, endFlowFinalState] using hstored.created.symm)
            (by
              simpa [endFlowFixStoredWorld, endFlowFinalState, storageWrite, hvalue,
                endFlowFixSlot_eq I hsz36] using hstored.accounts)
            abiVoidFallthrough
        · have hoverMulWorld :
              UInt256.size ≤ (endFlowNum0WorldWord cur.world.2 I cur.rdata).toNat *
                endRayNat := by
            omega
          have hoverMulSource :
              UInt256.size ≤ (endFlowNum0Word evm I cur.rdata).toNat * endRayNat := by
            simpa [hNum0Eq] using hoverMulWorld
          have hsource := endFlowAfterVatIlksSuffixMulRevert evm I cur.rdata hsz36
            hfit1Source hfit2Source hleSubSource hoverMulSource
          have hrev := endX_flow_after_vat_ilks_mul_fail
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
            (k := k) (C := C) (world := cur.world)
            hout h160 hfit1 hfit2 hleSub hoverMulWorld
            (by
              simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
          exact BlockProgress.ofRDrev hsource hrev
      · have hltSubWorld :
            (endFlowWadWorldWord cur.world.2 I cur.rdata).toNat <
              (endFlowGapWorldWord cur.world.2 I).toNat := by
          omega
        have hltSubSource :
            (endFlowWadWord evm I cur.rdata).toNat <
              (endFlowGapWord evm I).toNat := by
          simpa [hWadEq, hGapEq] using hltSubWorld
        have hsource := endFlowAfterVatIlksSuffixSubRevert evm I cur.rdata hsz36
          hfit1Source hfit2Source hltSubSource
        have hrev := endX_flow_after_vat_ilks_sub_fail
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
          (k := k) (C := C) (world := cur.world)
          hout h160 hfit1 hfit2 hltSubWorld
          (by
            simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
        exact BlockProgress.ofRDrev hsource hrev
    · have hover2World :
          UInt256.size ≤ (endFlowWad0WorldWord cur.world.2 I cur.rdata).toNat *
            (endFlowTagWorldWord cur.world.2 I).toNat := by
        omega
      have hover2Source :
          UInt256.size ≤ (endFlowWad0Word evm I cur.rdata).toNat *
            (endFlowTagWord evm I).toNat := by
        simpa [hWad0Eq, hTagEq] using hover2World
      have hsource := endFlowAfterVatIlksSuffixRmul2Revert evm I cur.rdata hsz36
        hfit1Source hover2Source
      have hrev := endX_flow_after_vat_ilks_rmul2_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
        (k := k) (C := C) (world := cur.world)
        hout h160 hfit1 hover2World
        (by
          simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
      exact BlockProgress.ofRDrev hsource hrev
  · have hover1World :
        UInt256.size ≤ (endFlowArtWorldWord cur.world.2 I).toNat *
          (endFlowVatIlksRateWord cur.rdata).toNat := by
      omega
    have hover1Source :
        UInt256.size ≤ (endFlowArtWord evm I).toNat *
          (endFlowVatIlksRateWord cur.rdata).toNat := by
      simpa [hArtEq] using hover1World
    have hsource := endFlowAfterVatIlksSuffixRmul1Revert evm I cur.rdata hsz36
      hover1Source
    have hrev := endX_flow_after_vat_ilks_rmul1_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
      (k := k) (C := C) (world := cur.world)
      hout h160 hover1World
      (by
        simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
    exact BlockProgress.ofRDrev hsource hrev

theorem endFlowAfterVatIlksSuffixProgressOrInvalid {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {cur : Cursor} {k C : ℕ} {frame : Frame} {evm : EVM.State}
    (hperm : I.perm = true) (hsz36 : 36 ≤ I.calldata.size)
    (hpc : cur.pc = ⟨3002⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP :
      frame = endFlowAfterVatIlksFrame I cur.rdata ∧
      CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world evm ∧
      cur.rdata.size < UInt256.size ∧
      160 ≤ cur.rdata.size ∧
      cur.stack =
        [UInt256.ofNat cur.rdata.size,
          memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I cur.rdata),
          ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
      cur.mem = endFlowVatIlksReturnMem I cur.rdata ∧
      cur.aw = endFlowAfterVatIlksAw aw) :
    BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      frame evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      (runtimeExit (.abi [])) ∨
    (ExecBlock config frame evm
      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
        .internalCall "mul" [.var "num0", .intLit RAY] "num",
        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ]
      .reverted ∧
    RDinvalid endBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  rcases hP with ⟨hframe, hrel, hout, h160, hstack, hmem, haw⟩
  cases hframe
  have hArtEq := endFlowArtWord_eq_world_of_callRel hrel hsz36
  have hTagEq := endFlowTagWord_eq_world_of_callRel hrel hsz36
  have hGapEq := endFlowGapWord_eq_world_of_callRel hrel hsz36
  have hWad0Eq := endFlowWad0Word_eq_world_of_callRel (out := cur.rdata) hrel hsz36
  have hWadEq := endFlowWadWord_eq_world_of_callRel (out := cur.rdata) hrel hsz36
  have hNum0Eq := endFlowNum0Word_eq_world_of_callRel (out := cur.rdata) hrel hsz36
  have hDenEq := endFlowDenWord_eq_world_of_callRel hrel
  by_cases hfit1 :
      (endFlowArtWorldWord cur.world.2 I).toNat *
        (endFlowVatIlksRateWord cur.rdata).toNat < UInt256.size
  · have hfit1Source :
        (endFlowArtWord evm I).toNat *
          (endFlowVatIlksRateWord cur.rdata).toNat < UInt256.size := by
      simpa [hArtEq] using hfit1
    by_cases hfit2 :
        (endFlowWad0WorldWord cur.world.2 I cur.rdata).toNat *
          (endFlowTagWorldWord cur.world.2 I).toNat < UInt256.size
    · have hfit2Source :
          (endFlowWad0Word evm I cur.rdata).toNat *
            (endFlowTagWord evm I).toNat < UInt256.size := by
        simpa [hWad0Eq, hTagEq] using hfit2
      by_cases hleSub :
          (endFlowGapWorldWord cur.world.2 I).toNat ≤
            (endFlowWadWorldWord cur.world.2 I cur.rdata).toNat
      · have hleSubSource :
            (endFlowGapWord evm I).toNat ≤
              (endFlowWadWord evm I cur.rdata).toNat := by
          simpa [hGapEq, hWadEq] using hleSub
        by_cases hfitMul :
            (endFlowNum0WorldWord cur.world.2 I cur.rdata).toNat * endRayNat <
              UInt256.size
        · have hfitMulSource :
              (endFlowNum0Word evm I cur.rdata).toNat * endRayNat < UInt256.size := by
            simpa [hNum0Eq] using hfitMul
          by_cases hdenZero : endFlowDenWorldWord cur.world.2 I = ⟨0⟩
          · have hdenSource : endFlowDenWord evm = ⟨0⟩ := by
              simpa [hDenEq] using hdenZero
            have hsource := endFlowAfterVatIlksSuffixDenRevert evm I cur.rdata hsz36
              hfit1Source hfit2Source hleSubSource hfitMulSource hdenSource
            have hinv := endX_flow_after_vat_ilks_den_invalid
              (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
              (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
              (k := k) (C := C) (world := cur.world)
              hout h160 hfit1 hfit2 hleSub hfitMul hdenZero
              (by
                simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
            exact Or.inr ⟨hsource, hinv⟩
          · have hdenSource : endFlowDenWord evm ≠ ⟨0⟩ := by
              simpa [hDenEq] using hdenZero
            have hsource := endFlowAfterVatIlksSuffixOk evm I cur.rdata
              hrel.env hsz36 hfit1Source hfit2Source hleSubSource hfitMulSource hdenSource
            have rdret := endX_flow_after_vat_ilks_ok
              (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
              (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
              (k := k) (C := C) (world := cur.world)
              hout h160 hfit1 hfit2 hleSub hfitMul hdenZero hperm
              (by
                simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
            have hvalue := endFlowFixValueWord_eq_world_of_callRel
              (out := cur.rdata) hrel hsz36
            have hstored :=
              hrel.storageStore_codeOwner (endFlowFixSlot I)
                (endFlowFixValueWord evm I cur.rdata)
            exact Or.inl <| BlockProgress.ofRDret hsource rdret
              (by
                simpa [endFlowFixStoredWorld, endFlowFinalState] using hstored.created.symm)
              (by
                simpa [endFlowFixStoredWorld, endFlowFinalState, storageWrite, hvalue,
                  endFlowFixSlot_eq I hsz36] using hstored.accounts)
              abiVoidFallthrough
        · have hoverMulWorld :
              UInt256.size ≤ (endFlowNum0WorldWord cur.world.2 I cur.rdata).toNat *
                endRayNat := by
            omega
          have hoverMulSource :
              UInt256.size ≤ (endFlowNum0Word evm I cur.rdata).toNat * endRayNat := by
            simpa [hNum0Eq] using hoverMulWorld
          have hsource := endFlowAfterVatIlksSuffixMulRevert evm I cur.rdata hsz36
            hfit1Source hfit2Source hleSubSource hoverMulSource
          have hrev := endX_flow_after_vat_ilks_mul_fail
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
            (k := k) (C := C) (world := cur.world)
            hout h160 hfit1 hfit2 hleSub hoverMulWorld
            (by
              simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
          exact Or.inl (BlockProgress.ofRDrev hsource hrev)
      · have hltSubWorld :
            (endFlowWadWorldWord cur.world.2 I cur.rdata).toNat <
              (endFlowGapWorldWord cur.world.2 I).toNat := by
          omega
        have hltSubSource :
            (endFlowWadWord evm I cur.rdata).toNat <
              (endFlowGapWord evm I).toNat := by
          simpa [hWadEq, hGapEq] using hltSubWorld
        have hsource := endFlowAfterVatIlksSuffixSubRevert evm I cur.rdata hsz36
          hfit1Source hfit2Source hltSubSource
        have hrev := endX_flow_after_vat_ilks_sub_fail
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
          (k := k) (C := C) (world := cur.world)
          hout h160 hfit1 hfit2 hltSubWorld
          (by
            simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
        exact Or.inl (BlockProgress.ofRDrev hsource hrev)
    · have hover2World :
          UInt256.size ≤ (endFlowWad0WorldWord cur.world.2 I cur.rdata).toNat *
            (endFlowTagWorldWord cur.world.2 I).toNat := by
        omega
      have hover2Source :
          UInt256.size ≤ (endFlowWad0Word evm I cur.rdata).toNat *
            (endFlowTagWord evm I).toNat := by
        simpa [hWad0Eq, hTagEq] using hover2World
      have hsource := endFlowAfterVatIlksSuffixRmul2Revert evm I cur.rdata hsz36
        hfit1Source hover2Source
      have hrev := endX_flow_after_vat_ilks_rmul2_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
        (k := k) (C := C) (world := cur.world)
        hout h160 hfit1 hover2World
        (by
          simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
      exact Or.inl (BlockProgress.ofRDrev hsource hrev)
  · have hover1World :
        UInt256.size ≤ (endFlowArtWorldWord cur.world.2 I).toNat *
          (endFlowVatIlksRateWord cur.rdata).toNat := by
      omega
    have hover1Source :
        UInt256.size ≤ (endFlowArtWord evm I).toNat *
          (endFlowVatIlksRateWord cur.rdata).toNat := by
      simpa [hArtEq] using hover1World
    have hsource := endFlowAfterVatIlksSuffixRmul1Revert evm I cur.rdata hsz36
      hover1Source
    have hrev := endX_flow_after_vat_ilks_rmul1_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (out := cur.rdata)
      (k := k) (C := C) (world := cur.world)
      hout h160 hover1World
      (by
        simpa [hpc, hstack, hmem, haw, endFlowAfterVatIlksCursor] using rd)
    exact Or.inl (BlockProgress.ofRDrev hsource hrev)

theorem endRDinvalidReEquivExecutionRevert
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code : ByteArray} {t callargs}
    (hcode : I.code = code)
    (hinv : RDinvalid code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode
      (t.params.map Param.name) (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
      (initState cA gh bl σ_solm σ₀ g A I) callargs t.body .reverted)
    (hfallback : contract.fallback = none) (hreceive : contract.receive = none) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀
      g.toUInt256 A I := by
  rcases hinv with hoog | hinv
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hinv
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hinv)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body .reverted := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    exact reEquiv_execution hd hdec hbody'
      (execResultsEquiv.invalidHalt hxi rfl) hfallback hreceive

theorem endFlowDebtWorldWord_eq_of_accountMapEquiv {σ_evm σ_solm I}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    endFlowDebtWorldWord σ_evm I = endFlowDebtWorldWord σ_solm I := by
  unfold endFlowDebtWorldWord
  simpa [storageRead_eq] using
    accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 11)
      (default : UInt256)

theorem endFlowFixWorldWord_eq_of_accountMapEquiv {σ_evm σ_solm I}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    endFlowFixWorldWord σ_evm I = endFlowFixWorldWord σ_solm I := by
  unfold endFlowFixWorldWord
  simpa [storageRead_eq] using
    accountMapEquiv_storage_findD hAccounts I.codeOwner (endFlowFixWorldSlot I)
      (default : UInt256)

theorem endFlowDebtWord_init_eq (cA gh bl σ σ₀ A I) (g : Sat256) :
    endFlowDebtWord (initState cA gh bl σ σ₀ g A I) =
      endFlowDebtWorldWord σ I := by
  unfold endFlowDebtWord endFlowDebtWorldWord
  change Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (UInt256.ofNat 11) = storageRead I.codeOwner σ (UInt256.ofNat 11)
  rw [endPackStorageLoad_init_eq]
  simp [solcSlotWord, storageRead_eq]

theorem endFlowFixWord_init_eq (cA gh bl σ σ₀ A I) (g : Sat256)
    (hsz36 : 36 ≤ I.calldata.size) :
    endFlowFixWord (initState cA gh bl σ σ₀ g A I) I =
      endFlowFixWorldWord σ I := by
  unfold endFlowFixWord endFlowFixWorldWord
  change Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (endFlowFixSlot I) = storageRead I.codeOwner σ (endFlowFixWorldSlot I)
  rw [endPackStorageLoad_init_eq]
  rw [endFlowFixSlot_eq I hsz36]
  simp [solcSlotWord, storageRead_eq]

set_option maxHeartbeats 12000000 in
theorem endFlowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 29))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨635⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 29 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some flowTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 29 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some flowTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (flowTransition.params.map Param.name) (transitionSignature flowTransition).paramTypes
        I.calldata = some (endFlowStore I) := by
      simpa [config, flowTransition, transitionSignature, bytes32, endFlowStore] using
        endDecode_legacyBytes32_ilk_ok (I := I) hsz36
    have hDebtWord :
        endFlowDebtWorldWord σ_evm I = endFlowDebtWorldWord σ_solm I :=
      endFlowDebtWorldWord_eq_of_accountMapEquiv hAccounts
    by_cases hdebtSolm : endFlowDebtWorldWord σ_solm I = ⟨0⟩
    · have hdebtEvm : endFlowDebtWorldWord σ_evm I = ⟨0⟩ :=
        hDebtWord.trans hdebtSolm
      have hdebtSrc :
          endFlowDebtWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) = ⟨0⟩ := by
        rw [endFlowDebtWord_init_eq]
        exact hdebtSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endFlowStore I) flowTransition.body .reverted := by
        simpa [initState] using
          endFlowBodyDebtFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hdebtSrc
      exact (endX_flow_debt_fail (g := Sat256.ofUInt256 g) hsz36 hsize
          hdebtEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hdebtEvm : endFlowDebtWorldWord σ_evm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebtSolm (hDebtWord.symm.trans hbad)
      have hdebtSrc :
          endFlowDebtWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ≠ ⟨0⟩ := by
        rw [endFlowDebtWord_init_eq]
        exact hdebtSolm
      have hFixWord :
          endFlowFixWorldWord σ_evm I = endFlowFixWorldWord σ_solm I :=
        endFlowFixWorldWord_eq_of_accountMapEquiv hAccounts
      by_cases hfixSolm : endFlowFixWorldWord σ_solm I = ⟨0⟩
      · have hfixEvm : endFlowFixWorldWord σ_evm I = ⟨0⟩ :=
          hFixWord.trans hfixSolm
        have hfixSrc :
            endFlowFixWord
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = ⟨0⟩ := by
          rw [endFlowFixWord_init_eq cA gh bl σ_solm σ₀ A I (Sat256.ofUInt256 g) hsz36]
          exact hfixSolm
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
                (endFlowStore I) flowTransition.body .reverted := by
            simpa [initState] using
              endFlowBodyVatNoCode
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hsz36 hdebtSrc hfixSrc
                hvatNoCodeSrc
          exact (endX_flow_vat_no_code (g := Sat256.ofUInt256 g) hsz36 hsize
              hdebtEvm hfixEvm hvatNoCodeEvm hreach)
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
            endX_flow_to_vat_ilks_call (g := Sat256.ofUInt256 g)
              hsz36 hsize hdebtEvm hfixEvm hvatNoCodeEvm hreach
          have hprefix :
              ExecBlock config { contract := contract, locals := endFlowStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (nonpayable ++
                  [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
                    .require (.binary .eq (.storage (fixRef (.var "ilk"))) (.intLit 0)),
                    .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
                (.ok { contract := contract, locals := endFlowStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
            endFlowBodyPrefixOk
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz36 hdebtSrc hfixSrc hvatCodeSrc
          have hpostRel :
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
                (cA, σ_evm)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
            CallStateRel.initState hAccounts
          have finishProgress :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endFlowStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                flowTransition.body (runtimeExit (.abi [])) →
              runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
            intro hprogressBody
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
          have hcallProgress :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endFlowStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                [ .externalCall (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"] "vatIlk" ]
                (sequenceExit ⟨3002⟩
                  (fun cur frame e =>
                    frame = endFlowAfterVatIlksFrame I cur.rdata ∧
                    CallStateRel
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                      I cur.world e ∧
                    cur.rdata.size < UInt256.size ∧
                    160 ≤ cur.rdata.size ∧
                    cur.stack =
                      [UInt256.ofNat cur.rdata.size,
                        memLoad (UInt256.ofNat 64) (endFlowVatIlksReturnMem I cur.rdata),
                        ⟨0⟩, endArg0Word I, ⟨562⟩, sel] ∧
                    cur.mem = endFlowVatIlksReturnMem I cur.rdata ∧
                    cur.aw = endFlowAfterVatIlksAw awCall)
                  (runtimeExit (.abi []))) :=
            (endFlowVatIlksExternalCallRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) (rdata := ByteArray.empty) (k := kCall)
              (C := CCall)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              hperm hsz36)
              (by simpa [endFlowVatIlksCallCursor] using rdCall)
              hpostRel
          rcases hcallProgress with ⟨result, endpoint, hcallBlock, hreachEndpoint, hQ⟩
          cases result with
          | ok frameAfter evmAfter =>
              cases endpoint with
              | reached curAfter =>
                  simp only [sequenceExit, fallthrough] at hQ
                  rcases hQ with ⟨hpcAfter, hAfter⟩
                  rcases hreachEndpoint with ⟨kAfter, CAfter, rdAfter⟩
                  have hsuffix :=
                    endFlowAfterVatIlksSuffixProgressOrInvalid
                      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                      (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                      (aw := awCall) (cur := curAfter) (k := kAfter) (C := CAfter)
                      (frame := frameAfter) (evm := evmAfter)
                      hperm hsz36 hpcAfter rdAfter hAfter
                  cases hsuffix with
                  | inl hsuffixProgress =>
                      have hcallSuffixProgress :
                          BlockProgress endBytecode I (Sat256.ofUInt256 g)
                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                            config { contract := contract, locals := endFlowStore I }
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                                [.var "ilk"] "vatIlk" ] ++
                              [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
                                .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
                                .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
                                .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
                                .internalCall "mul" [.var "num0", .intLit RAY] "num",
                                .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
                                .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
                                .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
                            (runtimeExit (.abi [])) :=
                        BlockProgress.prepend hcallBlock hsuffixProgress
                      have hprogress :=
                        BlockProgress.prepend hprefix hcallSuffixProgress
                      exact finishProgress (by
                        simpa [flowTransition, checkedExternalCallStmts, List.append_assoc]
                          using hprogress)
                  | inr hinvalid =>
                      rcases hinvalid with ⟨hsuffixBlock, hinv⟩
                      have hcallSuffixBlock :
                          ExecBlock config { contract := contract, locals := endFlowStore I }
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                                [.var "ilk"] "vatIlk" ] ++
                              [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
                                .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
                                .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
                                .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
                                .internalCall "mul" [.var "num0", .intLit RAY] "num",
                                .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
                                .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
                                .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
                            .reverted :=
                        Reasoning.Theory.execBlock_append hcallBlock hsuffixBlock
                      have hfullBlock :=
                        Reasoning.Theory.execBlock_append hprefix hcallSuffixBlock
                      have hbody :
                          ExecTransitionBody config contract
                            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                            (endFlowStore I) flowTransition.body .reverted := by
                        have hblock :
                            ExecBlock config { contract := contract, locals := endFlowStore I }
                              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                              flowTransition.body .reverted := by
                          simpa [flowTransition, checkedExternalCallStmts, List.append_assoc]
                            using hfullBlock
                        simpa [ExecTransitionBody] using execFuncBody_of_execBlock hblock
                      exact endRDinvalidReEquivExecutionRevert hcode hinv hd hdec hbody rfl rfl
              | returned world out =>
                  simp [sequenceExit, fallthrough] at hQ
              | reverted =>
                  simp [sequenceExit, fallthrough] at hQ
          | returned frameRet evmRet value =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endFlowStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
                        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
                        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
                        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
                        .internalCall "mul" [.var "num0", .intLit RAY] "num",
                        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
                        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
                        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
                    (runtimeExit (.abi [])) := by
                refine ⟨.returned frameRet evmRet value, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [flowTransition, checkedExternalCallStmts, List.append_assoc]
                  using hprogress)
          | reverted =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endFlowStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
                        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
                        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
                        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
                        .internalCall "mul" [.var "num0", .intLit RAY] "num",
                        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
                        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
                        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
                    (runtimeExit (.abi [])) := by
                refine ⟨.reverted, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [flowTransition, checkedExternalCallStmts, List.append_assoc]
                  using hprogress)
          | «break» frameBreak evmBreak =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endFlowStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
                        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
                        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
                        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
                        .internalCall "mul" [.var "num0", .intLit RAY] "num",
                        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
                        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
                        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
                    (runtimeExit (.abi [])) := by
                refine ⟨.break frameBreak evmBreak, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [flowTransition, checkedExternalCallStmts, List.append_assoc]
                  using hprogress)
          | «continue» frameContinue evmContinue =>
              have hcallSuffixProgress :
                  BlockProgress endBytecode I (Sat256.ofUInt256 g)
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    config { contract := contract, locals := endFlowStore I }
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    ([ .externalCall (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk" ] ++
                      [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
                        .internalCall "rmul" [.storage (ArtRef (.var "ilk")), .var "rate"] "wad0",
                        .internalCall "rmul" [.var "wad0", .storage (tagRef (.var "ilk"))] "wad",
                        .internalCall "sub" [.var "wad", .storage (gapRef (.var "ilk"))] "num0",
                        .internalCall "mul" [.var "num0", .intLit RAY] "num",
                        .letDecl "den" (some uint256) (.binary .div (.storage debtRef) (.intLit RAY)),
                        .letDecl "fixV" (some uint256) (.binary .div (.var "num") (.var "den")),
                        .assign .storage (fixRef (.var "ilk")) (.var "fixV") ])
                    (runtimeExit (.abi [])) := by
                refine ⟨.continue frameContinue evmContinue, endpoint, ?_, hreachEndpoint, ?_⟩
                · exact Reasoning.Theory.execBlock_append_term hcallBlock
                    (by intro f e h; cases h)
                · simpa [sequenceExit] using hQ
              have hprogress := BlockProgress.prepend hprefix hcallSuffixProgress
              exact finishProgress (by
                simpa [flowTransition, checkedExternalCallStmts, List.append_assoc]
                  using hprogress)
      · have hfixEvm : endFlowFixWorldWord σ_evm I ≠ ⟨0⟩ := by
          intro hbad
          exact hfixSolm (hFixWord.symm.trans hbad)
        have hfixSrc :
            endFlowFixWord
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠ ⟨0⟩ := by
          rw [endFlowFixWord_init_eq cA gh bl σ_solm σ₀ A I (Sat256.ofUInt256 g) hsz36]
          exact hfixSolm
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endFlowStore I) flowTransition.body .reverted := by
          simpa [initState] using
            endFlowBodyFixFail
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz36 hdebtSrc hfixSrc
        exact (endX_flow_fix_fail (g := Sat256.ofUInt256 g) hsz36 hsize
            hdebtEvm hfixEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (flowTransition.params.map Param.name) (transitionSignature flowTransition).paramTypes
        I.calldata = none := by
      simpa [config, flowTransition, transitionSignature, bytes32] using
        endDecode_legacyBytes32_ilk_none_short (I := I) hsz4 hshort
    exact (endX_flow_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
