import Benchmarks.Dss.End.Arithmetic
import Benchmarks.Dss.End.Presence
import Benchmarks.Dss.End.RuntimeBlocks_002
import Benchmarks.Dss.End.RuntimeBlocks_004
import Benchmarks.Dss.End.RuntimeBlocks_014
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `cash(bytes32,uint256)` -/

abbrev endCashStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
    (endUIntValue (endArg1Word I))

abbrev endCashFixSlot (I : ExecutionEnv) : UInt256 :=
  fixSlot (endArg0Bytes32Key I)

abbrev endCashFixWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 15) (endArg0Word I)

abbrev endCashFixWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashFixSlot I)

abbrev endCashFixWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (endCashFixWorldSlot I)

abbrev endCashAmtWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  endGenericRmulResult (endArg1Word I) (endCashFixWord evm I)

abbrev endCashAmtWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endGenericRmulResult (endArg1Word I) (endCashFixWorldWord σ I)

abbrev endCashAmtStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (endCashStore I).insert "amt" (endUIntValue (endCashAmtWord evm I))

abbrev endCashFluxSelectorWord : UInt256 := UInt256.ofNat 1628552750

def endCashFluxPayloadBytes (σ : AccountMap) (I : ExecutionEnv) : List UInt8 :=
  (((EVM.Word.toBytesBE (endArg0Word I) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) ++
      EVM.Word.toBytesBE (endCashAmtWorldWord σ I))

def endCashFluxEncodedCall (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  fluxSelector ++ ⟨(endCashFluxPayloadBytes σ I).toArray⟩

theorem endDecode_legacyBytes32_uint256_cash_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "wad"] [bytes32, uint256]
        I.calldata =
      some (endCashStore I) := by
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
        some ([endArg0Bytes32Value I, endUIntValue (endArg1Word I)], 64) by
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
          some (endUIntValue (endArg1Word I), 64) := by
      rw [decodeABIValue_scalarWordWithMode_eq (mode := DecodeMode.legacySolc05)
        (ty := uint256) (bytes := I.calldata.toList.drop 4) (start := 32) (by decide)]
      change decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256
          (I.calldata.toList.drop 4) 32 =
        some (endUIntValue (endArg1Word I), 64)
      rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := I.calldata.toList.drop 4) (start := 32) htake36]
      rw [hword36]
    rw [hval1]
    simp [endUIntValue]]
  simp [decodeCalldata.insertValues, endCashStore, endUIntValue]

theorem endDecode_legacyBytes32_uint256_cash_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["ilk", "wad"] [bytes32, uint256]
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

theorem endCashStore_get_ilk (I : ExecutionEnv) :
    (endCashStore I).get? "ilk" = some (endArg0Bytes32Value I) := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
    (endUIntValue (endArg1Word I))).get? "ilk") = some (endArg0Bytes32Value I)
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "wad") (a := "ilk") (endUIntValue (endArg1Word I)) (by decide)]
  exact store_get_self (∅ : Store) "ilk" (endArg0Bytes32Value I)

theorem endCashStore_get_wad (I : ExecutionEnv) :
    (endCashStore I).get? "wad" = some (endUIntValue (endArg1Word I)) := by
  simp [endCashStore, store_get_self]

theorem endCashStore_getElem?_ilk (I : ExecutionEnv) :
    (endCashStore I)["ilk"]? = some (endArg0Bytes32Value I) := by
  rw [← Std.HashMap.get?_eq_getElem?]
  exact endCashStore_get_ilk I

theorem endCashStore_getElem_ilk (I : ExecutionEnv) :
    (endCashStore I)["ilk"] = endArg0Bytes32Value I := by
  have hopt : (endCashStore I)["ilk"]? = some (endArg0Bytes32Value I) :=
    endCashStore_getElem?_ilk I
  have hmem : "ilk" ∈ endCashStore I := by
    simp [endCashStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endCashStore I) "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endCashStore_get_fix_none (I : ExecutionEnv) :
    (endCashStore I).get? "fix" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
    (endUIntValue (endArg1Word I))).get? "fix") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "wad") (a := "fix") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "fix")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endCashStore_get_vat_none (I : ExecutionEnv) :
    (endCashStore I).get? "vat" = none := by
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
    (endUIntValue (endArg1Word I))).get? "vat") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "wad") (a := "vat") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "vat")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endCashAmtStore_get_amt (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAmtStore evm I).get? "amt" =
      some (endUIntValue (endCashAmtWord evm I)) := by
  exact store_get_self (endCashStore I) "amt" (endUIntValue (endCashAmtWord evm I))

theorem endCashAmtStore_get_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAmtStore evm I).get? "ilk" = some (endArg0Bytes32Value I) := by
  unfold endCashAmtStore
  rw [store_get_ne (endCashStore I) (k := "amt") (a := "ilk")
    (endUIntValue (endCashAmtWord evm I)) (by decide)]
  exact endCashStore_get_ilk I

theorem endCashAmtStore_getElem_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAmtStore evm I)["ilk"] = endArg0Bytes32Value I := by
  have hopt : (endCashAmtStore evm I)["ilk"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endCashAmtStore_get_ilk evm I
  have hmem : "ilk" ∈ endCashAmtStore evm I := by
    simp [endCashAmtStore, endCashStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endCashAmtStore evm I) "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endCashAmtStore_get_wad (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAmtStore evm I).get? "wad" = some (endUIntValue (endArg1Word I)) := by
  unfold endCashAmtStore
  rw [store_get_ne (endCashStore I) (k := "amt") (a := "wad")
    (endUIntValue (endCashAmtWord evm I)) (by decide)]
  exact endCashStore_get_wad I

theorem endCashAmtStore_get_vat_none (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAmtStore evm I).get? "vat" = none := by
  unfold endCashAmtStore
  rw [store_get_ne (endCashStore I) (k := "amt") (a := "vat")
    (endUIntValue (endCashAmtWord evm I)) (by decide)]
  exact endCashStore_get_vat_none I

theorem endEvalFix_cash (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm
        (.storage (fixRef (.var "ilk"))) =
      .ok (endUIntValue (endCashFixWord evm I)) := by
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [evalExpr_storage_scalar
    (er := { base := "fix", steps := [.mindex (endArg0Bytes32Key I)] })
    (loc := wordLoc (fixSlot (endArg0Bytes32Key I)))
    (t := .int uint256Int)
    (hbase := endCashStore_get_fix_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, fixRef,
        endArg0Bytes32Value, endArg0Bytes32Key, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, bytes32Width, hlen,
        endCashStore_getElem_ilk])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_fix (endArg0Bytes32Key I))]
  simp [endRuntimeStorageLocLoad_uint256, endCashFixWord, endCashFixSlot]

theorem endEvalFixGuard_cash_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord evm I = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm
      (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFix_cash evm I hsz68, hfix]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endEvalFixGuard_cash_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord evm I ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCashStore I } evm
      (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalFix_cash evm I hsz68]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : ¬ (endCashFixWord evm I).toNat = 0 := by
    intro hzero
    exact hfix (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endCashBodyFixFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord evm I = ⟨0⟩) :
    ExecTransitionBody config contract evm (endCashStore I)
      cashTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cashTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalFixGuard_cash_false evm I hsz68 hfix)))

theorem endEvalCashRmulArgs (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config { contract := contract, locals := endCashStore I } evm
      [.var "wad", .storage (fixRef (.var "ilk"))] =
      .ok [endUIntValue (endArg1Word I), endUIntValue (endCashFixWord evm I)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endCashStore_get_wad]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalFix_cash evm I hsz68]
  simp [EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_rmul_cash (evm : EVM.State) (I : ExecutionEnv) :
    bindParams? rmulFunction.params
      [endUIntValue (endArg1Word I), endUIntValue (endCashFixWord evm I)] =
      some (endGenericMulStore (endArg1Word I) (endCashFixWord evm I)) := by
  simp [bindParams?, rmulFunction, endGenericMulStore, endUIntValue]

theorem endCashInternalRmulOk (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endArg1Word I).toNat * (endCashFixWord evm I).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endCashStore I } evm
      (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
      (.ok { contract := contract, locals := endCashAmtStore evm I } evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endCashAmtStore, endCashAmtWord] using
    internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endCashStore I })
      (evm := evm) (calleeEvm := evm) (name := "rmul") (retVar := "amt")
      (args := [.var "wad", .storage (fixRef (.var "ilk"))])
      (argVals := [endUIntValue (endArg1Word I), endUIntValue (endCashFixWord evm I)])
      (callee := rmulFunction) (locals := endGenericMulStore (endArg1Word I) (endCashFixWord evm I))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericRmulMStore (endArg1Word I) (endCashFixWord evm I) })
      (value := some [endUIntValue (endCashAmtWord evm I)])
      (endEvalCashRmulArgs evm I hsz68)
      (by
        change lookupCallable? contract "rmul" = some rmulFunction.toCallable
        rfl)
      (endBindParams_rmul_cash evm I)
      (by
        simpa [endCashAmtWord] using
          endGenericRmulFunctionOk evm (endArg1Word I) (endCashFixWord evm I) hfit)

theorem endCashInternalRmulRevert (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endArg1Word I).toNat * (endCashFixWord evm I).toNat) :
    ExecStmt config { contract := contract, locals := endCashStore I } evm
      (.internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endCashStore I })
    (evm := evm) (name := "rmul") (retVar := "amt")
    (args := [.var "wad", .storage (fixRef (.var "ilk"))])
    (argVals := [endUIntValue (endArg1Word I), endUIntValue (endCashFixWord evm I)])
    (callee := rmulFunction) (locals := endGenericMulStore (endArg1Word I) (endCashFixWord evm I))
    (endEvalCashRmulArgs evm I hsz68)
    (by
      change lookupCallable? contract "rmul" = some rmulFunction.toCallable
      rfl)
    (endBindParams_rmul_cash evm I)
    (endGenericRmulFunctionRevert evm (endArg1Word I) (endCashFixWord evm I) hover)

theorem endEvalVatAddress_cash (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endCashAmtStore evm I } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endCashAmtStore evm I } evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endCashAmtStore_get_vat_none evm I) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatExtCodeSize_cash (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endCashAmtStore evm I } evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_cash evm I]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_cash_false (evm : EVM.State) (I : ExecutionEnv)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCashAmtStore evm I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_cash evm I, hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_cash_true (evm : EVM.State) (I : ExecutionEnv)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endCashAmtStore evm I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_cash evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endCashBodyMulFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord evm I ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (endArg1Word I).toNat * (endCashFixWord evm I).toNat) :
    ExecTransitionBody config contract evm (endCashStore I)
      cashTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cashTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalFixGuard_cash_true evm I hsz68 hfix)) <|
      ExecBlock.consRevert
        (endCashInternalRmulRevert evm I hsz68 hover))

theorem endCashBodyVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord evm I ≠ ⟨0⟩)
    (hmulFit : (endArg1Word I).toNat * (endCashFixWord evm I).toNat < UInt256.size)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endCashStore I)
      cashTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cashTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalFixGuard_cash_true evm I hsz68 hfix)) <|
      ExecBlock.consNormal
        (endCashInternalRmulOk evm I hsz68 hmulFit) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_cash_false evm I hvatNoCode)))

theorem endCashBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hfix : endCashFixWord evm I ≠ ⟨0⟩)
    (hmulFit : (endArg1Word I).toNat * (endCashFixWord evm I).toNat < UInt256.size)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endCashStore I } evm
      (nonpayable ++
        [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
          .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt",
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endCashAmtStore evm I } evm) := by
  simpa [nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalFixGuard_cash_true evm I hsz68 hfix)) <|
      ExecBlock.consNormal
        (endCashInternalRmulOk evm I hsz68 hmulFit) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_cash_true evm I hvatCode)) <|
      ExecBlock.nil)

theorem endEvalCashFluxArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endCashAmtStore evm I } evm
      [.var "ilk", thisAddr, sender, .var "amt"] =
      .ok [endArg0Bytes32Value I, .address evm.executionEnv.codeOwner,
        .address evm.executionEnv.source, endUIntValue (endCashAmtWord evm I)] := by
  simp [evalExprs?, evalExpr?, thisAddr, sender, envValue, EvalResult.ofOption,
    EvalResult.bind, bind, pure, endCashAmtStore_getElem_ilk, endCashAmtStore_get_amt]

theorem endExternalEncode_flux_branch (args : List Value) :
    config.externalABI.encode? "flux" args =
      ABI.encodeCallWithSelector? fluxSelector [bytes32, addr, addr, uint256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "flux" = "cage")]
  rw [if_neg (by decide : ¬ "flux" = "vatIlks")]
  rw [if_neg (by decide : ¬ "flux" = "catIlks")]
  rw [if_neg (by decide : ¬ "flux" = "dogIlks")]
  rw [if_neg (by decide : ¬ "flux" = "spotIlks")]
  rw [if_neg (by decide : ¬ "flux" = "urns")]
  rw [if_neg (by decide : ¬ "flux" = "dai")]
  rw [if_neg (by decide : ¬ "flux" = "debt")]
  rw [if_neg (by decide : ¬ "flux" = "move")]
  rw [if_neg (by decide : ¬ "flux" = "hope")]
  rw [if_pos (by decide : "flux" = "flux")]

theorem endCashCodeOwnerWord_toNat (I : ExecutionEnv) :
    (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val := by
  exact ulit_toNat' _ (lt_of_lt_of_le I.codeOwner.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem endCashCodeOwnerWord_clean (I : ExecutionEnv) :
    UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val) =
      UInt256.ofNat I.codeOwner.val := by
  exact solcAddrMask_clean_left (by
    rw [endCashCodeOwnerWord_toNat I]
    change I.codeOwner.val < AccountAddress.size
    exact I.codeOwner.isLt)

theorem endCashEncodeBytes32_arg0 (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    encodeABIValue? bytes32 (endArg0Bytes32Value I) =
      some (EVM.Word.toBytesBE (endArg0Word I)) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hwordList :
      EVM.Word.toBytesBE (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)) =
        (I.calldata.toList.drop 4).take 32 :=
    toBytesBE_bytesToWord_of_length hlen
  have hword :
      ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) = endArg0Word I := by
    simpa [endArg0Word, calldataWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  simp [bytes32, bytes32Width, endArg0Bytes32Value, encodeABIValue?, hlen, zeroBytes]
  rw [← hwordList, hword]

theorem endEncodeAddress_this (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.codeOwner) =
      some (EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) := by
  have hownerWord : EVM.word I.codeOwner.val = UInt256.ofNat I.codeOwner.val := by rfl
  simp [addr, encodeABIValue?, encodeABIWord?, hownerWord]

theorem endEncodeUint_cashAmt (σ : AccountMap) (I : ExecutionEnv) :
    encodeABIValue? uint256 (endUIntValue (endCashAmtWorldWord σ I)) =
      some (EVM.Word.toBytesBE (endCashAmtWorldWord σ I)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? uint256 (endUIntValue (endCashAmtWorldWord σ I))
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (endCashAmtWorldWord σ I))
  rw [endEncodeABIWord_uint256]
  simp only [bind, Option.bind]

theorem endEncodeABIValues_flux (σ : AccountMap) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    encodeABIValues? [bytes32, addr, addr, uint256]
      [endArg0Bytes32Value I, .address I.codeOwner, .address I.source,
        endUIntValue (endCashAmtWorldWord σ I)] =
      some (endCashFluxPayloadBytes σ I) := by
  have hhead : abiTupleHeadSize? [bytes32, addr, addr, uint256] = some 128 := by
    native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endCashEncodeBytes32_arg0 I hsz68, hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_this I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_source I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeUint_cashAmt σ I, hdynUint]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endCashFluxPayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_flux (σ : AccountMap) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    ABI.encodeCallWithSelector? fluxSelector [bytes32, addr, addr, uint256]
      [endArg0Bytes32Value I, .address I.codeOwner, .address I.source,
        endUIntValue (endCashAmtWorldWord σ I)] =
      some (endCashFluxEncodedCall σ I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_flux σ I hsz68]
  simp [endCashFluxEncodedCall, endCashFluxPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_flux (σ : AccountMap) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    config.externalABI.encode? "flux"
      [endArg0Bytes32Value I, .address I.codeOwner, .address I.source,
        endUIntValue (endCashAmtWorldWord σ I)] =
      some (endCashFluxEncodedCall σ I) := by
  rw [endExternalEncode_flux_branch]
  exact endEncodeCallWithSelector_flux σ I hsz68

theorem endExternalDecode_flux (out : ByteArray) :
    config.externalABI.decode? "flux" out = some [] := by
  rfl

abbrev endCashFluxBaseMem (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_9705_memory
    (mem := endRuntimeBlocks.endRuntime_block_9609_taken_memory
      (mem := solcFreePtrMem) (x1 := endArg0Word I))
    (x1 := endArg0Word I)

abbrev endCashFluxCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_9758_memory
    (mem := endCashFluxBaseMem I) (x0 := endCashAmtWorldWord σ I)
    (x1 := UInt256.ofNat I.source.val) (x2 := UInt256.ofNat I.codeOwner.val)
    (x3 := endArg0Word I) (x4 := endCashFluxSelectorWord)

abbrev endCashFluxSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) endCashFluxSelectorWord)
    (UInt256.ofNat 224)

abbrev endCashFluxMemSel (I : ExecutionEnv) : ByteArray :=
  endCashFluxSelectorEncodedWord.toByteArray.write 0 (endCashFluxBaseMem I) 128 32

abbrev endCashFluxMemIlk (I : ExecutionEnv) : ByteArray :=
  (endArg0Word I).toByteArray.write 0 (endCashFluxMemSel I) 132 32

abbrev endCashFluxMemThis (I : ExecutionEnv) : ByteArray :=
  (UInt256.land endPackCallAddrMask (UInt256.ofNat I.codeOwner.val)).toByteArray.write 0
    (endCashFluxMemIlk I) 164 32

abbrev endCashFluxMemSource (I : ExecutionEnv) : ByteArray :=
  (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val)).toByteArray.write 0
    (endCashFluxMemThis I) 196 32

abbrev endCashFluxMemFull (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (endCashAmtWorldWord σ I).toByteArray.write 0 (endCashFluxMemSource I) 228 32

theorem endCashFluxBaseMem_size (I : ExecutionEnv) :
    (endCashFluxBaseMem I).size = 96 := by
  change (twoWordHashMem (endArg0Word I) (UInt256.ofNat 15)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 15) solcFreePtrMem)).size = 96
  exact twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)

theorem endCashFluxBaseMem_read64 (I : ExecutionEnv) :
    (endCashFluxBaseMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  change (twoWordHashMem (endArg0Word I) (UInt256.ofNat 15)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 15) solcFreePtrMem)).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  exact twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)

theorem endCashFluxBaseMem_mload64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endCashFluxBaseMem I) = ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [endCashFluxBaseMem_size I]; decide)
    (endCashFluxBaseMem_read64 I)

theorem endCashFluxCallMem_eq_full (σ : AccountMap) (I : ExecutionEnv) :
    endCashFluxCallMem σ I = endCashFluxMemFull σ I := by
  unfold endCashFluxCallMem endCashFluxMemFull endCashFluxMemSource endCashFluxMemThis
    endCashFluxMemIlk endCashFluxMemSel endCashFluxSelectorEncodedWord endPackCallAddrMask
  dsimp [endRuntimeBlocks.endRuntime_block_9758_memory]
  rw [endCashFluxBaseMem_mload64 I]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)).toNat = 132
    from by native_decide]
  rw [show ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256))).toNat = 164
    from by native_decide]
  rw [show ((UInt256.ofNat 32) +
      ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)))).toNat = 196
    from by native_decide]
  rw [show ((UInt256.ofNat 32) +
      ((UInt256.ofNat 32) +
        ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256))))).toNat = 228
    from by native_decide]

theorem endCashFluxMemSel_size_ge160 (I : ExecutionEnv) :
    160 ≤ (endCashFluxMemSel I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded endCashFluxSelectorEncodedWord
    (endCashFluxBaseMem I) 128

theorem endCashFluxMemIlk_size_ge164 (I : ExecutionEnv) :
    164 ≤ (endCashFluxMemIlk I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I)
    (endCashFluxMemSel I) 132

theorem endCashFluxMemThis_size_ge196 (I : ExecutionEnv) :
    196 ≤ (endCashFluxMemThis I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.codeOwner.val))
    (endCashFluxMemIlk I) 164

theorem endCashFluxMemSource_size_ge228 (I : ExecutionEnv) :
    228 ≤ (endCashFluxMemSource I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val))
    (endCashFluxMemThis I) 196

theorem endCashFluxCallMem_size_ge260 (σ : AccountMap) (I : ExecutionEnv) :
    260 ≤ (endCashFluxCallMem σ I).size := by
  rw [endCashFluxCallMem_eq_full σ I]
  exact toByteArray_write_size_ge_off_add32_unbounded (endCashAmtWorldWord σ I)
    (endCashFluxMemSource I) 228

theorem endCashFluxSelectorEncodedWord_prefix :
    (endCashFluxSelectorEncodedWord.toByteArray).extract 0 4 = fluxSelector := by
  native_decide

theorem endCashFluxCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endCashFluxCallMem_eq_full σ I]
  change (((endCashAmtWorldWord σ I).toByteArray.write 0
      (endCashFluxMemSource I) 228 32).readWithPadding 64 32) =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap_unbounded (endCashAmtWorldWord σ I)
    (endCashFluxMemSource I) 228 64
    (by have := endCashFluxMemSource_size_ge228 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val))
    (endCashFluxMemThis I) 196 64
    (by have := endCashFluxMemThis_size_ge196 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.codeOwner.val))
    (endCashFluxMemIlk I) 164 64
    (by have := endCashFluxMemIlk_size_ge164 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg0Word I)
    (endCashFluxMemSel I) 132 64
    (by have := endCashFluxMemSel_size_ge160 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endCashFluxSelectorEncodedWord
    (endCashFluxBaseMem I) 128 64
    (by rw [endCashFluxBaseMem_size I]) (by omega)]
  exact endCashFluxBaseMem_read64 I

theorem endCashFluxCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endCashFluxCallMem σ I) = ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥ (endCashFluxCallMem σ I).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((endCashFluxCallMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endCashFluxCallMem σ I)
    (by
      have hge := endCashFluxCallMem_size_ge260 σ I
      change 64 < (endCashFluxCallMem σ I).size
      omega)
    (endCashFluxCallMem_read64 σ I)

theorem endCashFluxCallMem_readSelector (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 128 4 = fluxSelector := by
  rw [endCashFluxCallMem_eq_full σ I]
  change (((endCashAmtWorldWord σ I).toByteArray.write 0
      (endCashFluxMemSource I) 228 32).readWithPadding 128 4) = fluxSelector
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (endCashFluxMemSource_size_ge228 I) (by omega)
    (by have := endCashFluxMemSource_size_ge228 I; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (endCashFluxMemThis_size_ge196 I) (by omega)
    (by have := endCashFluxMemThis_size_ge196 I; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endCashFluxMemIlk_size_ge164 I) (by omega)
    (by have := endCashFluxMemIlk_size_ge164 I; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endCashFluxMemSel_size_ge160 I; omega) (by omega)
    (by have := endCashFluxMemSel_size_ge160 I; omega) (by decide) (by decide)]
  change ((endCashFluxSelectorEncodedWord.toByteArray.write 0
      (endCashFluxBaseMem I) 128 32).readWithPadding 128 4) = fluxSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endCashFluxSelectorEncodedWord (endCashFluxBaseMem I) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endCashFluxSelectorEncodedWord_prefix]

theorem endCashFluxCallMem_readIlk (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 132 32 =
      (endArg0Word I).toByteArray := by
  rw [endCashFluxCallMem_eq_full σ I]
  change (((endCashAmtWorldWord σ I).toByteArray.write 0
      (endCashFluxMemSource I) 228 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  rw [toByteArray_write_read_below_of_gap_unbounded (endCashAmtWorldWord σ I)
    (endCashFluxMemSource I) 228 132
    (by have := endCashFluxMemSource_size_ge228 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val))
    (endCashFluxMemThis I) 196 132
    (by have := endCashFluxMemThis_size_ge196 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.codeOwner.val))
    (endCashFluxMemIlk I) 164 132
    (by have := endCashFluxMemIlk_size_ge164 I; omega) (by omega)]
  change (((endArg0Word I).toByteArray.write 0
      (endCashFluxMemSel I) 132 32).readWithPadding 132 32) =
    (endArg0Word I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg0Word I)
    (endCashFluxMemSel I) 132

theorem endCashFluxCallMem_readThis (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 164 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [endCashFluxCallMem_eq_full σ I]
  change (((endCashAmtWorldWord σ I).toByteArray.write 0
      (endCashFluxMemSource I) 228 32).readWithPadding 164 32) =
    (UInt256.ofNat I.codeOwner.val).toByteArray
  rw [toByteArray_write_read_below_of_gap_unbounded (endCashAmtWorldWord σ I)
    (endCashFluxMemSource I) 228 164
    (by have := endCashFluxMemSource_size_ge228 I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val))
    (endCashFluxMemThis I) 196 164
    (by have := endCashFluxMemThis_size_ge196 I; omega) (by omega)]
  change (((UInt256.land endPackCallAddrMask (UInt256.ofNat I.codeOwner.val)).toByteArray.write 0
      (endCashFluxMemIlk I) 164 32).readWithPadding 164 32) =
    (UInt256.ofNat I.codeOwner.val).toByteArray
  rw [toByteArray_write_read_back_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.codeOwner.val))
    (endCashFluxMemIlk I) 164]
  rw [endPackCallAddrMask_eq_solc, endCashCodeOwnerWord_clean I]

theorem endCashFluxCallMem_readSource (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 196 32 =
      (UInt256.ofNat I.source.val).toByteArray := by
  rw [endCashFluxCallMem_eq_full σ I]
  change (((endCashAmtWorldWord σ I).toByteArray.write 0
      (endCashFluxMemSource I) 228 32).readWithPadding 196 32) =
    (UInt256.ofNat I.source.val).toByteArray
  rw [toByteArray_write_read_below_of_gap_unbounded (endCashAmtWorldWord σ I)
    (endCashFluxMemSource I) 228 196
    (by have := endCashFluxMemSource_size_ge228 I; omega) (by omega)]
  change (((UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val)).toByteArray.write 0
      (endCashFluxMemThis I) 196 32).readWithPadding 196 32) =
    (UInt256.ofNat I.source.val).toByteArray
  rw [toByteArray_write_read_back_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val))
    (endCashFluxMemThis I) 196]
  rw [endPackCallAddrMask_eq_solc, endPackSourceWord_clean I]

theorem endCashFluxCallMem_readAmt (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 228 32 =
      (endCashAmtWorldWord σ I).toByteArray := by
  rw [endCashFluxCallMem_eq_full σ I]
  change (((endCashAmtWorldWord σ I).toByteArray.write 0
      (endCashFluxMemSource I) 228 32).readWithPadding 228 32) =
    (endCashAmtWorldWord σ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endCashAmtWorldWord σ I)
    (endCashFluxMemSource I) 228

theorem endCashFluxCallMem_readCallData (σ : AccountMap) (I : ExecutionEnv) :
    (endCashFluxCallMem σ I).readWithPadding 128 132 =
      endCashFluxEncodedCall σ I := by
  have hsize := endCashFluxCallMem_size_ge260 σ I
  rw [show 132 = 4 + 128 from rfl]
  rw [byteArray_readWithPadding_split (endCashFluxCallMem σ I) 128 4 128
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 128 = 32 + 96 from rfl]
  rw [byteArray_readWithPadding_split (endCashFluxCallMem σ I) 132 32 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split (endCashFluxCallMem σ I) 164 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endCashFluxCallMem σ I) 196 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 196 + 32 = 228 by norm_num]
  rw [endCashFluxCallMem_readSelector σ I, endCashFluxCallMem_readIlk σ I,
    endCashFluxCallMem_readThis σ I, endCashFluxCallMem_readSource σ I,
    endCashFluxCallMem_readAmt σ I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endCashFluxEncodedCall, endCashFluxPayloadBytes, toByteArray_eq_toBytesBE]

theorem endCashFixHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 15).toByteArray.write 0
          ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endCashFixWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0Word I) (UInt256.ofNat 15) mem) =
    endCashFixWorldSlot I
  simp [endCashFixWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endGenericMulSuccessCond (x y : UInt256)
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

theorem endGenericMulFailCond (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.eq (UInt256.div (endGenericMulProduct x y) y) x = UInt256.ofNat 0 := by
  exact u256_eq_of_ne (by
    simpa [endGenericMulProduct] using u256_mul_div_ne_of_overflow x y hover)

theorem endX_cash_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_64 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1292 := endRuntimeBlocks.endRuntime_block_1274_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_1292 (R :=
      endRuntimeBlocks.endRuntime_block_1274_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_1274_fallthrough_stack])
    (by simpa using rd1292)

theorem endX_cash_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9609⟩
      [endArg1Word I, endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_64 (I := I) hsz68 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1296 := endRuntimeBlocks.endRuntime_block_1274_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd9609 := endRuntimeBlocks.endRuntime_block_1296
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨562⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_1274_taken_stack] using rd1296)
  have hoff : ((UInt256.ofNat 32 + (⟨4⟩ : UInt256)).toNat) = 36 := by
    native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_1296_stack, endArg1Word, endArg0Word,
      calldataWord, hoff] using rd9609⟩

theorem endX_cash_fix_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfix : endCashFixWorldWord σ I = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_cash_to_body (g := g) hsz68 hsize hreach
  have hcond :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 15).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) = UInt256.ofNat 0 := by
    rw [endCashFixHashSlot solcFreePtrMem I]
    exact hfix
  obtain ⟨_, _, rd9629⟩ := endRuntimeBlocks.endRuntime_block_9609_fallthrough
    (R := [⟨562⟩, sel]) (by simp) hcond rdBody
  exact endRuntimeBlocks.endRuntime_block_9629
    (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by simpa using rd9629)

theorem endX_cash_to_flux_setup {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfix : endCashFixWorldWord σ I ≠ ⟨0⟩)
    (hmulFit : (endArg1Word I).toNat * (endCashFixWorldWord σ I).toNat < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9758⟩
      [endCashAmtWorldWord σ I, UInt256.ofNat I.source.val, UInt256.ofNat I.codeOwner.val,
        endArg0Word I, endCashFluxSelectorWord, endPackVatTarget σ I,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]
      (endCashFluxBaseMem I)
      aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_cash_to_body (g := g) hsz68 hsize hreach
  have hcondFix :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 15).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠ UInt256.ofNat 0 := by
    rw [endCashFixHashSlot solcFreePtrMem I]
    exact hfix
  obtain ⟨_, _, rd9705⟩ := endRuntimeBlocks.endRuntime_block_9609_taken
    (R := [⟨562⟩, sel]) (by simp) hcondFix (by jump_dest) rdBody
  obtain ⟨_, _, rd10114⟩ := endRuntimeBlocks.endRuntime_block_9705
    (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_9609_taken_memory,
        endRuntimeBlocks.endRuntime_block_9705_stack, endRuntimeBlocks.endRuntime_block_9705_memory,
        endCashFixWorldWord, endCashFixWorldSlot, endCashFluxSelectorWord, endPackVatTarget,
        endPackCallAddrMask_eq_solc, u256_land_comm, endCashFixHashSlot] using rd9705)
  have rd10170 := endRuntimeBlocks.endRuntime_block_10114
    (x0 := endCashFixWorldWord σ I) (x1 := endArg1Word I)
    (R := [⟨9758⟩, UInt256.ofNat I.source.val, UInt256.ofNat I.codeOwner.val,
      endArg0Word I, endCashFluxSelectorWord, endPackVatTarget σ I,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_9705_stack, endCashFixWorldWord,
        endCashFixWorldSlot, endCashFluxSelectorWord, endPackVatTarget,
        endPackCallAddrMask_eq_solc, u256_land_comm, endCashFixHashSlot] using rd10114)
  have hcondFixNonzero :
      UInt256.isZero (endCashFixWorldWord σ I) = UInt256.ofNat 0 :=
    Reasoning.Theory.isZero_eq_zero_of_ne hfix
  have rd10180 := endRuntimeBlocks.endRuntime_block_10170_fallthrough
    (x0 := endCashFixWorldWord σ I)
    (R := [endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondFixNonzero
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10114_stack, endRayWord] using rd10170)
  have rd10194 := endRuntimeBlocks.endRuntime_block_10180_taken
    (x0 := UInt256.isZero (endCashFixWorldWord σ I)) (x1 := (⟨0⟩ : UInt256))
    (x2 := endCashFixWorldWord σ I) (x3 := endArg1Word I)
    (R := [⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hfix (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10170_fallthrough_stack] using rd10180)
  have rd10197 := endRuntimeBlocks.endRuntime_block_10194
    (x0 := endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
    (x1 := endCashFixWorldWord σ I) (x2 := endArg1Word I)
    (R := [endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I),
      endCashFixWorldWord σ I, endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10180_taken_stack, endGenericMulProduct]
        using rd10194)
  have hcondMul := endGenericMulSuccessCond
    (endArg1Word I) (endCashFixWorldWord σ I) hmulFit hfix
  have rd10108 := endRuntimeBlocks.endRuntime_block_10197_taken
    (x0 := UInt256.eq
      (UInt256.div (endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
        (endCashFixWorldWord σ I))
      (endArg1Word I))
    (R := [endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I),
      endCashFixWorldWord σ I, endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondMul (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10194_stack] using rd10197)
  have rd10139 := endRuntimeBlocks.endRuntime_block_10108
    (x0 := endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
    (x1 := endCashFixWorldWord σ I) (x2 := endArg1Word I)
    (x3 := (⟨10139⟩ : UInt256))
    (R := [endRayWord, ⟨0⟩, endCashFixWorldWord σ I, endArg1Word I,
      ⟨9758⟩, UInt256.ofNat I.source.val, UInt256.ofNat I.codeOwner.val,
      endArg0Word I, endCashFluxSelectorWord, endPackVatTarget σ I,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10197_taken_stack] using rd10108)
  have hRayNonzero : endRayWord ≠ UInt256.ofNat 0 := by
    native_decide
  have rd10146 := endRuntimeBlocks.endRuntime_block_10139_taken
    (x0 := endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
    (x1 := endRayWord)
    (R := [⟨0⟩, endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩,
      UInt256.ofNat I.source.val, UInt256.ofNat I.codeOwner.val, endArg0Word I,
      endCashFluxSelectorWord, endPackVatTarget σ I, endArg1Word I,
      endArg0Word I, ⟨562⟩, sel])
    (by simp) hRayNonzero (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rd10139)
  have rd9758 := endRuntimeBlocks.endRuntime_block_10146
    (x0 := endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
    (x1 := endRayWord) (x2 := (⟨0⟩ : UInt256))
    (x3 := endCashFixWorldWord σ I) (x4 := endArg1Word I)
    (x5 := (⟨9758⟩ : UInt256))
    (R := [UInt256.ofNat I.source.val, UInt256.ofNat I.codeOwner.val, endArg0Word I,
      endCashFluxSelectorWord, endPackVatTarget σ I, endArg1Word I, endArg0Word I,
      ⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa using rd10146)
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_10146_stack, endCashAmtWorldWord,
      endGenericRmulResult] using rd9758⟩

theorem endX_cash_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfix : endCashFixWorldWord σ I ≠ ⟨0⟩)
    (hmulFit : (endArg1Word I).toNat * (endCashFixWorldWord σ I).toNat < UInt256.size)
    (hvatNoCode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw9758, k9758, C9758, rd9758⟩ :=
    endX_cash_to_flux_setup (g := g) hsz68 hsize hfix hmulFit hreach
  obtain ⟨aw9842, k9842, C9842, rd9842⟩ :=
    endRuntimeBlocks.endRuntime_block_9758_packed
      (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) rd9758
  have hfreeBase : memLoad (UInt256.ofNat 64) (endCashFluxBaseMem I) = ⟨128⟩ :=
    endCashFluxBaseMem_mload64 I
  have hfreeCallRaw := endCashFluxCallMem_mload64 σ I
  dsimp [endCashFluxCallMem, endRuntimeBlocks.endRuntime_block_9758_memory] at hfreeCallRaw
  rw [hfreeBase] at hfreeCallRaw
  have hend :
      ((UInt256.ofNat 32) +
        ((UInt256.ofNat 32) +
          ((UInt256.ofNat 32) +
            ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)))))) =
        ⟨260⟩ := by
    native_decide
  have hlen : UInt256.sub (⟨260⟩ : UInt256) ⟨128⟩ = ⟨132⟩ := by
    native_decide
  have rd9842' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9842⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          [UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)),
            endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
            ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (endCashFluxCallMem σ I) aw9842 ByteArray.empty (cA, σ) k9842 C9842 := by
    dsimp [endRuntimeBlocks.endRuntime_block_9758_stack,
      endRuntimeBlocks.endRuntime_block_9758_memory] at rd9842
    rw [hfreeBase] at rd9842
    rw [hfreeCallRaw] at rd9842
    rw [hend] at rd9842
    rw [hlen] at rd9842
    simpa [endCashFluxCallMem, endRuntimeBlocks.endRuntime_block_9758_memory,
      hfreeBase, endPackCallAddrMask_eq_solc] using rd9842
  have hcond :
      UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) =
        UInt256.ofNat 0 := by
    rw [hvatNoCode]
    native_decide
  have rd9847 := endRuntimeBlocks.endRuntime_block_9842_fallthrough
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := [UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)),
      endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
      ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcond rd9842'
  exact endRuntimeBlocks.endRuntime_block_9847
    (R := endRuntimeBlocks.endRuntime_block_9842_fallthrough_stack
      (R := [UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)),
        endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
        ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_9842_fallthrough_stack])
    rd9847

theorem endX_cash_to_flux_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfix : endCashFixWorldWord σ I ≠ ⟨0⟩)
    (hmulFit : (endArg1Word I).toNat * (endCashFixWorldWord σ I).toNat < UInt256.size)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9853⟩
      [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
        ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel]
      (endCashFluxCallMem σ I) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨aw9758, k9758, C9758, rd9758⟩ :=
    endX_cash_to_flux_setup (g := g) hsz68 hsize hfix hmulFit hreach
  obtain ⟨aw9842, k9842, C9842, rd9842⟩ :=
    endRuntimeBlocks.endRuntime_block_9758_packed
      (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel]) (by simp) rd9758
  have hfreeBase : memLoad (UInt256.ofNat 64) (endCashFluxBaseMem I) = ⟨128⟩ :=
    endCashFluxBaseMem_mload64 I
  have hfreeCallRaw := endCashFluxCallMem_mload64 σ I
  dsimp [endCashFluxCallMem, endRuntimeBlocks.endRuntime_block_9758_memory] at hfreeCallRaw
  rw [hfreeBase] at hfreeCallRaw
  have hend :
      ((UInt256.ofNat 32) +
        ((UInt256.ofNat 32) +
          ((UInt256.ofNat 32) +
            ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)))))) =
        ⟨260⟩ := by
    native_decide
  have hlen : UInt256.sub (⟨260⟩ : UInt256) ⟨128⟩ = ⟨132⟩ := by
    native_decide
  have rd9842' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9842⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          [UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)),
            endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
            ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
            endArg1Word I, endArg0Word I, ⟨562⟩, sel])
        (endCashFluxCallMem σ I) aw9842 ByteArray.empty (cA, σ) k9842 C9842 := by
    dsimp [endRuntimeBlocks.endRuntime_block_9758_stack,
      endRuntimeBlocks.endRuntime_block_9758_memory] at rd9842
    rw [hfreeBase] at rd9842
    rw [hfreeCallRaw] at rd9842
    rw [hend] at rd9842
    rw [hlen] at rd9842
    simpa [endCashFluxCallMem, endRuntimeBlocks.endRuntime_block_9758_memory,
      hfreeBase, endPackCallAddrMask_eq_solc] using rd9842
  have hcond :
      UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw9851, k9851, C9851, rd9851⟩ :=
    endRuntimeBlocks.endRuntime_block_9842_taken_packed
      (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
      (R := [UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)),
        endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
        ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) rd9842'
  obtain ⟨aw9853, k9853, C9853, rd9853⟩ :=
    endRuntimeBlocks.endRuntime_block_9851_packed
      (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
      (R := [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩,
        ⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
        endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by simp)
      (by simpa [endRuntimeBlocks.endRuntime_block_9842_taken_stack] using rd9851)
  exact ⟨aw9853, k9853, C9853, by
    simpa [endRuntimeBlocks.endRuntime_block_9851_stack] using rd9853⟩

abbrev endCashFluxCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨260⟩, endCashFluxSelectorWord, endPackVatTarget σ I,
    endArg1Word I, endArg0Word I, ⟨562⟩, sel]

abbrev endCashFluxCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨132⟩, ⟨128⟩, ⟨0⟩] ++
    endCashFluxCallRest σ I sel

abbrev endCashFluxCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨9853⟩, stack := endCashFluxCallStack σ I sel,
    mem := endCashFluxCallMem σ I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endCashFluxCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨132⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endCashAfterFluxFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract, locals := (endCashAmtStore evm I).insert "_flux" (collapseReturns []) }

abbrev endCashAfterFluxStatusCursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨9871⟩,
    stack := endRuntimeBlocks.endRuntime_block_9855_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endCashFluxCallRest σ I sel),
    mem := endCashFluxCallMem σ I, aw := endCashFluxCallAw aw, rdata := out,
    world := world }

theorem endCashAmtWord_eq_world_of_callRel {s0 cA σ I evm}
    (h : CallStateRel s0 I (cA, σ) evm) (hsz68 : 68 ≤ I.calldata.size) :
    endCashAmtWord evm I = endCashAmtWorldWord σ I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (endCashFixSlot I)
  have hslot : endCashFixSlot I = endCashFixWorldSlot I := by
    unfold endCashFixSlot endCashFixWorldSlot
    exact endFixSlot_eq I (by omega)
  unfold endCashAmtWord endCashAmtWorldWord endCashFixWord endCashFixWorldWord
  rw [hload, hslot]

theorem endCashFluxExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hpostPresent : ∀ {args : List Value} {out : ByteArray} {evm' : EVM.State},
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat (endPackVatTarget σ I).toNat))
        "flux" 0 args (true, evm', out) →
      ∃ acc, evm'.accountMap.find? evm'.executionEnv.codeOwner = some acc) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endCashFluxCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endCashAmtStore evm I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "flux" (.intLit 0)
          [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ]
      (sequenceExit ⟨9871⟩
        (fun cur frame e =>
          frame = endCashAfterFluxFrame evm I ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          (∃ acc, e.accountMap.find? e.executionEnv.codeOwner = some acc) ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_9855_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endCashFluxCallRest σ I sel) ∧
          cur.mem = endCashFluxCallMem σ I ∧
          cur.aw = endCashFluxCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨9853⟩ = some (.GAS, .none); decide)
    (by simp) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [endArg0Bytes32Value I, .address I.codeOwner, .address I.source,
      endUIntValue (endCashAmtWorldWord σ I)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨9854⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endCashFluxCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_cash]
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
    have hamt := endCashAmtWord_eq_world_of_callRel h hsz68
    rw [endEvalCashFluxArgs]
    rw [h.env]
    change EvalResult.ok
      [endArg0Bytes32Value I, Value.address I.codeOwner, Value.address I.source,
        endUIntValue (endCashAmtWord evm I)] =
      EvalResult.ok
        [endArg0Bytes32Value I, Value.address I.codeOwner, Value.address I.source,
          endUIntValue (endCashAmtWorldWord σ I)]
    rw [hamt]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_flux σ I hsz68]
    change some (endCashFluxEncodedCall σ I) =
      some ((endCashFluxCallMem σ I).readWithPadding 128 132)
    rw [endCashFluxCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro hcall _
    rw [endExternalDecode_flux out]
    intro rd hrel
    have rd9871 := endRuntimeBlocks.endRuntime_block_9855_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endCashFluxCallRest σ I sel)
      (by simp) (by native_decide) (by jump_dest)
      (by simpa [gasCursor, callCursor, endPackCallCopyZero, endCashFluxCallStack,
        endCashFluxCallAw] using rd)
    refine ⟨.ok (endCashAfterFluxFrame evm I) evm',
      Endpoint.reached (endCashAfterFluxStatusCursor σ I sel aw out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by simpa [endCashAfterFluxStatusCursor, endCashFluxCallAw] using rd9871⟩
    · exact ⟨rfl, rfl, hrel, hpostPresent hcall, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd9862 := endRuntimeBlocks.endRuntime_block_9855_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endCashFluxCallRest σ I sel)
      (by simp) (by native_decide)
      (by simpa [gasCursor, callCursor, endPackCallCopyZero, endCashFluxCallStack,
        endCashFluxCallAw] using rd)
    exact endRuntimeBlocks.endRuntime_block_9862
      (R := endRuntimeBlocks.endRuntime_block_9855_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endCashFluxCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_9855_fallthrough_stack,
        endCashFluxCallRest])
      rd9862

abbrev endCashOutSlot (I : ExecutionEnv) : UInt256 :=
  outSlot (endArg0Bytes32Key I) (.address I.source)

abbrev endCashOutWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot (UInt256.ofNat 17) (endArg0Word I))
    (UInt256.ofNat I.source.val)

abbrev endCashBagSlot (I : ExecutionEnv) : UInt256 :=
  bagSlot (.address I.source)

abbrev endCashBagWorldSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 16) (UInt256.ofNat I.source.val)

abbrev endCashOutWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endCashOutSlot I)

abbrev endCashOutNewWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  endCashOutWord evm I + endArg1Word I

abbrev endCashOutWorldWord
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  storageRead I.codeOwner world.2 (endCashOutWorldSlot I)

abbrev endCashOutWorldNewWord
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  endArg1Word I + endCashOutWorldWord world I

abbrev endCashOutStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 (endCashOutWorldSlot I)
    (endCashOutWorldNewWord world I))

abbrev endCashOutStoredState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endCashOutSlot I)
    (endCashOutNewWord evm I)

abbrev endCashOutAfterOutWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (endCashOutStoredState evm I)
    (endCashOutStoredState evm I).executionEnv.codeOwner (endCashOutSlot I)

abbrev endCashBagAfterOutWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (endCashOutStoredState evm I)
    (endCashOutStoredState evm I).executionEnv.codeOwner (endCashBagSlot I)

abbrev endCashBagAfterOutWorldWord
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  storageRead I.codeOwner (endCashOutStoredWorld world I).2 (endCashBagWorldSlot I)

abbrev endCashAddStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "y" (endUIntValue (endArg1Word I))).insert "x"
    (.int (Int.ofNat (endCashOutWord evm I).toNat))

abbrev endCashAddZStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (endCashAddStore evm I).insert "z"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))

abbrev endCashAfterAddFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (endCashAfterFluxFrame evm I).locals.insert "outNew"
      (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) }

abbrev endCashAfterAddFrameFrom (baseEvm evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (endCashAfterFluxFrame baseEvm I).locals.insert "outNew"
      (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) }

theorem endCashOutSlot_eq (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    endCashOutSlot I = endCashOutWorldSlot I := by
  have hsz36 : 36 ≤ I.calldata.size := by omega
  unfold endCashOutSlot endCashOutWorldSlot outSlot outIlkSlot mapSlot solcMappingSlot
  rw [endArg0Bytes32_key_word I hsz36, keyValueToWord_address]
  rw [show (⟨17⟩ : UInt256) = UInt256.ofNat 17 from by native_decide]

theorem endCashBagSlot_eq (I : ExecutionEnv) :
    endCashBagSlot I = endCashBagWorldSlot I := by
  simpa [endCashBagSlot, endCashBagWorldSlot, endPackBagSlot] using
    endPackBagSlot_source I

theorem endCashAfterFluxFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterFluxFrame evm I).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endCashAmtStore evm I).insert "_flux" (collapseReturns [])).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCashAmtStore evm I) (k := "_flux") (a := "ilk")
    (collapseReturns []) (by decide)]
  exact endCashAmtStore_get_ilk evm I

theorem endCashAfterFluxFrame_getElem_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterFluxFrame evm I).locals["ilk"] = endArg0Bytes32Value I := by
  have hopt :
      (endCashAfterFluxFrame evm I).locals["ilk"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endCashAfterFluxFrame_get_ilk evm I
  have hmem : "ilk" ∈ (endCashAfterFluxFrame evm I).locals := by
    simp [endCashAfterFluxFrame, endCashAmtStore, endCashStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endCashAfterFluxFrame evm I).locals "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endCashAfterFluxFrame_raw_getElem_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
      (endUIntValue (endArg1Word I))).insert "amt"
      (endUIntValue (endCashAmtWord evm I))).insert "_flux" (collapseReturns []))["ilk"] =
      endArg0Bytes32Value I := by
  change (endCashAfterFluxFrame evm I).locals["ilk"] = endArg0Bytes32Value I
  exact endCashAfterFluxFrame_getElem_ilk evm I

theorem endCashAfterFluxFrame_get_wad (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterFluxFrame evm I).locals.get? "wad" =
      some (endUIntValue (endArg1Word I)) := by
  change (((endCashAmtStore evm I).insert "_flux" (collapseReturns [])).get? "wad") =
    some (endUIntValue (endArg1Word I))
  rw [store_get_ne (endCashAmtStore evm I) (k := "_flux") (a := "wad")
    (collapseReturns []) (by decide)]
  exact endCashAmtStore_get_wad evm I

theorem endCashAfterFluxFrame_get_out_none (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterFluxFrame evm I).locals.get? "out" = none := by
  change (((endCashAmtStore evm I).insert "_flux" (collapseReturns [])).get? "out") = none
  rw [store_get_ne (endCashAmtStore evm I) (k := "_flux") (a := "out")
    (collapseReturns []) (by decide)]
  unfold endCashAmtStore
  rw [store_get_ne (endCashStore I) (k := "amt") (a := "out")
    (endUIntValue (endCashAmtWord evm I)) (by decide)]
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
    (endUIntValue (endArg1Word I))).get? "out") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "wad") (a := "out") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "out")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endCashAfterFluxFrame_get_bag_none (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterFluxFrame evm I).locals.get? "bag" = none := by
  change (((endCashAmtStore evm I).insert "_flux" (collapseReturns [])).get? "bag") = none
  rw [store_get_ne (endCashAmtStore evm I) (k := "_flux") (a := "bag")
    (collapseReturns []) (by decide)]
  unfold endCashAmtStore
  rw [store_get_ne (endCashStore I) (k := "amt") (a := "bag")
    (endUIntValue (endCashAmtWord evm I)) (by decide)]
  change ((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
    (endUIntValue (endArg1Word I))).get? "bag") = none
  rw [store_get_ne ((∅ : Store).insert "ilk" (endArg0Bytes32Value I))
    (k := "wad") (a := "bag") (endUIntValue (endArg1Word I)) (by decide)]
  rw [store_get_ne (∅ : Store) (k := "ilk") (a := "bag")
    (endArg0Bytes32Value I) (by decide)]
  simp

theorem endCashAfterAddFrame_get_outNew (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrame evm I).locals.get? "outNew" =
      some (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) := by
  exact store_get_self (endCashAfterFluxFrame evm I).locals "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))

theorem endCashAfterAddFrame_get_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrame evm I).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endCashAfterFluxFrame evm I).locals.insert "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCashAfterFluxFrame evm I).locals (k := "outNew") (a := "ilk")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAfterFluxFrame_get_ilk evm I

theorem endCashAfterAddFrame_getElem_ilk (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrame evm I).locals["ilk"] = endArg0Bytes32Value I := by
  have hopt :
      (endCashAfterAddFrame evm I).locals["ilk"]? = some (endArg0Bytes32Value I) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endCashAfterAddFrame_get_ilk evm I
  have hmem : "ilk" ∈ (endCashAfterAddFrame evm I).locals := by
    simp [endCashAfterAddFrame, endCashAfterFluxFrame, endCashAmtStore, endCashStore,
      Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endCashAfterAddFrame evm I).locals "ilk" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endCashAfterAddFrame_raw_getElem_ilk (evm : EVM.State) (I : ExecutionEnv) :
    ((((((∅ : Store).insert "ilk" (endArg0Bytes32Value I)).insert "wad"
      (endUIntValue (endArg1Word I))).insert "amt"
      (endUIntValue (endCashAmtWord evm I))).insert "_flux" (collapseReturns [])).insert
      "outNew" (.int (Int.ofNat (endCashOutNewWord evm I).toNat)))["ilk"] =
      endArg0Bytes32Value I := by
  change (endCashAfterAddFrame evm I).locals["ilk"] = endArg0Bytes32Value I
  exact endCashAfterAddFrame_getElem_ilk evm I

theorem endCashAfterAddFrame_get_out_none (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrame evm I).locals.get? "out" = none := by
  change (((endCashAfterFluxFrame evm I).locals.insert "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))).get? "out") = none
  rw [store_get_ne (endCashAfterFluxFrame evm I).locals (k := "outNew") (a := "out")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAfterFluxFrame_get_out_none evm I

theorem endCashAfterAddFrame_get_bag_none (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrame evm I).locals.get? "bag" = none := by
  change (((endCashAfterFluxFrame evm I).locals.insert "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))).get? "bag") = none
  rw [store_get_ne (endCashAfterFluxFrame evm I).locals (k := "outNew") (a := "bag")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAfterFluxFrame_get_bag_none evm I

theorem endCashAddStore_get_x (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAddStore evm I).get? "x" =
      some (.int (Int.ofNat (endCashOutWord evm I).toNat)) := by
  exact store_get_self ((∅ : Store).insert "y" (endUIntValue (endArg1Word I)))
    "x" (.int (Int.ofNat (endCashOutWord evm I).toNat))

theorem endCashAddStore_get_y (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAddStore evm I).get? "y" =
      some (endUIntValue (endArg1Word I)) := by
  unfold endCashAddStore
  rw [store_get_ne ((∅ : Store).insert "y" (endUIntValue (endArg1Word I)))
    (k := "x") (a := "y") (.int (Int.ofNat (endCashOutWord evm I).toNat)) (by decide)]
  exact store_get_self (∅ : Store) "y" (endUIntValue (endArg1Word I))

theorem endCashAddZStore_get_z (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAddZStore evm I).get? "z" =
      some (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) := by
  exact store_get_self (endCashAddStore evm I) "z"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))

theorem endCashAddZStore_get_x (evm : EVM.State) (I : ExecutionEnv) :
    (endCashAddZStore evm I).get? "x" =
      some (.int (Int.ofNat (endCashOutWord evm I).toNat)) := by
  unfold endCashAddZStore
  rw [store_get_ne (endCashAddStore evm I) (k := "z") (a := "x")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAddStore_get_x evm I

theorem endCashOutNew_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size) :
    (endCashOutNewWord evm I).toNat =
      (endCashOutWord evm I).toNat + (endArg1Word I).toNat := by
  unfold endCashOutNewWord
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]

theorem endCashArg0ValueToKey (I : ExecutionEnv) (hsz68 : 68 ≤ I.calldata.size) :
    valueToKey? (endArg0Bytes32Value I) = some (endArg0Bytes32Key I) := by
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hlenKey : ((I.calldata.toList.drop 4).take 32).length = bytes32Width.val + 1 := by
    simpa [bytes32Width] using hlen
  simp [endArg0Bytes32Key, valueToKey?, hlenKey]

abbrev endCashOutEvalRef (I : ExecutionEnv) (usr : AccountAddress) : EvaledStorageRef :=
  { base := "out", steps := [.mindex (endArg0Bytes32Key I), .mindex (KeyValue.address usr)] }

abbrev endCashBagEvalRef (usr : AccountAddress) : EvaledStorageRef :=
  { base := "bag", steps := [.mindex (KeyValue.address usr)] }

theorem endEvalOutRef_afterFlux (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endCashAfterFluxFrame evm I) evm
        (outRef (.var "ilk") sender) =
      .ok (endCashOutEvalRef I evm.executionEnv.source) := by
  have hvar :
      evalExpr? config (endCashAfterFluxFrame evm I) evm (.var "ilk") =
        .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [endCashAfterFluxFrame_get_ilk evm I]
    simp [EvalResult.ofOption]
  have hkey := endCashArg0ValueToKey I hsz68
  have hsender :
      evalExpr? config (endCashAfterFluxFrame evm I) evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address evm.executionEnv.source) =
        some (KeyValue.address evm.executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, outRef, hvar, hkey, hsender,
    hsenderKey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalOutRef_afterAdd (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endCashAfterAddFrame evm I) evm
        (outRef (.var "ilk") sender) =
      .ok (endCashOutEvalRef I evm.executionEnv.source) := by
  have hvar :
      evalExpr? config (endCashAfterAddFrame evm I) evm (.var "ilk") =
        .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [endCashAfterAddFrame_get_ilk evm I]
    simp [EvalResult.ofOption]
  have hkey := endCashArg0ValueToKey I hsz68
  have hsender :
      evalExpr? config (endCashAfterAddFrame evm I) evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address evm.executionEnv.source) =
        some (KeyValue.address evm.executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, outRef, hvar, hkey, hsender,
    hsenderKey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalOutRef_afterAssignState (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
        (outRef (.var "ilk") sender) =
      .ok (endCashOutEvalRef I (endCashOutStoredState evm I).executionEnv.source) := by
  have hvar :
      evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
        (.var "ilk") = .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [endCashAfterAddFrame_get_ilk evm I]
    simp [EvalResult.ofOption]
  have hkey := endCashArg0ValueToKey I hsz68
  have hsender :
      evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I) sender =
        .ok (.address (endCashOutStoredState evm I).executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address (endCashOutStoredState evm I).executionEnv.source) =
        some (KeyValue.address (endCashOutStoredState evm I).executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, outRef, hvar, hkey, hsender,
    hsenderKey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalBagRef_afterAssignState (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
        (bagRef sender) =
      .ok (endCashBagEvalRef (endCashOutStoredState evm I).executionEnv.source) := by
  have hsender :
      evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I) sender =
        .ok (.address (endCashOutStoredState evm I).executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address (endCashOutStoredState evm I).executionEnv.source) =
        some (KeyValue.address (endCashOutStoredState evm I).executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, bagRef, hsender, hsenderKey,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalOutStorage_cash (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config (endCashAfterFluxFrame evm I) evm
        (.storage (outRef (.var "ilk") sender)) =
      .ok (.int (Int.ofNat (endCashOutWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := endCashOutEvalRef I evm.executionEnv.source)
    (loc := wordLoc (outSlot (endArg0Bytes32Key I)
      (KeyValue.address evm.executionEnv.source)))
    (t := .int uint256Int)
    (hbase := endCashAfterFluxFrame_get_out_none evm I)
    (her := endEvalOutRef_afterFlux evm I hsz68)
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := by
      exact endConfig_storage_out (endArg0Bytes32Key I)
        (KeyValue.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endCashOutWord, endCashOutSlot, henv]

theorem endEvalCashAddArgs (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config (endCashAfterFluxFrame evm I) evm
      [.storage (outRef (.var "ilk") sender), .var "wad"] =
      .ok [.int (Int.ofNat (endCashOutWord evm I).toNat),
        endUIntValue (endArg1Word I)] := by
  rw [evalExprs?]
  rw [endEvalOutStorage_cash evm I henv hsz68]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endCashAfterFluxFrame_get_wad evm I]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_add_cash (evm : EVM.State) (I : ExecutionEnv) :
    bindParams? addFunction.params
      [.int (Int.ofNat (endCashOutWord evm I).toNat), endUIntValue (endArg1Word I)] =
      some (endCashAddStore evm I) := by
  simp [bindParams?, addFunction, endCashAddStore, endUIntValue]

theorem endEvalAddCashExpr (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endCashAddStore evm I } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .ok (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) := by
  have hsum := endCashOutNew_toNat evm I hfit
  have hfitPow : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hnotHi :
      ¬ Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) ≥
        (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact Int.ofNat_lt.mpr hfitPow
  have haddInt :
      Int.ofNat (endCashOutWord evm I).toNat + Int.ofNat (endArg1Word I).toNat =
        Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) := by
    exact (Nat.cast_add (endCashOutWord evm I).toNat (endArg1Word I).toNat).symm
  unfold u256
  simp only [evalExpr?, endCashAddStore_get_x, endCashAddStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int,
    endUIntValue]
  rw [haddInt]
  have hcond :
      (decide (Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) < 0) ||
        decide (Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) ≥
          (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg :
        decide (Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) < 0) =
          false :=
      decide_eq_false (show
        ¬ Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) ≥
          (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [hsum]

theorem endEvalAddCashExpr_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat) :
    evalExpr? config { contract := contract, locals := endCashAddStore evm I } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .revert := by
  have hhi :
      decide (Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) ≥
        (2 : Int) ^ (256 : Nat)) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  have haddInt :
      Int.ofNat (endCashOutWord evm I).toNat + Int.ofNat (endArg1Word I).toNat =
        Int.ofNat ((endCashOutWord evm I).toNat + (endArg1Word I).toNat) := by
    exact (Nat.cast_add (endCashOutWord evm I).toNat (endArg1Word I).toNat).symm
  unfold u256
  simp only [evalExpr?, endCashAddStore_get_x, endCashAddStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int,
    endUIntValue]
  rw [haddInt, hhi]
  simp

theorem endEvalAddCashGuard (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endCashAddZStore evm I } evm
      (.binary .ge (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hsum := endCashOutNew_toNat evm I hfit
  have hgeProp :
      Int.ofNat (endCashOutWord evm I).toNat ≤
        Int.ofNat (endCashOutNewWord evm I).toNat := by
    rw [hsum]
    exact Int.ofNat_le.mpr (by omega)
  have hge :
      decide (Int.ofNat (endCashOutNewWord evm I).toNat ≥
        Int.ofNat (endCashOutWord evm I).toNat) = true := by
    exact decide_eq_true hgeProp
  simp only [evalExpr?, endCashAddZStore_get_z, endCashAddZStore_get_x,
    EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?]
  rw [hge]

theorem endAddCashFunctionOk (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endCashAddStore evm I } evm
      addFunction.body
      (.returned { contract := contract, locals := endCashAddZStore evm I } evm
        (some [.int (Int.ofNat (endCashOutNewWord evm I).toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [addFunction, endCashAddZStore] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl
        (name := "z") (ty := some uint256)
        (expr := u256 (.binary .add (.var "x") (.var "y")))
        (value := .int (Int.ofNat (endCashOutNewWord evm I).toNat))
        (endEvalAddCashExpr evm I hfit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAddCashGuard evm I hfit)) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.var "z"])
          (values := [.int (Int.ofNat (endCashOutNewWord evm I).toNat)])
          (by
            simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
              endCashAddZStore_get_z])))

theorem endAddCashFunctionRevert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat) :
    ExecFuncBody config { contract := contract, locals := endCashAddStore evm I } evm
      addFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [addFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalAddCashExpr_revert evm I hover)))

theorem endCashInternalAddOk (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size) :
    ExecStmt config (endCashAfterFluxFrame evm I) evm
      (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
      (.ok (endCashAfterAddFrame evm I) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endCashAfterAddFrame] using
    internalCallFunctionReturn
      (cfg := config) (caller := endCashAfterFluxFrame evm I)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "outNew")
      (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
      (argVals := [.int (Int.ofNat (endCashOutWord evm I).toNat),
        endUIntValue (endArg1Word I)])
      (callee := addFunction) (locals := endCashAddStore evm I)
      (calleeSolm := { contract := contract, locals := endCashAddZStore evm I })
      (value := some [.int (Int.ofNat (endCashOutNewWord evm I).toNat)])
      (endEvalCashAddArgs evm I henv hsz68)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_cash evm I)
      (endAddCashFunctionOk evm I hfit)

theorem endCashInternalAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat) :
    ExecStmt config (endCashAfterFluxFrame evm I) evm
      (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endCashAfterFluxFrame evm I) (evm := evm)
    (name := "add") (retVar := "outNew")
    (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
    (argVals := [.int (Int.ofNat (endCashOutWord evm I).toNat),
      endUIntValue (endArg1Word I)])
    (callee := addFunction) (locals := endCashAddStore evm I)
    (endEvalCashAddArgs evm I henv hsz68)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_cash evm I)
    (endAddCashFunctionRevert evm I hover)

theorem endEvalOutNew_cash (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (endCashAfterAddFrame evm I) evm (.var "outNew") =
      .ok (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) := by
  simp [evalExpr?, EvalResult.ofOption, endCashAfterAddFrame_get_outNew]

theorem endAssignOutNew_cash (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config (endCashAfterAddFrame evm I) evm
        .storage (outRef (.var "ilk") sender)
        (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) =
      .ok (endCashAfterAddFrame evm I, endCashOutStoredState evm I) := by
  let er : EvaledStorageRef :=
    endCashOutEvalRef I evm.executionEnv.source
  let loc : StorageLoc :=
    wordLoc (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
  have her : evalStorageRef config (endCashAfterAddFrame evm I) evm
      (outRef (.var "ilk") sender) = .ok er := by
    simpa [er] using endEvalOutRef_afterAdd evm I hsz68
  have hty :
      storageTypeAt? (endCashAfterAddFrame evm I).contract.storage er =
        some (.elem (.int uint256Int)) := by
    simp [er, endCashOutEvalRef, storageTypeAt?, contract, storageDecls, storageTypeStep?,
      uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simpa [er, loc, endCashOutEvalRef] using
      endConfig_storage_out (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source)
  have hstore :
      storageLocStore evm loc (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
          (endCashOutNewWord evm I)) := by
    simpa [loc, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm
        (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
        (endCashOutNewWord evm I)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endCashAfterAddFrame evm I) (evm := evm)
    (slot := outRef (.var "ilk") sender) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endCashOutNewWord evm I).toNat)
    (endCashAfterAddFrame_get_out_none evm I) her hty hloc hstore
  have hstate :
      endCashOutStoredState evm I =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
          (endCashOutNewWord evm I) := by
    unfold endCashOutStoredState endCashOutSlot
    rw [henv]
  rw [hstate]
  exact hassign

theorem endEvalOutStorage_afterAssign_cash (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
        (.storage (outRef (.var "ilk") sender)) =
      .ok (.int (Int.ofNat (endCashOutAfterOutWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := endCashOutEvalRef I (endCashOutStoredState evm I).executionEnv.source)
    (loc := wordLoc (outSlot (endArg0Bytes32Key I)
      (KeyValue.address (endCashOutStoredState evm I).executionEnv.source)))
    (t := .int uint256Int)
    (hbase := endCashAfterAddFrame_get_out_none evm I)
    (her := endEvalOutRef_afterAssignState evm I hsz68)
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_out (endArg0Bytes32Key I)
      (KeyValue.address (endCashOutStoredState evm I).executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endCashOutAfterOutWord, endCashOutSlot,
    endCashOutStoredState, storageStore_executionEnv, henv]

theorem endEvalBagStorage_afterAssign_cash (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) :
    evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
        (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat (endCashBagAfterOutWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := endCashBagEvalRef (endCashOutStoredState evm I).executionEnv.source)
    (loc := wordLoc
      (bagSlot (KeyValue.address (endCashOutStoredState evm I).executionEnv.source)))
    (t := .int uint256Int)
    (hbase := endCashAfterAddFrame_get_bag_none evm I)
    (her := endEvalBagRef_afterAssignState evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_bag
      (KeyValue.address (endCashOutStoredState evm I).executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endCashBagAfterOutWord, endCashBagSlot,
    endCashOutStoredState, storageStore_executionEnv, henv]

theorem endEvalCashFinalGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hle : (endCashOutAfterOutWord evm I).toNat ≤
      (endCashBagAfterOutWord evm I).toNat) :
    evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
      (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalOutStorage_afterAssign_cash evm I henv hsz68]
  simp only [EvalResult.bind, bind]
  rw [endEvalBagStorage_afterAssign_cash evm I henv]
  simp only [evalBinaryOp?]
  have hdec :
      decide (Int.ofNat (endCashOutAfterOutWord evm I).toNat ≤
        Int.ofNat (endCashBagAfterOutWord evm I).toNat) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr hle)
  rw [hdec]

theorem endEvalCashFinalGuard_false (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hlt : (endCashBagAfterOutWord evm I).toNat <
      (endCashOutAfterOutWord evm I).toNat) :
    evalExpr? config (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)
      (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalOutStorage_afterAssign_cash evm I henv hsz68]
  simp only [EvalResult.bind, bind]
  rw [endEvalBagStorage_afterAssign_cash evm I henv]
  simp only [evalBinaryOp?]
  have hdec :
      decide (Int.ofNat (endCashOutAfterOutWord evm I).toNat ≤
        Int.ofNat (endCashBagAfterOutWord evm I).toNat) = false := by
    exact decide_eq_false (by
      intro hle
      exact Nat.not_lt_of_ge (Int.ofNat_le.mp hle) hlt)
  rw [hdec]

theorem endCashAfterFluxSuffixOk (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size)
    (hle : (endCashOutAfterOutWord evm I).toNat ≤
      (endCashBagAfterOutWord evm I).toNat) :
    ExecBlock config (endCashAfterFluxFrame evm I) evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      (.ok (endCashAfterAddFrame evm I) (endCashOutStoredState evm I)) := by
  exact ExecBlock.consNormal (endCashInternalAddOk evm I henv hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalOutNew_cash evm I) (endAssignOutNew_cash evm I henv hsz68)) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue (endEvalCashFinalGuard_true evm I henv hsz68 hle)) <|
    ExecBlock.nil

theorem endCashAfterFluxSuffixAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat) :
    ExecBlock config (endCashAfterFluxFrame evm I) evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      .reverted := by
  exact ExecBlock.consRevert (endCashInternalAddRevert evm I henv hsz68 hover)

theorem endCashAfterFluxSuffixBoundRevert (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size)
    (hlt : (endCashBagAfterOutWord evm I).toNat <
      (endCashOutAfterOutWord evm I).toNat) :
    ExecBlock config (endCashAfterFluxFrame evm I) evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      .reverted := by
  exact ExecBlock.consNormal (endCashInternalAddOk evm I henv hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalOutNew_cash evm I) (endAssignOutNew_cash evm I henv hsz68)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse (endEvalCashFinalGuard_false evm I henv hsz68 hlt))

theorem endCashAfterAddFrameFrom_get_outNew (baseEvm evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrameFrom baseEvm evm I).locals.get? "outNew" =
      some (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) := by
  exact store_get_self (endCashAfterFluxFrame baseEvm I).locals "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))

theorem endCashAfterAddFrameFrom_get_ilk (baseEvm evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrameFrom baseEvm evm I).locals.get? "ilk" =
      some (endArg0Bytes32Value I) := by
  change (((endCashAfterFluxFrame baseEvm I).locals.insert "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))).get? "ilk") =
    some (endArg0Bytes32Value I)
  rw [store_get_ne (endCashAfterFluxFrame baseEvm I).locals (k := "outNew") (a := "ilk")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAfterFluxFrame_get_ilk baseEvm I

theorem endCashAfterAddFrameFrom_get_out_none (baseEvm evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrameFrom baseEvm evm I).locals.get? "out" = none := by
  change (((endCashAfterFluxFrame baseEvm I).locals.insert "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))).get? "out") = none
  rw [store_get_ne (endCashAfterFluxFrame baseEvm I).locals (k := "outNew") (a := "out")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAfterFluxFrame_get_out_none baseEvm I

theorem endCashAfterAddFrameFrom_get_bag_none (baseEvm evm : EVM.State) (I : ExecutionEnv) :
    (endCashAfterAddFrameFrom baseEvm evm I).locals.get? "bag" = none := by
  change (((endCashAfterFluxFrame baseEvm I).locals.insert "outNew"
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat))).get? "bag") = none
  rw [store_get_ne (endCashAfterFluxFrame baseEvm I).locals (k := "outNew") (a := "bag")
    (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) (by decide)]
  exact endCashAfterFluxFrame_get_bag_none baseEvm I

theorem endEvalOutRef_afterFluxFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endCashAfterFluxFrame baseEvm I) evm
        (outRef (.var "ilk") sender) =
      .ok (endCashOutEvalRef I evm.executionEnv.source) := by
  have hvar :
      evalExpr? config (endCashAfterFluxFrame baseEvm I) evm (.var "ilk") =
        .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [endCashAfterFluxFrame_get_ilk baseEvm I]
    simp [EvalResult.ofOption]
  have hkey := endCashArg0ValueToKey I hsz68
  have hsender :
      evalExpr? config (endCashAfterFluxFrame baseEvm I) evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address evm.executionEnv.source) =
        some (KeyValue.address evm.executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, outRef, hvar, hkey, hsender,
    hsenderKey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalOutStorage_cashFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config (endCashAfterFluxFrame baseEvm I) evm
        (.storage (outRef (.var "ilk") sender)) =
      .ok (.int (Int.ofNat (endCashOutWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := endCashOutEvalRef I evm.executionEnv.source)
    (loc := wordLoc (outSlot (endArg0Bytes32Key I)
      (KeyValue.address evm.executionEnv.source)))
    (t := .int uint256Int)
    (hbase := endCashAfterFluxFrame_get_out_none baseEvm I)
    (her := endEvalOutRef_afterFluxFrom baseEvm evm I hsz68)
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := by
      exact endConfig_storage_out (endArg0Bytes32Key I)
        (KeyValue.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endCashOutWord, endCashOutSlot, henv]

theorem endEvalCashAddArgsFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    evalExprs? config (endCashAfterFluxFrame baseEvm I) evm
      [.storage (outRef (.var "ilk") sender), .var "wad"] =
      .ok [.int (Int.ofNat (endCashOutWord evm I).toNat),
        endUIntValue (endArg1Word I)] := by
  rw [evalExprs?]
  rw [endEvalOutStorage_cashFrom baseEvm evm I henv hsz68]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endCashAfterFluxFrame_get_wad baseEvm I]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endCashInternalAddOkFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size) :
    ExecStmt config (endCashAfterFluxFrame baseEvm I) evm
      (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
      (.ok (endCashAfterAddFrameFrom baseEvm evm I) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endCashAfterAddFrameFrom] using
    internalCallFunctionReturn
      (cfg := config) (caller := endCashAfterFluxFrame baseEvm I)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "outNew")
      (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
      (argVals := [.int (Int.ofNat (endCashOutWord evm I).toNat),
        endUIntValue (endArg1Word I)])
      (callee := addFunction) (locals := endCashAddStore evm I)
      (calleeSolm := { contract := contract, locals := endCashAddZStore evm I })
      (value := some [.int (Int.ofNat (endCashOutNewWord evm I).toNat)])
      (endEvalCashAddArgsFrom baseEvm evm I henv hsz68)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_cash evm I)
      (endAddCashFunctionOk evm I hfit)

theorem endCashInternalAddRevertFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat) :
    ExecStmt config (endCashAfterFluxFrame baseEvm I) evm
      (.internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endCashAfterFluxFrame baseEvm I) (evm := evm)
    (name := "add") (retVar := "outNew")
    (args := [.storage (outRef (.var "ilk") sender), .var "wad"])
    (argVals := [.int (Int.ofNat (endCashOutWord evm I).toNat),
      endUIntValue (endArg1Word I)])
    (callee := addFunction) (locals := endCashAddStore evm I)
    (endEvalCashAddArgsFrom baseEvm evm I henv hsz68)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_cash evm I)
    (endAddCashFunctionRevert evm I hover)

theorem endEvalOutRef_afterAddFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endCashAfterAddFrameFrom baseEvm evm I) evm
        (outRef (.var "ilk") sender) =
      .ok (endCashOutEvalRef I evm.executionEnv.source) := by
  have hvar :
      evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) evm (.var "ilk") =
        .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [endCashAfterAddFrameFrom_get_ilk baseEvm evm I]
    simp [EvalResult.ofOption]
  have hkey := endCashArg0ValueToKey I hsz68
  have hsender :
      evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address evm.executionEnv.source) =
        some (KeyValue.address evm.executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, outRef, hvar, hkey, hsender,
    hsenderKey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalOutRef_afterAssignStateFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config (endCashAfterAddFrameFrom baseEvm evm I)
        (endCashOutStoredState evm I) (outRef (.var "ilk") sender) =
      .ok (endCashOutEvalRef I (endCashOutStoredState evm I).executionEnv.source) := by
  have hvar :
      evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) (endCashOutStoredState evm I)
        (.var "ilk") = .ok (endArg0Bytes32Value I) := by
    rw [evalExpr?]
    rw [endCashAfterAddFrameFrom_get_ilk baseEvm evm I]
    simp [EvalResult.ofOption]
  have hkey := endCashArg0ValueToKey I hsz68
  have hsender :
      evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I)
          (endCashOutStoredState evm I) sender =
        .ok (.address (endCashOutStoredState evm I).executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address (endCashOutStoredState evm I).executionEnv.source) =
        some (KeyValue.address (endCashOutStoredState evm I).executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, outRef, hvar, hkey, hsender,
    hsenderKey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalBagRef_afterAssignStateFrom (baseEvm evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config (endCashAfterAddFrameFrom baseEvm evm I)
        (endCashOutStoredState evm I) (bagRef sender) =
      .ok (endCashBagEvalRef (endCashOutStoredState evm I).executionEnv.source) := by
  have hsender :
      evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I)
          (endCashOutStoredState evm I) sender =
        .ok (.address (endCashOutStoredState evm I).executionEnv.source) := by
    simp [evalExpr?, sender, envValue, pure]
  have hsenderKey :
      valueToKey? (.address (endCashOutStoredState evm I).executionEnv.source) =
        some (KeyValue.address (endCashOutStoredState evm I).executionEnv.source) := by
    rfl
  simp [evalStorageRef, evalStorageRefStep, bagRef, hsender, hsenderKey,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem endEvalOutNew_cashFrom (baseEvm evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) evm (.var "outNew") =
      .ok (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) := by
  simp [evalExpr?, EvalResult.ofOption, endCashAfterAddFrameFrom_get_outNew]

theorem endAssignOutNew_cashFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config (endCashAfterAddFrameFrom baseEvm evm I) evm
        .storage (outRef (.var "ilk") sender)
        (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) =
      .ok (endCashAfterAddFrameFrom baseEvm evm I, endCashOutStoredState evm I) := by
  let er : EvaledStorageRef :=
    endCashOutEvalRef I evm.executionEnv.source
  let loc : StorageLoc :=
    wordLoc (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
  have her : evalStorageRef config (endCashAfterAddFrameFrom baseEvm evm I) evm
      (outRef (.var "ilk") sender) = .ok er := by
    simpa [er] using endEvalOutRef_afterAddFrom baseEvm evm I hsz68
  have hty :
      storageTypeAt? (endCashAfterAddFrameFrom baseEvm evm I).contract.storage er =
        some (.elem (.int uint256Int)) := by
    simp [er, endCashOutEvalRef, storageTypeAt?, contract, storageDecls, storageTypeStep?,
      uint256St]
  have hloc : config.storage.layout er = fun _ => some loc := by
    simpa [er, loc, endCashOutEvalRef] using
      endConfig_storage_out (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source)
  have hstore :
      storageLocStore evm loc (.int (Int.ofNat (endCashOutNewWord evm I).toNat)) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
          (endCashOutNewWord evm I)) := by
    simpa [loc, wordLoc, uint256Loc] using
      storageLocStore_uint256 evm
        (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
        (endCashOutNewWord evm I)
  have hassign := assignStorageRef_storage_scalar
    (cfg := config) (solm := endCashAfterAddFrameFrom baseEvm evm I) (evm := evm)
    (slot := outRef (.var "ilk") sender) (er := er)
    (ty := .elem (.int uint256Int)) (loc := loc)
    (n := Int.ofNat (endCashOutNewWord evm I).toNat)
    (endCashAfterAddFrameFrom_get_out_none baseEvm evm I) her hty hloc hstore
  have hstate :
      endCashOutStoredState evm I =
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (outSlot (endArg0Bytes32Key I) (KeyValue.address evm.executionEnv.source))
          (endCashOutNewWord evm I) := by
    unfold endCashOutStoredState endCashOutSlot
    rw [henv]
  rw [hstate]
  exact hassign

theorem endEvalOutStorage_afterAssign_cashFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) (endCashOutStoredState evm I)
        (.storage (outRef (.var "ilk") sender)) =
      .ok (.int (Int.ofNat (endCashOutAfterOutWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := endCashOutEvalRef I (endCashOutStoredState evm I).executionEnv.source)
    (loc := wordLoc (outSlot (endArg0Bytes32Key I)
      (KeyValue.address (endCashOutStoredState evm I).executionEnv.source)))
    (t := .int uint256Int)
    (hbase := endCashAfterAddFrameFrom_get_out_none baseEvm evm I)
    (her := endEvalOutRef_afterAssignStateFrom baseEvm evm I hsz68)
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_out (endArg0Bytes32Key I)
      (KeyValue.address (endCashOutStoredState evm I).executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endCashOutAfterOutWord, endCashOutSlot,
    endCashOutStoredState, storageStore_executionEnv, henv]

theorem endEvalBagStorage_afterAssign_cashFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) :
    evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) (endCashOutStoredState evm I)
        (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat (endCashBagAfterOutWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar
    (er := endCashBagEvalRef (endCashOutStoredState evm I).executionEnv.source)
    (loc := wordLoc
      (bagSlot (KeyValue.address (endCashOutStoredState evm I).executionEnv.source)))
    (t := .int uint256Int)
    (hbase := endCashAfterAddFrameFrom_get_bag_none baseEvm evm I)
    (her := endEvalBagRef_afterAssignStateFrom baseEvm evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_bag
      (KeyValue.address (endCashOutStoredState evm I).executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endCashBagAfterOutWord, endCashBagSlot,
    endCashOutStoredState, storageStore_executionEnv, henv]

theorem endEvalCashFinalGuard_trueFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hle : (endCashOutAfterOutWord evm I).toNat ≤
      (endCashBagAfterOutWord evm I).toNat) :
    evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) (endCashOutStoredState evm I)
      (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalOutStorage_afterAssign_cashFrom baseEvm evm I henv hsz68]
  simp only [EvalResult.bind, bind]
  rw [endEvalBagStorage_afterAssign_cashFrom baseEvm evm I henv]
  simp only [evalBinaryOp?]
  have hdec :
      decide (Int.ofNat (endCashOutAfterOutWord evm I).toNat ≤
        Int.ofNat (endCashBagAfterOutWord evm I).toNat) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr hle)
  rw [hdec]

theorem endEvalCashFinalGuard_falseFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hlt : (endCashBagAfterOutWord evm I).toNat <
      (endCashOutAfterOutWord evm I).toNat) :
    evalExpr? config (endCashAfterAddFrameFrom baseEvm evm I) (endCashOutStoredState evm I)
      (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalOutStorage_afterAssign_cashFrom baseEvm evm I henv hsz68]
  simp only [EvalResult.bind, bind]
  rw [endEvalBagStorage_afterAssign_cashFrom baseEvm evm I henv]
  simp only [evalBinaryOp?]
  have hdec :
      decide (Int.ofNat (endCashOutAfterOutWord evm I).toNat ≤
        Int.ofNat (endCashBagAfterOutWord evm I).toNat) = false := by
    exact decide_eq_false (by
      intro hle
      exact Nat.not_lt_of_ge (Int.ofNat_le.mp hle) hlt)
  rw [hdec]

theorem endCashAfterFluxSuffixOkFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size)
    (hle : (endCashOutAfterOutWord evm I).toNat ≤
      (endCashBagAfterOutWord evm I).toNat) :
    ExecBlock config (endCashAfterFluxFrame baseEvm I) evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      (.ok (endCashAfterAddFrameFrom baseEvm evm I) (endCashOutStoredState evm I)) := by
  exact ExecBlock.consNormal (endCashInternalAddOkFrom baseEvm evm I henv hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalOutNew_cashFrom baseEvm evm I)
        (endAssignOutNew_cashFrom baseEvm evm I henv hsz68)) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue (endEvalCashFinalGuard_trueFrom baseEvm evm I henv hsz68 hle)) <|
    ExecBlock.nil

theorem endCashAfterFluxSuffixAddRevertFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hover : UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat) :
    ExecBlock config (endCashAfterFluxFrame baseEvm I) evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      .reverted := by
  exact ExecBlock.consRevert (endCashInternalAddRevertFrom baseEvm evm I henv hsz68 hover)

theorem endCashAfterFluxSuffixBoundRevertFrom (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) (hsz68 : 68 ≤ I.calldata.size)
    (hfit : (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size)
    (hlt : (endCashBagAfterOutWord evm I).toNat <
      (endCashOutAfterOutWord evm I).toNat) :
    ExecBlock config (endCashAfterFluxFrame baseEvm I) evm
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require
          (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      .reverted := by
  exact ExecBlock.consNormal (endCashInternalAddOkFrom baseEvm evm I henv hsz68 hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalOutNew_cashFrom baseEvm evm I)
        (endAssignOutNew_cashFrom baseEvm evm I henv hsz68)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalCashFinalGuard_falseFrom baseEvm evm I henv hsz68 hlt))

theorem endCashOutHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 17).toByteArray.write 0
            ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
          ((UInt256.ofNat I.source.val).toByteArray.write 0
            ((UInt256.ofNat 17).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)
            (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endCashOutWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  have hinner :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem (endArg0Word I) (UInt256.ofNat 17) mem) =
        solcMappingSlot (UInt256.ofNat 17) (endArg0Word I) := by
    simp [twoWordHashMem_keccak_solcMappingSlot_ofNat]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (wordAt32Mem
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (twoWordHashMem (endArg0Word I) (UInt256.ofNat 17) mem))
        (wordAt0Mem (UInt256.ofNat I.source.val)
          (twoWordHashMem (endArg0Word I) (UInt256.ofNat 17) mem))) =
    endCashOutWorldSlot I
  rw [hinner]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat I.source.val)
        (solcMappingSlot (UInt256.ofNat 17) (endArg0Word I))
        (twoWordHashMem (endArg0Word I) (UInt256.ofNat 17) mem)) =
    endCashOutWorldSlot I
  simp [endCashOutWorldSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endCashBagHashSlotAfterOut (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 16).toByteArray.write 0
          ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 17).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
            ((UInt256.ofNat I.source.val).toByteArray.write 0
              ((UInt256.ofNat 17).toByteArray.write 0
                ((endArg0Word I).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32)
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endCashBagWorldSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  let innerMem := twoWordHashMem (endArg0Word I) (UInt256.ofNat 17) mem
  let outer := keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) innerMem
  let source := UInt256.ofNat I.source.val
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (wordAt32Mem (UInt256.ofNat 16)
        (wordAt32Mem outer (wordAt0Mem source innerMem))) =
    endCashBagWorldSlot I
  have hread :
      (wordAt32Mem (UInt256.ofNat 16)
          (wordAt32Mem outer (wordAt0Mem source innerMem))).readWithPadding 0 64 =
        (twoWordHashMem source (UInt256.ofNat 16) innerMem).readWithPadding 0 64 := by
    rw [byteArray_readWithPadding_split _ 0 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (wordAt32Mem_size_ge_64 (UInt256.ofNat 16) _)]
    rw [twoWordHashMem_read0_64_any]
    rw [show (wordAt32Mem (UInt256.ofNat 16)
          (wordAt32Mem outer (wordAt0Mem source innerMem))).readWithPadding 0 32 =
        UInt256.toByteArray source by
      unfold wordAt32Mem
      rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat 16)
        ((UInt256.toByteArray outer).write 0 (wordAt0Mem source innerMem) 32 32) 32 0
        (by
          change 32 ≤ (wordAt32Mem outer (wordAt0Mem source innerMem)).size
          exact le_trans (by norm_num : 32 ≤ 64)
            (wordAt32Mem_size_ge_64 outer (wordAt0Mem source innerMem)))
        (by omega)]
      rw [toByteArray_write_read_below_of_gap_unbounded outer
        (wordAt0Mem source innerMem) 32 0
        (wordAt0Mem_size_ge_32 source innerMem) (by omega)]
      exact wordAt0Mem_read0 source innerMem]
    rw [wordAt32Mem_read32_any]
  rw [keccakWord]
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 64).toNat = 64 by decide]
  rw [hread]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem source (UInt256.ofNat 16) innerMem) = endCashBagWorldSlot I
  simp [endCashBagWorldSlot, source, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endCashFinalRequireSuccessCond (outNew bagAfter : UInt256)
    (hle : outNew.toNat ≤ bagAfter.toNat) :
    UInt256.isZero (UInt256.lt bagAfter outNew) ≠ UInt256.ofNat 0 := by
  have hlt : UInt256.lt bagAfter outNew = (⟨0⟩ : UInt256) := by
    exact ult_zero hle
  rw [hlt]
  decide

theorem endCashFinalRequireFailCond (outNew bagAfter : UInt256)
    (hlt : bagAfter.toNat < outNew.toNat) :
    UInt256.isZero (UInt256.lt bagAfter outNew) = UInt256.ofNat 0 := by
  have hltw : UInt256.lt bagAfter outNew = (⟨1⟩ : UInt256) := by
    exact ult_one hlt
  rw [hltw]
  decide

theorem endX_cash_after_flux_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hfit : (endCashOutWorldWord world I).toNat + (endArg1Word I).toNat < UInt256.size)
    (hle : (endCashOutWorldNewWord world I).toNat ≤
      (endCashBagAfterOutWorldWord world I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9871⟩
      (endRuntimeBlocks.endRuntime_block_9855_taken_stack (x0 := (⟨1⟩ : UInt256))
        (R := endCashFluxCallRest preσ I sel))
      (endCashFluxCallMem preσ I) aw rdata world k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (endCashOutStoredWorld world I) ByteArray.empty := by
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_9871_packed
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨260⟩ : UInt256))
      (x2 := endCashFluxSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endArg1Word I) (x5 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endCashFluxCallRest] using rd)
  have rd10092' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
        [endArg1Word I, endCashOutWorldWord world I, ⟨9911⟩,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endRuntimeBlocks.endRuntime_block_9871_memory
          (ee := I) (mem := endCashFluxCallMem preσ I) (x5 := endArg0Word I))
        aw10092 rdata world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_9871_stack, endCashFluxCallRest,
      endCashOutWorldWord, endCashOutHashSlot] using rd10092
  have hcondAdd := endPackAddSuccessCond (endArg1Word I) (endCashOutWorldWord world I) hfit
  obtain ⟨aw10108, k10108, C10108, rd10108⟩ :=
    endRuntimeBlocks.endRuntime_block_10092_taken_packed
      (cA := world.1) (σ := world.2)
      (x0 := endArg1Word I) (x1 := endCashOutWorldWord world I)
      (R := [⟨9911⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      hcondAdd (by jump_dest) rd10092'
  obtain ⟨aw9911, k9911, C9911, rd9911⟩ :=
    endRuntimeBlocks.endRuntime_block_10108_packed
      (cA := world.1) (σ := world.2)
      (x0 := endCashOutWorldNewWord world I)
      (x1 := endArg1Word I) (x2 := endCashOutWorldWord world I)
      (x3 := (⟨9911⟩ : UInt256))
      (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endCashOutWorldNewWord, endRuntimeBlocks.endRuntime_block_10092_taken_stack]
          using rd10108)
  have hcondFinal :
      (UInt256.isZero
        (UInt256.lt
          (storageRead I.codeOwner
            (storageWrite I.codeOwner world.2
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                  ((UInt256.ofNat 17).toByteArray.write 0
                    ((endArg0Word I).toByteArray.write 0
                      (endRuntimeBlocks.endRuntime_block_9871_memory
                        (ee := I) (mem := endCashFluxCallMem preσ I)
                        (x5 := endArg0Word I))
                      (UInt256.ofNat 0).toNat 32)
                    (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
                  ((UInt256.ofNat I.source.val).toByteArray.write 0
                    ((UInt256.ofNat 17).toByteArray.write 0
                      ((endArg0Word I).toByteArray.write 0
                        (endRuntimeBlocks.endRuntime_block_9871_memory
                          (ee := I) (mem := endCashFluxCallMem preσ I)
                          (x5 := endArg0Word I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32)
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32))
              (endCashOutWorldNewWord world I))
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 16).toByteArray.write 0
                ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 17).toByteArray.write 0
                      ((endArg0Word I).toByteArray.write 0
                        (endRuntimeBlocks.endRuntime_block_9871_memory
                          (ee := I) (mem := endCashFluxCallMem preσ I)
                          (x5 := endArg0Word I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
                  ((UInt256.ofNat I.source.val).toByteArray.write 0
                    ((UInt256.ofNat 17).toByteArray.write 0
                      ((endArg0Word I).toByteArray.write 0
                        (endRuntimeBlocks.endRuntime_block_9871_memory
                          (ee := I) (mem := endCashFluxCallMem preσ I)
                          (x5 := endArg0Word I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32)
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32)
                (UInt256.ofNat 32).toNat 32)))
          (endCashOutWorldNewWord world I))) ≠ UInt256.ofNat 0 := by
    simpa [endCashOutStoredWorld, endCashBagAfterOutWorldWord,
      endCashOutHashSlot, endCashBagHashSlotAfterOut] using
      endCashFinalRequireSuccessCond
        (endCashOutWorldNewWord world I) (endCashBagAfterOutWorldWord world I) hle
  obtain ⟨aw10033, k10033, C10033, rd10033⟩ :=
    endRuntimeBlocks.endRuntime_block_9911_taken_packed
      (cA := world.1) (σ := world.2)
      (x0 := endCashOutWorldNewWord world I) (x1 := endArg1Word I)
      (x2 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      hperm hcondFinal (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rd9911)
  have rd10033' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10033⟩
        [endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endRuntimeBlocks.endRuntime_block_9911_taken_memory
          (ee := I)
          (mem := endRuntimeBlocks.endRuntime_block_9871_memory
            (ee := I) (mem := endCashFluxCallMem preσ I) (x5 := endArg0Word I))
          (x2 := endArg0Word I))
        aw10033 rdata (endCashOutStoredWorld world I) k10033 C10033 := by
    simpa [endCashOutStoredWorld, endCashOutHashSlot,
      endRuntimeBlocks.endRuntime_block_9911_taken_stack] using rd10033
  obtain ⟨aw562, k562, C562, rd562⟩ :=
    endRuntimeBlocks.endRuntime_block_10033_packed
      (cA := (endCashOutStoredWorld world I).1)
      (σ := (endCashOutStoredWorld world I).2)
      (x0 := endArg1Word I) (x1 := endArg0Word I)
      (x2 := (⟨562⟩ : UInt256)) (R := [sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      hperm (by jump_dest) rd10033'
  exact endRuntimeBlocks.endRuntime_block_562
    (cA := (endCashOutStoredWorld world I).1)
    (σ := (endCashOutStoredWorld world I).2)
    (R := [sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10033_stack] using rd562)

theorem endX_cash_after_flux_add_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hover : UInt256.size ≤ (endCashOutWorldWord world I).toNat + (endArg1Word I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9871⟩
      (endRuntimeBlocks.endRuntime_block_9855_taken_stack (x0 := (⟨1⟩ : UInt256))
        (R := endCashFluxCallRest preσ I sel))
      (endCashFluxCallMem preσ I) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_9871_packed
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨260⟩ : UInt256))
      (x2 := endCashFluxSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endArg1Word I) (x5 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endCashFluxCallRest] using rd)
  have rd10092' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
        [endArg1Word I, endCashOutWorldWord world I, ⟨9911⟩,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endRuntimeBlocks.endRuntime_block_9871_memory
          (ee := I) (mem := endCashFluxCallMem preσ I) (x5 := endArg0Word I))
        aw10092 rdata world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_9871_stack, endCashFluxCallRest,
      endCashOutWorldWord, endCashOutHashSlot] using rd10092
  have hcondAdd := endPackAddFailCond (endArg1Word I) (endCashOutWorldWord world I) hover
  obtain ⟨aw10104, k10104, C10104, rd10104⟩ :=
    endRuntimeBlocks.endRuntime_block_10092_fallthrough_packed
      (cA := world.1) (σ := world.2)
      (x0 := endArg1Word I) (x1 := endCashOutWorldWord world I)
      (R := [⟨9911⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      hcondAdd rd10092'
  exact endRuntimeBlocks.endRuntime_block_10104
    (cA := world.1) (σ := world.2)
    (R := endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack
      (x0 := endArg1Word I) (x1 := endCashOutWorldWord world I)
      (R := [⟨9911⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by
      simp [endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack])
    rd10104

theorem endX_cash_after_flux_bound_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hfit : (endCashOutWorldWord world I).toNat + (endArg1Word I).toNat < UInt256.size)
    (hlt : (endCashBagAfterOutWorldWord world I).toNat <
      (endCashOutWorldNewWord world I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨9871⟩
      (endRuntimeBlocks.endRuntime_block_9855_taken_stack (x0 := (⟨1⟩ : UInt256))
        (R := endCashFluxCallRest preσ I sel))
      (endCashFluxCallMem preσ I) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw10092, k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_9871_packed
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨260⟩ : UInt256))
      (x2 := endCashFluxSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endArg1Word I) (x5 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endCashFluxCallRest] using rd)
  have rd10092' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
        [endArg1Word I, endCashOutWorldWord world I, ⟨9911⟩,
          endArg1Word I, endArg0Word I, ⟨562⟩, sel]
        (endRuntimeBlocks.endRuntime_block_9871_memory
          (ee := I) (mem := endCashFluxCallMem preσ I) (x5 := endArg0Word I))
        aw10092 rdata world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_9871_stack, endCashFluxCallRest,
      endCashOutWorldWord, endCashOutHashSlot] using rd10092
  have hcondAdd := endPackAddSuccessCond (endArg1Word I) (endCashOutWorldWord world I) hfit
  obtain ⟨aw10108, k10108, C10108, rd10108⟩ :=
    endRuntimeBlocks.endRuntime_block_10092_taken_packed
      (cA := world.1) (σ := world.2)
      (x0 := endArg1Word I) (x1 := endCashOutWorldWord world I)
      (R := [⟨9911⟩, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      hcondAdd (by jump_dest) rd10092'
  obtain ⟨aw9911, k9911, C9911, rd9911⟩ :=
    endRuntimeBlocks.endRuntime_block_10108_packed
      (cA := world.1) (σ := world.2)
      (x0 := endCashOutWorldNewWord world I)
      (x1 := endArg1Word I) (x2 := endCashOutWorldWord world I)
      (x3 := (⟨9911⟩ : UInt256))
      (R := [endArg1Word I, endArg0Word I, ⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endCashOutWorldNewWord, endRuntimeBlocks.endRuntime_block_10092_taken_stack]
          using rd10108)
  have hcondFinal :
      (UInt256.isZero
        (UInt256.lt
          (storageRead I.codeOwner
            (storageWrite I.codeOwner world.2
              (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                  ((UInt256.ofNat 17).toByteArray.write 0
                    ((endArg0Word I).toByteArray.write 0
                      (endRuntimeBlocks.endRuntime_block_9871_memory
                        (ee := I) (mem := endCashFluxCallMem preσ I)
                        (x5 := endArg0Word I))
                      (UInt256.ofNat 0).toNat 32)
                    (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
                  ((UInt256.ofNat I.source.val).toByteArray.write 0
                    ((UInt256.ofNat 17).toByteArray.write 0
                      ((endArg0Word I).toByteArray.write 0
                        (endRuntimeBlocks.endRuntime_block_9871_memory
                          (ee := I) (mem := endCashFluxCallMem preσ I)
                          (x5 := endArg0Word I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32)
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32))
              (endCashOutWorldNewWord world I))
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 16).toByteArray.write 0
                ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
                    ((UInt256.ofNat 17).toByteArray.write 0
                      ((endArg0Word I).toByteArray.write 0
                        (endRuntimeBlocks.endRuntime_block_9871_memory
                          (ee := I) (mem := endCashFluxCallMem preσ I)
                          (x5 := endArg0Word I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32)).toByteArray.write 0
                  ((UInt256.ofNat I.source.val).toByteArray.write 0
                    ((UInt256.ofNat 17).toByteArray.write 0
                      ((endArg0Word I).toByteArray.write 0
                        (endRuntimeBlocks.endRuntime_block_9871_memory
                          (ee := I) (mem := endCashFluxCallMem preσ I)
                          (x5 := endArg0Word I))
                        (UInt256.ofNat 0).toNat 32)
                      (UInt256.ofNat 32).toNat 32)
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32)
                (UInt256.ofNat 32).toNat 32)))
          (endCashOutWorldNewWord world I))) = UInt256.ofNat 0 := by
    simpa [endCashOutStoredWorld, endCashBagAfterOutWorldWord,
      endCashOutHashSlot, endCashBagHashSlotAfterOut] using
      endCashFinalRequireFailCond
        (endCashOutWorldNewWord world I) (endCashBagAfterOutWorldWord world I) hlt
  obtain ⟨aw9957, k9957, C9957, rd9957⟩ :=
    endRuntimeBlocks.endRuntime_block_9911_fallthrough_packed
      (cA := world.1) (σ := world.2)
      (x0 := endCashOutWorldNewWord world I) (x1 := endArg1Word I)
      (x2 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      hperm hcondFinal
      (by
        simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rd9911)
  exact endRuntimeBlocks.endRuntime_block_9957
    (cA := (endCashOutStoredWorld world I).1)
    (σ := (endCashOutStoredWorld world I).2)
    (R := endRuntimeBlocks.endRuntime_block_9911_fallthrough_stack
      (x1 := endArg1Word I) (x2 := endArg0Word I) (R := [⟨562⟩, sel]))
    (by
      simp [endRuntimeBlocks.endRuntime_block_9911_fallthrough_stack])
    (by
      simpa [endCashOutStoredWorld, endCashOutHashSlot,
        endRuntimeBlocks.endRuntime_block_9911_fallthrough_stack] using rd9957)

theorem endX_cash_mul_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hfix : endCashFixWorldWord σ I ≠ ⟨0⟩)
    (hmulOverflow : UInt256.size ≤ (endArg1Word I).toNat * (endCashFixWorldWord σ I).toNat)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_cash_to_body (g := g) hsz68 hsize hreach
  have hcondFix :
      storageRead I.codeOwner σ
          (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
            ((UInt256.ofNat 15).toByteArray.write 0
              ((endArg0Word I).toByteArray.write 0 solcFreePtrMem
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32)) ≠ UInt256.ofNat 0 := by
    rw [endCashFixHashSlot solcFreePtrMem I]
    exact hfix
  obtain ⟨_, _, rd9705⟩ := endRuntimeBlocks.endRuntime_block_9609_taken
    (R := [⟨562⟩, sel]) (by simp) hcondFix (by jump_dest) rdBody
  obtain ⟨_, _, rd10114⟩ := endRuntimeBlocks.endRuntime_block_9705
    (x0 := endArg1Word I) (x1 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_9609_taken_memory,
        endRuntimeBlocks.endRuntime_block_9705_stack, endRuntimeBlocks.endRuntime_block_9705_memory,
        endCashFixWorldWord, endCashFixWorldSlot, endCashFluxSelectorWord, endPackVatTarget,
        endPackCallAddrMask_eq_solc, u256_land_comm, endCashFixHashSlot] using rd9705)
  have rd10170 := endRuntimeBlocks.endRuntime_block_10114
    (x0 := endCashFixWorldWord σ I) (x1 := endArg1Word I)
    (R := [⟨9758⟩, UInt256.ofNat I.source.val, UInt256.ofNat I.codeOwner.val,
      endArg0Word I, endCashFluxSelectorWord, endPackVatTarget σ I,
      endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_9705_stack, endCashFixWorldWord,
        endCashFixWorldSlot, endCashFluxSelectorWord, endPackVatTarget,
        endPackCallAddrMask_eq_solc, u256_land_comm, endCashFixHashSlot] using rd10114)
  have hcondFixNonzero :
      UInt256.isZero (endCashFixWorldWord σ I) = UInt256.ofNat 0 :=
    Reasoning.Theory.isZero_eq_zero_of_ne hfix
  have rd10180 := endRuntimeBlocks.endRuntime_block_10170_fallthrough
    (x0 := endCashFixWorldWord σ I)
    (R := [endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondFixNonzero
    (by simpa [endRuntimeBlocks.endRuntime_block_10114_stack, endRayWord] using rd10170)
  have rd10194 := endRuntimeBlocks.endRuntime_block_10180_taken
    (x0 := UInt256.isZero (endCashFixWorldWord σ I)) (x1 := (⟨0⟩ : UInt256))
    (x2 := endCashFixWorldWord σ I) (x3 := endArg1Word I)
    (R := [⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hfix (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10170_fallthrough_stack] using rd10180)
  have rd10197 := endRuntimeBlocks.endRuntime_block_10194
    (x0 := endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
    (x1 := endCashFixWorldWord σ I) (x2 := endArg1Word I)
    (R := [endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I),
      endCashFixWorldWord σ I, endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10180_taken_stack, endGenericMulProduct]
        using rd10194)
  have hcondMul := endGenericMulFailCond
    (endArg1Word I) (endCashFixWorldWord σ I) hmulOverflow
  have rd10202 := endRuntimeBlocks.endRuntime_block_10197_fallthrough
    (x0 := UInt256.eq
      (UInt256.div (endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I))
        (endCashFixWorldWord σ I))
      (endArg1Word I))
    (R := [endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I),
      endCashFixWorldWord σ I, endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
      endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
      UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
      endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondMul
    (by simpa [endRuntimeBlocks.endRuntime_block_10194_stack] using rd10197)
  exact endRuntimeBlocks.endRuntime_block_10202
    (R := endRuntimeBlocks.endRuntime_block_10197_fallthrough_stack
      (R := [endGenericMulProduct (endArg1Word I) (endCashFixWorldWord σ I),
        endCashFixWorldWord σ I, endArg1Word I, ⟨10139⟩, endRayWord, ⟨0⟩,
        endCashFixWorldWord σ I, endArg1Word I, ⟨9758⟩, UInt256.ofNat I.source.val,
        UInt256.ofNat I.codeOwner.val, endArg0Word I, endCashFluxSelectorWord,
        endPackVatTarget σ I, endArg1Word I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_10197_fallthrough_stack])
    rd10202

theorem endCashOutWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endCashOutWord evm I = endCashOutWorldWord world I := by
  have hload := endPackRawSlotLoad_eq_of_callRel h (endCashOutSlot I)
  have hslot := endCashOutSlot_eq I hsz68
  unfold endCashOutWord endCashOutWorldWord
  rw [hload, hslot]

theorem endCashOutNewWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size) :
    endCashOutNewWord evm I = endCashOutWorldNewWord world I := by
  have hOut := endCashOutWord_eq_world_of_callRel h hsz68
  simp [endCashOutNewWord, endCashOutWorldNewWord, hOut, u256_add_comm]

theorem endCashOutAfterOutWord_eq_new_of_present (evm : EVM.State) (I : ExecutionEnv)
    {acc : Account}
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc) :
    endCashOutAfterOutWord evm I = endCashOutNewWord evm I := by
  unfold endCashOutAfterOutWord endCashOutStoredState
  rw [storageStore_executionEnv]
  exact storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
    (endCashOutSlot I) (endCashOutNewWord evm I)

theorem endCashBagAfterOutWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) (hsz68 : 68 ≤ I.calldata.size)
    (hvalue : endCashOutNewWord evm I = endCashOutWorldNewWord world I) :
    endCashBagAfterOutWord evm I = endCashBagAfterOutWorldWord world I := by
  have hstored :=
    h.storageStore_codeOwner (endCashOutSlot I) (endCashOutNewWord evm I)
  have hload := endPackRawSlotLoad_eq_of_callRel hstored (endCashBagSlot I)
  have houtSlot := endCashOutSlot_eq I hsz68
  have hbagSlot := endCashBagSlot_eq I
  simpa [endCashBagAfterOutWord, endCashBagAfterOutWorldWord, endCashOutStoredState,
    endCashOutStoredWorld, endCashBagSlot, endCashBagWorldSlot, hbagSlot, houtSlot,
    storageWrite, hvalue] using hload

theorem endCashFixWord_init_eq {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsz68 : 68 ≤ I.calldata.size) :
    endCashFixWord (initState cA gh bl σ σ₀ g A I) I =
      endCashFixWorldWord σ I := by
  have hslot : endCashFixSlot I = endCashFixWorldSlot I := by
    unfold endCashFixSlot endCashFixWorldSlot
    exact endFixSlot_eq I (by omega)
  simp [endCashFixWord, endCashFixWorldWord, hslot, initState, Solm.EVM.storageLoad,
    State.lookupAccount, storageRead, Account.lookupStorage]

theorem endCashCurrentAccountPresent_of_fix_ne (evm : EVM.State) (I : ExecutionEnv)
    (hfix : endCashFixWord evm I ≠ ⟨0⟩) :
    ∃ acc, evm.accountMap.find? evm.executionEnv.codeOwner = some acc := by
  unfold endCashFixWord Solm.EVM.storageLoad State.lookupAccount at hfix
  cases hacc : evm.accountMap.find? evm.executionEnv.codeOwner with
  | none =>
      simp [hacc, Option.option] at hfix
  | some acc =>
      exact ⟨acc, rfl⟩

theorem endCashAfterFluxSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {baseEvm : EVM.State}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨9871⟩
      (fun cur frame e =>
        frame = endCashAfterFluxFrame baseEvm I ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        (∃ acc, e.accountMap.find? e.executionEnv.codeOwner = some acc) ∧
        cur.stack =
          endRuntimeBlocks.endRuntime_block_9855_taken_stack (x0 := (⟨1⟩ : UInt256))
            (R := endCashFluxCallRest σ I sel) ∧
        cur.mem = endCashFluxCallMem σ I ∧
        cur.aw = endCashFluxCallAw aw)
      [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
        .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
        .require (.binary .le (.storage (outRef (.var "ilk") sender)) (.storage (bagRef sender))) ]
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hpresent, hstack, hmem, _haw⟩
  rcases hpresent with ⟨acc, hacc⟩
  cases hframe
  have hOutEq := endCashOutWord_eq_world_of_callRel hrel hsz68
  have hNewEq := endCashOutNewWord_eq_world_of_callRel hrel hsz68
  have hAfterOutEq : endCashOutAfterOutWord evm I = endCashOutWorldNewWord cur.world I :=
    (endCashOutAfterOutWord_eq_new_of_present evm I hacc).trans hNewEq
  have hBagEq := endCashBagAfterOutWord_eq_world_of_callRel hrel hsz68 hNewEq
  by_cases hfit :
      (endCashOutWorldWord cur.world I).toNat + (endArg1Word I).toNat < UInt256.size
  · have hfitSource :
        (endCashOutWord evm I).toNat + (endArg1Word I).toNat < UInt256.size := by
      simpa [hOutEq] using hfit
    by_cases hle :
        (endCashOutWorldNewWord cur.world I).toNat ≤
          (endCashBagAfterOutWorldWord cur.world I).toNat
    · have hleSource :
          (endCashOutAfterOutWord evm I).toNat ≤
            (endCashBagAfterOutWord evm I).toNat := by
        simpa [hAfterOutEq, hBagEq] using hle
      have hsource :=
        endCashAfterFluxSuffixOkFrom baseEvm evm I hrel.env hsz68 hfitSource hleSource
      have rdret := endX_cash_after_flux_success
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preσ := σ) (sel := sel) (aw := cur.aw)
        (rdata := cur.rdata) (k := k) (C := C) (world := cur.world)
        hperm hfit hle
        (by
          simpa [hpc, hstack, hmem] using rd)
      have hstored :=
        hrel.storageStore_codeOwner (endCashOutSlot I) (endCashOutNewWord evm I)
      exact BlockProgress.ofRDret hsource rdret
        (by
          simpa [endCashOutStoredWorld] using hstored.created.symm)
        (by
          simpa [endCashOutStoredWorld, storageWrite, hNewEq, endCashOutSlot_eq I hsz68]
            using hstored.accounts)
        abiVoidFallthrough
    · have hltWorld :
          (endCashBagAfterOutWorldWord cur.world I).toNat <
            (endCashOutWorldNewWord cur.world I).toNat := by
        omega
      have hltSource :
          (endCashBagAfterOutWord evm I).toNat <
            (endCashOutAfterOutWord evm I).toNat := by
        simpa [hAfterOutEq, hBagEq] using hltWorld
      have hsource :=
        endCashAfterFluxSuffixBoundRevertFrom baseEvm evm I hrel.env hsz68
          hfitSource hltSource
      have hrev := endX_cash_after_flux_bound_fail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preσ := σ) (sel := sel) (aw := cur.aw)
        (rdata := cur.rdata) (k := k) (C := C) (world := cur.world)
        hperm hfit hltWorld
        (by
          simpa [hpc, hstack, hmem] using rd)
      exact BlockProgress.ofRDrev hsource hrev
  · have hoverWorld :
        UInt256.size ≤ (endCashOutWorldWord cur.world I).toNat + (endArg1Word I).toNat := by
      omega
    have hoverSource :
        UInt256.size ≤ (endCashOutWord evm I).toNat + (endArg1Word I).toNat := by
      simpa [hOutEq] using hoverWorld
    have hsource :=
      endCashAfterFluxSuffixAddRevertFrom baseEvm evm I hrel.env hsz68 hoverSource
    have hrev := endX_cash_after_flux_add_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := σ) (sel := sel) (aw := cur.aw)
      (rdata := cur.rdata) (k := k) (C := C) (world := cur.world)
      hoverWorld
      (by
        simpa [hpc, hstack, hmem] using rd)
    exact BlockProgress.ofRDrev hsource hrev

theorem endCashBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 31))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1274⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 31 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some cashTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 31 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some cashTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (cashTransition.params.map Param.name) (transitionSignature cashTransition).paramTypes
        I.calldata = some (endCashStore I) := by
      simpa [config, cashTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_cash_ok (I := I) hsz68
    have hFixWord :
        endCashFixWorldWord σ_evm I = endCashFixWorldWord σ_solm I := by
      simpa [endCashFixWorldWord, storageRead] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endCashFixWorldSlot I) ⟨0⟩
    by_cases hfixSolm : endCashFixWorldWord σ_solm I = ⟨0⟩
    · have hfixEvm : endCashFixWorldWord σ_evm I = ⟨0⟩ :=
        hFixWord.trans hfixSolm
      have hfixSrc :
          endCashFixWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = ⟨0⟩ := by
        rw [endCashFixWord_init_eq hsz68]
        exact hfixSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endCashStore I) cashTransition.body .reverted := by
        simpa [initState] using
          endCashBodyFixFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hsz68 hfixSrc
      exact (endX_cash_fix_fail (g := Sat256.ofUInt256 g) hsz68 hsize hfixEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hfixEvm : endCashFixWorldWord σ_evm I ≠ ⟨0⟩ := by
        intro hbad
        exact hfixSolm (hFixWord.symm.trans hbad)
      have hfixSrc :
          endCashFixWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I ≠ ⟨0⟩ := by
        rw [endCashFixWord_init_eq hsz68]
        exact hfixSolm
      by_cases hmulFit :
          (endArg1Word I).toNat * (endCashFixWorldWord σ_solm I).toNat < UInt256.size
      · have hmulFitEvm :
            (endArg1Word I).toNat * (endCashFixWorldWord σ_evm I).toNat < UInt256.size := by
          simpa [hFixWord] using hmulFit
        have hmulFitSrc :
            (endArg1Word I).toNat *
                (endCashFixWord
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat <
              UInt256.size := by
          simpa [endCashFixWord_init_eq hsz68] using hmulFit
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
                (endCashStore I) cashTransition.body .reverted := by
            simpa [initState] using
              endCashBodyVatNoCode
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hsz68 hfixSrc hmulFitSrc hvatNoCodeSrc
          exact (endX_cash_vat_no_code (g := Sat256.ofUInt256 g) hsz68 hsize
              hfixEvm hmulFitEvm hvatNoCodeEvm hreach)
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
            endX_cash_to_flux_call (g := Sat256.ofUInt256 g)
              hsz68 hsize hfixEvm hmulFitEvm hvatNoCodeEvm hreach
          have hprefix :=
            endCashBodyPrefixOk
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz68 hfixSrc hmulFitSrc hvatCodeSrc
          have hpostRel :
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
                (cA, σ_evm)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
            CallStateRel.initState hAccounts
          have hprePresent :
              ∃ acc,
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
                    some acc :=
            endCashCurrentAccountPresent_of_fix_ne
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I hfixSrc
          have hpostPresent : ∀ {args : List Value} {out : ByteArray} {evm' : EVM.State},
              typedCallViaEVM config
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (EVM.address (AccountAddress.ofNat (endPackVatTarget σ_evm I).toNat))
                "flux" 0 args (true, evm', out) →
              ∃ acc, evm'.accountMap.find? evm'.executionEnv.codeOwner = some acc := by
            intro args out evm' hcall
            rcases hprePresent with ⟨acc, hacc⟩
            exact typedCallViaEVM_success_preserves_codeOwner_present hacc hcall
          have htail :
              BlockRefinesFrom endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) config
                (endCashFluxCallCursor cA σ_evm I sel awCall ByteArray.empty)
                kCall CCall
                { contract := contract,
                  locals :=
                    endCashAmtStore
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (fun cur _ e =>
                  CallStateRel
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    I cur.world e)
                ([ .externalCall (.storage vatRef) "flux" (.intLit 0)
                    [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ] ++
                  [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
                    .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
                    .require
                      (.binary .le (.storage (outRef (.var "ilk") sender))
                        (.storage (bagRef sender))) ])
                (runtimeExit (.abi [])) := by
            refine BlockRefinesFrom.seqOrExit
              (endCashFluxExternalCallRefines
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                (aw := awCall) (rdata := ByteArray.empty) (k := kCall)
                (C := CCall)
                (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                hperm hsz68 hpostPresent) ?_
            exact endCashAfterFluxSuffixRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) hperm hsz68
          have hprogress :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endCashStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                ((nonpayable ++
                  [ .require (.binary .ne (.storage (fixRef (.var "ilk"))) (.intLit 0)),
                    .internalCall "rmul" [.var "wad", .storage (fixRef (.var "ilk"))] "amt",
                    .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]) ++
                  ([ .externalCall (.storage vatRef) "flux" (.intLit 0)
                      [.var "ilk", thisAddr, sender, .var "amt"] "_flux" ] ++
                    [ .internalCall "add" [.storage (outRef (.var "ilk") sender), .var "wad"] "outNew",
                      .assign .storage (outRef (.var "ilk") sender) (.var "outNew"),
                      .require
                        (.binary .le (.storage (outRef (.var "ilk") sender))
                          (.storage (bagRef sender))) ]))
                (runtimeExit (.abi [])) :=
            BlockProgress.seqOfRD
              (R := fun cur _ e =>
                CallStateRel
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  I cur.world e)
              hprefix
              (by
                simpa [endCashFluxCallCursor] using rdCall)
              hpostRel
              htail
          have hprogressBody :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endCashStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                cashTransition.body (runtimeExit (.abi [])) := by
            simpa [cashTransition, checkedExternalCallStmts, List.append_assoc] using hprogress
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
      · have hmulOverflow :
            UInt256.size ≤
              (endArg1Word I).toNat * (endCashFixWorldWord σ_solm I).toNat := by
          omega
        have hmulOverflowEvm :
            UInt256.size ≤
              (endArg1Word I).toNat * (endCashFixWorldWord σ_evm I).toNat := by
          simpa [hFixWord] using hmulOverflow
        have hmulOverflowSrc :
            UInt256.size ≤
              (endArg1Word I).toNat *
                (endCashFixWord
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat := by
          simpa [endCashFixWord_init_eq hsz68] using hmulOverflow
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endCashStore I) cashTransition.body .reverted := by
          simpa [initState] using
            endCashBodyMulFail
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hsz68 hfixSrc hmulOverflowSrc
        exact (endX_cash_mul_fail (g := Sat256.ofUInt256 g) hsz68 hsize
            hfixEvm hmulOverflowEvm hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 68 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (cashTransition.params.map Param.name) (transitionSignature cashTransition).paramTypes
        I.calldata = none := by
      simpa [config, cashTransition, transitionSignature, bytes32, uint256] using
        endDecode_legacyBytes32_uint256_cash_none_short (I := I) hsz4 hshort
    exact (endX_cash_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
