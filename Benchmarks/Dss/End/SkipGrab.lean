import Benchmarks.Dss.End.SkipAfterYank

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)`: final `vat.grab` suffix -/

theorem endSkipAfterArtNewFrame_get_vat_none (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "vat" = none := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "vat") = none
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "vat")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  change (((endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids)).get? "vat") = none
  rw [store_get_ne (endSkipAfterYankFrame I outCat outVat outBids).locals
    (k := "art") (a := "vat") (endSkipArtValue outVat outBids) (by decide)]
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "vat") = none
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "vat") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "vat") = none
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "vat") (collapseReturns []) (by decide)]
  exact endSkipAfterSuck2Frame_get_vat_none I outCat outVat outBids

theorem endSkipAfterArtNewFrame_get_vow_none (evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    (endSkipAfterArtNewFrame evm I outCat outVat outBids).locals.get? "vow" = none := by
  change (((endSkipAfterArtFrame I outCat outVat outBids).locals.insert "ArtNew"
      (endUIntValue (endSkipArtNewWord evm I outVat outBids))).get? "vow") = none
  rw [store_get_ne (endSkipAfterArtFrame I outCat outVat outBids).locals
    (k := "ArtNew") (a := "vow")
    (endUIntValue (endSkipArtNewWord evm I outVat outBids)) (by decide)]
  change (((endSkipAfterYankFrame I outCat outVat outBids).locals.insert "art"
      (endSkipArtValue outVat outBids)).get? "vow") = none
  rw [store_get_ne (endSkipAfterYankFrame I outCat outVat outBids).locals
    (k := "art") (a := "vow") (endSkipArtValue outVat outBids) (by decide)]
  change (((endSkipAfterHopeFrame I outCat outVat outBids).locals.insert "_yank"
      (collapseReturns [])).get? "vow") = none
  rw [store_get_ne (endSkipAfterHopeFrame I outCat outVat outBids).locals
    (k := "_yank") (a := "vow") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck2Frame I outCat outVat outBids).locals.insert "_hope"
      (collapseReturns [])).get? "vow") = none
  rw [store_get_ne (endSkipAfterSuck2Frame I outCat outVat outBids).locals
    (k := "_hope") (a := "vow") (collapseReturns []) (by decide)]
  change (((endSkipAfterSuck1Frame I outCat outVat outBids).locals.insert "_suck2"
      (collapseReturns [])).get? "vow") = none
  rw [store_get_ne (endSkipAfterSuck1Frame I outCat outVat outBids).locals
    (k := "_suck2") (a := "vow") (collapseReturns []) (by decide)]
  exact endSkipAfterSuck1Frame_get_vow_none I outCat outVat outBids

theorem endEvalVatAddress_skipAfterArtNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids).locals)
    (evm := evm) (slot := vatRef) (er := { base := "vat", steps := [] })
    (wordSlot := UInt256.ofNat 1)
    (endSkipAfterArtNewFrame_get_vat_none baseEvm I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vat)

theorem endEvalVowAddress_skipAfterArtNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
        vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  unfold vowAddr
  exact endEvalAddressSlot_cage
    (locals := (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids).locals)
    (evm := evm) (slot := vowRef) (er := { base := "vow", steps := [] })
    (wordSlot := UInt256.ofNat 4)
    (endSkipAfterArtNewFrame_get_vow_none baseEvm I outCat outVat outBids)
    (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
    (by decide)
    (by exact endConfig_storage_vow)

theorem endEvalVatExtCodeSize_skipAfterArtNew (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_skipAfterArtNew baseEvm evm I outCat outVat outBids]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat) <;> rfl

theorem endEvalVatCodeGuard_skipAfterArtNew_false (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skipAfterArtNew baseEvm evm I outCat outVat outBids,
    hvatNoCode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_skipAfterArtNew_true (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_skipAfterArtNew baseEvm evm I outCat outVat outBids]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hvatCode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endEvalSkipUsrVarAfterAdd (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (.var "usr") = .ok (endSkipUsrValue outBids) := by
  rw [evalExpr?]
  rw [endSkipAfterArtNewFrame_get_usr baseEvm I outCat outVat outBids]
  rfl

theorem endEvalSkipCastLotAfterAdd (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (asInt256 (.var "lot")) =
      .ok (.int (Int.ofNat (endSkipBidsLotWord outBids).toNat)) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids)
        evm (.var "lot")
      EvalResult.ofOption EvalError.typeError (castValue? value int256St)) =
    .ok (.int (Int.ofNat (endSkipBidsLotWord outBids).toNat))
  rw [endEvalSkipLotVarAfterAdd baseEvm evm I outCat outVat outBids]
  simp [int256St, castValue?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    endSkipLotValue, endUIntValue]

theorem endEvalSkipCastArtAfterAdd (baseEvm evm : EVM.State)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (asInt256 (.var "art")) =
      .ok (.int (Int.ofNat (endSkipArtWord outVat outBids).toNat)) := by
  unfold asInt256
  rw [Solm.evalExpr?.eq_def]
  change (do
      let value ← evalExpr? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids)
        evm (.var "art")
      EvalResult.ofOption EvalError.typeError (castValue? value int256St)) =
    .ok (.int (Int.ofNat (endSkipArtWord outVat outBids).toNat))
  rw [endEvalSkipArtVarAfterAdd baseEvm evm I outCat outVat outBids]
  simp [int256St, castValue?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    endSkipArtValue, endUIntValue]

theorem endEvalSkipGrabArgs (baseEvm evm : EVM.State) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) :
    evalExprs? config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")] =
    .ok [endArg0Bytes32Value I, endSkipUsrValue outBids,
      .address evm.executionEnv.codeOwner,
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat),
      .int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
      .int (Int.ofNat (endSkipArtWord outVat outBids).toNat)] := by
  simp [evalExprs?, evalExpr?, thisAddr, envValue, EvalResult.bind,
    EvalResult.ofOption, bind, pure, endEvalSkipIlkVarAfterAdd,
    endEvalSkipUsrVarAfterAdd, endEvalVowAddress_skipAfterArtNew,
    endEvalSkipCastLotAfterAdd, endEvalSkipCastArtAfterAdd]

def endSkipGrabPayloadBytes (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outBids : ByteArray) : List UInt8 :=
  (((((EVM.Word.toBytesBE (endArg0Word I) ++
      EVM.Word.toBytesBE (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids))) ++
      EVM.Word.toBytesBE (UInt256.ofNat I.codeOwner.val)) ++
      EVM.Word.toBytesBE (endPackVowTarget postσ I)) ++
      EVM.Word.toBytesBE (endSkipBidsLotWord outBids)) ++
      EVM.Word.toBytesBE (endSkipArtWord outVat outBids))

def endSkipGrabEncodedCall (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outBids : ByteArray) : ByteArray :=
  grabSelector ++ ⟨(endSkipGrabPayloadBytes postσ I outVat outBids).toArray⟩

theorem endEncodeABIValues_grab_skip (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    encodeABIValues? [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, endSkipUsrValue outBids, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
        .int (Int.ofNat (endSkipArtWord outVat outBids).toNat)] =
      some (endSkipGrabPayloadBytes postσ I outVat outBids) := by
  have hhead : abiTupleHeadSize? [bytes32, addr, addr, addr, int256, int256] =
      some 192 := by native_decide
  have hdynBytes : isDynamicABIType bytes32 = false := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynInt : isDynamicABIType int256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeBytes32_arg0 I (by omega : 36 ≤ I.calldata.size), hdynBytes]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [show encodeABIValue? addr (endSkipUsrValue outBids) =
      some (EVM.Word.toBytesBE
        (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids))) by
    exact endEncodeAddress_maskedWord (endSkipBidsUsrWord outBids), hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_this_skim I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow postσ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_posWord (endSkipBidsLotWord outBids) hlot, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeInt256_posWord (endSkipArtWord outVat outBids) hart, hdynInt]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endSkipGrabPayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_grab_skip (postσ : AccountMap)
    (I : ExecutionEnv) (outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    ABI.encodeCallWithSelector? grabSelector [bytes32, addr, addr, addr, int256, int256]
      [endArg0Bytes32Value I, endSkipUsrValue outBids, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
        .int (Int.ofNat (endSkipArtWord outVat outBids).toNat)] =
      some (endSkipGrabEncodedCall postσ I outVat outBids) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_grab_skip postσ I outVat outBids hsz68 hlot hart]
  simp [endSkipGrabEncodedCall, endSkipGrabPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_grab_skip (postσ : AccountMap) (I : ExecutionEnv)
    (outVat outBids : ByteArray) (hsz68 : 68 ≤ I.calldata.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
      [endArg0Bytes32Value I, endSkipUsrValue outBids, .address I.codeOwner,
        .address (AccountAddress.ofNat (endPackVowTarget postσ I).toNat),
        .int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
        .int (Int.ofNat (endSkipArtWord outVat outBids).toNat)] =
      some (endSkipGrabEncodedCall postσ I outVat outBids) := by
  rw [endExternalEncode_grab_branch]
  exact endEncodeCallWithSelector_grab_skip postσ I outVat outBids hsz68 hlot hart

abbrev endSkipGrabSelectorWord : UInt256 := endFreeGrabSelectorWord

abbrev endSkipGrabSelectorEncodedWord : UInt256 := endFreeGrabSelectorEncodedWord

theorem endSkipArtHashMem_size (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids).size =
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
  have hbase : 64 ≤
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
    rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  simpa [endSkipArtHashMem, endRuntimeBlocks.endRuntime_block_4167_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 14) hbase

theorem endSkipArtHashMem_read64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hbase : 96 ≤
      (endSkipYankCallMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
    rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  have hread := endSkipYankCallMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  simpa [endSkipArtHashMem, endRuntimeBlocks.endRuntime_block_4167_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 14) hbase hread

theorem endSkipAfterArtStoreMem_size (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids).size =
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
  have hbase : 64 ≤
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
    rw [endSkipArtHashMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  simpa [endSkipAfterArtStoreMem, endRuntimeBlocks.endRuntime_block_4197_fallthrough_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_size_of_ge64 (endArg0Word I) (UInt256.ofNat 14) hbase

theorem endSkipAfterArtStoreMem_read64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hbase : 96 ≤
      (endSkipArtHashMem preSuck1σ preSuck2σ I outCat outVat outBids).size := by
    rw [endSkipArtHashMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
    omega
  have hread := endSkipArtHashMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256
  simpa [endSkipAfterArtStoreMem, endRuntimeBlocks.endRuntime_block_4197_fallthrough_memory,
    twoWordHashMem, wordAt0Mem, wordAt32Mem] using
    twoWordHashMem_read64_of_ge96 (endArg0Word I) (UInt256.ofNat 14) hbase hread

theorem endSkipAfterArtStoreMem_mload64 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64)
      (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
    (by
      rw [endSkipAfterArtStoreMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      rw [endSkipArtHashMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega)
    (endSkipAfterArtStoreMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)

abbrev endSkipGrabMemSel (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  endSkipGrabSelectorEncodedWord.toByteArray.write 0
    (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 32

abbrev endSkipGrabMemIlk (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (endArg0Word I).toByteArray.write 0
    (endSkipGrabMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 32

abbrev endSkipGrabMemUsr (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids)).toByteArray.write 0
    (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids) 164 32

abbrev endSkipGrabMemThis (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (outCat outVat outBids : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
    (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196 32

abbrev endSkipGrabMemVow (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) : ByteArray :=
  (endPackVowTarget postσ I).toByteArray.write 0
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228 32

abbrev endSkipGrabMemLot (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) : ByteArray :=
  (endSkipBidsLotWord outBids).toByteArray.write 0
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 32

abbrev endSkipGrabMemFull (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) : ByteArray :=
  (endSkipArtWord outVat outBids).toByteArray.write 0
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 32

abbrev endSkipGrabCallMem (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_4295_memory
    (ee := I) (mem := endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
    (σ := postσ) (x0 := endSkipArtWord outVat outBids)
    (x2 := endSkipBidsUsrWord outBids) (x3 := endSkipBidsLotWord outBids)
    (x9 := endArg0Word I)

theorem endSkipGrabCallMem_eq_full (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids =
      endSkipGrabMemFull preSuck1σ preSuck2σ postσ I outCat outVat outBids := by
  have hfreeCall := endSkipAfterArtStoreMem_mload64 preSuck1σ preSuck2σ I
    outCat outVat outBids houtCat h96 houtVat h160 houtBids h256
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endSkipGrabCallMem endSkipGrabMemFull endSkipGrabMemLot endSkipGrabMemVow
    endSkipGrabMemThis endSkipGrabMemUsr endSkipGrabMemIlk endSkipGrabMemSel
    endSkipGrabSelectorEncodedWord endFreeGrabSelectorEncodedWord endPackVowTarget
  dsimp [endRuntimeBlocks.endRuntime_block_4295_memory]
  rw [hfreeCall]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
  rw [hmaskGenerated]
  rfl

theorem endSkipGrabMemSel_size_ge160 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    160 ≤ (endSkipGrabMemSel preSuck1σ preSuck2σ I outCat outVat outBids).size :=
  toByteArray_write_size_ge_off_add32_unbounded endSkipGrabSelectorEncodedWord
    (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids) 128

theorem endSkipGrabMemIlk_size_ge164 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    164 ≤ (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endArg0Word I)
    (endSkipGrabMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132

theorem endSkipGrabMemUsr_size_ge196 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    196 ≤ (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids).size :=
  toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids))
    (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids) 164

theorem endSkipGrabMemThis_size_ge228 (preSuck1σ preSuck2σ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    228 ≤ (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids).size :=
  toByteArray_write_size_ge_off_add32_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196

theorem endSkipGrabMemVow_size_ge260 (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    260 ≤ (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endPackVowTarget postσ I)
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228

theorem endSkipGrabMemLot_size_ge292 (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray) :
    292 ≤ (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids).size :=
  toByteArray_write_size_ge_off_add32_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260

theorem endSkipGrabCallMem_size_ge324 (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    324 ≤ (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).size := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292

theorem endSkipGrabCallMem_read64 (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 64
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 64
    (by have := endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228 64
    (by have := endSkipGrabMemThis_size_ge228 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196 64
    (by have := endSkipGrabMemUsr_size_ge196 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids))
    (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids) 164 64
    (by have := endSkipGrabMemIlk_size_ge164 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endArg0Word I)
    (endSkipGrabMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 64
    (by have := endSkipGrabMemSel_size_ge160 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded endSkipGrabSelectorEncodedWord
    (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 64
    (by
      rw [endSkipAfterArtStoreMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      rw [endSkipArtHashMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      rw [endSkipYankCallMem_size preSuck1σ preSuck2σ I outCat outVat outBids
        houtCat h96 houtVat h160 houtBids h256]
      omega) (by omega)]
  exact endSkipAfterArtStoreMem_read64 preSuck1σ preSuck2σ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256

theorem endSkipGrabCallMem_mload64 (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    memLoad (UInt256.ofNat 64)
      (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) =
      ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥
        (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).size
      then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue
    (mem := endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids)
    (by
      have hge := endSkipGrabCallMem_size_ge324 preSuck1σ preSuck2σ postσ I
        outCat outVat outBids houtCat h96 houtVat h160 houtBids h256
      change 64 <
        (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).size
      omega)
    (endSkipGrabCallMem_read64 preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256)

theorem endSkipGrabSelectorEncodedWord_prefix :
    (endSkipGrabSelectorEncodedWord.toByteArray).extract 0 4 = grabSelector := by
  exact endFreeGrabSelectorEncodedWord_prefix

theorem endSkipGrabCallMem_readSelector (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        128 4 =
      grabSelector := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [write32_read_below_len _ _ 292 128 4 (by rw [toByteArray_size])
    (endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids)
    (by omega)
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 260 128 4 (by rw [toByteArray_size])
    (endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids)
    (by omega)
    (by have := endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 228 128 4 (by rw [toByteArray_size])
    (endSkipGrabMemThis_size_ge228 preSuck1σ preSuck2σ I outCat outVat outBids)
    (by omega)
    (by have := endSkipGrabMemThis_size_ge228 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (endSkipGrabMemUsr_size_ge196 preSuck1σ preSuck2σ I outCat outVat outBids)
    (by omega)
    (by have := endSkipGrabMemUsr_size_ge196 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endSkipGrabMemIlk_size_ge164 preSuck1σ preSuck2σ I outCat outVat outBids)
    (by omega)
    (by have := endSkipGrabMemIlk_size_ge164 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endSkipGrabMemSel_size_ge160 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)
    (by have := endSkipGrabMemSel_size_ge160 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by decide) (by decide)]
  change ((endSkipGrabSelectorEncodedWord.toByteArray.write 0
      (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids) 128 32).readWithPadding
        128 4) = grabSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endSkipGrabSelectorEncodedWord
    (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
    128 0 4 (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endSkipGrabSelectorEncodedWord_prefix]

theorem endSkipGrabCallMem_readIlk (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        132 32 =
      (endArg0Word I).toByteArray := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 132
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 132
    (by have := endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228 132
    (by have := endSkipGrabMemThis_size_ge228 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196 132
    (by have := endSkipGrabMemUsr_size_ge196 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids))
    (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids) 164 132
    (by have := endSkipGrabMemIlk_size_ge164 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  change (((endArg0Word I).toByteArray.write 0
      (endSkipGrabMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132 32).readWithPadding
        132 32) = (endArg0Word I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endArg0Word I)
    (endSkipGrabMemSel preSuck1σ preSuck2σ I outCat outVat outBids) 132

theorem endSkipGrabCallMem_readUsr (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        164 32 =
      (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids)).toByteArray := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 164
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 164
    (by have := endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228 164
    (by have := endSkipGrabMemThis_size_ge228 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196 164
    (by have := endSkipGrabMemUsr_size_ge196 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  change (((UInt256.land solcAddrMask (endSkipBidsUsrWord outBids)).toByteArray.write 0
      (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids) 164 32).readWithPadding
        164 32) =
    (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids)).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded
    (UInt256.land solcAddrMask (endSkipBidsUsrWord outBids))
    (endSkipGrabMemIlk preSuck1σ preSuck2σ I outCat outVat outBids) 164

theorem endSkipGrabCallMem_readThis (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        196 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 196
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 196
    (by have := endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228 196
    (by have := endSkipGrabMemThis_size_ge228 preSuck1σ preSuck2σ I outCat outVat outBids; omega)
    (by omega)]
  change (((UInt256.ofNat I.codeOwner.val).toByteArray.write 0
      (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196 32).readWithPadding
        196 32) = (UInt256.ofNat I.codeOwner.val).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (UInt256.ofNat I.codeOwner.val)
    (endSkipGrabMemUsr preSuck1σ preSuck2σ I outCat outVat outBids) 196

theorem endSkipGrabCallMem_readVow (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        228 32 =
      (endPackVowTarget postσ I).toByteArray := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 228
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 228
    (by have := endSkipGrabMemVow_size_ge260 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  change (((endPackVowTarget postσ I).toByteArray.write 0
      (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228 32).readWithPadding
        228 32) = (endPackVowTarget postσ I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackVowTarget postσ I)
    (endSkipGrabMemThis preSuck1σ preSuck2σ I outCat outVat outBids) 228

theorem endSkipGrabCallMem_readLot (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        260 32 =
      (endSkipBidsLotWord outBids).toByteArray := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 260
    (by have := endSkipGrabMemLot_size_ge292 preSuck1σ preSuck2σ postσ I outCat outVat outBids; omega)
    (by omega)]
  change (((endSkipBidsLotWord outBids).toByteArray.write 0
      (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 32).readWithPadding
        260 32) = (endSkipBidsLotWord outBids).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endSkipBidsLotWord outBids)
    (endSkipGrabMemVow preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260

theorem endSkipGrabCallMem_readArt (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        292 32 =
      (endSkipArtWord outVat outBids).toByteArray := by
  rw [endSkipGrabCallMem_eq_full preSuck1σ preSuck2σ postσ I outCat outVat outBids
    houtCat h96 houtVat h160 houtBids h256]
  change (((endSkipArtWord outVat outBids).toByteArray.write 0
      (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292 32).readWithPadding
        292 32) = (endSkipArtWord outVat outBids).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endSkipArtWord outVat outBids)
    (endSkipGrabMemLot preSuck1σ preSuck2σ postσ I outCat outVat outBids) 292

theorem endSkipGrabCallMem_readCallData (preSuck1σ preSuck2σ postσ : AccountMap)
    (I : ExecutionEnv) (outCat outVat outBids : ByteArray)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size) :
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids).readWithPadding
        128 196 =
      endSkipGrabEncodedCall postσ I outVat outBids := by
  have hsize := endSkipGrabCallMem_size_ge324 preSuck1σ preSuck2σ postσ I
    outCat outVat outBids houtCat h96 houtVat h160 houtBids h256
  rw [show 196 = 4 + 192 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) 128 4 192
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 192 = 32 + 160 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) 132 32 160
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 160 = 32 + 128 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) 164 32 128
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [show 128 = 32 + 96 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) 196 32 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 196 + 32 = 228 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) 228 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 228 + 32 = 260 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split
    (endSkipGrabCallMem preSuck1σ preSuck2σ postσ I outCat outVat outBids) 260 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 260 + 32 = 292 by norm_num]
  rw [endSkipGrabCallMem_readSelector preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipGrabCallMem_readIlk preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipGrabCallMem_readUsr preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipGrabCallMem_readThis preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipGrabCallMem_readVow preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipGrabCallMem_readLot preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256,
    endSkipGrabCallMem_readArt preSuck1σ preSuck2σ postσ I outCat outVat outBids
      houtCat h96 houtVat h160 houtBids h256]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endSkipGrabEncodedCall, endSkipGrabPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endSkipGrabGateStack (postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outCat outVat outBids : ByteArray) : List UInt256 :=
  [⟨196⟩, ⟨196⟩, ⟨128⟩, ⟨128⟩, endSkipGrabSelectorWord,
    endPackVatTarget postσ I] ++ endSkipGrabGateRest I sel outCat outVat outBids

abbrev endSkipGrabCallRest (postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outCat outVat outBids : ByteArray) : List UInt256 :=
  [⟨324⟩, endSkipGrabSelectorWord, endPackVatTarget postσ I] ++
    endSkipGrabGateRest I sel outCat outVat outBids

abbrev endSkipGrabCallStack (postσ : AccountMap) (I : ExecutionEnv)
    (sel : UInt256) (outCat outVat outBids : ByteArray) : List UInt256 :=
  [endPackVatTarget postσ I, ⟨0⟩, ⟨128⟩, ⟨196⟩, ⟨128⟩, ⟨0⟩] ++
    endSkipGrabCallRest postσ I sel outCat outVat outBids

abbrev endSkipGrabCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preSuck1σ preSuck2σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (rdata outCat outVat outBids : ByteArray) : Cursor :=
  { pc := ⟨4411⟩,
    stack := endSkipGrabCallStack world.2 I sel outCat outVat outBids,
    mem := endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids,
    aw := aw, rdata := rdata, world := world }

abbrev endSkipGrabCallAw (aw : UInt256) : UInt256 :=
  endFreeGrabCallAw aw

theorem endX_skip_after_guards_to_grab_gate {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipGrabGateRest I sel outCat outVat outBids)
      (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    ∃ aw' k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4380⟩
      (endSkipGrabGateStack world.2 I sel outCat outVat outBids)
      (endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids)
      aw' rdata world k' C' := by
  obtain ⟨aw4380, k4380, C4380, rd4380⟩ :=
    endRuntimeBlocks.endRuntime_block_4295_packed
      (x0 := endSkipArtWord outVat outBids)
      (x1 := endSkipBidsTabWord outBids)
      (x2 := endSkipBidsUsrWord outBids)
      (x3 := endSkipBidsLotWord outBids)
      (x4 := endSkipBidsBidWord outBids)
      (x5 := endFlowVatIlksRateWord outVat)
      (x6 := endSkipCatIlksFlipWord outCat)
      (x7 := endSkipCatIlksFlipWord outCat)
      (x8 := endArg1Word I) (x9 := endArg0Word I)
      (R := [⟨562⟩, sel])
      (by simp) (by simpa [endSkipGrabGateRest] using rd)
  have hpreMload := endSkipAfterArtStoreMem_mload64 preSuck1σ preSuck2σ I
    outCat outVat outBids houtCat h96 houtVat h160 houtBids h256
  have hcallMload := endSkipGrabCallMem_mload64 preSuck1σ preSuck2σ world.2 I
    outCat outVat outBids houtCat h96 houtVat h160 houtBids h256
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have htarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1))
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)) =
        endPackVatTarget world.2 I := by
    rw [hmaskGenerated, u256_land_comm]
  have hstack4380 :
      endRuntimeBlocks.endRuntime_block_4295_stack (ee := I)
          (mem := endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
          (σ := world.2)
          (x0 := endSkipArtWord outVat outBids)
          (x1 := endSkipBidsTabWord outBids)
          (x2 := endSkipBidsUsrWord outBids)
          (x3 := endSkipBidsLotWord outBids)
          (x4 := endSkipBidsBidWord outBids)
          (x5 := endFlowVatIlksRateWord outVat)
          (x6 := endSkipCatIlksFlipWord outCat)
          (x7 := endSkipCatIlksFlipWord outCat)
          (x8 := endArg1Word I) (x9 := endArg0Word I)
          (R := [⟨562⟩, sel]) =
        endSkipGrabGateStack world.2 I sel outCat outVat outBids := by
    have hcallMloadRaw := hcallMload
    dsimp [endSkipGrabCallMem, endRuntimeBlocks.endRuntime_block_4295_memory]
      at hcallMloadRaw
    rw [hpreMload] at hcallMloadRaw
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide] at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
      at hcallMloadRaw
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
      at hcallMloadRaw
    dsimp [endRuntimeBlocks.endRuntime_block_4295_stack, endSkipGrabGateStack,
      endSkipGrabGateRest, endSkipGrabSelectorWord, endFreeGrabSelectorWord]
    rw [htarget, hpreMload]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 4).toNat = 132 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 36).toNat = 164 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 68).toNat = 196 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 100).toNat = 228 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 132).toNat = 260 from by native_decide]
    rw [show ((⟨128⟩ : UInt256) + UInt256.ofNat 164).toNat = 292 from by native_decide]
    rw [hcallMloadRaw]
    rw [show UInt256.ofNat 196 = (⟨196⟩ : UInt256) from by native_decide]
  exact ⟨aw4380, k4380, C4380, by
    simpa [hstack4380, endSkipGrabCallMem] using rd4380⟩

theorem endX_skip_grab_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipGrabGateRest I sel outCat outVat outBids)
      (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨aw4380, k4380, C4380, rd4380⟩ :=
    endX_skip_after_guards_to_grab_gate
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
      (sel := sel) (aw := aw) (rdata := rdata) (outCat := outCat)
      (outVat := outVat) (outBids := outBids) (world := world)
      houtCat h96 houtVat h160 houtBids h256 rd
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) =
        UInt256.ofNat 0 := by
    rw [hvatNoCode]
    native_decide
  obtain ⟨aw4405, k4405, C4405, rd4405⟩ :=
    endRuntimeBlocks.endRuntime_block_4380_fallthrough_packed
      (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
      (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
      (x4 := endSkipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := endSkipGrabGateRest I sel outCat outVat outBids)
      (by simp [endSkipGrabGateRest]) hcondCode
      (by simpa [endSkipGrabGateStack] using rd4380)
  exact endRuntimeBlocks.endRuntime_block_4405
    (R := endRuntimeBlocks.endRuntime_block_4380_fallthrough_stack (σ := world.2)
      (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
      (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
      (x4 := endSkipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := endSkipGrabGateRest I sel outCat outVat outBids))
    (by simp [endRuntimeBlocks.endRuntime_block_4380_fallthrough_stack,
      endSkipGrabGateRest])
    rd4405

theorem endX_skip_to_grab_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {preSuck1σ preSuck2σ : AccountMap} {sel aw rdata k C}
    {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipGrabGateRest I sel outCat outVat outBids)
      (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
      aw rdata world k C) :
    ∃ awNext kNext CNext, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4411⟩
      (endSkipGrabCallStack world.2 I sel outCat outVat outBids)
      (endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids)
      awNext rdata world kNext CNext := by
  obtain ⟨aw4380, k4380, C4380, rd4380⟩ :=
    endX_skip_after_guards_to_grab_gate
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
      (sel := sel) (aw := aw) (rdata := rdata) (outCat := outCat)
      (outVat := outVat) (outBids := outBids) (world := world)
      houtCat h96 houtVat h160 houtBids h256 rd
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw4409, k4409, C4409, rd4409⟩ :=
    endRuntimeBlocks.endRuntime_block_4380_taken_packed
      (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
      (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
      (x4 := endSkipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
      (R := endSkipGrabGateRest I sel outCat outVat outBids)
      (by simp [endSkipGrabGateRest]) hcondCode (by jump_dest)
      (by simpa [endSkipGrabGateStack] using rd4380)
  have hlen : UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + (⟨196⟩ : UInt256) =
      ⟨196⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + (⟨196⟩ : UInt256) = ⟨324⟩ := by
    native_decide
  have hstack4409 :
      endRuntimeBlocks.endRuntime_block_4380_taken_stack (σ := world.2)
          (x0 := (⟨196⟩ : UInt256)) (x1 := (⟨196⟩ : UInt256))
          (x2 := (⟨128⟩ : UInt256)) (x3 := (⟨128⟩ : UInt256))
          (x4 := endSkipGrabSelectorWord) (x5 := endPackVatTarget world.2 I)
          (R := endSkipGrabGateRest I sel outCat outVat outBids) =
        UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipGrabCallStack world.2 I sel outCat outVat outBids := by
    dsimp [endRuntimeBlocks.endRuntime_block_4380_taken_stack,
      endSkipGrabCallStack, endSkipGrabCallRest, endSkipGrabGateRest]
    rw [hlen, hend]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from by native_decide]
  have rd4409Ok :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4409⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)) ::
          endSkipGrabCallStack world.2 I sel outCat outVat outBids)
        (endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids)
        aw4409 rdata world k4409 C4409 := by
    simpa [hstack4409] using rd4409
  obtain ⟨aw4411, k4411, C4411, rd4411⟩ :=
    endRuntimeBlocks.endRuntime_block_4409_packed
      (x0 := UInt256.isZero (extCodeSizeWord world.2 (endPackVatTarget world.2 I)))
      (R := endSkipGrabCallStack world.2 I sel outCat outVat outBids)
      (by simp [endSkipGrabCallStack, endSkipGrabCallRest, endSkipGrabGateRest])
      rd4409Ok
  exact ⟨aw4411, k4411, C4411, by
    simpa [endRuntimeBlocks.endRuntime_block_4409_stack] using rd4411⟩

theorem endSkipGrabExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C baseEvm evm}
    {preSuck1σ preSuck2σ : AccountMap} {outCat outVat outBids : ByteArray}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endSkipGrabCallCursor world preSuck1σ preSuck2σ I sel aw rdata
        outCat outVat outBids)
      k C (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr,
            asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ]
      (runtimeExit (.abi [])) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨4411⟩ = some (.GAS, .none); decide)
    (by simp [endSkipGrabCallCursor, endSkipGrabCallStack, endSkipGrabCallRest,
      endSkipGrabGateRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget world.2 I).toNat)
    (argVals := [endArg0Bytes32Value I, endSkipUsrValue outBids, .address I.codeOwner,
      .address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
      .int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
      .int (Int.ofNat (endSkipArtWord outVat outBids).toNat)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨4412⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endSkipGrabCallRest, endSkipGrabGateRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_skipAfterArtNew baseEvm evm I outCat outVat outBids]
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
    rw [endEvalSkipGrabArgs baseEvm evm I outCat outVat outBids]
    rw [h.env]
    change EvalResult.ok
      [endArg0Bytes32Value I, endSkipUsrValue outBids, Value.address I.codeOwner,
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        Value.int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
        Value.int (Int.ofNat (endSkipArtWord outVat outBids).toNat)] =
      EvalResult.ok
        [endArg0Bytes32Value I, endSkipUsrValue outBids, Value.address I.codeOwner,
          Value.address (AccountAddress.ofNat (endPackVowTarget world.2 I).toNat),
          Value.int (Int.ofNat (endSkipBidsLotWord outBids).toNat),
          Value.int (Int.ofNat (endSkipArtWord outVat outBids).toNat)]
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
    rw [endExternalEncode_grab_skip world.2 I outVat outBids hsz68 hlot hart]
    change some (endSkipGrabEncodedCall world.2 I outVat outBids) =
      some ((endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids).readWithPadding
        128 196)
    rw [endSkipGrabCallMem_readCallData preSuck1σ preSuck2σ world.2 I
      outCat outVat outBids houtCat h96 houtVat h160 houtBids h256]
  · intro out evmNext worldNext kNext CNext
    dsimp only
    intro _ _
    rw [endExternalDecode_grab out]
    intro rd hrel
    have rd4413 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4413⟩
          ((⟨1⟩ : UInt256) :: endSkipGrabCallRest world.2 I sel outCat outVat outBids)
          (endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids)
          (endSkipGrabCallAw aw) out worldNext kNext CNext := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipGrabCallCursor,
        endSkipGrabCallStack, endSkipGrabCallRest, endSkipGrabGateRest,
        endSkipGrabCallAw] using rd
    have rd4429 := endRuntimeBlocks.endRuntime_block_4413_taken
      (x0 := (⟨1⟩ : UInt256))
      (R := endSkipGrabCallRest world.2 I sel outCat outVat outBids)
      (by simp [endSkipGrabCallRest, endSkipGrabGateRest])
      (by native_decide) (by jump_dest) rd4413
    have rd562 := endRuntimeBlocks.endRuntime_block_4429
      (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨324⟩ : UInt256))
      (x2 := endSkipGrabSelectorWord) (x3 := endPackVatTarget world.2 I)
      (x4 := endSkipArtWord outVat outBids)
      (x5 := endSkipBidsTabWord outBids)
      (x6 := endSkipBidsUsrWord outBids)
      (x7 := endSkipBidsLotWord outBids)
      (x8 := endSkipBidsBidWord outBids)
      (x9 := endFlowVatIlksRateWord outVat)
      (x10 := endSkipCatIlksFlipWord outCat)
      (x11 := endSkipCatIlksFlipWord outCat)
      (x12 := endArg1Word I) (x13 := endArg0Word I)
      (x14 := (⟨562⟩ : UInt256)) (R := [sel])
      (by simp) hperm (by jump_dest)
      (by
        simpa [endRuntimeBlocks.endRuntime_block_4413_taken_stack,
          endSkipGrabCallRest, endSkipGrabGateRest] using rd4429)
    have rdret := endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp) rd562
    exact BlockProgress.ofRDret ExecBlock.nil rdret
      (by simpa using hrel.created.symm)
      (by simpa using hrel.accounts)
      abiVoidFallthrough
  · intro out worldNext kNext CNext
    dsimp only
    intro rd
    have rd4413 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4413⟩
          ((⟨0⟩ : UInt256) :: endSkipGrabCallRest world.2 I sel outCat outVat outBids)
          (endSkipGrabCallMem preSuck1σ preSuck2σ world.2 I outCat outVat outBids)
          (endSkipGrabCallAw aw) out worldNext kNext CNext := by
      simpa [gasCursor, callCursor, endPackCallCopyZero, endSkipGrabCallCursor,
        endSkipGrabCallStack, endSkipGrabCallRest, endSkipGrabGateRest,
        endSkipGrabCallAw] using rd
    have rd4420 := endRuntimeBlocks.endRuntime_block_4413_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endSkipGrabCallRest world.2 I sel outCat outVat outBids)
      (by simp [endSkipGrabCallRest, endSkipGrabGateRest])
      (by native_decide) rd4413
    exact endRuntimeBlocks.endRuntime_block_4420
      (R := endRuntimeBlocks.endRuntime_block_4413_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256))
        (R := endSkipGrabCallRest world.2 I sel outCat outVat outBids))
      (by simp [endRuntimeBlocks.endRuntime_block_4413_fallthrough_stack,
        endSkipGrabCallRest, endSkipGrabGateRest])
      rd4420

theorem endSkipGrabCheckedCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preSuck1σ preSuck2σ : AccountMap} {baseEvm : EVM.State}
    {outCat outVat outBids : ByteArray}
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (houtCat : outCat.size < UInt256.size) (h96 : 96 ≤ outCat.size)
    (houtVat : outVat.size < UInt256.size) (h160 : 160 ≤ outVat.size)
    (houtBids : outBids.size < UInt256.size) (h256 : 256 ≤ outBids.size)
    (hlot : (endSkipBidsLotWord outBids).toNat < endFreeInt256LimitWord.toNat)
    (hart : (endSkipArtWord outVat outBids).toNat < endFreeInt256LimitWord.toNat) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨4295⟩
      (fun cur frame e =>
        frame = endSkipAfterArtNewFrame baseEvm I outCat outVat outBids ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.stack = endSkipGrabGateRest I sel outCat outVat outBids ∧
        cur.mem = endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids ∧
        cur.aw = aw)
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")]
        "_grab")
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hstack, hmem, haw⟩
  cases hframe
  have rd4295 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
        (endSkipGrabGateRest I sel outCat outVat outBids)
        (endSkipAfterArtStoreMem preSuck1σ preSuck2σ I outCat outVat outBids)
        aw cur.rdata cur.world k C := by
    simpa [hpc, hstack, hmem, haw] using rd
  have hslotVat := endPackSlotLoad_eq_of_callRel hrel (UInt256.ofNat 1)
  rw [hrel.env] at hslotVat
  have hsrcCodeEq :
      extCodeSizeWord evm.accountMap
          (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
            solcAddrMask) =
        extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) := by
    rw [hrel.env, hslotVat]
    have htarget :
        UInt256.land (storageRead I.codeOwner cur.world.2 (UInt256.ofNat 1))
            solcAddrMask =
          endPackVatTarget cur.world.2 I := by
      simp [endPackVatTarget, u256_land_comm]
    rw [htarget]
    exact (extCodeSizeWord_accountMapEquiv hrel.accounts
      (endPackVatTarget cur.world.2 I)).symm
  by_cases hvatNoCode :
      extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) = ⟨0⟩ := by
      rw [hsrcCodeEq, hvatNoCode]
    have hsource :
        ExecBlock config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
          (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
            [.var "ilk", .var "usr", thisAddr, vowAddr,
              asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalVatCodeGuard_skipAfterArtNew_false baseEvm evm
              I outCat outVat outBids hsrcNoCode)))
    have hrev := endX_skip_grab_no_code
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
      (sel := sel) (aw := aw) (rdata := cur.rdata) (outCat := outCat)
      (outVat := outVat) (outBids := outBids) (world := cur.world)
      houtCat h96 houtVat h160 houtBids h256 hvatNoCode rd4295
    exact BlockProgress.ofRDrev hsource hrev
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
              solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hvatNoCode (hsrcCodeEq.symm.trans hzero)
    have hrequire :
        ExecBlock config (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
          [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
          (.ok (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm) :=
      ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalVatCodeGuard_skipAfterArtNew_true baseEvm evm
            I outCat outVat outBids hsrcCode))
        ExecBlock.nil
    obtain ⟨aw4411, k4411, C4411, rd4411⟩ :=
      endX_skip_to_grab_call
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (sel := sel) (aw := aw) (rdata := cur.rdata) (outCat := outCat)
        (outVat := outVat) (outBids := outBids) (world := cur.world)
        houtCat h96 houtVat h160 houtBids h256 hvatNoCode rd4295
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipGrabCallCursor cur.world preSuck1σ preSuck2σ I sel aw4411
            cur.rdata outCat outVat outBids)
          k4411 C4411 (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
          (fun cur _ e =>
            CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", .var "usr", thisAddr, vowAddr,
                asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ]
          (runtimeExit (.abi [])) :=
      endSkipGrabExternalCallRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (sel := sel) (aw := aw4411)
        (rdata := cur.rdata) (k := k4411) (C := C4411)
        (baseEvm := baseEvm) (evm := evm)
        (preSuck1σ := preSuck1σ) (preSuck2σ := preSuck2σ)
        (outCat := outCat) (outVat := outVat) (outBids := outBids)
        (world := cur.world)
        hperm hsz68 houtCat h96 houtVat h160 houtBids h256 hlot hart
    have htailProgress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
          [ .externalCall (.storage vatRef) "grab" (.intLit 0)
              [.var "ilk", .var "usr", thisAddr, vowAddr,
                asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ]
          (runtimeExit (.abi [])) :=
      htail (by simpa [endSkipGrabCallCursor] using rd4411) hrel
    have hprogress :
        BlockProgress endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endSkipAfterArtNewFrame baseEvm I outCat outVat outBids) evm
          ([ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
            [ .externalCall (.storage vatRef) "grab" (.intLit 0)
                [.var "ilk", .var "usr", thisAddr, vowAddr,
                  asInt256 (.var "lot"), asInt256 (.var "art")] "_grab" ])
          (runtimeExit (.abi [])) :=
      BlockProgress.prepend hrequire htailProgress
    simpa [checkedExternalCallStmts] using hprogress

def endSkipGrabCheckedStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
    [.var "ilk", .var "usr", thisAddr, vowAddr,
      asInt256 (.var "lot"), asInt256 (.var "art")]
    "_grab"

end Benchmarks.Dss.End
