import Benchmarks.Dss.End.Cage
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.RuntimeBlocks_008
import Benchmarks.Dss.End.RuntimeBlocks_009
import Reasoning.CallMemory
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `thaw()` -/

abbrev endThawStore : Store :=
  ∅

abbrev endThawLiveWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩

abbrev endThawDebtWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩

abbrev endThawLiveWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ ⟨8⟩

abbrev endThawDebtWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ ⟨11⟩

abbrev endThawWhenWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩

abbrev endThawWaitWord (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩

abbrev endThawDeadlineWord (evm : EVM.State) : UInt256 :=
  endThawWhenWord evm + endThawWaitWord evm

abbrev endThawWhenWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ ⟨9⟩

abbrev endThawWaitWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ ⟨10⟩

abbrev endThawDeadlineWorldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endThawWhenWorldWord σ I + endThawWaitWorldWord σ I

abbrev endThawUIntReturnWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

theorem endThawStore_get_none (name : String) :
    endThawStore.get? name = none := by
  simp [endThawStore]

theorem endEvalLiveStorage_thaw (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
        (.storage liveRef) =
      .ok (endUIntValue (endThawLiveWord evm)) := by
  simpa [endThawStore, endThawLiveWord, endUIntValue] using
    endEvalLiveStorage_cage evm

theorem endEvalDebtStorage_thaw (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
        (.storage debtRef) =
      .ok (endUIntValue (endThawDebtWord evm)) := by
  have her : evalStorageRef config { contract := contract, locals := endThawStore } evm
      debtRef = .ok { base := "debt", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind,
      endThawStore]
  have hty : storageTypeAt? contract.storage ({ base := "debt", steps := [] } : EvaledStorageRef)
      = some (.elem (.int uint256Int)) := by decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [endThawStore, debtRef]) (her := her) (hty := hty)
    (hloc := endConfig_storage_debt)]
  simp [endRuntimeStorageLocLoad_uint256, endThawDebtWord, endUIntValue]

theorem endEvalLiveEqZero_thaw_true (evm : EVM.State)
    (hlive : endThawLiveWord evm = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_thaw evm, hlive]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endEvalLiveEqZero_thaw_false (evm : EVM.State)
    (hlive : endThawLiveWord evm ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
      (.binary .eq (.storage liveRef) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalLiveStorage_thaw evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : (endThawLiveWord evm).toNat ≠ 0 := by
    intro hzero
    exact hlive (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endEvalDebtEqZero_thaw_true (evm : EVM.State)
    (hdebt : endThawDebtWord evm = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
      (.binary .eq (.storage debtRef) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalDebtStorage_thaw evm, hdebt]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?, endUIntValue]

theorem endEvalDebtEqZero_thaw_false (evm : EVM.State)
    (hdebt : endThawDebtWord evm ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
      (.binary .eq (.storage debtRef) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalDebtStorage_thaw evm]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat : (endThawDebtWord evm).toNat ≠ 0 := by
    intro hzero
    exact hdebt (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

theorem endThawBodyLiveFail (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord evm ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm endThawStore thawTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [thawTransition, checkedExternalCallStmts, nonpayable, endThawStore] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalLiveEqZero_thaw_false evm hlive)))

theorem endThawBodyDebtFail (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord evm = ⟨0⟩)
    (hdebt : endThawDebtWord evm ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm endThawStore thawTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [thawTransition, checkedExternalCallStmts, nonpayable, endThawStore] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveEqZero_thaw_true evm hlive)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalDebtEqZero_thaw_false evm hdebt)))

theorem endThawBodyVatDaiNoCode (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord evm = ⟨0⟩)
    (hdebt : endThawDebtWord evm = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm endThawStore thawTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [thawTransition, checkedExternalCallStmts, nonpayable, endThawStore] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveEqZero_thaw_true evm hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtEqZero_thaw_true evm hdebt)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_cage_false evm hvatNoCode)))

theorem endThawBodyPrefixOk (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : endThawLiveWord evm = ⟨0⟩)
    (hdebt : endThawDebtWord evm = ⟨0⟩)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endThawStore } evm
      (nonpayable ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
          .require (.binary .eq (.storage debtRef) (.intLit 0)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endThawStore } evm) := by
  simpa [nonpayable, endThawStore] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalLiveEqZero_thaw_true evm hlive)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtEqZero_thaw_true evm hdebt)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_cage_true evm hvatCode)) <|
      ExecBlock.nil)

theorem endExternalDecode_uint256_ok (name : Ident) {out : ByteArray}
    (hname : name = "dai" ∨ name = "debt" ∨ name = "tell")
    (h32 : 32 ≤ out.size) :
    externalABI.decode? name out = some [endUIntValue (endThawUIntReturnWord out)] := by
  rcases hname with rfl | rfl | rfl
  · simp [externalABI, decodeReturn?, endThawUIntReturnWord, endUIntValue, uint256,
      uint256Int, abiUInt256,
      decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) h32]
    rw [UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt h32)]
  · simp [externalABI, decodeReturn?, endThawUIntReturnWord, endUIntValue, uint256,
      uint256Int, abiUInt256,
      decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) h32]
    rw [UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt h32)]
  · simp [externalABI, decodeReturn?, endThawUIntReturnWord, endUIntValue, uint256,
      uint256Int, abiUInt256,
      decodeReturnValueWithMode_legacy_uint256_ok (returndata := out) h32]
    rw [UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt h32)]

theorem endExternalDecode_uint256_none_short (name : Ident) {out : ByteArray}
    (hname : name = "dai" ∨ name = "debt" ∨ name = "tell")
    (hshort : out.size < 32) :
    externalABI.decode? name out = none := by
  rcases hname with rfl | rfl | rfl
  · simp [externalABI, decodeReturn?, uint256, uint256Int, abiUInt256,
      decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]
  · simp [externalABI, decodeReturn?, uint256, uint256Int, abiUInt256,
      decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]
  · simp [externalABI, decodeReturn?, uint256, uint256Int, abiUInt256,
      decodeReturnValueWithMode_legacy_uint256_none_short (returndata := out) hshort]

abbrev endThawVatDaiSelectorWord : UInt256 := UInt256.ofNat 1814410054

abbrev endThawVatDaiSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 907205027) (UInt256.ofNat 225)

def endThawVatDaiPayloadBytes (σ : AccountMap) (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (endPackVowTarget σ I)

def endThawVatDaiEncodedCall (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  daiSelector ++ ⟨(endThawVatDaiPayloadBytes σ I).toArray⟩

theorem endEncodeABIValues_dai (σ : AccountMap) (I : ExecutionEnv) :
    encodeABIValues? [addr]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat)] =
      some (endThawVatDaiPayloadBytes σ I) := by
  have hhead : abiTupleHeadSize? [addr] = some 32 := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow σ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp [endThawVatDaiPayloadBytes, toByteArray_eq_toBytesBE]

theorem endEncodeCallWithSelector_dai (σ : AccountMap) (I : ExecutionEnv) :
    ABI.encodeCallWithSelector? daiSelector [addr]
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat)] =
      some (endThawVatDaiEncodedCall σ I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_dai σ I]
  simp [endThawVatDaiEncodedCall, endThawVatDaiPayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_dai_branch (args : List Value) :
    config.externalABI.encode? "dai" args =
      ABI.encodeCallWithSelector? daiSelector [addr] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "dai" = "cage")]
  rw [if_neg (by decide : ¬ "dai" = "vatIlks")]
  rw [if_neg (by decide : ¬ "dai" = "catIlks")]
  rw [if_neg (by decide : ¬ "dai" = "dogIlks")]
  rw [if_neg (by decide : ¬ "dai" = "spotIlks")]
  rw [if_neg (by decide : ¬ "dai" = "urns")]
  rw [if_pos (by decide : "dai" = "dai")]

theorem endExternalEncode_dai (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "dai"
      [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat)] =
      some (endThawVatDaiEncodedCall σ I) := by
  rw [endExternalEncode_dai_branch]
  exact endEncodeCallWithSelector_dai σ I

abbrev endThawVatDaiCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_4668_taken_memory
    (ee := I) (mem := solcFreePtrMem) (σ := σ)

abbrev endThawVatDaiMemSel : ByteArray :=
  endThawVatDaiSelectorEncodedWord.toByteArray.write 0 solcFreePtrMem 128 32

abbrev endThawVatDaiMemFull (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (endPackVowTarget σ I).toByteArray.write 0 endThawVatDaiMemSel 132 32

theorem endThawVatDaiCallMem_eq_full (σ : AccountMap) (I : ExecutionEnv) :
    endThawVatDaiCallMem σ I = endThawVatDaiMemFull σ I := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  unfold endThawVatDaiCallMem endThawVatDaiMemFull endThawVatDaiMemSel
    endThawVatDaiSelectorEncodedWord endPackVowTarget
  dsimp [endRuntimeBlocks.endRuntime_block_4668_taken_memory]
  rw [hload]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((⟨128⟩ : UInt256) + (UInt256.ofNat 4)).toNat = 132 from by native_decide]
  rw [hmask]

theorem endThawVatDaiMemSel_size_ge160 :
    160 ≤ endThawVatDaiMemSel.size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    endThawVatDaiSelectorEncodedWord solcFreePtrMem 128

theorem endThawVatDaiCallMem_size_ge164 (σ : AccountMap) (I : ExecutionEnv) :
    164 ≤ (endThawVatDaiCallMem σ I).size := by
  rw [endThawVatDaiCallMem_eq_full σ I]
  exact toByteArray_write_size_ge_off_add32_unbounded
    (endPackVowTarget σ I) endThawVatDaiMemSel 132

theorem endThawVatDaiMemSel_size :
    endThawVatDaiMemSel.size = 160 := by
  unfold endThawVatDaiMemSel
  exact toByteArray_write32_size_of_ge solcFreePtrMem
    endThawVatDaiSelectorEncodedWord 128 96 160
    solcFreePtrMem_size (by omega) (by native_decide) rfl

theorem endThawVatDaiCallMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (endThawVatDaiCallMem σ I).size = 164 := by
  rw [endThawVatDaiCallMem_eq_full σ I]
  unfold endThawVatDaiMemFull
  exact toByteArray_write32_size_of_le endThawVatDaiMemSel
    (endPackVowTarget σ I) 132 160 164
    endThawVatDaiMemSel_size
    (by rw [endThawVatDaiMemSel_size]; omega)
    (by omega)

theorem endThawVatDaiSelectorEncodedWord_prefix :
    (endThawVatDaiSelectorEncodedWord.toByteArray).extract 0 4 = daiSelector := by
  native_decide

theorem endThawVatDaiCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (endThawVatDaiCallMem σ I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endThawVatDaiCallMem_eq_full σ I]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endPackVowTarget σ I) endThawVatDaiMemSel 132 64
    (by have := endThawVatDaiMemSel_size_ge160; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    endThawVatDaiSelectorEncodedWord solcFreePtrMem 128 64
    (by rw [solcFreePtrMem_size]) (by omega)]
  exact solcFreePtrMem_read64

theorem endThawVatDaiCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endThawVatDaiCallMem σ I) = ⟨128⟩ := by
  exact mloadFreePtrValue (mem := endThawVatDaiCallMem σ I)
    (by have := endThawVatDaiCallMem_size_ge164 σ I; omega)
    (endThawVatDaiCallMem_read64 σ I)

theorem endThawVatDaiCallMem_readSelector (σ : AccountMap) (I : ExecutionEnv) :
    (endThawVatDaiCallMem σ I).readWithPadding 128 4 = daiSelector := by
  rw [endThawVatDaiCallMem_eq_full σ I]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endThawVatDaiMemSel_size_ge160; omega) (by omega)
    (by have := endThawVatDaiMemSel_size_ge160; omega) (by decide) (by decide)]
  change ((endThawVatDaiSelectorEncodedWord.toByteArray.write 0
      solcFreePtrMem 128 32).readWithPadding 128 4) = daiSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endThawVatDaiSelectorEncodedWord solcFreePtrMem 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endThawVatDaiSelectorEncodedWord_prefix]

theorem endThawVatDaiCallMem_readVow (σ : AccountMap) (I : ExecutionEnv) :
    (endThawVatDaiCallMem σ I).readWithPadding 132 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [endThawVatDaiCallMem_eq_full σ I]
  exact toByteArray_write_read_back_of_gap_unbounded
    (endPackVowTarget σ I) endThawVatDaiMemSel 132

theorem endThawVatDaiCallMem_readCallData (σ : AccountMap) (I : ExecutionEnv) :
    (endThawVatDaiCallMem σ I).readWithPadding 128 36 =
      endThawVatDaiEncodedCall σ I := by
  have hsize := endThawVatDaiCallMem_size_ge164 σ I
  rw [show 36 = 4 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endThawVatDaiCallMem σ I) 128 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [endThawVatDaiCallMem_readSelector σ I, endThawVatDaiCallMem_readVow σ I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endThawVatDaiEncodedCall, endThawVatDaiPayloadBytes, toByteArray_eq_toBytesBE]

abbrev endThawVatDaiReturnMem (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) : ByteArray :=
  out.write 0 (endThawVatDaiCallMem σ I) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev endThawVatDaiCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨164⟩, endThawVatDaiSelectorWord, endPackVatTarget σ I, ⟨562⟩, sel]

abbrev endThawVatDaiCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨128⟩, ⟨36⟩, ⟨128⟩, ⟨32⟩] ++
    endThawVatDaiCallRest σ I sel

abbrev endThawVatDaiCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨4751⟩, stack := endThawVatDaiCallStack σ I sel,
    mem := endThawVatDaiCallMem σ I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endThawVatDaiCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat)

abbrev endThawAfterVatDaiAw (aw : UInt256) : UInt256 :=
  M (endThawVatDaiCallAw aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endThawAfterVatDaiFrame (out : ByteArray) : Frame :=
  { contract := contract,
    locals := endThawStore.insert "vatDai"
      (collapseReturns [endUIntValue (endThawUIntReturnWord out)]) }

abbrev endThawAfterVatDaiCursor (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256)
    (out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨4791⟩,
    stack :=
      [UInt256.ofNat out.size,
        memLoad (UInt256.ofNat 64) (endThawVatDaiReturnMem σ I out), ⟨562⟩, sel],
    mem := endThawVatDaiReturnMem σ I out,
    aw := endThawAfterVatDaiAw aw, rdata := out, world := world }

theorem endEvalVatAddress_thaw (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endThawStore } evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind,
      endThawStore]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := by simp [endThawStore, vatRef]) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVowAddress_thaw (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := endThawStore } evm
        vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endThawStore } evm
      vowRef = .ok { base := "vow", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind,
      endThawStore]
  have hty : storageTypeAt? contract.storage ({ base := "vow", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  unfold vowAddr
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := by simp [endThawStore, vowRef]) (her := her)
    (hty := hty) (hloc := endConfig_storage_vow),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalThawVatDaiArgs (evm : EVM.State) :
    evalExprs? config { contract := contract, locals := endThawStore } evm
      [vowAddr] =
      .ok [.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)] := by
  simp [evalExprs?, EvalResult.bind, bind, pure, endEvalVowAddress_thaw]

theorem endThawVatDaiReturnMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endThawVatDaiReturnMem σ I out) = ⟨128⟩ := by
  have hfacts := callOutputFacts (endThawVatDaiCallMem σ I) out
    (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) hout
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      have := endThawVatDaiCallMem_size_ge164 σ I
      omega)
  have hsize :
      (endThawVatDaiReturnMem σ I out).size =
        (endThawVatDaiCallMem σ I).size := by
    simpa [endThawVatDaiReturnMem] using hfacts.size
  have hread :
      (endThawVatDaiReturnMem σ I out).readWithPadding 64 32 =
        (endThawVatDaiCallMem σ I).readWithPadding 64 32 := by
    exact hfacts.readBelow 64 (by native_decide)
  have hbase := endThawVatDaiCallMem_mload64 σ I
  unfold memLoad at hbase ⊢
  rw [show (UInt256.ofNat 64).toNat = 64 from by native_decide] at hbase ⊢
  rw [if_neg (by
    rw [hsize]
    have := endThawVatDaiCallMem_size_ge164 σ I
    omega)]
  rw [hread]
  rw [if_neg (by
    have := endThawVatDaiCallMem_size_ge164 σ I
    omega)] at hbase
  exact hbase

theorem endThawVatDaiReturnMem_mload128 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) (h32 : 32 ≤ out.size) :
    memLoad (UInt256.ofNat 128) (endThawVatDaiReturnMem σ I out) =
      endThawUIntReturnWord out := by
  have hfacts := callOutputFacts (endThawVatDaiCallMem σ I) out
    (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) hout
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      have := endThawVatDaiCallMem_size_ge164 σ I
      omega)
  have hsize :
      (endThawVatDaiReturnMem σ I out).size =
        (endThawVatDaiCallMem σ I).size := by
    simpa [endThawVatDaiReturnMem] using hfacts.size
  have hread :
      (endThawVatDaiReturnMem σ I out).readWithPadding 128 32 =
        out.extract 0 32 := by
    exact hfacts.readWord (by native_decide) h32
  unfold memLoad
  rw [show (UInt256.ofNat 128).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [hsize]
    have := endThawVatDaiCallMem_size_ge164 σ I
    omega)]
  rw [hread]

theorem endThawAfterVatDaiFrame_get_vatDai (out : ByteArray) :
    (endThawAfterVatDaiFrame out).locals.get? "vatDai" =
      some (endUIntValue (endThawUIntReturnWord out)) := by
  exact store_get_self endThawStore "vatDai" (endUIntValue (endThawUIntReturnWord out))

theorem endEvalVatDaiVar_thaw (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (endThawAfterVatDaiFrame out) evm (.var "vatDai") =
      .ok (endUIntValue (endThawUIntReturnWord out)) := by
  simp [evalExpr?, EvalResult.ofOption, endThawAfterVatDaiFrame_get_vatDai, collapseReturns]

theorem endEvalVatDaiEqZero_thaw_true (evm : EVM.State) (out : ByteArray)
    (hzero : endThawUIntReturnWord out = ⟨0⟩) :
    evalExpr? config (endThawAfterVatDaiFrame out) evm
      (.binary .eq (.var "vatDai") (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatDaiVar_thaw evm out]
  rw [hzero]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?,
    endUIntValue]

theorem endEvalVatDaiEqZero_thaw_false (evm : EVM.State) (out : ByteArray)
    (hnonzero : endThawUIntReturnWord out ≠ ⟨0⟩) :
    evalExpr? config (endThawAfterVatDaiFrame out) evm
      (.binary .eq (.var "vatDai") (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatDaiVar_thaw evm out]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExpr?]
  have hnat : (endThawUIntReturnWord out).toNat ≠ 0 := by
    intro hzero
    exact hnonzero (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat, endUIntValue]

abbrev endThawAddStore (evm : EVM.State) : Store :=
  ((∅ : Store).insert "y" (endUIntValue (endThawWaitWord evm))).insert "x"
    (endUIntValue (endThawWhenWord evm))

abbrev endThawAddZStore (evm : EVM.State) : Store :=
  (endThawAddStore evm).insert "z" (endUIntValue (endThawDeadlineWord evm))

abbrev endThawAfterDeadlineFrame (out : ByteArray) (evm : EVM.State) : Frame :=
  { contract := contract,
    locals := (endThawAfterVatDaiFrame out).locals.insert "deadline"
      (endUIntValue (endThawDeadlineWord evm)) }

theorem endThawAfterVatDaiFrame_get_when_none (out : ByteArray) :
    (endThawAfterVatDaiFrame out).locals.get? "when" = none := by
  unfold endThawAfterVatDaiFrame
  rw [store_get_ne endThawStore (k := "vatDai") (a := "when")
    (collapseReturns [endUIntValue (endThawUIntReturnWord out)]) (by decide)]
  exact endThawStore_get_none "when"

theorem endThawAfterVatDaiFrame_get_wait_none (out : ByteArray) :
    (endThawAfterVatDaiFrame out).locals.get? "wait" = none := by
  unfold endThawAfterVatDaiFrame
  rw [store_get_ne endThawStore (k := "vatDai") (a := "wait")
    (collapseReturns [endUIntValue (endThawUIntReturnWord out)]) (by decide)]
  exact endThawStore_get_none "wait"

theorem endThawAfterDeadlineFrame_get_vat_none (out : ByteArray) (evm : EVM.State) :
    (endThawAfterDeadlineFrame out evm).locals.get? "vat" = none := by
  unfold endThawAfterDeadlineFrame endThawAfterVatDaiFrame
  rw [store_get_ne (endThawStore.insert "vatDai"
      (collapseReturns [endUIntValue (endThawUIntReturnWord out)]))
    (k := "deadline") (a := "vat") (endUIntValue (endThawDeadlineWord evm))
    (by decide)]
  rw [store_get_ne endThawStore (k := "vatDai") (a := "vat")
    (collapseReturns [endUIntValue (endThawUIntReturnWord out)]) (by decide)]
  exact endThawStore_get_none "vat"

theorem endEvalWhenStorage_thaw_afterVatDai (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (endThawAfterVatDaiFrame out) evm (.storage whenRef) =
      .ok (endUIntValue (endThawWhenWord evm)) := by
  have her : evalStorageRef config (endThawAfterVatDaiFrame out) evm
      whenRef = .ok { base := "when", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, whenRef, EvalResult.bind, pure, bind,
      endThawAfterVatDaiFrame, endThawStore]
  have hty : storageTypeAt? contract.storage ({ base := "when", steps := [] } : EvaledStorageRef)
      = some (.elem (.int uint256Int)) := by decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endThawAfterVatDaiFrame_get_when_none out) (her := her) (hty := hty)
    (hloc := endConfig_storage_when)]
  simp [endRuntimeStorageLocLoad_uint256, endThawWhenWord, endUIntValue]

theorem endEvalWaitStorage_thaw_afterVatDai (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (endThawAfterVatDaiFrame out) evm (.storage waitRef) =
      .ok (endUIntValue (endThawWaitWord evm)) := by
  have her : evalStorageRef config (endThawAfterVatDaiFrame out) evm
      waitRef = .ok { base := "wait", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, waitRef, EvalResult.bind, pure, bind,
      endThawAfterVatDaiFrame, endThawStore]
  have hty : storageTypeAt? contract.storage ({ base := "wait", steps := [] } : EvaledStorageRef)
      = some (.elem (.int uint256Int)) := by decide
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endThawAfterVatDaiFrame_get_wait_none out) (her := her) (hty := hty)
    (hloc := endConfig_storage_wait)]
  simp [endRuntimeStorageLocLoad_uint256, endThawWaitWord, endUIntValue]

theorem endEvalThawAddArgs (evm : EVM.State) (out : ByteArray) :
    evalExprs? config (endThawAfterVatDaiFrame out) evm
      [.storage whenRef, .storage waitRef] =
      .ok [endUIntValue (endThawWhenWord evm), endUIntValue (endThawWaitWord evm)] := by
  rw [evalExprs?]
  rw [endEvalWhenStorage_thaw_afterVatDai evm out]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [endEvalWaitStorage_thaw_afterVatDai evm out]
  simp [evalExprs?, EvalResult.bind, bind, pure]

theorem endBindParams_add_thaw (evm : EVM.State) :
    bindParams? addFunction.params
      [endUIntValue (endThawWhenWord evm), endUIntValue (endThawWaitWord evm)] =
      some (endThawAddStore evm) := by
  simp [bindParams?, addFunction, endThawAddStore, endUIntValue]

theorem endThawAddStore_get_x (evm : EVM.State) :
    (endThawAddStore evm).get? "x" = some (endUIntValue (endThawWhenWord evm)) := by
  exact store_get_self ((∅ : Store).insert "y" (endUIntValue (endThawWaitWord evm)))
    "x" (endUIntValue (endThawWhenWord evm))

theorem endThawAddStore_get_y (evm : EVM.State) :
    (endThawAddStore evm).get? "y" = some (endUIntValue (endThawWaitWord evm)) := by
  unfold endThawAddStore
  rw [store_get_ne ((∅ : Store).insert "y" (endUIntValue (endThawWaitWord evm)))
    (k := "x") (a := "y") (endUIntValue (endThawWhenWord evm)) (by decide)]
  exact store_get_self (∅ : Store) "y" (endUIntValue (endThawWaitWord evm))

theorem endThawAddZStore_get_z (evm : EVM.State) :
    (endThawAddZStore evm).get? "z" = some (endUIntValue (endThawDeadlineWord evm)) := by
  exact store_get_self (endThawAddStore evm) "z" (endUIntValue (endThawDeadlineWord evm))

theorem endThawAddZStore_get_x (evm : EVM.State) :
    (endThawAddZStore evm).get? "x" = some (endUIntValue (endThawWhenWord evm)) := by
  unfold endThawAddZStore
  rw [store_get_ne (endThawAddStore evm) (k := "z") (a := "x")
    (endUIntValue (endThawDeadlineWord evm)) (by decide)]
  exact endThawAddStore_get_x evm

theorem endThawDeadlineWord_toNat (evm : EVM.State)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size) :
    (endThawDeadlineWord evm).toNat =
      (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat := by
  unfold endThawDeadlineWord
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]

theorem endEvalAddThawExpr (evm : EVM.State)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endThawAddStore evm } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .ok (endUIntValue (endThawDeadlineWord evm)) := by
  have hsum := endThawDeadlineWord_toNat evm hfit
  have hfitPow :
      (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hnotHi :
      ¬ Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) ≥
        (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact Int.ofNat_lt.mpr hfitPow
  have haddInt :
      Int.ofNat (endThawWhenWord evm).toNat + Int.ofNat (endThawWaitWord evm).toNat =
        Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) := by
    exact (Nat.cast_add (endThawWhenWord evm).toNat (endThawWaitWord evm).toNat).symm
  unfold u256
  simp only [evalExpr?, endThawAddStore_get_x, endThawAddStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int,
    endUIntValue]
  rw [haddInt]
  have hcond :
      (decide (Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) < 0) ||
        decide (Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) ≥
          (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg :
        decide (Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) < 0) =
          false :=
      decide_eq_false (show
        ¬ Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) ≥
          (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [hsum]

theorem endEvalAddThawExpr_revert (evm : EVM.State)
    (hover : UInt256.size ≤
      (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) :
    evalExpr? config { contract := contract, locals := endThawAddStore evm } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .revert := by
  have hhi :
      decide (Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) ≥
        (2 : Int) ^ (256 : Nat)) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  have haddInt :
      Int.ofNat (endThawWhenWord evm).toNat + Int.ofNat (endThawWaitWord evm).toNat =
        Int.ofNat ((endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) := by
    exact (Nat.cast_add (endThawWhenWord evm).toNat (endThawWaitWord evm).toNat).symm
  unfold u256
  simp only [evalExpr?, endThawAddStore_get_x, endThawAddStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int,
    endUIntValue]
  rw [haddInt, hhi]
  simp

theorem endEvalAddThawGuard (evm : EVM.State)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endThawAddZStore evm } evm
      (.binary .ge (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hsum := endThawDeadlineWord_toNat evm hfit
  have hgeProp :
      Int.ofNat (endThawWhenWord evm).toNat ≤
        Int.ofNat (endThawDeadlineWord evm).toNat := by
    rw [hsum]
    exact Int.ofNat_le.mpr (by omega)
  have hge :
      decide (Int.ofNat (endThawDeadlineWord evm).toNat ≥
        Int.ofNat (endThawWhenWord evm).toNat) = true := by
    exact decide_eq_true hgeProp
  simp only [evalExpr?, endThawAddZStore_get_z, endThawAddZStore_get_x,
    EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?, endUIntValue]
  rw [hge]

theorem endAddThawFunctionOk (evm : EVM.State)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endThawAddStore evm } evm
      addFunction.body
      (.returned { contract := contract, locals := endThawAddZStore evm } evm
        (some [endUIntValue (endThawDeadlineWord evm)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [addFunction, endThawAddZStore] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl
        (name := "z") (ty := some uint256)
        (expr := u256 (.binary .add (.var "x") (.var "y")))
        (value := endUIntValue (endThawDeadlineWord evm))
        (endEvalAddThawExpr evm hfit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAddThawGuard evm hfit)) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.var "z"])
          (values := [endUIntValue (endThawDeadlineWord evm)])
          (by
            simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
              endThawAddZStore_get_z])))

theorem endAddThawFunctionRevert (evm : EVM.State)
    (hover : UInt256.size ≤
      (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) :
    ExecFuncBody config { contract := contract, locals := endThawAddStore evm } evm
      addFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [addFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalAddThawExpr_revert evm hover)))

theorem endThawInternalAddOk (evm : EVM.State) (out : ByteArray)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size) :
    ExecStmt config (endThawAfterVatDaiFrame out) evm
      (.internalCall "add" [.storage whenRef, .storage waitRef] "deadline")
      (.ok (endThawAfterDeadlineFrame out evm) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endThawAfterDeadlineFrame] using
    internalCallFunctionReturn
      (cfg := config) (caller := endThawAfterVatDaiFrame out)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "deadline")
      (args := [.storage whenRef, .storage waitRef])
      (argVals := [endUIntValue (endThawWhenWord evm), endUIntValue (endThawWaitWord evm)])
      (callee := addFunction) (locals := endThawAddStore evm)
      (calleeSolm := { contract := contract, locals := endThawAddZStore evm })
      (value := some [endUIntValue (endThawDeadlineWord evm)])
      (endEvalThawAddArgs evm out)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_thaw evm)
      (endAddThawFunctionOk evm hfit)

theorem endThawInternalAddRevert (evm : EVM.State) (out : ByteArray)
    (hover : UInt256.size ≤
      (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) :
    ExecStmt config (endThawAfterVatDaiFrame out) evm
      (.internalCall "add" [.storage whenRef, .storage waitRef] "deadline") .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endThawAfterVatDaiFrame out) (evm := evm)
    (name := "add") (retVar := "deadline")
    (args := [.storage whenRef, .storage waitRef])
    (argVals := [endUIntValue (endThawWhenWord evm), endUIntValue (endThawWaitWord evm)])
    (callee := addFunction) (locals := endThawAddStore evm)
    (endEvalThawAddArgs evm out)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_thaw evm)
    (endAddThawFunctionRevert evm hover)

theorem endThawAfterDeadlineFrame_get_deadline (evm : EVM.State) (out : ByteArray) :
    (endThawAfterDeadlineFrame out evm).locals.get? "deadline" =
      some (endUIntValue (endThawDeadlineWord evm)) := by
  exact store_get_self (endThawAfterVatDaiFrame out).locals "deadline"
    (endUIntValue (endThawDeadlineWord evm))

theorem endEvalDeadlineVar_thaw (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm (.var "deadline") =
      .ok (endUIntValue (endThawDeadlineWord evm)) := by
  simp [evalExpr?, EvalResult.ofOption, endThawAfterDeadlineFrame_get_deadline]

theorem endEvalNow_thaw_afterDeadline (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm nowT =
      .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
  simp only [nowT, evalExpr?, envValue]
  rfl

theorem endEvalThawTimestampGuard_true (evm : EVM.State) (out : ByteArray)
    (hle : (endThawDeadlineWord evm).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm
      (.binary .ge nowT (.var "deadline")) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalNow_thaw_afterDeadline evm out]
  simp only [EvalResult.bind, bind]
  rw [endEvalDeadlineVar_thaw evm out]
  simp only [evalBinaryOp?, endUIntValue]
  have hdec :
      decide (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≥
        Int.ofNat (endThawDeadlineWord evm).toNat) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr hle)
  rw [hdec]

theorem endEvalThawTimestampGuard_false (evm : EVM.State) (out : ByteArray)
    (hlt : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (endThawDeadlineWord evm).toNat) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm
      (.binary .ge nowT (.var "deadline")) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalNow_thaw_afterDeadline evm out]
  simp only [EvalResult.bind, bind]
  rw [endEvalDeadlineVar_thaw evm out]
  simp only [evalBinaryOp?, endUIntValue]
  have hdec :
      decide (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat ≥
        Int.ofNat (endThawDeadlineWord evm).toNat) = false := by
    exact decide_eq_false (by
      intro hle
      exact Nat.not_lt_of_ge (Int.ofNat_le.mp hle) hlt)
  rw [hdec]

theorem endEvalVatAddress_thaw_afterDeadline (evm : EVM.State) (out : ByteArray) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config (endThawAfterDeadlineFrame out evm) evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind,
      endThawAfterDeadlineFrame, endThawAfterVatDaiFrame, endThawStore]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endThawAfterDeadlineFrame_get_vat_none out evm) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVatCodeGuard_thaw_afterDeadline_true (evm : EVM.State) (out : ByteArray)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endThawAfterDeadlineFrame out evm).locals)
    (receiver := .storage vatRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask)
    (endEvalVatAddress_thaw_afterDeadline evm out) hcode

theorem endEvalVatCodeGuard_thaw_afterDeadline_false (evm : EVM.State) (out : ByteArray)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endThawAfterDeadlineFrame out evm) evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endThawAfterDeadlineFrame out evm).locals)
    (receiver := .storage vatRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask)
    (endEvalVatAddress_thaw_afterDeadline evm out) hnocode

theorem endThawAfterVatDaiPrefixOk (evm : EVM.State) (out : ByteArray)
    (hvatDai : endThawUIntReturnWord out = ⟨0⟩)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size)
    (htime : (endThawDeadlineWord evm).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config (endThawAfterVatDaiFrame out) evm
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
      (.ok (endThawAfterDeadlineFrame out evm) evm) := by
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (endEvalVatDaiEqZero_thaw_true evm out hvatDai)) <|
    ExecBlock.consNormal (endThawInternalAddOk evm out hfit) <|
    ExecBlock.consNormal (ExecStmt.requireTrue
      (endEvalThawTimestampGuard_true evm out htime)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue
      (endEvalVatCodeGuard_thaw_afterDeadline_true evm out hvatCode)) <|
    ExecBlock.nil

theorem endThawAfterVatDaiRequireFail (evm : EVM.State) (out : ByteArray)
    (hvatDai : endThawUIntReturnWord out ≠ ⟨0⟩) :
    ExecBlock config (endThawAfterVatDaiFrame out) evm
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
      .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (endEvalVatDaiEqZero_thaw_false evm out hvatDai))

theorem endThawAfterVatDaiAddFail (evm : EVM.State) (out : ByteArray)
    (hvatDai : endThawUIntReturnWord out = ⟨0⟩)
    (hover : UInt256.size ≤
      (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat) :
    ExecBlock config (endThawAfterVatDaiFrame out) evm
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (endEvalVatDaiEqZero_thaw_true evm out hvatDai)) <|
    ExecBlock.consRevert (endThawInternalAddRevert evm out hover)

theorem endThawAfterVatDaiTimeFail (evm : EVM.State) (out : ByteArray)
    (hvatDai : endThawUIntReturnWord out = ⟨0⟩)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size)
    (htime : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
      (endThawDeadlineWord evm).toNat) :
    ExecBlock config (endThawAfterVatDaiFrame out) evm
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (endEvalVatDaiEqZero_thaw_true evm out hvatDai)) <|
    ExecBlock.consNormal (endThawInternalAddOk evm out hfit) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse (endEvalThawTimestampGuard_false evm out htime))

theorem endThawAfterVatDaiVatNoCode (evm : EVM.State) (out : ByteArray)
    (hvatDai : endThawUIntReturnWord out = ⟨0⟩)
    (hfit : (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size)
    (htime : (endThawDeadlineWord evm).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecBlock config (endThawAfterVatDaiFrame out) evm
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
      .reverted := by
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (endEvalVatDaiEqZero_thaw_true evm out hvatDai)) <|
    ExecBlock.consNormal (endThawInternalAddOk evm out hfit) <|
    ExecBlock.consNormal
      (ExecStmt.requireTrue (endEvalThawTimestampGuard_true evm out htime)) <|
    ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endEvalVatCodeGuard_thaw_afterDeadline_false evm out hvatNoCode))

theorem endX_thaw_live_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hlive : endThawLiveWorldWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨707⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  rcases hreach with ⟨k, C, rd707⟩
  have hcond : UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) =
      UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 8) ≠ ⟨0⟩ := by
      simpa [endThawLiveWorldWord] using hlive
    exact Reasoning.Theory.isZero_eq_zero_of_ne hread
  obtain ⟨_, _, rd4534⟩ :=
    endRuntimeBlocks.endRuntime_block_4525_fallthrough
      (R := [⟨562⟩, sel]) (by simp) hcond
      (endRuntimeBlocks.endRuntime_block_707
        (R := [sel]) (by simp) (by jump_dest) rd707)
  exact endRuntimeBlocks.endRuntime_block_4534 (R := [⟨562⟩, sel]) (by simp) rd4534

theorem endX_thaw_debt_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hlive : endThawLiveWorldWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWorldWord σ I ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨707⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  rcases hreach with ⟨k, C, rd707⟩
  have hcondLive :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 8) = ⟨0⟩ := by
      simpa [endThawLiveWorldWord] using hlive
    rw [hread]
    decide
  obtain ⟨_, _, rd4595⟩ :=
    endRuntimeBlocks.endRuntime_block_4525_taken
      (R := [⟨562⟩, sel]) (by simp) hcondLive (by jump_dest)
      (endRuntimeBlocks.endRuntime_block_707
        (R := [sel]) (by simp) (by jump_dest) rd707)
  have hcondDebt :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 11)) =
        UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 11) ≠ ⟨0⟩ := by
      simpa [endThawDebtWorldWord] using hdebt
    exact Reasoning.Theory.isZero_eq_zero_of_ne hread
  obtain ⟨_, _, rd4604⟩ :=
    endRuntimeBlocks.endRuntime_block_4595_fallthrough
      (R := [⟨562⟩, sel]) (by simp) hcondDebt rd4595
  exact endRuntimeBlocks.endRuntime_block_4604 (R := [⟨562⟩, sel]) (by simp) rd4604

theorem endX_thaw_vat_dai_no_code {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hlive : endThawLiveWorldWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWorldWord σ I = ⟨0⟩)
    (hvatNoCode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨707⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  rcases hreach with ⟨k, C, rd707⟩
  have hcondLive :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 8) = ⟨0⟩ := by
      simpa [endThawLiveWorldWord] using hlive
    rw [hread]
    decide
  obtain ⟨_, _, rd4595⟩ :=
    endRuntimeBlocks.endRuntime_block_4525_taken
      (R := [⟨562⟩, sel]) (by simp) hcondLive (by jump_dest)
      (endRuntimeBlocks.endRuntime_block_707
        (R := [sel]) (by simp) (by jump_dest) rd707)
  have hcondDebt :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 11)) ≠ UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 11) = ⟨0⟩ := by
      simpa [endThawDebtWorldWord] using hdebt
    rw [hread]
    decide
  obtain ⟨_, _, rd4668⟩ :=
    endRuntimeBlocks.endRuntime_block_4595_taken
      (R := [⟨562⟩, sel]) (by simp) hcondDebt (by jump_dest) rd4595
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ
            (UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    have htarget :
        extCodeSizeWord σ
            (UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))) = ⟨0⟩ := by
      simpa [endPackVatTarget, endPackCallAddrMask_eq_solc, u256_land_comm] using hvatNoCode
    rw [htarget]
    decide
  obtain ⟨_, _, rd4745⟩ :=
    endRuntimeBlocks.endRuntime_block_4668_fallthrough
      (R := [⟨562⟩, sel]) (by simp) hcondCode rd4668
  exact endRuntimeBlocks.endRuntime_block_4745
    (R := endRuntimeBlocks.endRuntime_block_4668_fallthrough_stack
      (ee := I) (mem := solcFreePtrMem) (σ := σ) (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_4668_fallthrough_stack])
    rd4745

theorem endX_thaw_to_vat_dai_call {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hlive : endThawLiveWorldWord σ I = ⟨0⟩)
    (hdebt : endThawDebtWorldWord σ I = ⟨0⟩)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨707⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4751⟩
      (endThawVatDaiCallStack σ I sel) (endThawVatDaiCallMem σ I) aw
      ByteArray.empty (cA, σ) k C := by
  rcases hreach with ⟨k, C, rd707⟩
  have hcondLive :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 8)) ≠ UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 8) = ⟨0⟩ := by
      simpa [endThawLiveWorldWord] using hlive
    rw [hread]
    decide
  obtain ⟨_, _, rd4595⟩ :=
    endRuntimeBlocks.endRuntime_block_4525_taken
      (R := [⟨562⟩, sel]) (by simp) hcondLive (by jump_dest)
      (endRuntimeBlocks.endRuntime_block_707
        (R := [sel]) (by simp) (by jump_dest) rd707)
  have hcondDebt :
      UInt256.isZero (storageRead I.codeOwner σ (UInt256.ofNat 11)) ≠
        UInt256.ofNat 0 := by
    have hread : storageRead I.codeOwner σ (UInt256.ofNat 11) = ⟨0⟩ := by
      simpa [endThawDebtWorldWord] using hdebt
    rw [hread]
    decide
  obtain ⟨_, _, rd4668⟩ :=
    endRuntimeBlocks.endRuntime_block_4595_taken
      (R := [⟨562⟩, sel]) (by simp) hcondDebt (by jump_dest) rd4595
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord σ
            (UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))))) ≠
        UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord σ
            (UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 1))
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))) ≠ ⟨0⟩ := by
      rw [hmaskGenerated]
      rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
      simpa [endPackVatTarget] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw4749, k4749, C4749, rd4749⟩ :=
    endRuntimeBlocks.endRuntime_block_4668_taken_packed
      (R := [⟨562⟩, sel]) (by simp) hcondCode (by jump_dest) rd4668
  have hfree : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  have hcallRaw := endThawVatDaiCallMem_mload64 σ I
  dsimp [endThawVatDaiCallMem, endRuntimeBlocks.endRuntime_block_4668_taken_memory] at hcallRaw
  rw [hfree] at hcallRaw
  have hlen :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + UInt256.ofNat 36 = ⟨36⟩ := by
    native_decide
  have hend : (⟨128⟩ : UInt256) + UInt256.ofNat 36 = ⟨164⟩ := by
    native_decide
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_4668_taken_stack (ee := I)
          (mem := solcFreePtrMem) (σ := σ) (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endThawVatDaiCallStack σ I sel := by
    dsimp [endRuntimeBlocks.endRuntime_block_4668_taken_stack,
      endThawVatDaiCallStack, endThawVatDaiCallRest, endThawVatDaiSelectorWord,
      endPackVatTarget]
    rw [hfree, hcallRaw, hlen, hend, hmaskGenerated]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
    rw [show UInt256.ofNat 32 = (⟨32⟩ : UInt256) from by native_decide]
  have rd4749' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4749⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          endThawVatDaiCallStack σ I sel)
        (endThawVatDaiCallMem σ I) aw4749 ByteArray.empty (cA, σ) k4749 C4749 := by
    simpa [endThawVatDaiCallMem, hstackTaken] using rd4749
  have rd4751 := endRuntimeBlocks.endRuntime_block_4749
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := endThawVatDaiCallStack σ I sel)
    (by simp [endThawVatDaiCallStack, endThawVatDaiCallRest]) rd4749'
  exact ⟨aw4749, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_4749_stack] using rd4751⟩

set_option maxHeartbeats 12000000 in
theorem endThawVatDaiExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm} :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endThawVatDaiCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endThawStore } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
          (perm := false) ]
      (sequenceExit ⟨4791⟩
        (fun cur frame e =>
          frame = endThawAfterVatDaiFrame cur.rdata ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          32 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64) (endThawVatDaiReturnMem σ I cur.rdata),
              ⟨562⟩, sel] ∧
          cur.mem = endThawVatDaiReturnMem σ I cur.rdata ∧
          cur.aw = endThawAfterVatDaiAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨4751⟩ = some (.GAS, .none); decide)
    (by simp [endThawVatDaiCallStack, endThawVatDaiCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨4752⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endThawVatDaiCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_thaw]
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
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 4)
    rw [h.env] at hload
    rw [endEvalThawVatDaiArgs]
    rw [h.env]
    change EvalResult.ok
      [Value.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
          solcAddrMask).toNat)] =
      EvalResult.ok
        [Value.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat)]
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 4)) solcAddrMask]
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_dai σ I]
    change some (endThawVatDaiEncodedCall σ I) =
      some ((endThawVatDaiCallMem σ I).readWithPadding 128 36)
    rw [endThawVatDaiCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h32 : 32 ≤ out.size
    · have hdecode : config.externalABI.decode? "dai" out =
          some [endUIntValue (endThawUIntReturnWord out)] := by
        change externalABI.decode? "dai" out =
          some [endUIntValue (endThawUIntReturnWord out)]
        exact endExternalDecode_uint256_ok "dai" (by exact Or.inl rfl) h32
      rw [hdecode]
      intro rd hrel
      have rd4753 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4753⟩
            ((⟨1⟩ : UInt256) :: endThawVatDaiCallRest σ I sel)
            (endThawVatDaiReturnMem σ I out) (endThawVatDaiCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endThawVatDaiCallStack,
          endThawVatDaiCallRest, endThawVatDaiCallAw, endThawVatDaiReturnMem]
          using rd
      have rd4769 := endRuntimeBlocks.endRuntime_block_4753_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endThawVatDaiCallRest σ I sel)
        (by simp [endThawVatDaiCallRest]) (by native_decide) (by jump_dest) rd4753
      have rd4769' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4769⟩
            [⟨0⟩, ⟨164⟩, endThawVatDaiSelectorWord, endPackVatTarget σ I,
              ⟨562⟩, sel]
            (endThawVatDaiReturnMem σ I out) (endThawVatDaiCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_4753_taken_stack,
          endThawVatDaiCallRest] using rd4769
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact h32
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd4791 := endRuntimeBlocks.endRuntime_block_4769_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endThawVatDaiSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd4769'
      refine ⟨.ok (endThawAfterVatDaiFrame out) evm',
        Endpoint.reached (endThawAfterVatDaiCursor σ I sel aw out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endThawAfterVatDaiCursor, endThawAfterVatDaiAw,
            endRuntimeBlocks.endRuntime_block_4769_taken_stack] using rd4791⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h32, rfl, rfl, rfl⟩
    · have hshort : out.size < 32 := by omega
      have hdecode : config.externalABI.decode? "dai" out = none := by
        change externalABI.decode? "dai" out = none
        exact endExternalDecode_uint256_none_short "dai" (by exact Or.inl rfl) hshort
      rw [hdecode]
      intro rd
      have rd4753 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4753⟩
            ((⟨1⟩ : UInt256) :: endThawVatDaiCallRest σ I sel)
            (endThawVatDaiReturnMem σ I out) (endThawVatDaiCallAw aw) out
            world' k' C' := by
        simpa [gasCursor, callCursor, endThawVatDaiCallStack,
          endThawVatDaiCallRest, endThawVatDaiCallAw, endThawVatDaiReturnMem]
          using rd
      have rd4769 := endRuntimeBlocks.endRuntime_block_4753_taken
        (x0 := (⟨1⟩ : UInt256)) (R := endThawVatDaiCallRest σ I sel)
        (by simp [endThawVatDaiCallRest]) (by native_decide) (by jump_dest) rd4753
      have rd4769' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4769⟩
            [⟨0⟩, ⟨164⟩, endThawVatDaiSelectorWord, endPackVatTarget σ I,
              ⟨562⟩, sel]
            (endThawVatDaiReturnMem σ I out) (endThawVatDaiCallAw aw) out
            world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_4753_taken_stack,
          endThawVatDaiCallRest] using rd4769
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd4787 := endRuntimeBlocks.endRuntime_block_4769_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := ⟨164⟩)
        (x2 := endThawVatDaiSelectorWord) (x3 := endPackVatTarget σ I)
        (R := [⟨562⟩, sel])
        (by simp) hretcond rd4769'
      exact endRuntimeBlocks.endRuntime_block_4787
        (R := endRuntimeBlocks.endRuntime_block_4769_fallthrough_stack
          (mem := endThawVatDaiReturnMem σ I out) (rdata := out)
          (R := [⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_4769_fallthrough_stack])
        rd4787
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd4753 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4753⟩
          ((⟨0⟩ : UInt256) :: endThawVatDaiCallRest σ I sel)
          (endThawVatDaiReturnMem σ I out) (endThawVatDaiCallAw aw) out
          world' k' C' := by
      simpa [gasCursor, callCursor, endThawVatDaiCallStack,
        endThawVatDaiCallRest, endThawVatDaiCallAw, endThawVatDaiReturnMem]
        using rd
    have rd4760 := endRuntimeBlocks.endRuntime_block_4753_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endThawVatDaiCallRest σ I sel)
      (by simp [endThawVatDaiCallRest]) (by native_decide) rd4753
    exact endRuntimeBlocks.endRuntime_block_4760
      (R := endRuntimeBlocks.endRuntime_block_4753_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endThawVatDaiCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_4753_fallthrough_stack,
        endThawVatDaiCallRest])
      rd4760

theorem endX_thaw_after_vat_dai_nonzero {I g s0 σ sel aw out world k C}
    (hout : out.size < UInt256.size) (h32 : 32 ≤ out.size)
    (hvatDai : endThawUIntReturnWord out ≠ ⟨0⟩)
    (rd : RD endBytecode I g s0
      (endThawAfterVatDaiCursor σ I sel aw out world).pc
      (endThawAfterVatDaiCursor σ I sel aw out world).stack
      (endThawAfterVatDaiCursor σ I sel aw out world).mem
      (endThawAfterVatDaiCursor σ I sel aw out world).aw
      (endThawAfterVatDaiCursor σ I sel aw out world).rdata
      (endThawAfterVatDaiCursor σ I sel aw out world).world k C) :
    RDrev endBytecode g s0 := by
  have hfree := endThawVatDaiReturnMem_mload64 σ I out hout
  have hword := endThawVatDaiReturnMem_mload128 σ I out hout h32
  have rd4791 :
      RD endBytecode I g s0 ⟨4791⟩
        [UInt256.ofNat out.size, ⟨128⟩, ⟨562⟩, sel]
        (endThawVatDaiReturnMem σ I out) (endThawAfterVatDaiAw aw) out world k C := by
    simpa [endThawAfterVatDaiCursor, hfree] using rd
  have hcond :
      UInt256.isZero (memLoad (UInt256.ofNat 128) (endThawVatDaiReturnMem σ I out)) =
        UInt256.ofNat 0 := by
    rw [hword]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hvatDai
  have rd4799 := endRuntimeBlocks.endRuntime_block_4791_fallthrough
    (x0 := UInt256.ofNat out.size) (x1 := ⟨128⟩) (R := [⟨562⟩, sel])
    (by simp) hcond rd4791
  exact endRuntimeBlocks.endRuntime_block_4799
    (R := endRuntimeBlocks.endRuntime_block_4791_fallthrough_stack
      (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_4791_fallthrough_stack])
    rd4799

theorem endX_thaw_after_vat_dai_zero {I g s0 σ sel aw out world k C}
    (hout : out.size < UInt256.size) (h32 : 32 ≤ out.size)
    (hvatDai : endThawUIntReturnWord out = ⟨0⟩)
    (rd : RD endBytecode I g s0
      (endThawAfterVatDaiCursor σ I sel aw out world).pc
      (endThawAfterVatDaiCursor σ I sel aw out world).stack
      (endThawAfterVatDaiCursor σ I sel aw out world).mem
      (endThawAfterVatDaiCursor σ I sel aw out world).aw
      (endThawAfterVatDaiCursor σ I sel aw out world).rdata
      (endThawAfterVatDaiCursor σ I sel aw out world).world k C) :
    ∃ aw' k' C', RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem σ I out) aw' out world k' C' := by
  have hfree := endThawVatDaiReturnMem_mload64 σ I out hout
  have hword := endThawVatDaiReturnMem_mload128 σ I out hout h32
  have rd4791 :
      RD endBytecode I g s0 ⟨4791⟩
        [UInt256.ofNat out.size, ⟨128⟩, ⟨562⟩, sel]
        (endThawVatDaiReturnMem σ I out) (endThawAfterVatDaiAw aw) out world k C := by
    simpa [endThawAfterVatDaiCursor, hfree] using rd
  have hcond :
      UInt256.isZero (memLoad (UInt256.ofNat 128) (endThawVatDaiReturnMem σ I out)) ≠
        UInt256.ofNat 0 := by
    rw [hword, hvatDai]
    decide
  have rd4866 := endRuntimeBlocks.endRuntime_block_4791_taken
    (x0 := UInt256.ofNat out.size) (x1 := ⟨128⟩) (R := [⟨562⟩, sel])
    (by simp) hcond (by jump_dest) rd4791
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_4791_taken_stack] using rd4866⟩

abbrev endThawVatDebtSelectorWord : UInt256 := UInt256.ofNat 231365057

abbrev endThawVatDebtSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 231365057) (UInt256.ofNat 224)

abbrev endThawVatDebtCallMem (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_4956_taken_memory
    (mem := endThawVatDaiReturnMem preσ I outDai)

abbrev endThawVatDebtMemFull (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) : ByteArray :=
  endThawVatDebtSelectorEncodedWord.toByteArray.write 0
    (endThawVatDaiReturnMem preσ I outDai) 128 32

abbrev endThawVatDebtGeneratedMask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
    (UInt256.ofNat 1)

abbrev endThawVatDebtTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land endThawVatDebtGeneratedMask (storageRead I.codeOwner σ (UInt256.ofNat 1))

abbrev endThawVatDebtBaseFree (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) : UInt256 :=
  memLoad (UInt256.ofNat 64) (endThawVatDaiReturnMem preσ I outDai)

abbrev endThawVatDebtCallFree (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) : UInt256 :=
  memLoad (UInt256.ofNat 64) (endThawVatDebtCallMem preσ I outDai)

abbrev endThawVatDebtCallSize (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) : UInt256 :=
  UInt256.sub (endThawVatDebtBaseFree preσ I outDai)
    (endThawVatDebtCallFree preσ I outDai) + UInt256.ofNat 4

abbrev endThawVatDebtCallEnd (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) : UInt256 :=
  endThawVatDebtBaseFree preσ I outDai + UInt256.ofNat 4

abbrev endThawVatDebtCallRest (preσ σ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (sel : UInt256) :
    List UInt256 :=
  [endThawVatDebtCallEnd preσ I outDai, endThawVatDebtSelectorWord,
    endThawVatDebtTarget σ I, ⟨5190⟩, ⟨562⟩, sel]

abbrev endThawVatDebtCallStack (preσ σ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (sel : UInt256) :
    List UInt256 :=
  [endThawVatDebtTarget σ I, ⟨0⟩, endThawVatDebtCallFree preσ I outDai,
    endThawVatDebtCallSize preσ I outDai, endThawVatDebtCallFree preσ I outDai, ⟨32⟩] ++
    endThawVatDebtCallRest preσ σ I outDai sel

abbrev endThawVatDebtCallCursor (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preσ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (outDai rdata : ByteArray) :
    Cursor :=
  { pc := ⟨5030⟩, stack := endThawVatDebtCallStack preσ world.2 I outDai sel,
    mem := endThawVatDebtCallMem preσ I outDai, aw := aw, rdata := rdata,
    world := world }

abbrev endThawVatDebtCallAw (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat
      (endThawVatDebtCallFree preσ I outDai).toNat
      (endThawVatDebtCallSize preσ I outDai).toNat)
      (endThawVatDebtCallFree preσ I outDai).toNat (⟨32⟩ : UInt256).toNat)

abbrev endThawAfterVatDebtAw (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (aw : UInt256) : UInt256 :=
  M (endThawVatDebtCallAw preσ I outDai aw) (UInt256.ofNat 64) (⟨32⟩ : UInt256)

abbrev endThawVatDebtReturnMem (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : ByteArray :=
  outDebt.write 0 (endThawVatDebtCallMem preσ I outDai)
    (endThawVatDebtCallFree preσ I outDai).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat outDebt.size)).toNat

abbrev endThawAfterVatDebtFrame (outDai outDebt : ByteArray) (evm : EVM.State) :
    Frame :=
  { contract := contract,
    locals := (endThawAfterDeadlineFrame outDai evm).locals.insert "vatDebt"
      (collapseReturns [endUIntValue (endThawUIntReturnWord outDebt)]) }

abbrev endThawAfterVatDebtCursor (preσ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outDai outDebt : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5070⟩,
    stack :=
      [UInt256.ofNat outDebt.size,
        memLoad (UInt256.ofNat 64) (endThawVatDebtReturnMem preσ I outDai outDebt),
        ⟨5190⟩, ⟨562⟩, sel],
    mem := endThawVatDebtReturnMem preσ I outDai outDebt,
    aw := endThawAfterVatDebtAw preσ I outDai aw,
    rdata := outDebt, world := world }

theorem endThawVatDaiReturnMem_size (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endThawVatDaiReturnMem σ I out).size = 164 := by
  have hfacts := callOutputFacts (endThawVatDaiCallMem σ I) out
    (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) hout
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      have := endThawVatDaiCallMem_size_ge164 σ I
      omega)
  have hsize :
      (endThawVatDaiReturnMem σ I out).size =
        (endThawVatDaiCallMem σ I).size := by
    simpa [endThawVatDaiReturnMem] using hfacts.size
  rw [hsize, endThawVatDaiCallMem_size]

theorem endThawVatDaiReturnMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (out : ByteArray) (hout : out.size < UInt256.size) :
    (endThawVatDaiReturnMem σ I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hfacts := callOutputFacts (endThawVatDaiCallMem σ I) out
    (⟨128⟩ : UInt256) (⟨32⟩ : UInt256) hout
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      have := endThawVatDaiCallMem_size_ge164 σ I
      omega)
  have hread :
      (endThawVatDaiReturnMem σ I out).readWithPadding 64 32 =
        (endThawVatDaiCallMem σ I).readWithPadding 64 32 := by
    simpa [endThawVatDaiReturnMem] using hfacts.readBelow 64 (by native_decide)
  rw [hread]
  exact endThawVatDaiCallMem_read64 σ I

theorem endThawVatDebtCallMem_eq_full (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    endThawVatDebtCallMem preσ I outDai = endThawVatDebtMemFull preσ I outDai := by
  have hfree := endThawVatDaiReturnMem_mload64 preσ I outDai hout
  unfold endThawVatDebtCallMem endThawVatDebtMemFull endThawVatDebtSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_4956_taken_memory]
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]

theorem endThawVatDebtCallMem_size (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    (endThawVatDebtCallMem preσ I outDai).size = 164 := by
  rw [endThawVatDebtCallMem_eq_full preσ I outDai hout]
  unfold endThawVatDebtMemFull
  exact toByteArray_write32_size_of_le
    (endThawVatDaiReturnMem preσ I outDai) endThawVatDebtSelectorEncodedWord
    128 164 164
    (endThawVatDaiReturnMem_size preσ I outDai hout)
    (by rw [endThawVatDaiReturnMem_size preσ I outDai hout]; omega)
    (by omega)

theorem endThawVatDebtCallMem_read64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    (endThawVatDebtCallMem preσ I outDai).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endThawVatDebtCallMem_eq_full preσ I outDai hout]
  unfold endThawVatDebtMemFull
  rw [toByteArray_write_read_below_of_gap_unbounded
    endThawVatDebtSelectorEncodedWord (endThawVatDaiReturnMem preσ I outDai) 128 64
    (by rw [endThawVatDaiReturnMem_size preσ I outDai hout]; omega) (by omega)]
  exact endThawVatDaiReturnMem_read64 preσ I outDai hout

theorem endThawVatDebtCallMem_mload64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endThawVatDebtCallMem preσ I outDai) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endThawVatDebtCallMem preσ I outDai)
    (by rw [endThawVatDebtCallMem_size preσ I outDai hout]; omega)
    (endThawVatDebtCallMem_read64 preσ I outDai hout)

theorem endThawVatDebtSelectorEncodedWord_prefix :
    (endThawVatDebtSelectorEncodedWord.toByteArray).extract 0 4 = debtSelector := by
  native_decide

theorem endThawVatDebtCallMem_readSelector (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    (endThawVatDebtCallMem preσ I outDai).readWithPadding 128 4 = debtSelector := by
  rw [endThawVatDebtCallMem_eq_full preσ I outDai hout]
  unfold endThawVatDebtMemFull
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endThawVatDebtSelectorEncodedWord (endThawVatDaiReturnMem preσ I outDai) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endThawVatDebtSelectorEncodedWord_prefix]

theorem endThawVatDebtCallMem_readCallData (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    (endThawVatDebtCallMem preσ I outDai).readWithPadding 128 4 = debtSelector := by
  exact endThawVatDebtCallMem_readSelector preσ I outDai hout

theorem endThawVatDebtCallMem_readCallData_raw (preσ : AccountMap) (I : ExecutionEnv)
    (outDai : ByteArray) (hout : outDai.size < UInt256.size) :
    (endThawVatDebtCallMem preσ I outDai).readWithPadding
      (endThawVatDebtCallFree preσ I outDai).toNat
      (endThawVatDebtCallSize preσ I outDai).toNat = debtSelector := by
  have hbase := endThawVatDaiReturnMem_mload64 preσ I outDai hout
  have hfree := endThawVatDebtCallMem_mload64 preσ I outDai hout
  have hsize : endThawVatDebtCallSize preσ I outDai = ⟨4⟩ := by
    unfold endThawVatDebtCallSize endThawVatDebtBaseFree endThawVatDebtCallFree
    rw [hbase, hfree]
    native_decide
  unfold endThawVatDebtCallFree
  rw [hfree, hsize]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show (⟨4⟩ : UInt256).toNat = 4 from by native_decide]
  exact endThawVatDebtCallMem_readCallData preσ I outDai hout

theorem endExternalEncode_debt :
    config.externalABI.encode? "debt" [] = some debtSelector := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "debt" = "cage")]
  rw [if_neg (by decide : ¬ "debt" = "vatIlks")]
  rw [if_neg (by decide : ¬ "debt" = "catIlks")]
  rw [if_neg (by decide : ¬ "debt" = "dogIlks")]
  rw [if_neg (by decide : ¬ "debt" = "spotIlks")]
  rw [if_neg (by decide : ¬ "debt" = "urns")]
  rw [if_neg (by decide : ¬ "debt" = "dai")]
  rw [if_pos (by decide : "debt" = "debt")]

theorem endThawVatDebtReturnMem_size (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    (endThawVatDebtReturnMem preσ I outDai outDebt).size = 164 := by
  have hfree := endThawVatDebtCallMem_mload64 preσ I outDai houtDai
  have hfacts := callOutputFacts (endThawVatDebtCallMem preσ I outDai) outDebt
    (endThawVatDebtCallFree preσ I outDai) (⟨32⟩ : UInt256) houtDebt
    (by
      unfold endThawVatDebtCallFree
      rw [hfree, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      rw [endThawVatDebtCallMem_size preσ I outDai houtDai]
      omega)
  have hsize :
      (endThawVatDebtReturnMem preσ I outDai outDebt).size =
        (endThawVatDebtCallMem preσ I outDai).size := by
    simpa [endThawVatDebtReturnMem] using hfacts.size
  rw [hsize, endThawVatDebtCallMem_size preσ I outDai houtDai]

theorem endThawVatDebtReturnMem_read64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    (endThawVatDebtReturnMem preσ I outDai outDebt).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hfree := endThawVatDebtCallMem_mload64 preσ I outDai houtDai
  have hfacts := callOutputFacts (endThawVatDebtCallMem preσ I outDai) outDebt
    (endThawVatDebtCallFree preσ I outDai) (⟨32⟩ : UInt256) houtDebt
    (by
      unfold endThawVatDebtCallFree
      rw [hfree, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      rw [endThawVatDebtCallMem_size preσ I outDai houtDai]
      omega)
  have hbelow : 64 + 32 ≤ (endThawVatDebtCallFree preσ I outDai).toNat := by
    unfold endThawVatDebtCallFree
    rw [hfree]
    native_decide
  have hread :
      (endThawVatDebtReturnMem preσ I outDai outDebt).readWithPadding 64 32 =
        (endThawVatDebtCallMem preσ I outDai).readWithPadding 64 32 := by
    simpa [endThawVatDebtReturnMem] using hfacts.readBelow 64 hbelow
  rw [hread]
  exact endThawVatDebtCallMem_read64 preσ I outDai houtDai

theorem endThawVatDebtReturnMem_mload64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endThawVatDebtReturnMem preσ I outDai outDebt) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endThawVatDebtReturnMem preσ I outDai outDebt)
    (by rw [endThawVatDebtReturnMem_size preσ I outDai outDebt houtDai houtDebt]; omega)
    (endThawVatDebtReturnMem_read64 preσ I outDai outDebt houtDai houtDebt)

theorem endThawVatDebtReturnMem_mloadCallFree (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (h32 : 32 ≤ outDebt.size) :
    memLoad (endThawVatDebtCallFree preσ I outDai)
        (endThawVatDebtReturnMem preσ I outDai outDebt) =
      endThawUIntReturnWord outDebt := by
  have hfree := endThawVatDebtCallMem_mload64 preσ I outDai houtDai
  have hfacts := callOutputFacts (endThawVatDebtCallMem preσ I outDai) outDebt
    (endThawVatDebtCallFree preσ I outDai) (⟨32⟩ : UInt256) houtDebt
    (by
      unfold endThawVatDebtCallFree
      rw [hfree, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      rw [endThawVatDebtCallMem_size preσ I outDai houtDai]
      omega)
  have hsize :
      (endThawVatDebtReturnMem preσ I outDai outDebt).size =
        (endThawVatDebtCallMem preσ I outDai).size := by
    simpa [endThawVatDebtReturnMem] using hfacts.size
  have hread :
      (endThawVatDebtReturnMem preσ I outDai outDebt).readWithPadding
          (endThawVatDebtCallFree preσ I outDai).toNat 32 =
        outDebt.extract 0 32 := by
    exact hfacts.readWord (by rfl) h32
  unfold memLoad
  unfold endThawVatDebtCallFree
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [hsize, endThawVatDebtCallMem_size preσ I outDai houtDai]
    omega)]
  rw [show (endThawVatDebtCallFree preσ I outDai).toNat = 128 by
    unfold endThawVatDebtCallFree
    rw [hfree]
    native_decide] at hread
  rw [hread]

set_option maxHeartbeats 12000000 in
theorem endThawVatDebtExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm preσ outDai world}
    (houtDai : outDai.size < UInt256.size) (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endThawVatDebtCallCursor world preσ I sel aw outDai rdata)
      k C (endThawAfterDeadlineFrame outDai evm) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ]
      (sequenceExit ⟨5070⟩
        (fun cur frame e =>
          frame = endThawAfterVatDebtFrame outDai cur.rdata evm ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.rdata.size < UInt256.size ∧
          32 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endThawVatDebtReturnMem preσ I outDai cur.rdata),
              ⟨5190⟩, ⟨562⟩, sel] ∧
          cur.mem = endThawVatDebtReturnMem preσ I outDai cur.rdata ∧
          cur.aw = endThawAfterVatDebtAw preσ I outDai aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨5030⟩ = some (.GAS, .none); decide)
    (by simp [endThawVatDebtCallStack, endThawVatDebtCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endThawVatDebtTarget world.2 I).toNat)
    (argVals := [])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨5031⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endThawVatDebtCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_thaw_afterDeadline]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endThawVatDebtTarget world.2 I).toNat))
    rw [hload]
    unfold endThawVatDebtTarget
    rw [show endThawVatDebtGeneratedMask = solcAddrMask from by native_decide]
    rw [u256_land_comm (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    simp [evalExprs?, pure]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endThawVatDebtTarget world.2 I).toNat % EVM.addressModulus % AccountAddress.size =
      (endThawVatDebtTarget world.2 I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_debt]
    change some debtSelector =
      some ((endThawVatDebtCallMem preσ I outDai).readWithPadding
        (endThawVatDebtCallFree preσ I outDai).toNat
        (endThawVatDebtCallSize preσ I outDai).toNat)
    rw [endThawVatDebtCallMem_readCallData_raw preσ I outDai houtDai]
  · intro out evm' world' k' C'
    dsimp only
    intro _ hout
    by_cases h32 : 32 ≤ out.size
    · have hdecode : config.externalABI.decode? "debt" out =
          some [endUIntValue (endThawUIntReturnWord out)] := by
        change externalABI.decode? "debt" out =
          some [endUIntValue (endThawUIntReturnWord out)]
        exact endExternalDecode_uint256_ok "debt" (by exact Or.inr (Or.inl rfl)) h32
      rw [hdecode]
      intro rd hrel
      have rd5032 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5032⟩
            ((⟨1⟩ : UInt256) :: endThawVatDebtCallRest preσ world.2 I outDai sel)
            (endThawVatDebtReturnMem preσ I outDai out)
            (endThawVatDebtCallAw preσ I outDai aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endThawVatDebtCallStack,
          endThawVatDebtCallRest, endThawVatDebtCallAw, endThawVatDebtReturnMem]
          using rd
      have rd5048 := endRuntimeBlocks.endRuntime_block_5032_taken
        (x0 := (⟨1⟩ : UInt256))
        (R := endThawVatDebtCallRest preσ world.2 I outDai sel)
        (by simp [endThawVatDebtCallRest]) (by native_decide) (by jump_dest) rd5032
      have rd5048' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5048⟩
            [⟨0⟩, endThawVatDebtCallEnd preσ I outDai, endThawVatDebtSelectorWord,
              endThawVatDebtTarget world.2 I, ⟨5190⟩, ⟨562⟩, sel]
            (endThawVatDebtReturnMem preσ I outDai out)
            (endThawVatDebtCallAw preσ I outDai aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_5032_taken_stack,
          endThawVatDebtCallRest] using rd5048
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact h32
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd5070 := endRuntimeBlocks.endRuntime_block_5048_taken
        (x0 := (⟨0⟩ : UInt256)) (x1 := endThawVatDebtCallEnd preσ I outDai)
        (x2 := endThawVatDebtSelectorWord) (x3 := endThawVatDebtTarget world.2 I)
        (R := [⟨5190⟩, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd5048'
      refine ⟨.ok (endThawAfterVatDebtFrame outDai out evm) evm',
        Endpoint.reached (endThawAfterVatDebtCursor preσ I sel aw outDai out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endThawAfterVatDebtCursor, endThawAfterVatDebtAw,
            endRuntimeBlocks.endRuntime_block_5048_taken_stack] using rd5070⟩
      · exact ⟨rfl, rfl, hrel, hout, h32, rfl, rfl, rfl⟩
    · have hshort : out.size < 32 := by omega
      have hdecode : config.externalABI.decode? "debt" out = none := by
        change externalABI.decode? "debt" out = none
        exact endExternalDecode_uint256_none_short "debt" (by exact Or.inr (Or.inl rfl))
          hshort
      rw [hdecode]
      intro rd
      have rd5032 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5032⟩
            ((⟨1⟩ : UInt256) :: endThawVatDebtCallRest preσ world.2 I outDai sel)
            (endThawVatDebtReturnMem preσ I outDai out)
            (endThawVatDebtCallAw preσ I outDai aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endThawVatDebtCallStack,
          endThawVatDebtCallRest, endThawVatDebtCallAw, endThawVatDebtReturnMem]
          using rd
      have rd5048 := endRuntimeBlocks.endRuntime_block_5032_taken
        (x0 := (⟨1⟩ : UInt256))
        (R := endThawVatDebtCallRest preσ world.2 I outDai sel)
        (by simp [endThawVatDebtCallRest]) (by native_decide) (by jump_dest) rd5032
      have rd5048' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5048⟩
            [⟨0⟩, endThawVatDebtCallEnd preσ I outDai, endThawVatDebtSelectorWord,
              endThawVatDebtTarget world.2 I, ⟨5190⟩, ⟨562⟩, sel]
            (endThawVatDebtReturnMem preσ I outDai out)
            (endThawVatDebtCallAw preσ I outDai aw) out world' (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_5032_taken_stack,
          endThawVatDebtCallRest] using rd5048
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd5066 := endRuntimeBlocks.endRuntime_block_5048_fallthrough
        (x0 := (⟨0⟩ : UInt256)) (x1 := endThawVatDebtCallEnd preσ I outDai)
        (x2 := endThawVatDebtSelectorWord) (x3 := endThawVatDebtTarget world.2 I)
        (R := [⟨5190⟩, ⟨562⟩, sel])
        (by simp) hretcond rd5048'
      exact endRuntimeBlocks.endRuntime_block_5066
        (R := endRuntimeBlocks.endRuntime_block_5048_fallthrough_stack
          (mem := endThawVatDebtReturnMem preσ I outDai out) (rdata := out)
          (R := [⟨5190⟩, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_5048_fallthrough_stack])
        rd5066
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd5032 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5032⟩
          ((⟨0⟩ : UInt256) :: endThawVatDebtCallRest preσ world.2 I outDai sel)
          (endThawVatDebtReturnMem preσ I outDai out)
          (endThawVatDebtCallAw preσ I outDai aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endThawVatDebtCallStack,
        endThawVatDebtCallRest, endThawVatDebtCallAw, endThawVatDebtReturnMem]
        using rd
    have rd5039 := endRuntimeBlocks.endRuntime_block_5032_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endThawVatDebtCallRest preσ world.2 I outDai sel)
      (by simp [endThawVatDebtCallRest]) (by native_decide) rd5032
    exact endRuntimeBlocks.endRuntime_block_5039
      (R := endRuntimeBlocks.endRuntime_block_5032_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256))
        (R := endThawVatDebtCallRest preσ world.2 I outDai sel))
      (by simp [endRuntimeBlocks.endRuntime_block_5032_fallthrough_stack,
        endThawVatDebtCallRest])
      rd5039

theorem endX_thaw_add_fail {I g s0 preσ sel aw outDai world k C}
    (hover : UInt256.size ≤
      (endThawWhenWorldWord world.2 I).toNat + (endThawWaitWorldWord world.2 I).toNat)
    (rd : RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw outDai world k C) :
    RDrev endBytecode g s0 := by
  obtain ⟨k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_4866
      (cA := world.1) (σ := world.2) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd
  have rd10092' :
      RD endBytecode I g s0 ⟨10092⟩
        [endThawWaitWorldWord world.2 I, endThawWhenWorldWord world.2 I,
          ⟨4880⟩, ⟨562⟩, sel]
        (endThawVatDaiReturnMem preσ I outDai) aw outDai world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_4866_stack, endThawWaitWorldWord,
      endThawWhenWorldWord] using rd10092
  have hcond := endPackAddFailCond (endThawWaitWorldWord world.2 I)
    (endThawWhenWorldWord world.2 I) hover
  have rd10104 := endRuntimeBlocks.endRuntime_block_10092_fallthrough
    (cA := world.1) (σ := world.2)
    (x0 := endThawWaitWorldWord world.2 I) (x1 := endThawWhenWorldWord world.2 I)
    (R := [⟨4880⟩, ⟨562⟩, sel])
    (by simp) hcond rd10092'
  exact endRuntimeBlocks.endRuntime_block_10104
    (cA := world.1) (σ := world.2)
    (R := endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack
      (x0 := endThawWaitWorldWord world.2 I) (x1 := endThawWhenWorldWord world.2 I)
      (R := [⟨4880⟩, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack])
    rd10104

theorem endX_thaw_to_deadline {I g s0 preσ sel aw outDai world k C}
    (hfit : (endThawWhenWorldWord world.2 I).toNat +
      (endThawWaitWorldWord world.2 I).toNat < UInt256.size)
    (rd : RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw outDai world k C) :
    ∃ aw' k' C', RD endBytecode I g s0 ⟨4880⟩
      [endThawDeadlineWorldWord world.2 I, ⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw' outDai world k' C' := by
  obtain ⟨k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_4866
      (cA := world.1) (σ := world.2) (R := [⟨562⟩, sel])
      (by simp) (by jump_dest) rd
  have rd10092' :
      RD endBytecode I g s0 ⟨10092⟩
        [endThawWaitWorldWord world.2 I, endThawWhenWorldWord world.2 I,
          ⟨4880⟩, ⟨562⟩, sel]
        (endThawVatDaiReturnMem preσ I outDai) aw outDai world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_4866_stack, endThawWaitWorldWord,
      endThawWhenWorldWord] using rd10092
  have hcond := endPackAddSuccessCond (endThawWaitWorldWord world.2 I)
    (endThawWhenWorldWord world.2 I) hfit
  have rd10108 := endRuntimeBlocks.endRuntime_block_10092_taken
    (cA := world.1) (σ := world.2)
    (x0 := endThawWaitWorldWord world.2 I) (x1 := endThawWhenWorldWord world.2 I)
    (R := [⟨4880⟩, ⟨562⟩, sel])
    (by simp) hcond (by jump_dest) rd10092'
  have rd4880 := endRuntimeBlocks.endRuntime_block_10108
    (cA := world.1) (σ := world.2)
    (x0 := endThawWaitWorldWord world.2 I + endThawWhenWorldWord world.2 I)
    (x1 := endThawWaitWorldWord world.2 I) (x2 := endThawWhenWorldWord world.2 I)
    (x3 := (⟨4880⟩ : UInt256)) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10092_taken_stack] using rd10108)
  exact ⟨_, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack, endThawDeadlineWorldWord,
      u256_add_comm (endThawWaitWorldWord world.2 I) (endThawWhenWorldWord world.2 I)]
      using rd4880⟩

theorem endX_thaw_time_fail {I g s0 preσ sel aw outDai world k C}
    (hfit : (endThawWhenWorldWord world.2 I).toNat +
      (endThawWaitWorldWord world.2 I).toNat < UInt256.size)
    (htime : (UInt256.ofNat I.header.timestamp).toNat <
      (endThawDeadlineWorldWord world.2 I).toNat)
    (rd : RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw outDai world k C) :
    RDrev endBytecode g s0 := by
  obtain ⟨aw4880, k4880, C4880, rd4880⟩ :=
    endX_thaw_to_deadline (preσ := preσ) (sel := sel) hfit rd
  have hlt :
      UInt256.lt (UInt256.ofNat I.header.timestamp)
        (endThawDeadlineWorldWord world.2 I) = ⟨1⟩ := by
    exact ult_one htime
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.ofNat I.header.timestamp)
            (endThawDeadlineWorldWord world.2 I)) =
        UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd4888 := endRuntimeBlocks.endRuntime_block_4880_fallthrough
    (cA := world.1) (σ := world.2)
    (x0 := endThawDeadlineWorldWord world.2 I) (R := [⟨562⟩, sel])
    (by simp) hcond rd4880
  exact endRuntimeBlocks.endRuntime_block_4888
    (cA := world.1) (σ := world.2)
    (R := endRuntimeBlocks.endRuntime_block_4880_fallthrough_stack (R := [⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_4880_fallthrough_stack])
    rd4888

theorem endX_thaw_to_vat_debt_guard {I g s0 preσ sel aw outDai world k C}
    (hfit : (endThawWhenWorldWord world.2 I).toNat +
      (endThawWaitWorldWord world.2 I).toNat < UInt256.size)
    (htime : (endThawDeadlineWorldWord world.2 I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (rd : RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw outDai world k C) :
    ∃ aw' k' C', RD endBytecode I g s0 ⟨4956⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw' outDai world k' C' := by
  obtain ⟨aw4880, k4880, C4880, rd4880⟩ :=
    endX_thaw_to_deadline (preσ := preσ) (sel := sel) hfit rd
  have hlt :
      UInt256.lt (UInt256.ofNat I.header.timestamp)
        (endThawDeadlineWorldWord world.2 I) = ⟨0⟩ := by
    exact ult_zero htime
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.ofNat I.header.timestamp)
            (endThawDeadlineWorldWord world.2 I)) ≠
        UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd4956 := endRuntimeBlocks.endRuntime_block_4880_taken
    (cA := world.1) (σ := world.2)
    (x0 := endThawDeadlineWorldWord world.2 I) (R := [⟨562⟩, sel])
    (by simp) hcond (by jump_dest) rd4880
  exact ⟨aw4880, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_4880_taken_stack] using rd4956⟩

theorem endX_thaw_vat_debt_no_code {I g s0 preσ sel aw outDai world k C}
    (hfit : (endThawWhenWorldWord world.2 I).toNat +
      (endThawWaitWorldWord world.2 I).toNat < UInt256.size)
    (htime : (endThawDeadlineWorldWord world.2 I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (hvatNoCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw outDai world k C) :
    RDrev endBytecode g s0 := by
  obtain ⟨aw4956, k4956, C4956, rd4956⟩ :=
    endX_thaw_to_vat_debt_guard (preσ := preσ) (sel := sel) hfit htime rd
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner world.2 (UInt256.ofNat 1))))) =
        UInt256.ofNat 0 := by
    have htarget :
        extCodeSizeWord world.2
            (UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1))
              (storageRead I.codeOwner world.2 (UInt256.ofNat 1))) = ⟨0⟩ := by
      simpa [endPackVatTarget, hmaskGenerated] using hvatNoCode
    rw [htarget]
    decide
  obtain ⟨aw5024, k5024, C5024, rd5024⟩ :=
    endRuntimeBlocks.endRuntime_block_4956_fallthrough_packed
      (cA := world.1) (σ := world.2) (R := [⟨562⟩, sel])
      (by simp) hcondCode rd4956
  exact endRuntimeBlocks.endRuntime_block_5024
    (cA := world.1) (σ := world.2)
    (R := endRuntimeBlocks.endRuntime_block_4956_fallthrough_stack
      (ee := I) (mem := endThawVatDaiReturnMem preσ I outDai)
      (σ := world.2) (R := [⟨562⟩, sel]))
    (by
      dsimp only [endRuntimeBlocks.endRuntime_block_4956_fallthrough_stack]
      simp only [List.length_cons, List.length_nil]
      omega)
    rd5024

theorem endX_thaw_to_vat_debt_call {I g s0 preσ sel aw outDai world k C}
    (hout : outDai.size < UInt256.size)
    (hfit : (endThawWhenWorldWord world.2 I).toNat +
      (endThawWaitWorldWord world.2 I).toNat < UInt256.size)
    (htime : (endThawDeadlineWorldWord world.2 I).toNat ≤
      (UInt256.ofNat I.header.timestamp).toNat)
    (hvatCode : extCodeSizeWord world.2 (endPackVatTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g s0 ⟨4866⟩ [⟨562⟩, sel]
      (endThawVatDaiReturnMem preσ I outDai) aw outDai world k C) :
    ∃ aw' k' C', RD endBytecode I g s0 ⟨5030⟩
      (endThawVatDebtCallStack preσ world.2 I outDai sel)
      (endThawVatDebtCallMem preσ I outDai) aw' outDai world k' C' := by
  obtain ⟨aw4956, k4956, C4956, rd4956⟩ :=
    endX_thaw_to_vat_debt_guard (preσ := preσ) (sel := sel) hfit htime rd
  have hmaskGenerated :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  have hcondCode :
      UInt256.isZero (UInt256.isZero
          (extCodeSizeWord world.2 (endThawVatDebtTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    have hnonzero :
        extCodeSizeWord world.2 (endThawVatDebtTarget world.2 I) ≠ ⟨0⟩ := by
      simpa [endThawVatDebtTarget, endThawVatDebtGeneratedMask, endPackVatTarget,
        hmaskGenerated] using hvatCode
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hnonzero]
    native_decide
  obtain ⟨aw5028, k5028, C5028, rd5028⟩ :=
    endRuntimeBlocks.endRuntime_block_4956_taken_packed
      (cA := world.1) (σ := world.2) (R := [⟨562⟩, sel])
      (by simp) hcondCode (by jump_dest) rd4956
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_4956_taken_stack (ee := I)
          (mem := endThawVatDaiReturnMem preσ I outDai) (σ := world.2)
          (R := [⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endThawVatDebtTarget world.2 I)) ::
          endThawVatDebtCallStack preσ world.2 I outDai sel := by
    rfl
  have rd5028' :
      RD endBytecode I g s0 ⟨5028⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endThawVatDebtTarget world.2 I)) ::
          endThawVatDebtCallStack preσ world.2 I outDai sel)
        (endThawVatDebtCallMem preσ I outDai) aw5028 outDai world k5028 C5028 := by
    rw [hstackTaken] at rd5028
    simpa [endThawVatDebtCallMem] using rd5028
  have rd5030 := endRuntimeBlocks.endRuntime_block_5028
    (cA := world.1) (σ := world.2)
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endThawVatDebtTarget world.2 I)))
    (R := endThawVatDebtCallStack preσ world.2 I outDai sel)
    (by
      dsimp only [endThawVatDebtCallStack, endThawVatDebtCallRest]
      simp only [List.length_cons, List.length_nil, List.length_append]
      omega)
    rd5028'
  exact ⟨aw5028, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_5028_stack] using rd5030⟩

theorem endThawWhenWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    endThawWhenWord evm = endThawWhenWorldWord world.2 I := by
  simpa [endThawWhenWord, endThawWhenWorldWord] using
    endPackRawSlotLoad_eq_of_callRel h (UInt256.ofNat 9)

theorem endThawWaitWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    endThawWaitWord evm = endThawWaitWorldWord world.2 I := by
  simpa [endThawWaitWord, endThawWaitWorldWord] using
    endPackRawSlotLoad_eq_of_callRel h (UInt256.ofNat 10)

theorem endThawDeadlineWord_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    endThawDeadlineWord evm = endThawDeadlineWorldWord world.2 I := by
  have hwhen := endThawWhenWord_eq_world_of_callRel h
  have hwait := endThawWaitWord_eq_world_of_callRel h
  simp [endThawDeadlineWord, endThawDeadlineWorldWord, hwhen, hwait]

theorem endThawVatCodeSize_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    extCodeSizeWord evm.accountMap
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
          solcAddrMask) =
      extCodeSizeWord world.2 (endPackVatTarget world.2 I) := by
  have hslotVat := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
  rw [h.env] at hslotVat
  rw [h.env]
  rw [hslotVat]
  have htarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 1)) solcAddrMask =
        endPackVatTarget world.2 I := by
    simp [endPackVatTarget, u256_land_comm]
  rw [htarget]
  exact (extCodeSizeWord_accountMapEquiv h.accounts (endPackVatTarget world.2 I)).symm

theorem endThawAfterVatDaiPrefixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preEvm : EVM.State} (preσ : AccountMap) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨4791⟩
      (fun cur frame e =>
        frame = endThawAfterVatDaiFrame cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        accountStaticStateEq preEvm.accountMap e.accountMap ∧
        cur.rdata.size < UInt256.size ∧
        32 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endThawVatDaiReturnMem preσ I cur.rdata),
            ⟨562⟩, sel] ∧
        cur.mem = endThawVatDaiReturnMem preσ I cur.rdata ∧
        cur.aw = endThawAfterVatDaiAw aw)
      [ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]
      (sequenceExit ⟨5030⟩
        (fun cur frame e =>
          frame = endThawAfterDeadlineFrame cur.rdata e ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq preEvm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          32 ≤ cur.rdata.size ∧
          cur.stack = endThawVatDebtCallStack preσ cur.world.2 I cur.rdata sel ∧
          cur.mem = endThawVatDebtCallMem preσ I cur.rdata)
        (runtimeExit (.abi []))) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hstatic, hout, h32, hstack, hmem, haw⟩
  cases hframe
  have rdAfter :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        (endThawAfterVatDaiCursor preσ I sel aw cur.rdata cur.world).pc
        (endThawAfterVatDaiCursor preσ I sel aw cur.rdata cur.world).stack
        (endThawAfterVatDaiCursor preσ I sel aw cur.rdata cur.world).mem
        (endThawAfterVatDaiCursor preσ I sel aw cur.rdata cur.world).aw
        (endThawAfterVatDaiCursor preσ I sel aw cur.rdata cur.world).rdata
        (endThawAfterVatDaiCursor preσ I sel aw cur.rdata cur.world).world k C := by
    simpa [endThawAfterVatDaiCursor, hpc, hstack, hmem, haw] using rd
  have hwhenEq := endThawWhenWord_eq_world_of_callRel hrel
  have hwaitEq := endThawWaitWord_eq_world_of_callRel hrel
  have hdeadlineEq := endThawDeadlineWord_eq_world_of_callRel hrel
  have hcodeEq := endThawVatCodeSize_eq_world_of_callRel hrel
  by_cases hvatDai : endThawUIntReturnWord cur.rdata = ⟨0⟩
  · obtain ⟨aw4866, k4866, C4866, rd4866⟩ :=
      endX_thaw_after_vat_dai_zero
        (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
        (σ := preσ) (sel := sel) (aw := aw) (out := cur.rdata)
        (world := cur.world) hout h32 hvatDai rdAfter
    by_cases hfit :
        (endThawWhenWorldWord cur.world.2 I).toNat +
          (endThawWaitWorldWord cur.world.2 I).toNat < UInt256.size
    · have hfitSource :
          (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat < UInt256.size := by
        simpa [hwhenEq, hwaitEq] using hfit
      by_cases htime :
          (endThawDeadlineWorldWord cur.world.2 I).toNat ≤
            (UInt256.ofNat I.header.timestamp).toNat
      · have htimeSource :
            (endThawDeadlineWord evm).toNat ≤
              (UInt256.ofNat evm.executionEnv.header.timestamp).toNat := by
          rw [hrel.env]
          simpa [hdeadlineEq] using htime
        by_cases hvatNoCode :
            extCodeSizeWord cur.world.2 (endPackVatTarget cur.world.2 I) = ⟨0⟩
        · have hsrcNoCode :
              extCodeSizeWord evm.accountMap
                  (UInt256.land
                    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
                    solcAddrMask) = ⟨0⟩ := by
            rw [hcodeEq, hvatNoCode]
          have hsource := endThawAfterVatDaiVatNoCode evm cur.rdata hvatDai
            hfitSource htimeSource hsrcNoCode
          have hrev := endX_thaw_vat_debt_no_code
            (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
            (preσ := preσ) (sel := sel) (aw := aw4866) (outDai := cur.rdata)
            (world := cur.world) hfit htime hvatNoCode rd4866
          exact ⟨.reverted, .reverted, hsource, hrev, by
            change True
            trivial⟩
        · have hsrcCode :
              extCodeSizeWord evm.accountMap
                  (UInt256.land
                    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 1))
                    solcAddrMask) ≠ ⟨0⟩ := by
            intro hzero
            exact hvatNoCode (hcodeEq.symm.trans hzero)
          have hsource := endThawAfterVatDaiPrefixOk evm cur.rdata hvatDai
            hfitSource htimeSource hsrcCode
          obtain ⟨awDebt, kDebt, CDebt, rdDebt⟩ :=
            endX_thaw_to_vat_debt_call
              (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
              (preσ := preσ) (sel := sel) (aw := aw4866) (outDai := cur.rdata)
              (world := cur.world) hout hfit htime hvatNoCode
              rd4866
          exact BlockProgress.ofRD hsource
            (cur := endThawVatDebtCallCursor cur.world preσ I sel awDebt cur.rdata cur.rdata)
            (k := kDebt) (C := CDebt)
            (by simpa [endThawVatDebtCallCursor] using rdDebt)
            (by exact ⟨rfl, rfl, hrel, hstatic, hout, h32, rfl, rfl⟩)
      · have htimeLt :
            (UInt256.ofNat I.header.timestamp).toNat <
              (endThawDeadlineWorldWord cur.world.2 I).toNat := by
          omega
        have htimeSource :
            (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
              (endThawDeadlineWord evm).toNat := by
          rw [hrel.env]
          simpa [hdeadlineEq] using htimeLt
        have hsource := endThawAfterVatDaiTimeFail evm cur.rdata hvatDai
          hfitSource htimeSource
        have hrev := endX_thaw_time_fail
          (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
          (preσ := preσ) (sel := sel) (aw := aw4866) (outDai := cur.rdata)
          (world := cur.world) hfit htimeLt rd4866
        exact ⟨.reverted, .reverted, hsource, hrev, by
          change True
          trivial⟩
    · have hoverWorld :
          UInt256.size ≤ (endThawWhenWorldWord cur.world.2 I).toNat +
            (endThawWaitWorldWord cur.world.2 I).toNat := by
        omega
      have hoverSource :
          UInt256.size ≤ (endThawWhenWord evm).toNat + (endThawWaitWord evm).toNat := by
        simpa [hwhenEq, hwaitEq] using hoverWorld
      have hsource := endThawAfterVatDaiAddFail evm cur.rdata hvatDai hoverSource
      have hrev := endX_thaw_add_fail
        (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
        (preσ := preσ) (sel := sel) (aw := aw4866) (outDai := cur.rdata)
        (world := cur.world) hoverWorld rd4866
      exact ⟨.reverted, .reverted, hsource, hrev, by
        change True
        trivial⟩
  · have hsource := endThawAfterVatDaiRequireFail evm cur.rdata hvatDai
    have hrev := endX_thaw_after_vat_dai_nonzero
      (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (σ := preσ) (sel := sel) (aw := aw) (out := cur.rdata)
      (world := cur.world) hout h32 hvatDai rdAfter
    exact ⟨.reverted, .reverted, hsource, hrev, by
      change True
      trivial⟩

abbrev endThawCureTellSelectorWord : UInt256 := UInt256.ofNat 1406599397

abbrev endThawCureTellSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)

abbrev endThawCureTellTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 7)) endThawVatDebtGeneratedMask

abbrev endThawCureTellBaseFree (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : UInt256 :=
  memLoad (UInt256.ofNat 64) (endThawVatDebtReturnMem preσ I outDai outDebt)

abbrev endThawVatDebtLoadedWord (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : UInt256 :=
  memLoad (endThawCureTellBaseFree preσ I outDai outDebt)
    (endThawVatDebtReturnMem preσ I outDai outDebt)

abbrev endThawCureTellCallMem (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_5070_taken_memory
    (mem := endThawVatDebtReturnMem preσ I outDai outDebt)

abbrev endThawCureTellMemFull (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : ByteArray :=
  endThawCureTellSelectorEncodedWord.toByteArray.write 0
    (endThawVatDebtReturnMem preσ I outDai outDebt) 128 32

abbrev endThawCureTellCallFree (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : UInt256 :=
  memLoad (UInt256.ofNat 64) (endThawCureTellCallMem preσ I outDai outDebt)

abbrev endThawCureTellCallSize (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : UInt256 :=
  UInt256.sub (endThawCureTellBaseFree preσ I outDai outDebt)
    (endThawCureTellCallFree preσ I outDai outDebt) + UInt256.ofNat 4

abbrev endThawCureTellCallEnd (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) : UInt256 :=
  endThawCureTellBaseFree preσ I outDai outDebt + UInt256.ofNat 4

abbrev endThawCureTellCallRest (preσ σ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (sel : UInt256) : List UInt256 :=
  [endThawCureTellCallEnd preσ I outDai outDebt, endThawCureTellSelectorWord,
    endThawCureTellTarget σ I, endThawVatDebtLoadedWord preσ I outDai outDebt,
    ⟨5190⟩, ⟨562⟩, sel]

abbrev endThawCureTellCallStack (preσ σ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (sel : UInt256) : List UInt256 :=
  [endThawCureTellTarget σ I, endThawCureTellCallFree preσ I outDai outDebt,
    endThawCureTellCallSize preσ I outDai outDebt,
    endThawCureTellCallFree preσ I outDai outDebt, ⟨32⟩] ++
    endThawCureTellCallRest preσ σ I outDai outDebt sel

abbrev endThawCureTellCallCursor
    (world : Batteries.RBSet AccountAddress compare × AccountMap)
    (preσ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256)
    (outDai outDebt rdata : ByteArray) : Cursor :=
  { pc := ⟨5143⟩,
    stack := endThawCureTellCallStack preσ world.2 I outDai outDebt sel,
    mem := endThawCureTellCallMem preσ I outDai outDebt,
    aw := aw, rdata := rdata, world := world }

abbrev endThawCureTellCallAw (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat
      (endThawCureTellCallFree preσ I outDai outDebt).toNat
      (endThawCureTellCallSize preσ I outDai outDebt).toNat)
      (endThawCureTellCallFree preσ I outDai outDebt).toNat (⟨32⟩ : UInt256).toNat)

abbrev endThawAfterCureTellAw (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (aw : UInt256) : UInt256 :=
  M (endThawCureTellCallAw preσ I outDai outDebt aw) (UInt256.ofNat 64)
    (⟨32⟩ : UInt256)

abbrev endThawCureTellReturnMem (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt outTell : ByteArray) : ByteArray :=
  outTell.write 0 (endThawCureTellCallMem preσ I outDai outDebt)
    (endThawCureTellCallFree preσ I outDai outDebt).toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat outTell.size)).toNat

abbrev endThawAfterCureTellFrame (outDai outDebt outTell : ByteArray)
    (evm : EVM.State) : Frame :=
  { contract := contract,
    locals := (endThawAfterVatDebtFrame outDai outDebt evm).locals.insert "cureTell"
      (collapseReturns [endUIntValue (endThawUIntReturnWord outTell)]) }

theorem endExternalEncode_tell :
    config.externalABI.encode? "tell" [] = some tellSelector := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "tell" = "cage")]
  rw [if_neg (by decide : ¬ "tell" = "vatIlks")]
  rw [if_neg (by decide : ¬ "tell" = "catIlks")]
  rw [if_neg (by decide : ¬ "tell" = "dogIlks")]
  rw [if_neg (by decide : ¬ "tell" = "spotIlks")]
  rw [if_neg (by decide : ¬ "tell" = "urns")]
  rw [if_neg (by decide : ¬ "tell" = "dai")]
  rw [if_neg (by decide : ¬ "tell" = "debt")]
  rw [if_neg (by decide : ¬ "tell" = "move")]
  rw [if_neg (by decide : ¬ "tell" = "hope")]
  rw [if_neg (by decide : ¬ "tell" = "flux")]
  rw [if_neg (by decide : ¬ "tell" = "grab")]
  rw [if_neg (by decide : ¬ "tell" = "suck")]
  rw [if_neg (by decide : ¬ "tell" = "par")]
  rw [if_pos (by decide : "tell" = "tell")]

theorem endThawAfterVatDebtFrame_get_cure_none (outDai outDebt : ByteArray)
    (evm : EVM.State) :
    (endThawAfterVatDebtFrame outDai outDebt evm).locals.get? "cure" = none := by
  unfold endThawAfterVatDebtFrame
  rw [store_get_ne (endThawAfterDeadlineFrame outDai evm).locals
    (k := "vatDebt") (a := "cure")
    (collapseReturns [endUIntValue (endThawUIntReturnWord outDebt)]) (by decide)]
  unfold endThawAfterDeadlineFrame
  rw [store_get_ne (endThawAfterVatDaiFrame outDai).locals
    (k := "deadline") (a := "cure")
    (endUIntValue (endThawDeadlineWord evm)) (by decide)]
  unfold endThawAfterVatDaiFrame
  rw [store_get_ne endThawStore (k := "vatDai") (a := "cure")
    (collapseReturns [endUIntValue (endThawUIntReturnWord outDai)]) (by decide)]
  exact endThawStore_get_none "cure"

theorem endEvalCureAddress_thaw_afterVatDebt (evm : EVM.State)
    (outDai outDebt : ByteArray) (preDebtEvm : EVM.State) :
    evalExpr? config (endThawAfterVatDebtFrame outDai outDebt preDebtEvm) evm
        (.storage cureRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
          solcAddrMask).toNat)) := by
  simpa [endThawAfterVatDebtFrame] using
    (endEvalAddressSlot_cage
      (locals := (endThawAfterVatDebtFrame outDai outDebt preDebtEvm).locals)
      (evm := evm) (slot := cureRef) (er := { base := "cure", steps := [] })
      (wordSlot := UInt256.ofNat 7)
      (endThawAfterVatDebtFrame_get_cure_none outDai outDebt preDebtEvm)
      (by simp [evalStorageRef, evalStorageRefSteps, cureRef, EvalResult.bind, pure, bind])
      (by decide)
      (by
        rw [show (UInt256.ofNat 7) = (⟨7⟩ : UInt256) from by native_decide]
        exact endConfig_storage_cure))

theorem endEvalCureCodeGuard_thaw_afterVatDebt_true (evm : EVM.State)
    (outDai outDebt : ByteArray) (preDebtEvm : EVM.State)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config (endThawAfterVatDebtFrame outDai outDebt preDebtEvm) evm
      (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) =
      .ok (.bool true) := by
  exact endEvalCodeSizeGuard_cage_true
    (locals := (endThawAfterVatDebtFrame outDai outDebt preDebtEvm).locals)
    (receiver := .storage cureRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
      solcAddrMask)
    (endEvalCureAddress_thaw_afterVatDebt evm outDai outDebt preDebtEvm) hcode

theorem endEvalCureCodeGuard_thaw_afterVatDebt_false (evm : EVM.State)
    (outDai outDebt : ByteArray) (preDebtEvm : EVM.State)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config (endThawAfterVatDebtFrame outDai outDebt preDebtEvm) evm
      (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) =
      .ok (.bool false) := by
  exact endEvalCodeSizeGuard_cage_false
    (locals := (endThawAfterVatDebtFrame outDai outDebt preDebtEvm).locals)
    (receiver := .storage cureRef)
    (target := UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
      solcAddrMask)
    (endEvalCureAddress_thaw_afterVatDebt evm outDai outDebt preDebtEvm) hnocode

theorem endThawCureTellCallMem_eq_full (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    endThawCureTellCallMem preσ I outDai outDebt =
      endThawCureTellMemFull preσ I outDai outDebt := by
  have hfree := endThawVatDebtReturnMem_mload64 preσ I outDai outDebt houtDai houtDebt
  unfold endThawCureTellCallMem endThawCureTellMemFull
    endThawCureTellSelectorEncodedWord
  dsimp [endRuntimeBlocks.endRuntime_block_5070_taken_memory]
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]

theorem endThawCureTellCallMem_size (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    (endThawCureTellCallMem preσ I outDai outDebt).size = 164 := by
  rw [endThawCureTellCallMem_eq_full preσ I outDai outDebt houtDai houtDebt]
  unfold endThawCureTellMemFull
  exact toByteArray_write32_size_of_le
    (endThawVatDebtReturnMem preσ I outDai outDebt)
    endThawCureTellSelectorEncodedWord 128 164 164
    (endThawVatDebtReturnMem_size preσ I outDai outDebt houtDai houtDebt)
    (by rw [endThawVatDebtReturnMem_size preσ I outDai outDebt houtDai houtDebt]; omega)
    (by omega)

theorem endThawCureTellCallMem_read64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    (endThawCureTellCallMem preσ I outDai outDebt).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endThawCureTellCallMem_eq_full preσ I outDai outDebt houtDai houtDebt]
  unfold endThawCureTellMemFull
  rw [toByteArray_write_read_below_of_gap_unbounded
    endThawCureTellSelectorEncodedWord
    (endThawVatDebtReturnMem preσ I outDai outDebt) 128 64
    (by rw [endThawVatDebtReturnMem_size preσ I outDai outDebt houtDai houtDebt]; omega)
    (by omega)]
  exact endThawVatDebtReturnMem_read64 preσ I outDai outDebt houtDai houtDebt

theorem endThawCureTellCallMem_mload64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    memLoad (UInt256.ofNat 64) (endThawCureTellCallMem preσ I outDai outDebt) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endThawCureTellCallMem preσ I outDai outDebt)
    (by rw [endThawCureTellCallMem_size preσ I outDai outDebt houtDai houtDebt]; omega)
    (endThawCureTellCallMem_read64 preσ I outDai outDebt houtDai houtDebt)

theorem endThawCureTellSelectorEncodedWord_prefix :
    (endThawCureTellSelectorEncodedWord.toByteArray).extract 0 4 = tellSelector := by
  native_decide

theorem endThawCureTellCallMem_readSelector (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    (endThawCureTellCallMem preσ I outDai outDebt).readWithPadding 128 4 =
      tellSelector := by
  rw [endThawCureTellCallMem_eq_full preσ I outDai outDebt houtDai houtDebt]
  unfold endThawCureTellMemFull
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endThawCureTellSelectorEncodedWord
    (endThawVatDebtReturnMem preσ I outDai outDebt) 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endThawCureTellSelectorEncodedWord_prefix]

theorem endThawCureTellCallMem_readCallData_raw (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) :
    (endThawCureTellCallMem preσ I outDai outDebt).readWithPadding
      (endThawCureTellCallFree preσ I outDai outDebt).toNat
      (endThawCureTellCallSize preσ I outDai outDebt).toNat = tellSelector := by
  have hbase := endThawVatDebtReturnMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have hfree := endThawCureTellCallMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have hsize : endThawCureTellCallSize preσ I outDai outDebt = ⟨4⟩ := by
    unfold endThawCureTellCallSize endThawCureTellBaseFree endThawCureTellCallFree
    rw [hbase, hfree]
    native_decide
  unfold endThawCureTellCallFree
  rw [hfree, hsize]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
    show (⟨4⟩ : UInt256).toNat = 4 from by native_decide]
  exact endThawCureTellCallMem_readSelector preσ I outDai outDebt houtDai houtDebt

theorem endThawVatDebtLoadedWord_eq (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (h32 : 32 ≤ outDebt.size) :
    endThawVatDebtLoadedWord preσ I outDai outDebt =
      endThawUIntReturnWord outDebt := by
  have hretFree := endThawVatDebtReturnMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have hcallFree := endThawVatDebtCallMem_mload64 preσ I outDai houtDai
  have hloaded := endThawVatDebtReturnMem_mloadCallFree preσ I outDai outDebt
    houtDai houtDebt h32
  unfold endThawVatDebtLoadedWord endThawCureTellBaseFree
  rw [hretFree]
  unfold endThawVatDebtCallFree at hloaded
  rw [hcallFree] at hloaded
  exact hloaded

abbrev endThawAfterCureTellCursor (preσ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (outDai outDebt outTell : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨5183⟩,
    stack :=
      [UInt256.ofNat outTell.size,
        memLoad (UInt256.ofNat 64)
          (endThawCureTellReturnMem preσ I outDai outDebt outTell),
        endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel],
    mem := endThawCureTellReturnMem preσ I outDai outDebt outTell,
    aw := endThawAfterCureTellAw preσ I outDai outDebt aw,
    rdata := outTell, world := world }

theorem endX_thaw_cure_tell_no_code {I g s0 preσ sel aw outDai outDebt world k C}
    (hcode : extCodeSizeWord world.2 (endThawCureTellTarget world.2 I) = ⟨0⟩)
    (rd : RD endBytecode I g s0
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).pc
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).stack
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).mem
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).aw
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).rdata
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).world k C) :
    RDrev endBytecode g s0 := by
  have rd5070 :
      RD endBytecode I g s0 ⟨5070⟩
        [UInt256.ofNat outDebt.size,
          memLoad (UInt256.ofNat 64) (endThawVatDebtReturnMem preσ I outDai outDebt),
          ⟨5190⟩, ⟨562⟩, sel]
        (endThawVatDebtReturnMem preσ I outDai outDebt)
        (endThawAfterVatDebtAw preσ I outDai aw) outDebt world k C := by
    simpa [endThawAfterVatDebtCursor] using rd
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endThawCureTellTarget world.2 I))) =
        UInt256.ofNat 0 := by
    rw [hcode]
    decide
  obtain ⟨k5137, C5137, rd5137⟩ :=
    endRuntimeBlocks.endRuntime_block_5070_fallthrough
      (ee := I) (mem := endThawVatDebtReturnMem preσ I outDai outDebt)
      (σ := world.2) (x0 := UInt256.ofNat outDebt.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endThawVatDebtReturnMem preσ I outDai outDebt))
      (R := [⟨5190⟩, ⟨562⟩, sel])
      (by simp) hcond rd5070
  exact endRuntimeBlocks.endRuntime_block_5137
    (R := endRuntimeBlocks.endRuntime_block_5070_fallthrough_stack
      (ee := I) (mem := endThawVatDebtReturnMem preσ I outDai outDebt)
      (σ := world.2)
      (x1 := memLoad (UInt256.ofNat 64)
        (endThawVatDebtReturnMem preσ I outDai outDebt))
      (R := [⟨5190⟩, ⟨562⟩, sel]))
    (by
      dsimp only [endRuntimeBlocks.endRuntime_block_5070_fallthrough_stack]
      simp only [List.length_cons, List.length_nil]
      omega)
    rd5137

theorem endX_thaw_to_cure_tell_call {I g s0 preσ sel aw outDai outDebt world k C}
    (hcode : extCodeSizeWord world.2 (endThawCureTellTarget world.2 I) ≠ ⟨0⟩)
    (rd : RD endBytecode I g s0
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).pc
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).stack
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).mem
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).aw
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).rdata
      (endThawAfterVatDebtCursor preσ I sel aw outDai outDebt world).world k C) :
    ∃ aw' k' C', RD endBytecode I g s0 ⟨5143⟩
      (endThawCureTellCallStack preσ world.2 I outDai outDebt sel)
      (endThawCureTellCallMem preσ I outDai outDebt) aw' outDebt world k' C' := by
  have rd5070 :
      RD endBytecode I g s0 ⟨5070⟩
        [UInt256.ofNat outDebt.size,
          memLoad (UInt256.ofNat 64) (endThawVatDebtReturnMem preσ I outDai outDebt),
          ⟨5190⟩, ⟨562⟩, sel]
        (endThawVatDebtReturnMem preσ I outDai outDebt)
        (endThawAfterVatDebtAw preσ I outDai aw) outDebt world k C := by
    simpa [endThawAfterVatDebtCursor] using rd
  have hcond :
      UInt256.isZero
          (UInt256.isZero (extCodeSizeWord world.2 (endThawCureTellTarget world.2 I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hcode]
    native_decide
  obtain ⟨aw5141, k5141, C5141, rd5141⟩ :=
    endRuntimeBlocks.endRuntime_block_5070_taken_packed
      (ee := I) (mem := endThawVatDebtReturnMem preσ I outDai outDebt)
      (σ := world.2) (x0 := UInt256.ofNat outDebt.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endThawVatDebtReturnMem preσ I outDai outDebt))
      (R := [⟨5190⟩, ⟨562⟩, sel])
      (by simp) hcond (by jump_dest) rd5070
  have hstackTaken :
      endRuntimeBlocks.endRuntime_block_5070_taken_stack
          (ee := I) (mem := endThawVatDebtReturnMem preσ I outDai outDebt)
          (σ := world.2)
          (x1 := memLoad (UInt256.ofNat 64)
            (endThawVatDebtReturnMem preσ I outDai outDebt))
          (R := [⟨5190⟩, ⟨562⟩, sel]) =
        UInt256.isZero (extCodeSizeWord world.2 (endThawCureTellTarget world.2 I)) ::
          endThawCureTellCallStack preσ world.2 I outDai outDebt sel := by
    rfl
  have rd5141' :
      RD endBytecode I g s0 ⟨5141⟩
        (UInt256.isZero (extCodeSizeWord world.2 (endThawCureTellTarget world.2 I)) ::
          endThawCureTellCallStack preσ world.2 I outDai outDebt sel)
        (endThawCureTellCallMem preσ I outDai outDebt) aw5141 outDebt
        world k5141 C5141 := by
    rw [hstackTaken] at rd5141
    simpa [endThawCureTellCallMem] using rd5141
  have rd5143 := endRuntimeBlocks.endRuntime_block_5141
    (ee := I) (cA := world.1) (σ := world.2)
    (x0 := UInt256.isZero (extCodeSizeWord world.2 (endThawCureTellTarget world.2 I)))
    (R := endThawCureTellCallStack preσ world.2 I outDai outDebt sel)
    (by
      dsimp only [endThawCureTellCallStack, endThawCureTellCallRest]
      simp only [List.length_cons, List.length_nil, List.length_append]
      omega)
    rd5141'
  exact ⟨aw5141, _, _, by
    simpa [endRuntimeBlocks.endRuntime_block_5141_stack] using rd5143⟩

set_option maxHeartbeats 12000000 in
theorem endThawCureTellExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm preDebtEvm preσ outDai outDebt world}
    (houtDai : outDai.size < UInt256.size) (houtDebt : outDebt.size < UInt256.size) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endThawCureTellCallCursor world preσ I sel aw outDai outDebt rdata)
      k C (endThawAfterVatDebtFrame outDai outDebt preDebtEvm) evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ]
      (sequenceExit ⟨5183⟩
        (fun cur frame e =>
          frame = endThawAfterCureTellFrame outDai outDebt cur.rdata preDebtEvm ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          accountStaticStateEq evm.accountMap e.accountMap ∧
          cur.rdata.size < UInt256.size ∧
          32 ≤ cur.rdata.size ∧
          cur.stack =
            [UInt256.ofNat cur.rdata.size,
              memLoad (UInt256.ofNat 64)
                (endThawCureTellReturnMem preσ I outDai outDebt cur.rdata),
              endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel] ∧
          cur.mem = endThawCureTellReturnMem preσ I outDai outDebt cur.rdata ∧
          cur.aw = endThawAfterCureTellAw preσ I outDai outDebt aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨5143⟩ = some (.GAS, .none); decide)
    (by simp [endThawCureTellCallStack, endThawCureTellCallRest]) ?_
  intro callGas
  refine BlockRefinesFrom.staticExternalCall
    (tgt := AccountAddress.ofNat (endThawCureTellTarget world.2 I).toNat)
    (argVals := [])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨5144⟩ = some (.STATICCALL, .none)
      decide) (hov := by simp [endThawCureTellCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 7)
    rw [h.env] at hload
    rw [endEvalCureAddress_thaw_afterVatDebt]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 7))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address
          (AccountAddress.ofNat (endThawCureTellTarget world.2 I).toNat))
    rw [hload]
    unfold endThawCureTellTarget
    rw [show endThawVatDebtGeneratedMask = solcAddrMask from by native_decide]
  · intro _
    simp [evalExpr?, pure]
  · intro _
    simp [evalExprs?, pure]
  · intro _
    apply Fin.ext
    show (endThawCureTellTarget world.2 I).toNat % EVM.addressModulus %
        AccountAddress.size =
      (endThawCureTellTarget world.2 I).val % AccountAddress.size %
        AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_tell]
    change some tellSelector =
      some ((endThawCureTellCallMem preσ I outDai outDebt).readWithPadding
        (endThawCureTellCallFree preσ I outDai outDebt).toNat
        (endThawCureTellCallSize preσ I outDai outDebt).toNat)
    rw [endThawCureTellCallMem_readCallData_raw preσ I outDai outDebt
      houtDai houtDebt]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _ hout
    by_cases h32 : 32 ≤ out.size
    · have hdecode : config.externalABI.decode? "tell" out =
          some [endUIntValue (endThawUIntReturnWord out)] := by
        change externalABI.decode? "tell" out =
          some [endUIntValue (endThawUIntReturnWord out)]
        exact endExternalDecode_uint256_ok "tell" (by exact Or.inr (Or.inr rfl)) h32
      rw [hdecode]
      intro rd hrel
      have rd5145 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5145⟩
            ((⟨1⟩ : UInt256) ::
              endThawCureTellCallRest preσ world.2 I outDai outDebt sel)
            (endThawCureTellReturnMem preσ I outDai outDebt out)
            (endThawCureTellCallAw preσ I outDai outDebt aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endThawCureTellCallStack,
          endThawCureTellCallRest, endThawCureTellCallAw,
          endThawCureTellReturnMem] using rd
      have rd5161 := endRuntimeBlocks.endRuntime_block_5145_taken
        (x0 := (⟨1⟩ : UInt256))
        (R := endThawCureTellCallRest preσ world.2 I outDai outDebt sel)
        (by simp [endThawCureTellCallRest]) (by native_decide) (by jump_dest) rd5145
      have rd5161' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5161⟩
            [⟨0⟩, endThawCureTellCallEnd preσ I outDai outDebt,
              endThawCureTellSelectorWord, endThawCureTellTarget world.2 I,
              endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel]
            (endThawCureTellReturnMem preσ I outDai outDebt out)
            (endThawCureTellCallAw preσ I outDai outDebt aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_5145_taken_stack,
          endThawCureTellCallRest] using rd5161
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨0⟩ := by
        apply Reasoning.Theory.ult_zero
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact h32
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) ≠
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd5183 := endRuntimeBlocks.endRuntime_block_5161_taken
        (x0 := (⟨0⟩ : UInt256))
        (x1 := endThawCureTellCallEnd preσ I outDai outDebt)
        (x2 := endThawCureTellSelectorWord) (x3 := endThawCureTellTarget world.2 I)
        (R := [endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel])
        (by simp) hretcond (by jump_dest) rd5161'
      refine ⟨.ok (endThawAfterCureTellFrame outDai outDebt out preDebtEvm) evm',
        Endpoint.reached
          (endThawAfterCureTellCursor preσ I sel aw outDai outDebt out world'),
        ExecBlock.nil, ?_, ?_⟩
      · exact ⟨_, _, by
          simpa [endThawAfterCureTellCursor, endThawAfterCureTellAw,
            endRuntimeBlocks.endRuntime_block_5161_taken_stack] using rd5183⟩
      · exact ⟨rfl, rfl, hrel.1, hrel.2, hout, h32, rfl, rfl, rfl⟩
    · have hshort : out.size < 32 := by omega
      have hdecode : config.externalABI.decode? "tell" out = none := by
        change externalABI.decode? "tell" out = none
        exact endExternalDecode_uint256_none_short "tell" (by exact Or.inr (Or.inr rfl))
          hshort
      rw [hdecode]
      intro rd
      have rd5145 :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5145⟩
            ((⟨1⟩ : UInt256) ::
              endThawCureTellCallRest preσ world.2 I outDai outDebt sel)
            (endThawCureTellReturnMem preσ I outDai outDebt out)
            (endThawCureTellCallAw preσ I outDai outDebt aw) out world' k' C' := by
        simpa [gasCursor, callCursor, endThawCureTellCallStack,
          endThawCureTellCallRest, endThawCureTellCallAw,
          endThawCureTellReturnMem] using rd
      have rd5161 := endRuntimeBlocks.endRuntime_block_5145_taken
        (x0 := (⟨1⟩ : UInt256))
        (R := endThawCureTellCallRest preσ world.2 I outDai outDebt sel)
        (by simp [endThawCureTellCallRest]) (by native_decide) (by jump_dest) rd5145
      have rd5161' :
          RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5161⟩
            [⟨0⟩, endThawCureTellCallEnd preσ I outDai outDebt,
              endThawCureTellSelectorWord, endThawCureTellTarget world.2 I,
              endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel]
            (endThawCureTellReturnMem preσ I outDai outDebt out)
            (endThawCureTellCallAw preσ I outDai outDebt aw) out world'
            (k' + 5) (C' + 22) := by
        simpa [endRuntimeBlocks.endRuntime_block_5145_taken_stack,
          endThawCureTellCallRest] using rd5161
      have hlt :
          UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ := by
        apply Reasoning.Theory.ult_one
        rw [show (UInt256.ofNat 32).toNat = 32 from by native_decide,
          ulit_toNat' out.size hout]
        exact hshort
      have hretcond :
          UInt256.isZero
              (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) =
            UInt256.ofNat 0 := by
        rw [hlt]
        decide
      have rd5179 := endRuntimeBlocks.endRuntime_block_5161_fallthrough
        (x0 := (⟨0⟩ : UInt256))
        (x1 := endThawCureTellCallEnd preσ I outDai outDebt)
        (x2 := endThawCureTellSelectorWord) (x3 := endThawCureTellTarget world.2 I)
        (R := [endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel])
        (by simp) hretcond rd5161'
      exact endRuntimeBlocks.endRuntime_block_5179
        (R := endRuntimeBlocks.endRuntime_block_5161_fallthrough_stack
          (mem := endThawCureTellReturnMem preσ I outDai outDebt out)
          (rdata := out)
          (R := [endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel]))
        (by simp [endRuntimeBlocks.endRuntime_block_5161_fallthrough_stack])
        rd5179
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd5145 :
        RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5145⟩
          ((⟨0⟩ : UInt256) ::
            endThawCureTellCallRest preσ world.2 I outDai outDebt sel)
          (endThawCureTellReturnMem preσ I outDai outDebt out)
          (endThawCureTellCallAw preσ I outDai outDebt aw) out world' k' C' := by
      simpa [gasCursor, callCursor, endThawCureTellCallStack,
        endThawCureTellCallRest, endThawCureTellCallAw,
        endThawCureTellReturnMem] using rd
    have rd5152 := endRuntimeBlocks.endRuntime_block_5145_fallthrough
      (x0 := (⟨0⟩ : UInt256))
      (R := endThawCureTellCallRest preσ world.2 I outDai outDebt sel)
      (by simp [endThawCureTellCallRest]) (by native_decide) rd5145
    exact endRuntimeBlocks.endRuntime_block_5152
      (R := endRuntimeBlocks.endRuntime_block_5145_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256))
        (R := endThawCureTellCallRest preσ world.2 I outDai outDebt sel))
      (by simp [endRuntimeBlocks.endRuntime_block_5145_fallthrough_stack,
        endThawCureTellCallRest])
      rd5152

theorem endThawCureTellReturnMem_size (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt outTell : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (houtTell : outTell.size < UInt256.size) :
    (endThawCureTellReturnMem preσ I outDai outDebt outTell).size = 164 := by
  have hfree := endThawCureTellCallMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have hfacts := callOutputFacts (endThawCureTellCallMem preσ I outDai outDebt)
    outTell (endThawCureTellCallFree preσ I outDai outDebt) (⟨32⟩ : UInt256)
    houtTell
    (by
      unfold endThawCureTellCallFree
      rw [hfree, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      rw [endThawCureTellCallMem_size preσ I outDai outDebt houtDai houtDebt]
      omega)
  have hsize :
      (endThawCureTellReturnMem preσ I outDai outDebt outTell).size =
        (endThawCureTellCallMem preσ I outDai outDebt).size := by
    simpa [endThawCureTellReturnMem] using hfacts.size
  rw [hsize, endThawCureTellCallMem_size preσ I outDai outDebt houtDai houtDebt]

theorem endThawCureTellReturnMem_read64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt outTell : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (houtTell : outTell.size < UInt256.size) :
    (endThawCureTellReturnMem preσ I outDai outDebt outTell).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hfree := endThawCureTellCallMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have hfacts := callOutputFacts (endThawCureTellCallMem preσ I outDai outDebt)
    outTell (endThawCureTellCallFree preσ I outDai outDebt) (⟨32⟩ : UInt256)
    houtTell
    (by
      unfold endThawCureTellCallFree
      rw [hfree, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      rw [endThawCureTellCallMem_size preσ I outDai outDebt houtDai houtDebt]
      omega)
  have hbelow : 64 + 32 ≤ (endThawCureTellCallFree preσ I outDai outDebt).toNat := by
    unfold endThawCureTellCallFree
    rw [hfree]
    native_decide
  have hread :
      (endThawCureTellReturnMem preσ I outDai outDebt outTell).readWithPadding 64 32 =
        (endThawCureTellCallMem preσ I outDai outDebt).readWithPadding 64 32 := by
    simpa [endThawCureTellReturnMem] using hfacts.readBelow 64 hbelow
  rw [hread]
  exact endThawCureTellCallMem_read64 preσ I outDai outDebt houtDai houtDebt

theorem endThawCureTellReturnMem_mload64 (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt outTell : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (houtTell : outTell.size < UInt256.size) :
    memLoad (UInt256.ofNat 64)
        (endThawCureTellReturnMem preσ I outDai outDebt outTell) = ⟨128⟩ := by
  exact mloadFreePtrValue
    (mem := endThawCureTellReturnMem preσ I outDai outDebt outTell)
    (by
      rw [endThawCureTellReturnMem_size preσ I outDai outDebt outTell houtDai
        houtDebt houtTell]
      omega)
    (endThawCureTellReturnMem_read64 preσ I outDai outDebt outTell houtDai
      houtDebt houtTell)

theorem endThawCureTellReturnMem_mloadCallFree (preσ : AccountMap) (I : ExecutionEnv)
    (outDai outDebt outTell : ByteArray) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (houtTell : outTell.size < UInt256.size)
    (h32 : 32 ≤ outTell.size) :
    memLoad (endThawCureTellCallFree preσ I outDai outDebt)
        (endThawCureTellReturnMem preσ I outDai outDebt outTell) =
      endThawUIntReturnWord outTell := by
  have hfree := endThawCureTellCallMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have hfacts := callOutputFacts (endThawCureTellCallMem preσ I outDai outDebt)
    outTell (endThawCureTellCallFree preσ I outDai outDebt) (⟨32⟩ : UInt256)
    houtTell
    (by
      unfold endThawCureTellCallFree
      rw [hfree, show (⟨128⟩ : UInt256).toNat = 128 from by native_decide,
        show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
      rw [endThawCureTellCallMem_size preσ I outDai outDebt houtDai houtDebt]
      omega)
  have hsize :
      (endThawCureTellReturnMem preσ I outDai outDebt outTell).size =
        (endThawCureTellCallMem preσ I outDai outDebt).size := by
    simpa [endThawCureTellReturnMem] using hfacts.size
  have hread :
      (endThawCureTellReturnMem preσ I outDai outDebt outTell).readWithPadding
          (endThawCureTellCallFree preσ I outDai outDebt).toNat 32 =
        outTell.extract 0 32 := by
    exact hfacts.readWord (by rfl) h32
  unfold memLoad
  unfold endThawCureTellCallFree
  rw [hfree]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [if_neg (by
    rw [hsize, endThawCureTellCallMem_size preσ I outDai outDebt houtDai houtDebt]
    omega)]
  rw [show (endThawCureTellCallFree preσ I outDai outDebt).toNat = 128 by
    unfold endThawCureTellCallFree
    rw [hfree]
    native_decide] at hread
  rw [hread]

abbrev endThawDebtNewWord (outDebt outTell : ByteArray) : UInt256 :=
  UInt256.sub (endThawUIntReturnWord outDebt) (endThawUIntReturnWord outTell)

abbrev endThawAfterDebtNewFrame (outDai outDebt outTell : ByteArray)
    (preDebtEvm : EVM.State) : Frame :=
  { contract := contract,
    locals := (endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm).locals.insert
      "debtNew" (endUIntValue (endThawDebtNewWord outDebt outTell)) }

abbrev endThawFinalState (evm : EVM.State) (outDebt outTell : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨11⟩
    (endThawDebtNewWord outDebt outTell)

abbrev endThawDebtStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv)
    (outDebt outTell : ByteArray) : Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 ⟨11⟩ (endThawDebtNewWord outDebt outTell))

theorem endThawAfterVatDebtFrame_get_vatDebt (outDai outDebt : ByteArray)
    (evm : EVM.State) :
    (endThawAfterVatDebtFrame outDai outDebt evm).locals.get? "vatDebt" =
      some (endUIntValue (endThawUIntReturnWord outDebt)) := by
  unfold endThawAfterVatDebtFrame
  exact store_get_self (endThawAfterDeadlineFrame outDai evm).locals "vatDebt"
    (endUIntValue (endThawUIntReturnWord outDebt))

theorem endThawAfterCureTellFrame_get_vatDebt (outDai outDebt outTell : ByteArray)
    (evm : EVM.State) :
    (endThawAfterCureTellFrame outDai outDebt outTell evm).locals.get? "vatDebt" =
      some (endUIntValue (endThawUIntReturnWord outDebt)) := by
  unfold endThawAfterCureTellFrame
  rw [store_get_ne (endThawAfterVatDebtFrame outDai outDebt evm).locals
    (k := "cureTell") (a := "vatDebt")
    (collapseReturns [endUIntValue (endThawUIntReturnWord outTell)]) (by decide)]
  exact endThawAfterVatDebtFrame_get_vatDebt outDai outDebt evm

theorem endThawAfterCureTellFrame_get_cureTell (outDai outDebt outTell : ByteArray)
    (evm : EVM.State) :
    (endThawAfterCureTellFrame outDai outDebt outTell evm).locals.get? "cureTell" =
      some (endUIntValue (endThawUIntReturnWord outTell)) := by
  unfold endThawAfterCureTellFrame
  exact store_get_self (endThawAfterVatDebtFrame outDai outDebt evm).locals "cureTell"
    (endUIntValue (endThawUIntReturnWord outTell))

theorem endThawAfterDebtNewFrame_get_debtNew (outDai outDebt outTell : ByteArray)
    (evm : EVM.State) :
    (endThawAfterDebtNewFrame outDai outDebt outTell evm).locals.get? "debtNew" =
      some (endUIntValue (endThawDebtNewWord outDebt outTell)) := by
  unfold endThawAfterDebtNewFrame
  exact store_get_self (endThawAfterCureTellFrame outDai outDebt outTell evm).locals
    "debtNew" (endUIntValue (endThawDebtNewWord outDebt outTell))

theorem endThawAfterDebtNewFrame_get_debt_none (outDai outDebt outTell : ByteArray)
    (evm : EVM.State) :
    (endThawAfterDebtNewFrame outDai outDebt outTell evm).locals.get? "debt" = none := by
  unfold endThawAfterDebtNewFrame
  rw [store_get_ne (endThawAfterCureTellFrame outDai outDebt outTell evm).locals
    (k := "debtNew") (a := "debt") (endUIntValue (endThawDebtNewWord outDebt outTell))
    (by decide)]
  unfold endThawAfterCureTellFrame
  rw [store_get_ne (endThawAfterVatDebtFrame outDai outDebt evm).locals
    (k := "cureTell") (a := "debt")
    (collapseReturns [endUIntValue (endThawUIntReturnWord outTell)]) (by decide)]
  unfold endThawAfterVatDebtFrame
  rw [store_get_ne (endThawAfterDeadlineFrame outDai evm).locals
    (k := "vatDebt") (a := "debt")
    (collapseReturns [endUIntValue (endThawUIntReturnWord outDebt)]) (by decide)]
  unfold endThawAfterDeadlineFrame
  rw [store_get_ne (endThawAfterVatDaiFrame outDai).locals
    (k := "deadline") (a := "debt") (endUIntValue (endThawDeadlineWord evm))
    (by decide)]
  unfold endThawAfterVatDaiFrame
  rw [store_get_ne endThawStore (k := "vatDai") (a := "debt")
    (collapseReturns [endUIntValue (endThawUIntReturnWord outDai)]) (by decide)]
  exact endThawStore_get_none "debt"

theorem endEvalThawSubArgs (evm : EVM.State) (outDai outDebt outTell : ByteArray)
    (preDebtEvm : EVM.State) :
    evalExprs? config (endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm)
      evm [.var "vatDebt", .var "cureTell"] =
      .ok [endUIntValue (endThawUIntReturnWord outDebt),
        endUIntValue (endThawUIntReturnWord outTell)] := by
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endThawAfterCureTellFrame_get_vatDebt outDai outDebt outTell preDebtEvm]
  simp only [EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endThawAfterCureTellFrame_get_cureTell outDai outDebt outTell preDebtEvm]
  simp [evalExprs?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem endBindParams_sub_thaw (outDebt outTell : ByteArray) :
    bindParams? subFunction.params
      [endUIntValue (endThawUIntReturnWord outDebt),
        endUIntValue (endThawUIntReturnWord outTell)] =
      some (endGenericMulStore (endThawUIntReturnWord outDebt)
        (endThawUIntReturnWord outTell)) := by
  simp [bindParams?, subFunction, endGenericMulStore, endUIntValue]

theorem endThawInternalSubOk (evm : EVM.State) (outDai outDebt outTell : ByteArray)
    (preDebtEvm : EVM.State)
    (hle : (endThawUIntReturnWord outTell).toNat ≤
      (endThawUIntReturnWord outDebt).toNat) :
    ExecStmt config (endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm) evm
      (.internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew")
      (.ok (endThawAfterDebtNewFrame outDai outDebt outTell preDebtEvm) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endThawAfterDebtNewFrame,
    endThawDebtNewWord, endGenericSubResult] using
    internalCallFunctionReturn
      (cfg := config) (caller := endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm)
      (evm := evm) (calleeEvm := evm) (name := "sub") (retVar := "debtNew")
      (args := [.var "vatDebt", .var "cureTell"])
      (argVals := [endUIntValue (endThawUIntReturnWord outDebt),
        endUIntValue (endThawUIntReturnWord outTell)])
      (callee := subFunction)
      (locals := endGenericMulStore (endThawUIntReturnWord outDebt)
        (endThawUIntReturnWord outTell))
      (calleeSolm :=
        { contract := contract,
          locals := endGenericSubZStore (endThawUIntReturnWord outDebt)
            (endThawUIntReturnWord outTell) })
      (value := some [endUIntValue (endThawDebtNewWord outDebt outTell)])
      (endEvalThawSubArgs evm outDai outDebt outTell preDebtEvm)
      (by
        change lookupCallable? contract "sub" = some subFunction.toCallable
        rfl)
      (endBindParams_sub_thaw outDebt outTell)
      (by
        simpa [endThawDebtNewWord, endGenericSubResult] using
          endGenericSubFunctionOk evm (endThawUIntReturnWord outDebt)
            (endThawUIntReturnWord outTell) hle)

theorem endThawInternalSubRevert (evm : EVM.State) (outDai outDebt outTell : ByteArray)
    (preDebtEvm : EVM.State)
    (hlt : (endThawUIntReturnWord outDebt).toNat <
      (endThawUIntReturnWord outTell).toNat) :
    ExecStmt config (endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm) evm
      (.internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew")
      .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm)
    (evm := evm) (name := "sub") (retVar := "debtNew")
    (args := [.var "vatDebt", .var "cureTell"])
    (argVals := [endUIntValue (endThawUIntReturnWord outDebt),
      endUIntValue (endThawUIntReturnWord outTell)])
    (callee := subFunction)
    (locals := endGenericMulStore (endThawUIntReturnWord outDebt)
      (endThawUIntReturnWord outTell))
    (endEvalThawSubArgs evm outDai outDebt outTell preDebtEvm)
    (by
      change lookupCallable? contract "sub" = some subFunction.toCallable
      rfl)
    (endBindParams_sub_thaw outDebt outTell)
    (endGenericSubFunctionRevert evm (endThawUIntReturnWord outDebt)
      (endThawUIntReturnWord outTell) hlt)

theorem endEvalDebtNewVar_thaw (evm : EVM.State) (outDai outDebt outTell : ByteArray)
    (preDebtEvm : EVM.State) :
    evalExpr? config (endThawAfterDebtNewFrame outDai outDebt outTell preDebtEvm) evm
      (.var "debtNew") =
      .ok (endUIntValue (endThawDebtNewWord outDebt outTell)) := by
  simp [evalExpr?, EvalResult.ofOption,
    endThawAfterDebtNewFrame_get_debtNew outDai outDebt outTell preDebtEvm]

theorem endAssignDebtNew_thaw (evm : EVM.State) (outDai outDebt outTell : ByteArray)
    (preDebtEvm : EVM.State) :
    assignStorageRef? config (endThawAfterDebtNewFrame outDai outDebt outTell preDebtEvm)
        evm .storage debtRef (endUIntValue (endThawDebtNewWord outDebt outTell)) =
      .ok (endThawAfterDebtNewFrame outDai outDebt outTell preDebtEvm,
        endThawFinalState evm outDebt outTell) := by
  rw [assignStorageRef_storage_scalar
    (slot := debtRef)
    (er := { base := "debt", steps := [] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc ⟨11⟩)
    (n := Int.ofNat (endThawDebtNewWord outDebt outTell).toNat)
    (hbase := endThawAfterDebtNewFrame_get_debt_none outDai outDebt outTell preDebtEvm)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind,
        EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_debt)
    (hstore := by
      simpa [wordLoc, uint256Loc, endThawFinalState] using
        storageLocStore_uint256 evm ⟨11⟩ (endThawDebtNewWord outDebt outTell))]

theorem endThawAfterCureTellSuffixOk (evm : EVM.State)
    (outDai outDebt outTell : ByteArray) (preDebtEvm : EVM.State)
    (hle : (endThawUIntReturnWord outTell).toNat ≤
      (endThawUIntReturnWord outDebt).toNat) :
    ExecBlock config (endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm) evm
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ]
      (.ok (endThawAfterDebtNewFrame outDai outDebt outTell preDebtEvm)
        (endThawFinalState evm outDebt outTell)) := by
  exact ExecBlock.consNormal
    (endThawInternalSubOk evm outDai outDebt outTell preDebtEvm hle) <|
    ExecBlock.consNormal
      (ExecStmt.assign
        (endEvalDebtNewVar_thaw evm outDai outDebt outTell preDebtEvm)
        (endAssignDebtNew_thaw evm outDai outDebt outTell preDebtEvm))
      ExecBlock.nil

theorem endThawAfterCureTellSuffixSubRevert (evm : EVM.State)
    (outDai outDebt outTell : ByteArray) (preDebtEvm : EVM.State)
    (hlt : (endThawUIntReturnWord outDebt).toNat <
      (endThawUIntReturnWord outTell).toNat) :
    ExecBlock config (endThawAfterCureTellFrame outDai outDebt outTell preDebtEvm) evm
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ]
      .reverted := by
  exact ExecBlock.consRevert
    (endThawInternalSubRevert evm outDai outDebt outTell preDebtEvm hlt)

theorem endX_thaw_after_cure_tell_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw outDai outDebt outTell k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (houtTell : outTell.size < UInt256.size)
    (h32Debt : 32 ≤ outDebt.size) (h32Tell : 32 ≤ outTell.size)
    (hle : (endThawUIntReturnWord outTell).toNat ≤
      (endThawUIntReturnWord outDebt).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).pc
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).stack
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).mem
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).aw
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).rdata
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).world k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (endThawDebtStoredWorld world I outDebt outTell) ByteArray.empty := by
  have hfree :=
    endThawCureTellReturnMem_mload64 preσ I outDai outDebt outTell houtDai houtDebt
      houtTell
  have hcallFree :=
    endThawCureTellCallMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have htell :=
    endThawCureTellReturnMem_mloadCallFree preσ I outDai outDebt outTell houtDai
      houtDebt houtTell h32Tell
  have htell128 :
      memLoad (⟨128⟩ : UInt256)
          (endThawCureTellReturnMem preσ I outDai outDebt outTell) =
        endThawUIntReturnWord outTell := by
    unfold endThawCureTellCallFree at htell
    rw [hcallFree] at htell
    simpa using htell
  have hdebt :=
    endThawVatDebtLoadedWord_eq preσ I outDai outDebt houtDai houtDebt h32Debt
  have rd5183 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5183⟩
        [UInt256.ofNat outTell.size,
          memLoad (UInt256.ofNat 64)
            (endThawCureTellReturnMem preσ I outDai outDebt outTell),
          endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel]
        (endThawCureTellReturnMem preσ I outDai outDebt outTell)
        (endThawAfterCureTellAw preσ I outDai outDebt aw) outTell world k C := by
    simpa [endThawAfterCureTellCursor] using rd
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endRuntimeBlocks.endRuntime_block_5183_packed
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.ofNat outTell.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endThawCureTellReturnMem preσ I outDai outDebt outTell))
      (R := [endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel])
      (by simp) (by jump_dest) rd5183
  have rd10154' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
        [endThawUIntReturnWord outTell, endThawUIntReturnWord outDebt, ⟨5190⟩, ⟨562⟩, sel]
        (endThawCureTellReturnMem preσ I outDai outDebt outTell) aw10154 outTell
        world k10154 C10154 := by
    simpa [endRuntimeBlocks.endRuntime_block_5183_stack, hfree, htell128, hdebt] using
      rd10154
  obtain ⟨aw5190, k5190, C5190, rd5190⟩ :=
    endX_flow_sub_ok
      (x := endThawUIntReturnWord outDebt)
      (y := endThawUIntReturnWord outTell)
      (ret := (⟨5190⟩ : UInt256)) (R := [⟨562⟩, sel])
      hle (by jump_dest) (by simp) rd10154'
  obtain ⟨aw562, k562, C562, rd562⟩ :=
    endRuntimeBlocks.endRuntime_block_5190_packed
      (cA := world.1) (σ := world.2)
      (x0 := endThawDebtNewWord outDebt outTell) (x1 := (⟨562⟩ : UInt256))
      (R := [sel]) (by simp) hperm (by jump_dest)
      (by simpa [endThawDebtNewWord] using rd5190)
  have rd562' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨562⟩ [sel]
        (endThawCureTellReturnMem preσ I outDai outDebt outTell) aw562 outTell
        (endThawDebtStoredWorld world I outDebt outTell) k562 C562 := by
    simpa [endThawDebtStoredWorld, endRuntimeBlocks.endRuntime_block_5190_stack] using
      rd562
  exact endRuntimeBlocks.endRuntime_block_562
    (cA := (endThawDebtStoredWorld world I outDebt outTell).1)
    (σ := (endThawDebtStoredWorld world I outDebt outTell).2)
    (R := [sel]) (by simp) rd562'

theorem endX_thaw_after_cure_tell_sub_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw outDai outDebt outTell k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (houtDai : outDai.size < UInt256.size) (houtDebt : outDebt.size < UInt256.size)
    (houtTell : outTell.size < UInt256.size) (h32Debt : 32 ≤ outDebt.size)
    (h32Tell : 32 ≤ outTell.size)
    (hlt : (endThawUIntReturnWord outDebt).toNat <
      (endThawUIntReturnWord outTell).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).pc
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).stack
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).mem
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).aw
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).rdata
      (endThawAfterCureTellCursor preσ I sel aw outDai outDebt outTell world).world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hfree :=
    endThawCureTellReturnMem_mload64 preσ I outDai outDebt outTell houtDai houtDebt
      houtTell
  have hcallFree :=
    endThawCureTellCallMem_mload64 preσ I outDai outDebt houtDai houtDebt
  have htell :=
    endThawCureTellReturnMem_mloadCallFree preσ I outDai outDebt outTell houtDai
      houtDebt houtTell h32Tell
  have htell128 :
      memLoad (⟨128⟩ : UInt256)
          (endThawCureTellReturnMem preσ I outDai outDebt outTell) =
        endThawUIntReturnWord outTell := by
    unfold endThawCureTellCallFree at htell
    rw [hcallFree] at htell
    simpa using htell
  have hdebt :=
    endThawVatDebtLoadedWord_eq preσ I outDai outDebt houtDai houtDebt h32Debt
  have rd5183 :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5183⟩
        [UInt256.ofNat outTell.size,
          memLoad (UInt256.ofNat 64)
            (endThawCureTellReturnMem preσ I outDai outDebt outTell),
          endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel]
        (endThawCureTellReturnMem preσ I outDai outDebt outTell)
        (endThawAfterCureTellAw preσ I outDai outDebt aw) outTell world k C := by
    simpa [endThawAfterCureTellCursor] using rd
  obtain ⟨aw10154, k10154, C10154, rd10154⟩ :=
    endRuntimeBlocks.endRuntime_block_5183_packed
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.ofNat outTell.size)
      (x1 := memLoad (UInt256.ofNat 64)
        (endThawCureTellReturnMem preσ I outDai outDebt outTell))
      (R := [endThawVatDebtLoadedWord preσ I outDai outDebt, ⟨5190⟩, ⟨562⟩, sel])
      (by simp) (by jump_dest) rd5183
  have rd10154' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10154⟩
        [endThawUIntReturnWord outTell, endThawUIntReturnWord outDebt, ⟨5190⟩, ⟨562⟩, sel]
        (endThawCureTellReturnMem preσ I outDai outDebt outTell) aw10154 outTell
        world k10154 C10154 := by
    simpa [endRuntimeBlocks.endRuntime_block_5183_stack, hfree, htell128, hdebt] using
      rd10154
  exact endX_flow_sub_fail
    (x := endThawUIntReturnWord outDebt)
    (y := endThawUIntReturnWord outTell)
    (ret := (⟨5190⟩ : UInt256)) (R := [⟨562⟩, sel])
    hlt (by simp) rd10154'

theorem endThawAfterCureTellSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preσ : AccountMap} {preDebtEvm : EVM.State}
    {preCureEvm : EVM.State} {outDai outDebt : ByteArray}
    (hperm : I.perm = true) (houtDai : outDai.size < UInt256.size)
    (houtDebt : outDebt.size < UInt256.size) (h32Debt : 32 ≤ outDebt.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨5183⟩
      (fun cur frame e =>
        frame = endThawAfterCureTellFrame outDai outDebt cur.rdata preDebtEvm ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        accountStaticStateEq preCureEvm.accountMap e.accountMap ∧
        cur.rdata.size < UInt256.size ∧
        32 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64)
              (endThawCureTellReturnMem preσ I outDai outDebt cur.rdata),
            endThawVatDebtLoadedWord preσ I outDai outDebt,
            ⟨5190⟩, ⟨562⟩, sel] ∧
        cur.mem = endThawCureTellReturnMem preσ I outDai outDebt cur.rdata ∧
        cur.aw = endThawAfterCureTellAw preσ I outDai outDebt aw)
      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
        .assign .storage debtRef (.var "debtNew") ]
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, _hstatic, houtTell, h32Tell, hstack, hmem, haw⟩
  cases hframe
  by_cases hle :
      (endThawUIntReturnWord cur.rdata).toNat ≤
        (endThawUIntReturnWord outDebt).toNat
  · have hsource := endThawAfterCureTellSuffixOk evm outDai outDebt cur.rdata
      preDebtEvm hle
    have rdret := endX_thaw_after_cure_tell_success
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw)
      (outDai := outDai) (outDebt := outDebt) (outTell := cur.rdata)
      (k := k) (C := C) (world := cur.world)
      hperm houtDai houtDebt houtTell h32Debt h32Tell hle
      (by
        simpa [hpc, hstack, hmem, haw, endThawAfterCureTellCursor] using rd)
    have hstored := hrel.storageStore_codeOwner ⟨11⟩
      (endThawDebtNewWord outDebt cur.rdata)
    exact BlockProgress.ofRDret hsource rdret
      (by
        simpa [endThawDebtStoredWorld] using hstored.created.symm)
      (by
        simpa [endThawDebtStoredWorld, storageWrite] using hstored.accounts)
      abiVoidFallthrough
  · have hlt :
        (endThawUIntReturnWord outDebt).toNat <
          (endThawUIntReturnWord cur.rdata).toNat := by
      omega
    have hsource := endThawAfterCureTellSuffixSubRevert evm outDai outDebt cur.rdata
      preDebtEvm hlt
    have hrev := endX_thaw_after_cure_tell_sub_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := preσ) (sel := sel) (aw := aw)
      (outDai := outDai) (outDebt := outDebt) (outTell := cur.rdata)
      (k := k) (C := C) (world := cur.world)
      houtDai houtDebt houtTell h32Debt h32Tell hlt
      (by
        simpa [hpc, hstack, hmem, haw, endThawAfterCureTellCursor] using rd)
    exact ⟨.reverted, .reverted, hsource, hrev, by
      change True
      trivial⟩

theorem endThawCureCodeSize_eq_world_of_callRel {s0 world I evm}
    (h : CallStateRel s0 I world evm) :
    extCodeSizeWord evm.accountMap
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
          solcAddrMask) =
      extCodeSizeWord world.2 (endThawCureTellTarget world.2 I) := by
  have hslot := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 7)
  rw [h.env] at hslot
  rw [h.env]
  rw [hslot]
  have htarget :
      UInt256.land (storageRead I.codeOwner world.2 (UInt256.ofNat 7)) solcAddrMask =
        endThawCureTellTarget world.2 I := by
    unfold endThawCureTellTarget
    rw [show endThawVatDebtGeneratedMask = solcAddrMask from by native_decide]
  rw [htarget]
  exact (extCodeSizeWord_accountMapEquiv h.accounts
    (endThawCureTellTarget world.2 I)).symm

set_option maxHeartbeats 12000000 in
theorem endThawAfterVatDebtSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preσ : AccountMap} {preDebtEvm : EVM.State}
    {outDai : ByteArray} (hperm : I.perm = true)
    (houtDai : outDai.size < UInt256.size) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨5070⟩
      (fun cur frame e =>
        frame = endThawAfterVatDebtFrame outDai cur.rdata preDebtEvm ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.rdata.size < UInt256.size ∧
        32 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endThawVatDebtReturnMem preσ I outDai cur.rdata),
            ⟨5190⟩, ⟨562⟩, sel] ∧
        cur.mem = endThawVatDebtReturnMem preσ I outDai cur.rdata ∧
        cur.aw = endThawAfterVatDebtAw preσ I outDai aw)
      (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
          (perm := false) ++
        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
          .assign .storage debtRef (.var "debtNew") ])
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, houtDebt, h32Debt, hstack, hmem, haw⟩
  cases hframe
  have rdDebt :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        (endThawAfterVatDebtCursor preσ I sel aw outDai cur.rdata cur.world).pc
        (endThawAfterVatDebtCursor preσ I sel aw outDai cur.rdata cur.world).stack
        (endThawAfterVatDebtCursor preσ I sel aw outDai cur.rdata cur.world).mem
        (endThawAfterVatDebtCursor preσ I sel aw outDai cur.rdata cur.world).aw
        (endThawAfterVatDebtCursor preσ I sel aw outDai cur.rdata cur.world).rdata
        (endThawAfterVatDebtCursor preσ I sel aw outDai cur.rdata cur.world).world k C := by
    simpa [endThawAfterVatDebtCursor, hpc, hstack, hmem, haw] using rd
  have hcodeEq := endThawCureCodeSize_eq_world_of_callRel hrel
  by_cases hnocode : extCodeSizeWord cur.world.2 (endThawCureTellTarget cur.world.2 I) = ⟨0⟩
  · have hsrcNoCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
              solcAddrMask) = ⟨0⟩ := by
      rw [hcodeEq, hnocode]
    have hsource :
        ExecBlock config (endThawAfterVatDebtFrame outDai cur.rdata preDebtEvm) evm
          (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
              (perm := false) ++
            [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
              .assign .storage debtRef (.var "debtNew") ])
          .reverted := by
      simpa [checkedExternalCallStmts] using
        (ExecBlock.consRevert
          (ExecStmt.requireFalse
            (endEvalCureCodeGuard_thaw_afterVatDebt_false evm outDai cur.rdata
              preDebtEvm hsrcNoCode)))
    have hrev := endX_thaw_cure_tell_no_code
      (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (preσ := preσ) (sel := sel) (aw := aw) (outDai := outDai)
      (outDebt := cur.rdata) (world := cur.world) hnocode rdDebt
    exact ⟨.reverted, .reverted, hsource, hrev, by
      change True
      trivial⟩
  · have hsrcCode :
        extCodeSizeWord evm.accountMap
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 7))
              solcAddrMask) ≠ ⟨0⟩ := by
      intro hzero
      exact hnocode (hcodeEq.symm.trans hzero)
    have hsourceReq :
        ExecBlock config (endThawAfterVatDebtFrame outDai cur.rdata preDebtEvm) evm
          [ .require (.binary .gt (.extCodeSize (.storage cureRef)) (.intLit 0)) ]
          (.ok (endThawAfterVatDebtFrame outDai cur.rdata preDebtEvm) evm) := by
      exact ExecBlock.consNormal
        (ExecStmt.requireTrue
          (endEvalCureCodeGuard_thaw_afterVatDebt_true evm outDai cur.rdata
            preDebtEvm hsrcCode))
        ExecBlock.nil
    obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
      endX_thaw_to_cure_tell_call
        (I := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
        (preσ := preσ) (sel := sel) (aw := aw) (outDai := outDai)
        (outDebt := cur.rdata) (world := cur.world) hnocode rdDebt
    have htail :
        BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
          (endThawCureTellCallCursor cur.world preσ I sel awCall outDai cur.rdata
            cur.rdata)
          kCall CCall (endThawAfterVatDebtFrame outDai cur.rdata preDebtEvm) evm
          (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
          ([ .externalCall (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
              (perm := false) ] ++
            [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
              .assign .storage debtRef (.var "debtNew") ])
          (runtimeExit (.abi [])) := by
      refine BlockRefinesFrom.seqOrExit
        (endThawCureTellExternalCallRefines
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
          (I := I) (g := g) (sel := sel) (aw := awCall) (rdata := cur.rdata)
          (k := kCall) (C := CCall) (evm := evm) (preDebtEvm := preDebtEvm)
          (preσ := preσ) (outDai := outDai) (outDebt := cur.rdata)
          (world := cur.world) houtDai houtDebt) ?_
      exact endThawAfterCureTellSuffixRefines
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g) (sel := sel) (aw := awCall) (preσ := preσ)
        (preDebtEvm := preDebtEvm) (preCureEvm := evm)
        (outDai := outDai) (outDebt := cur.rdata) hperm houtDai houtDebt h32Debt
    have hprogress := BlockProgress.seqOfRD hsourceReq
      (cur' := endThawCureTellCallCursor cur.world preσ I sel awCall outDai cur.rdata
        cur.rdata)
      (k' := kCall) (C' := CCall)
      (frame' := endThawAfterVatDebtFrame outDai cur.rdata preDebtEvm) (evm' := evm)
      rdCall hrel htail
    simpa [checkedExternalCallStmts, List.append_assoc] using hprogress

theorem endThawVatDebtThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {preσ : AccountMap} {preEvm : EVM.State}
    (hperm : I.perm = true) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨5030⟩
      (fun cur frame e =>
        frame = endThawAfterDeadlineFrame cur.rdata e ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        accountStaticStateEq preEvm.accountMap e.accountMap ∧
        cur.rdata.size < UInt256.size ∧
        32 ≤ cur.rdata.size ∧
        cur.stack = endThawVatDebtCallStack preσ cur.world.2 I cur.rdata sel ∧
        cur.mem = endThawVatDebtCallMem preσ I cur.rdata)
      ([ .externalCall (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ] ++
        (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
            (perm := false) ++
          [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
            .assign .storage debtRef (.var "debtNew") ]))
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, _hstatic, houtDai, _h32Dai, hstack, hmem⟩
  cases hframe
  have rdDebtStart :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        (endThawVatDebtCallCursor cur.world preσ I sel cur.aw cur.rdata cur.rdata).pc
        (endThawVatDebtCallCursor cur.world preσ I sel cur.aw cur.rdata cur.rdata).stack
        (endThawVatDebtCallCursor cur.world preσ I sel cur.aw cur.rdata cur.rdata).mem
        (endThawVatDebtCallCursor cur.world preσ I sel cur.aw cur.rdata cur.rdata).aw
        (endThawVatDebtCallCursor cur.world preσ I sel cur.aw cur.rdata cur.rdata).rdata
        (endThawVatDebtCallCursor cur.world preσ I sel cur.aw cur.rdata cur.rdata).world
        k C := by
    simpa [endThawVatDebtCallCursor, hpc, hstack, hmem] using rd
  exact (BlockRefinesFrom.seqOrExit
    (endThawVatDebtExternalCallRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := cur.aw) (rdata := cur.rdata)
      (k := k) (C := C) (evm := evm) (preσ := preσ) (outDai := cur.rdata)
      (world := cur.world) houtDai hperm)
    (endThawAfterVatDebtSuffixRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := cur.aw) (preσ := preσ)
      (preDebtEvm := evm) (outDai := cur.rdata) hperm houtDai))
    rdDebtStart hrel

theorem endThawAfterVatDaiThroughFinalRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256} {preσ : AccountMap} {preEvm : EVM.State}
    (hperm : I.perm = true) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨4791⟩
      (fun cur frame e =>
        frame = endThawAfterVatDaiFrame cur.rdata ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        accountStaticStateEq preEvm.accountMap e.accountMap ∧
        cur.rdata.size < UInt256.size ∧
        32 ≤ cur.rdata.size ∧
        cur.stack =
          [UInt256.ofNat cur.rdata.size,
            memLoad (UInt256.ofNat 64) (endThawVatDaiReturnMem preσ I cur.rdata),
            ⟨562⟩, sel] ∧
        cur.mem = endThawVatDaiReturnMem preσ I cur.rdata ∧
        cur.aw = endThawAfterVatDaiAw aw)
      ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
        .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
        .require (.binary .ge nowT (.var "deadline")),
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
        ([ .externalCall (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ] ++
          (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) [] "cureTell"
              (perm := false) ++
            [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
              .assign .storage debtRef (.var "debtNew") ])))
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  exact BlockProgress.seqOrExit
    (endThawAfterVatDaiPrefixRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (aw := aw) (preEvm := preEvm) preσ
      cur k C frame evm hpc rd hP)
    (endThawVatDebtThroughFinalRefines
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (sel := sel) (preσ := preσ) (preEvm := preEvm) hperm)

theorem endThawLiveWorldWord_eq_of_accountMapEquiv {σ_evm σ_solm I}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    endThawLiveWorldWord σ_evm I = endThawLiveWorldWord σ_solm I := by
  unfold endThawLiveWorldWord
  simpa [storageRead_eq] using
    accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 8)
      (default : UInt256)

theorem endThawDebtWorldWord_eq_of_accountMapEquiv {σ_evm σ_solm I}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    endThawDebtWorldWord σ_evm I = endThawDebtWorldWord σ_solm I := by
  unfold endThawDebtWorldWord
  simpa [storageRead_eq] using
    accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 11)
      (default : UInt256)

theorem endThawLiveWord_init_eq (cA gh bl σ σ₀ A I) (g : Sat256) :
    endThawLiveWord (initState cA gh bl σ σ₀ g A I) =
      endThawLiveWorldWord σ I := by
  unfold endThawLiveWord endThawLiveWorldWord
  change Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (UInt256.ofNat 8) = storageRead I.codeOwner σ (UInt256.ofNat 8)
  rw [endPackStorageLoad_init_eq]
  simp [solcSlotWord, storageRead_eq]

theorem endThawDebtWord_init_eq (cA gh bl σ σ₀ A I) (g : Sat256) :
    endThawDebtWord (initState cA gh bl σ σ₀ g A I) =
      endThawDebtWorldWord σ I := by
  unfold endThawDebtWord endThawDebtWorldWord
  change Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
      (UInt256.ofNat 11) = storageRead I.codeOwner σ (UInt256.ofNat 11)
  rw [endPackStorageLoad_init_eq]
  simp [solcSlotWord, storageRead_eq]

set_option maxHeartbeats 12000000 in
theorem endThawBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 28))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨707⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 28 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some thawTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 28 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some thawTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (thawTransition.params.map Param.name) (transitionSignature thawTransition).paramTypes
      I.calldata = some endThawStore := by
    show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata =
      some (∅ : Store)
    exact decodeCalldataWithMode_empty_ok hsz4
  have hLiveWord :
      endThawLiveWorldWord σ_evm I = endThawLiveWorldWord σ_solm I :=
    endThawLiveWorldWord_eq_of_accountMapEquiv hAccounts
  by_cases hliveSolm : endThawLiveWorldWord σ_solm I = ⟨0⟩
  · have hliveEvm : endThawLiveWorldWord σ_evm I = ⟨0⟩ :=
      hLiveWord.trans hliveSolm
    have hliveSrc :
        endThawLiveWord
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) = ⟨0⟩ := by
      rw [endThawLiveWord_init_eq]
      exact hliveSolm
    have hDebtWord :
        endThawDebtWorldWord σ_evm I = endThawDebtWorldWord σ_solm I :=
      endThawDebtWorldWord_eq_of_accountMapEquiv hAccounts
    by_cases hdebtSolm : endThawDebtWorldWord σ_solm I = ⟨0⟩
    · have hdebtEvm : endThawDebtWorldWord σ_evm I = ⟨0⟩ :=
        hDebtWord.trans hdebtSolm
      have hdebtSrc :
          endThawDebtWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) = ⟨0⟩ := by
        rw [endThawDebtWord_init_eq]
        exact hdebtSolm
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
              endThawStore thawTransition.body .reverted := by
          simpa [initState] using
            endThawBodyVatDaiNoCode
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (by simp only [initState]; exact hwv) hliveSrc hdebtSrc hvatNoCodeSrc
        exact (endX_thaw_vat_dai_no_code
            (g := Sat256.ofUInt256 g) hliveEvm hdebtEvm hvatNoCodeEvm hreach)
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
          endX_thaw_to_vat_dai_call
            (g := Sat256.ofUInt256 g) hliveEvm hdebtEvm hvatNoCodeEvm hreach
        have hprefix :
            ExecBlock config { contract := contract, locals := endThawStore }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (nonpayable ++
                [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
                  .require (.binary .eq (.storage debtRef) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
              (.ok { contract := contract, locals := endThawStore }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
          endThawBodyPrefixOk
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (by simp only [initState]; exact hwv) hliveSrc hdebtSrc hvatCodeSrc
        have hpostRel :
            CallStateRel
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
              (cA, σ_evm)
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
          CallStateRel.initState hAccounts
        have htail :
            BlockRefinesFrom endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) config
              (endThawVatDaiCallCursor cA σ_evm I sel awCall ByteArray.empty)
              kCall CCall { contract := contract, locals := endThawStore }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (fun cur _ e =>
                CallStateRel
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  I cur.world e)
              ([ .externalCall (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
                  (perm := false) ] ++
                ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                  .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
                  .require (.binary .ge nowT (.var "deadline")),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
                  ([ .externalCall (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ] ++
                    (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) []
                        "cureTell" (perm := false) ++
                      [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
                        .assign .storage debtRef (.var "debtNew") ]))))
              (runtimeExit (.abi [])) := by
          refine BlockRefinesFrom.seqOrExit
            (endThawVatDaiExternalCallRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) (rdata := ByteArray.empty) (k := kCall)
              (C := CCall)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ?_
          exact endThawAfterVatDaiThroughFinalRefines
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
            (I := I) (g := Sat256.ofUInt256 g) (sel := sel) (aw := awCall)
            (preσ := σ_evm)
            (preEvm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            hperm
        have hprogress :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endThawStore }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ((nonpayable ++
                [ .require (.binary .eq (.storage liveRef) (.intLit 0)),
                  .require (.binary .eq (.storage debtRef) (.intLit 0)),
                  .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]) ++
                ([ .externalCall (.storage vatRef) "dai" (.intLit 0) [vowAddr] "vatDai"
                    (perm := false) ] ++
                  ([ .require (.binary .eq (.var "vatDai") (.intLit 0)),
                    .internalCall "add" [.storage whenRef, .storage waitRef] "deadline",
                    .require (.binary .ge nowT (.var "deadline")),
                    .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ] ++
                    ([ .externalCall (.storage vatRef) "debt" (.intLit 0) [] "vatDebt" ] ++
                      (checkedExternalCallStmts (.storage cureRef) "tell" (.intLit 0) []
                          "cureTell" (perm := false) ++
                        [ .internalCall "sub" [.var "vatDebt", .var "cureTell"] "debtNew",
                          .assign .storage debtRef (.var "debtNew") ])))))
              (runtimeExit (.abi [])) :=
          BlockProgress.seqOfRD
            (R := fun cur _ e =>
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I cur.world e)
            hprefix
            (by simpa [endThawVatDaiCallCursor] using rdCall)
            hpostRel
            htail
        have hprogressBody :
            BlockProgress endBytecode I (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              config { contract := contract, locals := endThawStore }
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              thawTransition.body (runtimeExit (.abi [])) := by
          simpa [thawTransition, checkedExternalCallStmts, List.append_assoc] using hprogress
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
    · have hdebtEvm : endThawDebtWorldWord σ_evm I ≠ ⟨0⟩ := by
        intro hbad
        exact hdebtSolm (hDebtWord.symm.trans hbad)
      have hdebtSrc :
          endThawDebtWord
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ≠ ⟨0⟩ := by
        rw [endThawDebtWord_init_eq]
        exact hdebtSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            endThawStore thawTransition.body .reverted := by
        simpa [initState] using
          endThawBodyDebtFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (by simp only [initState]; exact hwv) hliveSrc hdebtSrc
      exact (endX_thaw_debt_fail (g := Sat256.ofUInt256 g) hliveEvm hdebtEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hliveEvm : endThawLiveWorldWord σ_evm I ≠ ⟨0⟩ := by
      intro hbad
      exact hliveSolm (hLiveWord.symm.trans hbad)
    have hliveSrc :
        endThawLiveWord
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ≠ ⟨0⟩ := by
      rw [endThawLiveWord_init_eq]
      exact hliveSolm
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          endThawStore thawTransition.body .reverted := by
      simpa [initState] using
        endThawBodyLiveFail
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv) hliveSrc
    exact (endX_thaw_live_fail (g := Sat256.ofUInt256 g) hliveEvm hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.Dss.End
