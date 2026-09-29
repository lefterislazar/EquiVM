import Benchmarks.ActAmm4.Common
import Benchmarks.ActAmm4.Transfer
import Benchmarks.ActAmm4.Allowance
import Benchmarks.ActAmm4.Arithmetic
import Benchmarks.ActAmm4.Decode
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Trusted
import Benchmarks.ActAmm4.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
abbrev amm4TransferFromFromWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)
abbrev amm4TransferFromToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)
abbrev amm4TransferFromValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)
abbrev amm4TransferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "from"
    (.address (AccountAddress.ofNat (amm4TransferFromFromWord I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (amm4TransferFromToWord I).toNat))).insert "value"
    (.int (Int.ofNat (amm4TransferFromValueWord I).toNat))
theorem amm4Decode_transferFrom_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hfrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hto : (amm4TransferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (amm4TransferFromStore I) := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, amm4TransferFromStore,
    amm4TransferFromFromWord, amm4TransferFromToWord, amm4TransferFromValueWord,
    calldataWord] using
    decodeCalldata_address_address_uint256_ok
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hfrom hto
theorem amm4Decode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_address_address_uint256_none_short
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz4 hshort
theorem amm4Decode_transferFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_address_address_uint256_none_huge
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hbig
theorem amm4Decode_transferFrom_none_noncanonFrom {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4TransferFromFromWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, amm4TransferFromFromWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hnc
theorem amm4Decode_transferFrom_none_noncanonTo {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hfrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (amm4TransferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, amm4TransferFromFromWord,
    amm4TransferFromToWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hfrom hnc
abbrev amm4TransferFromFromValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4TransferFromFromWord I).toNat)
abbrev amm4TransferFromToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (amm4TransferFromToWord I).toNat)
abbrev amm4TransferFromValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (amm4TransferFromValueWord I).toNat)

def amm4TransferFromAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (amm4TransferFromFromWord I).toNat))
    (.address I.source)

def amm4TransferFromBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (amm4TransferFromFromWord I).toNat))

def amm4TransferFromToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (amm4TransferFromToWord I).toNat))

theorem amm4TransferFromAllowanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4TransferFromFromWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (amm4TransferFromFromWord I))
      (solcSourceWord I) = amm4TransferFromAllowanceSlot I := by
  unfold amm4TransferFromAllowanceSlot allowanceSlot allowanceOwnerSlot mapSlot
    solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon,
    amm4Source_keyValueToWord I.source]

theorem amm4TransferFromBalanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4TransferFromFromWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (amm4TransferFromFromWord I) =
      amm4TransferFromBalanceSlot I := by
  unfold amm4TransferFromBalanceSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem amm4TransferFromToSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4TransferFromToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (amm4TransferFromToWord I) =
      amm4TransferFromToSlot I := by
  unfold amm4TransferFromToSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem amm4TransferFromStore_from (I : ExecutionEnv) :
    (amm4TransferFromStore I).get? "from" = some (amm4TransferFromFromValue I) := by
  rw [amm4TransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem amm4TransferFromStore_to (I : ExecutionEnv) :
    (amm4TransferFromStore I).get? "to" = some (amm4TransferFromToValue I) := by
  rw [amm4TransferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem amm4TransferFromStore_value (I : ExecutionEnv) :
    (amm4TransferFromStore I).get? "value" = some (amm4TransferFromValueValue I) := by
  rw [amm4TransferFromStore, store_get_self]

theorem amm4TransferFromStore_allowance (I : ExecutionEnv) :
    (amm4TransferFromStore I).get? "allowance" = none := by
  rw [amm4TransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem amm4TransferFromStore_balance (I : ExecutionEnv) :
    (amm4TransferFromStore I).get? "balanceOf" = none := by
  rw [amm4TransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def amm4TransferFromAllowanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps :=
    [.mindex (.address (AccountAddress.ofNat (amm4TransferFromFromWord I).toNat)),
      .mindex (.address I.source)] }

def amm4TransferFromBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps :=
    [.mindex (.address (AccountAddress.ofNat (amm4TransferFromFromWord I).toNat))] }

def amm4TransferFromToRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps :=
    [.mindex (.address (AccountAddress.ofNat (amm4TransferFromToWord I).toNat))] }

theorem amm4TransferFromEvalAllowanceRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := amm4TransferFromStore I } evm
      (allowanceRef (.var "from") sender) = .ok (amm4TransferFromAllowanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferFromAllowanceRef, amm4TransferFromFromValue,
    amm4TransferFromStore_from, sender, envValue, hsrc]

theorem amm4TransferFromEvalBalanceRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := amm4TransferFromStore I } evm
      (balanceOfRef (.var "from")) = .ok (amm4TransferFromBalanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferFromBalanceRef, amm4TransferFromFromValue,
    amm4TransferFromStore_from]

theorem amm4TransferFromEvalToRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := amm4TransferFromStore I } evm
      (balanceOfRef (.var "to")) = .ok (amm4TransferFromToRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferFromToRef, amm4TransferFromToValue,
    amm4TransferFromStore_to]

def amm4TransferFromAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (amm4TransferFromAllowanceSlot I)

def amm4TransferFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (amm4TransferFromBalanceSlot I)

theorem amm4TransferFromEvalAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.storage (allowanceRef (.var "from") sender)) =
        .ok (.int (Int.ofNat (amm4TransferFromAllowanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := amm4TransferFromStore_allowance I)
    (her := amm4TransferFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [amm4TransferFromAllowanceWord, amm4TransferFromAllowanceSlot,
    amm4StorageLocLoad_uint256]

theorem amm4TransferFromEvalBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.storage (balanceOfRef (.var "from"))) =
        .ok (.int (Int.ofNat (amm4TransferFromBalanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := amm4TransferFromStore_balance I)
    (her := amm4TransferFromEvalBalanceRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferFromBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [amm4TransferFromBalanceWord, amm4TransferFromBalanceSlot,
    amm4StorageLocLoad_uint256]

theorem amm4TransferFromEvalToBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.storage (balanceOfRef (.var "to"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (amm4TransferFromToSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := amm4TransferFromStore_balance I)
    (her := amm4TransferFromEvalToRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferFromToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [amm4TransferFromToSlot, amm4StorageLocLoad_uint256]

theorem amm4TransferFromEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.var "value") = .ok (amm4TransferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4TransferFromStore_value]

theorem amm4TransferFromEvalFromNeSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.binary .ne (.var "from") sender) =
        .ok (.bool (!(amm4TransferFromFromValue I == .address I.source))) := by
  have hfrom : evalExpr? config
      { contract := contract, locals := amm4TransferFromStore I } evm (.var "from") =
      .ok (amm4TransferFromFromValue I) := by
    simp only [evalExpr?, EvalResult.ofOption, amm4TransferFromStore_from]
  have hsender : evalExpr? config
      { contract := contract, locals := amm4TransferFromStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hfrom, hsender, evalBinaryOp?]

theorem amm4TransferFromEvalAllowanceNeMax (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "from") sender))
        (.intLit maxUint256)) =
      .ok (.bool (!(Value.int (Int.ofNat
        (amm4TransferFromAllowanceWord evm I).toNat) == .int maxUint256))) := by
  have hallow := amm4TransferFromEvalAllowance evm I hsrc
  simp [evalExpr?, EvalResult.bind, bind, hallow, evalBinaryOp?]

theorem amm4TransferFromEvalCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) =
      .ok (.bool ((!(amm4TransferFromFromValue I == .address I.source)) &&
        (!(Value.int (Int.ofNat (amm4TransferFromAllowanceWord evm I).toNat) ==
          .int maxUint256)))) := by
  rw [evalExpr?]
  rw [amm4TransferFromEvalFromNeSender evm I hsrc]
  simp only [EvalResult.bind, bind]
  cases hleft : (!(amm4TransferFromFromValue I == .address I.source))
  · simp [pure]
  · rw [amm4TransferFromEvalAllowanceNeMax evm I hsrc]
    simp [pure]

def amm4TransferFromShouldSpend (evm : EVM.State) (I : ExecutionEnv) : Bool :=
  (!(amm4TransferFromFromValue I == .address I.source)) &&
    (!(Value.int (Int.ofNat (amm4TransferFromAllowanceWord evm I).toNat) ==
      .int maxUint256))

theorem amm4TransferFromEvalCond' (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) =
      .ok (.bool (amm4TransferFromShouldSpend evm I)) := by
  exact amm4TransferFromEvalCond evm I hsrc

def amm4TransferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((amm4TransferFromAllowanceWord evm I).toNat -
    (amm4TransferFromValueWord I).toNat)

def amm4TransferFromAfterAllowance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if amm4TransferFromShouldSpend evm I then
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (amm4TransferFromAllowanceSlot I) (amm4TransferFromAllowanceDebitWord evm I)
  else evm

def amm4TransferFromBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat -
    (amm4TransferFromValueWord I).toNat)

def amm4TransferFromAfterBalance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (amm4TransferFromAfterAllowance evm I) evm.executionEnv.codeOwner
    (amm4TransferFromBalanceSlot I) (amm4TransferFromBalanceDebitWord evm I)

def amm4TransferFromToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (amm4TransferFromAfterBalance evm I) evm.executionEnv.codeOwner
    (amm4TransferFromToSlot I)

def amm4TransferFromNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (amm4TransferFromToBalanceWord evm I).toNat + (amm4TransferFromValueWord I).toNat

def amm4TransferFromNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (amm4TransferFromNewToNat evm I)

def amm4TransferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (amm4TransferFromAfterBalance evm I) evm.executionEnv.codeOwner
    (amm4TransferFromToSlot I) (amm4TransferFromNewToWord evm I)

theorem amm4TransferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferFromAfterAllowance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  unfold amm4TransferFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem amm4TransferFromAfterAllowance_source (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferFromAfterAllowance evm I).executionEnv.source =
      evm.executionEnv.source := by
  unfold amm4TransferFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem amm4TransferFromAfterBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferFromAfterBalance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [amm4TransferFromAfterBalance, storageStore_executionEnv,
    amm4TransferFromAfterAllowance_codeOwner]

theorem amm4TransferFromAllowanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferFromAllowanceDebitWord evm I).toNat =
      (amm4TransferFromAllowanceWord evm I).toNat -
        (amm4TransferFromValueWord I).toNat := by
  unfold amm4TransferFromAllowanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (amm4TransferFromAllowanceWord evm I).val.isLt

theorem amm4TransferFromBalanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (amm4TransferFromBalanceDebitWord evm I).toNat =
      (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat -
        (amm4TransferFromValueWord I).toNat := by
  unfold amm4TransferFromBalanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _)
    (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).val.isLt

theorem amm4TransferFromEvalAllowanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (amm4TransferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) =
        .ok (.int (Int.ofNat ((amm4TransferFromAllowanceWord evm I).toNat -
          (amm4TransferFromValueWord I).toNat))) := by
  exact amm4EvalCheckedSub_ok (amm4TransferFromEvalAllowance evm I hsrc)
    (amm4TransferFromEvalValue evm I) hle (amm4TransferFromAllowanceWord evm I).val.isLt

theorem amm4TransferFromEvalAllowanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (amm4TransferFromAllowanceWord evm I).toNat <
      (amm4TransferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I } evm
      (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) =
        .revert := by
  exact amm4EvalCheckedSub_revert (amm4TransferFromEvalAllowance evm I hsrc)
    (amm4TransferFromEvalValue evm I) hunder

theorem amm4TransferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := amm4TransferFromStore I } evm
      .storage (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (amm4TransferFromAllowanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := amm4TransferFromStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (amm4TransferFromAllowanceSlot I) (amm4TransferFromAllowanceDebitWord evm I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := amm4TransferFromStore_allowance I)
    (her := amm4TransferFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [amm4TransferFromAllowanceSlot] using
    amm4StorageLocStore_uint256 evm (amm4TransferFromAllowanceSlot I)
      (amm4TransferFromAllowanceDebitWord evm I)

theorem amm4TransferFromEvalBalanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I }
      (amm4TransferFromAfterAllowance evm I)
      (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .ok (.int (Int.ofNat
          ((amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat -
            (amm4TransferFromValueWord I).toNat))) := by
  exact amm4EvalCheckedSub_ok
    (amm4TransferFromEvalBalance (amm4TransferFromAfterAllowance evm I) I)
    (amm4TransferFromEvalValue (amm4TransferFromAfterAllowance evm I) I) hle
    (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).val.isLt

theorem amm4TransferFromEvalBalanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hunder : (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat <
      (amm4TransferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I }
      (amm4TransferFromAfterAllowance evm I)
      (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .revert := by
  exact amm4EvalCheckedSub_revert
    (amm4TransferFromEvalBalance (amm4TransferFromAfterAllowance evm I) I)
    (amm4TransferFromEvalValue (amm4TransferFromAfterAllowance evm I) I) hunder

theorem amm4TransferFromAssignBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := amm4TransferFromStore I }
      (amm4TransferFromAfterAllowance evm I)
      .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat (amm4TransferFromBalanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := amm4TransferFromStore I },
        amm4TransferFromAfterBalance evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := amm4TransferFromStore_balance I)
    (her := amm4TransferFromEvalBalanceRef (amm4TransferFromAfterAllowance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferFromBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [amm4TransferFromAfterBalance, amm4TransferFromBalanceSlot,
    amm4TransferFromAfterAllowance_codeOwner evm I] using
    amm4StorageLocStore_uint256 (amm4TransferFromAfterAllowance evm I)
      (amm4TransferFromBalanceSlot I) (amm4TransferFromBalanceDebitWord evm I)

theorem amm4TransferFromNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferFromNewToNat evm I < UInt256.size) :
    (amm4TransferFromNewToWord evm I).toNat = amm4TransferFromNewToNat evm I := by
  unfold amm4TransferFromNewToWord
  exact ulit_toNat' _ hfit

theorem amm4TransferFromEvalCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferFromNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I }
      (amm4TransferFromAfterBalance evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .ok (.int (Int.ofNat (amm4TransferFromNewToNat evm I))) := by
  have hload := amm4TransferFromEvalToBalance (amm4TransferFromAfterBalance evm I) I
  rw [amm4TransferFromAfterBalance_codeOwner evm I] at hload
  exact amm4EvalCheckedAdd_ok hload
    (amm4TransferFromEvalValue (amm4TransferFromAfterBalance evm I) I) hfit

theorem amm4TransferFromEvalCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ amm4TransferFromNewToNat evm I) :
    evalExpr? config { contract := contract, locals := amm4TransferFromStore I }
      (amm4TransferFromAfterBalance evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .revert := by
  have hload := amm4TransferFromEvalToBalance (amm4TransferFromAfterBalance evm I) I
  rw [amm4TransferFromAfterBalance_codeOwner evm I] at hload
  exact amm4EvalCheckedAdd_revert hload
    (amm4TransferFromEvalValue (amm4TransferFromAfterBalance evm I) I) hover

theorem amm4TransferFromAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : amm4TransferFromNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := amm4TransferFromStore I }
      (amm4TransferFromAfterBalance evm I) .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat (amm4TransferFromNewToNat evm I))) =
      .ok ({ contract := contract, locals := amm4TransferFromStore I },
        amm4TransferFromPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := amm4TransferFromStore_balance I)
    (her := amm4TransferFromEvalToRef (amm4TransferFromAfterBalance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferFromToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [amm4TransferFromPostState, amm4TransferFromAfterBalance_codeOwner evm I,
    amm4TransferFromToSlot, amm4TransferFromNewToWord_toNat evm I hfit] using
    amm4StorageLocStore_uint256 (amm4TransferFromAfterBalance evm I)
      (amm4TransferFromToSlot I) (amm4TransferFromNewToWord evm I)

theorem amm4TransferFromAllowanceStep_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : amm4TransferFromShouldSpend evm I = true →
      (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromAllowanceWord evm I).toNat) :
    ExecStmt config { contract := contract, locals := amm4TransferFromStore I } evm
      (.ite
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256)))
        [.assign .storage (allowanceRef (.var "from") sender)
          (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value"))] [])
      (.ok { contract := contract, locals := amm4TransferFromStore I }
        (amm4TransferFromAfterAllowance evm I)) := by
  by_cases hspend : amm4TransferFromShouldSpend evm I = true
  · have hcond : evalExpr? config
        { contract := contract, locals := amm4TransferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256))) = .ok (.bool true) := by
      rw [amm4TransferFromEvalCond' evm I hsrc, hspend]
    have hassign := amm4TransferFromAssignAllowance evm I hsrc
    rw [amm4TransferFromAllowanceDebitWord_toNat evm I] at hassign
    have hthen : ExecBlock config { contract := contract, locals := amm4TransferFromStore I }
        evm [.assign .storage (allowanceRef (.var "from") sender)
          (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value"))]
        (.ok { contract := contract, locals := amm4TransferFromStore I }
          (amm4TransferFromAfterAllowance evm I)) := by
      simpa [amm4TransferFromAfterAllowance, hspend] using
        (ExecBlock.consNormal
          (ExecStmt.assign
            (amm4TransferFromEvalAllowanceDebit_ok evm I hsrc (hle hspend)) hassign)
          ExecBlock.nil)
    exact ExecStmt.iteTrue hcond hthen
  · have hfalse : amm4TransferFromShouldSpend evm I = false := by
      cases h : amm4TransferFromShouldSpend evm I <;> simp_all
    have hcond : evalExpr? config
        { contract := contract, locals := amm4TransferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256))) = .ok (.bool false) := by
      rw [amm4TransferFromEvalCond' evm I hsrc, hfalse]
    simpa [amm4TransferFromAfterAllowance, hfalse] using
      (ExecStmt.iteFalse hcond (ExecBlock.nil :
        ExecBlock config { contract := contract, locals := amm4TransferFromStore I }
          evm [] (.ok { contract := contract, locals := amm4TransferFromStore I } evm)))

theorem amm4TransferFromBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : amm4TransferFromShouldSpend evm I = true →
      (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromAllowanceWord evm I).toNat)
    (hbalance : (amm4TransferFromValueWord I).toNat ≤
      (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat)
    (hfit : amm4TransferFromNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (amm4TransferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := amm4TransferFromStore I }
        (amm4TransferFromPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (amm4TransferFromAllowanceStep_ok evm I hsrc hallow) ?_
  have hassign := amm4TransferFromAssignBalance evm I
  rw [amm4TransferFromBalanceDebitWord_toNat evm I] at hassign
  refine ExecBlock.consNormal
    (ExecStmt.assign (amm4TransferFromEvalBalanceDebit_ok evm I hbalance) hassign) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (amm4TransferFromEvalCredit_ok evm I hfit)
      (amm4TransferFromAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem amm4TransferFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hspend : amm4TransferFromShouldSpend evm I = true)
    (hunder : (amm4TransferFromAllowanceWord evm I).toNat <
      (amm4TransferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (amm4TransferFromStore I)
      transferFromTransition.body .reverted := by
  have hcond : evalExpr? config
      { contract := contract, locals := amm4TransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) = .ok (.bool true) := by
    rw [amm4TransferFromEvalCond' evm I hsrc, hspend]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.iteTrue hcond <|
        ExecBlock.consRevert (ExecStmt.assignExprRevert
          (amm4TransferFromEvalAllowanceDebit_revert evm I hsrc hunder)))

theorem amm4TransferFromBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : amm4TransferFromShouldSpend evm I = true →
      (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromAllowanceWord evm I).toNat)
    (hunder : (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat <
      (amm4TransferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (amm4TransferFromStore I)
      transferFromTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (amm4TransferFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (amm4TransferFromEvalBalanceDebit_revert evm I hunder))

theorem amm4TransferFromBodyReverts_credit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : amm4TransferFromShouldSpend evm I = true →
      (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromAllowanceWord evm I).toNat)
    (hbalance : (amm4TransferFromValueWord I).toNat ≤
      (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evm I) I).toNat)
    (hover : UInt256.size ≤ amm4TransferFromNewToNat evm I) :
    ExecTransitionBody config contract evm (amm4TransferFromStore I)
      transferFromTransition.body .reverted := by
  have hassign := amm4TransferFromAssignBalance evm I
  rw [amm4TransferFromBalanceDebitWord_toNat evm I] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (amm4TransferFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consNormal
          (ExecStmt.assign (amm4TransferFromEvalBalanceDebit_ok evm I hbalance) hassign) <|
          ExecBlock.consRevert
            (ExecStmt.assignExprRevert (amm4TransferFromEvalCredit_revert evm I hover))

theorem amm4TransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4881⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨253⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨248⟩, swap2, swap1, push2 ⟨4881⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4TransferFromX_dec4657_from {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨4917⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    simpa using (solcCalldataStaticLenCheckOk (words := 3)
      (sz := I.calldata.size) (by omega) hszhi hsize)
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨4904⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨4917⟩, dup7, dup3, dup8, add, push2 ⟨4657⟩,
    jump (by jump_dest) ]⟩

theorem amm4TransferFromX_dec4917 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4917⟩
      [amm4TransferFromFromWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4657_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.amm4DecodeAddrOk rd hcanonFrom (by jump_dest) (by evm_ov)

theorem amm4TransferFromX_dec4657_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨4934⟩, ⟨32⟩,
        ⟨0⟩, ⟨0⟩, amm4TransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4917 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨4934⟩,
    dup7, dup3, dup8, add, push2 ⟨4657⟩, jump (by jump_dest) ]⟩

theorem amm4TransferFromX_dec4934 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4934⟩
      [amm4TransferFromToWord I, ⟨32⟩, ⟨0⟩, ⟨0⟩,
        amm4TransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4657_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.amm4DecodeAddrOk rd hcanonTo (by jump_dest) (by evm_ov)

theorem amm4TransferFromX_dec4708_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4708⟩
      [⟨4⟩ + ⟨64⟩, UInt256.ofNat I.calldata.size, ⟨4951⟩, ⟨64⟩,
        ⟨0⟩, amm4TransferFromToWord I, amm4TransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4934 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨4951⟩,
    dup7, dup3, dup8, add, push2 ⟨4708⟩, jump (by jump_dest) ]⟩

theorem amm4TransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨716⟩
      [amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4708_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  obtain ⟨_, _, rd4951⟩ := RD.amm4DecodeUint256Ok rd (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd4951 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, pop, swap3,
    jump (by jump_dest), jumpdest, push2 ⟨716⟩, jump (by jump_dest) ]⟩

theorem amm4TransferFromX_self_to_balance {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hself : amm4TransferFromFromWord I = solcSourceWord I)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd716⟩ := amm4TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (amm4TransferFromFromWord I) =
      amm4TransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd766₀ := evm_run rd716 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup5, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd766 := rd766₀
  rw [hsourceClean, hfromClean, hself] at rd766
  have hzero : UInt256.isZero (UInt256.eq (solcSourceWord I) (solcSourceWord I)) =
      ⟨0⟩ := by rw [uInt256_eq_self]; decide
  rw [hzero] at rd766
  have rd1191 := evm_run rd766 with [
    iszero, push2 ⟨929⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, iszero, push2 ⟨1191⟩, jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, by simpa [hself] using rd1191⟩

def amm4TransferFromAllowanceOuterSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨2⟩ (amm4TransferFromFromWord I)

noncomputable def amm4TransferFromAllowanceOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (amm4TransferFromFromWord I) ⟨2⟩ solcFreePtrMem

noncomputable def amm4TransferFromAllowanceMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (amm4TransferFromAllowanceOuterSlot I)
    (amm4TransferFromAllowanceOuterMem I)

def amm4TransferFromMaxWord : UInt256 :=
  ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩

theorem amm4TransferFromX_nonself_allowanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨927⟩
      [solcSlotWord σ I (amm4TransferFromAllowanceSlot I), amm4TransferFromMaxWord,
        ⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd716⟩ := amm4TransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (amm4TransferFromFromWord I) =
      amm4TransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hneqWord : UInt256.eq (amm4TransferFromFromWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hne (uInt256_eq_one_eq he))
  have rd766₀ := evm_run rd716 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup5, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd766 := rd766₀
  rw [hsourceClean, hfromClean, hneqWord] at rd766
  have rd773 := evm_run rd766 with [
    iszero, push2 ⟨929⟩, jumpiNT (by decide),
    pop ]
  have rd806 := rd773.pushConst amm4TransferFromMaxWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd854₀ := evm_run rd806 with [
    push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd854 := rd854₀
  rw [hfromClean, hfromClean] at rd854
  obtain ⟨_, _, rd867⟩ := RD.amm4MappingHashSuffix rd854 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromAllowanceOuterMem,
      amm4TransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (amm4TransferFromFromWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd854'₀ := evm_run rd867 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd854' := rd854'₀
  rw [hsourceClean, hsourceClean] at rd854'
  have hmem : (amm4TransferFromAllowanceOuterMem I).size = 96 := by
    unfold amm4TransferFromAllowanceOuterMem
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd926⟩ := RD.amm4MappingHashSuffix rd854' amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromAllowanceMem,
      amm4TransferFromAllowanceOuterSlot,
      amm4TransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (amm4TransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd927⟩ := rd926.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd927⟩

theorem amm4TransferFromX_max_to_balance {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hmax : solcSlotWord σ I (amm4TransferFromAllowanceSlot I) =
      amm4TransferFromMaxWord)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd927₀⟩ := amm4TransferFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz100 hsize hszhi
    hcanonFrom hcanonTo hne hreach
  have rd927 := rd927₀
  rw [hmax] at rd927
  exact ⟨_, _, evm_run rd927 with [
    eq, iszero, jumpdest, iszero, push2 ⟨1191⟩,
    jumpiT (by decide) (by jump_dest) ]⟩

theorem amm4TransferFromX_spend_start {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (amm4TransferFromAllowanceSlot I) ≠
      amm4TransferFromMaxWord)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨935⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd927₀⟩ := amm4TransferFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz100 hsize hszhi
    hcanonFrom hcanonTo hne hreach
  have hneqWord : UInt256.eq (solcSlotWord σ I (amm4TransferFromAllowanceSlot I))
      amm4TransferFromMaxWord = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnotmax (uInt256_eq_one_eq he))
  have rd928 := evm_run rd927₀ with [eq]
  rw [hneqWord] at rd928
  exact ⟨_, _, evm_run rd928 with [
    iszero, jumpdest, iszero, push2 ⟨1191⟩,
    jumpiNT (by decide) ]⟩

noncomputable def amm4TransferFromAllowanceReadOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (amm4TransferFromFromWord I) ⟨2⟩ (amm4TransferFromAllowanceMem I)

noncomputable def amm4TransferFromAllowanceReadMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (amm4TransferFromAllowanceOuterSlot I)
    (amm4TransferFromAllowanceReadOuterMem I)

theorem amm4TransferFromX_spend_load {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (amm4TransferFromAllowanceSlot I) ≠
      amm4TransferFromMaxWord)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1057⟩
      [solcSlotWord σ I (amm4TransferFromAllowanceSlot I),
        amm4TransferFromValueWord I, ⟨0⟩, amm4TransferFromValueWord I,
        amm4TransferFromToWord I, amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd935⟩ := amm4TransferFromX_spend_start (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have hfromClean : UInt256.land solcAddrMask (amm4TransferFromFromWord I) =
      amm4TransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd984₀ := evm_run rd935 with [
    dup2, push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd984 := rd984₀
  rw [hfromClean, hfromClean] at rd984
  have hmem : (amm4TransferFromAllowanceMem I).size = 96 := by
    unfold amm4TransferFromAllowanceMem amm4TransferFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd997⟩ := RD.amm4MappingHashSuffix rd984 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromAllowanceReadOuterMem,
      amm4TransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (amm4TransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1043₀ := evm_run rd997 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1043 := rd1043₀
  rw [hsourceClean, hsourceClean] at rd1043
  have hmem2 : (amm4TransferFromAllowanceReadOuterMem I).size = 96 := by
    unfold amm4TransferFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd1056⟩ := RD.amm4MappingHashSuffix rd1043 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromAllowanceReadMem,
      amm4TransferFromAllowanceOuterSlot,
      amm4TransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (amm4TransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1057⟩ := rd1056.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1057⟩

theorem amm4TransferFromX_spend_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (amm4TransferFromAllowanceSlot I) ≠
      amm4TransferFromMaxWord)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1066⟩
      [UInt256.sub (solcSlotWord σ I (amm4TransferFromAllowanceSlot I))
        (amm4TransferFromValueWord I), ⟨0⟩, amm4TransferFromValueWord I,
        amm4TransferFromToWord I, amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1057⟩ := amm4TransferFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have rd5253 := evm_run rd1057 with [
    push2 ⟨1066⟩, swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedSubOk rd5253 hle (by jump_dest) (by evm_ov)

theorem amm4TransferFromX_spend_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (amm4TransferFromAllowanceSlot I) ≠
      amm4TransferFromMaxWord)
    (hunder : (solcSlotWord σ I (amm4TransferFromAllowanceSlot I)).toNat <
      (amm4TransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1057⟩ := amm4TransferFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have rd5253 := evm_run rd1057 with [
    push2 ⟨1066⟩, swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedSubUnderflow rd5253 hunder (by evm_ov)

noncomputable def amm4TransferFromAllowanceStoreOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (amm4TransferFromFromWord I) ⟨2⟩ (amm4TransferFromAllowanceReadMem I)

noncomputable def amm4TransferFromAllowanceStoreMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (amm4TransferFromAllowanceOuterSlot I)
    (amm4TransferFromAllowanceStoreOuterMem I)

def amm4TransferFromEvmAllowanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (amm4TransferFromAllowanceSlot I)
    (UInt256.sub (solcSlotWord σ I (amm4TransferFromAllowanceSlot I))
      (amm4TransferFromValueWord I))

theorem amm4TransferFromX_spend_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hne : amm4TransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (amm4TransferFromAllowanceSlot I) ≠
      amm4TransferFromMaxWord)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromAllowanceStoreMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferFromEvmAllowanceMap σ I) k C := by
  obtain ⟨_, _, rd1066⟩ := amm4TransferFromX_spend_debit (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hle hreach
  have hfromClean : UInt256.land solcAddrMask (amm4TransferFromFromWord I) =
      amm4TransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd1115₀ := evm_run rd1066 with [
    jumpdest, push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1115 := rd1115₀
  rw [hfromClean, hfromClean] at rd1115
  have hmem : (amm4TransferFromAllowanceReadMem I).size = 96 := by
    unfold amm4TransferFromAllowanceReadMem amm4TransferFromAllowanceReadOuterMem
      amm4TransferFromAllowanceMem amm4TransferFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd1128⟩ := RD.amm4MappingHashSuffix rd1115 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromAllowanceStoreOuterMem,
      amm4TransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (amm4TransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1174₀ := evm_run rd1128 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1174 := rd1174₀
  rw [hsourceClean, hsourceClean] at rd1174
  have hmem2 : (amm4TransferFromAllowanceStoreOuterMem I).size = 96 := by
    unfold amm4TransferFromAllowanceStoreOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd1187⟩ := RD.amm4MappingHashSuffix rd1174 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromAllowanceStoreMem,
      amm4TransferFromAllowanceOuterSlot,
      amm4TransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (amm4TransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1189 := evm_run rd1187 with [dup2, swap1]
  obtain ⟨_, _, rd1190⟩ := rd1189.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [amm4TransferFromEvmAllowanceMap] using
    (evm_run rd1190 with [pop])⟩

noncomputable def amm4TransferFromBalanceReadMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (amm4TransferFromFromWord I) ⟨1⟩ mem

def amm4TransferFromEvmBalanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (amm4TransferFromBalanceSlot I)
    (UInt256.sub (solcSlotWord σ I (amm4TransferFromBalanceSlot I))
      (amm4TransferFromValueWord I))

noncomputable def amm4TransferFromBalanceStoreMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (amm4TransferFromFromWord I) ⟨1⟩
    (amm4TransferFromBalanceReadMem I mem)

noncomputable def amm4TransferFromToReadMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (amm4TransferFromToWord I) ⟨1⟩
    (amm4TransferFromBalanceStoreMem I mem)

noncomputable def amm4TransferFromToStoreMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (amm4TransferFromToWord I) ⟨1⟩
    (amm4TransferFromToReadMem I mem)

def amm4TransferFromEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (amm4TransferFromEvmBalanceMap σ I)
    (amm4TransferFromToSlot I)
    (solcSlotWord (amm4TransferFromEvmBalanceMap σ I) I
      (amm4TransferFromToSlot I) + amm4TransferFromValueWord I)

theorem amm4TransferFromX_balance_load {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1255⟩
      [solcSlotWord σA I (amm4TransferFromBalanceSlot I),
        amm4TransferFromValueWord I, ⟨0⟩, amm4TransferFromValueWord I,
        amm4TransferFromToWord I, amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromBalanceReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σA) k C := by
  obtain ⟨_, _, rd1191⟩ := hreach
  have hfromClean : UInt256.land solcAddrMask (amm4TransferFromFromWord I) =
      amm4TransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd1241₀ := evm_run rd1191 with [
    jumpdest, dup2, push1 ⟨1⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1241 := rd1241₀
  rw [hfromClean, hfromClean] at rd1241
  obtain ⟨_, _, rd1254⟩ := RD.amm4MappingHashSuffix rd1241 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromBalanceReadMem,
      amm4TransferFromBalanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (amm4TransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1255⟩ := rd1254.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1255⟩

theorem amm4TransferFromX_balance_debit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1264⟩
      [UInt256.sub (solcSlotWord σA I (amm4TransferFromBalanceSlot I))
        (amm4TransferFromValueWord I), ⟨0⟩, amm4TransferFromValueWord I,
        amm4TransferFromToWord I, amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromBalanceReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σA) k C := by
  obtain ⟨_, _, rd1255⟩ := amm4TransferFromX_balance_load hcanonFrom hmem hreach
  have rd5253 := evm_run rd1255 with [
    push2 ⟨1264⟩, swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedSubOk rd5253 hle (by jump_dest) (by evm_ov)

theorem amm4TransferFromX_balance_underflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hunder : (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat <
      (amm4TransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1255⟩ := amm4TransferFromX_balance_load hcanonFrom hmem hreach
  have rd5253 := evm_run rd1255 with [
    push2 ⟨1264⟩, swap2, swap1, push2 ⟨5253⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedSubUnderflow rd5253 hunder (by evm_ov)

theorem amm4TransferFromX_balance_stored {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1330⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromBalanceStoreMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd1264⟩ := amm4TransferFromX_balance_debit hcanonFrom hmem hle hreach
  have hfromClean : UInt256.land solcAddrMask (amm4TransferFromFromWord I) =
      amm4TransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd1313₀ := evm_run rd1264 with [
    jumpdest, push1 ⟨1⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1313 := rd1313₀
  rw [hfromClean, hfromClean] at rd1313
  have hmem2 : (amm4TransferFromBalanceReadMem I mem).size = 96 := by
    unfold amm4TransferFromBalanceReadMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd1326⟩ := RD.amm4MappingHashSuffix rd1313 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromBalanceStoreMem,
      amm4TransferFromBalanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (amm4TransferFromFromWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1328 := evm_run rd1326 with [dup2, swap1]
  obtain ⟨_, _, rd1329⟩ := rd1328.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [amm4TransferFromEvmBalanceMap] using
    (evm_run rd1329 with [pop])⟩

theorem amm4TransferFromX_toBalance_load {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1393⟩
      [solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
        (amm4TransferFromToSlot I), amm4TransferFromValueWord I,
        ⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromToReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd1330⟩ := amm4TransferFromX_balance_stored hperm hcanonFrom hmem
    hle hreach
  have htoClean : UInt256.land solcAddrMask (amm4TransferFromToWord I) =
      amm4TransferFromToWord I := solcAddrMask_clean_left hcanonTo
  have rd1379₀ := evm_run rd1330 with [
    dup2, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1379 := rd1379₀
  rw [htoClean, htoClean] at rd1379
  have hmem2 : (amm4TransferFromBalanceStoreMem I mem).size = 96 := by
    unfold amm4TransferFromBalanceStoreMem amm4TransferFromBalanceReadMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd1392⟩ := RD.amm4MappingHashSuffix rd1379 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromToReadMem,
      amm4TransferFromToSlot_eq_solc I hcanonTo] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (amm4TransferFromToWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1393⟩ := rd1392.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1393⟩

theorem amm4TransferFromX_credit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
      (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1402⟩
      [solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I (amm4TransferFromToSlot I) +
        amm4TransferFromValueWord I, ⟨0⟩, amm4TransferFromValueWord I,
        amm4TransferFromToWord I, amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromToReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd1393⟩ := amm4TransferFromX_toBalance_load hperm hcanonFrom
    hcanonTo hmem hle hreach
  have rd5304 := evm_run rd1393 with [
    push2 ⟨1402⟩, swap2, swap1, push2 ⟨5304⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedAddOk rd5304 hfit (by jump_dest) (by evm_ov)

theorem amm4TransferFromX_overflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hover : UInt256.size ≤ (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
      (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1393⟩ := amm4TransferFromX_toBalance_load hperm hcanonFrom
    hcanonTo hmem hle hreach
  have rd5304 := evm_run rd1393 with [
    push2 ⟨1402⟩, swap2, swap1, push2 ⟨5304⟩, jump (by jump_dest) ]
  exact RD.amm4CheckedAddOverflow rd5304 hover (by evm_ov)

theorem amm4TransferFromX_toBalance_stored {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
      (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1468⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      (amm4TransferFromToStoreMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, amm4TransferFromEvmPostMap σA I) k C := by
  obtain ⟨_, _, rd1402⟩ := amm4TransferFromX_credit hperm hcanonFrom hcanonTo
    hmem hle hfit hreach
  have htoClean : UInt256.land solcAddrMask (amm4TransferFromToWord I) =
      amm4TransferFromToWord I := solcAddrMask_clean_left hcanonTo
  have rd1451₀ := evm_run rd1402 with [
    jumpdest, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1451 := rd1451₀
  rw [htoClean, htoClean] at rd1451
  have hmem2 : (amm4TransferFromToReadMem I mem).size = 96 := by
    unfold amm4TransferFromToReadMem amm4TransferFromBalanceStoreMem
      amm4TransferFromBalanceReadMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd1464⟩ := RD.amm4MappingHashSuffix rd1451 amm4_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [amm4TransferFromToStoreMem,
      amm4TransferFromToSlot_eq_solc I hcanonTo] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (amm4TransferFromToWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1466 := evm_run rd1464 with [dup2, swap1]
  obtain ⟨_, _, rd1467⟩ := rd1466.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [amm4TransferFromEvmPostMap] using
    (evm_run rd1467 with [pop])⟩

theorem amm4TransferFromToStoreMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) : (amm4TransferFromToStoreMem I mem).size = 96 := by
  unfold amm4TransferFromToStoreMem amm4TransferFromToReadMem
    amm4TransferFromBalanceStoreMem amm4TransferFromBalanceReadMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ hmem

theorem amm4TransferFromToStoreMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (amm4TransferFromToStoreMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4TransferFromToStoreMem amm4TransferFromToReadMem
    amm4TransferFromBalanceStoreMem amm4TransferFromBalanceReadMem
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ hmem)))
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ hmem))
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ hmem)
  exact twoWordHashMem_read64 _ _ hmem hread

theorem amm4X_transferFrom_tail {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
      (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDret amm4Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, amm4TransferFromEvmPostMap σA I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd1468⟩ := amm4TransferFromX_toBalance_stored hperm hcanonFrom
    hcanonTo hmem hle hfit hreach
  have rd253 := evm_run rd1468 with [
    push1 ⟨1⟩, swap1, pop, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have hmemFinal := amm4TransferFromToStoreMem_size I hmem
  have hreadFinal := amm4TransferFromToStoreMem_read64 I hmem hread
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (amm4TransferFromToStoreMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((amm4TransferFromToStoreMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmemFinal]; decide) (by decide) hreadFinal
  have rd4816 := evm_run rd253 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨266⟩, swap2, swap1, push2 ⟨4816⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd266⟩ := RD.amm4RoutineEncodeBoolFromMem
    (memout := amm4WordReturnMem (amm4TransferFromToStoreMem I mem) (⟨1⟩ : UInt256))
    rd4816 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd266 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (amm4WordReturnMem_mload64_of_size96 ⟨1⟩ hmemFinal hreadFinal)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact amm4WordReturnMem_read128_of_size96 ⟨1⟩ hmemFinal)
      (by evm_ov) ]

theorem amm4TransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using (solcCalldataStaticLenCheckShort (words := 3)
      (sz := I.calldata.size) hsz4 (by omega) hsize (by norm_num))
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨4904⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨4903⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4TransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using (solcCalldataStaticLenCheckHuge (words := 3)
      (sz := I.calldata.size) hbig hsize (by norm_num))
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨4904⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨4903⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4TransferFromX_noncanonFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (amm4TransferFromFromWord I)
      (UInt256.land (amm4TransferFromFromWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4657_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4TransferFromX_noncanonTo {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (amm4TransferFromToWord I)
      (UInt256.land (amm4TransferFromToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4TransferFromX_dec4657_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.amm4DecodeAddrRevert rd hnc (by evm_ov)

theorem amm4TransferFromSelector_size {I : ExecutionEnv}
    (hsel : amm4SelIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem amm4Dispatch_transferFrom {cd : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferFromTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition, swapTransition,
      totalSupplyTransition, transferTransition])
    (post := [])
    rfl rfl ?_ (by rw [selectorOf, amm4TransferFromSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, amm4AllowanceSelectorBytes, hcd]
    | rw [selectorOf, amm4ApproveSelectorBytes, hcd]
    | rw [selectorOf, amm4BalanceOfSelectorBytes, hcd]
    | rw [selectorOf, amm4BurnSelectorBytes, hcd]
    | rw [selectorOf, amm4MintSelectorBytes, hcd]
    | rw [selectorOf, amm4SwapSelectorBytes, hcd]
    | rw [selectorOf, amm4TotalSupplySelectorBytes, hcd]
    | rw [selectorOf, amm4TransferSelectorBytes, hcd]
  all_goals decide

theorem amm4TransferFromFromWord_eq_source_iff (I : ExecutionEnv)
    (hcanon : (amm4TransferFromFromWord I).toNat < EVM.addressModulus) :
    amm4TransferFromFromWord I = solcSourceWord I ↔
      AccountAddress.ofNat (amm4TransferFromFromWord I).toNat = I.source := by
  constructor
  · intro h
    rw [h]
    exact solcSource_ofNat I
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    change (amm4TransferFromFromWord I).toNat % AccountAddress.size = I.source.val at hv
    have hcanon' : (amm4TransferFromFromWord I).toNat < AccountAddress.size := hcanon
    rw [Nat.mod_eq_of_lt hcanon'] at hv
    rw [solcSourceWord_toNat]
    exact hv

theorem amm4TransferFromMaxWord_toNat :
    amm4TransferFromMaxWord.toNat = Int.toNat maxUint256 := by
  native_decide

theorem amm4TransferFromAllowanceValue_eq_max_iff (w : UInt256) :
    Value.int (Int.ofNat w.toNat) = .int maxUint256 ↔
      w = amm4TransferFromMaxWord := by
  constructor
  · intro h
    have hnat : w.toNat = amm4TransferFromMaxWord.toNat := by
      have hi : Int.ofNat w.toNat = maxUint256 := by
        injection h with hi
      rw [amm4TransferFromMaxWord_toNat]
      exact congrArg Int.toNat hi
    exact u256_inj hnat
  · intro h
    rw [h]
    native_decide

theorem amm4TransferFromShouldSpend_iff (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (amm4TransferFromFromWord I).toNat < EVM.addressModulus) :
    amm4TransferFromShouldSpend evm I = true ↔
      amm4TransferFromFromWord I ≠ solcSourceWord I ∧
        amm4TransferFromAllowanceWord evm I ≠ amm4TransferFromMaxWord := by
  rw [amm4TransferFromShouldSpend]
  simp only [Bool.and_eq_true, Bool.not_eq_true]
  constructor
  · rintro ⟨hfrom, hallow⟩
    constructor
    · intro he
      have hv := (amm4TransferFromFromWord_eq_source_iff I hcanon).mp he
      simp [amm4TransferFromFromValue, BEq.beq, hv] at hfrom
    · intro he
      have hv := (amm4TransferFromAllowanceValue_eq_max_iff _).mpr he
      have hi : Int.ofNat (amm4TransferFromAllowanceWord evm I).toNat =
          maxUint256 := by injection hv with hi
      simp [BEq.beq] at hallow
      exact hallow hi
  · rintro ⟨hfrom, hallow⟩
    constructor
    · have hv : AccountAddress.ofNat (amm4TransferFromFromWord I).toNat ≠
          I.source := fun he => hfrom ((amm4TransferFromFromWord_eq_source_iff I hcanon).mpr he)
      simp [amm4TransferFromFromValue, BEq.beq, hv]
    · have hv : Value.int (Int.ofNat (amm4TransferFromAllowanceWord evm I).toNat) ≠
          .int maxUint256 := fun he => hallow ((amm4TransferFromAllowanceValue_eq_max_iff _).mp he)
      simp [BEq.beq]
      intro hi
      exact hv (congrArg Value.int hi)

theorem amm4TransferFromAllowanceMem_size (I : ExecutionEnv) :
    (amm4TransferFromAllowanceMem I).size = 96 := by
  unfold amm4TransferFromAllowanceMem amm4TransferFromAllowanceOuterMem
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size

theorem amm4TransferFromAllowanceMem_read64 (I : ExecutionEnv) :
    (amm4TransferFromAllowanceMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold amm4TransferFromAllowanceMem amm4TransferFromAllowanceOuterMem
  apply twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem amm4TransferFromAllowanceStoreMem_size (I : ExecutionEnv) :
    (amm4TransferFromAllowanceStoreMem I).size = 96 := by
  unfold amm4TransferFromAllowanceStoreMem amm4TransferFromAllowanceStoreOuterMem
    amm4TransferFromAllowanceReadMem amm4TransferFromAllowanceReadOuterMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ (amm4TransferFromAllowanceMem_size I)

theorem amm4TransferFromAllowanceStoreMem_read64 (I : ExecutionEnv) :
    (amm4TransferFromAllowanceStoreMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [amm4TransferFromAllowanceStoreMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold amm4TransferFromAllowanceStoreOuterMem
    apply twoWordHashMem_size_96
    unfold amm4TransferFromAllowanceReadMem amm4TransferFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (amm4TransferFromAllowanceMem_size I))
  rw [amm4TransferFromAllowanceStoreOuterMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold amm4TransferFromAllowanceReadMem amm4TransferFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (amm4TransferFromAllowanceMem_size I))
  rw [amm4TransferFromAllowanceReadMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold amm4TransferFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ (amm4TransferFromAllowanceMem_size I))
  rw [amm4TransferFromAllowanceReadOuterMem]
  exact twoWordHashMem_read64 _ _ (amm4TransferFromAllowanceMem_size I)
    (amm4TransferFromAllowanceMem_read64 I)

theorem amm4TransferFromTailCore
    {cA gh bl σ_evm σ_solm σ₀ σA A I} {g : UInt256} {mem : ByteArray}
    (hcode : I.code = amm4Bytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hd : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdec : decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (amm4TransferFromStore I))
    (hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus)
    (hallow : amm4TransferFromShouldSpend
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = true →
      (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromAllowanceWord
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hState : EVMStateEquiv
      (amm4TransferFromAfterAllowance
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
      (amm4TransferFromAfterAllowance
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I))
    (hmapA : (amm4TransferFromAfterAllowance
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap = σA)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1191⟩
      [⟨0⟩, amm4TransferFromValueWord I, amm4TransferFromToWord I,
        amm4TransferFromFromWord I, ⟨253⟩, amm4SelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσA : EVMStateEquiv (amm4TransferFromAfterAllowance evmE I)
      (amm4TransferFromAfterAllowance evmS I) := hState
  have hmapA' : (amm4TransferFromAfterAllowance evmE I).accountMap = σA := hmapA
  have hbalanceE :
      amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmE I) I =
        solcSlotWord σA I (amm4TransferFromBalanceSlot I) := by
    unfold amm4TransferFromBalanceWord
    rw [amm4TransferFromAfterAllowance_codeOwner evmE I,
      show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
    simp only [Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWord, hmapA']
  have hbalanceS :
      amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmS I) I =
        solcSlotWord σA I (amm4TransferFromBalanceSlot I) := by
    rw [show amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmS I) I =
        amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmE I) I from
          (hσA.storageLoad_codeOwner (amm4TransferFromBalanceSlot I)).symm, hbalanceE]
  by_cases hle : (amm4TransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat
  · have hleE : (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmE I) I).toNat :=
      hbalanceE ▸ hle
    have hleS : (amm4TransferFromValueWord I).toNat ≤
        (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmS I) I).toNat :=
      hbalanceS ▸ hle
    have hdebit : amm4TransferFromBalanceDebitWord evmE I =
        amm4TransferFromBalanceDebitWord evmS I := by
      unfold amm4TransferFromBalanceDebitWord
      rw [hbalanceE, hbalanceS]
    have hσBalance : EVMStateEquiv
        (amm4TransferFromAfterBalance evmE I) (amm4TransferFromAfterBalance evmS I) := by
      unfold amm4TransferFromAfterBalance
      rw [← amm4TransferFromAfterAllowance_codeOwner evmE I,
        ← amm4TransferFromAfterAllowance_codeOwner evmS I]
      exact hσA.storageStore_codeOwner (amm4TransferFromBalanceSlot I) hdebit
    have hmapBalance : (amm4TransferFromAfterBalance evmE I).accountMap =
        amm4TransferFromEvmBalanceMap σA I := by
      unfold amm4TransferFromAfterBalance amm4TransferFromEvmBalanceMap
      rw [storageStore_accountMap,
        show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
        hmapA']
      apply congrArg (sstoreAccountMap I.codeOwner σA (amm4TransferFromBalanceSlot I))
      apply u256_inj
      rw [amm4TransferFromBalanceDebitWord_toNat evmE I,
        hbalanceE, usub_toNat hle]
    have htoE : amm4TransferFromToBalanceWord evmE I =
        solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
          (amm4TransferFromToSlot I) := by
      unfold amm4TransferFromToBalanceWord
      rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
      simp only [Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, solcSlotWord, hmapBalance]
    have htoS : amm4TransferFromToBalanceWord evmS I =
        solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
          (amm4TransferFromToSlot I) := by
      rw [show amm4TransferFromToBalanceWord evmS I =
          amm4TransferFromToBalanceWord evmE I from by
            unfold amm4TransferFromToBalanceWord
            rw [← amm4TransferFromAfterBalance_codeOwner evmE I,
              ← amm4TransferFromAfterBalance_codeOwner evmS I]
            exact (hσBalance.storageLoad_codeOwner (amm4TransferFromToSlot I)).symm,
        htoE]
    have hnewE : amm4TransferFromNewToNat evmE I =
        (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
          (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat := by
      rw [amm4TransferFromNewToNat, htoE]
    have hnewS : amm4TransferFromNewToNat evmS I =
        (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
          (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat := by
      rw [amm4TransferFromNewToNat, htoS]
    by_cases hfit : (solcSlotWord (amm4TransferFromEvmBalanceMap σA I) I
        (amm4TransferFromToSlot I)).toNat + (amm4TransferFromValueWord I).toNat <
        UInt256.size
    · have hfitE : amm4TransferFromNewToNat evmE I < UInt256.size :=
        hnewE ▸ hfit
      have hfitS : amm4TransferFromNewToNat evmS I < UInt256.size :=
        hnewS ▸ hfit
      have hnewWord : amm4TransferFromNewToWord evmE I =
          amm4TransferFromNewToWord evmS I := by
        unfold amm4TransferFromNewToWord
        rw [hnewE, hnewS]
      have hσPost : EVMStateEquiv
          (amm4TransferFromPostState evmE I) (amm4TransferFromPostState evmS I) := by
        change EVMStateEquiv
          (Solm.EVM.storageStore (amm4TransferFromAfterBalance evmE I)
            evmE.executionEnv.codeOwner (amm4TransferFromToSlot I)
            (amm4TransferFromNewToWord evmE I))
          (Solm.EVM.storageStore (amm4TransferFromAfterBalance evmS I)
            evmS.executionEnv.codeOwner (amm4TransferFromToSlot I)
            (amm4TransferFromNewToWord evmS I))
        exact hσBalance.storageStore rfl (amm4TransferFromToSlot I) hnewWord
      have hmapPost : (amm4TransferFromPostState evmE I).accountMap =
          amm4TransferFromEvmPostMap σA I := by
        unfold amm4TransferFromPostState amm4TransferFromEvmPostMap
        rw [storageStore_accountMap,
          show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
          hmapBalance]
        apply congrArg (sstoreAccountMap I.codeOwner
          (amm4TransferFromEvmBalanceMap σA I) (amm4TransferFromToSlot I))
        apply u256_inj
        rw [amm4TransferFromNewToWord_toNat evmE I hfitE, uadd_toNat,
          hnewE, Nat.mod_eq_of_lt hfit]
      have hbody := amm4TransferFromBodyReturns evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hfitS
      have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
          (some [(.bool true)]) transferFromTransition.returnType :=
        returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
      exact (amm4X_transferFrom_tail (g := Sat256.ofUInt256 g)
          hperm hcanonFrom hcanonTo hmem hread hle hfit hreach)
        |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
          (by
            have hcreatedA : (amm4TransferFromAfterAllowance evmE I).createdAccounts =
                cA := by
              unfold amm4TransferFromAfterAllowance
              split
              · simp [storageStore_createdAccounts, evmE, initState]
              · rfl
            rw [amm4TransferFromPostState, storageStore_createdAccounts,
              amm4TransferFromAfterBalance, storageStore_createdAccounts, hcreatedA])
          (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
    · have hover : UInt256.size ≤ amm4TransferFromNewToNat evmS I := by
        rw [hnewS]
        omega
      have hbody := amm4TransferFromBodyReverts_credit evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hover
      exact (amm4TransferFromX_overflow (g := Sat256.ofUInt256 g)
          hperm hcanonFrom hcanonTo hmem hle (by omega) hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hunder : (solcSlotWord σA I (amm4TransferFromBalanceSlot I)).toNat <
        (amm4TransferFromValueWord I).toNat := by omega
    have hunderS :
        (amm4TransferFromBalanceWord (amm4TransferFromAfterAllowance evmS I) I).toNat <
          (amm4TransferFromValueWord I).toNat := by rw [hbalanceS]; exact hunder
    have hbody := amm4TransferFromBodyReverts_balance evmS I
      (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hunderS
    exact (amm4TransferFromX_balance_underflow (g := Sat256.ofUInt256 g)
        hcanonFrom hmem hunder hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

/-- The transferFrom wrapper, entered at PC 227, refines its Solm transition. -/
theorem amm4TransferFromBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = amm4Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : amm4SelIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hreach : ∃ k C, RD amm4Bytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨227⟩ [amm4SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := amm4TransferFromSelector_size hsel
  have hd := amm4Dispatch_transferFrom (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (amm4TransferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (amm4TransferFromToWord I).toNat < EVM.addressModulus
        · have hdec := amm4Decode_transferFrom_ok (I := I) hsz100 hbig
            hcanonFrom hcanonTo
          let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hσ : EVMStateEquiv evmE evmS := by
            simpa [evmE, evmS] using
              EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
          have hallowWordE : amm4TransferFromAllowanceWord evmE I =
              solcSlotWord σ_evm I (amm4TransferFromAllowanceSlot I) := by
            simpa [amm4TransferFromAllowanceWord, solcSlotWord,
              codeOwnerStorageWord] using
              (codeOwnerStorageWord_initState
                (g := Sat256.ofUInt256 g) (σ := σ_evm)
                (slot := amm4TransferFromAllowanceSlot I) (cA := cA)
                (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
          have hallowWordS : amm4TransferFromAllowanceWord evmS I =
              solcSlotWord σ_evm I (amm4TransferFromAllowanceSlot I) := by
            rw [show amm4TransferFromAllowanceWord evmS I =
                amm4TransferFromAllowanceWord evmE I from
                  (hσ.storageLoad_codeOwner (amm4TransferFromAllowanceSlot I)).symm,
              hallowWordE]
          by_cases hself : amm4TransferFromFromWord I = solcSourceWord I
          · have hspendE : amm4TransferFromShouldSpend evmE I = false := by
              cases hs : amm4TransferFromShouldSpend evmE I with
              | false => rfl
              | true => exact False.elim (((amm4TransferFromShouldSpend_iff evmE I hcanonFrom).mp hs).1 hself)
            have hspendS : amm4TransferFromShouldSpend evmS I = false := by
              cases hs : amm4TransferFromShouldSpend evmS I with
              | false => rfl
              | true => exact False.elim (((amm4TransferFromShouldSpend_iff evmS I hcanonFrom).mp hs).1 hself)
            have hState : EVMStateEquiv
                (amm4TransferFromAfterAllowance evmE I)
                (amm4TransferFromAfterAllowance evmS I) := by
              simpa [amm4TransferFromAfterAllowance, hspendE, hspendS] using hσ
            have hmapA : (amm4TransferFromAfterAllowance evmE I).accountMap =
                σ_evm := by
              rw [amm4TransferFromAfterAllowance, hspendE]
              rfl
            exact amm4TransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
              hcanonTo (by intro hs; rw [hspendS] at hs; cases hs)
              hState hmapA solcFreePtrMem_size solcFreePtrMem_read64
              (amm4TransferFromX_self_to_balance (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hcanonFrom hcanonTo hself hreach)
          · by_cases hmax : solcSlotWord σ_evm I (amm4TransferFromAllowanceSlot I) =
                amm4TransferFromMaxWord
            · have hspendE : amm4TransferFromShouldSpend evmE I = false := by
                cases hs : amm4TransferFromShouldSpend evmE I with
                | false => rfl
                | true => exact False.elim (((amm4TransferFromShouldSpend_iff evmE I hcanonFrom).mp hs).2
                    (by rw [hallowWordE]; exact hmax))
              have hspendS : amm4TransferFromShouldSpend evmS I = false := by
                cases hs : amm4TransferFromShouldSpend evmS I with
                | false => rfl
                | true => exact False.elim (((amm4TransferFromShouldSpend_iff evmS I hcanonFrom).mp hs).2
                    (by rw [hallowWordS]; exact hmax))
              have hState : EVMStateEquiv
                  (amm4TransferFromAfterAllowance evmE I)
                  (amm4TransferFromAfterAllowance evmS I) := by
                simpa [amm4TransferFromAfterAllowance, hspendE, hspendS] using hσ
              have hmapA : (amm4TransferFromAfterAllowance evmE I).accountMap =
                  σ_evm := by
                rw [amm4TransferFromAfterAllowance, hspendE]
                rfl
              exact amm4TransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
                hcanonTo (by intro hs; rw [hspendS] at hs; cases hs)
                hState hmapA (amm4TransferFromAllowanceMem_size I)
                (amm4TransferFromAllowanceMem_read64 I)
                (amm4TransferFromX_max_to_balance (g := Sat256.ofUInt256 g)
                  hsz100 hsize hbig hcanonFrom hcanonTo hself hmax hreach)
            · have hspendE : amm4TransferFromShouldSpend evmE I = true :=
                (amm4TransferFromShouldSpend_iff evmE I hcanonFrom).mpr
                  ⟨hself, by rwa [hallowWordE]⟩
              have hspendS : amm4TransferFromShouldSpend evmS I = true :=
                (amm4TransferFromShouldSpend_iff evmS I hcanonFrom).mpr
                  ⟨hself, by rwa [hallowWordS]⟩
              by_cases hle : (amm4TransferFromValueWord I).toNat ≤
                  (solcSlotWord σ_evm I (amm4TransferFromAllowanceSlot I)).toNat
              · have hdebit : amm4TransferFromAllowanceDebitWord evmE I =
                    amm4TransferFromAllowanceDebitWord evmS I := by
                  unfold amm4TransferFromAllowanceDebitWord
                  rw [hallowWordE, hallowWordS]
                have hState : EVMStateEquiv
                    (amm4TransferFromAfterAllowance evmE I)
                    (amm4TransferFromAfterAllowance evmS I) := by
                  simp only [amm4TransferFromAfterAllowance, hspendE, hspendS,
                    if_true]
                  exact hσ.storageStore_codeOwner
                    (amm4TransferFromAllowanceSlot I) hdebit
                have hmapA : (amm4TransferFromAfterAllowance evmE I).accountMap =
                    amm4TransferFromEvmAllowanceMap σ_evm I := by
                  rw [amm4TransferFromAfterAllowance, if_pos hspendE,
                    storageStore_accountMap]
                  change sstoreAccountMap I.codeOwner σ_evm
                    (amm4TransferFromAllowanceSlot I)
                    (amm4TransferFromAllowanceDebitWord evmE I) = _
                  unfold amm4TransferFromEvmAllowanceMap
                  apply congrArg (sstoreAccountMap I.codeOwner σ_evm
                    (amm4TransferFromAllowanceSlot I))
                  apply u256_inj
                  rw [amm4TransferFromAllowanceDebitWord_toNat evmE I,
                    hallowWordE, usub_toNat hle]
                exact amm4TransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
                  hcanonTo (by intro _; rwa [hallowWordS]) hState hmapA
                  (amm4TransferFromAllowanceStoreMem_size I)
                  (amm4TransferFromAllowanceStoreMem_read64 I)
                  (amm4TransferFromX_spend_stored (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonFrom hcanonTo hself hmax hle hreach)
              · have hunder : (solcSlotWord σ_evm I
                    (amm4TransferFromAllowanceSlot I)).toNat <
                    (amm4TransferFromValueWord I).toNat := by omega
                have hbody := amm4TransferFromBodyReverts_allowance evmS I
                  (by simp only [evmS, initState]; exact hwv) (by rfl) hspendS
                  (by rwa [hallowWordS])
                exact (amm4TransferFromX_spend_underflow (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hcanonFrom hcanonTo hself hmax hunder hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := amm4Decode_transferFrom_none_noncanonTo
            (I := I) hsz100 hbig hcanonFrom hcanonTo
          have hnc : UInt256.eq (amm4TransferFromToWord I)
              (UInt256.land (amm4TransferFromToWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonTo (solcAddrCanonical_of_clean he))
          exact (amm4TransferFromX_noncanonTo (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonFrom hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := amm4Decode_transferFrom_none_noncanonFrom
          (I := I) hsz100 hbig hcanonFrom
        have hnc : UInt256.eq (amm4TransferFromFromWord I)
            (UInt256.land (amm4TransferFromFromWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonFrom (solcAddrCanonical_of_clean he))
        exact (amm4TransferFromX_noncanonFrom (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := amm4Decode_transferFrom_none_huge (I := I) hbigge
      exact (amm4TransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := amm4Decode_transferFrom_none_short (I := I) hsz4 hshort
    exact (amm4TransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm4
