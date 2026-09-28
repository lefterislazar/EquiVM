import Benchmarks.ActAmm.Common
import Benchmarks.ActAmm.Transfer
import Benchmarks.ActAmm.Allowance
import Benchmarks.ActAmm.Arithmetic
import Benchmarks.ActAmm.Decode
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Trusted
import Benchmarks.ActAmm.Routines
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000
abbrev ammTransferFromFromWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)
abbrev ammTransferFromToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)
abbrev ammTransferFromValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)
abbrev ammTransferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "from"
    (.address (AccountAddress.ofNat (ammTransferFromFromWord I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (ammTransferFromToWord I).toNat))).insert "value"
    (.int (Int.ofNat (ammTransferFromValueWord I).toNat))
theorem ammDecode_transferFrom_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hfrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hto : (ammTransferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (ammTransferFromStore I) := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, ammTransferFromStore,
    ammTransferFromFromWord, ammTransferFromToWord, ammTransferFromValueWord,
    calldataWord] using
    decodeCalldata_address_address_uint256_ok
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hfrom hto
theorem ammDecode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_address_address_uint256_none_short
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz4 hshort
theorem ammDecode_transferFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_address_address_uint256_none_huge
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hbig
theorem ammDecode_transferFrom_none_noncanonFrom {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammTransferFromFromWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, ammTransferFromFromWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hnc
theorem ammDecode_transferFrom_none_noncanonTo {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hfrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (ammTransferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, ammTransferFromFromWord,
    ammTransferFromToWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hfrom hnc
abbrev ammTransferFromFromValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammTransferFromFromWord I).toNat)
abbrev ammTransferFromToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (ammTransferFromToWord I).toNat)
abbrev ammTransferFromValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (ammTransferFromValueWord I).toNat)

def ammTransferFromAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (ammTransferFromFromWord I).toNat))
    (.address I.source)

def ammTransferFromBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (ammTransferFromFromWord I).toNat))

def ammTransferFromToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (ammTransferFromToWord I).toNat))

theorem ammTransferFromAllowanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammTransferFromFromWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (ammTransferFromFromWord I))
      (solcSourceWord I) = ammTransferFromAllowanceSlot I := by
  unfold ammTransferFromAllowanceSlot allowanceSlot allowanceOwnerSlot mapSlot
    solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon,
    ammSource_keyValueToWord I.source]

theorem ammTransferFromBalanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammTransferFromFromWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (ammTransferFromFromWord I) =
      ammTransferFromBalanceSlot I := by
  unfold ammTransferFromBalanceSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem ammTransferFromToSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammTransferFromToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (ammTransferFromToWord I) =
      ammTransferFromToSlot I := by
  unfold ammTransferFromToSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem ammTransferFromStore_from (I : ExecutionEnv) :
    (ammTransferFromStore I).get? "from" = some (ammTransferFromFromValue I) := by
  rw [ammTransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem ammTransferFromStore_to (I : ExecutionEnv) :
    (ammTransferFromStore I).get? "to" = some (ammTransferFromToValue I) := by
  rw [ammTransferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem ammTransferFromStore_value (I : ExecutionEnv) :
    (ammTransferFromStore I).get? "value" = some (ammTransferFromValueValue I) := by
  rw [ammTransferFromStore, store_get_self]

theorem ammTransferFromStore_allowance (I : ExecutionEnv) :
    (ammTransferFromStore I).get? "allowance" = none := by
  rw [ammTransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem ammTransferFromStore_balance (I : ExecutionEnv) :
    (ammTransferFromStore I).get? "balanceOf" = none := by
  rw [ammTransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def ammTransferFromAllowanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps :=
    [.mindex (.address (AccountAddress.ofNat (ammTransferFromFromWord I).toNat)),
      .mindex (.address I.source)] }

def ammTransferFromBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps :=
    [.mindex (.address (AccountAddress.ofNat (ammTransferFromFromWord I).toNat))] }

def ammTransferFromToRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps :=
    [.mindex (.address (AccountAddress.ofNat (ammTransferFromToWord I).toNat))] }

theorem ammTransferFromEvalAllowanceRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := ammTransferFromStore I } evm
      (allowanceRef (.var "from") sender) = .ok (ammTransferFromAllowanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferFromAllowanceRef, ammTransferFromFromValue,
    ammTransferFromStore_from, sender, envValue, hsrc]

theorem ammTransferFromEvalBalanceRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := ammTransferFromStore I } evm
      (balanceOfRef (.var "from")) = .ok (ammTransferFromBalanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferFromBalanceRef, ammTransferFromFromValue,
    ammTransferFromStore_from]

theorem ammTransferFromEvalToRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := ammTransferFromStore I } evm
      (balanceOfRef (.var "to")) = .ok (ammTransferFromToRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferFromToRef, ammTransferFromToValue,
    ammTransferFromStore_to]

def ammTransferFromAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ammTransferFromAllowanceSlot I)

def ammTransferFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ammTransferFromBalanceSlot I)

theorem ammTransferFromEvalAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.storage (allowanceRef (.var "from") sender)) =
        .ok (.int (Int.ofNat (ammTransferFromAllowanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := ammTransferFromStore_allowance I)
    (her := ammTransferFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [ammTransferFromAllowanceWord, ammTransferFromAllowanceSlot,
    ammStorageLocLoad_uint256]

theorem ammTransferFromEvalBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.storage (balanceOfRef (.var "from"))) =
        .ok (.int (Int.ofNat (ammTransferFromBalanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := ammTransferFromStore_balance I)
    (her := ammTransferFromEvalBalanceRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferFromBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [ammTransferFromBalanceWord, ammTransferFromBalanceSlot,
    ammStorageLocLoad_uint256]

theorem ammTransferFromEvalToBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.storage (balanceOfRef (.var "to"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (ammTransferFromToSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := ammTransferFromStore_balance I)
    (her := ammTransferFromEvalToRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferFromToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [ammTransferFromToSlot, ammStorageLocLoad_uint256]

theorem ammTransferFromEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.var "value") = .ok (ammTransferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, ammTransferFromStore_value]

theorem ammTransferFromEvalFromNeSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.binary .ne (.var "from") sender) =
        .ok (.bool (!(ammTransferFromFromValue I == .address I.source))) := by
  have hfrom : evalExpr? config
      { contract := contract, locals := ammTransferFromStore I } evm (.var "from") =
      .ok (ammTransferFromFromValue I) := by
    simp only [evalExpr?, EvalResult.ofOption, ammTransferFromStore_from]
  have hsender : evalExpr? config
      { contract := contract, locals := ammTransferFromStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hfrom, hsender, evalBinaryOp?]

theorem ammTransferFromEvalAllowanceNeMax (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "from") sender))
        (.intLit maxUint256)) =
      .ok (.bool (!(Value.int (Int.ofNat
        (ammTransferFromAllowanceWord evm I).toNat) == .int maxUint256))) := by
  have hallow := ammTransferFromEvalAllowance evm I hsrc
  simp [evalExpr?, EvalResult.bind, bind, hallow, evalBinaryOp?]

theorem ammTransferFromEvalCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) =
      .ok (.bool ((!(ammTransferFromFromValue I == .address I.source)) &&
        (!(Value.int (Int.ofNat (ammTransferFromAllowanceWord evm I).toNat) ==
          .int maxUint256)))) := by
  rw [evalExpr?]
  rw [ammTransferFromEvalFromNeSender evm I hsrc]
  simp only [EvalResult.bind, bind]
  cases hleft : (!(ammTransferFromFromValue I == .address I.source))
  · simp [pure]
  · rw [ammTransferFromEvalAllowanceNeMax evm I hsrc]
    simp [pure]

def ammTransferFromShouldSpend (evm : EVM.State) (I : ExecutionEnv) : Bool :=
  (!(ammTransferFromFromValue I == .address I.source)) &&
    (!(Value.int (Int.ofNat (ammTransferFromAllowanceWord evm I).toNat) ==
      .int maxUint256))

theorem ammTransferFromEvalCond' (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) =
      .ok (.bool (ammTransferFromShouldSpend evm I)) := by
  exact ammTransferFromEvalCond evm I hsrc

def ammTransferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((ammTransferFromAllowanceWord evm I).toNat -
    (ammTransferFromValueWord I).toNat)

def ammTransferFromAfterAllowance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if ammTransferFromShouldSpend evm I then
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (ammTransferFromAllowanceSlot I) (ammTransferFromAllowanceDebitWord evm I)
  else evm

def ammTransferFromBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat -
    (ammTransferFromValueWord I).toNat)

def ammTransferFromAfterBalance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (ammTransferFromAfterAllowance evm I) evm.executionEnv.codeOwner
    (ammTransferFromBalanceSlot I) (ammTransferFromBalanceDebitWord evm I)

def ammTransferFromToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (ammTransferFromAfterBalance evm I) evm.executionEnv.codeOwner
    (ammTransferFromToSlot I)

def ammTransferFromNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (ammTransferFromToBalanceWord evm I).toNat + (ammTransferFromValueWord I).toNat

def ammTransferFromNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (ammTransferFromNewToNat evm I)

def ammTransferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (ammTransferFromAfterBalance evm I) evm.executionEnv.codeOwner
    (ammTransferFromToSlot I) (ammTransferFromNewToWord evm I)

theorem ammTransferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferFromAfterAllowance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  unfold ammTransferFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem ammTransferFromAfterAllowance_source (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferFromAfterAllowance evm I).executionEnv.source =
      evm.executionEnv.source := by
  unfold ammTransferFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem ammTransferFromAfterBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferFromAfterBalance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [ammTransferFromAfterBalance, storageStore_executionEnv,
    ammTransferFromAfterAllowance_codeOwner]

theorem ammTransferFromAllowanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferFromAllowanceDebitWord evm I).toNat =
      (ammTransferFromAllowanceWord evm I).toNat -
        (ammTransferFromValueWord I).toNat := by
  unfold ammTransferFromAllowanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (ammTransferFromAllowanceWord evm I).val.isLt

theorem ammTransferFromBalanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (ammTransferFromBalanceDebitWord evm I).toNat =
      (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat -
        (ammTransferFromValueWord I).toNat := by
  unfold ammTransferFromBalanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _)
    (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).val.isLt

theorem ammTransferFromEvalAllowanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (ammTransferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) =
        .ok (.int (Int.ofNat ((ammTransferFromAllowanceWord evm I).toNat -
          (ammTransferFromValueWord I).toNat))) := by
  exact ammEvalCheckedSub_ok (ammTransferFromEvalAllowance evm I hsrc)
    (ammTransferFromEvalValue evm I) hle (ammTransferFromAllowanceWord evm I).val.isLt

theorem ammTransferFromEvalAllowanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (ammTransferFromAllowanceWord evm I).toNat <
      (ammTransferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I } evm
      (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) =
        .revert := by
  exact ammEvalCheckedSub_revert (ammTransferFromEvalAllowance evm I hsrc)
    (ammTransferFromEvalValue evm I) hunder

theorem ammTransferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := ammTransferFromStore I } evm
      .storage (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (ammTransferFromAllowanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := ammTransferFromStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (ammTransferFromAllowanceSlot I) (ammTransferFromAllowanceDebitWord evm I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := ammTransferFromStore_allowance I)
    (her := ammTransferFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [ammTransferFromAllowanceSlot] using
    ammStorageLocStore_uint256 evm (ammTransferFromAllowanceSlot I)
      (ammTransferFromAllowanceDebitWord evm I)

theorem ammTransferFromEvalBalanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I }
      (ammTransferFromAfterAllowance evm I)
      (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .ok (.int (Int.ofNat
          ((ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat -
            (ammTransferFromValueWord I).toNat))) := by
  exact ammEvalCheckedSub_ok
    (ammTransferFromEvalBalance (ammTransferFromAfterAllowance evm I) I)
    (ammTransferFromEvalValue (ammTransferFromAfterAllowance evm I) I) hle
    (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).val.isLt

theorem ammTransferFromEvalBalanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hunder : (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat <
      (ammTransferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I }
      (ammTransferFromAfterAllowance evm I)
      (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .revert := by
  exact ammEvalCheckedSub_revert
    (ammTransferFromEvalBalance (ammTransferFromAfterAllowance evm I) I)
    (ammTransferFromEvalValue (ammTransferFromAfterAllowance evm I) I) hunder

theorem ammTransferFromAssignBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := ammTransferFromStore I }
      (ammTransferFromAfterAllowance evm I)
      .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat (ammTransferFromBalanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := ammTransferFromStore I },
        ammTransferFromAfterBalance evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := ammTransferFromStore_balance I)
    (her := ammTransferFromEvalBalanceRef (ammTransferFromAfterAllowance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferFromBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [ammTransferFromAfterBalance, ammTransferFromBalanceSlot,
    ammTransferFromAfterAllowance_codeOwner evm I] using
    ammStorageLocStore_uint256 (ammTransferFromAfterAllowance evm I)
      (ammTransferFromBalanceSlot I) (ammTransferFromBalanceDebitWord evm I)

theorem ammTransferFromNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferFromNewToNat evm I < UInt256.size) :
    (ammTransferFromNewToWord evm I).toNat = ammTransferFromNewToNat evm I := by
  unfold ammTransferFromNewToWord
  exact ulit_toNat' _ hfit

theorem ammTransferFromEvalCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferFromNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I }
      (ammTransferFromAfterBalance evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .ok (.int (Int.ofNat (ammTransferFromNewToNat evm I))) := by
  have hload := ammTransferFromEvalToBalance (ammTransferFromAfterBalance evm I) I
  rw [ammTransferFromAfterBalance_codeOwner evm I] at hload
  exact ammEvalCheckedAdd_ok hload
    (ammTransferFromEvalValue (ammTransferFromAfterBalance evm I) I) hfit

theorem ammTransferFromEvalCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ ammTransferFromNewToNat evm I) :
    evalExpr? config { contract := contract, locals := ammTransferFromStore I }
      (ammTransferFromAfterBalance evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .revert := by
  have hload := ammTransferFromEvalToBalance (ammTransferFromAfterBalance evm I) I
  rw [ammTransferFromAfterBalance_codeOwner evm I] at hload
  exact ammEvalCheckedAdd_revert hload
    (ammTransferFromEvalValue (ammTransferFromAfterBalance evm I) I) hover

theorem ammTransferFromAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : ammTransferFromNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := ammTransferFromStore I }
      (ammTransferFromAfterBalance evm I) .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat (ammTransferFromNewToNat evm I))) =
      .ok ({ contract := contract, locals := ammTransferFromStore I },
        ammTransferFromPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := ammTransferFromStore_balance I)
    (her := ammTransferFromEvalToRef (ammTransferFromAfterBalance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      ammTransferFromToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [ammTransferFromPostState, ammTransferFromAfterBalance_codeOwner evm I,
    ammTransferFromToSlot, ammTransferFromNewToWord_toNat evm I hfit] using
    ammStorageLocStore_uint256 (ammTransferFromAfterBalance evm I)
      (ammTransferFromToSlot I) (ammTransferFromNewToWord evm I)

theorem ammTransferFromAllowanceStep_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : ammTransferFromShouldSpend evm I = true →
      (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromAllowanceWord evm I).toNat) :
    ExecStmt config { contract := contract, locals := ammTransferFromStore I } evm
      (.ite
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256)))
        [.assign .storage (allowanceRef (.var "from") sender)
          (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value"))] [])
      (.ok { contract := contract, locals := ammTransferFromStore I }
        (ammTransferFromAfterAllowance evm I)) := by
  by_cases hspend : ammTransferFromShouldSpend evm I = true
  · have hcond : evalExpr? config
        { contract := contract, locals := ammTransferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256))) = .ok (.bool true) := by
      rw [ammTransferFromEvalCond' evm I hsrc, hspend]
    have hassign := ammTransferFromAssignAllowance evm I hsrc
    rw [ammTransferFromAllowanceDebitWord_toNat evm I] at hassign
    have hthen : ExecBlock config { contract := contract, locals := ammTransferFromStore I }
        evm [.assign .storage (allowanceRef (.var "from") sender)
          (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value"))]
        (.ok { contract := contract, locals := ammTransferFromStore I }
          (ammTransferFromAfterAllowance evm I)) := by
      simpa [ammTransferFromAfterAllowance, hspend] using
        (ExecBlock.consNormal
          (ExecStmt.assign
            (ammTransferFromEvalAllowanceDebit_ok evm I hsrc (hle hspend)) hassign)
          ExecBlock.nil)
    exact ExecStmt.iteTrue hcond hthen
  · have hfalse : ammTransferFromShouldSpend evm I = false := by
      cases h : ammTransferFromShouldSpend evm I <;> simp_all
    have hcond : evalExpr? config
        { contract := contract, locals := ammTransferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256))) = .ok (.bool false) := by
      rw [ammTransferFromEvalCond' evm I hsrc, hfalse]
    simpa [ammTransferFromAfterAllowance, hfalse] using
      (ExecStmt.iteFalse hcond (ExecBlock.nil :
        ExecBlock config { contract := contract, locals := ammTransferFromStore I }
          evm [] (.ok { contract := contract, locals := ammTransferFromStore I } evm)))

theorem ammTransferFromBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : ammTransferFromShouldSpend evm I = true →
      (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromAllowanceWord evm I).toNat)
    (hbalance : (ammTransferFromValueWord I).toNat ≤
      (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat)
    (hfit : ammTransferFromNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (ammTransferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := ammTransferFromStore I }
        (ammTransferFromPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ammTransferFromAllowanceStep_ok evm I hsrc hallow) ?_
  have hassign := ammTransferFromAssignBalance evm I
  rw [ammTransferFromBalanceDebitWord_toNat evm I] at hassign
  refine ExecBlock.consNormal
    (ExecStmt.assign (ammTransferFromEvalBalanceDebit_ok evm I hbalance) hassign) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (ammTransferFromEvalCredit_ok evm I hfit)
      (ammTransferFromAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem ammTransferFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hspend : ammTransferFromShouldSpend evm I = true)
    (hunder : (ammTransferFromAllowanceWord evm I).toNat <
      (ammTransferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (ammTransferFromStore I)
      transferFromTransition.body .reverted := by
  have hcond : evalExpr? config
      { contract := contract, locals := ammTransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) = .ok (.bool true) := by
    rw [ammTransferFromEvalCond' evm I hsrc, hspend]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.iteTrue hcond <|
        ExecBlock.consRevert (ExecStmt.assignExprRevert
          (ammTransferFromEvalAllowanceDebit_revert evm I hsrc hunder)))

theorem ammTransferFromBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : ammTransferFromShouldSpend evm I = true →
      (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromAllowanceWord evm I).toNat)
    (hunder : (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat <
      (ammTransferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (ammTransferFromStore I)
      transferFromTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ammTransferFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (ammTransferFromEvalBalanceDebit_revert evm I hunder))

theorem ammTransferFromBodyReverts_credit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : ammTransferFromShouldSpend evm I = true →
      (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromAllowanceWord evm I).toNat)
    (hbalance : (ammTransferFromValueWord I).toNat ≤
      (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evm I) I).toNat)
    (hover : UInt256.size ≤ ammTransferFromNewToNat evm I) :
    ExecTransitionBody config contract evm (ammTransferFromStore I)
      transferFromTransition.body .reverted := by
  have hassign := ammTransferFromAssignBalance evm I
  rw [ammTransferFromBalanceDebitWord_toNat evm I] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ammTransferFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consNormal
          (ExecStmt.assign (ammTransferFromEvalBalanceDebit_ok evm I hbalance) hassign) <|
          ExecBlock.consRevert
            (ExecStmt.assignExprRevert (ammTransferFromEvalCredit_revert evm I hover))

theorem ammTransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5756⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨287⟩, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨292⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨287⟩, swap2, swap1, push2 ⟨5756⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammTransferFromX_dec5470_from {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5792⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨287⟩, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    simpa using (solcCalldataStaticLenCheckOk (words := 3)
      (sz := I.calldata.size) (by omega) hszhi hsize)
  obtain ⟨_, _, rd⟩ := ammTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨5779⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5792⟩, dup7, dup3, dup8, add, push2 ⟨5470⟩,
    jump (by jump_dest) ]⟩

theorem ammTransferFromX_dec5792 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5792⟩
      [ammTransferFromFromWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨287⟩, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5470_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.ammDecodeAddrOk rd hcanonFrom (by jump_dest) (by evm_ov)

theorem ammTransferFromX_dec5470_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5809⟩, ⟨32⟩,
        ⟨0⟩, ⟨0⟩, ammTransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨287⟩, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5792 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨5809⟩,
    dup7, dup3, dup8, add, push2 ⟨5470⟩, jump (by jump_dest) ]⟩

theorem ammTransferFromX_dec5809 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5809⟩
      [ammTransferFromToWord I, ⟨32⟩, ⟨0⟩, ⟨0⟩,
        ammTransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨287⟩, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5470_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.ammDecodeAddrOk rd hcanonTo (by jump_dest) (by evm_ov)

theorem ammTransferFromX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5521⟩
      [⟨4⟩ + ⟨64⟩, UInt256.ofNat I.calldata.size, ⟨5826⟩, ⟨64⟩,
        ⟨0⟩, ammTransferFromToWord I, ammTransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨287⟩, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5809 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨5826⟩,
    dup7, dup3, dup8, add, push2 ⟨5521⟩, jump (by jump_dest) ]⟩

theorem ammTransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1801⟩
      [ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5521_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  obtain ⟨_, _, rd5826⟩ := RD.ammDecodeUint256Ok rd (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5826 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, pop, swap3,
    jump (by jump_dest), jumpdest, push2 ⟨1801⟩, jump (by jump_dest) ]⟩

theorem ammTransferFromX_self_to_balance {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hself : ammTransferFromFromWord I = solcSourceWord I)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1801⟩ := ammTransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (ammTransferFromFromWord I) =
      ammTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd1851₀ := evm_run rd1801 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup5, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd1851 := rd1851₀
  rw [hsourceClean, hfromClean, hself] at rd1851
  have hzero : UInt256.isZero (UInt256.eq (solcSourceWord I) (solcSourceWord I)) =
      ⟨0⟩ := by rw [uInt256_eq_self]; decide
  rw [hzero] at rd1851
  have rd2276 := evm_run rd1851 with [
    iszero, push2 ⟨2014⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, iszero, push2 ⟨2276⟩, jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, by simpa [hself] using rd2276⟩

def ammTransferFromAllowanceOuterSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨2⟩ (ammTransferFromFromWord I)

noncomputable def ammTransferFromAllowanceOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (ammTransferFromFromWord I) ⟨2⟩ solcFreePtrMem

noncomputable def ammTransferFromAllowanceMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (ammTransferFromAllowanceOuterSlot I)
    (ammTransferFromAllowanceOuterMem I)

def ammTransferFromMaxWord : UInt256 :=
  ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩

theorem ammTransferFromX_nonself_allowanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2012⟩
      [solcSlotWord σ I (ammTransferFromAllowanceSlot I), ammTransferFromMaxWord,
        ⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1801⟩ := ammTransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (ammTransferFromFromWord I) =
      ammTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hneqWord : UInt256.eq (ammTransferFromFromWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hne (uInt256_eq_one_eq he))
  have rd1851₀ := evm_run rd1801 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup5, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd1851 := rd1851₀
  rw [hsourceClean, hfromClean, hneqWord] at rd1851
  have rd1858 := evm_run rd1851 with [
    iszero, push2 ⟨2014⟩, jumpiNT (by decide),
    pop ]
  have rd1891 := rd1858.pushConst ammTransferFromMaxWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1939₀ := evm_run rd1891 with [
    push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1939 := rd1939₀
  rw [hfromClean, hfromClean] at rd1939
  obtain ⟨_, _, rd1952⟩ := RD.ammMappingHashSuffix rd1939 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromAllowanceOuterMem,
      ammTransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (ammTransferFromFromWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1939'₀ := evm_run rd1952 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1939' := rd1939'₀
  rw [hsourceClean, hsourceClean] at rd1939'
  have hmem : (ammTransferFromAllowanceOuterMem I).size = 96 := by
    unfold ammTransferFromAllowanceOuterMem
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2011⟩ := RD.ammMappingHashSuffix rd1939' amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromAllowanceMem,
      ammTransferFromAllowanceOuterSlot,
      ammTransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (ammTransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2012⟩ := rd2011.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2012⟩

theorem ammTransferFromX_max_to_balance {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hmax : solcSlotWord σ I (ammTransferFromAllowanceSlot I) =
      ammTransferFromMaxWord)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2012₀⟩ := ammTransferFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz100 hsize hszhi
    hcanonFrom hcanonTo hne hreach
  have rd2012 := rd2012₀
  rw [hmax] at rd2012
  exact ⟨_, _, evm_run rd2012 with [
    eq, iszero, jumpdest, iszero, push2 ⟨2276⟩,
    jumpiT (by decide) (by jump_dest) ]⟩

theorem ammTransferFromX_spend_start {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (ammTransferFromAllowanceSlot I) ≠
      ammTransferFromMaxWord)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2020⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2012₀⟩ := ammTransferFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz100 hsize hszhi
    hcanonFrom hcanonTo hne hreach
  have hneqWord : UInt256.eq (solcSlotWord σ I (ammTransferFromAllowanceSlot I))
      ammTransferFromMaxWord = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnotmax (uInt256_eq_one_eq he))
  have rd2013 := evm_run rd2012₀ with [eq]
  rw [hneqWord] at rd2013
  exact ⟨_, _, evm_run rd2013 with [
    iszero, jumpdest, iszero, push2 ⟨2276⟩,
    jumpiNT (by decide) ]⟩

noncomputable def ammTransferFromAllowanceReadOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (ammTransferFromFromWord I) ⟨2⟩ (ammTransferFromAllowanceMem I)

noncomputable def ammTransferFromAllowanceReadMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (ammTransferFromAllowanceOuterSlot I)
    (ammTransferFromAllowanceReadOuterMem I)

theorem ammTransferFromX_spend_load {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (ammTransferFromAllowanceSlot I) ≠
      ammTransferFromMaxWord)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2142⟩
      [solcSlotWord σ I (ammTransferFromAllowanceSlot I),
        ammTransferFromValueWord I, ⟨0⟩, ammTransferFromValueWord I,
        ammTransferFromToWord I, ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2020⟩ := ammTransferFromX_spend_start (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have hfromClean : UInt256.land solcAddrMask (ammTransferFromFromWord I) =
      ammTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd2069₀ := evm_run rd2020 with [
    dup2, push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2069 := rd2069₀
  rw [hfromClean, hfromClean] at rd2069
  have hmem : (ammTransferFromAllowanceMem I).size = 96 := by
    unfold ammTransferFromAllowanceMem ammTransferFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2082⟩ := RD.ammMappingHashSuffix rd2069 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromAllowanceReadOuterMem,
      ammTransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (ammTransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2128₀ := evm_run rd2082 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2128 := rd2128₀
  rw [hsourceClean, hsourceClean] at rd2128
  have hmem2 : (ammTransferFromAllowanceReadOuterMem I).size = 96 := by
    unfold ammTransferFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2141⟩ := RD.ammMappingHashSuffix rd2128 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromAllowanceReadMem,
      ammTransferFromAllowanceOuterSlot,
      ammTransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (ammTransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2142⟩ := rd2141.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2142⟩

theorem ammTransferFromX_spend_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (ammTransferFromAllowanceSlot I) ≠
      ammTransferFromMaxWord)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2151⟩
      [UInt256.sub (solcSlotWord σ I (ammTransferFromAllowanceSlot I))
        (ammTransferFromValueWord I), ⟨0⟩, ammTransferFromValueWord I,
        ammTransferFromToWord I, ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2142⟩ := ammTransferFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have rd6645 := evm_run rd2142 with [
    push2 ⟨2151⟩, swap2, swap1, push2 ⟨6645⟩, jump (by jump_dest) ]
  exact RD.ammCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem ammTransferFromX_spend_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (ammTransferFromAllowanceSlot I) ≠
      ammTransferFromMaxWord)
    (hunder : (solcSlotWord σ I (ammTransferFromAllowanceSlot I)).toNat <
      (ammTransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2142⟩ := ammTransferFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have rd6645 := evm_run rd2142 with [
    push2 ⟨2151⟩, swap2, swap1, push2 ⟨6645⟩, jump (by jump_dest) ]
  exact RD.ammCheckedSubUnderflow rd6645 hunder (by evm_ov)

noncomputable def ammTransferFromAllowanceStoreOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (ammTransferFromFromWord I) ⟨2⟩ (ammTransferFromAllowanceReadMem I)

noncomputable def ammTransferFromAllowanceStoreMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (ammTransferFromAllowanceOuterSlot I)
    (ammTransferFromAllowanceStoreOuterMem I)

def ammTransferFromEvmAllowanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (ammTransferFromAllowanceSlot I)
    (UInt256.sub (solcSlotWord σ I (ammTransferFromAllowanceSlot I))
      (ammTransferFromValueWord I))

theorem ammTransferFromX_spend_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : ammTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (ammTransferFromAllowanceSlot I) ≠
      ammTransferFromMaxWord)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σ I (ammTransferFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromAllowanceStoreMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferFromEvmAllowanceMap σ I) k C := by
  obtain ⟨_, _, rd2151⟩ := ammTransferFromX_spend_debit (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hle hreach
  have hfromClean : UInt256.land solcAddrMask (ammTransferFromFromWord I) =
      ammTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd2200₀ := evm_run rd2151 with [
    jumpdest, push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2200 := rd2200₀
  rw [hfromClean, hfromClean] at rd2200
  have hmem : (ammTransferFromAllowanceReadMem I).size = 96 := by
    unfold ammTransferFromAllowanceReadMem ammTransferFromAllowanceReadOuterMem
      ammTransferFromAllowanceMem ammTransferFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2213⟩ := RD.ammMappingHashSuffix rd2200 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromAllowanceStoreOuterMem,
      ammTransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (ammTransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2259₀ := evm_run rd2213 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2259 := rd2259₀
  rw [hsourceClean, hsourceClean] at rd2259
  have hmem2 : (ammTransferFromAllowanceStoreOuterMem I).size = 96 := by
    unfold ammTransferFromAllowanceStoreOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2272⟩ := RD.ammMappingHashSuffix rd2259 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromAllowanceStoreMem,
      ammTransferFromAllowanceOuterSlot,
      ammTransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (ammTransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2274 := evm_run rd2272 with [dup2, swap1]
  obtain ⟨_, _, rd2275⟩ := rd2274.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [ammTransferFromEvmAllowanceMap] using
    (evm_run rd2275 with [pop])⟩

noncomputable def ammTransferFromBalanceReadMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (ammTransferFromFromWord I) ⟨1⟩ mem

def ammTransferFromEvmBalanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (ammTransferFromBalanceSlot I)
    (UInt256.sub (solcSlotWord σ I (ammTransferFromBalanceSlot I))
      (ammTransferFromValueWord I))

noncomputable def ammTransferFromBalanceStoreMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (ammTransferFromFromWord I) ⟨1⟩
    (ammTransferFromBalanceReadMem I mem)

noncomputable def ammTransferFromToReadMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (ammTransferFromToWord I) ⟨1⟩
    (ammTransferFromBalanceStoreMem I mem)

noncomputable def ammTransferFromToStoreMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (ammTransferFromToWord I) ⟨1⟩
    (ammTransferFromToReadMem I mem)

def ammTransferFromEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (ammTransferFromEvmBalanceMap σ I)
    (ammTransferFromToSlot I)
    (solcSlotWord (ammTransferFromEvmBalanceMap σ I) I
      (ammTransferFromToSlot I) + ammTransferFromValueWord I)

theorem ammTransferFromX_balance_load {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2340⟩
      [solcSlotWord σA I (ammTransferFromBalanceSlot I),
        ammTransferFromValueWord I, ⟨0⟩, ammTransferFromValueWord I,
        ammTransferFromToWord I, ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromBalanceReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σA) k C := by
  obtain ⟨_, _, rd2276⟩ := hreach
  have hfromClean : UInt256.land solcAddrMask (ammTransferFromFromWord I) =
      ammTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd2326₀ := evm_run rd2276 with [
    jumpdest, dup2, push1 ⟨1⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2326 := rd2326₀
  rw [hfromClean, hfromClean] at rd2326
  obtain ⟨_, _, rd2339⟩ := RD.ammMappingHashSuffix rd2326 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromBalanceReadMem,
      ammTransferFromBalanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (ammTransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2340⟩ := rd2339.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2340⟩

theorem ammTransferFromX_balance_debit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2349⟩
      [UInt256.sub (solcSlotWord σA I (ammTransferFromBalanceSlot I))
        (ammTransferFromValueWord I), ⟨0⟩, ammTransferFromValueWord I,
        ammTransferFromToWord I, ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromBalanceReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σA) k C := by
  obtain ⟨_, _, rd2340⟩ := ammTransferFromX_balance_load hcanonFrom hmem hreach
  have rd6645 := evm_run rd2340 with [
    push2 ⟨2349⟩, swap2, swap1, push2 ⟨6645⟩, jump (by jump_dest) ]
  exact RD.ammCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem ammTransferFromX_balance_underflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hunder : (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat <
      (ammTransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2340⟩ := ammTransferFromX_balance_load hcanonFrom hmem hreach
  have rd6645 := evm_run rd2340 with [
    push2 ⟨2349⟩, swap2, swap1, push2 ⟨6645⟩, jump (by jump_dest) ]
  exact RD.ammCheckedSubUnderflow rd6645 hunder (by evm_ov)

theorem ammTransferFromX_balance_stored {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2415⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromBalanceStoreMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd2349⟩ := ammTransferFromX_balance_debit hcanonFrom hmem hle hreach
  have hfromClean : UInt256.land solcAddrMask (ammTransferFromFromWord I) =
      ammTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd2398₀ := evm_run rd2349 with [
    jumpdest, push1 ⟨1⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2398 := rd2398₀
  rw [hfromClean, hfromClean] at rd2398
  have hmem2 : (ammTransferFromBalanceReadMem I mem).size = 96 := by
    unfold ammTransferFromBalanceReadMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2411⟩ := RD.ammMappingHashSuffix rd2398 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromBalanceStoreMem,
      ammTransferFromBalanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (ammTransferFromFromWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2413 := evm_run rd2411 with [dup2, swap1]
  obtain ⟨_, _, rd2414⟩ := rd2413.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [ammTransferFromEvmBalanceMap] using
    (evm_run rd2414 with [pop])⟩

theorem ammTransferFromX_toBalance_load {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2478⟩
      [solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
        (ammTransferFromToSlot I), ammTransferFromValueWord I,
        ⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromToReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd2415⟩ := ammTransferFromX_balance_stored hperm hcanonFrom hmem
    hle hreach
  have htoClean : UInt256.land solcAddrMask (ammTransferFromToWord I) =
      ammTransferFromToWord I := solcAddrMask_clean_left hcanonTo
  have rd2464₀ := evm_run rd2415 with [
    dup2, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2464 := rd2464₀
  rw [htoClean, htoClean] at rd2464
  have hmem2 : (ammTransferFromBalanceStoreMem I mem).size = 96 := by
    unfold ammTransferFromBalanceStoreMem ammTransferFromBalanceReadMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2477⟩ := RD.ammMappingHashSuffix rd2464 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromToReadMem,
      ammTransferFromToSlot_eq_solc I hcanonTo] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (ammTransferFromToWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2478⟩ := rd2477.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2478⟩

theorem ammTransferFromX_credit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
      (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2487⟩
      [solcSlotWord (ammTransferFromEvmBalanceMap σA I) I (ammTransferFromToSlot I) +
        ammTransferFromValueWord I, ⟨0⟩, ammTransferFromValueWord I,
        ammTransferFromToWord I, ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromToReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd2478⟩ := ammTransferFromX_toBalance_load hperm hcanonFrom
    hcanonTo hmem hle hreach
  have rd6696 := evm_run rd2478 with [
    push2 ⟨2487⟩, swap2, swap1, push2 ⟨6696⟩, jump (by jump_dest) ]
  exact RD.ammCheckedAddOk rd6696 hfit (by jump_dest) (by evm_ov)

theorem ammTransferFromX_overflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hover : UInt256.size ≤ (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
      (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2478⟩ := ammTransferFromX_toBalance_load hperm hcanonFrom
    hcanonTo hmem hle hreach
  have rd6696 := evm_run rd2478 with [
    push2 ⟨2487⟩, swap2, swap1, push2 ⟨6696⟩, jump (by jump_dest) ]
  exact RD.ammCheckedAddOverflow rd6696 hover (by evm_ov)

theorem ammTransferFromX_toBalance_stored {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
      (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2553⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      (ammTransferFromToStoreMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, ammTransferFromEvmPostMap σA I) k C := by
  obtain ⟨_, _, rd2487⟩ := ammTransferFromX_credit hperm hcanonFrom hcanonTo
    hmem hle hfit hreach
  have htoClean : UInt256.land solcAddrMask (ammTransferFromToWord I) =
      ammTransferFromToWord I := solcAddrMask_clean_left hcanonTo
  have rd2536₀ := evm_run rd2487 with [
    jumpdest, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2536 := rd2536₀
  rw [htoClean, htoClean] at rd2536
  have hmem2 : (ammTransferFromToReadMem I mem).size = 96 := by
    unfold ammTransferFromToReadMem ammTransferFromBalanceStoreMem
      ammTransferFromBalanceReadMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2549⟩ := RD.ammMappingHashSuffix rd2536 amm_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [ammTransferFromToStoreMem,
      ammTransferFromToSlot_eq_solc I hcanonTo] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (ammTransferFromToWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2551 := evm_run rd2549 with [dup2, swap1]
  obtain ⟨_, _, rd2552⟩ := rd2551.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [ammTransferFromEvmPostMap] using
    (evm_run rd2552 with [pop])⟩

theorem ammTransferFromToStoreMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) : (ammTransferFromToStoreMem I mem).size = 96 := by
  unfold ammTransferFromToStoreMem ammTransferFromToReadMem
    ammTransferFromBalanceStoreMem ammTransferFromBalanceReadMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ hmem

theorem ammTransferFromToStoreMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ammTransferFromToStoreMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammTransferFromToStoreMem ammTransferFromToReadMem
    ammTransferFromBalanceStoreMem ammTransferFromBalanceReadMem
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ hmem)))
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ hmem))
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ hmem)
  exact twoWordHashMem_read64 _ _ hmem hread

theorem ammX_transferFrom_tail {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
      (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDret ammBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, ammTransferFromEvmPostMap σA I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd2553⟩ := ammTransferFromX_toBalance_stored hperm hcanonFrom
    hcanonTo hmem hle hfit hreach
  have rd292 := evm_run rd2553 with [
    push1 ⟨1⟩, swap1, pop, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have hmemFinal := ammTransferFromToStoreMem_size I hmem
  have hreadFinal := ammTransferFromToStoreMem_read64 I hmem hread
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (ammTransferFromToStoreMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((ammTransferFromToStoreMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmemFinal]; decide) (by decide) hreadFinal
  have rd5629 := evm_run rd292 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨305⟩, swap2, swap1, push2 ⟨5629⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd305⟩ := RD.ammRoutineEncodeBoolFromMem
    (memout := ammWordReturnMem (ammTransferFromToStoreMem I mem) (⟨1⟩ : UInt256))
    rd5629 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd305 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (ammWordReturnMem_mload64_of_size96 ⟨1⟩ hmemFinal hreadFinal)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact ammWordReturnMem_read128_of_size96 ⟨1⟩ hmemFinal)
      (by evm_ov) ]

theorem ammTransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using (solcCalldataStaticLenCheckShort (words := 3)
      (sz := I.calldata.size) hsz4 (by omega) hsize (by norm_num))
  obtain ⟨_, _, rd⟩ := ammTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨5779⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5778⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammTransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using (solcCalldataStaticLenCheckHuge (words := 3)
      (sz := I.calldata.size) hbig hsize (by norm_num))
  obtain ⟨_, _, rd⟩ := ammTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨5779⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5778⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammTransferFromX_noncanonFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (ammTransferFromFromWord I)
      (UInt256.land (ammTransferFromFromWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5470_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammTransferFromX_noncanonTo {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (ammTransferFromToWord I)
      (UInt256.land (ammTransferFromToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨266⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammTransferFromX_dec5470_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.ammDecodeAddrRevert rd hnc (by evm_ov)

theorem ammTransferFromSelector_size {I : ExecutionEnv}
    (hsel : ammSelIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem ammDispatch_transferFrom {cd : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferFromTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, mintTransition, swap0Transition, swap1Transition,
      totalSupplyTransition, transferTransition])
    (post := [])
    rfl rfl ?_ (by rw [selectorOf, ammTransferFromSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, ammAllowanceSelectorBytes, hcd]
    | rw [selectorOf, ammApproveSelectorBytes, hcd]
    | rw [selectorOf, ammBalanceOfSelectorBytes, hcd]
    | rw [selectorOf, ammBurnSelectorBytes, hcd]
    | rw [selectorOf, ammMintSelectorBytes, hcd]
    | rw [selectorOf, ammSwap0SelectorBytes, hcd]
    | rw [selectorOf, ammSwap1SelectorBytes, hcd]
    | rw [selectorOf, ammTotalSupplySelectorBytes, hcd]
    | rw [selectorOf, ammTransferSelectorBytes, hcd]
  all_goals decide

theorem ammTransferFromFromWord_eq_source_iff (I : ExecutionEnv)
    (hcanon : (ammTransferFromFromWord I).toNat < EVM.addressModulus) :
    ammTransferFromFromWord I = solcSourceWord I ↔
      AccountAddress.ofNat (ammTransferFromFromWord I).toNat = I.source := by
  constructor
  · intro h
    rw [h]
    exact solcSource_ofNat I
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    change (ammTransferFromFromWord I).toNat % AccountAddress.size = I.source.val at hv
    have hcanon' : (ammTransferFromFromWord I).toNat < AccountAddress.size := hcanon
    rw [Nat.mod_eq_of_lt hcanon'] at hv
    rw [solcSourceWord_toNat]
    exact hv

theorem ammTransferFromMaxWord_toNat :
    ammTransferFromMaxWord.toNat = Int.toNat maxUint256 := by
  native_decide

theorem ammTransferFromAllowanceValue_eq_max_iff (w : UInt256) :
    Value.int (Int.ofNat w.toNat) = .int maxUint256 ↔
      w = ammTransferFromMaxWord := by
  constructor
  · intro h
    have hnat : w.toNat = ammTransferFromMaxWord.toNat := by
      have hi : Int.ofNat w.toNat = maxUint256 := by
        injection h with hi
      rw [ammTransferFromMaxWord_toNat]
      exact congrArg Int.toNat hi
    exact u256_inj hnat
  · intro h
    rw [h]
    native_decide

theorem ammTransferFromShouldSpend_iff (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (ammTransferFromFromWord I).toNat < EVM.addressModulus) :
    ammTransferFromShouldSpend evm I = true ↔
      ammTransferFromFromWord I ≠ solcSourceWord I ∧
        ammTransferFromAllowanceWord evm I ≠ ammTransferFromMaxWord := by
  rw [ammTransferFromShouldSpend]
  simp only [Bool.and_eq_true, Bool.not_eq_true]
  constructor
  · rintro ⟨hfrom, hallow⟩
    constructor
    · intro he
      have hv := (ammTransferFromFromWord_eq_source_iff I hcanon).mp he
      simp [ammTransferFromFromValue, BEq.beq, hv] at hfrom
    · intro he
      have hv := (ammTransferFromAllowanceValue_eq_max_iff _).mpr he
      have hi : Int.ofNat (ammTransferFromAllowanceWord evm I).toNat =
          maxUint256 := by injection hv with hi
      simp [BEq.beq] at hallow
      exact hallow hi
  · rintro ⟨hfrom, hallow⟩
    constructor
    · have hv : AccountAddress.ofNat (ammTransferFromFromWord I).toNat ≠
          I.source := fun he => hfrom ((ammTransferFromFromWord_eq_source_iff I hcanon).mpr he)
      simp [ammTransferFromFromValue, BEq.beq, hv]
    · have hv : Value.int (Int.ofNat (ammTransferFromAllowanceWord evm I).toNat) ≠
          .int maxUint256 := fun he => hallow ((ammTransferFromAllowanceValue_eq_max_iff _).mp he)
      simp [BEq.beq]
      intro hi
      exact hv (congrArg Value.int hi)

theorem ammTransferFromAllowanceMem_size (I : ExecutionEnv) :
    (ammTransferFromAllowanceMem I).size = 96 := by
  unfold ammTransferFromAllowanceMem ammTransferFromAllowanceOuterMem
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size

theorem ammTransferFromAllowanceMem_read64 (I : ExecutionEnv) :
    (ammTransferFromAllowanceMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold ammTransferFromAllowanceMem ammTransferFromAllowanceOuterMem
  apply twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem ammTransferFromAllowanceStoreMem_size (I : ExecutionEnv) :
    (ammTransferFromAllowanceStoreMem I).size = 96 := by
  unfold ammTransferFromAllowanceStoreMem ammTransferFromAllowanceStoreOuterMem
    ammTransferFromAllowanceReadMem ammTransferFromAllowanceReadOuterMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ (ammTransferFromAllowanceMem_size I)

theorem ammTransferFromAllowanceStoreMem_read64 (I : ExecutionEnv) :
    (ammTransferFromAllowanceStoreMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [ammTransferFromAllowanceStoreMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold ammTransferFromAllowanceStoreOuterMem
    apply twoWordHashMem_size_96
    unfold ammTransferFromAllowanceReadMem ammTransferFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (ammTransferFromAllowanceMem_size I))
  rw [ammTransferFromAllowanceStoreOuterMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold ammTransferFromAllowanceReadMem ammTransferFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (ammTransferFromAllowanceMem_size I))
  rw [ammTransferFromAllowanceReadMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold ammTransferFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ (ammTransferFromAllowanceMem_size I))
  rw [ammTransferFromAllowanceReadOuterMem]
  exact twoWordHashMem_read64 _ _ (ammTransferFromAllowanceMem_size I)
    (ammTransferFromAllowanceMem_read64 I)

theorem ammTransferFromTailCore
    {cA gh bl σ_evm σ_solm σ₀ σA A I} {g : UInt256} {mem : ByteArray}
    (hcode : I.code = ammBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hd : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdec : decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (ammTransferFromStore I))
    (hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus)
    (hallow : ammTransferFromShouldSpend
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = true →
      (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromAllowanceWord
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hState : EVMStateEquiv
      (ammTransferFromAfterAllowance
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
      (ammTransferFromAfterAllowance
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I))
    (hmapA : (ammTransferFromAfterAllowance
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap = σA)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2276⟩
      [⟨0⟩, ammTransferFromValueWord I, ammTransferFromToWord I,
        ammTransferFromFromWord I, ⟨292⟩, ammSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσA : EVMStateEquiv (ammTransferFromAfterAllowance evmE I)
      (ammTransferFromAfterAllowance evmS I) := hState
  have hmapA' : (ammTransferFromAfterAllowance evmE I).accountMap = σA := hmapA
  have hbalanceE :
      ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmE I) I =
        solcSlotWord σA I (ammTransferFromBalanceSlot I) := by
    unfold ammTransferFromBalanceWord
    rw [ammTransferFromAfterAllowance_codeOwner evmE I,
      show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
    simp only [Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWord, hmapA']
  have hbalanceS :
      ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmS I) I =
        solcSlotWord σA I (ammTransferFromBalanceSlot I) := by
    rw [show ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmS I) I =
        ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmE I) I from
          (hσA.storageLoad_codeOwner (ammTransferFromBalanceSlot I)).symm, hbalanceE]
  by_cases hle : (ammTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat
  · have hleE : (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmE I) I).toNat :=
      hbalanceE ▸ hle
    have hleS : (ammTransferFromValueWord I).toNat ≤
        (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmS I) I).toNat :=
      hbalanceS ▸ hle
    have hdebit : ammTransferFromBalanceDebitWord evmE I =
        ammTransferFromBalanceDebitWord evmS I := by
      unfold ammTransferFromBalanceDebitWord
      rw [hbalanceE, hbalanceS]
    have hσBalance : EVMStateEquiv
        (ammTransferFromAfterBalance evmE I) (ammTransferFromAfterBalance evmS I) := by
      unfold ammTransferFromAfterBalance
      rw [← ammTransferFromAfterAllowance_codeOwner evmE I,
        ← ammTransferFromAfterAllowance_codeOwner evmS I]
      exact hσA.storageStore_codeOwner (ammTransferFromBalanceSlot I) hdebit
    have hmapBalance : (ammTransferFromAfterBalance evmE I).accountMap =
        ammTransferFromEvmBalanceMap σA I := by
      unfold ammTransferFromAfterBalance ammTransferFromEvmBalanceMap
      rw [storageStore_accountMap,
        show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
        hmapA']
      apply congrArg (sstoreAccountMap I.codeOwner σA (ammTransferFromBalanceSlot I))
      apply u256_inj
      rw [ammTransferFromBalanceDebitWord_toNat evmE I,
        hbalanceE, usub_toNat hle]
    have htoE : ammTransferFromToBalanceWord evmE I =
        solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
          (ammTransferFromToSlot I) := by
      unfold ammTransferFromToBalanceWord
      rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
      simp only [Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, solcSlotWord, hmapBalance]
    have htoS : ammTransferFromToBalanceWord evmS I =
        solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
          (ammTransferFromToSlot I) := by
      rw [show ammTransferFromToBalanceWord evmS I =
          ammTransferFromToBalanceWord evmE I from by
            unfold ammTransferFromToBalanceWord
            rw [← ammTransferFromAfterBalance_codeOwner evmE I,
              ← ammTransferFromAfterBalance_codeOwner evmS I]
            exact (hσBalance.storageLoad_codeOwner (ammTransferFromToSlot I)).symm,
        htoE]
    have hnewE : ammTransferFromNewToNat evmE I =
        (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
          (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat := by
      rw [ammTransferFromNewToNat, htoE]
    have hnewS : ammTransferFromNewToNat evmS I =
        (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
          (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat := by
      rw [ammTransferFromNewToNat, htoS]
    by_cases hfit : (solcSlotWord (ammTransferFromEvmBalanceMap σA I) I
        (ammTransferFromToSlot I)).toNat + (ammTransferFromValueWord I).toNat <
        UInt256.size
    · have hfitE : ammTransferFromNewToNat evmE I < UInt256.size :=
        hnewE ▸ hfit
      have hfitS : ammTransferFromNewToNat evmS I < UInt256.size :=
        hnewS ▸ hfit
      have hnewWord : ammTransferFromNewToWord evmE I =
          ammTransferFromNewToWord evmS I := by
        unfold ammTransferFromNewToWord
        rw [hnewE, hnewS]
      have hσPost : EVMStateEquiv
          (ammTransferFromPostState evmE I) (ammTransferFromPostState evmS I) := by
        change EVMStateEquiv
          (Solm.EVM.storageStore (ammTransferFromAfterBalance evmE I)
            evmE.executionEnv.codeOwner (ammTransferFromToSlot I)
            (ammTransferFromNewToWord evmE I))
          (Solm.EVM.storageStore (ammTransferFromAfterBalance evmS I)
            evmS.executionEnv.codeOwner (ammTransferFromToSlot I)
            (ammTransferFromNewToWord evmS I))
        exact hσBalance.storageStore rfl (ammTransferFromToSlot I) hnewWord
      have hmapPost : (ammTransferFromPostState evmE I).accountMap =
          ammTransferFromEvmPostMap σA I := by
        unfold ammTransferFromPostState ammTransferFromEvmPostMap
        rw [storageStore_accountMap,
          show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
          hmapBalance]
        apply congrArg (sstoreAccountMap I.codeOwner
          (ammTransferFromEvmBalanceMap σA I) (ammTransferFromToSlot I))
        apply u256_inj
        rw [ammTransferFromNewToWord_toNat evmE I hfitE, uadd_toNat,
          hnewE, Nat.mod_eq_of_lt hfit]
      have hbody := ammTransferFromBodyReturns evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hfitS
      have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
          (some [(.bool true)]) transferFromTransition.returnType :=
        returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
      exact (ammX_transferFrom_tail (g := Sat256.ofUInt256 g)
          hperm hcanonFrom hcanonTo hmem hread hle hfit hreach)
        |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
          (by
            have hcreatedA : (ammTransferFromAfterAllowance evmE I).createdAccounts =
                cA := by
              unfold ammTransferFromAfterAllowance
              split
              · simp [storageStore_createdAccounts, evmE, initState]
              · rfl
            rw [ammTransferFromPostState, storageStore_createdAccounts,
              ammTransferFromAfterBalance, storageStore_createdAccounts, hcreatedA])
          (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
    · have hover : UInt256.size ≤ ammTransferFromNewToNat evmS I := by
        rw [hnewS]
        omega
      have hbody := ammTransferFromBodyReverts_credit evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hover
      exact (ammTransferFromX_overflow (g := Sat256.ofUInt256 g)
          hperm hcanonFrom hcanonTo hmem hle (by omega) hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hunder : (solcSlotWord σA I (ammTransferFromBalanceSlot I)).toNat <
        (ammTransferFromValueWord I).toNat := by omega
    have hunderS :
        (ammTransferFromBalanceWord (ammTransferFromAfterAllowance evmS I) I).toNat <
          (ammTransferFromValueWord I).toNat := by rw [hbalanceS]; exact hunder
    have hbody := ammTransferFromBodyReverts_balance evmS I
      (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hunderS
    exact (ammTransferFromX_balance_underflow (g := Sat256.ofUInt256 g)
        hcanonFrom hmem hunder hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

/-- The transferFrom wrapper, entered at PC 266, refines its Solm transition. -/
theorem ammTransferFromBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = ammBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : ammSelIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hreach : ∃ k C, RD ammBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨266⟩ [ammSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := ammTransferFromSelector_size hsel
  have hd := ammDispatch_transferFrom (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (ammTransferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (ammTransferFromToWord I).toNat < EVM.addressModulus
        · have hdec := ammDecode_transferFrom_ok (I := I) hsz100 hbig
            hcanonFrom hcanonTo
          let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hσ : EVMStateEquiv evmE evmS := by
            simpa [evmE, evmS] using
              EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
          have hallowWordE : ammTransferFromAllowanceWord evmE I =
              solcSlotWord σ_evm I (ammTransferFromAllowanceSlot I) := by
            simpa [ammTransferFromAllowanceWord, solcSlotWord,
              codeOwnerStorageWord] using
              (codeOwnerStorageWord_initState
                (g := Sat256.ofUInt256 g) (σ := σ_evm)
                (slot := ammTransferFromAllowanceSlot I) (cA := cA)
                (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
          have hallowWordS : ammTransferFromAllowanceWord evmS I =
              solcSlotWord σ_evm I (ammTransferFromAllowanceSlot I) := by
            rw [show ammTransferFromAllowanceWord evmS I =
                ammTransferFromAllowanceWord evmE I from
                  (hσ.storageLoad_codeOwner (ammTransferFromAllowanceSlot I)).symm,
              hallowWordE]
          by_cases hself : ammTransferFromFromWord I = solcSourceWord I
          · have hspendE : ammTransferFromShouldSpend evmE I = false := by
              cases hs : ammTransferFromShouldSpend evmE I with
              | false => rfl
              | true => exact False.elim (((ammTransferFromShouldSpend_iff evmE I hcanonFrom).mp hs).1 hself)
            have hspendS : ammTransferFromShouldSpend evmS I = false := by
              cases hs : ammTransferFromShouldSpend evmS I with
              | false => rfl
              | true => exact False.elim (((ammTransferFromShouldSpend_iff evmS I hcanonFrom).mp hs).1 hself)
            have hState : EVMStateEquiv
                (ammTransferFromAfterAllowance evmE I)
                (ammTransferFromAfterAllowance evmS I) := by
              simpa [ammTransferFromAfterAllowance, hspendE, hspendS] using hσ
            have hmapA : (ammTransferFromAfterAllowance evmE I).accountMap =
                σ_evm := by
              rw [ammTransferFromAfterAllowance, hspendE]
              rfl
            exact ammTransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
              hcanonTo (by intro hs; rw [hspendS] at hs; cases hs)
              hState hmapA solcFreePtrMem_size solcFreePtrMem_read64
              (ammTransferFromX_self_to_balance (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hcanonFrom hcanonTo hself hreach)
          · by_cases hmax : solcSlotWord σ_evm I (ammTransferFromAllowanceSlot I) =
                ammTransferFromMaxWord
            · have hspendE : ammTransferFromShouldSpend evmE I = false := by
                cases hs : ammTransferFromShouldSpend evmE I with
                | false => rfl
                | true => exact False.elim (((ammTransferFromShouldSpend_iff evmE I hcanonFrom).mp hs).2
                    (by rw [hallowWordE]; exact hmax))
              have hspendS : ammTransferFromShouldSpend evmS I = false := by
                cases hs : ammTransferFromShouldSpend evmS I with
                | false => rfl
                | true => exact False.elim (((ammTransferFromShouldSpend_iff evmS I hcanonFrom).mp hs).2
                    (by rw [hallowWordS]; exact hmax))
              have hState : EVMStateEquiv
                  (ammTransferFromAfterAllowance evmE I)
                  (ammTransferFromAfterAllowance evmS I) := by
                simpa [ammTransferFromAfterAllowance, hspendE, hspendS] using hσ
              have hmapA : (ammTransferFromAfterAllowance evmE I).accountMap =
                  σ_evm := by
                rw [ammTransferFromAfterAllowance, hspendE]
                rfl
              exact ammTransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
                hcanonTo (by intro hs; rw [hspendS] at hs; cases hs)
                hState hmapA (ammTransferFromAllowanceMem_size I)
                (ammTransferFromAllowanceMem_read64 I)
                (ammTransferFromX_max_to_balance (g := Sat256.ofUInt256 g)
                  hsz100 hsize hbig hcanonFrom hcanonTo hself hmax hreach)
            · have hspendE : ammTransferFromShouldSpend evmE I = true :=
                (ammTransferFromShouldSpend_iff evmE I hcanonFrom).mpr
                  ⟨hself, by rwa [hallowWordE]⟩
              have hspendS : ammTransferFromShouldSpend evmS I = true :=
                (ammTransferFromShouldSpend_iff evmS I hcanonFrom).mpr
                  ⟨hself, by rwa [hallowWordS]⟩
              by_cases hle : (ammTransferFromValueWord I).toNat ≤
                  (solcSlotWord σ_evm I (ammTransferFromAllowanceSlot I)).toNat
              · have hdebit : ammTransferFromAllowanceDebitWord evmE I =
                    ammTransferFromAllowanceDebitWord evmS I := by
                  unfold ammTransferFromAllowanceDebitWord
                  rw [hallowWordE, hallowWordS]
                have hState : EVMStateEquiv
                    (ammTransferFromAfterAllowance evmE I)
                    (ammTransferFromAfterAllowance evmS I) := by
                  simp only [ammTransferFromAfterAllowance, hspendE, hspendS,
                    if_true]
                  exact hσ.storageStore_codeOwner
                    (ammTransferFromAllowanceSlot I) hdebit
                have hmapA : (ammTransferFromAfterAllowance evmE I).accountMap =
                    ammTransferFromEvmAllowanceMap σ_evm I := by
                  rw [ammTransferFromAfterAllowance, if_pos hspendE,
                    storageStore_accountMap]
                  change sstoreAccountMap I.codeOwner σ_evm
                    (ammTransferFromAllowanceSlot I)
                    (ammTransferFromAllowanceDebitWord evmE I) = _
                  unfold ammTransferFromEvmAllowanceMap
                  apply congrArg (sstoreAccountMap I.codeOwner σ_evm
                    (ammTransferFromAllowanceSlot I))
                  apply u256_inj
                  rw [ammTransferFromAllowanceDebitWord_toNat evmE I,
                    hallowWordE, usub_toNat hle]
                exact ammTransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
                  hcanonTo (by intro _; rwa [hallowWordS]) hState hmapA
                  (ammTransferFromAllowanceStoreMem_size I)
                  (ammTransferFromAllowanceStoreMem_read64 I)
                  (ammTransferFromX_spend_stored (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonFrom hcanonTo hself hmax hle hreach)
              · have hunder : (solcSlotWord σ_evm I
                    (ammTransferFromAllowanceSlot I)).toNat <
                    (ammTransferFromValueWord I).toNat := by omega
                have hbody := ammTransferFromBodyReverts_allowance evmS I
                  (by simp only [evmS, initState]; exact hwv) (by rfl) hspendS
                  (by rwa [hallowWordS])
                exact (ammTransferFromX_spend_underflow (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hcanonFrom hcanonTo hself hmax hunder hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := ammDecode_transferFrom_none_noncanonTo
            (I := I) hsz100 hbig hcanonFrom hcanonTo
          have hnc : UInt256.eq (ammTransferFromToWord I)
              (UInt256.land (ammTransferFromToWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonTo (solcAddrCanonical_of_clean he))
          exact (ammTransferFromX_noncanonTo (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonFrom hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := ammDecode_transferFrom_none_noncanonFrom
          (I := I) hsz100 hbig hcanonFrom
        have hnc : UInt256.eq (ammTransferFromFromWord I)
            (UInt256.land (ammTransferFromFromWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonFrom (solcAddrCanonical_of_clean he))
        exact (ammTransferFromX_noncanonFrom (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := ammDecode_transferFrom_none_huge (I := I) hbigge
      exact (ammTransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := ammDecode_transferFrom_none_short (I := I) hsz4 hshort
    exact (ammTransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmm
