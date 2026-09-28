import Benchmarks.ActAmmToken.Decode
import Benchmarks.ActAmmToken.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `transferFrom` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

abbrev tokenTransferFromFromWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)
abbrev tokenTransferFromToWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)
abbrev tokenTransferFromValueWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨64⟩ : UInt256).toNat 32)
abbrev tokenTransferFromStore (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "from"
    (.address (AccountAddress.ofNat (tokenTransferFromFromWord I).toNat))).insert "to"
    (.address (AccountAddress.ofNat (tokenTransferFromToWord I).toNat))).insert "value"
    (.int (Int.ofNat (tokenTransferFromValueWord I).toNat))
theorem tokenDecode_transferFrom_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hfrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hto : (tokenTransferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (tokenTransferFromStore I) := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, tokenTransferFromStore,
    tokenTransferFromFromWord, tokenTransferFromToWord, tokenTransferFromValueWord,
    calldataWord] using
    decodeCalldata_address_address_uint256_ok
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hfrom hto
theorem tokenDecode_transferFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_address_address_uint256_none_short
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hsz4 hshort
theorem tokenDecode_transferFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using
    decodeCalldata_address_address_uint256_none_huge
      (cd := I.calldata) (x := "from") (y := "to") (z := "value") hbig
theorem tokenDecode_transferFrom_none_noncanonFrom {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (tokenTransferFromFromWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, tokenTransferFromFromWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon0
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hnc
theorem tokenDecode_transferFrom_none_noncanonTo {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hfrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (tokenTransferFromToWord I).toNat < EVM.addressModulus) :
    decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["from", "to", "value"] [addr, addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, tokenTransferFromFromWord,
    tokenTransferFromToWord, calldataWord] using
    decodeCalldata_address_address_uint256_none_noncanon1
      (cd := I.calldata) (x := "from") (y := "to") (z := "value")
      hsz100 hbig hfrom hnc
abbrev tokenTransferFromFromValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (tokenTransferFromFromWord I).toNat)
abbrev tokenTransferFromToValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (tokenTransferFromToWord I).toNat)
abbrev tokenTransferFromValueValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (tokenTransferFromValueWord I).toNat)

def tokenTransferFromAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (tokenTransferFromFromWord I).toNat))
    (.address I.source)

def tokenTransferFromBalanceSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (tokenTransferFromFromWord I).toNat))

def tokenTransferFromToSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (tokenTransferFromToWord I).toNat))

theorem tokenTransferFromAllowanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (tokenTransferFromFromWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (tokenTransferFromFromWord I))
      (solcSourceWord I) = tokenTransferFromAllowanceSlot I := by
  unfold tokenTransferFromAllowanceSlot allowanceSlot allowanceOwnerSlot mapSlot
    solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon,
    tokenSource_keyValueToWord I.source]

theorem tokenTransferFromBalanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (tokenTransferFromFromWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (tokenTransferFromFromWord I) =
      tokenTransferFromBalanceSlot I := by
  unfold tokenTransferFromBalanceSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem tokenTransferFromToSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (tokenTransferFromToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (tokenTransferFromToWord I) =
      tokenTransferFromToSlot I := by
  unfold tokenTransferFromToSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem tokenTransferFromStore_from (I : ExecutionEnv) :
    (tokenTransferFromStore I).get? "from" = some (tokenTransferFromFromValue I) := by
  rw [tokenTransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem tokenTransferFromStore_to (I : ExecutionEnv) :
    (tokenTransferFromStore I).get? "to" = some (tokenTransferFromToValue I) := by
  rw [tokenTransferFromStore, store_get_ne _ _ (by decide), store_get_self]

theorem tokenTransferFromStore_value (I : ExecutionEnv) :
    (tokenTransferFromStore I).get? "value" = some (tokenTransferFromValueValue I) := by
  rw [tokenTransferFromStore, store_get_self]

theorem tokenTransferFromStore_allowance (I : ExecutionEnv) :
    (tokenTransferFromStore I).get? "allowance" = none := by
  rw [tokenTransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem tokenTransferFromStore_balance (I : ExecutionEnv) :
    (tokenTransferFromStore I).get? "balanceOf" = none := by
  rw [tokenTransferFromStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

def tokenTransferFromAllowanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps :=
    [.mindex (.address (AccountAddress.ofNat (tokenTransferFromFromWord I).toNat)),
      .mindex (.address I.source)] }

def tokenTransferFromBalanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps :=
    [.mindex (.address (AccountAddress.ofNat (tokenTransferFromFromWord I).toNat))] }

def tokenTransferFromToRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps :=
    [.mindex (.address (AccountAddress.ofNat (tokenTransferFromToWord I).toNat))] }

theorem tokenTransferFromEvalAllowanceRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := tokenTransferFromStore I } evm
      (allowanceRef (.var "from") sender) = .ok (tokenTransferFromAllowanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, tokenTransferFromAllowanceRef, tokenTransferFromFromValue,
    tokenTransferFromStore_from, sender, envValue, hsrc]

theorem tokenTransferFromEvalBalanceRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := tokenTransferFromStore I } evm
      (balanceOfRef (.var "from")) = .ok (tokenTransferFromBalanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, tokenTransferFromBalanceRef, tokenTransferFromFromValue,
    tokenTransferFromStore_from]

theorem tokenTransferFromEvalToRef (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := tokenTransferFromStore I } evm
      (balanceOfRef (.var "to")) = .ok (tokenTransferFromToRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, tokenTransferFromToRef, tokenTransferFromToValue,
    tokenTransferFromStore_to]

def tokenTransferFromAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tokenTransferFromAllowanceSlot I)

def tokenTransferFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tokenTransferFromBalanceSlot I)

theorem tokenTransferFromEvalAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.storage (allowanceRef (.var "from") sender)) =
        .ok (.int (Int.ofNat (tokenTransferFromAllowanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := tokenTransferFromStore_allowance I)
    (her := tokenTransferFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      tokenTransferFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [tokenTransferFromAllowanceWord, tokenTransferFromAllowanceSlot,
    tokenStorageLocLoad_uint256]

theorem tokenTransferFromEvalBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.storage (balanceOfRef (.var "from"))) =
        .ok (.int (Int.ofNat (tokenTransferFromBalanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := tokenTransferFromStore_balance I)
    (her := tokenTransferFromEvalBalanceRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      tokenTransferFromBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [tokenTransferFromBalanceWord, tokenTransferFromBalanceSlot,
    tokenStorageLocLoad_uint256]

theorem tokenTransferFromEvalToBalance (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.storage (balanceOfRef (.var "to"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (tokenTransferFromToSlot I)).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := tokenTransferFromStore_balance I)
    (her := tokenTransferFromEvalToRef evm I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      tokenTransferFromToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [tokenTransferFromToSlot, tokenStorageLocLoad_uint256]

theorem tokenTransferFromEvalValue (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.var "value") = .ok (tokenTransferFromValueValue I) := by
  simp only [evalExpr?, EvalResult.ofOption, tokenTransferFromStore_value]

theorem tokenTransferFromEvalFromNeSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.binary .ne (.var "from") sender) =
        .ok (.bool (!(tokenTransferFromFromValue I == .address I.source))) := by
  have hfrom : evalExpr? config
      { contract := contract, locals := tokenTransferFromStore I } evm (.var "from") =
      .ok (tokenTransferFromFromValue I) := by
    simp only [evalExpr?, EvalResult.ofOption, tokenTransferFromStore_from]
  have hsender : evalExpr? config
      { contract := contract, locals := tokenTransferFromStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hfrom, hsender, evalBinaryOp?]

theorem tokenTransferFromEvalAllowanceNeMax (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "from") sender))
        (.intLit maxUint256)) =
      .ok (.bool (!(Value.int (Int.ofNat
        (tokenTransferFromAllowanceWord evm I).toNat) == .int maxUint256))) := by
  have hallow := tokenTransferFromEvalAllowance evm I hsrc
  simp [evalExpr?, EvalResult.bind, bind, hallow, evalBinaryOp?]

theorem tokenTransferFromEvalCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) =
      .ok (.bool ((!(tokenTransferFromFromValue I == .address I.source)) &&
        (!(Value.int (Int.ofNat (tokenTransferFromAllowanceWord evm I).toNat) ==
          .int maxUint256)))) := by
  rw [evalExpr?]
  rw [tokenTransferFromEvalFromNeSender evm I hsrc]
  simp only [EvalResult.bind, bind]
  cases hleft : (!(tokenTransferFromFromValue I == .address I.source))
  · simp [pure]
  · rw [tokenTransferFromEvalAllowanceNeMax evm I hsrc]
    simp [pure]

def tokenTransferFromShouldSpend (evm : EVM.State) (I : ExecutionEnv) : Bool :=
  (!(tokenTransferFromFromValue I == .address I.source)) &&
    (!(Value.int (Int.ofNat (tokenTransferFromAllowanceWord evm I).toNat) ==
      .int maxUint256))

theorem tokenTransferFromEvalCond' (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) =
      .ok (.bool (tokenTransferFromShouldSpend evm I)) := by
  exact tokenTransferFromEvalCond evm I hsrc

def tokenTransferFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((tokenTransferFromAllowanceWord evm I).toNat -
    (tokenTransferFromValueWord I).toNat)

def tokenTransferFromAfterAllowance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if tokenTransferFromShouldSpend evm I then
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (tokenTransferFromAllowanceSlot I) (tokenTransferFromAllowanceDebitWord evm I)
  else evm

def tokenTransferFromBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat -
    (tokenTransferFromValueWord I).toNat)

def tokenTransferFromAfterBalance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (tokenTransferFromAfterAllowance evm I) evm.executionEnv.codeOwner
    (tokenTransferFromBalanceSlot I) (tokenTransferFromBalanceDebitWord evm I)

def tokenTransferFromToBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (tokenTransferFromAfterBalance evm I) evm.executionEnv.codeOwner
    (tokenTransferFromToSlot I)

def tokenTransferFromNewToNat (evm : EVM.State) (I : ExecutionEnv) : ℕ :=
  (tokenTransferFromToBalanceWord evm I).toNat + (tokenTransferFromValueWord I).toNat

def tokenTransferFromNewToWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (tokenTransferFromNewToNat evm I)

def tokenTransferFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (tokenTransferFromAfterBalance evm I) evm.executionEnv.codeOwner
    (tokenTransferFromToSlot I) (tokenTransferFromNewToWord evm I)

theorem tokenTransferFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (tokenTransferFromAfterAllowance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  unfold tokenTransferFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem tokenTransferFromAfterAllowance_source (evm : EVM.State) (I : ExecutionEnv) :
    (tokenTransferFromAfterAllowance evm I).executionEnv.source =
      evm.executionEnv.source := by
  unfold tokenTransferFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem tokenTransferFromAfterBalance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (tokenTransferFromAfterBalance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [tokenTransferFromAfterBalance, storageStore_executionEnv,
    tokenTransferFromAfterAllowance_codeOwner]

theorem tokenTransferFromAllowanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (tokenTransferFromAllowanceDebitWord evm I).toNat =
      (tokenTransferFromAllowanceWord evm I).toNat -
        (tokenTransferFromValueWord I).toNat := by
  unfold tokenTransferFromAllowanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (tokenTransferFromAllowanceWord evm I).val.isLt

theorem tokenTransferFromBalanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (tokenTransferFromBalanceDebitWord evm I).toNat =
      (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat -
        (tokenTransferFromValueWord I).toNat := by
  unfold tokenTransferFromBalanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _)
    (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).val.isLt

theorem tokenTransferFromEvalAllowanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (tokenTransferFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) =
        .ok (.int (Int.ofNat ((tokenTransferFromAllowanceWord evm I).toNat -
          (tokenTransferFromValueWord I).toNat))) := by
  exact tokenEvalCheckedSub_ok (tokenTransferFromEvalAllowance evm I hsrc)
    (tokenTransferFromEvalValue evm I) hle (tokenTransferFromAllowanceWord evm I).val.isLt

theorem tokenTransferFromEvalAllowanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (tokenTransferFromAllowanceWord evm I).toNat <
      (tokenTransferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I } evm
      (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) =
        .revert := by
  exact tokenEvalCheckedSub_revert (tokenTransferFromEvalAllowance evm I hsrc)
    (tokenTransferFromEvalValue evm I) hunder

theorem tokenTransferFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := tokenTransferFromStore I } evm
      .storage (allowanceRef (.var "from") sender)
      (.int (Int.ofNat (tokenTransferFromAllowanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := tokenTransferFromStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (tokenTransferFromAllowanceSlot I) (tokenTransferFromAllowanceDebitWord evm I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := tokenTransferFromStore_allowance I)
    (her := tokenTransferFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      tokenTransferFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [tokenTransferFromAllowanceSlot] using
    tokenStorageLocStore_uint256 evm (tokenTransferFromAllowanceSlot I)
      (tokenTransferFromAllowanceDebitWord evm I)

theorem tokenTransferFromEvalBalanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I }
      (tokenTransferFromAfterAllowance evm I)
      (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .ok (.int (Int.ofNat
          ((tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat -
            (tokenTransferFromValueWord I).toNat))) := by
  exact tokenEvalCheckedSub_ok
    (tokenTransferFromEvalBalance (tokenTransferFromAfterAllowance evm I) I)
    (tokenTransferFromEvalValue (tokenTransferFromAfterAllowance evm I) I) hle
    (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).val.isLt

theorem tokenTransferFromEvalBalanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hunder : (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat <
      (tokenTransferFromValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I }
      (tokenTransferFromAfterAllowance evm I)
      (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")) =
        .revert := by
  exact tokenEvalCheckedSub_revert
    (tokenTransferFromEvalBalance (tokenTransferFromAfterAllowance evm I) I)
    (tokenTransferFromEvalValue (tokenTransferFromAfterAllowance evm I) I) hunder

theorem tokenTransferFromAssignBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tokenTransferFromStore I }
      (tokenTransferFromAfterAllowance evm I)
      .storage (balanceOfRef (.var "from"))
      (.int (Int.ofNat (tokenTransferFromBalanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := tokenTransferFromStore I },
        tokenTransferFromAfterBalance evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := tokenTransferFromStore_balance I)
    (her := tokenTransferFromEvalBalanceRef (tokenTransferFromAfterAllowance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      tokenTransferFromBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [tokenTransferFromAfterBalance, tokenTransferFromBalanceSlot,
    tokenTransferFromAfterAllowance_codeOwner evm I] using
    tokenStorageLocStore_uint256 (tokenTransferFromAfterAllowance evm I)
      (tokenTransferFromBalanceSlot I) (tokenTransferFromBalanceDebitWord evm I)

theorem tokenTransferFromNewToWord_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : tokenTransferFromNewToNat evm I < UInt256.size) :
    (tokenTransferFromNewToWord evm I).toNat = tokenTransferFromNewToNat evm I := by
  unfold tokenTransferFromNewToWord
  exact ulit_toNat' _ hfit

theorem tokenTransferFromEvalCredit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hfit : tokenTransferFromNewToNat evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I }
      (tokenTransferFromAfterBalance evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .ok (.int (Int.ofNat (tokenTransferFromNewToNat evm I))) := by
  have hload := tokenTransferFromEvalToBalance (tokenTransferFromAfterBalance evm I) I
  rw [tokenTransferFromAfterBalance_codeOwner evm I] at hload
  exact tokenEvalCheckedAdd_ok hload
    (tokenTransferFromEvalValue (tokenTransferFromAfterBalance evm I) I) hfit

theorem tokenTransferFromEvalCredit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ tokenTransferFromNewToNat evm I) :
    evalExpr? config { contract := contract, locals := tokenTransferFromStore I }
      (tokenTransferFromAfterBalance evm I)
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")) =
        .revert := by
  have hload := tokenTransferFromEvalToBalance (tokenTransferFromAfterBalance evm I) I
  rw [tokenTransferFromAfterBalance_codeOwner evm I] at hload
  exact tokenEvalCheckedAdd_revert hload
    (tokenTransferFromEvalValue (tokenTransferFromAfterBalance evm I) I) hover

theorem tokenTransferFromAssignTo (evm : EVM.State) (I : ExecutionEnv)
    (hfit : tokenTransferFromNewToNat evm I < UInt256.size) :
    assignStorageRef? config { contract := contract, locals := tokenTransferFromStore I }
      (tokenTransferFromAfterBalance evm I) .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat (tokenTransferFromNewToNat evm I))) =
      .ok ({ contract := contract, locals := tokenTransferFromStore I },
        tokenTransferFromPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := tokenTransferFromStore_balance I)
    (her := tokenTransferFromEvalToRef (tokenTransferFromAfterBalance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      tokenTransferFromToRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [tokenTransferFromPostState, tokenTransferFromAfterBalance_codeOwner evm I,
    tokenTransferFromToSlot, tokenTransferFromNewToWord_toNat evm I hfit] using
    tokenStorageLocStore_uint256 (tokenTransferFromAfterBalance evm I)
      (tokenTransferFromToSlot I) (tokenTransferFromNewToWord evm I)

theorem tokenTransferFromAllowanceStep_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : tokenTransferFromShouldSpend evm I = true →
      (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromAllowanceWord evm I).toNat) :
    ExecStmt config { contract := contract, locals := tokenTransferFromStore I } evm
      (.ite
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256)))
        [.assign .storage (allowanceRef (.var "from") sender)
          (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value"))] [])
      (.ok { contract := contract, locals := tokenTransferFromStore I }
        (tokenTransferFromAfterAllowance evm I)) := by
  by_cases hspend : tokenTransferFromShouldSpend evm I = true
  · have hcond : evalExpr? config
        { contract := contract, locals := tokenTransferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256))) = .ok (.bool true) := by
      rw [tokenTransferFromEvalCond' evm I hsrc, hspend]
    have hassign := tokenTransferFromAssignAllowance evm I hsrc
    rw [tokenTransferFromAllowanceDebitWord_toNat evm I] at hassign
    have hthen : ExecBlock config { contract := contract, locals := tokenTransferFromStore I }
        evm [.assign .storage (allowanceRef (.var "from") sender)
          (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value"))]
        (.ok { contract := contract, locals := tokenTransferFromStore I }
          (tokenTransferFromAfterAllowance evm I)) := by
      simpa [tokenTransferFromAfterAllowance, hspend] using
        (ExecBlock.consNormal
          (ExecStmt.assign
            (tokenTransferFromEvalAllowanceDebit_ok evm I hsrc (hle hspend)) hassign)
          ExecBlock.nil)
    exact ExecStmt.iteTrue hcond hthen
  · have hfalse : tokenTransferFromShouldSpend evm I = false := by
      cases h : tokenTransferFromShouldSpend evm I <;> simp_all
    have hcond : evalExpr? config
        { contract := contract, locals := tokenTransferFromStore I } evm
        (.binary .and
          (.binary .ne (.var "from") sender)
          (.binary .ne (.storage (allowanceRef (.var "from") sender))
            (.intLit maxUint256))) = .ok (.bool false) := by
      rw [tokenTransferFromEvalCond' evm I hsrc, hfalse]
    simpa [tokenTransferFromAfterAllowance, hfalse] using
      (ExecStmt.iteFalse hcond (ExecBlock.nil :
        ExecBlock config { contract := contract, locals := tokenTransferFromStore I }
          evm [] (.ok { contract := contract, locals := tokenTransferFromStore I } evm)))

theorem tokenTransferFromBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : tokenTransferFromShouldSpend evm I = true →
      (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromAllowanceWord evm I).toNat)
    (hbalance : (tokenTransferFromValueWord I).toNat ≤
      (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat)
    (hfit : tokenTransferFromNewToNat evm I < UInt256.size) :
    ExecTransitionBody config contract evm (tokenTransferFromStore I)
      transferFromTransition.body
      (.returned { contract := contract, locals := tokenTransferFromStore I }
        (tokenTransferFromPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (tokenTransferFromAllowanceStep_ok evm I hsrc hallow) ?_
  have hassign := tokenTransferFromAssignBalance evm I
  rw [tokenTransferFromBalanceDebitWord_toNat evm I] at hassign
  refine ExecBlock.consNormal
    (ExecStmt.assign (tokenTransferFromEvalBalanceDebit_ok evm I hbalance) hassign) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (tokenTransferFromEvalCredit_ok evm I hfit)
      (tokenTransferFromAssignTo evm I hfit)) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem tokenTransferFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hspend : tokenTransferFromShouldSpend evm I = true)
    (hunder : (tokenTransferFromAllowanceWord evm I).toNat <
      (tokenTransferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (tokenTransferFromStore I)
      transferFromTransition.body .reverted := by
  have hcond : evalExpr? config
      { contract := contract, locals := tokenTransferFromStore I } evm
      (.binary .and
        (.binary .ne (.var "from") sender)
        (.binary .ne (.storage (allowanceRef (.var "from") sender))
          (.intLit maxUint256))) = .ok (.bool true) := by
    rw [tokenTransferFromEvalCond' evm I hsrc, hspend]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.iteTrue hcond <|
        ExecBlock.consRevert (ExecStmt.assignExprRevert
          (tokenTransferFromEvalAllowanceDebit_revert evm I hsrc hunder)))

theorem tokenTransferFromBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : tokenTransferFromShouldSpend evm I = true →
      (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromAllowanceWord evm I).toNat)
    (hunder : (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat <
      (tokenTransferFromValueWord I).toNat) :
    ExecTransitionBody config contract evm (tokenTransferFromStore I)
      transferFromTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (tokenTransferFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (tokenTransferFromEvalBalanceDebit_revert evm I hunder))

theorem tokenTransferFromBodyReverts_credit (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : tokenTransferFromShouldSpend evm I = true →
      (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromAllowanceWord evm I).toNat)
    (hbalance : (tokenTransferFromValueWord I).toNat ≤
      (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evm I) I).toNat)
    (hover : UInt256.size ≤ tokenTransferFromNewToNat evm I) :
    ExecTransitionBody config contract evm (tokenTransferFromStore I)
      transferFromTransition.body .reverted := by
  have hassign := tokenTransferFromAssignBalance evm I
  rw [tokenTransferFromBalanceDebitWord_toNat evm I] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (tokenTransferFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consNormal
          (ExecStmt.assign (tokenTransferFromEvalBalanceDebit_ok evm I hbalance) hassign) <|
          ExecBlock.consRevert
            (ExecStmt.assignExprRevert (tokenTransferFromEvalCredit_revert evm I hover))


theorem tokenTransferFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3130⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨253⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨248⟩, swap2, swap1, push2 ⟨3130⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem tokenTransferFromX_dec5470_from {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3166⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    simpa using (solcCalldataStaticLenCheckOk (words := 3)
      (sz := I.calldata.size) (by omega) hszhi hsize)
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨3153⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3166⟩, dup7, dup3, dup8, add, push2 ⟨2906⟩,
    jump (by jump_dest) ]⟩

theorem tokenTransferFromX_dec5792 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3166⟩
      [tokenTransferFromFromWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5470_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.tokenDecodeAddrOk rd hcanonFrom (by jump_dest) (by evm_ov)

theorem tokenTransferFromX_dec5470_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨3183⟩, ⟨32⟩,
        ⟨0⟩, ⟨0⟩, tokenTransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5792 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨3183⟩,
    dup7, dup3, dup8, add, push2 ⟨2906⟩, jump (by jump_dest) ]⟩

theorem tokenTransferFromX_dec5809 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3183⟩
      [tokenTransferFromToWord I, ⟨32⟩, ⟨0⟩, ⟨0⟩,
        tokenTransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5470_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.tokenDecodeAddrOk rd hcanonTo (by jump_dest) (by evm_ov)

theorem tokenTransferFromX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [⟨4⟩ + ⟨64⟩, UInt256.ofNat I.calldata.size, ⟨3200⟩, ⟨64⟩,
        ⟨0⟩, tokenTransferFromToWord I, tokenTransferFromFromWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨248⟩, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5809 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨3200⟩,
    dup7, dup3, dup8, add, push2 ⟨2957⟩, jump (by jump_dest) ]⟩

theorem tokenTransferFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨756⟩
      [tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5521_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  obtain ⟨_, _, rd5826⟩ := RD.tokenDecodeUint256Ok rd (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5826 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, pop, swap3,
    jump (by jump_dest), jumpdest, push2 ⟨756⟩, jump (by jump_dest) ]⟩


theorem tokenTransferFromX_self_to_balance {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hself : tokenTransferFromFromWord I = solcSourceWord I)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1801⟩ := tokenTransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (tokenTransferFromFromWord I) =
      tokenTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd1851₀ := evm_run rd1801 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup5, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd1851 := rd1851₀
  rw [hsourceClean, hfromClean, hself] at rd1851
  have hzero : UInt256.isZero (UInt256.eq (solcSourceWord I) (solcSourceWord I)) =
      ⟨0⟩ := by rw [uInt256_eq_self]; decide
  rw [hzero] at rd1851
  have rd2276 := evm_run rd1851 with [
    iszero, push2 ⟨969⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, iszero, push2 ⟨1231⟩, jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, by simpa [hself] using rd2276⟩

def tokenTransferFromAllowanceOuterSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨2⟩ (tokenTransferFromFromWord I)

noncomputable def tokenTransferFromAllowanceOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tokenTransferFromFromWord I) ⟨2⟩ solcFreePtrMem

noncomputable def tokenTransferFromAllowanceMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (tokenTransferFromAllowanceOuterSlot I)
    (tokenTransferFromAllowanceOuterMem I)

def tokenTransferFromMaxWord : UInt256 :=
  ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩

theorem tokenTransferFromX_nonself_allowanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨967⟩
      [solcSlotWord σ I (tokenTransferFromAllowanceSlot I), tokenTransferFromMaxWord,
        ⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1801⟩ := tokenTransferFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hcanonTo hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (tokenTransferFromFromWord I) =
      tokenTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hneqWord : UInt256.eq (tokenTransferFromFromWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hne (uInt256_eq_one_eq he))
  have rd1851₀ := evm_run rd1801 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup5, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd1851 := rd1851₀
  rw [hsourceClean, hfromClean, hneqWord] at rd1851
  have rd1858 := evm_run rd1851 with [
    iszero, push2 ⟨969⟩, jumpiNT (by decide),
    pop ]
  have rd1891 := rd1858.pushConst tokenTransferFromMaxWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1939₀ := evm_run rd1891 with [
    push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1939 := rd1939₀
  rw [hfromClean, hfromClean] at rd1939
  obtain ⟨_, _, rd1952⟩ := RD.tokenMappingHashSuffix rd1939 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromAllowanceOuterMem,
      tokenTransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (tokenTransferFromFromWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1939'₀ := evm_run rd1952 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1939' := rd1939'₀
  rw [hsourceClean, hsourceClean] at rd1939'
  have hmem : (tokenTransferFromAllowanceOuterMem I).size = 96 := by
    unfold tokenTransferFromAllowanceOuterMem
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2011⟩ := RD.tokenMappingHashSuffix rd1939' token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromAllowanceMem,
      tokenTransferFromAllowanceOuterSlot,
      tokenTransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (tokenTransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2012⟩ := rd2011.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2012⟩

theorem tokenTransferFromX_max_to_balance {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hmax : solcSlotWord σ I (tokenTransferFromAllowanceSlot I) =
      tokenTransferFromMaxWord)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2012₀⟩ := tokenTransferFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz100 hsize hszhi
    hcanonFrom hcanonTo hne hreach
  have rd2012 := rd2012₀
  rw [hmax] at rd2012
  exact ⟨_, _, evm_run rd2012 with [
    eq, iszero, jumpdest, iszero, push2 ⟨1231⟩,
    jumpiT (by decide) (by jump_dest) ]⟩

theorem tokenTransferFromX_spend_start {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (tokenTransferFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨975⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2012₀⟩ := tokenTransferFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz100 hsize hszhi
    hcanonFrom hcanonTo hne hreach
  have hneqWord : UInt256.eq (solcSlotWord σ I (tokenTransferFromAllowanceSlot I))
      tokenTransferFromMaxWord = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnotmax (uInt256_eq_one_eq he))
  have rd2013 := evm_run rd2012₀ with [eq]
  rw [hneqWord] at rd2013
  exact ⟨_, _, evm_run rd2013 with [
    iszero, jumpdest, iszero, push2 ⟨1231⟩,
    jumpiNT (by decide) ]⟩

noncomputable def tokenTransferFromAllowanceReadOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tokenTransferFromFromWord I) ⟨2⟩ (tokenTransferFromAllowanceMem I)

noncomputable def tokenTransferFromAllowanceReadMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (tokenTransferFromAllowanceOuterSlot I)
    (tokenTransferFromAllowanceReadOuterMem I)

theorem tokenTransferFromX_spend_load {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (tokenTransferFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1097⟩
      [solcSlotWord σ I (tokenTransferFromAllowanceSlot I),
        tokenTransferFromValueWord I, ⟨0⟩, tokenTransferFromValueWord I,
        tokenTransferFromToWord I, tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2020⟩ := tokenTransferFromX_spend_start (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have hfromClean : UInt256.land solcAddrMask (tokenTransferFromFromWord I) =
      tokenTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd2069₀ := evm_run rd2020 with [
    dup2, push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2069 := rd2069₀
  rw [hfromClean, hfromClean] at rd2069
  have hmem : (tokenTransferFromAllowanceMem I).size = 96 := by
    unfold tokenTransferFromAllowanceMem tokenTransferFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2082⟩ := RD.tokenMappingHashSuffix rd2069 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromAllowanceReadOuterMem,
      tokenTransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (tokenTransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2128₀ := evm_run rd2082 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2128 := rd2128₀
  rw [hsourceClean, hsourceClean] at rd2128
  have hmem2 : (tokenTransferFromAllowanceReadOuterMem I).size = 96 := by
    unfold tokenTransferFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2141⟩ := RD.tokenMappingHashSuffix rd2128 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromAllowanceReadMem,
      tokenTransferFromAllowanceOuterSlot,
      tokenTransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (tokenTransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2142⟩ := rd2141.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2142⟩

theorem tokenTransferFromX_spend_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (tokenTransferFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σ I (tokenTransferFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1106⟩
      [UInt256.sub (solcSlotWord σ I (tokenTransferFromAllowanceSlot I))
        (tokenTransferFromValueWord I), ⟨0⟩, tokenTransferFromValueWord I,
        tokenTransferFromToWord I, tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2142⟩ := tokenTransferFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have rd6645 := evm_run rd2142 with [
    push2 ⟨1106⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem tokenTransferFromX_spend_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (tokenTransferFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hunder : (solcSlotWord σ I (tokenTransferFromAllowanceSlot I)).toNat <
      (tokenTransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2142⟩ := tokenTransferFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hreach
  have rd6645 := evm_run rd2142 with [
    push2 ⟨1106⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubUnderflow rd6645 hunder (by evm_ov)

noncomputable def tokenTransferFromAllowanceStoreOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (tokenTransferFromFromWord I) ⟨2⟩ (tokenTransferFromAllowanceReadMem I)

noncomputable def tokenTransferFromAllowanceStoreMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (tokenTransferFromAllowanceOuterSlot I)
    (tokenTransferFromAllowanceStoreOuterMem I)

def tokenTransferFromEvmAllowanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (tokenTransferFromAllowanceSlot I)
    (UInt256.sub (solcSlotWord σ I (tokenTransferFromAllowanceSlot I))
      (tokenTransferFromValueWord I))

theorem tokenTransferFromX_spend_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hne : tokenTransferFromFromWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (tokenTransferFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σ I (tokenTransferFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromAllowanceStoreMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, tokenTransferFromEvmAllowanceMap σ I) k C := by
  obtain ⟨_, _, rd2151⟩ := tokenTransferFromX_spend_debit (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz100 hsize hszhi hcanonFrom hcanonTo hne hnotmax hle hreach
  have hfromClean : UInt256.land solcAddrMask (tokenTransferFromFromWord I) =
      tokenTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd2200₀ := evm_run rd2151 with [
    jumpdest, push1 ⟨2⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2200 := rd2200₀
  rw [hfromClean, hfromClean] at rd2200
  have hmem : (tokenTransferFromAllowanceReadMem I).size = 96 := by
    unfold tokenTransferFromAllowanceReadMem tokenTransferFromAllowanceReadOuterMem
      tokenTransferFromAllowanceMem tokenTransferFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2213⟩ := RD.tokenMappingHashSuffix rd2200 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromAllowanceStoreOuterMem,
      tokenTransferFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (tokenTransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2259₀ := evm_run rd2213 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2259 := rd2259₀
  rw [hsourceClean, hsourceClean] at rd2259
  have hmem2 : (tokenTransferFromAllowanceStoreOuterMem I).size = 96 := by
    unfold tokenTransferFromAllowanceStoreOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2272⟩ := RD.tokenMappingHashSuffix rd2259 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromAllowanceStoreMem,
      tokenTransferFromAllowanceOuterSlot,
      tokenTransferFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (tokenTransferFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2274 := evm_run rd2272 with [dup2, swap1]
  obtain ⟨_, _, rd2275⟩ := rd2274.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [tokenTransferFromEvmAllowanceMap] using
    (evm_run rd2275 with [pop])⟩

noncomputable def tokenTransferFromBalanceReadMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (tokenTransferFromFromWord I) ⟨1⟩ mem

def tokenTransferFromEvmBalanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (tokenTransferFromBalanceSlot I)
    (UInt256.sub (solcSlotWord σ I (tokenTransferFromBalanceSlot I))
      (tokenTransferFromValueWord I))

noncomputable def tokenTransferFromBalanceStoreMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (tokenTransferFromFromWord I) ⟨1⟩
    (tokenTransferFromBalanceReadMem I mem)

noncomputable def tokenTransferFromToReadMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (tokenTransferFromToWord I) ⟨1⟩
    (tokenTransferFromBalanceStoreMem I mem)

noncomputable def tokenTransferFromToStoreMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (tokenTransferFromToWord I) ⟨1⟩
    (tokenTransferFromToReadMem I mem)

def tokenTransferFromEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (tokenTransferFromEvmBalanceMap σ I)
    (tokenTransferFromToSlot I)
    (solcSlotWord (tokenTransferFromEvmBalanceMap σ I) I
      (tokenTransferFromToSlot I) + tokenTransferFromValueWord I)

theorem tokenTransferFromX_balance_load {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1295⟩
      [solcSlotWord σA I (tokenTransferFromBalanceSlot I),
        tokenTransferFromValueWord I, ⟨0⟩, tokenTransferFromValueWord I,
        tokenTransferFromToWord I, tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromBalanceReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σA) k C := by
  obtain ⟨_, _, rd2276⟩ := hreach
  have hfromClean : UInt256.land solcAddrMask (tokenTransferFromFromWord I) =
      tokenTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd2326₀ := evm_run rd2276 with [
    jumpdest, dup2, push1 ⟨1⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2326 := rd2326₀
  rw [hfromClean, hfromClean] at rd2326
  obtain ⟨_, _, rd2339⟩ := RD.tokenMappingHashSuffix rd2326 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromBalanceReadMem,
      tokenTransferFromBalanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tokenTransferFromFromWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2340⟩ := rd2339.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2340⟩

theorem tokenTransferFromX_balance_debit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1304⟩
      [UInt256.sub (solcSlotWord σA I (tokenTransferFromBalanceSlot I))
        (tokenTransferFromValueWord I), ⟨0⟩, tokenTransferFromValueWord I,
        tokenTransferFromToWord I, tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromBalanceReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σA) k C := by
  obtain ⟨_, _, rd2340⟩ := tokenTransferFromX_balance_load hcanonFrom hmem hreach
  have rd6645 := evm_run rd2340 with [
    push2 ⟨1304⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem tokenTransferFromX_balance_underflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hunder : (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat <
      (tokenTransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2340⟩ := tokenTransferFromX_balance_load hcanonFrom hmem hreach
  have rd6645 := evm_run rd2340 with [
    push2 ⟨1304⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubUnderflow rd6645 hunder (by evm_ov)

theorem tokenTransferFromX_balance_stored {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1370⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromBalanceStoreMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, tokenTransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd2349⟩ := tokenTransferFromX_balance_debit hcanonFrom hmem hle hreach
  have hfromClean : UInt256.land solcAddrMask (tokenTransferFromFromWord I) =
      tokenTransferFromFromWord I := solcAddrMask_clean_left hcanonFrom
  have rd2398₀ := evm_run rd2349 with [
    jumpdest, push1 ⟨1⟩, push0, dup7,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2398 := rd2398₀
  rw [hfromClean, hfromClean] at rd2398
  have hmem2 : (tokenTransferFromBalanceReadMem I mem).size = 96 := by
    unfold tokenTransferFromBalanceReadMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2411⟩ := RD.tokenMappingHashSuffix rd2398 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromBalanceStoreMem,
      tokenTransferFromBalanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tokenTransferFromFromWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2413 := evm_run rd2411 with [dup2, swap1]
  obtain ⟨_, _, rd2414⟩ := rd2413.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [tokenTransferFromEvmBalanceMap] using
    (evm_run rd2414 with [pop])⟩

theorem tokenTransferFromX_toBalance_load {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1433⟩
      [solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
        (tokenTransferFromToSlot I), tokenTransferFromValueWord I,
        ⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromToReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, tokenTransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd2415⟩ := tokenTransferFromX_balance_stored hperm hcanonFrom hmem
    hle hreach
  have htoClean : UInt256.land solcAddrMask (tokenTransferFromToWord I) =
      tokenTransferFromToWord I := solcAddrMask_clean_left hcanonTo
  have rd2464₀ := evm_run rd2415 with [
    dup2, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2464 := rd2464₀
  rw [htoClean, htoClean] at rd2464
  have hmem2 : (tokenTransferFromBalanceStoreMem I mem).size = 96 := by
    unfold tokenTransferFromBalanceStoreMem tokenTransferFromBalanceReadMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2477⟩ := RD.tokenMappingHashSuffix rd2464 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromToReadMem,
      tokenTransferFromToSlot_eq_solc I hcanonTo] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tokenTransferFromToWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2478⟩ := rd2477.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2478⟩

theorem tokenTransferFromX_credit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
      (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1442⟩
      [solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I (tokenTransferFromToSlot I) +
        tokenTransferFromValueWord I, ⟨0⟩, tokenTransferFromValueWord I,
        tokenTransferFromToWord I, tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromToReadMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, tokenTransferFromEvmBalanceMap σA I) k C := by
  obtain ⟨_, _, rd2478⟩ := tokenTransferFromX_toBalance_load hperm hcanonFrom
    hcanonTo hmem hle hreach
  have rd6696 := evm_run rd2478 with [
    push2 ⟨1442⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedAddOk rd6696 hfit (by jump_dest) (by evm_ov)

theorem tokenTransferFromX_overflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hover : UInt256.size ≤ (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
      (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2478⟩ := tokenTransferFromX_toBalance_load hperm hcanonFrom
    hcanonTo hmem hle hreach
  have rd6696 := evm_run rd2478 with [
    push2 ⟨1442⟩, swap2, swap1, push2 ⟨3516⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedAddOverflow rd6696 hover (by evm_ov)

theorem tokenTransferFromX_toBalance_stored {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
      (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1508⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      (tokenTransferFromToStoreMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, tokenTransferFromEvmPostMap σA I) k C := by
  obtain ⟨_, _, rd2487⟩ := tokenTransferFromX_credit hperm hcanonFrom hcanonTo
    hmem hle hfit hreach
  have htoClean : UInt256.land solcAddrMask (tokenTransferFromToWord I) =
      tokenTransferFromToWord I := solcAddrMask_clean_left hcanonTo
  have rd2536₀ := evm_run rd2487 with [
    jumpdest, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2536 := rd2536₀
  rw [htoClean, htoClean] at rd2536
  have hmem2 : (tokenTransferFromToReadMem I mem).size = 96 := by
    unfold tokenTransferFromToReadMem tokenTransferFromBalanceStoreMem
      tokenTransferFromBalanceReadMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2549⟩ := RD.tokenMappingHashSuffix rd2536 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [tokenTransferFromToStoreMem,
      tokenTransferFromToSlot_eq_solc I hcanonTo] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (tokenTransferFromToWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2551 := evm_run rd2549 with [dup2, swap1]
  obtain ⟨_, _, rd2552⟩ := rd2551.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [tokenTransferFromEvmPostMap] using
    (evm_run rd2552 with [pop])⟩

theorem tokenTransferFromToStoreMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) : (tokenTransferFromToStoreMem I mem).size = 96 := by
  unfold tokenTransferFromToStoreMem tokenTransferFromToReadMem
    tokenTransferFromBalanceStoreMem tokenTransferFromBalanceReadMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ hmem

theorem tokenTransferFromToStoreMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (tokenTransferFromToStoreMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold tokenTransferFromToStoreMem tokenTransferFromToReadMem
    tokenTransferFromBalanceStoreMem tokenTransferFromBalanceReadMem
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ hmem)))
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _
    (twoWordHashMem_size_96 _ _ hmem))
  apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ hmem)
  exact twoWordHashMem_read64 _ _ hmem hread

theorem tokenX_transferFrom_tail {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {sel : UInt256} {mem : ByteArray}
    (hperm : I.perm = true)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat)
    (hfit : (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
      (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, tokenTransferFromEvmPostMap σA I)
      (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd2553⟩ := tokenTransferFromX_toBalance_stored hperm hcanonFrom
    hcanonTo hmem hle hfit hreach
  have rd292 := evm_run rd2553 with [
    push1 ⟨1⟩, swap1, pop, swap4, swap3, pop, pop, pop, jump (by jump_dest) ]
  have hmemFinal := tokenTransferFromToStoreMem_size I hmem
  have hreadFinal := tokenTransferFromToStoreMem_read64 I hmem hread
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (tokenTransferFromToStoreMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((tokenTransferFromToStoreMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmemFinal]; decide) (by decide) hreadFinal
  have rd5629 := evm_run rd292 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨266⟩, swap2, swap1, push2 ⟨3065⟩, jump (by jump_dest) ]
  obtain ⟨_, _, rd305⟩ := RD.tokenRoutineEncodeBoolFromMem
    (memout := tokenWordReturnMem (tokenTransferFromToStoreMem I mem) (⟨1⟩ : UInt256))
    rd5629 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd305 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (tokenWordReturnMem_mload64_of_size96 ⟨1⟩ hmemFinal hreadFinal)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (⟨1⟩ : UInt256)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
        exact tokenWordReturnMem_read128_of_size96 ⟨1⟩ hmemFinal)
      (by evm_ov) ]


theorem tokenTransferFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using (solcCalldataStaticLenCheckShort (words := 3)
      (sz := I.calldata.size) hsz4 (by omega) hsize (by norm_num))
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨3153⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨3152⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem tokenTransferFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    simpa using (solcCalldataStaticLenCheckHuge (words := 3)
      (sz := I.calldata.size) hbig hsize (by norm_num))
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨3153⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨3152⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem tokenTransferFromX_noncanonFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (tokenTransferFromFromWord I)
      (UInt256.land (tokenTransferFromFromWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5470_from (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)

theorem tokenTransferFromX_noncanonTo {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hnc : UInt256.eq (tokenTransferFromToWord I)
      (UInt256.land (tokenTransferFromToWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨227⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := tokenTransferFromX_dec5470_to (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hcanonFrom hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)

theorem tokenTransferFromSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_transferFrom {cd : ByteArray}
    (hsel : ((⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some transferFromTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition, burnFromTransition, mintTransition,
      totalSupplyTransition, transferTransition])
    (post := [])
    rfl rfl ?_ (by rw [selectorOf, transferFromSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, allowanceSelectorBytes, hcd]
    | rw [selectorOf, approveSelectorBytes, hcd]
    | rw [selectorOf, balanceOfSelectorBytes, hcd]
    | rw [selectorOf, burnSelectorBytes, hcd]
    | rw [selectorOf, burnFromSelectorBytes, hcd]
    | rw [selectorOf, mintSelectorBytes, hcd]
    | rw [selectorOf, totalSupplySelectorBytes, hcd]
    | rw [selectorOf, transferSelectorBytes, hcd]
  all_goals decide

theorem tokenTransferFromFromWord_eq_source_iff (I : ExecutionEnv)
    (hcanon : (tokenTransferFromFromWord I).toNat < EVM.addressModulus) :
    tokenTransferFromFromWord I = solcSourceWord I ↔
      AccountAddress.ofNat (tokenTransferFromFromWord I).toNat = I.source := by
  constructor
  · intro h
    rw [h]
    exact solcSource_ofNat I
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    change (tokenTransferFromFromWord I).toNat % AccountAddress.size = I.source.val at hv
    have hcanon' : (tokenTransferFromFromWord I).toNat < AccountAddress.size := hcanon
    rw [Nat.mod_eq_of_lt hcanon'] at hv
    rw [solcSourceWord_toNat]
    exact hv

theorem tokenTransferFromMaxWord_toNat :
    tokenTransferFromMaxWord.toNat = Int.toNat maxUint256 := by
  native_decide

theorem tokenTransferFromAllowanceValue_eq_max_iff (w : UInt256) :
    Value.int (Int.ofNat w.toNat) = .int maxUint256 ↔
      w = tokenTransferFromMaxWord := by
  constructor
  · intro h
    have hnat : w.toNat = tokenTransferFromMaxWord.toNat := by
      have hi : Int.ofNat w.toNat = maxUint256 := by
        injection h with hi
      rw [tokenTransferFromMaxWord_toNat]
      exact congrArg Int.toNat hi
    exact u256_inj hnat
  · intro h
    rw [h]
    native_decide

theorem tokenTransferFromShouldSpend_iff (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (tokenTransferFromFromWord I).toNat < EVM.addressModulus) :
    tokenTransferFromShouldSpend evm I = true ↔
      tokenTransferFromFromWord I ≠ solcSourceWord I ∧
        tokenTransferFromAllowanceWord evm I ≠ tokenTransferFromMaxWord := by
  rw [tokenTransferFromShouldSpend]
  simp only [Bool.and_eq_true, Bool.not_eq_true]
  constructor
  · rintro ⟨hfrom, hallow⟩
    constructor
    · intro he
      have hv := (tokenTransferFromFromWord_eq_source_iff I hcanon).mp he
      simp [tokenTransferFromFromValue, BEq.beq, hv] at hfrom
    · intro he
      have hv := (tokenTransferFromAllowanceValue_eq_max_iff _).mpr he
      have hi : Int.ofNat (tokenTransferFromAllowanceWord evm I).toNat =
          maxUint256 := by injection hv with hi
      simp [BEq.beq] at hallow
      exact hallow hi
  · rintro ⟨hfrom, hallow⟩
    constructor
    · have hv : AccountAddress.ofNat (tokenTransferFromFromWord I).toNat ≠
          I.source := fun he => hfrom ((tokenTransferFromFromWord_eq_source_iff I hcanon).mpr he)
      simp [tokenTransferFromFromValue, BEq.beq, hv]
    · have hv : Value.int (Int.ofNat (tokenTransferFromAllowanceWord evm I).toNat) ≠
          .int maxUint256 := fun he => hallow ((tokenTransferFromAllowanceValue_eq_max_iff _).mp he)
      simp [BEq.beq]
      intro hi
      exact hv (congrArg Value.int hi)

theorem tokenTransferFromAllowanceMem_size (I : ExecutionEnv) :
    (tokenTransferFromAllowanceMem I).size = 96 := by
  unfold tokenTransferFromAllowanceMem tokenTransferFromAllowanceOuterMem
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size

theorem tokenTransferFromAllowanceMem_read64 (I : ExecutionEnv) :
    (tokenTransferFromAllowanceMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold tokenTransferFromAllowanceMem tokenTransferFromAllowanceOuterMem
  apply twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem tokenTransferFromAllowanceStoreMem_size (I : ExecutionEnv) :
    (tokenTransferFromAllowanceStoreMem I).size = 96 := by
  unfold tokenTransferFromAllowanceStoreMem tokenTransferFromAllowanceStoreOuterMem
    tokenTransferFromAllowanceReadMem tokenTransferFromAllowanceReadOuterMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ (tokenTransferFromAllowanceMem_size I)

theorem tokenTransferFromAllowanceStoreMem_read64 (I : ExecutionEnv) :
    (tokenTransferFromAllowanceStoreMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [tokenTransferFromAllowanceStoreMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold tokenTransferFromAllowanceStoreOuterMem
    apply twoWordHashMem_size_96
    unfold tokenTransferFromAllowanceReadMem tokenTransferFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (tokenTransferFromAllowanceMem_size I))
  rw [tokenTransferFromAllowanceStoreOuterMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold tokenTransferFromAllowanceReadMem tokenTransferFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (tokenTransferFromAllowanceMem_size I))
  rw [tokenTransferFromAllowanceReadMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold tokenTransferFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ (tokenTransferFromAllowanceMem_size I))
  rw [tokenTransferFromAllowanceReadOuterMem]
  exact twoWordHashMem_read64 _ _ (tokenTransferFromAllowanceMem_size I)
    (tokenTransferFromAllowanceMem_read64 I)

theorem tokenTransferFromTailCore
    {cA gh bl σ_evm σ_solm σ₀ σA A I} {g : UInt256} {mem : ByteArray}
    (hcode : I.code = tokenBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hd : dispatchMsg contract I.calldata = some transferFromTransition)
    (hdec : decodeCalldata (transferFromTransition.params.map Param.name)
      (transitionSignature transferFromTransition).paramTypes I.calldata =
        some (tokenTransferFromStore I))
    (hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus)
    (hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus)
    (hallow : tokenTransferFromShouldSpend
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = true →
      (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromAllowanceWord
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hState : EVMStateEquiv
      (tokenTransferFromAfterAllowance
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
      (tokenTransferFromAfterAllowance
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I))
    (hmapA : (tokenTransferFromAfterAllowance
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap = σA)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1231⟩
      [⟨0⟩, tokenTransferFromValueWord I, tokenTransferFromToWord I,
        tokenTransferFromFromWord I, ⟨253⟩, tokenSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσA : EVMStateEquiv (tokenTransferFromAfterAllowance evmE I)
      (tokenTransferFromAfterAllowance evmS I) := hState
  have hmapA' : (tokenTransferFromAfterAllowance evmE I).accountMap = σA := hmapA
  have hbalanceE :
      tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmE I) I =
        solcSlotWord σA I (tokenTransferFromBalanceSlot I) := by
    unfold tokenTransferFromBalanceWord
    rw [tokenTransferFromAfterAllowance_codeOwner evmE I,
      show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
    simp only [Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWord, hmapA']
  have hbalanceS :
      tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmS I) I =
        solcSlotWord σA I (tokenTransferFromBalanceSlot I) := by
    rw [show tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmS I) I =
        tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmE I) I from
          (hσA.storageLoad_codeOwner (tokenTransferFromBalanceSlot I)).symm, hbalanceE]
  by_cases hle : (tokenTransferFromValueWord I).toNat ≤
      (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat
  · have hleE : (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmE I) I).toNat :=
      hbalanceE ▸ hle
    have hleS : (tokenTransferFromValueWord I).toNat ≤
        (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmS I) I).toNat :=
      hbalanceS ▸ hle
    have hdebit : tokenTransferFromBalanceDebitWord evmE I =
        tokenTransferFromBalanceDebitWord evmS I := by
      unfold tokenTransferFromBalanceDebitWord
      rw [hbalanceE, hbalanceS]
    have hσBalance : EVMStateEquiv
        (tokenTransferFromAfterBalance evmE I) (tokenTransferFromAfterBalance evmS I) := by
      unfold tokenTransferFromAfterBalance
      rw [← tokenTransferFromAfterAllowance_codeOwner evmE I,
        ← tokenTransferFromAfterAllowance_codeOwner evmS I]
      exact hσA.storageStore_codeOwner (tokenTransferFromBalanceSlot I) hdebit
    have hmapBalance : (tokenTransferFromAfterBalance evmE I).accountMap =
        tokenTransferFromEvmBalanceMap σA I := by
      unfold tokenTransferFromAfterBalance tokenTransferFromEvmBalanceMap
      rw [storageStore_accountMap,
        show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
        hmapA']
      apply congrArg (sstoreAccountMap I.codeOwner σA (tokenTransferFromBalanceSlot I))
      apply u256_inj
      rw [tokenTransferFromBalanceDebitWord_toNat evmE I,
        hbalanceE, usub_toNat hle]
    have htoE : tokenTransferFromToBalanceWord evmE I =
        solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
          (tokenTransferFromToSlot I) := by
      unfold tokenTransferFromToBalanceWord
      rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
      simp only [Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, solcSlotWord, hmapBalance]
    have htoS : tokenTransferFromToBalanceWord evmS I =
        solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
          (tokenTransferFromToSlot I) := by
      rw [show tokenTransferFromToBalanceWord evmS I =
          tokenTransferFromToBalanceWord evmE I from by
            unfold tokenTransferFromToBalanceWord
            rw [← tokenTransferFromAfterBalance_codeOwner evmE I,
              ← tokenTransferFromAfterBalance_codeOwner evmS I]
            exact (hσBalance.storageLoad_codeOwner (tokenTransferFromToSlot I)).symm,
        htoE]
    have hnewE : tokenTransferFromNewToNat evmE I =
        (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
          (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat := by
      rw [tokenTransferFromNewToNat, htoE]
    have hnewS : tokenTransferFromNewToNat evmS I =
        (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
          (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat := by
      rw [tokenTransferFromNewToNat, htoS]
    by_cases hfit : (solcSlotWord (tokenTransferFromEvmBalanceMap σA I) I
        (tokenTransferFromToSlot I)).toNat + (tokenTransferFromValueWord I).toNat <
        UInt256.size
    · have hfitE : tokenTransferFromNewToNat evmE I < UInt256.size :=
        hnewE ▸ hfit
      have hfitS : tokenTransferFromNewToNat evmS I < UInt256.size :=
        hnewS ▸ hfit
      have hnewWord : tokenTransferFromNewToWord evmE I =
          tokenTransferFromNewToWord evmS I := by
        unfold tokenTransferFromNewToWord
        rw [hnewE, hnewS]
      have hσPost : EVMStateEquiv
          (tokenTransferFromPostState evmE I) (tokenTransferFromPostState evmS I) := by
        change EVMStateEquiv
          (Solm.EVM.storageStore (tokenTransferFromAfterBalance evmE I)
            evmE.executionEnv.codeOwner (tokenTransferFromToSlot I)
            (tokenTransferFromNewToWord evmE I))
          (Solm.EVM.storageStore (tokenTransferFromAfterBalance evmS I)
            evmS.executionEnv.codeOwner (tokenTransferFromToSlot I)
            (tokenTransferFromNewToWord evmS I))
        exact hσBalance.storageStore rfl (tokenTransferFromToSlot I) hnewWord
      have hmapPost : (tokenTransferFromPostState evmE I).accountMap =
          tokenTransferFromEvmPostMap σA I := by
        unfold tokenTransferFromPostState tokenTransferFromEvmPostMap
        rw [storageStore_accountMap,
          show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
          hmapBalance]
        apply congrArg (sstoreAccountMap I.codeOwner
          (tokenTransferFromEvmBalanceMap σA I) (tokenTransferFromToSlot I))
        apply u256_inj
        rw [tokenTransferFromNewToWord_toNat evmE I hfitE, uadd_toNat,
          hnewE, Nat.mod_eq_of_lt hfit]
      have hbody := tokenTransferFromBodyReturns evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hfitS
      have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
          (some [(.bool true)]) transferFromTransition.returnType :=
        returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
      exact (tokenX_transferFrom_tail (g := Sat256.ofUInt256 g)
          hperm hcanonFrom hcanonTo hmem hread hle hfit hreach)
        |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
          (by
            have hcreatedA : (tokenTransferFromAfterAllowance evmE I).createdAccounts =
                cA := by
              unfold tokenTransferFromAfterAllowance
              split
              · simp [storageStore_createdAccounts, evmE, initState]
              · rfl
            rw [tokenTransferFromPostState, storageStore_createdAccounts,
              tokenTransferFromAfterBalance, storageStore_createdAccounts, hcreatedA])
          (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
    · have hover : UInt256.size ≤ tokenTransferFromNewToNat evmS I := by
        rw [hnewS]
        omega
      have hbody := tokenTransferFromBodyReverts_credit evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hover
      exact (tokenTransferFromX_overflow (g := Sat256.ofUInt256 g)
          hperm hcanonFrom hcanonTo hmem hle (by omega) hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hunder : (solcSlotWord σA I (tokenTransferFromBalanceSlot I)).toNat <
        (tokenTransferFromValueWord I).toNat := by omega
    have hunderS :
        (tokenTransferFromBalanceWord (tokenTransferFromAfterAllowance evmS I) I).toNat <
          (tokenTransferFromValueWord I).toNat := by rw [hbalanceS]; exact hunder
    have hbody := tokenTransferFromBodyReverts_balance evmS I
      (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hunderS
    exact (tokenTransferFromX_balance_underflow (g := Sat256.ofUInt256 g)
        hcanonFrom hmem hunder hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

/-- The transferFrom wrapper, entered at PC 266, refines its Solm transition. -/
theorem tokenTransferFromBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨227⟩ [tokenSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tokenTransferFromSelector_size hsel
  have hd := tokenDispatch_transferFrom (cd := I.calldata) hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (tokenTransferFromFromWord I).toNat < EVM.addressModulus
      · by_cases hcanonTo : (tokenTransferFromToWord I).toNat < EVM.addressModulus
        · have hdec := tokenDecode_transferFrom_ok (I := I) hsz100 hbig
            hcanonFrom hcanonTo
          let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hσ : EVMStateEquiv evmE evmS := by
            simpa [evmE, evmS] using
              EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
          have hallowWordE : tokenTransferFromAllowanceWord evmE I =
              solcSlotWord σ_evm I (tokenTransferFromAllowanceSlot I) := by
            simpa [tokenTransferFromAllowanceWord, solcSlotWord,
              codeOwnerStorageWord] using
              (codeOwnerStorageWord_initState
                (g := Sat256.ofUInt256 g) (σ := σ_evm)
                (slot := tokenTransferFromAllowanceSlot I) (cA := cA)
                (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
          have hallowWordS : tokenTransferFromAllowanceWord evmS I =
              solcSlotWord σ_evm I (tokenTransferFromAllowanceSlot I) := by
            rw [show tokenTransferFromAllowanceWord evmS I =
                tokenTransferFromAllowanceWord evmE I from
                  (hσ.storageLoad_codeOwner (tokenTransferFromAllowanceSlot I)).symm,
              hallowWordE]
          by_cases hself : tokenTransferFromFromWord I = solcSourceWord I
          · have hspendE : tokenTransferFromShouldSpend evmE I = false := by
              cases hs : tokenTransferFromShouldSpend evmE I with
              | false => rfl
              | true => exact False.elim (((tokenTransferFromShouldSpend_iff evmE I hcanonFrom).mp hs).1 hself)
            have hspendS : tokenTransferFromShouldSpend evmS I = false := by
              cases hs : tokenTransferFromShouldSpend evmS I with
              | false => rfl
              | true => exact False.elim (((tokenTransferFromShouldSpend_iff evmS I hcanonFrom).mp hs).1 hself)
            have hState : EVMStateEquiv
                (tokenTransferFromAfterAllowance evmE I)
                (tokenTransferFromAfterAllowance evmS I) := by
              simpa [tokenTransferFromAfterAllowance, hspendE, hspendS] using hσ
            have hmapA : (tokenTransferFromAfterAllowance evmE I).accountMap =
                σ_evm := by
              rw [tokenTransferFromAfterAllowance, hspendE]
              rfl
            exact tokenTransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
              hcanonTo (by intro hs; rw [hspendS] at hs; cases hs)
              hState hmapA solcFreePtrMem_size solcFreePtrMem_read64
              (tokenTransferFromX_self_to_balance (g := Sat256.ofUInt256 g)
                hsz100 hsize hbig hcanonFrom hcanonTo hself hreach)
          · by_cases hmax : solcSlotWord σ_evm I (tokenTransferFromAllowanceSlot I) =
                tokenTransferFromMaxWord
            · have hspendE : tokenTransferFromShouldSpend evmE I = false := by
                cases hs : tokenTransferFromShouldSpend evmE I with
                | false => rfl
                | true => exact False.elim (((tokenTransferFromShouldSpend_iff evmE I hcanonFrom).mp hs).2
                    (by rw [hallowWordE]; exact hmax))
              have hspendS : tokenTransferFromShouldSpend evmS I = false := by
                cases hs : tokenTransferFromShouldSpend evmS I with
                | false => rfl
                | true => exact False.elim (((tokenTransferFromShouldSpend_iff evmS I hcanonFrom).mp hs).2
                    (by rw [hallowWordS]; exact hmax))
              have hState : EVMStateEquiv
                  (tokenTransferFromAfterAllowance evmE I)
                  (tokenTransferFromAfterAllowance evmS I) := by
                simpa [tokenTransferFromAfterAllowance, hspendE, hspendS] using hσ
              have hmapA : (tokenTransferFromAfterAllowance evmE I).accountMap =
                  σ_evm := by
                rw [tokenTransferFromAfterAllowance, hspendE]
                rfl
              exact tokenTransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
                hcanonTo (by intro hs; rw [hspendS] at hs; cases hs)
                hState hmapA (tokenTransferFromAllowanceMem_size I)
                (tokenTransferFromAllowanceMem_read64 I)
                (tokenTransferFromX_max_to_balance (g := Sat256.ofUInt256 g)
                  hsz100 hsize hbig hcanonFrom hcanonTo hself hmax hreach)
            · have hspendE : tokenTransferFromShouldSpend evmE I = true :=
                (tokenTransferFromShouldSpend_iff evmE I hcanonFrom).mpr
                  ⟨hself, by rwa [hallowWordE]⟩
              have hspendS : tokenTransferFromShouldSpend evmS I = true :=
                (tokenTransferFromShouldSpend_iff evmS I hcanonFrom).mpr
                  ⟨hself, by rwa [hallowWordS]⟩
              by_cases hle : (tokenTransferFromValueWord I).toNat ≤
                  (solcSlotWord σ_evm I (tokenTransferFromAllowanceSlot I)).toNat
              · have hdebit : tokenTransferFromAllowanceDebitWord evmE I =
                    tokenTransferFromAllowanceDebitWord evmS I := by
                  unfold tokenTransferFromAllowanceDebitWord
                  rw [hallowWordE, hallowWordS]
                have hState : EVMStateEquiv
                    (tokenTransferFromAfterAllowance evmE I)
                    (tokenTransferFromAfterAllowance evmS I) := by
                  simp only [tokenTransferFromAfterAllowance, hspendE, hspendS,
                    if_true]
                  exact hσ.storageStore_codeOwner
                    (tokenTransferFromAllowanceSlot I) hdebit
                have hmapA : (tokenTransferFromAfterAllowance evmE I).accountMap =
                    tokenTransferFromEvmAllowanceMap σ_evm I := by
                  rw [tokenTransferFromAfterAllowance, if_pos hspendE,
                    storageStore_accountMap]
                  change sstoreAccountMap I.codeOwner σ_evm
                    (tokenTransferFromAllowanceSlot I)
                    (tokenTransferFromAllowanceDebitWord evmE I) = _
                  unfold tokenTransferFromEvmAllowanceMap
                  apply congrArg (sstoreAccountMap I.codeOwner σ_evm
                    (tokenTransferFromAllowanceSlot I))
                  apply u256_inj
                  rw [tokenTransferFromAllowanceDebitWord_toNat evmE I,
                    hallowWordE, usub_toNat hle]
                exact tokenTransferFromTailCore hcode hperm hwv hd hdec hcanonFrom
                  hcanonTo (by intro _; rwa [hallowWordS]) hState hmapA
                  (tokenTransferFromAllowanceStoreMem_size I)
                  (tokenTransferFromAllowanceStoreMem_read64 I)
                  (tokenTransferFromX_spend_stored (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hperm hcanonFrom hcanonTo hself hmax hle hreach)
              · have hunder : (solcSlotWord σ_evm I
                    (tokenTransferFromAllowanceSlot I)).toNat <
                    (tokenTransferFromValueWord I).toNat := by omega
                have hbody := tokenTransferFromBodyReverts_allowance evmS I
                  (by simp only [evmS, initState]; exact hwv) (by rfl) hspendS
                  (by rwa [hallowWordS])
                exact (tokenTransferFromX_spend_underflow (g := Sat256.ofUInt256 g)
                    hsz100 hsize hbig hcanonFrom hcanonTo hself hmax hunder hreach)
                  |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hdec := tokenDecode_transferFrom_none_noncanonTo
            (I := I) hsz100 hbig hcanonFrom hcanonTo
          have hnc : UInt256.eq (tokenTransferFromToWord I)
              (UInt256.land (tokenTransferFromToWord I) solcAddrMask) = ⟨0⟩ :=
            uInt256_eq_zero_of_ne (fun he => hcanonTo (solcAddrCanonical_of_clean he))
          exact (tokenTransferFromX_noncanonTo (g := Sat256.ofUInt256 g)
              hsz100 hsize hbig hcanonFrom hnc hreach)
            |>.reEquivDecodingFailed hcode hd hdec
      · have hdec := tokenDecode_transferFrom_none_noncanonFrom
          (I := I) hsz100 hbig hcanonFrom
        have hnc : UInt256.eq (tokenTransferFromFromWord I)
            (UInt256.land (tokenTransferFromFromWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonFrom (solcAddrCanonical_of_clean he))
        exact (tokenTransferFromX_noncanonFrom (g := Sat256.ofUInt256 g)
            hsz100 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_transferFrom_none_huge (I := I) hbigge
      exact (tokenTransferFromX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 100 := by omega
    have hdec := tokenDecode_transferFrom_none_short (I := I) hsz4 hshort
    exact (tokenTransferFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmmToken
