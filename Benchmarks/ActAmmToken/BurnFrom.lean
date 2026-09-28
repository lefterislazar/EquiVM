import Benchmarks.ActAmmToken.Mint
import Benchmarks.ActAmmToken.TransferFrom

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-! The `burnFrom` ABI entry proof. -/

namespace Benchmarks.ActAmmToken

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def burnFromAllowanceSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (.address (AccountAddress.ofNat (mintAccountWord I).toNat))
    (.address I.source)

theorem burnFromAllowanceSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus) :
    solcMappingSlot (solcMappingSlot ⟨2⟩ (mintAccountWord I))
      (solcSourceWord I) = burnFromAllowanceSlot I := by
  unfold burnFromAllowanceSlot allowanceSlot allowanceOwnerSlot mapSlot
    solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon,
    tokenSource_keyValueToWord I.source]

theorem mintStore_allowance (I : ExecutionEnv) :
    (mintStore I).get? "allowance" = none := by
  rw [mintStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

def burnFromAllowanceRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps :=
    [.mindex (.address (AccountAddress.ofNat (mintAccountWord I).toNat)),
      .mindex (.address I.source)] }

theorem burnFromEvalAllowanceRef (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := mintStore I } evm
      (allowanceRef (.var "account") sender) = .ok (burnFromAllowanceRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    allowanceRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, burnFromAllowanceRef, mintAccountValue,
    mintStore_account, sender, envValue, hsrc]

def burnFromAllowanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (burnFromAllowanceSlot I)

theorem burnFromEvalAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.storage (allowanceRef (.var "account") sender)) =
        .ok (.int (Int.ofNat (burnFromAllowanceWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := mintStore_allowance I)
    (her := burnFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      burnFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)]
  simp [burnFromAllowanceWord, burnFromAllowanceSlot,
    tokenStorageLocLoad_uint256]

theorem burnFromEvalFromNeSender (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .ne (.var "account") sender) =
        .ok (.bool (!(mintAccountValue I == .address I.source))) := by
  have hfrom : evalExpr? config
      { contract := contract, locals := mintStore I } evm (.var "account") =
      .ok (mintAccountValue I) := by
    simp only [evalExpr?, EvalResult.ofOption, mintStore_account]
  have hsender : evalExpr? config
      { contract := contract, locals := mintStore I } evm sender =
      .ok (.address I.source) := by
    simp [sender, evalExpr?, envValue, hsrc, pure]
  simp [evalExpr?, EvalResult.bind, bind, hfrom, hsender, evalBinaryOp?]

theorem burnFromEvalAllowanceNeMax (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .ne (.storage (allowanceRef (.var "account") sender))
        (.intLit maxUint256)) =
      .ok (.bool (!(Value.int (Int.ofNat
        (burnFromAllowanceWord evm I).toNat) == .int maxUint256))) := by
  have hallow := burnFromEvalAllowance evm I hsrc
  simp [evalExpr?, EvalResult.bind, bind, hallow, evalBinaryOp?]

theorem burnFromEvalCond (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .and
        (.binary .ne (.var "account") sender)
        (.binary .ne (.storage (allowanceRef (.var "account") sender))
          (.intLit maxUint256))) =
      .ok (.bool ((!(mintAccountValue I == .address I.source)) &&
        (!(Value.int (Int.ofNat (burnFromAllowanceWord evm I).toNat) ==
          .int maxUint256)))) := by
  rw [evalExpr?]
  rw [burnFromEvalFromNeSender evm I hsrc]
  simp only [EvalResult.bind, bind]
  cases hleft : (!(mintAccountValue I == .address I.source))
  · simp [pure]
  · rw [burnFromEvalAllowanceNeMax evm I hsrc]
    simp [pure]

def burnFromShouldSpend (evm : EVM.State) (I : ExecutionEnv) : Bool :=
  (!(mintAccountValue I == .address I.source)) &&
    (!(Value.int (Int.ofNat (burnFromAllowanceWord evm I).toNat) ==
      .int maxUint256))

theorem burnFromEvalCond' (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (.binary .and
        (.binary .ne (.var "account") sender)
        (.binary .ne (.storage (allowanceRef (.var "account") sender))
          (.intLit maxUint256))) =
      .ok (.bool (burnFromShouldSpend evm I)) := by
  exact burnFromEvalCond evm I hsrc

def burnFromAllowanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnFromAllowanceWord evm I).toNat -
    (mintValueWord I).toNat)

def burnFromAfterAllowance (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  if burnFromShouldSpend evm I then
    Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (burnFromAllowanceSlot I) (burnFromAllowanceDebitWord evm I)
  else evm

theorem burnFromAfterAllowance_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (burnFromAfterAllowance evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  unfold burnFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem burnFromAfterAllowance_source (evm : EVM.State) (I : ExecutionEnv) :
    (burnFromAfterAllowance evm I).executionEnv.source =
      evm.executionEnv.source := by
  unfold burnFromAfterAllowance
  split <;> simp [storageStore_executionEnv]

theorem burnFromAllowanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (burnFromAllowanceDebitWord evm I).toNat =
      (burnFromAllowanceWord evm I).toNat -
        (mintValueWord I).toNat := by
  unfold burnFromAllowanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (burnFromAllowanceWord evm I).val.isLt

theorem burnFromEvalAllowanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : (mintValueWord I).toNat ≤
      (burnFromAllowanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (checkedSub (.storage (allowanceRef (.var "account") sender)) (.var "value")) =
        .ok (.int (Int.ofNat ((burnFromAllowanceWord evm I).toNat -
          (mintValueWord I).toNat))) := by
  exact tokenEvalCheckedSub_ok (burnFromEvalAllowance evm I hsrc)
    (mintEvalValue evm I) hle (burnFromAllowanceWord evm I).val.isLt

theorem burnFromEvalAllowanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hunder : (burnFromAllowanceWord evm I).toNat <
      (mintValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := mintStore I } evm
      (checkedSub (.storage (allowanceRef (.var "account") sender)) (.var "value")) =
        .revert := by
  exact tokenEvalCheckedSub_revert (burnFromEvalAllowance evm I hsrc)
    (mintEvalValue evm I) hunder

theorem burnFromAssignAllowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := mintStore I } evm
      .storage (allowanceRef (.var "account") sender)
      (.int (Int.ofNat (burnFromAllowanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := mintStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (burnFromAllowanceSlot I) (burnFromAllowanceDebitWord evm I)) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := mintStore_allowance I)
    (her := burnFromEvalAllowanceRef evm I hsrc)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      burnFromAllowanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [burnFromAllowanceSlot] using
    tokenStorageLocStore_uint256 evm (burnFromAllowanceSlot I)
      (burnFromAllowanceDebitWord evm I)

theorem burnFromAllowanceStep_ok (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hle : burnFromShouldSpend evm I = true →
      (mintValueWord I).toNat ≤
        (burnFromAllowanceWord evm I).toNat) :
    ExecStmt config { contract := contract, locals := mintStore I } evm
      (.ite
        (.binary .and
          (.binary .ne (.var "account") sender)
          (.binary .ne (.storage (allowanceRef (.var "account") sender))
            (.intLit maxUint256)))
        [.assign .storage (allowanceRef (.var "account") sender)
          (checkedSub (.storage (allowanceRef (.var "account") sender)) (.var "value"))] [])
      (.ok { contract := contract, locals := mintStore I }
        (burnFromAfterAllowance evm I)) := by
  by_cases hspend : burnFromShouldSpend evm I = true
  · have hcond : evalExpr? config
        { contract := contract, locals := mintStore I } evm
        (.binary .and
          (.binary .ne (.var "account") sender)
          (.binary .ne (.storage (allowanceRef (.var "account") sender))
            (.intLit maxUint256))) = .ok (.bool true) := by
      rw [burnFromEvalCond' evm I hsrc, hspend]
    have hassign := burnFromAssignAllowance evm I hsrc
    rw [burnFromAllowanceDebitWord_toNat evm I] at hassign
    have hthen : ExecBlock config { contract := contract, locals := mintStore I }
        evm [.assign .storage (allowanceRef (.var "account") sender)
          (checkedSub (.storage (allowanceRef (.var "account") sender)) (.var "value"))]
        (.ok { contract := contract, locals := mintStore I }
          (burnFromAfterAllowance evm I)) := by
      simpa [burnFromAfterAllowance, hspend] using
        (ExecBlock.consNormal
          (ExecStmt.assign
            (burnFromEvalAllowanceDebit_ok evm I hsrc (hle hspend)) hassign)
          ExecBlock.nil)
    exact ExecStmt.iteTrue hcond hthen
  · have hfalse : burnFromShouldSpend evm I = false := by
      cases h : burnFromShouldSpend evm I <;> simp_all
    have hcond : evalExpr? config
        { contract := contract, locals := mintStore I } evm
        (.binary .and
          (.binary .ne (.var "account") sender)
          (.binary .ne (.storage (allowanceRef (.var "account") sender))
            (.intLit maxUint256))) = .ok (.bool false) := by
      rw [burnFromEvalCond' evm I hsrc, hfalse]
    simpa [burnFromAfterAllowance, hfalse] using
      (ExecStmt.iteFalse hcond (ExecBlock.nil :
        ExecBlock config { contract := contract, locals := mintStore I }
          evm [] (.ok { contract := contract, locals := mintStore I } evm)))

def burnFromSupplyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  mintSupplyWord (burnFromAfterAllowance evm I)

def burnFromSupplyDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnFromSupplyWord evm I).toNat - (mintValueWord I).toNat)

def burnFromAfterSupply (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (burnFromAfterAllowance evm I) evm.executionEnv.codeOwner
    ⟨0⟩ (burnFromSupplyDebitWord evm I)

def burnFromBalanceWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad (burnFromAfterSupply evm I) evm.executionEnv.codeOwner
    (mintBalanceSlot I)

def burnFromBalanceDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat ((burnFromBalanceWord evm I).toNat - (mintValueWord I).toNat)

def burnFromPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (burnFromAfterSupply evm I) evm.executionEnv.codeOwner
    (mintBalanceSlot I) (burnFromBalanceDebitWord evm I)

theorem burnFromSupplyDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (burnFromSupplyDebitWord evm I).toNat =
      (burnFromSupplyWord evm I).toNat - (mintValueWord I).toNat := by
  unfold burnFromSupplyDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (burnFromSupplyWord evm I).val.isLt

theorem burnFromSupplyDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (mintValueWord I).toNat ≤ (burnFromSupplyWord evm I).toNat) :
    burnFromSupplyDebitWord evm I =
      UInt256.sub (burnFromSupplyWord evm I) (mintValueWord I) := by
  apply u256_inj
  rw [burnFromSupplyDebitWord_toNat evm I, usub_toNat hle]

theorem burnFromEvalSupplyDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hle : (mintValueWord I).toNat ≤ (burnFromSupplyWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := mintStore I }
      (burnFromAfterAllowance evm I)
      (checkedSub (.storage totalSupplyRef) (.var "value")) =
        .ok (.int (Int.ofNat ((burnFromSupplyWord evm I).toNat -
          (mintValueWord I).toNat))) := by
  exact tokenEvalCheckedSub_ok
    (mintEvalSupply (burnFromAfterAllowance evm I) I)
    (mintEvalValue (burnFromAfterAllowance evm I) I) hle
    (burnFromSupplyWord evm I).val.isLt

theorem burnFromEvalSupplyDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hunder : (burnFromSupplyWord evm I).toNat < (mintValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := mintStore I }
      (burnFromAfterAllowance evm I)
      (checkedSub (.storage totalSupplyRef) (.var "value")) = .revert := by
  exact tokenEvalCheckedSub_revert
    (mintEvalSupply (burnFromAfterAllowance evm I) I)
    (mintEvalValue (burnFromAfterAllowance evm I) I) hunder

theorem burnFromAssignSupply (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := mintStore I }
      (burnFromAfterAllowance evm I) .storage totalSupplyRef
      (.int (Int.ofNat (burnFromSupplyDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := mintStore I },
        burnFromAfterSupply evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := mintStore_totalSupply I)
    (her := mintEvalSupplyRef (burnFromAfterAllowance evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := tokenConfig_storage_totalSupply)
  simpa [burnFromAfterSupply, burnFromAfterAllowance_codeOwner evm I] using
    tokenStorageLocStore_uint256 (burnFromAfterAllowance evm I) ⟨0⟩
      (burnFromSupplyDebitWord evm I)

theorem burnFromAfterSupply_codeOwner (evm : EVM.State) (I : ExecutionEnv) :
    (burnFromAfterSupply evm I).executionEnv.codeOwner =
      evm.executionEnv.codeOwner := by
  simp [burnFromAfterSupply, storageStore_executionEnv,
    burnFromAfterAllowance_codeOwner]

theorem burnFromBalanceDebitWord_toNat (evm : EVM.State) (I : ExecutionEnv) :
    (burnFromBalanceDebitWord evm I).toNat =
      (burnFromBalanceWord evm I).toNat - (mintValueWord I).toNat := by
  unfold burnFromBalanceDebitWord
  apply ulit_toNat'
  exact lt_of_le_of_lt (Nat.sub_le _ _) (burnFromBalanceWord evm I).val.isLt

theorem burnFromBalanceDebitWord_eq_sub (evm : EVM.State) (I : ExecutionEnv)
    (hle : (mintValueWord I).toNat ≤ (burnFromBalanceWord evm I).toNat) :
    burnFromBalanceDebitWord evm I =
      UInt256.sub (burnFromBalanceWord evm I) (mintValueWord I) := by
  apply u256_inj
  rw [burnFromBalanceDebitWord_toNat evm I, usub_toNat hle]

theorem burnFromEvalBalanceDebit_ok (evm : EVM.State) (I : ExecutionEnv)
    (hle : (mintValueWord I).toNat ≤ (burnFromBalanceWord evm I).toNat) :
    evalExpr? config { contract := contract, locals := mintStore I }
      (burnFromAfterSupply evm I)
      (checkedSub (.storage (balanceOfRef (.var "account"))) (.var "value")) =
        .ok (.int (Int.ofNat ((burnFromBalanceWord evm I).toNat -
          (mintValueWord I).toNat))) := by
  have hload := mintEvalBalance (burnFromAfterSupply evm I) I
  rw [burnFromAfterSupply_codeOwner evm I] at hload
  exact tokenEvalCheckedSub_ok hload
    (mintEvalValue (burnFromAfterSupply evm I) I) hle
    (burnFromBalanceWord evm I).val.isLt

theorem burnFromEvalBalanceDebit_revert (evm : EVM.State) (I : ExecutionEnv)
    (hunder : (burnFromBalanceWord evm I).toNat < (mintValueWord I).toNat) :
    evalExpr? config { contract := contract, locals := mintStore I }
      (burnFromAfterSupply evm I)
      (checkedSub (.storage (balanceOfRef (.var "account"))) (.var "value")) =
        .revert := by
  have hload := mintEvalBalance (burnFromAfterSupply evm I) I
  rw [burnFromAfterSupply_codeOwner evm I] at hload
  exact tokenEvalCheckedSub_revert hload
    (mintEvalValue (burnFromAfterSupply evm I) I) hunder

theorem burnFromAssignBalance (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := mintStore I }
      (burnFromAfterSupply evm I) .storage (balanceOfRef (.var "account"))
      (.int (Int.ofNat (burnFromBalanceDebitWord evm I).toNat)) =
      .ok ({ contract := contract, locals := mintStore I },
        burnFromPostState evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (hbase := mintStore_balanceOf I)
    (her := mintEvalBalanceRef (burnFromAfterSupply evm I) I)
    (hty := by simp [storageTypeAt?, contract, storageDecls,
      mintBalanceRef, uint256St, storageTypeStep?])
    (hloc := by rfl)
  simpa [burnFromPostState, burnFromAfterSupply_codeOwner evm I,
    mintBalanceSlot] using
    tokenStorageLocStore_uint256 (burnFromAfterSupply evm I)
      (mintBalanceSlot I) (burnFromBalanceDebitWord evm I)

theorem burnFromBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : burnFromShouldSpend evm I = true →
      (mintValueWord I).toNat ≤ (burnFromAllowanceWord evm I).toNat)
    (hsupply : (mintValueWord I).toNat ≤ (burnFromSupplyWord evm I).toNat)
    (hbalance : (mintValueWord I).toNat ≤ (burnFromBalanceWord evm I).toNat) :
    ExecTransitionBody config contract evm (mintStore I)
      burnFromTransition.body
      (.returned { contract := contract, locals := mintStore I }
        (burnFromPostState evm I) (some [(.bool true)])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (burnFromAllowanceStep_ok evm I hsrc hallow) ?_
  have hassign := burnFromAssignSupply evm I
  rw [burnFromSupplyDebitWord_toNat evm I] at hassign
  refine ExecBlock.consNormal
    (ExecStmt.assign (burnFromEvalSupplyDebit_ok evm I hsupply) hassign) ?_
  have hassign2 := burnFromAssignBalance evm I
  rw [burnFromBalanceDebitWord_toNat evm I] at hassign2
  refine ExecBlock.consNormal
    (ExecStmt.assign (burnFromEvalBalanceDebit_ok evm I hbalance) hassign2) ?_
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]))

theorem burnFromBodyReverts_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hspend : burnFromShouldSpend evm I = true)
    (hunder : (burnFromAllowanceWord evm I).toNat <
      (mintValueWord I).toNat) :
    ExecTransitionBody config contract evm (mintStore I)
      burnFromTransition.body .reverted := by
  have hcond : evalExpr? config
      { contract := contract, locals := mintStore I } evm
      (.binary .and
        (.binary .ne (.var "account") sender)
        (.binary .ne (.storage (allowanceRef (.var "account") sender))
          (.intLit maxUint256))) = .ok (.bool true) := by
    rw [burnFromEvalCond' evm I hsrc, hspend]
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.iteTrue hcond <|
        ExecBlock.consRevert (ExecStmt.assignExprRevert
          (burnFromEvalAllowanceDebit_revert evm I hsrc hunder)))

theorem burnFromBodyReverts_supply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : burnFromShouldSpend evm I = true →
      (mintValueWord I).toNat ≤ (burnFromAllowanceWord evm I).toNat)
    (hunder : (burnFromSupplyWord evm I).toNat < (mintValueWord I).toNat) :
    ExecTransitionBody config contract evm (mintStore I)
      burnFromTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (burnFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consRevert
          (ExecStmt.assignExprRevert (burnFromEvalSupplyDebit_revert evm I hunder))

theorem burnFromBodyReverts_balance (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source)
    (hallow : burnFromShouldSpend evm I = true →
      (mintValueWord I).toNat ≤ (burnFromAllowanceWord evm I).toNat)
    (hsupply : (mintValueWord I).toNat ≤ (burnFromSupplyWord evm I).toNat)
    (hunder : (burnFromBalanceWord evm I).toNat < (mintValueWord I).toNat) :
    ExecTransitionBody config contract evm (mintStore I)
      burnFromTransition.body .reverted := by
  have hassign := burnFromAssignSupply evm I
  rw [burnFromSupplyDebitWord_toNat evm I] at hassign
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (burnFromAllowanceStep_ok evm I hsrc hallow) <|
        ExecBlock.consNormal
          (ExecStmt.assign (burnFromEvalSupplyDebit_ok evm I hsupply) hassign) <|
          ExecBlock.consRevert
            (ExecStmt.assignExprRevert (burnFromEvalBalanceDebit_revert evm I hunder))

theorem tokenDecode_burnFrom_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (burnFromTransition.params.map Param.name)
      (transitionSignature burnFromTransition).paramTypes I.calldata =
        some (mintStore I) := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, abiUInt256, mintStore, mintAccountValue,
    mintValueValue, mintAccountWord, mintValueWord, calldataWord]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "account") (y := "value") hsz68 hbig hcanon

theorem tokenDecode_burnFrom_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldata (burnFromTransition.params.map Param.name)
      (transitionSignature burnFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using decodeCalldata_addr_uint256_none_short
    (cd := I.calldata) (x := "account") (y := "value") hsz4 hshort

theorem tokenDecode_burnFrom_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (mintAccountWord I).toNat < EVM.addressModulus) :
    decodeCalldata (burnFromTransition.params.map Param.name)
      (transitionSignature burnFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256, calldataWord, mintAccountWord]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "account") (y := "value") hsz68 hbig hnc

theorem tokenDecode_burnFrom_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (burnFromTransition.params.map Param.name)
      (transitionSignature burnFromTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["account", "value"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, abiUInt256] using decodeCalldata_addr_uint256_none_huge
    (cd := I.calldata) (x := "account") (y := "value") hbig

theorem burnFromX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2977⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨440⟩, ⟨445⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨445⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨440⟩, swap2, swap1, push2 ⟨2977⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem burnFromX_dec5470_spender {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2906⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨3012⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
        ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨440⟩, ⟨445⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := burnFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨3012⟩, dup6, dup3, dup7, add, push2 ⟨2906⟩,
    jump (by jump_dest) ]⟩

theorem burnFromX_dec5576 {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3012⟩
      [mintAccountWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨440⟩, ⟨445⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := burnFromX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrOk rd hcanonSpender (by jump_dest) (by evm_ov)

theorem burnFromX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨3029⟩, ⟨32⟩,
        ⟨0⟩, mintAccountWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨440⟩, ⟨445⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := burnFromX_dec5576 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨3029⟩,
    dup6, dup3, dup7, add, push2 ⟨2957⟩, jump (by jump_dest) ]⟩

theorem burnFromX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonSpender : (mintAccountWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1872⟩
      [mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd5521⟩ := burnFromX_dec5521_value (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonSpender hreach
  have rd5499 := evm_run rd5521 with [
    jumpdest, push0, dup2, calldataload, swap1, pop,
    push2 ⟨2971⟩, dup2, push2 ⟨2935⟩, jump (by jump_dest) ]
  have rd5508 := evm_run rd5499 with [
    jumpdest, push2 ⟨2944⟩, dup2, push2 ⟨2926⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest) ]
  have heq : UInt256.eq (mintValueWord I) (mintValueWord I) = ⟨1⟩ :=
    u256_eq_refl _
  have rd5518 := evm_run rd5508 with [
    jumpdest, dup2, eq, push2 ⟨2954⟩,
    jumpiT (by rw [heq]; decide) (by jump_dest) ]
  exact ⟨_, _, evm_run rd5518 with [
    jumpdest, pop, jump (by jump_dest),
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest),
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1872⟩, jump (by jump_dest) ]⟩
theorem burnFromX_self_to_supply {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hself : mintAccountWord I = solcSourceWord I)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2347⟩
      [⟨0⟩, mintValueWord I,         mintAccountWord I, ⟨445⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1801⟩ := burnFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonFrom hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanonFrom
  have rd1851₀ := evm_run rd1801 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd1851 := rd1851₀
  rw [hsourceClean, hfromClean, hself] at rd1851
  have hzero : UInt256.isZero (UInt256.eq (solcSourceWord I) (solcSourceWord I)) =
      ⟨0⟩ := by rw [uInt256_eq_self]; decide
  rw [hzero] at rd1851
  have rd2276 := evm_run rd1851 with [
    iszero, push2 ⟨2085⟩, jumpiT (by decide) (by jump_dest),
    jumpdest, iszero, push2 ⟨2347⟩, jumpiT (by decide) (by jump_dest) ]
  exact ⟨_, _, by simpa [hself] using rd2276⟩

def burnFromAllowanceOuterSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨2⟩ (mintAccountWord I)

noncomputable def burnFromAllowanceOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨2⟩ solcFreePtrMem

noncomputable def burnFromAllowanceMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (burnFromAllowanceOuterSlot I)
    (burnFromAllowanceOuterMem I)

theorem burnFromX_nonself_allowanceLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2083⟩
      [solcSlotWord σ I (burnFromAllowanceSlot I), tokenTransferFromMaxWord,
        ⟨0⟩, mintValueWord I,         mintAccountWord I, ⟨445⟩, sel]
      (burnFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1801⟩ := burnFromX_decoded (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hcanonFrom hreach
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have hfromClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanonFrom
  have hneqWord : UInt256.eq (mintAccountWord I) (solcSourceWord I) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hne (uInt256_eq_one_eq he))
  have rd1851₀ := evm_run rd1801 with [
    jumpdest, push0, caller, push20 solcAddrMask, and,
    dup4, push20 solcAddrMask, and, eq, iszero, dup1 ]
  have rd1851 := rd1851₀
  rw [hsourceClean, hfromClean, hneqWord] at rd1851
  have rd1858 := evm_run rd1851 with [
    iszero, push2 ⟨2085⟩, jumpiNT (by decide),
    pop ]
  have rd1891 := rd1858.pushConst tokenTransferFromMaxWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1939₀ := evm_run rd1891 with [
    push1 ⟨2⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1939 := rd1939₀
  rw [hfromClean, hfromClean] at rd1939
  obtain ⟨_, _, rd1952⟩ := RD.tokenMappingHashSuffix rd1939 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [burnFromAllowanceOuterMem,
      burnFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (mintAccountWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1939'₀ := evm_run rd1952 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd1939' := rd1939'₀
  rw [hsourceClean, hsourceClean] at rd1939'
  have hmem : (burnFromAllowanceOuterMem I).size = 96 := by
    unfold burnFromAllowanceOuterMem
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2011⟩ := RD.tokenMappingHashSuffix rd1939' token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [burnFromAllowanceMem,
      burnFromAllowanceOuterSlot,
      burnFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (burnFromAllowanceOuterSlot I) (solcSourceWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2012⟩ := rd2011.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2012⟩

theorem burnFromX_max_to_supply {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hmax : solcSlotWord σ I (burnFromAllowanceSlot I) =
      tokenTransferFromMaxWord)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2347⟩
      [⟨0⟩, mintValueWord I,         mintAccountWord I, ⟨445⟩, sel]
      (burnFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2012₀⟩ := burnFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz68 hsize hszhi
    hcanonFrom hne hreach
  have rd2012 := rd2012₀
  rw [hmax] at rd2012
  exact ⟨_, _, evm_run rd2012 with [
    eq, iszero, jumpdest, iszero, push2 ⟨2347⟩,
    jumpiT (by decide) (by jump_dest) ]⟩

theorem burnFromX_spend_start {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (burnFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2091⟩
      [⟨0⟩, mintValueWord I,         mintAccountWord I, ⟨445⟩, sel]
      (burnFromAllowanceMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2012₀⟩ := burnFromX_nonself_allowanceLoad
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) (sel := sel) hsz68 hsize hszhi
    hcanonFrom hne hreach
  have hneqWord : UInt256.eq (solcSlotWord σ I (burnFromAllowanceSlot I))
      tokenTransferFromMaxWord = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnotmax (uInt256_eq_one_eq he))
  have rd2013 := evm_run rd2012₀ with [eq]
  rw [hneqWord] at rd2013
  exact ⟨_, _, evm_run rd2013 with [
    iszero, jumpdest, iszero, push2 ⟨2347⟩,
    jumpiNT (by decide) ]⟩

noncomputable def burnFromAllowanceReadOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨2⟩ (burnFromAllowanceMem I)

noncomputable def burnFromAllowanceReadMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (burnFromAllowanceOuterSlot I)
    (burnFromAllowanceReadOuterMem I)

theorem burnFromX_spend_load {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (burnFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2213⟩
      [solcSlotWord σ I (burnFromAllowanceSlot I),
        mintValueWord I, ⟨0⟩, mintValueWord I,
        mintAccountWord I, ⟨445⟩, sel]
      (burnFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2020⟩ := burnFromX_spend_start (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz68 hsize hszhi hcanonFrom hne hnotmax hreach
  have hfromClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd2069₀ := evm_run rd2020 with [
    dup2, push1 ⟨2⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2069 := rd2069₀
  rw [hfromClean, hfromClean] at rd2069
  have hmem : (burnFromAllowanceMem I).size = 96 := by
    unfold burnFromAllowanceMem burnFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2082⟩ := RD.tokenMappingHashSuffix rd2069 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [burnFromAllowanceReadOuterMem,
      burnFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (mintAccountWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2128₀ := evm_run rd2082 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2128 := rd2128₀
  rw [hsourceClean, hsourceClean] at rd2128
  have hmem2 : (burnFromAllowanceReadOuterMem I).size = 96 := by
    unfold burnFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2141⟩ := RD.tokenMappingHashSuffix rd2128 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [burnFromAllowanceReadMem,
      burnFromAllowanceOuterSlot,
      burnFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (burnFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2142⟩ := rd2141.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2142⟩

theorem burnFromX_spend_debit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (burnFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hle : (mintValueWord I).toNat ≤
      (solcSlotWord σ I (burnFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2222⟩
      [UInt256.sub (solcSlotWord σ I (burnFromAllowanceSlot I))
        (mintValueWord I), ⟨0⟩, mintValueWord I,
        mintAccountWord I, ⟨445⟩, sel]
      (burnFromAllowanceReadMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd2142⟩ := burnFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz68 hsize hszhi hcanonFrom hne hnotmax hreach
  have rd6645 := evm_run rd2142 with [
    push2 ⟨2222⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubOk rd6645 hle (by jump_dest) (by evm_ov)

theorem burnFromX_spend_underflow {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (burnFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hunder : (solcSlotWord σ I (burnFromAllowanceSlot I)).toNat <
      (mintValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2142⟩ := burnFromX_spend_load (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz68 hsize hszhi hcanonFrom hne hnotmax hreach
  have rd6645 := evm_run rd2142 with [
    push2 ⟨2222⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest) ]
  exact RD.tokenCheckedSubUnderflow rd6645 hunder (by evm_ov)

noncomputable def burnFromAllowanceStoreOuterMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨2⟩ (burnFromAllowanceReadMem I)

noncomputable def burnFromAllowanceStoreMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) (burnFromAllowanceOuterSlot I)
    (burnFromAllowanceStoreOuterMem I)

def burnFromEvmAllowanceMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ (burnFromAllowanceSlot I)
    (UInt256.sub (solcSlotWord σ I (burnFromAllowanceSlot I))
      (mintValueWord I))

theorem burnFromX_spend_stored {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4) (hperm : I.perm = true)
    (hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus)
    (hne : mintAccountWord I ≠ solcSourceWord I)
    (hnotmax : solcSlotWord σ I (burnFromAllowanceSlot I) ≠
      tokenTransferFromMaxWord)
    (hle : (mintValueWord I).toNat ≤
      (solcSlotWord σ I (burnFromAllowanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2347⟩
      [⟨0⟩, mintValueWord I,         mintAccountWord I, ⟨445⟩, sel]
      (burnFromAllowanceStoreMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnFromEvmAllowanceMap σ I) k C := by
  obtain ⟨_, _, rd2151⟩ := burnFromX_spend_debit (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    (sel := sel) hsz68 hsize hszhi hcanonFrom hne hnotmax hle hreach
  have hfromClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanonFrom
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd2200₀ := evm_run rd2151 with [
    jumpdest, push1 ⟨2⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2200 := rd2200₀
  rw [hfromClean, hfromClean] at rd2200
  have hmem : (burnFromAllowanceReadMem I).size = 96 := by
    unfold burnFromAllowanceReadMem burnFromAllowanceReadOuterMem
      burnFromAllowanceMem burnFromAllowanceOuterMem
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
  obtain ⟨_, _, rd2213⟩ := RD.tokenMappingHashSuffix rd2200 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [burnFromAllowanceStoreOuterMem,
      burnFromAllowanceOuterSlot] using
      (twoWordHashMem_solcMappingSlot ⟨2⟩ (mintAccountWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2259₀ := evm_run rd2213 with [
    push0, caller, push20 solcAddrMask, and, push20 solcAddrMask, and ]
  have rd2259 := rd2259₀
  rw [hsourceClean, hsourceClean] at rd2259
  have hmem2 : (burnFromAllowanceStoreOuterMem I).size = 96 := by
    unfold burnFromAllowanceStoreOuterMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2272⟩ := RD.tokenMappingHashSuffix rd2259 token_mapping_hash_wf
    (by rfl) (by rfl)
    (by simpa [burnFromAllowanceStoreMem,
      burnFromAllowanceOuterSlot,
      burnFromAllowanceSlot_eq_solc I hcanonFrom] using
      (twoWordHashMem_solcMappingSlot
        (burnFromAllowanceOuterSlot I) (solcSourceWord I) hmem2))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2274 := evm_run rd2272 with [dup2, swap1]
  obtain ⟨_, _, rd2275⟩ := rd2274.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [burnFromEvmAllowanceMap] using
    (evm_run rd2275 with [pop])⟩

def burnFromEvmSupplyMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨0⟩
    (UInt256.sub (solcSlotWord σ I ⟨0⟩) (mintValueWord I))

def burnFromEvmPostMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (burnFromEvmSupplyMap σ I) (mintBalanceSlot I)
    (UInt256.sub (solcSlotWord (burnFromEvmSupplyMap σ I) I (mintBalanceSlot I))
      (mintValueWord I))

noncomputable def burnFromBalanceHashMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨1⟩ mem

noncomputable def burnFromFinalHashMem (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  twoWordHashMem (mintAccountWord I) ⟨1⟩ (burnFromBalanceHashMem I mem)

theorem burnFromX_supplyLoad {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2351⟩
      [solcSlotWord σA I ⟨0⟩, mintValueWord I, ⟨0⟩,
        mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rdLoad := evm_run rd with [jumpdest, dup2, push0]
  obtain ⟨_, _, rdLoaded⟩ := rdLoad.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rdLoaded⟩

theorem burnFromX_supplyDebit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hle : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2360⟩
      [UInt256.sub (solcSlotWord σA I ⟨0⟩) (mintValueWord I), ⟨0⟩,
        mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C := by
  obtain ⟨_, _, rd⟩ := burnFromX_supplyLoad hreach
  have rdSub := evm_run rd with [
    push2 ⟨2360⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubOk rdSub hle (by jump_dest) (by evm_ov)

theorem burnFromX_supplyUnderflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hunder : (solcSlotWord σA I ⟨0⟩).toNat < (mintValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := burnFromX_supplyLoad hreach
  have rdSub := evm_run rd with [
    push2 ⟨2360⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubUnderflow rdSub hunder (by evm_ov)

theorem burnFromX_supplyStore {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hle : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2366⟩
      [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, burnFromEvmSupplyMap σA I) k C := by
  obtain ⟨_, _, rd⟩ := burnFromX_supplyDebit hle hreach
  have rdStore := evm_run rd with [jumpdest, push0, dup2, swap1]
  obtain ⟨_, _, rdStored⟩ := rdStore.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [burnFromEvmSupplyMap] using
    (evm_run rdStored with [pop])⟩

theorem burnFromX_balanceLoad {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hle : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2429⟩
      [solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I),
        mintValueWord I, ⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      (burnFromBalanceHashMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnFromEvmSupplyMap σA I) k C := by
  obtain ⟨_, _, rd2366⟩ := burnFromX_supplyStore hperm hle hreach
  have haccountClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanon
  have rd2415₀ := evm_run rd2366 with [
    dup2, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd2415 := rd2415₀
  rw [haccountClean, haccountClean] at rd2415
  obtain ⟨_, _, rd2428⟩ := RD.tokenMappingHashSuffix rd2415
    token_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [burnFromBalanceHashMem, mintBalanceSlot_eq_solc I hcanon] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (mintAccountWord I) hmem))
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2429⟩ := rd2428.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd2429⟩

theorem burnFromX_balanceDebit {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hsupply : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hbalance : (mintValueWord I).toNat ≤
      (solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2438⟩
      [UInt256.sub (solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I))
        (mintValueWord I), ⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      (burnFromBalanceHashMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnFromEvmSupplyMap σA I) k C := by
  obtain ⟨_, _, rd⟩ := burnFromX_balanceLoad hperm hcanon hmem hsupply hreach
  have rdSub := evm_run rd with [
    push2 ⟨2438⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubOk rdSub hbalance (by jump_dest) (by evm_ov)

theorem burnFromX_balanceUnderflow {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hsupply : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hunder : (solcSlotWord (burnFromEvmSupplyMap σA I) I
      (mintBalanceSlot I)).toNat < (mintValueWord I).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := burnFromX_balanceLoad hperm hcanon hmem hsupply hreach
  have rdSub := evm_run rd with [
    push2 ⟨2438⟩, swap2, swap1, push2 ⟨3465⟩, jump (by jump_dest)]
  exact RD.tokenCheckedSubUnderflow rdSub hunder (by evm_ov)

theorem burnFromX_balanceStore {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hsupply : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hbalance : (mintValueWord I).toNat ≤
      (solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2504⟩
      [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      (burnFromFinalHashMem I mem) (UInt256.ofNat 3) ByteArray.empty
      (cA, burnFromEvmPostMap σA I) k C := by
  obtain ⟨_, _, rd2438⟩ := burnFromX_balanceDebit
    hperm hcanon hmem hsupply hbalance hreach
  have haccountClean : UInt256.land solcAddrMask (mintAccountWord I) =
      mintAccountWord I := solcAddrMask_clean_left hcanon
  have rd2487₀ := evm_run rd2438 with [
    jumpdest, push1 ⟨1⟩, push0, dup6,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd2487 := rd2487₀
  rw [haccountClean, haccountClean] at rd2487
  have hmem1 : (burnFromBalanceHashMem I mem).size = 96 := by
    unfold burnFromBalanceHashMem
    exact twoWordHashMem_size_96 _ _ hmem
  obtain ⟨_, _, rd2500⟩ := RD.tokenMappingHashSuffix rd2487
    token_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [burnFromFinalHashMem, mintBalanceSlot_eq_solc I hcanon] using
      twoWordHashMem_solcMappingSlot ⟨1⟩ (mintAccountWord I) hmem1)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd2502 := evm_run rd2500 with [dup2, swap1]
  obtain ⟨_, _, rd2503⟩ := rd2502.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [burnFromEvmPostMap, burnFromFinalHashMem] using
    (evm_run rd2503 with [pop])⟩

theorem burnFromX_return {cA gh bl σ σ₀ σA A I} {g : Sat256}
    {mem : ByteArray} {sel : UInt256}
    (hperm : I.perm = true)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hsupply : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat)
    (hbalance : (mintValueWord I).toNat ≤
      (solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I)).toNat)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2347⟩ [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    RDret tokenBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, burnFromEvmPostMap σA I) (UInt256.toByteArray (⟨1⟩ : UInt256)) := by
  obtain ⟨_, _, rd2504⟩ := burnFromX_balanceStore
    hperm hcanon hmem hsupply hbalance hreach
  have rd445 := evm_run rd2504 with [
    push1 ⟨1⟩, swap1, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have hmemFinal : (burnFromFinalHashMem I mem).size = 96 := by
    unfold burnFromFinalHashMem burnFromBalanceHashMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ hmem
  have hreadFinal : (burnFromFinalHashMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
    unfold burnFromFinalHashMem burnFromBalanceHashMem
    apply twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ hmem)
    exact twoWordHashMem_read64 _ _ hmem hread
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ (burnFromFinalHashMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
         ((burnFromFinalHashMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := mloadFreePtrValue (by rw [hmemFinal]; decide) (by decide) hreadFinal
  have rd3065 := evm_run rd445 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload (by decide) (by evm_ov),
    push2 ⟨458⟩, swap2, swap1, push2 ⟨3065⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd458⟩ := RD.tokenRoutineEncodeBoolFromMem
    (memout := tokenWordReturnMem (burnFromFinalHashMem I mem) (⟨1⟩ : UInt256))
    rd3065 (by
      rw [show UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ from by decide]
      rfl)
    (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  exact evm_run rd458 with [
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
      (by evm_ov)]

theorem burnFromX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := burnFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2998⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem burnFromX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := burnFromX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨2999⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨2998⟩, push2 ⟨2832⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem burnFromX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : UInt256.eq (mintAccountWord I)
      (UInt256.land (mintAccountWord I) solcAddrMask) = ⟨0⟩)
    (hreach : ∃ k C, RD tokenBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨419⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev tokenBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := burnFromX_dec5470_spender (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.tokenDecodeAddrRevert rd hnc (by evm_ov)


theorem burnFromAccountWord_eq_source_iff (I : ExecutionEnv)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus) :
    mintAccountWord I = solcSourceWord I ↔
      AccountAddress.ofNat (mintAccountWord I).toNat = I.source := by
  constructor
  · intro h
    rw [h]
    exact solcSource_ofNat I
  · intro h
    apply u256_inj
    have hv := congrArg Fin.val h
    change (mintAccountWord I).toNat % AccountAddress.size = I.source.val at hv
    have hcanon' : (mintAccountWord I).toNat < AccountAddress.size := hcanon
    rw [Nat.mod_eq_of_lt hcanon'] at hv
    rw [solcSourceWord_toNat]
    exact hv

theorem burnFromShouldSpend_iff (evm : EVM.State) (I : ExecutionEnv)
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus) :
    burnFromShouldSpend evm I = true ↔
      mintAccountWord I ≠ solcSourceWord I ∧
        burnFromAllowanceWord evm I ≠ tokenTransferFromMaxWord := by
  rw [burnFromShouldSpend]
  simp only [Bool.and_eq_true, Bool.not_eq_true]
  constructor
  · rintro ⟨hfrom, hallow⟩
    constructor
    · intro he
      have hv := (burnFromAccountWord_eq_source_iff I hcanon).mp he
      simp [mintAccountValue, BEq.beq, hv] at hfrom
    · intro he
      have hv := (tokenTransferFromAllowanceValue_eq_max_iff _).mpr he
      have hi : Int.ofNat (burnFromAllowanceWord evm I).toNat =
          maxUint256 := by injection hv with hi
      simp [BEq.beq] at hallow
      exact hallow hi
  · rintro ⟨hfrom, hallow⟩
    constructor
    · have hv : AccountAddress.ofNat (mintAccountWord I).toNat ≠
          I.source := fun he => hfrom ((burnFromAccountWord_eq_source_iff I hcanon).mpr he)
      simp [mintAccountValue, BEq.beq, hv]
    · have hv : Value.int (Int.ofNat (burnFromAllowanceWord evm I).toNat) ≠
          .int maxUint256 := fun he => hallow ((tokenTransferFromAllowanceValue_eq_max_iff _).mp he)
      simp [BEq.beq]
      intro hi
      exact hv (congrArg Value.int hi)

theorem burnFromAllowanceMem_size (I : ExecutionEnv) :
    (burnFromAllowanceMem I).size = 96 := by
  unfold burnFromAllowanceMem burnFromAllowanceOuterMem
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size

theorem burnFromAllowanceMem_read64 (I : ExecutionEnv) :
    (burnFromAllowanceMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold burnFromAllowanceMem burnFromAllowanceOuterMem
  apply twoWordHashMem_read64 _ _
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  exact twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem burnFromAllowanceStoreMem_size (I : ExecutionEnv) :
    (burnFromAllowanceStoreMem I).size = 96 := by
  unfold burnFromAllowanceStoreMem burnFromAllowanceStoreOuterMem
    burnFromAllowanceReadMem burnFromAllowanceReadOuterMem
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  apply twoWordHashMem_size_96
  exact twoWordHashMem_size_96 _ _ (burnFromAllowanceMem_size I)

theorem burnFromAllowanceStoreMem_read64 (I : ExecutionEnv) :
    (burnFromAllowanceStoreMem I).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [burnFromAllowanceStoreMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold burnFromAllowanceStoreOuterMem
    apply twoWordHashMem_size_96
    unfold burnFromAllowanceReadMem burnFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (burnFromAllowanceMem_size I))
  rw [burnFromAllowanceStoreOuterMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold burnFromAllowanceReadMem burnFromAllowanceReadOuterMem
    apply twoWordHashMem_size_96
    exact twoWordHashMem_size_96 _ _ (burnFromAllowanceMem_size I))
  rw [burnFromAllowanceReadMem]
  apply twoWordHashMem_read64 _ _ (by
    unfold burnFromAllowanceReadOuterMem
    exact twoWordHashMem_size_96 _ _ (burnFromAllowanceMem_size I))
  rw [burnFromAllowanceReadOuterMem]
  exact twoWordHashMem_read64 _ _ (burnFromAllowanceMem_size I)
    (burnFromAllowanceMem_read64 I)

theorem tokenBurnFromSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x79, 0xcc, 0x67, 0x90]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x79, 0xcc, 0x67, 0x90]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem tokenDispatch_burnFrom {cd : ByteArray}
    (hsel : ((⟨#[0x79, 0xcc, 0x67, 0x90]⟩ : ByteArray) ==
      cd.extract 0 4) = true) :
    dispatchMsg contract cd = some burnFromTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x79, 0xcc, 0x67, 0x90]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [allowanceTransition, approveTransition, balanceOfTransition,
      burnTransition])
    (post := [mintTransition, totalSupplyTransition, transferTransition,
      transferFromTransition])
    rfl rfl ?_ (by rw [selectorOf, burnFromSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  all_goals first
    | rw [selectorOf, allowanceSelectorBytes, hcd]
    | rw [selectorOf, approveSelectorBytes, hcd]
    | rw [selectorOf, balanceOfSelectorBytes, hcd]
    | rw [selectorOf, burnSelectorBytes, hcd]
  all_goals decide

set_option maxHeartbeats 5000000 in
theorem burnFromTailCore
    {cA gh bl σ_evm σ_solm σ₀ σA A I} {g : UInt256} {mem : ByteArray}
    (hcode : I.code = tokenBytecode) (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hd : dispatchMsg contract I.calldata = some burnFromTransition)
    (hdec : decodeCalldata (burnFromTransition.params.map Param.name)
      (transitionSignature burnFromTransition).paramTypes I.calldata =
        some (mintStore I))
    (hcanon : (mintAccountWord I).toNat < EVM.addressModulus)
    (hallow : burnFromShouldSpend
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I = true →
      (mintValueWord I).toNat ≤
        (burnFromAllowanceWord
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I).toNat)
    (hState : EVMStateEquiv
      (burnFromAfterAllowance
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I)
      (burnFromAfterAllowance
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I))
    (hmapA : (burnFromAfterAllowance
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I).accountMap = σA)
    (hmem : mem.size = 96)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2347⟩
      [⟨0⟩, mintValueWord I, mintAccountWord I, ⟨445⟩, tokenSelWord I]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σA) k C) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hσA : EVMStateEquiv (burnFromAfterAllowance evmE I)
      (burnFromAfterAllowance evmS I) := hState
  have hmapA' : (burnFromAfterAllowance evmE I).accountMap = σA := hmapA
  have hsupplyE : burnFromSupplyWord evmE I = solcSlotWord σA I ⟨0⟩ := by
    unfold burnFromSupplyWord mintSupplyWord
    rw [burnFromAfterAllowance_codeOwner evmE I,
      show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
    simp only [Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWord, hmapA']
  have hsupplyEq : burnFromSupplyWord evmE I = burnFromSupplyWord evmS I :=
    hσA.storageLoad_codeOwner ⟨0⟩
  have hsupplyS : burnFromSupplyWord evmS I = solcSlotWord σA I ⟨0⟩ :=
    hsupplyEq.symm.trans hsupplyE
  by_cases hle : (mintValueWord I).toNat ≤ (solcSlotWord σA I ⟨0⟩).toNat
  · have hleE : (mintValueWord I).toNat ≤ (burnFromSupplyWord evmE I).toNat :=
      hsupplyE ▸ hle
    have hleS : (mintValueWord I).toNat ≤ (burnFromSupplyWord evmS I).toNat :=
      hsupplyS ▸ hle
    have hdebit : burnFromSupplyDebitWord evmE I =
        burnFromSupplyDebitWord evmS I := by
      exact congrArg (fun w : UInt256 => UInt256.ofNat
        (w.toNat - (mintValueWord I).toNat)) hsupplyEq
    have hσSupply : EVMStateEquiv
        (burnFromAfterSupply evmE I) (burnFromAfterSupply evmS I) := by
      unfold burnFromAfterSupply
      rw [← burnFromAfterAllowance_codeOwner evmE I,
        ← burnFromAfterAllowance_codeOwner evmS I]
      exact hσA.storageStore_codeOwner ⟨0⟩ hdebit
    have hmapSupply : (burnFromAfterSupply evmE I).accountMap =
        burnFromEvmSupplyMap σA I := by
      unfold burnFromAfterSupply burnFromEvmSupplyMap
      rw [storageStore_accountMap,
        show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
        hmapA', burnFromSupplyDebitWord_eq_sub evmE I hleE, hsupplyE]
    have hbalanceE : burnFromBalanceWord evmE I =
        solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I) := by
      unfold burnFromBalanceWord
      rw [show evmE.executionEnv.codeOwner = I.codeOwner from rfl]
      simp only [Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, solcSlotWord, hmapSupply]
    have hbalanceEq : burnFromBalanceWord evmE I =
        burnFromBalanceWord evmS I := by
      unfold burnFromBalanceWord
      rw [← burnFromAfterSupply_codeOwner evmE I,
        ← burnFromAfterSupply_codeOwner evmS I]
      exact hσSupply.storageLoad_codeOwner (mintBalanceSlot I)
    have hbalanceS : burnFromBalanceWord evmS I =
        solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I) :=
      hbalanceEq.symm.trans hbalanceE
    by_cases hbal : (mintValueWord I).toNat ≤
        (solcSlotWord (burnFromEvmSupplyMap σA I) I (mintBalanceSlot I)).toNat
    · have hbalE : (mintValueWord I).toNat ≤
          (burnFromBalanceWord evmE I).toNat := hbalanceE ▸ hbal
      have hbalS : (mintValueWord I).toNat ≤
          (burnFromBalanceWord evmS I).toNat := hbalanceS ▸ hbal
      have hbalanceDebit : burnFromBalanceDebitWord evmE I =
          burnFromBalanceDebitWord evmS I := by
        exact congrArg (fun w : UInt256 => UInt256.ofNat
          (w.toNat - (mintValueWord I).toNat)) hbalanceEq
      have hσPost : EVMStateEquiv
          (burnFromPostState evmE I) (burnFromPostState evmS I) := by
        unfold burnFromPostState
        rw [← burnFromAfterSupply_codeOwner evmE I,
          ← burnFromAfterSupply_codeOwner evmS I]
        exact hσSupply.storageStore_codeOwner (mintBalanceSlot I) hbalanceDebit
      have hmapPost : (burnFromPostState evmE I).accountMap =
          burnFromEvmPostMap σA I := by
        unfold burnFromPostState burnFromEvmPostMap
        rw [storageStore_accountMap,
          show evmE.executionEnv.codeOwner = I.codeOwner from rfl,
          hmapSupply, burnFromBalanceDebitWord_eq_sub evmE I hbalE, hbalanceE]
      have hbody := burnFromBodyReturns evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl)
        hallow hleS hbalS
      have henc : returnEquiv (UInt256.toByteArray (⟨1⟩ : UInt256))
          (some [(.bool true)]) burnFromTransition.returnType :=
        returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)
      exact (burnFromX_return (g := Sat256.ofUInt256 g)
          hperm hcanon hmem hread hle hbal hreach)
        |>.reEquivExecutionGenEVMStateEquiv hcode hd hdec hbody
          (by
            have hcreatedA : (burnFromAfterAllowance evmE I).createdAccounts =
                cA := by
              unfold burnFromAfterAllowance
              split
              · simp [storageStore_createdAccounts, evmE, initState]
              · rfl
            rw [burnFromPostState, storageStore_createdAccounts,
              burnFromAfterSupply, storageStore_createdAccounts, hcreatedA])
          (accountMapEquiv.of_eq (by simpa [hmapPost])) hσPost henc
    · have hunderE : (solcSlotWord (burnFromEvmSupplyMap σA I) I
          (mintBalanceSlot I)).toNat < (mintValueWord I).toNat := by omega
      have hunderS : (burnFromBalanceWord evmS I).toNat <
          (mintValueWord I).toNat := by rw [hbalanceS]; exact hunderE
      have hbody := burnFromBodyReverts_balance evmS I
        (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hleS hunderS
      exact (burnFromX_balanceUnderflow (g := Sat256.ofUInt256 g)
          hperm hcanon hmem hle hunderE hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hunderE : (solcSlotWord σA I ⟨0⟩).toNat <
        (mintValueWord I).toNat := by omega
    have hunderS : (burnFromSupplyWord evmS I).toNat <
        (mintValueWord I).toNat := by rw [hsupplyS]; exact hunderE
    have hbody := burnFromBodyReverts_supply evmS I
      (by simp only [evmS, initState]; exact hwv) (by rfl) hallow hunderS
    exact (burnFromX_supplyUnderflow (g := Sat256.ofUInt256 g)
        hunderE hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

theorem tokenBurnFromBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = tokenBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x79, 0xcc, 0x67, 0x90]⟩)
    (hreach : ∃ k C, RD tokenBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨419⟩ [tokenSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz4 := tokenBurnFromSelector_size hsel
  have hd := tokenDispatch_burnFrom (cd := I.calldata) hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanonFrom : (mintAccountWord I).toNat < EVM.addressModulus
      · have hdec := tokenDecode_burnFrom_ok (I := I) hsz68 hbig
          hcanonFrom
        let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
        let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hσ : EVMStateEquiv evmE evmS := by
          simpa [evmE, evmS] using
            EVMStateEquiv.initState (g := Sat256.ofUInt256 g) hAccounts
        have hallowWordE : burnFromAllowanceWord evmE I =
            solcSlotWord σ_evm I (burnFromAllowanceSlot I) := by
          simpa [burnFromAllowanceWord, solcSlotWord,
            codeOwnerStorageWord] using
            (codeOwnerStorageWord_initState
              (g := Sat256.ofUInt256 g) (σ := σ_evm)
              (slot := burnFromAllowanceSlot I) (cA := cA)
              (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A) (I := I))
        have hallowWordS : burnFromAllowanceWord evmS I =
            solcSlotWord σ_evm I (burnFromAllowanceSlot I) := by
          rw [show burnFromAllowanceWord evmS I =
              burnFromAllowanceWord evmE I from
                (hσ.storageLoad_codeOwner (burnFromAllowanceSlot I)).symm,
            hallowWordE]
        by_cases hself : mintAccountWord I = solcSourceWord I
        · have hspendE : burnFromShouldSpend evmE I = false := by
            cases hs : burnFromShouldSpend evmE I with
            | false => rfl
            | true => exact False.elim (((burnFromShouldSpend_iff evmE I hcanonFrom).mp hs).1 hself)
          have hspendS : burnFromShouldSpend evmS I = false := by
            cases hs : burnFromShouldSpend evmS I with
            | false => rfl
            | true => exact False.elim (((burnFromShouldSpend_iff evmS I hcanonFrom).mp hs).1 hself)
          have hState : EVMStateEquiv
              (burnFromAfterAllowance evmE I)
              (burnFromAfterAllowance evmS I) := by
            simpa [burnFromAfterAllowance, hspendE, hspendS] using hσ
          have hmapA : (burnFromAfterAllowance evmE I).accountMap =
              σ_evm := by
            rw [burnFromAfterAllowance, hspendE]
            rfl
          exact burnFromTailCore hcode hperm hwv hd hdec hcanonFrom
            (by intro hs; rw [hspendS] at hs; cases hs)
            hState hmapA solcFreePtrMem_size solcFreePtrMem_read64
            (burnFromX_self_to_supply (g := Sat256.ofUInt256 g)
              hsz68 hsize hbig hcanonFrom hself hreach)
        · by_cases hmax : solcSlotWord σ_evm I (burnFromAllowanceSlot I) =
              tokenTransferFromMaxWord
          · have hspendE : burnFromShouldSpend evmE I = false := by
              cases hs : burnFromShouldSpend evmE I with
              | false => rfl
              | true => exact False.elim (((burnFromShouldSpend_iff evmE I hcanonFrom).mp hs).2
                  (by rw [hallowWordE]; exact hmax))
            have hspendS : burnFromShouldSpend evmS I = false := by
              cases hs : burnFromShouldSpend evmS I with
              | false => rfl
              | true => exact False.elim (((burnFromShouldSpend_iff evmS I hcanonFrom).mp hs).2
                  (by rw [hallowWordS]; exact hmax))
            have hState : EVMStateEquiv
                (burnFromAfterAllowance evmE I)
                (burnFromAfterAllowance evmS I) := by
              simpa [burnFromAfterAllowance, hspendE, hspendS] using hσ
            have hmapA : (burnFromAfterAllowance evmE I).accountMap =
                σ_evm := by
              rw [burnFromAfterAllowance, hspendE]
              rfl
            exact burnFromTailCore hcode hperm hwv hd hdec hcanonFrom
              (by intro hs; rw [hspendS] at hs; cases hs)
              hState hmapA (burnFromAllowanceMem_size I)
              (burnFromAllowanceMem_read64 I)
              (burnFromX_max_to_supply (g := Sat256.ofUInt256 g)
                hsz68 hsize hbig hcanonFrom hself hmax hreach)
          · have hspendE : burnFromShouldSpend evmE I = true :=
              (burnFromShouldSpend_iff evmE I hcanonFrom).mpr
                ⟨hself, by rwa [hallowWordE]⟩
            have hspendS : burnFromShouldSpend evmS I = true :=
              (burnFromShouldSpend_iff evmS I hcanonFrom).mpr
                ⟨hself, by rwa [hallowWordS]⟩
            by_cases hle : (mintValueWord I).toNat ≤
                (solcSlotWord σ_evm I (burnFromAllowanceSlot I)).toNat
            · have hdebit : burnFromAllowanceDebitWord evmE I =
                  burnFromAllowanceDebitWord evmS I := by
                unfold burnFromAllowanceDebitWord
                rw [hallowWordE, hallowWordS]
              have hState : EVMStateEquiv
                  (burnFromAfterAllowance evmE I)
                  (burnFromAfterAllowance evmS I) := by
                simp only [burnFromAfterAllowance, hspendE, hspendS,
                  if_true]
                exact hσ.storageStore_codeOwner
                  (burnFromAllowanceSlot I) hdebit
              have hmapA : (burnFromAfterAllowance evmE I).accountMap =
                  burnFromEvmAllowanceMap σ_evm I := by
                rw [burnFromAfterAllowance, if_pos hspendE,
                  storageStore_accountMap]
                change sstoreAccountMap I.codeOwner σ_evm
                  (burnFromAllowanceSlot I)
                  (burnFromAllowanceDebitWord evmE I) = _
                unfold burnFromEvmAllowanceMap
                apply congrArg (sstoreAccountMap I.codeOwner σ_evm
                  (burnFromAllowanceSlot I))
                apply u256_inj
                rw [burnFromAllowanceDebitWord_toNat evmE I,
                  hallowWordE, usub_toNat hle]
              exact burnFromTailCore hcode hperm hwv hd hdec hcanonFrom
                (by intro _; rwa [hallowWordS]) hState hmapA
                (burnFromAllowanceStoreMem_size I)
                (burnFromAllowanceStoreMem_read64 I)
                (burnFromX_spend_stored (g := Sat256.ofUInt256 g)
                  hsz68 hsize hbig hperm hcanonFrom hself hmax hle hreach)
            · have hunder : (solcSlotWord σ_evm I
                  (burnFromAllowanceSlot I)).toNat <
                  (mintValueWord I).toNat := by omega
              have hbody := burnFromBodyReverts_allowance evmS I
                (by simp only [evmS, initState]; exact hwv) (by rfl) hspendS
                (by rwa [hallowWordS])
              exact (burnFromX_spend_underflow (g := Sat256.ofUInt256 g)
                  hsz68 hsize hbig hcanonFrom hself hmax hunder hreach)
                |>.reEquivExecutionRevert hcode hd hdec hbody
      · have hdec := tokenDecode_burnFrom_none_noncanon
          (I := I) hsz68 hbig hcanonFrom
        have hnc : UInt256.eq (mintAccountWord I)
            (UInt256.land (mintAccountWord I) solcAddrMask) = ⟨0⟩ :=
          uInt256_eq_zero_of_ne (fun he => hcanonFrom (solcAddrCanonical_of_clean he))
        exact (burnFromX_noncanon (g := Sat256.ofUInt256 g)
            hsz68 hsize hbig hnc hreach)
          |>.reEquivDecodingFailed hcode hd hdec
    · have hbigge : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := tokenDecode_burnFrom_none_huge (I := I) hbigge
      exact (burnFromX_hugearg (g := Sat256.ofUInt256 g)
          hsz4 hsize hbigge hreach)
        |>.reEquivDecodingFailed hcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := tokenDecode_burnFrom_none_short (I := I) hsz4 hshort
    exact (burnFromX_shortarg (g := Sat256.ofUInt256 g)
        hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.ActAmmToken
