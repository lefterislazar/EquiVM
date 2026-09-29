import Benchmarks.ActAmm4.BurnSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4BurnAfterAmount1Store_balanceOf_none (evm : EVM.State)
    (I : ExecutionEnv) :
    (amm4BurnAfterAmount1Store evm I).get? "balanceOf" = none := by
  simp [amm4BurnAfterAmount1Store, amm4BurnAfterNum1Store,
    amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnEvalSenderRef {evm0 evm2 : EVM.State} (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source) :
    evalStorageRef config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I }
      evm2 (balanceOfRef sender) = .ok (amm4TransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferSenderRef, sender, envValue, hsrc]

theorem amm4BurnEvalSenderBalance {evm0 evm2 : EVM.State} (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source) :
    evalExpr? config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I }
      evm2 (.storage (balanceOfRef sender)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
            (amm4TransferSenderSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I })
    (evm := evm2)
    (slot := balanceOfRef sender)
    (er := amm4TransferSenderRef I)
    (t := .int uint256Int)
    (loc := wordLoc (amm4TransferSenderSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm2
      evm2.executionEnv.codeOwner (amm4TransferSenderSlot I)).toNat))
    (amm4BurnAfterAmount1Store_balanceOf_none evm0 I)
    (amm4BurnEvalSenderRef I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
    (by simpa [amm4TransferSenderSlot] using
      amm4StorageLocLoad_uint256 evm2 (amm4TransferSenderSlot I))

theorem amm4BurnEvalSenderDebit_revert {evm0 evm2 : EVM.State}
    (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source)
    (hunder :
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).toNat <
      (amm4BurnLiquidityWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I }
      evm2 (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity")) =
        .revert := by
  exact amm4EvalCheckedSub_revert (amm4BurnEvalSenderBalance I hsrc)
    (amm4BurnEvalLiquidityAfterAmount1 (evm := evm0) (evm2 := evm2) (I := I)) hunder

def amm4BurnSenderDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (amm4TransferSenderSlot I)).toNat - (amm4BurnLiquidityWord I).toNat)

def amm4BurnAfterSender (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (amm4TransferSenderSlot I) (amm4BurnSenderDebitWord evm I)

theorem amm4BurnEvalSenderDebit_ok {evm0 evm2 : EVM.State}
    (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source)
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).toNat) :
    evalExpr? config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I }
      evm2 (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity")) =
        .ok (.int (Int.ofNat
          ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
            (amm4TransferSenderSlot I)).toNat -
            (amm4BurnLiquidityWord I).toNat))) := by
  exact amm4EvalCheckedSub_ok (amm4BurnEvalSenderBalance I hsrc)
    (amm4BurnEvalLiquidityAfterAmount1 (evm := evm0) (evm2 := evm2) (I := I))
    hle (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
      (amm4TransferSenderSlot I)).val.isLt

theorem amm4BurnAssignSender {evm0 evm2 : EVM.State} (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source)
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).toNat) :
    assignStorageRef? config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I }
      evm2 .storage (balanceOfRef sender)
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
          (amm4TransferSenderSlot I)).toNat -
          (amm4BurnLiquidityWord I).toNat))) =
      .ok ({ contract := contract, locals := amm4BurnAfterAmount1Store evm0 I },
        amm4BurnAfterSender evm2 I) := by
  have hword : (amm4BurnSenderDebitWord evm2 I).toNat =
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).toNat -
        (amm4BurnLiquidityWord I).toNat := by
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).val.isLt)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := amm4BurnAfterAmount1Store evm0 I })
    (evm := evm2) (evm' := amm4BurnAfterSender evm2 I)
    (slot := balanceOfRef sender)
    (er := amm4TransferSenderRef I)
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (amm4TransferSenderSlot I))
    (n := Int.ofNat ((Solm.EVM.storageLoad evm2
      evm2.executionEnv.codeOwner (amm4TransferSenderSlot I)).toNat -
        (amm4BurnLiquidityWord I).toNat))
    (amm4BurnAfterAmount1Store_balanceOf_none evm0 I)
    (amm4BurnEvalSenderRef I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
    (by simpa [amm4BurnAfterSender, hword] using
      (amm4StorageLocStore_uint256 evm2 (amm4TransferSenderSlot I)
        (amm4BurnSenderDebitWord evm2 I)))

def amm4BurnSourcePrefixSupply : List Stmt :=
  amm4BurnSourcePrefixAmounts ++
    [.assign .storage totalSupplyRef
      (checkedSub (.storage totalSupplyRef) (.var "liquidity"))]

theorem amm4BurnSourceSenderUnderflow {evm evm2 : EVM.State}
    (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm amm4BurnSourcePrefixSupply
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I } evm2))
    (hsrc : evm2.executionEnv.source = I.source)
    (hunder :
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).toNat <
      (amm4BurnLiquidityWord I).toNat) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have heval := amm4BurnEvalSenderDebit_revert (evm0 := evm) I hsrc hunder
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm I }
      evm2 (burnTransition.body.drop 9) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixSupply, amm4BurnSourcePrefixAmounts,
      amm4BurnSourcePrefixNum1, amm4BurnSourcePrefixAmount0,
      burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4BurnSourceSenderOk {evm evm2 : EVM.State}
    (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm amm4BurnSourcePrefixSupply
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I } evm2))
    (hsrc : evm2.executionEnv.source = I.source)
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4TransferSenderSlot I)).toNat) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixSupply ++
        [.assign .storage (balanceOfRef sender)
          (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity"))])
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I }
        (amm4BurnAfterSender evm2 I)) := by
  have heval := amm4BurnEvalSenderDebit_ok (evm0 := evm) I hsrc hle
  have hassign := amm4BurnAssignSender (evm0 := evm) I hsrc hle
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm I }
      evm2 [.assign .storage (balanceOfRef sender)
        (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity"))]
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I }
        (amm4BurnAfterSender evm2 I)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
