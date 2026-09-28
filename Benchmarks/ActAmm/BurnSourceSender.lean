import Benchmarks.ActAmm.BurnSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammBurnAfterAmount1Store_balanceOf_none (evm : EVM.State)
    (I : ExecutionEnv) :
    (ammBurnAfterAmount1Store evm I).get? "balanceOf" = none := by
  simp [ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
    ammBurnAfterAmount0Store, ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnEvalSenderRef {evm0 evm2 : EVM.State} (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source) :
    evalStorageRef config
      { contract := contract, locals := ammBurnAfterAmount1Store evm0 I }
      evm2 (balanceOfRef sender) = .ok (ammTransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferSenderRef, sender, envValue, hsrc]

theorem ammBurnEvalSenderBalance {evm0 evm2 : EVM.State} (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source) :
    evalExpr? config
      { contract := contract, locals := ammBurnAfterAmount1Store evm0 I }
      evm2 (.storage (balanceOfRef sender)) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
            (ammTransferSenderSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := ammBurnAfterAmount1Store evm0 I })
    (evm := evm2)
    (slot := balanceOfRef sender)
    (er := ammTransferSenderRef I)
    (t := .int uint256Int)
    (loc := wordLoc (ammTransferSenderSlot I))
    (value := .int (Int.ofNat (Solm.EVM.storageLoad evm2
      evm2.executionEnv.codeOwner (ammTransferSenderSlot I)).toNat))
    (ammBurnAfterAmount1Store_balanceOf_none evm0 I)
    (ammBurnEvalSenderRef I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      ammTransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
    (by simpa [ammTransferSenderSlot] using
      ammStorageLocLoad_uint256 evm2 (ammTransferSenderSlot I))

theorem ammBurnEvalSenderDebit_revert {evm0 evm2 : EVM.State}
    (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source)
    (hunder :
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).toNat <
      (ammBurnLiquidityWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammBurnAfterAmount1Store evm0 I }
      evm2 (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity")) =
        .revert := by
  exact ammEvalCheckedSub_revert (ammBurnEvalSenderBalance I hsrc)
    (ammBurnEvalLiquidityAfterAmount1 (evm := evm0) (evm2 := evm2) (I := I)) hunder

def ammBurnSenderDebitWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (ammTransferSenderSlot I)).toNat - (ammBurnLiquidityWord I).toNat)

def ammBurnAfterSender (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (ammTransferSenderSlot I) (ammBurnSenderDebitWord evm I)

theorem ammBurnEvalSenderDebit_ok {evm0 evm2 : EVM.State}
    (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source)
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).toNat) :
    evalExpr? config
      { contract := contract, locals := ammBurnAfterAmount1Store evm0 I }
      evm2 (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity")) =
        .ok (.int (Int.ofNat
          ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
            (ammTransferSenderSlot I)).toNat -
            (ammBurnLiquidityWord I).toNat))) := by
  exact ammEvalCheckedSub_ok (ammBurnEvalSenderBalance I hsrc)
    (ammBurnEvalLiquidityAfterAmount1 (evm := evm0) (evm2 := evm2) (I := I))
    hle (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
      (ammTransferSenderSlot I)).val.isLt

theorem ammBurnAssignSender {evm0 evm2 : EVM.State} (I : ExecutionEnv)
    (hsrc : evm2.executionEnv.source = I.source)
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).toNat) :
    assignStorageRef? config
      { contract := contract, locals := ammBurnAfterAmount1Store evm0 I }
      evm2 .storage (balanceOfRef sender)
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
          (ammTransferSenderSlot I)).toNat -
          (ammBurnLiquidityWord I).toNat))) =
      .ok ({ contract := contract, locals := ammBurnAfterAmount1Store evm0 I },
        ammBurnAfterSender evm2 I) := by
  have hword : (ammBurnSenderDebitWord evm2 I).toNat =
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).toNat -
        (ammBurnLiquidityWord I).toNat := by
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _)
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).val.isLt)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals := ammBurnAfterAmount1Store evm0 I })
    (evm := evm2) (evm' := ammBurnAfterSender evm2 I)
    (slot := balanceOfRef sender)
    (er := ammTransferSenderRef I)
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (ammTransferSenderSlot I))
    (n := Int.ofNat ((Solm.EVM.storageLoad evm2
      evm2.executionEnv.codeOwner (ammTransferSenderSlot I)).toNat -
        (ammBurnLiquidityWord I).toNat))
    (ammBurnAfterAmount1Store_balanceOf_none evm0 I)
    (ammBurnEvalSenderRef I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      ammTransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
    (by simpa [ammBurnAfterSender, hword] using
      (ammStorageLocStore_uint256 evm2 (ammTransferSenderSlot I)
        (ammBurnSenderDebitWord evm2 I)))

def ammBurnSourcePrefixSupply : List Stmt :=
  ammBurnSourcePrefixAmounts ++
    [.assign .storage totalSupplyRef
      (checkedSub (.storage totalSupplyRef) (.var "liquidity"))]

theorem ammBurnSourceSenderUnderflow {evm evm2 : EVM.State}
    (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm ammBurnSourcePrefixSupply
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm2))
    (hsrc : evm2.executionEnv.source = I.source)
    (hunder :
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).toNat <
      (ammBurnLiquidityWord I).toNat) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have heval := ammBurnEvalSenderDebit_revert (evm0 := evm) I hsrc hunder
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I }
      evm2 (burnTransition.body.drop 9) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixSupply, ammBurnSourcePrefixAmounts,
      ammBurnSourcePrefixNum1, ammBurnSourcePrefixAmount0,
      burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammBurnSourceSenderOk {evm evm2 : EVM.State}
    (I : ExecutionEnv)
    (hprefix : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm ammBurnSourcePrefixSupply
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm2))
    (hsrc : evm2.executionEnv.source = I.source)
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammTransferSenderSlot I)).toNat) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixSupply ++
        [.assign .storage (balanceOfRef sender)
          (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity"))])
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I }
        (ammBurnAfterSender evm2 I)) := by
  have heval := ammBurnEvalSenderDebit_ok (evm0 := evm) I hsrc hle
  have hassign := ammBurnAssignSender (evm0 := evm) I hsrc hle
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I }
      evm2 [.assign .storage (balanceOfRef sender)
        (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity"))]
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I }
        (ammBurnAfterSender evm2 I)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
