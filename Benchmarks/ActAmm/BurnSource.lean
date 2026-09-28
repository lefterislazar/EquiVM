import Benchmarks.ActAmm.BurnBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammBurnSourceZeroSupply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hguard := ammMintEvalSupplyGuard_false (evm := evm)
    (locals := ammBurnStore I) (by simp [ammBurnStore]) hzero
  have hblock : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm burnTransition.body .reverted := by
    simp only [burnTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammBurnSourceGuarded (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0))])
      (.ok { contract := contract, locals := ammBurnStore I } evm) := by
  have hguard := ammMintEvalSupplyGuard_true (evm := evm)
    (locals := ammBurnStore I) (by simp [ammBurnStore]) hnonzero
  simp only [nonpayable, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil

theorem ammBurnEvalLiquidity {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := ammBurnStore I } evm
      (.var "liquidity") =
      .ok (.int (Int.ofNat (ammBurnLiquidityWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammBurnStore]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem ammBurnEvalAmount0Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    (hover : UInt256.size ≤ (ammBurnLiquidityWord I).toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config { contract := contract, locals := ammBurnStore I } evm
      (checkedMul (.var "liquidity") (.storage reserve0Ref)) = .revert := by
  exact ammEvalCheckedMul_revert ammBurnEvalLiquidity
    (ammMintEvalReserve0 (evm := evm) (locals := ammBurnStore I)
      (by simp [ammBurnStore])) hover

def ammBurnAmount0Numerator (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  (ammBurnLiquidityWord I).toNat *
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat

def ammBurnAfterNum0Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (ammBurnStore I).insert "amount0Numerator"
    (.int (Int.ofNat (ammBurnAmount0Numerator evm I)))

theorem ammBurnEvalAmount0Numerator_ok {evm : EVM.State} {I : ExecutionEnv}
    (hfit : ammBurnAmount0Numerator evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := ammBurnStore I } evm
      (checkedMul (.var "liquidity") (.storage reserve0Ref)) =
      .ok (.int (Int.ofNat (ammBurnAmount0Numerator evm I))) := by
  exact ammEvalCheckedMul_ok ammBurnEvalLiquidity
    (ammMintEvalReserve0 (evm := evm) (locals := ammBurnStore I)
      (by simp [ammBurnStore])) hfit

theorem ammBurnSourceNum0Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit : ammBurnAmount0Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         .letDecl "amount0Numerator" (some uint256)
           (checkedMul (.var "liquidity") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := ammBurnAfterNum0Store evm I } evm) := by
  have hprefix := ammBurnSourceGuarded evm I hwv hnonzero
  have heval := ammBurnEvalAmount0Numerator_ok (evm := evm) (I := I) hfit
  have htail : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm [.letDecl "amount0Numerator" (some uint256)
        (checkedMul (.var "liquidity") (.storage reserve0Ref))]
      (.ok { contract := contract, locals := ammBurnAfterNum0Store evm I } evm) := by
    simpa [ammBurnAfterNum0Store] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  simpa [List.append_assoc] using execBlock_append hprefix htail

def ammBurnAmount0Value (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  ammBurnAmount0Numerator evm I /
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat

def ammBurnAfterAmount0Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (ammBurnAfterNum0Store evm I).insert "amount0"
    (.int (Int.ofNat (ammBurnAmount0Value evm I)))

theorem ammBurnEvalNum0Local {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := ammBurnAfterNum0Store evm I }
      evm (.var "amount0Numerator") =
        .ok (.int (Int.ofNat (ammBurnAmount0Numerator evm I))) := by
  simp [ammBurnAfterNum0Store, evalExpr?, EvalResult.ofOption]

theorem ammBurnEvalSupplyAfterNum0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := ammBurnAfterNum0Store evm I }
      evm (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply ammMintEvalSupply
  simp [ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnSourceAmount0Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit : ammBurnAmount0Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         .letDecl "amount0Numerator" (some uint256)
           (checkedMul (.var "liquidity") (.storage reserve0Ref))] ++
        checkedDivInto "amount0" (.var "amount0Numerator")
          (.storage totalSupplyRef))
      (.ok { contract := contract, locals := ammBurnAfterAmount0Store evm I } evm) := by
  have hprefix := ammBurnSourceNum0Ok evm I hwv hnonzero hfit
  have hpositive : 0 < (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨0⟩).toNat := by
    have hn : (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).toNat ≠ 0 := by
      intro hz
      exact hnonzero (uint256_toNat_eq_zero hz)
    omega
  have hguard := ammEvalNatNeZero_true
    (ammBurnEvalSupplyAfterNum0 (I := I)) hpositive
  have hdiv := ammEvalNatDiv_ok
    (ammBurnEvalNum0Local (I := I))
    (ammBurnEvalSupplyAfterNum0 (I := I)) hpositive
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterNum0Store evm I }
      evm (checkedDivInto "amount0" (.var "amount0Numerator")
        (.storage totalSupplyRef))
      (.ok { contract := contract, locals := ammBurnAfterAmount0Store evm I } evm) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [ammBurnAfterAmount0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [List.append_assoc] using execBlock_append hprefix htail

def ammBurnSourcePrefixAmount0 : List Stmt :=
  nonpayable ++
    [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
     .letDecl "amount0Numerator" (some uint256)
       (checkedMul (.var "liquidity") (.storage reserve0Ref))] ++
    checkedDivInto "amount0" (.var "amount0Numerator")
      (.storage totalSupplyRef)

def ammBurnAmount1Numerator (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  (ammBurnLiquidityWord I).toNat *
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat

def ammBurnAfterNum1Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (ammBurnAfterAmount0Store evm I).insert "amount1Numerator"
    (.int (Int.ofNat (ammBurnAmount1Numerator evm I)))

theorem ammBurnEvalLiquidityAfterAmount0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount0Store evm I } evm (.var "liquidity") =
      .ok (.int (Int.ofNat (ammBurnLiquidityWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammBurnAfterAmount0Store,
    ammBurnAfterNum0Store, ammBurnStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem ammBurnEvalReserve1AfterAmount0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount0Store evm I } evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply ammMintEvalReserve1
  simp [ammBurnAfterAmount0Store, ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnEvalAmount1Numerator_ok {evm : EVM.State} {I : ExecutionEnv}
    (hfit : ammBurnAmount1Numerator evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount0Store evm I } evm
      (checkedMul (.var "liquidity") (.storage reserve1Ref)) =
      .ok (.int (Int.ofNat (ammBurnAmount1Numerator evm I))) := by
  exact ammEvalCheckedMul_ok ammBurnEvalLiquidityAfterAmount0
    ammBurnEvalReserve1AfterAmount0 hfit

theorem ammBurnEvalAmount1Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    (hover : UInt256.size ≤ ammBurnAmount1Numerator evm I) :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount0Store evm I } evm
      (checkedMul (.var "liquidity") (.storage reserve1Ref)) = .revert := by
  exact ammEvalCheckedMul_revert ammBurnEvalLiquidityAfterAmount0
    ammBurnEvalReserve1AfterAmount0 hover

theorem ammBurnSourceNum1Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : ammBurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : ammBurnAmount1Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixAmount0 ++
        [.letDecl "amount1Numerator" (some uint256)
          (checkedMul (.var "liquidity") (.storage reserve1Ref))])
      (.ok { contract := contract, locals := ammBurnAfterNum1Store evm I } evm) := by
  have hprefix := ammBurnSourceAmount0Ok evm I hwv hnonzero hfit0
  have heval := ammBurnEvalAmount1Numerator_ok (evm := evm) (I := I) hfit1
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount0Store evm I } evm
      [.letDecl "amount1Numerator" (some uint256)
        (checkedMul (.var "liquidity") (.storage reserve1Ref))]
      (.ok { contract := contract, locals := ammBurnAfterNum1Store evm I } evm) := by
    simpa [ammBurnAfterNum1Store] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  simpa [ammBurnSourcePrefixAmount0] using execBlock_append hprefix htail

theorem ammBurnSourceNum1Overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : ammBurnAmount0Numerator evm I < UInt256.size)
    (hover1 : UInt256.size ≤ ammBurnAmount1Numerator evm I) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hprefix := ammBurnSourceAmount0Ok evm I hwv hnonzero hfit0
  have heval := ammBurnEvalAmount1Numerator_revert (evm := evm)
    (I := I) hover1
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount0Store evm I } evm
      (burnTransition.body.drop 5) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammBurnSourcePrefixNum1 : List Stmt :=
  ammBurnSourcePrefixAmount0 ++
    [.letDecl "amount1Numerator" (some uint256)
      (checkedMul (.var "liquidity") (.storage reserve1Ref))]

def ammBurnAmount1Value (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  ammBurnAmount1Numerator evm I /
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat

def ammBurnAfterAmount1Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (ammBurnAfterNum1Store evm I).insert "amount1"
    (.int (Int.ofNat (ammBurnAmount1Value evm I)))

theorem ammBurnEvalNum1Local {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := ammBurnAfterNum1Store evm I }
      evm (.var "amount1Numerator") =
        .ok (.int (Int.ofNat (ammBurnAmount1Numerator evm I))) := by
  simp [ammBurnAfterNum1Store, evalExpr?, EvalResult.ofOption]

theorem ammBurnEvalSupplyAfterNum1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := ammBurnAfterNum1Store evm I }
      evm (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply ammMintEvalSupply
  simp [ammBurnAfterNum1Store, ammBurnAfterAmount0Store,
    ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnSourceAmount1Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : ammBurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : ammBurnAmount1Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixNum1 ++
        checkedDivInto "amount1" (.var "amount1Numerator")
          (.storage totalSupplyRef))
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm) := by
  have hprefix := ammBurnSourceNum1Ok evm I hwv hnonzero hfit0 hfit1
  have hpositive : 0 < (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨0⟩).toNat := by
    have hn : (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).toNat ≠ 0 := by
      intro hz
      exact hnonzero (uint256_toNat_eq_zero hz)
    omega
  have hguard := ammEvalNatNeZero_true
    (ammBurnEvalSupplyAfterNum1 (I := I)) hpositive
  have hdiv := ammEvalNatDiv_ok
    (ammBurnEvalNum1Local (I := I))
    (ammBurnEvalSupplyAfterNum1 (I := I)) hpositive
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterNum1Store evm I }
      evm (checkedDivInto "amount1" (.var "amount1Numerator")
        (.storage totalSupplyRef))
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [ammBurnAfterAmount1Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [ammBurnSourcePrefixNum1, List.append_assoc] using
    execBlock_append hprefix htail

def ammBurnSourcePrefixAmounts : List Stmt :=
  ammBurnSourcePrefixNum1 ++
    checkedDivInto "amount1" (.var "amount1Numerator")
      (.storage totalSupplyRef)

theorem ammBurnEvalLiquidityAfterAmount1 {evm evm2 : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount1Store evm I } evm2 (.var "liquidity") =
      .ok (.int (Int.ofNat (ammBurnLiquidityWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammBurnAfterAmount1Store,
    ammBurnAfterNum1Store, ammBurnAfterAmount0Store,
    ammBurnAfterNum0Store, ammBurnStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem ammBurnEvalSupplyAfterAmount1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount1Store evm I } evm (.storage totalSupplyRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply ammMintEvalSupply
  simp [ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
    ammBurnAfterAmount0Store, ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnSourceSupplyUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : ammBurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : ammBurnAmount1Numerator evm I < UInt256.size)
    (hunder : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat <
      (ammBurnLiquidityWord I).toNat) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hprefix := ammBurnSourceAmount1Ok evm I hwv hnonzero hfit0 hfit1
  have heval := ammEvalCheckedSub_revert
    (ammBurnEvalSupplyAfterAmount1 (I := I))
    (ammBurnEvalLiquidityAfterAmount1 (I := I)) hunder
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm
      (burnTransition.body.drop 8) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammBurnSupplyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
      (ammBurnLiquidityWord I).toNat)

def ammBurnAfterSupply (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (ammBurnSupplyWord evm I)

theorem ammBurnEvalSupplySubOk {evm : EVM.State} {I : ExecutionEnv}
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    evalExpr? config { contract := contract, locals :=
      ammBurnAfterAmount1Store evm I } evm
      (checkedSub (.storage totalSupplyRef) (.var "liquidity")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
          (ammBurnLiquidityWord I).toNat))) := by
  exact ammEvalCheckedSub_ok (ammBurnEvalSupplyAfterAmount1 (I := I))
    (ammBurnEvalLiquidityAfterAmount1 (I := I)) hle
    (by exact (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨0⟩).val.isLt)

theorem ammBurnAssignSupply {evm : EVM.State} {I : ExecutionEnv}
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    assignStorageRef? config { contract := contract, locals :=
      (ammBurnAfterAmount1Store evm I) } evm .storage totalSupplyRef
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
          (ammBurnLiquidityWord I).toNat))) =
      .ok ({ contract := contract, locals := ammBurnAfterAmount1Store evm I },
        ammBurnAfterSupply evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (hbase := by simp [ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
      ammBurnAfterAmount0Store, ammBurnAfterNum0Store,
      ammBurnStore, totalSupplyRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  have hword : (ammBurnSupplyWord evm I).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
        (ammBurnLiquidityWord I).toNat := by
    exact ulit_toNat' _ (by
      have hlt := (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).val.isLt
      change (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).toNat < UInt256.size at hlt
      omega)
  simpa [ammBurnAfterSupply, hword] using
    ammStorageLocStore_uint256 evm ⟨0⟩ (ammBurnSupplyWord evm I)

theorem ammBurnSourceSupplyOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : ammBurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : ammBurnAmount1Numerator evm I < UInt256.size)
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    ExecBlock config { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixAmounts ++
        [.assign .storage totalSupplyRef
          (checkedSub (.storage totalSupplyRef) (.var "liquidity"))])
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I }
        (ammBurnAfterSupply evm I)) := by
  have hprefix := ammBurnSourceAmount1Ok evm I hwv hnonzero hfit0 hfit1
  have heval := ammBurnEvalSupplySubOk (evm := evm) (I := I) hle
  have hassign := ammBurnAssignSupply (evm := evm) (I := I) hle
  have htail : ExecBlock config
      { contract := contract, locals := ammBurnAfterAmount1Store evm I } evm
      [.assign .storage totalSupplyRef
        (checkedSub (.storage totalSupplyRef) (.var "liquidity"))]
      (.ok { contract := contract, locals := ammBurnAfterAmount1Store evm I }
        (ammBurnAfterSupply evm I)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  simpa [ammBurnSourcePrefixAmounts] using execBlock_append hprefix htail

theorem ammBurnSourceAmount0NumeratorOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (ammBurnLiquidityWord I).toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hprefix := ammBurnSourceGuarded evm I hwv hnonzero
  have heval := ammBurnEvalAmount0Numerator_revert (evm := evm)
    (I := I) hover
  have htail : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm (burnTransition.body.drop 2) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammBurnStore I }
      evm burnTransition.body .reverted := by
    simpa [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm
