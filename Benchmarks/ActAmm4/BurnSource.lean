import Benchmarks.ActAmm4.BurnBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4BurnSourceZeroSupply (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hguard := amm4MintEvalSupplyGuard_false (evm := evm)
    (locals := amm4BurnStore I) (by simp [amm4BurnStore]) hzero
  have hblock : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm burnTransition.body .reverted := by
    simp only [burnTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem amm4BurnSourceGuarded (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0))])
      (.ok { contract := contract, locals := amm4BurnStore I } evm) := by
  have hguard := amm4MintEvalSupplyGuard_true (evm := evm)
    (locals := amm4BurnStore I) (by simp [amm4BurnStore]) hnonzero
  simp only [nonpayable, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil

theorem amm4BurnEvalLiquidity {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4BurnStore I } evm
      (.var "liquidity") =
      .ok (.int (Int.ofNat (amm4BurnLiquidityWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4BurnStore]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem amm4BurnEvalAmount0Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    (hover : UInt256.size ≤ (amm4BurnLiquidityWord I).toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4BurnStore I } evm
      (checkedMul (.var "liquidity") (.storage reserve0Ref)) = .revert := by
  exact amm4EvalCheckedMul_revert amm4BurnEvalLiquidity
    (amm4MintEvalReserve0 (evm := evm) (locals := amm4BurnStore I)
      (by simp [amm4BurnStore])) hover

def amm4BurnAmount0Numerator (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  (amm4BurnLiquidityWord I).toNat *
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat

def amm4BurnAfterNum0Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (amm4BurnStore I).insert "amount0Numerator"
    (.int (Int.ofNat (amm4BurnAmount0Numerator evm I)))

theorem amm4BurnEvalAmount0Numerator_ok {evm : EVM.State} {I : ExecutionEnv}
    (hfit : amm4BurnAmount0Numerator evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals := amm4BurnStore I } evm
      (checkedMul (.var "liquidity") (.storage reserve0Ref)) =
      .ok (.int (Int.ofNat (amm4BurnAmount0Numerator evm I))) := by
  exact amm4EvalCheckedMul_ok amm4BurnEvalLiquidity
    (amm4MintEvalReserve0 (evm := evm) (locals := amm4BurnStore I)
      (by simp [amm4BurnStore])) hfit

theorem amm4BurnSourceNum0Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit : amm4BurnAmount0Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         .letDecl "amount0Numerator" (some uint256)
           (checkedMul (.var "liquidity") (.storage reserve0Ref))])
      (.ok { contract := contract, locals := amm4BurnAfterNum0Store evm I } evm) := by
  have hprefix := amm4BurnSourceGuarded evm I hwv hnonzero
  have heval := amm4BurnEvalAmount0Numerator_ok (evm := evm) (I := I) hfit
  have htail : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm [.letDecl "amount0Numerator" (some uint256)
        (checkedMul (.var "liquidity") (.storage reserve0Ref))]
      (.ok { contract := contract, locals := amm4BurnAfterNum0Store evm I } evm) := by
    simpa [amm4BurnAfterNum0Store] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  simpa [List.append_assoc] using execBlock_append hprefix htail

def amm4BurnAmount0Value (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  amm4BurnAmount0Numerator evm I /
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat

def amm4BurnAfterAmount0Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (amm4BurnAfterNum0Store evm I).insert "amount0"
    (.int (Int.ofNat (amm4BurnAmount0Value evm I)))

theorem amm4BurnEvalNum0Local {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4BurnAfterNum0Store evm I }
      evm (.var "amount0Numerator") =
        .ok (.int (Int.ofNat (amm4BurnAmount0Numerator evm I))) := by
  simp [amm4BurnAfterNum0Store, evalExpr?, EvalResult.ofOption]

theorem amm4BurnEvalSupplyAfterNum0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4BurnAfterNum0Store evm I }
      evm (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply amm4MintEvalSupply
  simp [amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnSourceAmount0Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit : amm4BurnAmount0Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (nonpayable ++
        [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
         .letDecl "amount0Numerator" (some uint256)
           (checkedMul (.var "liquidity") (.storage reserve0Ref))] ++
        checkedDivInto "amount0" (.var "amount0Numerator")
          (.storage totalSupplyRef))
      (.ok { contract := contract, locals := amm4BurnAfterAmount0Store evm I } evm) := by
  have hprefix := amm4BurnSourceNum0Ok evm I hwv hnonzero hfit
  have hpositive : 0 < (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨0⟩).toNat := by
    have hn : (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).toNat ≠ 0 := by
      intro hz
      exact hnonzero (uint256_toNat_eq_zero hz)
    omega
  have hguard := amm4EvalNatNeZero_true
    (amm4BurnEvalSupplyAfterNum0 (I := I)) hpositive
  have hdiv := amm4EvalNatDiv_ok
    (amm4BurnEvalNum0Local (I := I))
    (amm4BurnEvalSupplyAfterNum0 (I := I)) hpositive
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterNum0Store evm I }
      evm (checkedDivInto "amount0" (.var "amount0Numerator")
        (.storage totalSupplyRef))
      (.ok { contract := contract, locals := amm4BurnAfterAmount0Store evm I } evm) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [amm4BurnAfterAmount0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [List.append_assoc] using execBlock_append hprefix htail

def amm4BurnSourcePrefixAmount0 : List Stmt :=
  nonpayable ++
    [.require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
     .letDecl "amount0Numerator" (some uint256)
       (checkedMul (.var "liquidity") (.storage reserve0Ref))] ++
    checkedDivInto "amount0" (.var "amount0Numerator")
      (.storage totalSupplyRef)

def amm4BurnAmount1Numerator (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  (amm4BurnLiquidityWord I).toNat *
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat

def amm4BurnAfterNum1Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (amm4BurnAfterAmount0Store evm I).insert "amount1Numerator"
    (.int (Int.ofNat (amm4BurnAmount1Numerator evm I)))

theorem amm4BurnEvalLiquidityAfterAmount0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount0Store evm I } evm (.var "liquidity") =
      .ok (.int (Int.ofNat (amm4BurnLiquidityWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4BurnAfterAmount0Store,
    amm4BurnAfterNum0Store, amm4BurnStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem amm4BurnEvalReserve1AfterAmount0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount0Store evm I } evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply amm4MintEvalReserve1
  simp [amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnEvalAmount1Numerator_ok {evm : EVM.State} {I : ExecutionEnv}
    (hfit : amm4BurnAmount1Numerator evm I < UInt256.size) :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount0Store evm I } evm
      (checkedMul (.var "liquidity") (.storage reserve1Ref)) =
      .ok (.int (Int.ofNat (amm4BurnAmount1Numerator evm I))) := by
  exact amm4EvalCheckedMul_ok amm4BurnEvalLiquidityAfterAmount0
    amm4BurnEvalReserve1AfterAmount0 hfit

theorem amm4BurnEvalAmount1Numerator_revert {evm : EVM.State} {I : ExecutionEnv}
    (hover : UInt256.size ≤ amm4BurnAmount1Numerator evm I) :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount0Store evm I } evm
      (checkedMul (.var "liquidity") (.storage reserve1Ref)) = .revert := by
  exact amm4EvalCheckedMul_revert amm4BurnEvalLiquidityAfterAmount0
    amm4BurnEvalReserve1AfterAmount0 hover

theorem amm4BurnSourceNum1Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : amm4BurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : amm4BurnAmount1Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixAmount0 ++
        [.letDecl "amount1Numerator" (some uint256)
          (checkedMul (.var "liquidity") (.storage reserve1Ref))])
      (.ok { contract := contract, locals := amm4BurnAfterNum1Store evm I } evm) := by
  have hprefix := amm4BurnSourceAmount0Ok evm I hwv hnonzero hfit0
  have heval := amm4BurnEvalAmount1Numerator_ok (evm := evm) (I := I) hfit1
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterAmount0Store evm I } evm
      [.letDecl "amount1Numerator" (some uint256)
        (checkedMul (.var "liquidity") (.storage reserve1Ref))]
      (.ok { contract := contract, locals := amm4BurnAfterNum1Store evm I } evm) := by
    simpa [amm4BurnAfterNum1Store] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  simpa [amm4BurnSourcePrefixAmount0] using execBlock_append hprefix htail

theorem amm4BurnSourceNum1Overflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : amm4BurnAmount0Numerator evm I < UInt256.size)
    (hover1 : UInt256.size ≤ amm4BurnAmount1Numerator evm I) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hprefix := amm4BurnSourceAmount0Ok evm I hwv hnonzero hfit0
  have heval := amm4BurnEvalAmount1Numerator_revert (evm := evm)
    (I := I) hover1
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterAmount0Store evm I } evm
      (burnTransition.body.drop 5) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def amm4BurnSourcePrefixNum1 : List Stmt :=
  amm4BurnSourcePrefixAmount0 ++
    [.letDecl "amount1Numerator" (some uint256)
      (checkedMul (.var "liquidity") (.storage reserve1Ref))]

def amm4BurnAmount1Value (evm : EVM.State) (I : ExecutionEnv) : Nat :=
  amm4BurnAmount1Numerator evm I /
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat

def amm4BurnAfterAmount1Store (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (amm4BurnAfterNum1Store evm I).insert "amount1"
    (.int (Int.ofNat (amm4BurnAmount1Value evm I)))

theorem amm4BurnEvalNum1Local {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4BurnAfterNum1Store evm I }
      evm (.var "amount1Numerator") =
        .ok (.int (Int.ofNat (amm4BurnAmount1Numerator evm I))) := by
  simp [amm4BurnAfterNum1Store, evalExpr?, EvalResult.ofOption]

theorem amm4BurnEvalSupplyAfterNum1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4BurnAfterNum1Store evm I }
      evm (.storage totalSupplyRef) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply amm4MintEvalSupply
  simp [amm4BurnAfterNum1Store, amm4BurnAfterAmount0Store,
    amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnSourceAmount1Ok (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : amm4BurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : amm4BurnAmount1Numerator evm I < UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixNum1 ++
        checkedDivInto "amount1" (.var "amount1Numerator")
          (.storage totalSupplyRef))
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I } evm) := by
  have hprefix := amm4BurnSourceNum1Ok evm I hwv hnonzero hfit0 hfit1
  have hpositive : 0 < (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨0⟩).toNat := by
    have hn : (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).toNat ≠ 0 := by
      intro hz
      exact hnonzero (uint256_toNat_eq_zero hz)
    omega
  have hguard := amm4EvalNatNeZero_true
    (amm4BurnEvalSupplyAfterNum1 (I := I)) hpositive
  have hdiv := amm4EvalNatDiv_ok
    (amm4BurnEvalNum1Local (I := I))
    (amm4BurnEvalSupplyAfterNum1 (I := I)) hpositive
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterNum1Store evm I }
      evm (checkedDivInto "amount1" (.var "amount1Numerator")
        (.storage totalSupplyRef))
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I } evm) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [amm4BurnAfterAmount1Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [amm4BurnSourcePrefixNum1, List.append_assoc] using
    execBlock_append hprefix htail

def amm4BurnSourcePrefixAmounts : List Stmt :=
  amm4BurnSourcePrefixNum1 ++
    checkedDivInto "amount1" (.var "amount1Numerator")
      (.storage totalSupplyRef)

theorem amm4BurnEvalLiquidityAfterAmount1 {evm evm2 : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount1Store evm I } evm2 (.var "liquidity") =
      .ok (.int (Int.ofNat (amm4BurnLiquidityWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4BurnAfterAmount1Store,
    amm4BurnAfterNum1Store, amm4BurnAfterAmount0Store,
    amm4BurnAfterNum0Store, amm4BurnStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem amm4BurnEvalSupplyAfterAmount1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount1Store evm I } evm (.storage totalSupplyRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply amm4MintEvalSupply
  simp [amm4BurnAfterAmount1Store, amm4BurnAfterNum1Store,
    amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnSourceSupplyUnderflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : amm4BurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : amm4BurnAmount1Numerator evm I < UInt256.size)
    (hunder : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat <
      (amm4BurnLiquidityWord I).toNat) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hprefix := amm4BurnSourceAmount1Ok evm I hwv hnonzero hfit0 hfit1
  have heval := amm4EvalCheckedSub_revert
    (amm4BurnEvalSupplyAfterAmount1 (I := I))
    (amm4BurnEvalLiquidityAfterAmount1 (I := I)) hunder
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm I } evm
      (burnTransition.body.drop 8) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixAmounts, amm4BurnSourcePrefixNum1,
      amm4BurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def amm4BurnSupplyWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
      (amm4BurnLiquidityWord I).toNat)

def amm4BurnAfterSupply (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (amm4BurnSupplyWord evm I)

theorem amm4BurnEvalSupplySubOk {evm : EVM.State} {I : ExecutionEnv}
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    evalExpr? config { contract := contract, locals :=
      amm4BurnAfterAmount1Store evm I } evm
      (checkedSub (.storage totalSupplyRef) (.var "liquidity")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
          (amm4BurnLiquidityWord I).toNat))) := by
  exact amm4EvalCheckedSub_ok (amm4BurnEvalSupplyAfterAmount1 (I := I))
    (amm4BurnEvalLiquidityAfterAmount1 (I := I)) hle
    (by exact (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨0⟩).val.isLt)

theorem amm4BurnAssignSupply {evm : EVM.State} {I : ExecutionEnv}
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    assignStorageRef? config { contract := contract, locals :=
      (amm4BurnAfterAmount1Store evm I) } evm .storage totalSupplyRef
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
          (amm4BurnLiquidityWord I).toNat))) =
      .ok ({ contract := contract, locals := amm4BurnAfterAmount1Store evm I },
        amm4BurnAfterSupply evm I) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (hbase := by simp [amm4BurnAfterAmount1Store, amm4BurnAfterNum1Store,
      amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store,
      amm4BurnStore, totalSupplyRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  have hword : (amm4BurnSupplyWord evm I).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat -
        (amm4BurnLiquidityWord I).toNat := by
    exact ulit_toNat' _ (by
      have hlt := (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).val.isLt
      change (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨0⟩).toNat < UInt256.size at hlt
      omega)
  simpa [amm4BurnAfterSupply, hword] using
    amm4StorageLocStore_uint256 evm ⟨0⟩ (amm4BurnSupplyWord evm I)

theorem amm4BurnSourceSupplyOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hfit0 : amm4BurnAmount0Numerator evm I < UInt256.size)
    (hfit1 : amm4BurnAmount1Numerator evm I < UInt256.size)
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat) :
    ExecBlock config { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixAmounts ++
        [.assign .storage totalSupplyRef
          (checkedSub (.storage totalSupplyRef) (.var "liquidity"))])
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I }
        (amm4BurnAfterSupply evm I)) := by
  have hprefix := amm4BurnSourceAmount1Ok evm I hwv hnonzero hfit0 hfit1
  have heval := amm4BurnEvalSupplySubOk (evm := evm) (I := I) hle
  have hassign := amm4BurnAssignSupply (evm := evm) (I := I) hle
  have htail : ExecBlock config
      { contract := contract, locals := amm4BurnAfterAmount1Store evm I } evm
      [.assign .storage totalSupplyRef
        (checkedSub (.storage totalSupplyRef) (.var "liquidity"))]
      (.ok { contract := contract, locals := amm4BurnAfterAmount1Store evm I }
        (amm4BurnAfterSupply evm I)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  simpa [amm4BurnSourcePrefixAmounts] using execBlock_append hprefix htail

theorem amm4BurnSourceAmount0NumeratorOverflow (evm : EVM.State)
    (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnonzero : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (amm4BurnLiquidityWord I).toNat *
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hprefix := amm4BurnSourceGuarded evm I hwv hnonzero
  have heval := amm4BurnEvalAmount0Numerator_revert (evm := evm)
    (I := I) hover
  have htail : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm (burnTransition.body.drop 2) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4BurnStore I }
      evm burnTransition.body .reverted := by
    simpa [burnTransition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm4
