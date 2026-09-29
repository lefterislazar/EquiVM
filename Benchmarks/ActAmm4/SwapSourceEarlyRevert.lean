import Benchmarks.ActAmm4.SwapSourceGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

private def outputGuard : Expr :=
  .binary .or
    (.binary .gt (.var "amount0Out") (.intLit 0))
    (.binary .gt (.var "amount1Out") (.intLit 0))

private def liquidityGuard : Expr :=
  .binary .and
    (.binary .lt (.var "amount0Out") (.storage reserve0Ref))
    (.binary .lt (.var "amount1Out") (.storage reserve1Ref))

private def recipientGuard : Expr :=
  .binary .and
    (.binary .ne (.var "to") (.storage token0Ref))
    (.binary .ne (.var "to") (.storage token1Ref))

theorem amm4SwapSourceGuard0Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfalse : evalExpr? config
      { contract := contract, locals := amm4SwapStore I }
      evm outputGuard = .ok (.bool false)) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simp only [swapTransition, nonpayable, outputGuard,
      List.cons_append, List.nil_append]
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
      (ExecBlock.consRevert (ExecStmt.requireFalse hfalse))
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceGuard1Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htrue : evalExpr? config
      { contract := contract, locals := amm4SwapStore I }
      evm outputGuard = .ok (.bool true))
    (hfalse : evalExpr? config
      { contract := contract, locals := amm4SwapStore I }
      evm liquidityGuard = .ok (.bool false)) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simp only [swapTransition, nonpayable, outputGuard, liquidityGuard,
      List.cons_append, List.nil_append]
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue htrue) <|
      ExecBlock.consRevert (ExecStmt.requireFalse hfalse)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceGuard2Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (htrue0 : evalExpr? config
      { contract := contract, locals := amm4SwapStore I }
      evm outputGuard = .ok (.bool true))
    (htrue1 : evalExpr? config
      { contract := contract, locals := amm4SwapStore I }
      evm liquidityGuard = .ok (.bool true))
    (hfalse : evalExpr? config
      { contract := contract, locals := amm4SwapStore I }
      evm recipientGuard = .ok (.bool false)) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simp only [swapTransition, nonpayable, outputGuard,
      liquidityGuard, recipientGuard,
      List.cons_append, List.nil_append]
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.requireTrue htrue0) <|
      ExecBlock.consNormal (ExecStmt.requireTrue htrue1) <|
      ExecBlock.consRevert (ExecStmt.requireFalse hfalse)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceZeroOutput
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero0 : (amm4SwapAmount0Word I).toNat = 0)
    (hzero1 : (amm4SwapAmount1Word I).toNat = 0) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  exact amm4SwapSourceGuard0Revert evm I hwv
    (by simpa only [outputGuard] using
      (amm4SwapEvalOutputGuard_false (evm := evm) hzero0 hzero1))

theorem amm4SwapSourceLiquidity0Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      (amm4SwapAmount0Word I).toNat) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  exact amm4SwapSourceGuard1Revert evm I hwv
    (by simpa only [outputGuard] using
      (amm4SwapEvalOutputGuard_true (evm := evm) hpos))
    (by simpa only [liquidityGuard] using
      (amm4SwapEvalLiquidityGuard_false0 (evm := evm) hliq0))

theorem amm4SwapSourceLiquidity1Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      (amm4SwapAmount1Word I).toNat) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  exact amm4SwapSourceGuard1Revert evm I hwv
    (by simpa only [outputGuard] using
      (amm4SwapEvalOutputGuard_true (evm := evm) hpos))
    (by simpa only [liquidityGuard] using
      (amm4SwapEvalLiquidityGuard_false1 (evm := evm) hliq0 hliq1))

theorem amm4SwapSourceRecipient0Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (heq : AccountAddress.ofNat (amm4SwapToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  exact amm4SwapSourceGuard2Revert evm I hwv
    (by simpa only [outputGuard] using
      (amm4SwapEvalOutputGuard_true (evm := evm) hpos))
    (by simpa only [liquidityGuard] using
      (amm4SwapEvalLiquidityGuard_true (evm := evm) hliq0 hliq1))
    (by simpa only [recipientGuard] using
      (amm4SwapEvalRecipientGuard_false0 (evm := evm) heq))

theorem amm4SwapSourceRecipient1Revert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (hne0 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (heq1 : AccountAddress.ofNat (amm4SwapToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  exact amm4SwapSourceGuard2Revert evm I hwv
    (by simpa only [outputGuard] using
      (amm4SwapEvalOutputGuard_true (evm := evm) hpos))
    (by simpa only [liquidityGuard] using
      (amm4SwapEvalLiquidityGuard_true (evm := evm) hliq0 hliq1))
    (by simpa only [recipientGuard] using
      (amm4SwapEvalRecipientGuard_false1 (evm := evm) hne0 heq1))

end Benchmarks.ActAmm4
