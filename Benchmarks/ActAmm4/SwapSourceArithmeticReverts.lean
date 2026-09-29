import Benchmarks.ActAmm4.SwapSourceSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapSourceReserve0Underflow
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance1
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 } evm4))
    (hunder : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨5⟩).toNat <
      (amm4SwapAmount0Word I).toNat) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
      evm4 (checkedSub (.storage reserve0Ref)
        (.var "amount0Out")) = .revert :=
    amm4EvalCheckedSub_revert
      amm4SwapEvalReserve0AfterBalances
      amm4SwapEvalAmount0AfterBalances hunder
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
      evm4 (swapTransition.body.drop 8) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixBalance1,
      amm4SwapSourcePrefixBalance0,
      amm4SwapSourcePrefixTransfer1,
      amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient,
      swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceReserve1Underflow
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (amount0In : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount0In
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1
          out0 out1 amount0In) } evm4))
    (hunder : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨6⟩).toNat <
      (amm4SwapAmount1Word I).toNat) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1
          out0 out1 amount0In) }
      evm4 (checkedSub (.storage reserve1Ref)
        (.var "amount1Out")) = .revert :=
    amm4EvalCheckedSub_revert
      amm4SwapEvalReserve1AfterAmount0In
      amm4SwapEvalAmount1AfterAmount0In hunder
  have htail : ExecBlock config
      { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1
          out0 out1 amount0In) }
      evm4 (swapTransition.body.drop 10) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixAmount0In,
      amm4SwapSourcePrefixReserve0,
      amm4SwapSourcePrefixBalance1,
      amm4SwapSourcePrefixBalance0,
      amm4SwapSourcePrefixTransfer1,
      amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient,
      swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceInputGuardRevert
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (amount0In amount1In : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount1In
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount1InStore evm4 I b0 b1
          out0 out1 amount0In amount1In) } evm4))
    (hzero0 : amount0In = 0) (hzero1 : amount1In = 0) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hprefix' : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount1In
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 0 0 }
        evm4) := by
    simpa [hzero0, hzero1] using hprefix
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 0 0 }
      evm4 (swapTransition.body.drop 12) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse amm4SwapEvalInputGuard_false)
  have hblock := execBlock_append hprefix' htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixAmount1In,
      amm4SwapSourcePrefixReserve1,
      amm4SwapSourcePrefixAmount0In,
      amm4SwapSourcePrefixReserve0,
      amm4SwapSourcePrefixBalance1,
      amm4SwapSourcePrefixBalance0,
      amm4SwapSourcePrefixTransfer1,
      amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient,
      swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm4
