import Benchmarks.ActAmm4.SwapSourceArithmeticReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapSourceNewProductOverflow
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        (amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1) }
        evm4))
    (hover : UInt256.size ≤ amm4SwapNewProductNat out0 out1) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 (checkedMul (.var "balance0") (.var "balance1")) =
        .revert :=
    amm4EvalCheckedMul_revert
      amm4SwapEvalBalance0AfterInputs
      amm4SwapEvalBalance1AfterInputs hover
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 (swapTransition.body.drop 13) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixInputGuard,
      amm4SwapSourcePrefixAmount1In,
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

theorem amm4SwapSourceOldProductOverflow
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixNewProduct
      (.ok { contract := contract, locals :=
        (amm4SwapAfterNewProductStore evm4 I b0 b1
          out0 out1 a0 a1) } evm4))
    (hover : UInt256.size ≤ amm4SwapOldProductNat evm4) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1
          out0 out1 a0 a1 }
      evm4 (checkedMul (.storage reserve0Ref)
        (.storage reserve1Ref)) = .revert :=
    amm4EvalCheckedMul_revert
      amm4SwapEvalReserve0AfterNewProduct
      amm4SwapEvalReserve1AfterNewProduct hover
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1
          out0 out1 a0 a1 }
      evm4 (swapTransition.body.drop 14) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixNewProduct,
      amm4SwapSourcePrefixInputGuard,
      amm4SwapSourcePrefixAmount1In,
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

theorem amm4SwapSourceKGuardRevert
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixOldProduct
      (.ok { contract := contract, locals :=
        (amm4SwapAfterOldProductStore evm4 I b0 b1
          out0 out1 a0 a1) } evm4))
    (hlt : amm4SwapNewProductNat out0 out1 <
      amm4SwapOldProductNat evm4) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1
          out0 out1 a0 a1 }
      evm4 (swapTransition.body.drop 15) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (amm4SwapEvalKGuard_false hlt))
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixOldProduct,
      amm4SwapSourcePrefixNewProduct,
      amm4SwapSourcePrefixInputGuard,
      amm4SwapSourcePrefixAmount1In,
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
