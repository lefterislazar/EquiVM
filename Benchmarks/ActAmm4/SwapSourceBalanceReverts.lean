import Benchmarks.ActAmm4.SwapSourceBalances

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapSourceBalance0RevertAfterStmt
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer1
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 } evm2))
    (hstmt : ExecStmt config
      { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 }
      evm2 (tokenBalance (.storage token0Ref) "balance0")
      .reverted) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 }
      evm2 (swapTransition.body.drop 6) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert hstmt
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixTransfer1,
      amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient, swapTransition,
      nonpayable, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceBalance1RevertAfterStmt
    {evm evm3 : EVM.State} (I : ExecutionEnv) (b0 b1 : Bool)
    (out0 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance0
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 } evm3))
    (hstmt : ExecStmt config
      { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 }
      evm3 (tokenBalance (.storage token1Ref) "balance1")
      .reverted) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 }
      evm3 (swapTransition.body.drop 7) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert hstmt
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixBalance0,
      amm4SwapSourcePrefixTransfer1,
      amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient, swapTransition,
      nonpayable, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceBalance0CallFailed
    {evm evm2 evm3 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer1
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 } evm2))
    (hcall : typedCallViaEVM config evm2
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm2
          evm2.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm2.executionEnv.codeOwner]
      (false, evm3, out) false) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken0 (evm := evm2)
    (locals := amm4SwapAfterTransfer1Store I b0 b1)
    (by simp [amm4SwapAfterTransfer1Store,
      amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm2)
    (locals := amm4SwapAfterTransfer1Store I b0 b1)
  exact amm4SwapSourceBalance0RevertAfterStmt I b0 b1 hprefix
    (by
      simp only [tokenBalance]
      exact ExecStmt.externalCallFailure
        hreceiver (by simp [evalExpr?, pure]) hargs hcall)

theorem amm4SwapSourceBalance0DecodeRevert
    {evm evm2 evm3 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer1
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer1Store I b0 b1 } evm2))
    (hcall : typedCallViaEVM config evm2
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm2
          evm2.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm2.executionEnv.codeOwner]
      (true, evm3, out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken0 (evm := evm2)
    (locals := amm4SwapAfterTransfer1Store I b0 b1)
    (by simp [amm4SwapAfterTransfer1Store,
      amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm2)
    (locals := amm4SwapAfterTransfer1Store I b0 b1)
  exact amm4SwapSourceBalance0RevertAfterStmt I b0 b1 hprefix
    (by
      simp only [tokenBalance]
      exact ExecStmt.externalCallReturnDecodeRevert
        hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)

theorem amm4SwapSourceBalance1CallFailed
    {evm evm3 evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance0
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 } evm3))
    (hcall : typedCallViaEVM config evm3
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm3
          evm3.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm3.executionEnv.codeOwner]
      (false, evm4, out1) false) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken1 (evm := evm3)
    (locals := amm4SwapAfterBalance0Store I b0 b1 out0)
    (by simp [amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store,
      amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm3)
    (locals := amm4SwapAfterBalance0Store I b0 b1 out0)
  exact amm4SwapSourceBalance1RevertAfterStmt I b0 b1 out0 hprefix
    (by
      simp only [tokenBalance]
      exact ExecStmt.externalCallFailure
        hreceiver (by simp [evalExpr?, pure]) hargs hcall)

theorem amm4SwapSourceBalance1DecodeRevert
    {evm evm3 evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance0
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance0Store I b0 b1 out0 } evm3))
    (hcall : typedCallViaEVM config evm3
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm3
          evm3.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm3.executionEnv.codeOwner]
      (true, evm4, out1) false)
    (hdec : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken1 (evm := evm3)
    (locals := amm4SwapAfterBalance0Store I b0 b1 out0)
    (by simp [amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store,
      amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4MintEvalBalanceArgs (evm := evm3)
    (locals := amm4SwapAfterBalance0Store I b0 b1 out0)
  exact amm4SwapSourceBalance1RevertAfterStmt I b0 b1 out0 hprefix
    (by
      simp only [tokenBalance]
      exact ExecStmt.externalCallReturnDecodeRevert
        hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)

end Benchmarks.ActAmm4
