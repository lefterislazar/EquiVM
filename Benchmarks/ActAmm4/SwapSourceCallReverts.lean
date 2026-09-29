import Benchmarks.ActAmm4.SwapSourceCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapSourceTransfer0CallFailed
    {evm evm1 : EVM.State} (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (false, evm1, out) true) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hprefix := amm4SwapSourceRecipientOk evm I
    hwv hpos hliq0 hliq1 h0 h1
  have hreceiver := amm4SwapEvalToken0 (evm := evm) (I := I)
  have hargs := amm4SwapEvalTransfer0Args (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm (swapTransition.body.drop 4) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixRecipient, swapTransition,
      nonpayable, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceTransfer0DecodeRevert
    {evm evm1 : EVM.State} (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat)
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount0Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evm1, out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hprefix := amm4SwapSourceRecipientOk evm I
    hwv hpos hliq0 hliq1 h0 h1
  have hreceiver := amm4SwapEvalToken0 (evm := evm) (I := I)
  have hargs := amm4SwapEvalTransfer0Args (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm (swapTransition.body.drop 4) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixRecipient, swapTransition,
      nonpayable, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceTransfer1CallFailed
    {evm evm1 evm2 : EVM.State} (I : ExecutionEnv)
    (out : ByteArray) (b0 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer0
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer0Store I b0 } evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (false, evm2, out) true) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken1 (evm := evm1)
    (locals := amm4SwapAfterTransfer0Store I b0)
    (by simp [amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4SwapEvalTransfer1Args
    (evm := evm1) (I := I) (b0 := b0)
  have htail : ExecBlock config
      { contract := contract,
        locals := amm4SwapAfterTransfer0Store I b0 }
      evm1 (swapTransition.body.drop 5) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient, swapTransition,
      nonpayable, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4SwapSourceTransfer1DecodeRevert
    {evm evm1 evm2 : EVM.State} (I : ExecutionEnv)
    (out : ByteArray) (b0 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixTransfer0
      (.ok { contract := contract, locals :=
        amm4SwapAfterTransfer0Store I b0 } evm1))
    (hcall : typedCallViaEVM config evm1
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm1
          evm1.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (amm4SwapAmount1Word I).toNat),
        .address (AccountAddress.ofUInt256 (amm4SwapToWord I))]
      (true, evm2, out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken1 (evm := evm1)
    (locals := amm4SwapAfterTransfer0Store I b0)
    (by simp [amm4SwapAfterTransfer0Store, amm4SwapStore])
  have hargs := amm4SwapEvalTransfer1Args
    (evm := evm1) (I := I) (b0 := b0)
  have htail : ExecBlock config
      { contract := contract,
        locals := amm4SwapAfterTransfer0Store I b0 }
      evm1 (swapTransition.body.drop 5) .reverted := by
    simp only [swapTransition, nonpayable, tokenTransfer,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.externalCallReturnDecodeRevert
        hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body .reverted := by
    simpa [amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient, swapTransition,
      nonpayable, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm4
