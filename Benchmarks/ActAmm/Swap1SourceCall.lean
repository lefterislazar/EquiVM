import Benchmarks.ActAmm.Swap1TransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1EvalTransferArgs {evm : EVM.State} {I : ExecutionEnv} :
    evalExprs? config
      { contract := contract, locals := ammSwap1Store I }
      evm [(.var "amount0Out"), (.var "to")] =
        .ok [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
          .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))] := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExprs?, evalExpr?, ammSwap1Store,
    EvalResult.bind, EvalResult.ofOption, bind, pure,
    Std.HashMap.getElem_insert]

theorem ammSwap1SourceTransferCallFailed
    {evm evm1 : EVM.State} (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (false, evm1, out) true) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hprefix := ammSwap1SourceRecipientOk evm I
    hwv hpos hliq h0 h1
  have hreceiver := ammSwap1EvalToken0 (evm := evm) (I := I)
  have hargs := ammSwap1EvalTransferArgs (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm (swap1Transition.body.drop 4) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenTransfer, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
      swap1Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap1SourceTransferDepthRevert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hdepth : evm.executionEnv.depth = 1024)
    (hto : (ammSwap1ToWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  let tgt : EVM.Address :=
    EVM.address (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val
  have hcall : typedCallViaEVM config evm tgt "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (false,
        { evm with substate := (evm.addAccessedAccount tgt).substate },
        ByteArray.empty) true := by
    apply callNotMade_depthLimit
      (calldata := (ammSwap1TransferCalldataMem I).readWithPadding 128 68)
    · exact ammSwap1TransferCalldataMem_encode I hto
    · exact hdepth
  exact ammSwap1SourceTransferCallFailed I ByteArray.empty
    hwv hpos hliq h0 h1 hcall

theorem ammSwap1SourceTransferDecodeRevert
    {evm evm1 : EVM.State} (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (true, evm1, out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hprefix := ammSwap1SourceRecipientOk evm I
    hwv hpos hliq h0 h1
  have hreceiver := ammSwap1EvalToken0 (evm := evm) (I := I)
  have hargs := ammSwap1EvalTransferArgs (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm (swap1Transition.body.drop 4) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenTransfer, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
      swap1Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap1AfterTransferStore (I : ExecutionEnv) (b : Bool) : Store :=
  (ammSwap1Store I).insert "transferOk" (.bool b)

def ammSwap1SourcePrefixTransfer : List Stmt :=
  ammSwap1SourcePrefixRecipient ++
    [tokenTransfer (.storage token0Ref) (.var "amount0Out")
      (.var "to") "transferOk"]

theorem ammSwap1SourceTransferCallOk
    {evm evm1 : EVM.State} (I : ExecutionEnv)
    (out : ByteArray) (b : Bool)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap1AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap1ToWord I))]
      (true, evm1, out) true)
    (hdec : config.externalABI.decode? "transfer" out =
      some [.bool b]) :
    ExecBlock config { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap1AfterTransferStore I b }
        evm1) := by
  have hprefix := ammSwap1SourceRecipientOk evm I
    hwv hpos hliq h0 h1
  have hreceiver := ammSwap1EvalToken0 (evm := evm) (I := I)
  have hargs := ammSwap1EvalTransferArgs (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm [tokenTransfer (.storage token0Ref) (.var "amount0Out")
        (.var "to") "transferOk"]
      (.ok { contract := contract, locals := ammSwap1AfterTransferStore I b }
        evm1) := by
    simp only [tokenTransfer]
    simpa [ammSwap1AfterTransferStore, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
