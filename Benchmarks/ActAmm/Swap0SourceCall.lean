import Benchmarks.ActAmm.Swap0TransferTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0EvalTransferArgs {evm : EVM.State} {I : ExecutionEnv} :
    evalExprs? config
      { contract := contract, locals := ammSwap0Store I }
      evm [(.var "amount1Out"), (.var "to")] =
        .ok [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
          .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))] := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  simp [evalExprs?, evalExpr?, ammSwap0Store,
    EvalResult.bind, EvalResult.ofOption, bind, pure,
    Std.HashMap.getElem_insert]

theorem ammSwap0SourceTransferCallFailed
    {evm evm1 : EVM.State} (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (false, evm1, out) true) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hprefix := ammSwap0SourceRecipientOk evm I
    hwv hpos hliq h0 h1
  have hreceiver := ammSwap0EvalToken1 (evm := evm) (I := I)
  have hargs := ammSwap0EvalTransferArgs (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm (swap0Transition.body.drop 4) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenTransfer, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap0SourceTransferDepthRevert
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hdepth : evm.executionEnv.depth = 1024)
    (hto : (ammSwap0ToWord I).toNat < EVM.addressModulus) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  let tgt : EVM.Address :=
    EVM.address (AccountAddress.ofUInt256
      (UInt256.land (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val
  have hcall : typedCallViaEVM config evm tgt "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (false,
        { evm with substate := (evm.addAccessedAccount tgt).substate },
        ByteArray.empty) true := by
    apply callNotMade_depthLimit
      (calldata := (ammSwap0TransferCalldataMem I).readWithPadding 128 68)
    · exact ammSwap0TransferCalldataMem_encode I hto
    · exact hdepth
  exact ammSwap0SourceTransferCallFailed I ByteArray.empty
    hwv hpos hliq h0 h1 hcall

theorem ammSwap0SourceTransferDecodeRevert
    {evm evm1 : EVM.State} (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (true, evm1, out) true)
    (hdec : config.externalABI.decode? "transfer" out = none) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hprefix := ammSwap0SourceRecipientOk evm I
    hwv hpos hliq h0 h1
  have hreceiver := ammSwap0EvalToken1 (evm := evm) (I := I)
  have hargs := ammSwap0EvalTransferArgs (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm (swap0Transition.body.drop 4) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenTransfer, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap0AfterTransferStore (I : ExecutionEnv) (b : Bool) : Store :=
  (ammSwap0Store I).insert "transferOk" (.bool b)

def ammSwap0SourcePrefixTransfer : List Stmt :=
  ammSwap0SourcePrefixRecipient ++
    [tokenTransfer (.storage token1Ref) (.var "amount1Out")
      (.var "to") "transferOk"]

theorem ammSwap0SourceTransferCallOk
    {evm evm1 : EVM.State} (I : ExecutionEnv)
    (out : ByteArray) (b : Bool)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask))
    (hcall : typedCallViaEVM config evm
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm
          evm.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "transfer" 0
      [.int (Int.ofNat (ammSwap0AmountWord I).toNat),
        .address (AccountAddress.ofUInt256 (ammSwap0ToWord I))]
      (true, evm1, out) true)
    (hdec : config.externalABI.decode? "transfer" out =
      some [.bool b]) :
    ExecBlock config { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixTransfer
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        evm1) := by
  have hprefix := ammSwap0SourceRecipientOk evm I
    hwv hpos hliq h0 h1
  have hreceiver := ammSwap0EvalToken1 (evm := evm) (I := I)
  have hargs := ammSwap0EvalTransferArgs (evm := evm) (I := I)
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm [tokenTransfer (.storage token1Ref) (.var "amount1Out")
        (.var "to") "transferOk"]
      (.ok { contract := contract, locals := ammSwap0AfterTransferStore I b }
        evm1) := by
    simp only [tokenTransfer]
    simpa [ammSwap0AfterTransferStore, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
