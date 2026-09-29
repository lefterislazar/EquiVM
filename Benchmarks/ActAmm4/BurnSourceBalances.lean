import Benchmarks.ActAmm4.BurnSourceCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

theorem amm4StorageStore_preserves_call_context (evm : EVM.State)
    (addr : AccountAddress) (slot val : UInt256) :
    let out := Solm.EVM.storageStore evm addr slot val
    out.σ₀ = evm.σ₀ ∧
    out.genesisBlockHeader = evm.genesisBlockHeader ∧
    out.blocks = evm.blocks ∧ out.substate = evm.substate := by
  dsimp
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;>
    simp [Option.option, State.setAccount]

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4BurnSourcePrefixTransfers : List Stmt :=
  amm4BurnSourcePrefixSender ++
    [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
      "transfer0Ok",
     tokenTransfer (.storage token1Ref) (.var "amount1") (.var "to")
      "transfer1Ok"]

theorem amm4BurnAfterTransfer1Store_token0_none (evm : EVM.State)
    (I : ExecutionEnv) (b0 b1 : Bool) :
    (amm4BurnAfterTransfer1Store evm I b0 b1).get? "token0" = none := by
  simp [amm4BurnAfterTransfer1Store, amm4BurnAfterTransfer0Store,
    amm4BurnAfterAmount1Store, amm4BurnAfterNum1Store,
    amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnSourceBalance0CallFailed {evm evm6 evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      amm4BurnSourcePrefixTransfers
      (.ok { contract := contract, locals :=
        amm4BurnAfterTransfer1Store evm I b0 b1 } evm6))
    (hcall : typedCallViaEVM config evm6
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm6
          evm6.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm6.executionEnv.codeOwner]
      (false, evm7, out) false) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken0 (evm := evm6)
    (locals := amm4BurnAfterTransfer1Store evm I b0 b1)
    (amm4BurnAfterTransfer1Store_token0_none evm I b0 b1)
  have hargs := amm4MintEvalBalanceArgs (evm := evm6)
    (locals := amm4BurnAfterTransfer1Store evm I b0 b1)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterTransfer1Store evm I b0 b1 }
      evm6 (burnTransition.body.drop 12) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixTransfers, amm4BurnSourcePrefixSender,
      amm4BurnSourcePrefixSupply, amm4BurnSourcePrefixAmounts,
      amm4BurnSourcePrefixNum1, amm4BurnSourcePrefixAmount0,
      burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4BurnSourceBalance0DecodeRevert {evm evm6 evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      amm4BurnSourcePrefixTransfers
      (.ok { contract := contract, locals :=
        amm4BurnAfterTransfer1Store evm I b0 b1 } evm6))
    (hcall : typedCallViaEVM config evm6
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm6
          evm6.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm6.executionEnv.codeOwner]
      (true, evm7, out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken0 (evm := evm6)
    (locals := amm4BurnAfterTransfer1Store evm I b0 b1)
    (amm4BurnAfterTransfer1Store_token0_none evm I b0 b1)
  have hargs := amm4MintEvalBalanceArgs (evm := evm6)
    (locals := amm4BurnAfterTransfer1Store evm I b0 b1)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterTransfer1Store evm I b0 b1 }
      evm6 (burnTransition.body.drop 12) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixTransfers, amm4BurnSourcePrefixSender,
      amm4BurnSourcePrefixSupply, amm4BurnSourcePrefixAmounts,
      amm4BurnSourcePrefixNum1, amm4BurnSourcePrefixAmount0,
      burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def amm4BurnAfterBalance0Store (evm : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out : ByteArray) : Store :=
  (amm4BurnAfterTransfer1Store evm I b0 b1).insert "newBalance0"
    (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))))

theorem amm4BurnSourceBalance0CallOk {evm evm6 evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      amm4BurnSourcePrefixTransfers
      (.ok { contract := contract, locals :=
        amm4BurnAfterTransfer1Store evm I b0 b1 } evm6))
    (hcall : typedCallViaEVM config evm6
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm6
          evm6.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm6.executionEnv.codeOwner]
      (true, evm7, out) false)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixTransfers ++
        [tokenBalance (.storage token0Ref) "newBalance0"])
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out } evm7) := by
  have hreceiver := amm4MintEvalToken0 (evm := evm6)
    (locals := amm4BurnAfterTransfer1Store evm I b0 b1)
    (amm4BurnAfterTransfer1Store_token0_none evm I b0 b1)
  have hargs := amm4MintEvalBalanceArgs (evm := evm6)
    (locals := amm4BurnAfterTransfer1Store evm I b0 b1)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : out.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterTransfer1Store evm I b0 b1 }
      evm6 [tokenBalance (.storage token0Ref) "newBalance0"]
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out } evm7) := by
    simp only [tokenBalance]
    simpa [amm4BurnAfterBalance0Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

def amm4BurnReserve0Word (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

def amm4BurnAfterReserve0 (evm : EVM.State) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (amm4BurnReserve0Word out)

theorem amm4BurnEvalNewBalance0 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out : ByteArray) :
    evalExpr? config
      { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out }
      evm' (.var "newBalance0") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32)))) := by
  simp [evalExpr?, amm4BurnAfterBalance0Store, EvalResult.ofOption]

theorem amm4BurnAssignReserve0 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out : ByteArray)
    (hlo : 32 ≤ out.size) :
    assignStorageRef? config
      { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out }
      evm' .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out },
        amm4BurnAfterReserve0 evm' out) := by
  have hword : (amm4BurnReserve0Word out).toNat =
      fromByteArrayBigEndian (out.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm' (wordLoc ⟨5⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      some (amm4BurnAfterReserve0 evm' out) := by
    simpa [amm4BurnAfterReserve0, hword] using
      amm4StorageLocStore_uint256 evm' ⟨5⟩ (amm4BurnReserve0Word out)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      amm4BurnAfterBalance0Store evm I b0 b1 out })
    (evm := evm') (evm' := amm4BurnAfterReserve0 evm' out)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (by simp [amm4BurnAfterBalance0Store,
      amm4BurnAfterTransfer1Store, amm4BurnAfterTransfer0Store,
      amm4BurnAfterAmount1Store, amm4BurnAfterNum1Store,
      amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store,
      amm4BurnStore, reserve0Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem amm4BurnSourceReserve0Ok {evm evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixTransfers ++
        [tokenBalance (.storage token0Ref) "newBalance0"])
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out } evm7))
    (hlo : 32 ≤ out.size) :
    ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixTransfers ++
        [tokenBalance (.storage token0Ref) "newBalance0",
         .assign .storage reserve0Ref (.var "newBalance0")])
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out }
        (amm4BurnAfterReserve0 evm7 out)) := by
  have heval := amm4BurnEvalNewBalance0
    (evm := evm) (evm' := evm7) I b0 b1 out
  have hassign := amm4BurnAssignReserve0
    (evm := evm) (evm' := evm7) I b0 b1 out hlo
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out }
      evm7 [.assign .storage reserve0Ref (.var "newBalance0")]
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out }
        (amm4BurnAfterReserve0 evm7 out)) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign heval hassign) ExecBlock.nil
  simpa [List.append_assoc] using execBlock_append hprefix htail

def amm4BurnSourcePrefixReserve0 : List Stmt :=
  amm4BurnSourcePrefixTransfers ++
    [tokenBalance (.storage token0Ref) "newBalance0",
     .assign .storage reserve0Ref (.var "newBalance0")]

theorem amm4BurnAfterBalance0Store_token1_none (evm : EVM.State)
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 : ByteArray) :
    (amm4BurnAfterBalance0Store evm I b0 b1 out0).get? "token1" = none := by
  simp [amm4BurnAfterBalance0Store, amm4BurnAfterTransfer1Store,
    amm4BurnAfterTransfer0Store, amm4BurnAfterAmount1Store,
    amm4BurnAfterNum1Store, amm4BurnAfterAmount0Store,
    amm4BurnAfterNum0Store, amm4BurnStore]

theorem amm4BurnSourceBalance1CallFailed {evm evm8 evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      amm4BurnSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out0 } evm8))
    (hcall : typedCallViaEVM config evm8
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm8
          evm8.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm8.executionEnv.codeOwner]
      (false, evm9, out1) false) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken1 (evm := evm8)
    (locals := amm4BurnAfterBalance0Store evm I b0 b1 out0)
    (amm4BurnAfterBalance0Store_token1_none evm I b0 b1 out0)
  have hargs := amm4MintEvalBalanceArgs (evm := evm8)
    (locals := amm4BurnAfterBalance0Store evm I b0 b1 out0)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out0 }
      evm8 (burnTransition.body.drop 14) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixReserve0, amm4BurnSourcePrefixTransfers,
      amm4BurnSourcePrefixSender, amm4BurnSourcePrefixSupply,
      amm4BurnSourcePrefixAmounts, amm4BurnSourcePrefixNum1,
      amm4BurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, tokenTransfer, tokenBalance,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem amm4BurnSourceBalance1DecodeRevert {evm evm8 evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      amm4BurnSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out0 } evm8))
    (hcall : typedCallViaEVM config evm8
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm8
          evm8.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm8.executionEnv.codeOwner]
      (true, evm9, out1) false)
    (hdec : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := amm4MintEvalToken1 (evm := evm8)
    (locals := amm4BurnAfterBalance0Store evm I b0 b1 out0)
    (amm4BurnAfterBalance0Store_token1_none evm I b0 b1 out0)
  have hargs := amm4MintEvalBalanceArgs (evm := evm8)
    (locals := amm4BurnAfterBalance0Store evm I b0 b1 out0)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out0 }
      evm8 (burnTransition.body.drop 14) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      burnTransition.body .reverted := by
    simpa [amm4BurnSourcePrefixReserve0, amm4BurnSourcePrefixTransfers,
      amm4BurnSourcePrefixSender, amm4BurnSourcePrefixSupply,
      amm4BurnSourcePrefixAmounts, amm4BurnSourcePrefixNum1,
      amm4BurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, tokenTransfer, tokenBalance,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def amm4BurnAfterBalance1Store (evm : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) : Store :=
  (amm4BurnAfterBalance0Store evm I b0 b1 out0).insert "newBalance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32))))

theorem amm4BurnSourceBalance1CallOk {evm evm8 evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      amm4BurnSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out0 } evm8))
    (hcall : typedCallViaEVM config evm8
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm8
          evm8.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm8.executionEnv.codeOwner]
      (true, evm9, out1) false)
    (hlo : 32 ≤ out1.size) (hbound : out1.size < 2 ^ 138) :
    ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixReserve0 ++
        [tokenBalance (.storage token1Ref) "newBalance1"])
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 } evm9) := by
  have hreceiver := amm4MintEvalToken1 (evm := evm8)
    (locals := amm4BurnAfterBalance0Store evm I b0 b1 out0)
    (amm4BurnAfterBalance0Store_token1_none evm I b0 b1 out0)
  have hargs := amm4MintEvalBalanceArgs (evm := evm8)
    (locals := amm4BurnAfterBalance0Store evm I b0 b1 out0)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : out1.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterBalance0Store evm I b0 b1 out0 }
      evm8 [tokenBalance (.storage token1Ref) "newBalance1"]
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 } evm9) := by
    simp only [tokenBalance]
    simpa [amm4BurnAfterBalance1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

def amm4BurnReserve1Word (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

def amm4BurnAfterReserve1 (evm : EVM.State) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (amm4BurnReserve1Word out)

theorem amm4BurnEvalNewBalance1 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray) :
    evalExpr? config
      { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 }
      evm' (.var "newBalance1") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out1.extract 0 32)))) := by
  simp [evalExpr?, amm4BurnAfterBalance1Store, EvalResult.ofOption]

theorem amm4BurnAssignReserve1 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hlo : 32 ≤ out1.size) :
    assignStorageRef? config
      { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 }
      evm' .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 },
        amm4BurnAfterReserve1 evm' out1) := by
  have hword : (amm4BurnReserve1Word out1).toNat =
      fromByteArrayBigEndian (out1.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm' (wordLoc ⟨6⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))) =
      some (amm4BurnAfterReserve1 evm' out1) := by
    simpa [amm4BurnAfterReserve1, hword] using
      amm4StorageLocStore_uint256 evm' ⟨6⟩ (amm4BurnReserve1Word out1)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 })
    (evm := evm') (evm' := amm4BurnAfterReserve1 evm' out1)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))
    (by simp [amm4BurnAfterBalance1Store, amm4BurnAfterBalance0Store,
      amm4BurnAfterTransfer1Store, amm4BurnAfterTransfer0Store,
      amm4BurnAfterAmount1Store, amm4BurnAfterNum1Store,
      amm4BurnAfterAmount0Store, amm4BurnAfterNum0Store,
      amm4BurnStore, reserve1Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem amm4BurnSourceReserve1Ok {evm evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      (amm4BurnSourcePrefixReserve0 ++
        [tokenBalance (.storage token1Ref) "newBalance1"])
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 } evm9))
    (hlo : 32 ≤ out1.size) :
    ExecTransitionBody config contract evm (amm4BurnStore I)
      burnTransition.body
      (.returned { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 }
        (amm4BurnAfterReserve1 evm9 out1) none) := by
  have heval := amm4BurnEvalNewBalance1
    (evm := evm) (evm' := evm9) I b0 b1 out0 out1
  have hassign := amm4BurnAssignReserve1
    (evm := evm) (evm' := evm9) I b0 b1 out0 out1 hlo
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 }
      evm9 [.assign .storage reserve1Ref (.var "newBalance1")]
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 }
        (amm4BurnAfterReserve1 evm9 out1)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := amm4BurnStore I } evm
      burnTransition.body
      (.ok { contract := contract, locals :=
        amm4BurnAfterBalance1Store evm I b0 b1 out0 out1 }
        (amm4BurnAfterReserve1 evm9 out1)) := by
    simpa [amm4BurnSourcePrefixReserve0, amm4BurnSourcePrefixTransfers,
      amm4BurnSourcePrefixSender, amm4BurnSourcePrefixSupply,
      amm4BurnSourcePrefixAmounts, amm4BurnSourcePrefixNum1,
      amm4BurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, tokenTransfer, tokenBalance,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hbody

end Benchmarks.ActAmm4
