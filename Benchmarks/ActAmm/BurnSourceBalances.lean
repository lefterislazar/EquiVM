import Benchmarks.ActAmm.BurnSourceCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

theorem ammStorageStore_preserves_call_context (evm : EVM.State)
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

def ammBurnSourcePrefixTransfers : List Stmt :=
  ammBurnSourcePrefixSender ++
    [tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to")
      "transfer0Ok",
     tokenTransfer (.storage token1Ref) (.var "amount1") (.var "to")
      "transfer1Ok"]

theorem ammBurnAfterTransfer1Store_token0_none (evm : EVM.State)
    (I : ExecutionEnv) (b0 b1 : Bool) :
    (ammBurnAfterTransfer1Store evm I b0 b1).get? "token0" = none := by
  simp [ammBurnAfterTransfer1Store, ammBurnAfterTransfer0Store,
    ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
    ammBurnAfterAmount0Store, ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnSourceBalance0CallFailed {evm evm6 evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixTransfers
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 } evm6))
    (hcall : typedCallViaEVM config evm6
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm6
          evm6.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm6.executionEnv.codeOwner]
      (false, evm7, out) false) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken0 (evm := evm6)
    (locals := ammBurnAfterTransfer1Store evm I b0 b1)
    (ammBurnAfterTransfer1Store_token0_none evm I b0 b1)
  have hargs := ammMintEvalBalanceArgs (evm := evm6)
    (locals := ammBurnAfterTransfer1Store evm I b0 b1)
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 }
      evm6 (burnTransition.body.drop 12) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixTransfers, ammBurnSourcePrefixSender,
      ammBurnSourcePrefixSupply, ammBurnSourcePrefixAmounts,
      ammBurnSourcePrefixNum1, ammBurnSourcePrefixAmount0,
      burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammBurnSourceBalance0DecodeRevert {evm evm6 evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixTransfers
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 } evm6))
    (hcall : typedCallViaEVM config evm6
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm6
          evm6.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm6.executionEnv.codeOwner]
      (true, evm7, out) false)
    (hdec : config.externalABI.decode? "balanceOf" out = none) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken0 (evm := evm6)
    (locals := ammBurnAfterTransfer1Store evm I b0 b1)
    (ammBurnAfterTransfer1Store_token0_none evm I b0 b1)
  have hargs := ammMintEvalBalanceArgs (evm := evm6)
    (locals := ammBurnAfterTransfer1Store evm I b0 b1)
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 }
      evm6 (burnTransition.body.drop 12) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixTransfers, ammBurnSourcePrefixSender,
      ammBurnSourcePrefixSupply, ammBurnSourcePrefixAmounts,
      ammBurnSourcePrefixNum1, ammBurnSourcePrefixAmount0,
      burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammBurnAfterBalance0Store (evm : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out : ByteArray) : Store :=
  (ammBurnAfterTransfer1Store evm I b0 b1).insert "newBalance0"
    (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))))

theorem ammBurnSourceBalance0CallOk {evm evm6 evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixTransfers
      (.ok { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 } evm6))
    (hcall : typedCallViaEVM config evm6
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm6
          evm6.executionEnv.codeOwner ⟨3⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm6.executionEnv.codeOwner]
      (true, evm7, out) false)
    (hlo : 32 ≤ out.size) (hbound : out.size < 2 ^ 138) :
    ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixTransfers ++
        [tokenBalance (.storage token0Ref) "newBalance0"])
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out } evm7) := by
  have hreceiver := ammMintEvalToken0 (evm := evm6)
    (locals := ammBurnAfterTransfer1Store evm I b0 b1)
    (ammBurnAfterTransfer1Store_token0_none evm I b0 b1)
  have hargs := ammMintEvalBalanceArgs (evm := evm6)
    (locals := ammBurnAfterTransfer1Store evm I b0 b1)
  have hdec := ammMintDecodeBalance_ok hlo
    (by omega : out.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterTransfer1Store evm I b0 b1 }
      evm6 [tokenBalance (.storage token0Ref) "newBalance0"]
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out } evm7) := by
    simp only [tokenBalance]
    simpa [ammBurnAfterBalance0Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

def ammBurnReserve0Word (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

def ammBurnAfterReserve0 (evm : EVM.State) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (ammBurnReserve0Word out)

theorem ammBurnEvalNewBalance0 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out : ByteArray) :
    evalExpr? config
      { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out }
      evm' (.var "newBalance0") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32)))) := by
  simp [evalExpr?, ammBurnAfterBalance0Store, EvalResult.ofOption]

theorem ammBurnAssignReserve0 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out : ByteArray)
    (hlo : 32 ≤ out.size) :
    assignStorageRef? config
      { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out }
      evm' .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out },
        ammBurnAfterReserve0 evm' out) := by
  have hword : (ammBurnReserve0Word out).toNat =
      fromByteArrayBigEndian (out.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm' (wordLoc ⟨5⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      some (ammBurnAfterReserve0 evm' out) := by
    simpa [ammBurnAfterReserve0, hword] using
      ammStorageLocStore_uint256 evm' ⟨5⟩ (ammBurnReserve0Word out)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      ammBurnAfterBalance0Store evm I b0 b1 out })
    (evm := evm') (evm' := ammBurnAfterReserve0 evm' out)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (by simp [ammBurnAfterBalance0Store,
      ammBurnAfterTransfer1Store, ammBurnAfterTransfer0Store,
      ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
      ammBurnAfterAmount0Store, ammBurnAfterNum0Store,
      ammBurnStore, reserve0Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem ammBurnSourceReserve0Ok {evm evm7 : EVM.State}
    (I : ExecutionEnv) (out : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixTransfers ++
        [tokenBalance (.storage token0Ref) "newBalance0"])
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out } evm7))
    (hlo : 32 ≤ out.size) :
    ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixTransfers ++
        [tokenBalance (.storage token0Ref) "newBalance0",
         .assign .storage reserve0Ref (.var "newBalance0")])
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out }
        (ammBurnAfterReserve0 evm7 out)) := by
  have heval := ammBurnEvalNewBalance0
    (evm := evm) (evm' := evm7) I b0 b1 out
  have hassign := ammBurnAssignReserve0
    (evm := evm) (evm' := evm7) I b0 b1 out hlo
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out }
      evm7 [.assign .storage reserve0Ref (.var "newBalance0")]
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out }
        (ammBurnAfterReserve0 evm7 out)) := by
    exact ExecBlock.consNormal
      (ExecStmt.assign heval hassign) ExecBlock.nil
  simpa [List.append_assoc] using execBlock_append hprefix htail

def ammBurnSourcePrefixReserve0 : List Stmt :=
  ammBurnSourcePrefixTransfers ++
    [tokenBalance (.storage token0Ref) "newBalance0",
     .assign .storage reserve0Ref (.var "newBalance0")]

theorem ammBurnAfterBalance0Store_token1_none (evm : EVM.State)
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 : ByteArray) :
    (ammBurnAfterBalance0Store evm I b0 b1 out0).get? "token1" = none := by
  simp [ammBurnAfterBalance0Store, ammBurnAfterTransfer1Store,
    ammBurnAfterTransfer0Store, ammBurnAfterAmount1Store,
    ammBurnAfterNum1Store, ammBurnAfterAmount0Store,
    ammBurnAfterNum0Store, ammBurnStore]

theorem ammBurnSourceBalance1CallFailed {evm evm8 evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out0 } evm8))
    (hcall : typedCallViaEVM config evm8
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm8
          evm8.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm8.executionEnv.codeOwner]
      (false, evm9, out1) false) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm8)
    (locals := ammBurnAfterBalance0Store evm I b0 b1 out0)
    (ammBurnAfterBalance0Store_token1_none evm I b0 b1 out0)
  have hargs := ammMintEvalBalanceArgs (evm := evm8)
    (locals := ammBurnAfterBalance0Store evm I b0 b1 out0)
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out0 }
      evm8 (burnTransition.body.drop 14) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallFailure
      hreceiver (by simp [evalExpr?, pure]) hargs hcall)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixReserve0, ammBurnSourcePrefixTransfers,
      ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, tokenTransfer, tokenBalance,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammBurnSourceBalance1DecodeRevert {evm evm8 evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out0 } evm8))
    (hcall : typedCallViaEVM config evm8
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm8
          evm8.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm8.executionEnv.codeOwner]
      (true, evm9, out1) false)
    (hdec : config.externalABI.decode? "balanceOf" out1 = none) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body .reverted := by
  have hreceiver := ammMintEvalToken1 (evm := evm8)
    (locals := ammBurnAfterBalance0Store evm I b0 b1 out0)
    (ammBurnAfterBalance0Store_token1_none evm I b0 b1 out0)
  have hargs := ammMintEvalBalanceArgs (evm := evm8)
    (locals := ammBurnAfterBalance0Store evm I b0 b1 out0)
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out0 }
      evm8 (burnTransition.body.drop 14) .reverted := by
    simp only [burnTransition, nonpayable, checkedDivInto, tokenTransfer,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
      hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body .reverted := by
    simpa [ammBurnSourcePrefixReserve0, ammBurnSourcePrefixTransfers,
      ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, tokenTransfer, tokenBalance,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammBurnAfterBalance1Store (evm : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) : Store :=
  (ammBurnAfterBalance0Store evm I b0 b1 out0).insert "newBalance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32))))

theorem ammBurnSourceBalance1CallOk {evm evm8 evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      ammBurnSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out0 } evm8))
    (hcall : typedCallViaEVM config evm8
      (EVM.address (AccountAddress.ofUInt256
        (UInt256.land (Solm.EVM.storageLoad evm8
          evm8.executionEnv.codeOwner ⟨4⟩) solcAddrMask)).val)
      "balanceOf" 0 [.address evm8.executionEnv.codeOwner]
      (true, evm9, out1) false)
    (hlo : 32 ≤ out1.size) (hbound : out1.size < 2 ^ 138) :
    ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixReserve0 ++
        [tokenBalance (.storage token1Ref) "newBalance1"])
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 } evm9) := by
  have hreceiver := ammMintEvalToken1 (evm := evm8)
    (locals := ammBurnAfterBalance0Store evm I b0 b1 out0)
    (ammBurnAfterBalance0Store_token1_none evm I b0 b1 out0)
  have hargs := ammMintEvalBalanceArgs (evm := evm8)
    (locals := ammBurnAfterBalance0Store evm I b0 b1 out0)
  have hdec := ammMintDecodeBalance_ok hlo
    (by omega : out1.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterBalance0Store evm I b0 b1 out0 }
      evm8 [tokenBalance (.storage token1Ref) "newBalance1"]
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 } evm9) := by
    simp only [tokenBalance]
    simpa [ammBurnAfterBalance1Store, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess hreceiver
          (by simp [evalExpr?, pure]) hargs hcall hdec) ExecBlock.nil)
  exact execBlock_append hprefix htail

def ammBurnReserve1Word (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

def ammBurnAfterReserve1 (evm : EVM.State) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (ammBurnReserve1Word out)

theorem ammBurnEvalNewBalance1 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray) :
    evalExpr? config
      { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 }
      evm' (.var "newBalance1") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out1.extract 0 32)))) := by
  simp [evalExpr?, ammBurnAfterBalance1Store, EvalResult.ofOption]

theorem ammBurnAssignReserve1 {evm evm' : EVM.State}
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hlo : 32 ≤ out1.size) :
    assignStorageRef? config
      { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 }
      evm' .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 },
        ammBurnAfterReserve1 evm' out1) := by
  have hword : (ammBurnReserve1Word out1).toNat =
      fromByteArrayBigEndian (out1.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm' (wordLoc ⟨6⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))) =
      some (ammBurnAfterReserve1 evm' out1) := by
    simpa [ammBurnAfterReserve1, hword] using
      ammStorageLocStore_uint256 evm' ⟨6⟩ (ammBurnReserve1Word out1)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      ammBurnAfterBalance1Store evm I b0 b1 out0 out1 })
    (evm := evm') (evm' := ammBurnAfterReserve1 evm' out1)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))
    (by simp [ammBurnAfterBalance1Store, ammBurnAfterBalance0Store,
      ammBurnAfterTransfer1Store, ammBurnAfterTransfer0Store,
      ammBurnAfterAmount1Store, ammBurnAfterNum1Store,
      ammBurnAfterAmount0Store, ammBurnAfterNum0Store,
      ammBurnStore, reserve1Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem ammBurnSourceReserve1Ok {evm evm9 : EVM.State}
    (I : ExecutionEnv) (out0 out1 : ByteArray) (b0 b1 : Bool)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      (ammBurnSourcePrefixReserve0 ++
        [tokenBalance (.storage token1Ref) "newBalance1"])
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 } evm9))
    (hlo : 32 ≤ out1.size) :
    ExecTransitionBody config contract evm (ammBurnStore I)
      burnTransition.body
      (.returned { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 }
        (ammBurnAfterReserve1 evm9 out1) none) := by
  have heval := ammBurnEvalNewBalance1
    (evm := evm) (evm' := evm9) I b0 b1 out0 out1
  have hassign := ammBurnAssignReserve1
    (evm := evm) (evm' := evm9) I b0 b1 out0 out1 hlo
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 }
      evm9 [.assign .storage reserve1Ref (.var "newBalance1")]
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 }
        (ammBurnAfterReserve1 evm9 out1)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammBurnStore I } evm
      burnTransition.body
      (.ok { contract := contract, locals :=
        ammBurnAfterBalance1Store evm I b0 b1 out0 out1 }
        (ammBurnAfterReserve1 evm9 out1)) := by
    simpa [ammBurnSourcePrefixReserve0, ammBurnSourcePrefixTransfers,
      ammBurnSourcePrefixSender, ammBurnSourcePrefixSupply,
      ammBurnSourcePrefixAmounts, ammBurnSourcePrefixNum1,
      ammBurnSourcePrefixAmount0, burnTransition, nonpayable,
      checkedDivInto, tokenTransfer, tokenBalance,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hbody

end Benchmarks.ActAmm
