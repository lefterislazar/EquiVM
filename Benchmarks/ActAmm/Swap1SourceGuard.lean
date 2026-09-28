import Benchmarks.ActAmm.Swap0SourceGuard
import Benchmarks.ActAmm.Swap1GuardTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1EvalAmount {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.var "amount0Out") =
      .ok (.int (Int.ofNat (ammSwap1AmountWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammSwap1Store]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem ammSwap1EvalReserve1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  exact ammMintEvalReserve0 (evm := evm) (locals := ammSwap1Store I)
    (by simp [ammSwap1Store])

theorem ammSwap1EvalPositive_true {evm : EVM.State} {I : ExecutionEnv}
    (hpos : 0 < (ammSwap1AmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.binary .gt (.var "amount0Out") (.intLit 0)) =
      .ok (.bool true) := by
  exact ammEvalNatGt_true (a := (ammSwap1AmountWord I).toNat)
    (b := 0) ammSwap1EvalAmount
    (by simp [evalExpr?, pure]) hpos

theorem ammSwap1EvalPositive_false {evm : EVM.State} {I : ExecutionEnv}
    (hzero : (ammSwap1AmountWord I).toNat = 0) :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.binary .gt (.var "amount0Out") (.intLit 0)) =
      .ok (.bool false) := by
  exact ammEvalNatGt_false (a := (ammSwap1AmountWord I).toNat)
    (b := 0) ammSwap1EvalAmount
    (by simp [evalExpr?, pure]) (by omega)

theorem ammSwap1EvalLiquidity_true {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.binary .lt (.var "amount0Out") (.storage reserve0Ref)) =
      .ok (.bool true) := by
  exact ammEvalNatLt_true ammSwap1EvalAmount
    ammSwap1EvalReserve1 hliq

theorem ammSwap1EvalLiquidity_false {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      (ammSwap1AmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.binary .lt (.var "amount0Out") (.storage reserve0Ref)) =
      .ok (.bool false) := by
  exact ammEvalNatLt_false ammSwap1EvalAmount
    ammSwap1EvalReserve1 hliq

theorem ammSwap1SourceZeroOutput (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : (ammSwap1AmountWord I).toNat = 0) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hguard := ammSwap1EvalPositive_false (evm := evm) hzero
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simp only [swap1Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammSwap1SourceInsufficientLiquidity
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      (ammSwap1AmountWord I).toNat) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hguard0 := ammSwap1EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap1EvalLiquidity_false (evm := evm) hliq
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simp only [swap1Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue hguard0) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard1)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

def ammSwap1SourcePrefixLiquidity : List Stmt :=
  nonpayable ++
    [.require (.binary .gt (.var "amount0Out") (.intLit 0)),
     .require (.binary .lt (.var "amount0Out") (.storage reserve0Ref))]

theorem ammSwap1SourceLiquidityOk
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecBlock config { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixLiquidity
      (.ok { contract := contract, locals := ammSwap1Store I } evm) := by
  have hguard0 := ammSwap1EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap1EvalLiquidity_true (evm := evm) hliq
  simp only [ammSwap1SourcePrefixLiquidity, nonpayable,
    List.cons_append, List.nil_append]
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard0) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard1) ExecBlock.nil

theorem ammSwap1EvalTo {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.var "to") =
      .ok (.address (AccountAddress.ofNat
        (ammSwap1ToWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammSwap1Store]
  rw [store_get_self]

theorem ammSwap1EvalToken0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.storage token0Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask))) := by
  exact ammMintEvalToken0 (evm := evm) (locals := ammSwap1Store I)
    (by simp [ammSwap1Store])

theorem ammSwap1EvalToken1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap1Store I } evm
      (.storage token1Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask))) := by
  exact ammMintEvalToken1 (evm := evm) (locals := ammSwap1Store I)
    (by simp [ammSwap1Store])

theorem ammSwap1EvalRecipientGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := ammSwap1Store I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool true) := by
  exact ammEvalAnd_true
    (ammEvalAddressNe_true ammSwap1EvalTo ammSwap1EvalToken0 h0)
    (ammEvalAddressNe_true ammSwap1EvalTo ammSwap1EvalToken1 h1)

theorem ammSwap1EvalRecipientGuard_false0 {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := ammSwap1Store I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool false) := by
  exact ammEvalAnd_false_left
    (ammEvalAddressNe_false ammSwap1EvalTo ammSwap1EvalToken0 h0)

theorem ammSwap1EvalRecipientGuard_false1 {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := ammSwap1Store I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool false) := by
  exact ammEvalAnd_false_right
    (ammEvalAddressNe_true ammSwap1EvalTo ammSwap1EvalToken0 h0)
    (ammEvalAddressNe_false ammSwap1EvalTo ammSwap1EvalToken1 h1)

theorem ammSwap1SourceInvalidRecipient0
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hguard0 := ammSwap1EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap1EvalLiquidity_true (evm := evm) hliq
  have hguard2 := ammSwap1EvalRecipientGuard_false0 (evm := evm) h0
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simp only [swap1Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard0) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard1) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard2)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammSwap1SourceInvalidRecipient1
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap1AmountWord I).toNat)
    (hliq : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap1ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have hguard0 := ammSwap1EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap1EvalLiquidity_true (evm := evm) hliq
  have hguard2 := ammSwap1EvalRecipientGuard_false1 (evm := evm) h0 h1
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simp only [swap1Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard0) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard1) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard2)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

def ammSwap1SourcePrefixRecipient : List Stmt :=
  ammSwap1SourcePrefixLiquidity ++
    [.require (.binary .and
      (.binary .ne (.var "to") (.storage token0Ref))
      (.binary .ne (.var "to") (.storage token1Ref)))]

theorem ammSwap1SourceRecipientOk
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
        solcAddrMask)) :
    ExecBlock config { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixRecipient
      (.ok { contract := contract, locals := ammSwap1Store I } evm) := by
  have hguard0 := ammSwap1EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap1EvalLiquidity_true (evm := evm) hliq
  have hguard2 := ammSwap1EvalRecipientGuard_true (evm := evm) h0 h1
  simp only [ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
    nonpayable, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard0) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard1) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard2) ExecBlock.nil

theorem ammSwap1ValidSourceGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcanon : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hliq : (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨5⟩).toNat)
    (hne0 : ammSwap1ToWord I ≠ ammMintToken0Word σ_evm I)
    (hne1 : ammSwap1ToWord I ≠ ammMintToken1Word σ_evm I) :
    let evmS := initState cA gh bl σ_solm σ₀ g A I
    (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨5⟩).toNat ∧
    AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) ∧
    AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask) := by
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  have hslot3 : solcSlotWord σ_evm I ⟨3⟩ =
      solcSlotWord σ_solm I ⟨3⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hslot4 : solcSlotWord σ_evm I ⟨4⟩ =
      solcSlotWord σ_solm I ⟨4⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
  have hslot5 : solcSlotWord σ_evm I ⟨5⟩ =
      solcSlotWord σ_solm I ⟨5⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliqS : (ammSwap1AmountWord I).toNat <
      (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨5⟩).toNat := by
    change (ammSwap1AmountWord I).toNat <
      (solcSlotWord σ_solm I ⟨5⟩).toNat
    rw [← hslot5]
    exact hliq
  have h0S : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (ammMintToken0Word σ_solm I)
    rw [← show ammMintToken0Word σ_evm I =
      ammMintToken0Word σ_solm I by
        simp only [ammMintToken0Word, hslot3]]
    intro haddr
    exact hne0 ((ammCanonicalAddressWordEq hcanon
      (solcAddrMask_result_canonical
        (solcSlotWord σ_evm I ⟨3⟩))).mp haddr)
  have h1S : AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap1ToWord I).toNat ≠
      AccountAddress.ofUInt256 (ammMintToken1Word σ_solm I)
    rw [← show ammMintToken1Word σ_evm I =
      ammMintToken1Word σ_solm I by
        simp only [ammMintToken1Word, hslot4]]
    intro haddr
    exact hne1 ((ammCanonicalAddressWordEq hcanon
      (solcAddrMask_result_canonical
        (solcSlotWord σ_evm I ⟨4⟩))).mp haddr)
  exact ⟨hliqS, h0S, h1S⟩

end Benchmarks.ActAmm
