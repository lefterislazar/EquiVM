import Benchmarks.ActAmm.Swap0GuardTrace
import Benchmarks.ActAmm.MintSourceArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

-- LIBRARY CANDIDATE: Reasoning.SolmBody, natural-number comparison expressions.
theorem ammEvalNatGt_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : b < a) :
    evalExpr? cfg frame evm (.binary .gt x y) = .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem ammEvalNatGt_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : a ≤ b) :
    evalExpr? cfg frame evm (.binary .gt x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem ammEvalNatLt_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : a < b) :
    evalExpr? cfg frame evm (.binary .lt x y) = .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem ammEvalNatLt_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : b ≤ a) :
    evalExpr? cfg frame evm (.binary .lt x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem ammSwap0EvalAmount {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.var "amount1Out") =
      .ok (.int (Int.ofNat (ammSwap0AmountWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammSwap0Store]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem ammSwap0EvalReserve1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  exact ammMintEvalReserve1 (evm := evm) (locals := ammSwap0Store I)
    (by simp [ammSwap0Store])

theorem ammSwap0EvalPositive_true {evm : EVM.State} {I : ExecutionEnv}
    (hpos : 0 < (ammSwap0AmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.binary .gt (.var "amount1Out") (.intLit 0)) =
      .ok (.bool true) := by
  exact ammEvalNatGt_true (a := (ammSwap0AmountWord I).toNat)
    (b := 0) ammSwap0EvalAmount
    (by simp [evalExpr?, pure]) hpos

theorem ammSwap0EvalPositive_false {evm : EVM.State} {I : ExecutionEnv}
    (hzero : (ammSwap0AmountWord I).toNat = 0) :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.binary .gt (.var "amount1Out") (.intLit 0)) =
      .ok (.bool false) := by
  exact ammEvalNatGt_false (a := (ammSwap0AmountWord I).toNat)
    (b := 0) ammSwap0EvalAmount
    (by simp [evalExpr?, pure]) (by omega)

theorem ammSwap0EvalLiquidity_true {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.binary .lt (.var "amount1Out") (.storage reserve1Ref)) =
      .ok (.bool true) := by
  exact ammEvalNatLt_true ammSwap0EvalAmount
    ammSwap0EvalReserve1 hliq

theorem ammSwap0EvalLiquidity_false {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      (ammSwap0AmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.binary .lt (.var "amount1Out") (.storage reserve1Ref)) =
      .ok (.bool false) := by
  exact ammEvalNatLt_false ammSwap0EvalAmount
    ammSwap0EvalReserve1 hliq

theorem ammSwap0SourceZeroOutput (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : (ammSwap0AmountWord I).toNat = 0) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hguard := ammSwap0EvalPositive_false (evm := evm) hzero
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simp only [swap0Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammSwap0SourceInsufficientLiquidity
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      (ammSwap0AmountWord I).toNat) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hguard0 := ammSwap0EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap0EvalLiquidity_false (evm := evm) hliq
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simp only [swap0Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue hguard0) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard1)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

def ammSwap0SourcePrefixLiquidity : List Stmt :=
  nonpayable ++
    [.require (.binary .gt (.var "amount1Out") (.intLit 0)),
     .require (.binary .lt (.var "amount1Out") (.storage reserve1Ref))]

theorem ammSwap0SourceLiquidityOk
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm
        evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecBlock config { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixLiquidity
      (.ok { contract := contract, locals := ammSwap0Store I } evm) := by
  have hguard0 := ammSwap0EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap0EvalLiquidity_true (evm := evm) hliq
  simp only [ammSwap0SourcePrefixLiquidity, nonpayable,
    List.cons_append, List.nil_append]
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard0) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard1) ExecBlock.nil

theorem ammSwap0EvalTo {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.var "to") =
      .ok (.address (AccountAddress.ofNat
        (ammSwap0ToWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, ammSwap0Store]
  rw [store_get_self]

theorem ammSwap0EvalToken0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.storage token0Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask))) := by
  exact ammMintEvalToken0 (evm := evm) (locals := ammSwap0Store I)
    (by simp [ammSwap0Store])

theorem ammSwap0EvalToken1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := ammSwap0Store I } evm
      (.storage token1Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask))) := by
  exact ammMintEvalToken1 (evm := evm) (locals := ammSwap0Store I)
    (by simp [ammSwap0Store])

-- LIBRARY CANDIDATE: Reasoning.SolmBody, address equality expressions.
theorem ammEvalAddressNe_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (hne : a ≠ b) :
    evalExpr? cfg frame evm (.binary .ne x y) =
      .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy,
    hne]

theorem ammEvalAddressNe_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (heq : a = b) :
    evalExpr? cfg frame evm (.binary .ne x y) =
      .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy,
    heq]

-- The expression evaluator handles logical conjunction before generic binary
-- operators, so the right operand is evaluated only when the left is true.
theorem ammEvalAnd_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool true))
    (hy : evalExpr? cfg frame evm y = .ok (.bool true)) :
    evalExpr? cfg frame evm (.binary .and x y) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, pure]

theorem ammEvalAnd_false_left {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool false)) :
    evalExpr? cfg frame evm (.binary .and x y) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, pure]

theorem ammEvalAnd_false_right {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool true))
    (hy : evalExpr? cfg frame evm y = .ok (.bool false)) :
    evalExpr? cfg frame evm (.binary .and x y) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, pure]

theorem ammCanonicalAddressWordEq {a b : UInt256}
    (ha : a.toNat < EVM.addressModulus)
    (hb : b.toNat < EVM.addressModulus) :
    AccountAddress.ofNat a.toNat = AccountAddress.ofUInt256 b ↔ a = b := by
  constructor
  · intro h
    rw [accountAddress_ofUInt256_eq_ofNat_toNat] at h
    have ha' : a.toNat < AccountAddress.size := by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using ha
    have hb' : b.toNat < AccountAddress.size := by
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hb
    have hv := congrArg (fun x : AccountAddress => x.val) h
    change a.toNat % AccountAddress.size =
      b.toNat % AccountAddress.size at hv
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hv
    exact u256_inj hv
  · intro h
    subst b
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem ammSwap0EvalRecipientGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := ammSwap0Store I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool true) := by
  exact ammEvalAnd_true
    (ammEvalAddressNe_true ammSwap0EvalTo ammSwap0EvalToken0 h0)
    (ammEvalAddressNe_true ammSwap0EvalTo ammSwap0EvalToken1 h1)

theorem ammSwap0EvalRecipientGuard_false0 {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := ammSwap0Store I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool false) := by
  exact ammEvalAnd_false_left
    (ammEvalAddressNe_false ammSwap0EvalTo ammSwap0EvalToken0 h0)

theorem ammSwap0EvalRecipientGuard_false1 {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := ammSwap0Store I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool false) := by
  exact ammEvalAnd_false_right
    (ammEvalAddressNe_true ammSwap0EvalTo ammSwap0EvalToken0 h0)
    (ammEvalAddressNe_false ammSwap0EvalTo ammSwap0EvalToken1 h1)

theorem ammSwap0SourceInvalidRecipient0
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hguard0 := ammSwap0EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap0EvalLiquidity_true (evm := evm) hliq
  have hguard2 := ammSwap0EvalRecipientGuard_false0 (evm := evm) h0
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simp only [swap0Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard0) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard1) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard2)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem ammSwap0SourceInvalidRecipient1
    (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hpos : 0 < (ammSwap0AmountWord I).toNat)
    (hliq : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)
    (h0 : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (ammSwap0ToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have hguard0 := ammSwap0EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap0EvalLiquidity_true (evm := evm) hliq
  have hguard2 := ammSwap0EvalRecipientGuard_false1 (evm := evm) h0 h1
  have hblock : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simp only [swap0Transition, nonpayable,
      List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard0) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard1) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard2)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

def ammSwap0SourcePrefixRecipient : List Stmt :=
  ammSwap0SourcePrefixLiquidity ++
    [.require (.binary .and
      (.binary .ne (.var "to") (.storage token0Ref))
      (.binary .ne (.var "to") (.storage token1Ref)))]

theorem ammSwap0SourceRecipientOk
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
        solcAddrMask)) :
    ExecBlock config { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixRecipient
      (.ok { contract := contract, locals := ammSwap0Store I } evm) := by
  have hguard0 := ammSwap0EvalPositive_true (evm := evm) hpos
  have hguard1 := ammSwap0EvalLiquidity_true (evm := evm) hliq
  have hguard2 := ammSwap0EvalRecipientGuard_true (evm := evm) h0 h1
  simp only [ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
    nonpayable, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard0) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard1) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hguard2) ExecBlock.nil

theorem ammSwap0ValidSourceGuards
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcanon : (ammSwap0ToWord I).toNat < EVM.addressModulus)
    (hliq : (ammSwap0AmountWord I).toNat <
      (solcSlotWord σ_evm I ⟨6⟩).toNat)
    (hne0 : ammSwap0ToWord I ≠ ammMintToken0Word σ_evm I)
    (hne1 : ammSwap0ToWord I ≠ ammMintToken1Word σ_evm I) :
    let evmS := initState cA gh bl σ_solm σ₀ g A I
    (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨6⟩).toNat ∧
    AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) ∧
    AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
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
  have hslot6 : solcSlotWord σ_evm I ⟨6⟩ =
      solcSlotWord σ_solm I ⟨6⟩ := by
    simpa [solcSlotWord, codeOwnerStorageWord] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hliqS : (ammSwap0AmountWord I).toNat <
      (Solm.EVM.storageLoad evmS
        evmS.executionEnv.codeOwner ⟨6⟩).toNat := by
    change (ammSwap0AmountWord I).toNat <
      (solcSlotWord σ_solm I ⟨6⟩).toNat
    rw [← hslot6]
    exact hliq
  have h0S : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (ammMintToken0Word σ_solm I)
    rw [← show ammMintToken0Word σ_evm I =
      ammMintToken0Word σ_solm I by
        simp only [ammMintToken0Word, hslot3]]
    intro haddr
    exact hne0 ((ammCanonicalAddressWordEq hcanon
      (solcAddrMask_result_canonical
        (solcSlotWord σ_evm I ⟨3⟩))).mp haddr)
  have h1S : AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask) := by
    change AccountAddress.ofNat (ammSwap0ToWord I).toNat ≠
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
