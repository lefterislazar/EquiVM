import Benchmarks.ActAmm4.SwapArithmeticTrace
import Benchmarks.ActAmm4.MintSourceArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4EvalNatGt_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : b < a) :
    evalExpr? cfg frame evm (.binary .gt x y) = .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem amm4EvalNatGt_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : a ≤ b) :
    evalExpr? cfg frame evm (.binary .gt x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem amm4EvalNatLt_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : a < b) :
    evalExpr? cfg frame evm (.binary .lt x y) = .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem amm4EvalNatLt_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : Nat}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (h : b ≤ a) :
    evalExpr? cfg frame evm (.binary .lt x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

theorem amm4EvalOr_true_left {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool true)) :
    evalExpr? cfg frame evm (.binary .or x y) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, pure]

theorem amm4EvalOr_true_right {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool false))
    (hy : evalExpr? cfg frame evm y = .ok (.bool true)) :
    evalExpr? cfg frame evm (.binary .or x y) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, pure]

theorem amm4EvalOr_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool false))
    (hy : evalExpr? cfg frame evm y = .ok (.bool false)) :
    evalExpr? cfg frame evm (.binary .or x y) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, pure]

theorem amm4EvalAnd_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool true))
    (hy : evalExpr? cfg frame evm y = .ok (.bool true)) :
    evalExpr? cfg frame evm (.binary .and x y) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, pure]

theorem amm4EvalAnd_false_left {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool false)) :
    evalExpr? cfg frame evm (.binary .and x y) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, pure]

theorem amm4EvalAnd_false_right {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr}
    (hx : evalExpr? cfg frame evm x = .ok (.bool true))
    (hy : evalExpr? cfg frame evm y = .ok (.bool false)) :
    evalExpr? cfg frame evm (.binary .and x y) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, pure]

theorem amm4SwapEvalAmount0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.var "amount0Out") =
      .ok (.int (Int.ofNat (amm4SwapAmount0Word I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4SwapStore]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem amm4SwapEvalAmount1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.var "amount1Out") =
      .ok (.int (Int.ofNat (amm4SwapAmount1Word I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4SwapStore]
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem amm4SwapEvalTo {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.var "to") =
      .ok (.address (AccountAddress.ofNat (amm4SwapToWord I).toNat)) := by
  simp only [evalExpr?, EvalResult.ofOption, amm4SwapStore]
  rw [store_get_self]

theorem amm4SwapEvalReserve0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  exact amm4MintEvalReserve0 (evm := evm) (locals := amm4SwapStore I)
    (by simp [amm4SwapStore])

theorem amm4SwapEvalReserve1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  exact amm4MintEvalReserve1 (evm := evm) (locals := amm4SwapStore I)
    (by simp [amm4SwapStore])

theorem amm4SwapEvalPositive0_true {evm : EVM.State} {I : ExecutionEnv}
    (hpos : 0 < (amm4SwapAmount0Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .gt (.var "amount0Out") (.intLit 0)) =
      .ok (.bool true) := by
  exact amm4EvalNatGt_true amm4SwapEvalAmount0
    (by simp [evalExpr?, pure]) hpos

theorem amm4SwapEvalPositive0_false {evm : EVM.State} {I : ExecutionEnv}
    (hzero : (amm4SwapAmount0Word I).toNat = 0) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .gt (.var "amount0Out") (.intLit 0)) =
      .ok (.bool false) := by
  exact amm4EvalNatGt_false
    (a := (amm4SwapAmount0Word I).toNat) (b := 0)
    amm4SwapEvalAmount0
    (by simp [evalExpr?, pure]) (by omega)

theorem amm4SwapEvalPositive1_true {evm : EVM.State} {I : ExecutionEnv}
    (hpos : 0 < (amm4SwapAmount1Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .gt (.var "amount1Out") (.intLit 0)) =
      .ok (.bool true) := by
  exact amm4EvalNatGt_true amm4SwapEvalAmount1
    (by simp [evalExpr?, pure]) hpos

theorem amm4SwapEvalPositive1_false {evm : EVM.State} {I : ExecutionEnv}
    (hzero : (amm4SwapAmount1Word I).toNat = 0) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .gt (.var "amount1Out") (.intLit 0)) =
      .ok (.bool false) := by
  exact amm4EvalNatGt_false
    (a := (amm4SwapAmount1Word I).toNat) (b := 0)
    amm4SwapEvalAmount1
    (by simp [evalExpr?, pure]) (by omega)

theorem amm4SwapEvalOutputGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (hpos : 0 < (amm4SwapAmount0Word I).toNat ∨
      0 < (amm4SwapAmount1Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .or
        (.binary .gt (.var "amount0Out") (.intLit 0))
        (.binary .gt (.var "amount1Out") (.intLit 0))) =
      .ok (.bool true) := by
  rcases hpos with h0 | h1
  · exact amm4EvalOr_true_left (amm4SwapEvalPositive0_true h0)
  · by_cases h0 : 0 < (amm4SwapAmount0Word I).toNat
    · exact amm4EvalOr_true_left (amm4SwapEvalPositive0_true h0)
    · exact amm4EvalOr_true_right
        (amm4SwapEvalPositive0_false (Nat.eq_zero_of_not_pos h0))
        (amm4SwapEvalPositive1_true h1)

theorem amm4SwapEvalOutputGuard_false {evm : EVM.State} {I : ExecutionEnv}
    (h0 : (amm4SwapAmount0Word I).toNat = 0)
    (h1 : (amm4SwapAmount1Word I).toNat = 0) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .or
        (.binary .gt (.var "amount0Out") (.intLit 0))
        (.binary .gt (.var "amount1Out") (.intLit 0))) =
      .ok (.bool false) := by
  exact amm4EvalOr_false
    (amm4SwapEvalPositive0_false h0)
    (amm4SwapEvalPositive1_false h1)

theorem amm4SwapEvalLiquidity0_true {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .lt (.var "amount0Out") (.storage reserve0Ref)) =
      .ok (.bool true) := by
  exact amm4EvalNatLt_true amm4SwapEvalAmount0
    amm4SwapEvalReserve0 hliq

theorem amm4SwapEvalLiquidity0_false {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      (amm4SwapAmount0Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .lt (.var "amount0Out") (.storage reserve0Ref)) =
      .ok (.bool false) := by
  exact amm4EvalNatLt_false amm4SwapEvalAmount0
    amm4SwapEvalReserve0 hliq

theorem amm4SwapEvalLiquidity1_true {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .lt (.var "amount1Out") (.storage reserve1Ref)) =
      .ok (.bool true) := by
  exact amm4EvalNatLt_true amm4SwapEvalAmount1
    amm4SwapEvalReserve1 hliq

theorem amm4SwapEvalLiquidity1_false {evm : EVM.State} {I : ExecutionEnv}
    (hliq : (Solm.EVM.storageLoad evm
      evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      (amm4SwapAmount1Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .lt (.var "amount1Out") (.storage reserve1Ref)) =
      .ok (.bool false) := by
  exact amm4EvalNatLt_false amm4SwapEvalAmount1
    amm4SwapEvalReserve1 hliq

theorem amm4SwapEvalLiquidityGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (amm4SwapAmount1Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .and
        (.binary .lt (.var "amount0Out") (.storage reserve0Ref))
        (.binary .lt (.var "amount1Out") (.storage reserve1Ref))) =
      .ok (.bool true) := by
  exact amm4EvalAnd_true
    (amm4SwapEvalLiquidity0_true hliq0)
    (amm4SwapEvalLiquidity1_true hliq1)

theorem amm4SwapEvalLiquidityGuard_false0 {evm : EVM.State} {I : ExecutionEnv}
    (hliq0 : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      (amm4SwapAmount0Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .and
        (.binary .lt (.var "amount0Out") (.storage reserve0Ref))
        (.binary .lt (.var "amount1Out") (.storage reserve1Ref))) =
      .ok (.bool false) := by
  exact amm4EvalAnd_false_left (amm4SwapEvalLiquidity0_false hliq0)

theorem amm4SwapEvalLiquidityGuard_false1 {evm : EVM.State} {I : ExecutionEnv}
    (hliq0 : (amm4SwapAmount0Word I).toNat <
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)
    (hliq1 : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      (amm4SwapAmount1Word I).toNat) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .and
        (.binary .lt (.var "amount0Out") (.storage reserve0Ref))
        (.binary .lt (.var "amount1Out") (.storage reserve1Ref))) =
      .ok (.bool false) := by
  exact amm4EvalAnd_false_right
    (amm4SwapEvalLiquidity0_true hliq0)
    (amm4SwapEvalLiquidity1_false hliq1)


theorem amm4EvalAddressNe_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (hne : a ≠ b) :
    evalExpr? cfg frame evm (.binary .ne x y) =
      .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy,
    hne]

theorem amm4EvalAddressNe_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (heq : a = b) :
    evalExpr? cfg frame evm (.binary .ne x y) =
      .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy,
    heq]


theorem amm4CanonicalAddressWordEq {a b : UInt256}
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


theorem amm4SwapEvalToken0 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := amm4SwapStore I } evm
      (.storage token0Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask))) := by
  exact amm4MintEvalToken0 (evm := evm) (locals := amm4SwapStore I)
    (by simp [amm4SwapStore])

theorem amm4SwapEvalToken1 {evm : EVM.State} {I : ExecutionEnv} :
    evalExpr? config
      { contract := contract, locals := amm4SwapStore I } evm
      (.storage token1Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask))) := by
  exact amm4MintEvalToken1 (evm := evm) (locals := amm4SwapStore I)
    (by simp [amm4SwapStore])

theorem amm4SwapEvalRecipientGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool true) := by
  exact amm4EvalAnd_true
    (amm4EvalAddressNe_true amm4SwapEvalTo amm4SwapEvalToken0 h0)
    (amm4EvalAddressNe_true amm4SwapEvalTo amm4SwapEvalToken1 h1)

theorem amm4SwapEvalRecipientGuard_false0 {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (amm4SwapToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool false) := by
  exact amm4EvalAnd_false_left
    (amm4EvalAddressNe_false amm4SwapEvalTo amm4SwapEvalToken0 h0)

theorem amm4SwapEvalRecipientGuard_false1 {evm : EVM.State} {I : ExecutionEnv}
    (h0 : AccountAddress.ofNat (amm4SwapToWord I).toNat ≠
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        solcAddrMask))
    (h1 : AccountAddress.ofNat (amm4SwapToWord I).toNat =
      AccountAddress.ofUInt256 (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        solcAddrMask)) :
    evalExpr? config { contract := contract, locals := amm4SwapStore I } evm
      (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) =
      .ok (.bool false) := by
  exact amm4EvalAnd_false_right
    (amm4EvalAddressNe_true amm4SwapEvalTo amm4SwapEvalToken0 h0)
    (amm4EvalAddressNe_false amm4SwapEvalTo amm4SwapEvalToken1 h1)

def amm4SwapSourcePrefixRecipient : List Stmt :=
  nonpayable ++
    [ .require (.binary .or
        (.binary .gt (.var "amount0Out") (.intLit 0))
        (.binary .gt (.var "amount1Out") (.intLit 0))),
      .require (.binary .and
        (.binary .lt (.var "amount0Out") (.storage reserve0Ref))
        (.binary .lt (.var "amount1Out") (.storage reserve1Ref))),
      .require (.binary .and
        (.binary .ne (.var "to") (.storage token0Ref))
        (.binary .ne (.var "to") (.storage token1Ref))) ]

theorem amm4SwapSourceRecipientOk
    (evm : EVM.State) (I : ExecutionEnv)
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
        solcAddrMask)) :
    ExecBlock config { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixRecipient
      (.ok { contract := contract, locals := amm4SwapStore I } evm) := by
  have hg0 := amm4SwapEvalOutputGuard_true (evm := evm) hpos
  have hg1 := amm4SwapEvalLiquidityGuard_true (evm := evm) hliq0 hliq1
  have hg2 := amm4SwapEvalRecipientGuard_true (evm := evm) h0 h1
  simp only [amm4SwapSourcePrefixRecipient, nonpayable,
    List.cons_append, List.nil_append]
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hg0) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hg1) <|
    ExecBlock.consNormal (ExecStmt.requireTrue hg2) ExecBlock.nil


end Benchmarks.ActAmm4
