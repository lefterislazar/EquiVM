import Benchmarks.ActAmm4.MintSourceArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4MintLiq0Value (o1 : ByteArray) (r0 supply reserve0 : UInt256) : Nat :=
  ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) * supply.toNat) /
    reserve0.toNat

def amm4MintLiq1Value (o2 : ByteArray) (r1 supply1 reserve1 : UInt256) : Nat :=
  ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) * supply1.toNat) /
    reserve1.toNat

theorem amm4MintEvalLiq0Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.var "liq0") =
      .ok (.int (Int.ofNat (amm4MintLiq0Value o1 r0 supply reserve0))) := by
  have hget : (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1).get?
      "liq0" = some (.int (Int.ofNat (amm4MintLiq0Value o1 r0 supply reserve0))) := by
    unfold amm4MintAfterLiq1Store amm4MintAfterLiq1NumeratorStore
    rw [store_get_ne _ (k := "liq1") (a := "liq0") _ (by decide)]
    rw [store_get_ne _ (k := "liq1Numerator") (a := "liq0") _ (by decide)]
    simp [amm4MintAfterLiq0Store, amm4MintLiq0Value]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem amm4MintEvalLiq1Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.var "liq1") =
      .ok (.int (Int.ofNat (amm4MintLiq1Value o2 r1 supply1 reserve1))) := by
  simp [amm4MintAfterLiq1Store, amm4MintLiq1Value, evalExpr?, EvalResult.ofOption]

theorem amm4MintEvalLiqSelect0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hle : amm4MintLiq0Value o1 r0 supply reserve0 ≤
      amm4MintLiq1Value o2 r1 supply1 reserve1) :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.binary .le (.var "liq0") (.var "liq1")) = .ok (.bool true) := by
  exact amm4EvalNatLe_true amm4MintEvalLiq0Local amm4MintEvalLiq1Local hle

theorem amm4MintEvalLiqSelect1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hgt : amm4MintLiq1Value o2 r1 supply1 reserve1 <
      amm4MintLiq0Value o1 r0 supply reserve0) :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.binary .le (.var "liq0") (.var "liq1")) = .ok (.bool false) := by
  exact amm4EvalNatLe_false amm4MintEvalLiq0Local amm4MintEvalLiq1Local hgt

def amm4MintAfterLiquidityStore (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) : Store :=
  (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1).insert
    "liquidity" (.int (Int.ofNat liquidity))

theorem amm4MintSourceSelect0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hle : amm4MintLiq0Value o1 r0 supply reserve0 ≤
      amm4MintLiq1Value o2 r1 supply1 reserve1) :
    ExecBlock config
      { contract := contract, locals :=
        (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.ite (.binary .le (.var "liq0") (.var "liq1"))
        [.letDecl "liquidity" (some uint256) (.var "liq0")]
        [.letDecl "liquidity" (some uint256) (.var "liq1")]]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (amm4MintLiq0Value o1 r0 supply reserve0)) } evm) := by
  have hcond := amm4MintEvalLiqSelect0 (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1) hle
  have hval := amm4MintEvalLiq0Local (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
  have hthen : ExecBlock config
      { contract := contract, locals :=
        (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.letDecl "liquidity" (some uint256) (.var "liq0")]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (amm4MintLiq0Value o1 r0 supply reserve0)) } evm) := by
    simpa only [amm4MintAfterLiquidityStore] using
      (amm4LetDeclOne (ty := some uint256) (name := "liquidity") hval)
  exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil

theorem amm4MintSourceSelect1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hgt : amm4MintLiq1Value o2 r1 supply1 reserve1 <
      amm4MintLiq0Value o1 r0 supply reserve0) :
    ExecBlock config
      { contract := contract, locals :=
        (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.ite (.binary .le (.var "liq0") (.var "liq1"))
        [.letDecl "liquidity" (some uint256) (.var "liq0")]
        [.letDecl "liquidity" (some uint256) (.var "liq1")]]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (amm4MintLiq1Value o2 r1 supply1 reserve1)) } evm) := by
  have hcond := amm4MintEvalLiqSelect1 (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1) hgt
  have hval := amm4MintEvalLiq1Local (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
  have helse : ExecBlock config
      { contract := contract, locals :=
        (amm4MintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.letDecl "liquidity" (some uint256) (.var "liq1")]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (amm4MintLiq1Value o2 r1 supply1 reserve1)) } evm) := by
    simpa only [amm4MintAfterLiquidityStore] using
      (amm4LetDeclOne (ty := some uint256) (name := "liquidity") hval)
  exact ExecBlock.consNormal (ExecStmt.iteFalse hcond helse) ExecBlock.nil

theorem amm4MintEvalLiquidityLocal {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.var "liquidity") = .ok (.int (Int.ofNat liquidity)) := by
  simp [amm4MintAfterLiquidityStore, evalExpr?, EvalResult.ofOption]

def amm4MintSourcePrefixSelected : List Stmt :=
  amm4MintSourcePrefixLiq1Numerator ++
    checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref) ++
    [.ite (.binary .le (.var "liq0") (.var "liq1"))
      [.letDecl "liquidity" (some uint256) (.var "liq0")]
      [.letDecl "liquidity" (some uint256) (.var "liq1")]]

theorem amm4MintSourceLiquidityNonzero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixSelected
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hnonzero : 0 < liquidity) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixSelected ++
        [.require (.binary .ne (.var "liquidity") (.intLit 0))])
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2) := by
  have hguard := amm4EvalNatNeZero_true
    (amm4MintEvalLiquidityLocal (evm := evm2) (I := I)
      (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
      (supply := supply) (reserve0 := reserve0)
      (supply1 := supply1) (reserve1 := reserve1)
      (liquidity := liquidity)) hnonzero
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.require (.binary .ne (.var "liquidity") (.intLit 0))]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4MintSourceLiquidityZero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixSelected
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hzero : liquidity = 0) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  subst liquidity
  have hval := amm4MintEvalLiquidityLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := 0)
  have hguard := amm4EvalNatNeZero_false hval
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 0) }
      evm2 (mintTransition.body.drop 13) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [amm4MintSourcePrefixSelected, amm4MintSourcePrefixLiq1Numerator,
      mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm4
