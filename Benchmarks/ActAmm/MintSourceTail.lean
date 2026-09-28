import Benchmarks.ActAmm.MintSourceArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def ammMintLiq0Value (o1 : ByteArray) (r0 supply reserve0 : UInt256) : Nat :=
  ((fromByteArrayBigEndian (o1.extract 0 32) - r0.toNat) * supply.toNat) /
    reserve0.toNat

def ammMintLiq1Value (o2 : ByteArray) (r1 supply1 reserve1 : UInt256) : Nat :=
  ((fromByteArrayBigEndian (o2.extract 0 32) - r1.toNat) * supply1.toNat) /
    reserve1.toNat

theorem ammMintEvalLiq0Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.var "liq0") =
      .ok (.int (Int.ofNat (ammMintLiq0Value o1 r0 supply reserve0))) := by
  have hget : (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1).get?
      "liq0" = some (.int (Int.ofNat (ammMintLiq0Value o1 r0 supply reserve0))) := by
    unfold ammMintAfterLiq1Store ammMintAfterLiq1NumeratorStore
    rw [store_get_ne _ (k := "liq1") (a := "liq0") _ (by decide)]
    rw [store_get_ne _ (k := "liq1Numerator") (a := "liq0") _ (by decide)]
    simp [ammMintAfterLiq0Store, ammMintLiq0Value]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammMintEvalLiq1Local {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.var "liq1") =
      .ok (.int (Int.ofNat (ammMintLiq1Value o2 r1 supply1 reserve1))) := by
  simp [ammMintAfterLiq1Store, ammMintLiq1Value, evalExpr?, EvalResult.ofOption]

theorem ammMintEvalLiqSelect0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hle : ammMintLiq0Value o1 r0 supply reserve0 ≤
      ammMintLiq1Value o2 r1 supply1 reserve1) :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.binary .le (.var "liq0") (.var "liq1")) = .ok (.bool true) := by
  exact ammEvalNatLe_true ammMintEvalLiq0Local ammMintEvalLiq1Local hle

theorem ammMintEvalLiqSelect1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hgt : ammMintLiq1Value o2 r1 supply1 reserve1 <
      ammMintLiq0Value o1 r0 supply reserve0) :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm (.binary .le (.var "liq0") (.var "liq1")) = .ok (.bool false) := by
  exact ammEvalNatLe_false ammMintEvalLiq0Local ammMintEvalLiq1Local hgt

def ammMintAfterLiquidityStore (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) : Store :=
  (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1).insert
    "liquidity" (.int (Int.ofNat liquidity))

theorem ammMintSourceSelect0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hle : ammMintLiq0Value o1 r0 supply reserve0 ≤
      ammMintLiq1Value o2 r1 supply1 reserve1) :
    ExecBlock config
      { contract := contract, locals :=
        (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.ite (.binary .le (.var "liq0") (.var "liq1"))
        [.letDecl "liquidity" (some uint256) (.var "liq0")]
        [.letDecl "liquidity" (some uint256) (.var "liq1")]]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (ammMintLiq0Value o1 r0 supply reserve0)) } evm) := by
  have hcond := ammMintEvalLiqSelect0 (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1) hle
  have hval := ammMintEvalLiq0Local (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
  have hthen : ExecBlock config
      { contract := contract, locals :=
        (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.letDecl "liquidity" (some uint256) (.var "liq0")]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (ammMintLiq0Value o1 r0 supply reserve0)) } evm) := by
    simpa only [ammMintAfterLiquidityStore] using
      (ammLetDeclOne (ty := some uint256) (name := "liquidity") hval)
  exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil

theorem ammMintSourceSelect1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    (hgt : ammMintLiq1Value o2 r1 supply1 reserve1 <
      ammMintLiq0Value o1 r0 supply reserve0) :
    ExecBlock config
      { contract := contract, locals :=
        (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.ite (.binary .le (.var "liq0") (.var "liq1"))
        [.letDecl "liquidity" (some uint256) (.var "liq0")]
        [.letDecl "liquidity" (some uint256) (.var "liq1")]]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (ammMintLiq1Value o2 r1 supply1 reserve1)) } evm) := by
  have hcond := ammMintEvalLiqSelect1 (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1) hgt
  have hval := ammMintEvalLiq1Local (evm := evm) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
  have helse : ExecBlock config
      { contract := contract, locals :=
        (ammMintAfterLiq1Store I o1 o2 r0 r1 supply reserve0 supply1 reserve1) }
      evm [.letDecl "liquidity" (some uint256) (.var "liq1")]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1
        (ammMintLiq1Value o2 r1 supply1 reserve1)) } evm) := by
    simpa only [ammMintAfterLiquidityStore] using
      (ammLetDeclOne (ty := some uint256) (name := "liquidity") hval)
  exact ExecBlock.consNormal (ExecStmt.iteFalse hcond helse) ExecBlock.nil

theorem ammMintEvalLiquidityLocal {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.var "liquidity") = .ok (.int (Int.ofNat liquidity)) := by
  simp [ammMintAfterLiquidityStore, evalExpr?, EvalResult.ofOption]

def ammMintSourcePrefixSelected : List Stmt :=
  ammMintSourcePrefixLiq1Numerator ++
    checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref) ++
    [.ite (.binary .le (.var "liq0") (.var "liq1"))
      [.letDecl "liquidity" (some uint256) (.var "liq0")]
      [.letDecl "liquidity" (some uint256) (.var "liq1")]]

theorem ammMintSourceLiquidityNonzero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixSelected
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hnonzero : 0 < liquidity) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (ammMintSourcePrefixSelected ++
        [.require (.binary .ne (.var "liquidity") (.intLit 0))])
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2) := by
  have hguard := ammEvalNatNeZero_true
    (ammMintEvalLiquidityLocal (evm := evm2) (I := I)
      (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
      (supply := supply) (reserve0 := reserve0)
      (supply1 := supply1) (reserve1 := reserve1)
      (liquidity := liquidity)) hnonzero
  have htail : ExecBlock config
      { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.require (.binary .ne (.var "liquidity") (.intLit 0))]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hguard) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem ammMintSourceLiquidityZero {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixSelected
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hzero : liquidity = 0) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  subst liquidity
  have hval := ammMintEvalLiquidityLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := 0)
  have hguard := ammEvalNatNeZero_false hval
  have htail : ExecBlock config
      { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 0) }
      evm2 (mintTransition.body.drop 13) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [ammMintSourcePrefixSelected, ammMintSourcePrefixLiq1Numerator,
      mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm
