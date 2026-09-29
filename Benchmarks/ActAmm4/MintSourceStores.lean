import Benchmarks.ActAmm4.MintSourceTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintEvalSupplyAfterLiquidity {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.storage totalSupplyRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply amm4MintEvalSupply
  simp [amm4MintAfterLiquidityStore, amm4MintAfterLiq1Store,
    amm4MintAfterLiq1NumeratorStore, amm4MintAfterLiq0Store,
    amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
    amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
    amm4MintAfterBalance0Store, amm4MintStore]

theorem amm4MintEvalSupplyAdd {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
      liquidity < UInt256.size) :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage totalSupplyRef) (.var "liquidity")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
          liquidity))) := by
  exact amm4EvalCheckedAdd_ok amm4MintEvalSupplyAfterLiquidity
    amm4MintEvalLiquidityLocal hfit

theorem amm4MintEvalSupplyAdd_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat + liquidity) :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage totalSupplyRef) (.var "liquidity")) = .revert := by
  exact amm4EvalCheckedAdd_revert amm4MintEvalSupplyAfterLiquidity
    amm4MintEvalLiquidityLocal hover

def amm4MintNewSupplyWord (evm : EVM.State) (liquidity : Nat) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat + liquidity)

def amm4MintAfterSupply (evm : EVM.State) (liquidity : Nat) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (amm4MintNewSupplyWord evm liquidity)

theorem amm4MintAssignSupply {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
      liquidity < UInt256.size) :
    assignStorageRef? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm .storage totalSupplyRef
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
          liquidity))) =
      .ok ({ contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) },
        amm4MintAfterSupply evm liquidity) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (hbase := by simp [amm4MintAfterLiquidityStore, amm4MintAfterLiq1Store,
      amm4MintAfterLiq1NumeratorStore, amm4MintAfterLiq0Store,
      amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore, totalSupplyRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  have hword : (amm4MintNewSupplyWord evm liquidity).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
        liquidity := by
    exact ulit_toNat' _ hfit
  simpa [amm4MintAfterSupply, hword] using
    amm4StorageLocStore_uint256 evm ⟨0⟩ (amm4MintNewSupplyWord evm liquidity)

def amm4MintSourcePrefixGuarded : List Stmt :=
  amm4MintSourcePrefixSelected ++
    [.require (.binary .ne (.var "liquidity") (.intLit 0))]

theorem amm4MintSourceSupplyOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixGuarded
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat +
      liquidity < UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixGuarded ++
        [.assign .storage totalSupplyRef
          (checkedAdd (.storage totalSupplyRef) (.var "liquidity"))])
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterSupply evm2 liquidity)) := by
  have heval := amm4MintEvalSupplyAdd (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have hassign := amm4MintAssignSupply (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.assign .storage totalSupplyRef
        (checkedAdd (.storage totalSupplyRef) (.var "liquidity"))]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterSupply evm2 liquidity)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4MintSourceSupplyOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixGuarded
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat + liquidity) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have heval := amm4MintEvalSupplyAdd_revert (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hover
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 (mintTransition.body.drop 14) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [amm4MintSourcePrefixGuarded, amm4MintSourcePrefixSelected,
      amm4MintSourcePrefixLiq1Numerator, mintTransition, nonpayable,
      tokenBalance, checkedDivInto, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm4
