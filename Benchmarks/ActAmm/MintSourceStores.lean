import Benchmarks.ActAmm.MintSourceTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammMintEvalSupplyAfterLiquidity {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.storage totalSupplyRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  apply ammMintEvalSupply
  simp [ammMintAfterLiquidityStore, ammMintAfterLiq1Store,
    ammMintAfterLiq1NumeratorStore, ammMintAfterLiq0Store,
    ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
    ammMintAfterAmount0Store, ammMintAfterBalance1Store,
    ammMintAfterBalance0Store, ammMintStore]

theorem ammMintEvalSupplyAdd {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
      liquidity < UInt256.size) :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage totalSupplyRef) (.var "liquidity")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
          liquidity))) := by
  exact ammEvalCheckedAdd_ok ammMintEvalSupplyAfterLiquidity
    ammMintEvalLiquidityLocal hfit

theorem ammMintEvalSupplyAdd_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat + liquidity) :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage totalSupplyRef) (.var "liquidity")) = .revert := by
  exact ammEvalCheckedAdd_revert ammMintEvalSupplyAfterLiquidity
    ammMintEvalLiquidityLocal hover

def ammMintNewSupplyWord (evm : EVM.State) (liquidity : Nat) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat + liquidity)

def ammMintAfterSupply (evm : EVM.State) (liquidity : Nat) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (ammMintNewSupplyWord evm liquidity)

theorem ammMintAssignSupply {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
      liquidity < UInt256.size) :
    assignStorageRef? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm .storage totalSupplyRef
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
          liquidity))) =
      .ok ({ contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) },
        ammMintAfterSupply evm liquidity) := by
  apply assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (hbase := by simp [ammMintAfterLiquidityStore, ammMintAfterLiq1Store,
      ammMintAfterLiq1NumeratorStore, ammMintAfterLiq0Store,
      ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
      ammMintAfterAmount0Store, ammMintAfterBalance1Store,
      ammMintAfterBalance0Store, ammMintStore, totalSupplyRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  have hword : (ammMintNewSupplyWord evm liquidity).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat +
        liquidity := by
    exact ulit_toNat' _ hfit
  simpa [ammMintAfterSupply, hword] using
    ammStorageLocStore_uint256 evm ⟨0⟩ (ammMintNewSupplyWord evm liquidity)

def ammMintSourcePrefixGuarded : List Stmt :=
  ammMintSourcePrefixSelected ++
    [.require (.binary .ne (.var "liquidity") (.intLit 0))]

theorem ammMintSourceSupplyOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixGuarded
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat +
      liquidity < UInt256.size) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (ammMintSourcePrefixGuarded ++
        [.assign .storage totalSupplyRef
          (checkedAdd (.storage totalSupplyRef) (.var "liquidity"))])
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (ammMintAfterSupply evm2 liquidity)) := by
  have heval := ammMintEvalSupplyAdd (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have hassign := ammMintAssignSupply (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have htail : ExecBlock config
      { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.assign .storage totalSupplyRef
        (checkedAdd (.storage totalSupplyRef) (.var "liquidity"))]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (ammMintAfterSupply evm2 liquidity)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem ammMintSourceSupplyOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixGuarded
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨0⟩).toNat + liquidity) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have heval := ammMintEvalSupplyAdd_revert (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hover
  have htail : ExecBlock config
      { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 (mintTransition.body.drop 14) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [ammMintSourcePrefixGuarded, ammMintSourcePrefixSelected,
      ammMintSourcePrefixLiq1Numerator, mintTransition, nonpayable,
      tokenBalance, checkedDivInto, List.cons_append, List.nil_append,
      List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm
