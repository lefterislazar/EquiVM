import Benchmarks.ActAmm4.MintSourceStores

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4MintRecipientRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (amm4MintToWord I).toNat))] }

def amm4MintRecipientSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (amm4MintToWord I).toNat))

theorem amm4MintRecipientSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (amm4MintToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (amm4MintToWord I) = amm4MintRecipientSlot I := by
  unfold amm4MintRecipientSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem amm4MintAfterLiquidityStore_to (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) :
    (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
      liquidity).get? "to" = some (amm4MintToValue I) := by
  unfold amm4MintAfterLiquidityStore amm4MintAfterLiq1Store
    amm4MintAfterLiq1NumeratorStore amm4MintAfterLiq0Store
    amm4MintAfterLiq0NumeratorStore amm4MintAfterAmount1Store
    amm4MintAfterAmount0Store amm4MintAfterBalance1Store
    amm4MintAfterBalance0Store
  rw [store_get_ne _ (k := "liquidity") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq1") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq1Numerator") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq0") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq0Numerator") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "amount1") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "amount0") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "balance1") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "balance0") (a := "to") _ (by decide)]
  simp [amm4MintStore]

theorem amm4MintAfterLiquidityStore_balanceOf_none (I : ExecutionEnv)
    (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) :
    (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
      liquidity).get? "balanceOf" = none := by
  simp [amm4MintAfterLiquidityStore, amm4MintAfterLiq1Store,
    amm4MintAfterLiq1NumeratorStore, amm4MintAfterLiq0Store,
    amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
    amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
    amm4MintAfterBalance0Store, amm4MintStore]

theorem amm4MintEvalRecipientRef {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalStorageRef config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (balanceOfRef (.var "to")) = .ok (amm4MintRecipientRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4MintRecipientRef, amm4MintToValue,
    amm4MintAfterLiquidityStore_to]

theorem amm4MintEvalRecipientBalance {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.storage (balanceOfRef (.var "to"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (amm4MintRecipientSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }) (evm := evm)
    (slot := balanceOfRef (.var "to"))
    (er := amm4MintRecipientRef I)
    (t := .int uint256Int) (loc := wordLoc (amm4MintRecipientSlot I))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (amm4MintRecipientSlot I)).toNat))
    (amm4MintAfterLiquidityStore_balanceOf_none I o1 o2
      r0 r1 supply reserve0 supply1 reserve1 liquidity)
    amm4MintEvalRecipientRef
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4MintRecipientRef, uint256St, storageTypeStep?])
    (by rfl)
    (by simpa using amm4StorageLocLoad_uint256 evm (amm4MintRecipientSlot I))

theorem amm4MintEvalRecipientAdd {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (amm4MintRecipientSlot I)).toNat + liquidity < UInt256.size) :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (amm4MintRecipientSlot I)).toNat + liquidity))) := by
  exact amm4EvalCheckedAdd_ok amm4MintEvalRecipientBalance
    amm4MintEvalLiquidityLocal hfit

theorem amm4MintEvalRecipientAdd_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (amm4MintRecipientSlot I)).toNat + liquidity) :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")) =
      .revert := by
  exact amm4EvalCheckedAdd_revert amm4MintEvalRecipientBalance
    amm4MintEvalLiquidityLocal hover

def amm4MintNewRecipientWord (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Nat) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (amm4MintRecipientSlot I)).toNat + liquidity)

def amm4MintAfterRecipient (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Nat) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (amm4MintRecipientSlot I) (amm4MintNewRecipientWord evm I liquidity)

theorem amm4MintAssignRecipient {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (amm4MintRecipientSlot I)).toNat + liquidity < UInt256.size) :
    assignStorageRef? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (amm4MintRecipientSlot I)).toNat + liquidity))) =
      .ok ({ contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) },
        amm4MintAfterRecipient evm I liquidity) := by
  have hword : (amm4MintNewRecipientWord evm I liquidity).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (amm4MintRecipientSlot I)).toNat + liquidity := by
    exact ulit_toNat' _ hfit
  have hstore : storageLocStore evm (wordLoc (amm4MintRecipientSlot I))
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (amm4MintRecipientSlot I)).toNat + liquidity))) =
      some (amm4MintAfterRecipient evm I liquidity) := by
    simpa [amm4MintAfterRecipient, hword] using
      amm4StorageLocStore_uint256 evm (amm4MintRecipientSlot I)
        (amm4MintNewRecipientWord evm I liquidity)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }) (evm := evm)
    (evm' := amm4MintAfterRecipient evm I liquidity)
    (slot := balanceOfRef (.var "to"))
    (er := amm4MintRecipientRef I) (ty := .elem (.int uint256Int))
    (loc := wordLoc (amm4MintRecipientSlot I))
    (n := Int.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (amm4MintRecipientSlot I)).toNat + liquidity))
    (amm4MintAfterLiquidityStore_balanceOf_none I o1 o2
      r0 r1 supply reserve0 supply1 reserve1 liquidity)
    amm4MintEvalRecipientRef
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4MintRecipientRef, uint256St, storageTypeStep?])
    (by rfl) hstore

def amm4MintSourcePrefixSupplyStored : List Stmt :=
  amm4MintSourcePrefixGuarded ++
    [.assign .storage totalSupplyRef
      (checkedAdd (.storage totalSupplyRef) (.var "liquidity"))]

theorem amm4MintSourceRecipientOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixSupplyStored
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
      (amm4MintRecipientSlot I)).toNat + liquidity < UInt256.size) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixSupplyStored ++
        [.assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity"))])
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterRecipient evm2 I liquidity)) := by
  have heval := amm4MintEvalRecipientAdd (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have hassign := amm4MintAssignRecipient (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.assign .storage (balanceOfRef (.var "to"))
        (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity"))]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterRecipient evm2 I liquidity)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4MintSourceRecipientOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixSupplyStored
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (amm4MintRecipientSlot I)).toNat + liquidity) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body .reverted := by
  have heval := amm4MintEvalRecipientAdd_revert (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hover
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 (mintTransition.body.drop 15) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body .reverted := by
    simpa [amm4MintSourcePrefixSupplyStored, amm4MintSourcePrefixGuarded,
      amm4MintSourcePrefixSelected, amm4MintSourcePrefixLiq1Numerator,
      mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm4
