import Benchmarks.ActAmm.MintSourceStores

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def ammMintRecipientRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf",
    steps := [.mindex (.address (AccountAddress.ofNat (ammMintToWord I).toNat))] }

def ammMintRecipientSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address (AccountAddress.ofNat (ammMintToWord I).toNat))

theorem ammMintRecipientSlot_eq_solc (I : ExecutionEnv)
    (hcanon : (ammMintToWord I).toNat < EVM.addressModulus) :
    solcMappingSlot ⟨1⟩ (ammMintToWord I) = ammMintRecipientSlot I := by
  unfold ammMintRecipientSlot balanceOfSlot mapSlot solcMappingSlot
  rw [keyValueToWord_address_of_canonical _ hcanon]

theorem ammMintAfterLiquidityStore_to (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) :
    (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
      liquidity).get? "to" = some (ammMintToValue I) := by
  unfold ammMintAfterLiquidityStore ammMintAfterLiq1Store
    ammMintAfterLiq1NumeratorStore ammMintAfterLiq0Store
    ammMintAfterLiq0NumeratorStore ammMintAfterAmount1Store
    ammMintAfterAmount0Store ammMintAfterBalance1Store
    ammMintAfterBalance0Store
  rw [store_get_ne _ (k := "liquidity") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq1") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq1Numerator") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq0") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "liq0Numerator") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "amount1") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "amount0") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "balance1") (a := "to") _ (by decide)]
  rw [store_get_ne _ (k := "balance0") (a := "to") _ (by decide)]
  simp [ammMintStore]

theorem ammMintAfterLiquidityStore_balanceOf_none (I : ExecutionEnv)
    (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) :
    (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
      liquidity).get? "balanceOf" = none := by
  simp [ammMintAfterLiquidityStore, ammMintAfterLiq1Store,
    ammMintAfterLiq1NumeratorStore, ammMintAfterLiq0Store,
    ammMintAfterLiq0NumeratorStore, ammMintAfterAmount1Store,
    ammMintAfterAmount0Store, ammMintAfterBalance1Store,
    ammMintAfterBalance0Store, ammMintStore]

theorem ammMintEvalRecipientRef {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalStorageRef config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (balanceOfRef (.var "to")) = .ok (ammMintRecipientRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammMintRecipientRef, ammMintToValue,
    ammMintAfterLiquidityStore_to]

theorem ammMintEvalRecipientBalance {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.storage (balanceOfRef (.var "to"))) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (ammMintRecipientSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }) (evm := evm)
    (slot := balanceOfRef (.var "to"))
    (er := ammMintRecipientRef I)
    (t := .int uint256Int) (loc := wordLoc (ammMintRecipientSlot I))
    (value := .int (Int.ofNat
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (ammMintRecipientSlot I)).toNat))
    (ammMintAfterLiquidityStore_balanceOf_none I o1 o2
      r0 r1 supply reserve0 supply1 reserve1 liquidity)
    ammMintEvalRecipientRef
    (by simp [storageTypeAt?, contract, storageDecls,
      ammMintRecipientRef, uint256St, storageTypeStep?])
    (by rfl)
    (by simpa using ammStorageLocLoad_uint256 evm (ammMintRecipientSlot I))

theorem ammMintEvalRecipientAdd {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (ammMintRecipientSlot I)).toNat + liquidity < UInt256.size) :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (ammMintRecipientSlot I)).toNat + liquidity))) := by
  exact ammEvalCheckedAdd_ok ammMintEvalRecipientBalance
    ammMintEvalLiquidityLocal hfit

theorem ammMintEvalRecipientAdd_revert {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (ammMintRecipientSlot I)).toNat + liquidity) :
    evalExpr? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")) =
      .revert := by
  exact ammEvalCheckedAdd_revert ammMintEvalRecipientBalance
    ammMintEvalLiquidityLocal hover

def ammMintNewRecipientWord (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Nat) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (ammMintRecipientSlot I)).toNat + liquidity)

def ammMintAfterRecipient (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Nat) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (ammMintRecipientSlot I) (ammMintNewRecipientWord evm I liquidity)

theorem ammMintAssignRecipient {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (ammMintRecipientSlot I)).toNat + liquidity < UInt256.size) :
    assignStorageRef? config { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm .storage (balanceOfRef (.var "to"))
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (ammMintRecipientSlot I)).toNat + liquidity))) =
      .ok ({ contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) },
        ammMintAfterRecipient evm I liquidity) := by
  have hword : (ammMintNewRecipientWord evm I liquidity).toNat =
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (ammMintRecipientSlot I)).toNat + liquidity := by
    exact ulit_toNat' _ hfit
  have hstore : storageLocStore evm (wordLoc (ammMintRecipientSlot I))
      (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (ammMintRecipientSlot I)).toNat + liquidity))) =
      some (ammMintAfterRecipient evm I liquidity) := by
    simpa [ammMintAfterRecipient, hword] using
      ammStorageLocStore_uint256 evm (ammMintRecipientSlot I)
        (ammMintNewRecipientWord evm I liquidity)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      (ammMintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }) (evm := evm)
    (evm' := ammMintAfterRecipient evm I liquidity)
    (slot := balanceOfRef (.var "to"))
    (er := ammMintRecipientRef I) (ty := .elem (.int uint256Int))
    (loc := wordLoc (ammMintRecipientSlot I))
    (n := Int.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (ammMintRecipientSlot I)).toNat + liquidity))
    (ammMintAfterLiquidityStore_balanceOf_none I o1 o2
      r0 r1 supply reserve0 supply1 reserve1 liquidity)
    ammMintEvalRecipientRef
    (by simp [storageTypeAt?, contract, storageDecls,
      ammMintRecipientRef, uint256St, storageTypeStep?])
    (by rfl) hstore

def ammMintSourcePrefixSupplyStored : List Stmt :=
  ammMintSourcePrefixGuarded ++
    [.assign .storage totalSupplyRef
      (checkedAdd (.storage totalSupplyRef) (.var "liquidity"))]

theorem ammMintSourceRecipientOk {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixSupplyStored
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
      (ammMintRecipientSlot I)).toNat + liquidity < UInt256.size) :
    ExecBlock config { contract := contract, locals := ammMintStore I } evm
      (ammMintSourcePrefixSupplyStored ++
        [.assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity"))])
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (ammMintAfterRecipient evm2 I liquidity)) := by
  have heval := ammMintEvalRecipientAdd (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have hassign := ammMintAssignRecipient (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hfit
  have htail : ExecBlock config
      { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.assign .storage (balanceOfRef (.var "to"))
        (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity"))]
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (ammMintAfterRecipient evm2 I liquidity)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem ammMintSourceRecipientOverflow {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := ammMintStore I } evm
      ammMintSourcePrefixSupplyStored
      (.ok { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner
        (ammMintRecipientSlot I)).toNat + liquidity) :
    ExecTransitionBody config contract evm (ammMintStore I)
      mintTransition.body .reverted := by
  have heval := ammMintEvalRecipientAdd_revert (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hover
  have htail : ExecBlock config
      { contract := contract, locals := (ammMintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 (mintTransition.body.drop 15) .reverted := by
    simp only [mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := ammMintStore I }
      evm mintTransition.body .reverted := by
    simpa [ammMintSourcePrefixSupplyStored, ammMintSourcePrefixGuarded,
      ammMintSourcePrefixSelected, ammMintSourcePrefixLiq1Numerator,
      mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

end Benchmarks.ActAmm
