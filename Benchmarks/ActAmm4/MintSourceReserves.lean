import Benchmarks.ActAmm4.MintSourceRecipient

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4MintAfterLiquidityStore_balance0 (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) :
    (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
      liquidity).get? "balance0" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) := by
  unfold amm4MintAfterLiquidityStore amm4MintAfterLiq1Store
    amm4MintAfterLiq1NumeratorStore amm4MintAfterLiq0Store
    amm4MintAfterLiq0NumeratorStore amm4MintAfterAmount1Store
    amm4MintAfterAmount0Store amm4MintAfterBalance1Store
  rw [store_get_ne _ (k := "liquidity") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "liq1") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "liq1Numerator") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "liq0") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "liq0Numerator") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "amount1") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "amount0") (a := "balance0") _ (by decide)]
  rw [store_get_ne _ (k := "balance1") (a := "balance0") _ (by decide)]
  simp [amm4MintAfterBalance0Store]

theorem amm4MintAfterLiquidityStore_balance1 (I : ExecutionEnv) (o1 o2 : ByteArray)
    (r0 r1 supply reserve0 supply1 reserve1 : UInt256) (liquidity : Nat) :
    (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
      liquidity).get? "balance1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
  unfold amm4MintAfterLiquidityStore amm4MintAfterLiq1Store
    amm4MintAfterLiq1NumeratorStore amm4MintAfterLiq0Store
    amm4MintAfterLiq0NumeratorStore amm4MintAfterAmount1Store
    amm4MintAfterAmount0Store
  rw [store_get_ne _ (k := "liquidity") (a := "balance1") _ (by decide)]
  rw [store_get_ne _ (k := "liq1") (a := "balance1") _ (by decide)]
  rw [store_get_ne _ (k := "liq1Numerator") (a := "balance1") _ (by decide)]
  rw [store_get_ne _ (k := "liq0") (a := "balance1") _ (by decide)]
  rw [store_get_ne _ (k := "liq0Numerator") (a := "balance1") _ (by decide)]
  rw [store_get_ne _ (k := "amount1") (a := "balance1") _ (by decide)]
  rw [store_get_ne _ (k := "amount0") (a := "balance1") _ (by decide)]
  simp [amm4MintAfterBalance1Store]

theorem amm4MintEvalBalance0AfterLiquidity {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) := by
  have hget := amm4MintAfterLiquidityStore_balance0 I o1 o2 r0 r1 supply
    reserve0 supply1 reserve1 liquidity
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem amm4MintEvalBalance1AfterLiquidity {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} :
    evalExpr? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) := by
  have hget := amm4MintAfterLiquidityStore_balance1 I o1 o2 r0 r1 supply
    reserve0 supply1 reserve1 liquidity
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

def amm4MintReserve0Word (o1 : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (o1.extract 0 32))

def amm4MintAfterReserve0 (evm : EVM.State) (o1 : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (amm4MintReserve0Word o1)

theorem amm4MintAssignReserve0 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} (hlo : 32 ≤ o1.size) :
    assignStorageRef? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) =
      .ok ({ contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) },
        amm4MintAfterReserve0 evm o1) := by
  have hword : (amm4MintReserve0Word o1).toNat =
      fromByteArrayBigEndian (o1.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm (wordLoc ⟨5⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))) =
      some (amm4MintAfterReserve0 evm o1) := by
    simpa [amm4MintAfterReserve0, hword] using
      amm4StorageLocStore_uint256 evm ⟨5⟩ (amm4MintReserve0Word o1)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }) (evm := evm) (evm' := amm4MintAfterReserve0 evm o1)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (o1.extract 0 32)))
    (by simp [amm4MintAfterLiquidityStore, amm4MintAfterLiq1Store,
      amm4MintAfterLiq1NumeratorStore, amm4MintAfterLiq0Store,
      amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore, reserve0Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem amm4MintSourceReserve0Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixSupplyStored ++
        [.assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity"))])
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hlo : 32 ≤ o1.size) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixSupplyStored ++
        [.assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")),
         .assign .storage reserve0Ref (.var "balance0")])
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterReserve0 evm2 o1)) := by
  have heval := amm4MintEvalBalance0AfterLiquidity (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity)
  have hassign := amm4MintAssignReserve0 (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hlo
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.assign .storage reserve0Ref (.var "balance0")]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterReserve0 evm2 o1)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  simpa only [List.append_assoc] using (execBlock_append hprefix htail)

def amm4MintReserve1Word (o2 : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32))

def amm4MintAfterReserve1 (evm : EVM.State) (o2 : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (amm4MintReserve1Word o2)

theorem amm4MintAssignReserve1 {evm : EVM.State} {I : ExecutionEnv}
    {o1 o2 : ByteArray} {r0 r1 supply reserve0 supply1 reserve1 : UInt256}
    {liquidity : Nat} (hlo : 32 ≤ o2.size) :
    assignStorageRef? config { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }
      evm .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) =
      .ok ({ contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) },
        amm4MintAfterReserve1 evm o2) := by
  have hword : (amm4MintReserve1Word o2).toNat =
      fromByteArrayBigEndian (o2.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm (wordLoc ⟨6⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))) =
      some (amm4MintAfterReserve1 evm o2) := by
    simpa [amm4MintAfterReserve1, hword] using
      amm4StorageLocStore_uint256 evm ⟨6⟩ (amm4MintReserve1Word o2)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      (amm4MintAfterLiquidityStore I o1 o2 r0 r1 supply reserve0 supply1 reserve1
        liquidity) }) (evm := evm) (evm' := amm4MintAfterReserve1 evm o2)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (o2.extract 0 32)))
    (by simp [amm4MintAfterLiquidityStore, amm4MintAfterLiq1Store,
      amm4MintAfterLiq1NumeratorStore, amm4MintAfterLiq0Store,
      amm4MintAfterLiq0NumeratorStore, amm4MintAfterAmount1Store,
      amm4MintAfterAmount0Store, amm4MintAfterBalance1Store,
      amm4MintAfterBalance0Store, amm4MintStore, reserve1Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

def amm4MintSourcePrefixReserve0Stored : List Stmt :=
  amm4MintSourcePrefixSupplyStored ++
    [.assign .storage (balanceOfRef (.var "to"))
      (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")),
     .assign .storage reserve0Ref (.var "balance0")]

theorem amm4MintSourceReserve1Ok {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixReserve0Stored
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2))
    (hlo : 32 ≤ o2.size) :
    ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      (amm4MintSourcePrefixReserve0Stored ++
        [.assign .storage reserve1Ref (.var "balance1")])
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterReserve1 evm2 o2)) := by
  have heval := amm4MintEvalBalance1AfterLiquidity (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity)
  have hassign := amm4MintAssignReserve1 (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity) hlo
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.assign .storage reserve1Ref (.var "balance1")]
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1
        o2 r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        (amm4MintAfterReserve1 evm2 o2)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

def amm4MintSourcePrefixAllStored : List Stmt :=
  amm4MintSourcePrefixReserve0Stored ++
    [.assign .storage reserve1Ref (.var "balance1")]

theorem amm4MintSourceReturn {evm evm2 : EVM.State}
    {I : ExecutionEnv} {o1 o2 : ByteArray}
    {r0 r1 supply reserve0 supply1 reserve1 : UInt256} {liquidity : Nat}
    (hprefix : ExecBlock config { contract := contract, locals := amm4MintStore I } evm
      amm4MintSourcePrefixAllStored
      (.ok { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) } evm2)) :
    ExecTransitionBody config contract evm (amm4MintStore I)
      mintTransition.body
      (.returned { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        evm2 (some [(.int (Int.ofNat liquidity))])) := by
  have hval := amm4MintEvalLiquidityLocal (evm := evm2) (I := I)
    (o1 := o1) (o2 := o2) (r0 := r0) (r1 := r1)
    (supply := supply) (reserve0 := reserve0)
    (supply1 := supply1) (reserve1 := reserve1)
    (liquidity := liquidity)
  have htail : ExecBlock config
      { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
      evm2 [.return [(.var "liquidity")]]
      (.returned { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        evm2 (some [(.int (Int.ofNat liquidity))])) := by
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hval))
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config { contract := contract, locals := amm4MintStore I }
      evm mintTransition.body
      (.returned { contract := contract, locals := (amm4MintAfterLiquidityStore I o1 o2
        r0 r1 supply reserve0 supply1 reserve1 liquidity) }
        evm2 (some [(.int (Int.ofNat liquidity))])) := by
    simpa [amm4MintSourcePrefixAllStored, amm4MintSourcePrefixReserve0Stored,
      amm4MintSourcePrefixSupplyStored, amm4MintSourcePrefixGuarded,
      amm4MintSourcePrefixSelected, amm4MintSourcePrefixLiq1Numerator,
      mintTransition, nonpayable, tokenBalance, checkedDivInto,
      List.cons_append, List.nil_append] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRet hbody

end Benchmarks.ActAmm4
