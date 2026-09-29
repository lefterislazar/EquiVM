import Benchmarks.ActAmm4.SwapSourceProducts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapEvalBalance0AfterProducts
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out0.extract 0 32)))) := by
  simp [evalExpr?, amm4SwapAfterOldProductStore,
    amm4SwapAfterNewProductStore, amm4SwapInputStore,
    amm4SwapAfterAmount1InStore, amm4SwapAfterReserve1Store,
    amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
    amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
    EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem amm4SwapEvalBalance1AfterProducts
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out1.extract 0 32)))) := by
  simp [evalExpr?, amm4SwapAfterOldProductStore,
    amm4SwapAfterNewProductStore, amm4SwapInputStore,
    amm4SwapAfterAmount1InStore, amm4SwapAfterReserve1Store,
    amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
    amm4SwapAfterBalance1Store,
    EvalResult.ofOption, Std.HashMap.getElem_insert]

def amm4SwapReserve0Word (out0 : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out0.extract 0 32))

def amm4SwapAfterReserve0 (evm : EVM.State) (out0 : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (amm4SwapReserve0Word out0)

theorem amm4SwapAssignReserve0
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat}
    (hlo : 32 ≤ out0.size) :
    assignStorageRef? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out0.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 },
        amm4SwapAfterReserve0 evm out0) := by
  have hword : (amm4SwapReserve0Word out0).toNat =
      fromByteArrayBigEndian (out0.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm (wordLoc ⟨5⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out0.extract 0 32)))) =
      some (amm4SwapAfterReserve0 evm out0) := by
    simpa [amm4SwapAfterReserve0, hword] using
      amm4StorageLocStore_uint256 evm ⟨5⟩ (amm4SwapReserve0Word out0)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 })
    (evm := evm) (evm' := amm4SwapAfterReserve0 evm out0)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out0.extract 0 32)))
    (by simp [amm4SwapAfterOldProductStore,
      amm4SwapAfterNewProductStore, amm4SwapInputStore,
      amm4SwapAfterAmount1InStore, amm4SwapAfterReserve1Store,
      amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
      amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store, amm4SwapAfterTransfer0Store,
      amm4SwapStore, reserve0Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

def amm4SwapSourcePrefixReserve0Stored : List Stmt :=
  amm4SwapSourcePrefixKGuard ++
    [.assign .storage reserve0Ref (.var "balance0")]

theorem amm4SwapSourceReserve0Stored
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixKGuard
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4))
    (hlo : 32 ≤ out0.size) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0Stored
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve0 evm4 out0)) := by
  have heval := amm4SwapEvalBalance0AfterProducts
    (evm := evm4) (evm4 := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) (a0 := a0) (a1 := a1)
  have hassign := amm4SwapAssignReserve0
    (evm := evm4) (evm4 := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) (a0 := a0) (a1 := a1) hlo
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 [.assign .storage reserve0Ref (.var "balance0")]
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve0 evm4 out0)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

def amm4SwapReserve1Word (out1 : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))

def amm4SwapAfterReserve1 (evm : EVM.State) (out1 : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (amm4SwapReserve1Word out1)

theorem amm4SwapAssignReserve1
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat}
    (hlo : 32 ≤ out1.size) :
    assignStorageRef? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 },
        amm4SwapAfterReserve1 evm out1) := by
  have hword : (amm4SwapReserve1Word out1).toNat =
      fromByteArrayBigEndian (out1.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hstore : storageLocStore evm (wordLoc ⟨6⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))) =
      some (amm4SwapAfterReserve1 evm out1) := by
    simpa [amm4SwapAfterReserve1, hword] using
      amm4StorageLocStore_uint256 evm ⟨6⟩ (amm4SwapReserve1Word out1)
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 })
    (evm := evm) (evm' := amm4SwapAfterReserve1 evm out1)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out1.extract 0 32)))
    (by simp [amm4SwapAfterOldProductStore,
      amm4SwapAfterNewProductStore, amm4SwapInputStore,
      amm4SwapAfterAmount1InStore, amm4SwapAfterReserve1Store,
      amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
      amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store, amm4SwapAfterTransfer0Store,
      amm4SwapStore, reserve1Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem amm4SwapSourceReserve1Stored
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0Stored
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve0 evm4 out0)))
    (hlo : 32 ≤ out1.size) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm (amm4SwapSourcePrefixReserve0Stored ++
        [.assign .storage reserve1Ref (.var "balance1")])
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve1 (amm4SwapAfterReserve0 evm4 out0) out1)) := by
  have heval := amm4SwapEvalBalance1AfterProducts
    (evm := amm4SwapAfterReserve0 evm4 out0) (evm4 := evm4)
    (I := I) (b0 := b0) (b1 := b1) (out0 := out0) (out1 := out1)
    (a0 := a0) (a1 := a1)
  have hassign := amm4SwapAssignReserve1
    (evm := amm4SwapAfterReserve0 evm4 out0) (evm4 := evm4)
    (I := I) (b0 := b0) (b1 := b1) (out0 := out0) (out1 := out1)
    (a0 := a0) (a1 := a1) hlo
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      (amm4SwapAfterReserve0 evm4 out0)
      [.assign .storage reserve1Ref (.var "balance1")]
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve1 (amm4SwapAfterReserve0 evm4 out0) out1)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4SwapSourceSuccess
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0Stored
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve0 evm4 out0)))
    (hlo : 32 ≤ out1.size) :
    ExecTransitionBody config contract evm (amm4SwapStore I)
      swapTransition.body
      (.returned { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve1 (amm4SwapAfterReserve0 evm4 out0) out1)
        none) := by
  have hblock := amm4SwapSourceReserve1Stored I b0 b1 out0 out1 a0 a1
    hprefix hlo
  have hbody : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm swapTransition.body
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
        (amm4SwapAfterReserve1 (amm4SwapAfterReserve0 evm4 out0) out1)) := by
    simpa [amm4SwapSourcePrefixReserve0Stored,
      amm4SwapSourcePrefixKGuard, amm4SwapSourcePrefixOldProduct,
      amm4SwapSourcePrefixNewProduct, amm4SwapSourcePrefixInputGuard,
      amm4SwapSourcePrefixAmount1In, amm4SwapSourcePrefixReserve1,
      amm4SwapSourcePrefixAmount0In, amm4SwapSourcePrefixReserve0,
      amm4SwapSourcePrefixBalance1, amm4SwapSourcePrefixBalance0,
      amm4SwapSourcePrefixTransfer1, amm4SwapSourcePrefixTransfer0,
      amm4SwapSourcePrefixRecipient, swapTransition, nonpayable,
      tokenTransfer, tokenBalance, List.cons_append, List.nil_append]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hbody

end Benchmarks.ActAmm4
