import Benchmarks.ActAmm4.SwapSourceArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

def amm4SwapInputStore (evm4 : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (a0 a1 : Nat) : Store :=
  amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 a0 a1

theorem amm4SwapEvalBalance0AfterInputs
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out0.extract 0 32)))) := by
  simp [amm4SwapInputStore, evalExpr?, amm4SwapAfterAmount1InStore,
    amm4SwapAfterReserve1Store, amm4SwapAfterAmount0InStore,
    amm4SwapAfterReserve0Store, amm4SwapAfterBalance1Store,
    amm4SwapAfterBalance0Store, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem amm4SwapEvalBalance1AfterInputs
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out1.extract 0 32)))) := by
  simp [amm4SwapInputStore, evalExpr?, amm4SwapAfterAmount1InStore,
    amm4SwapAfterReserve1Store, amm4SwapAfterAmount0InStore,
    amm4SwapAfterReserve0Store, amm4SwapAfterBalance1Store,
    EvalResult.ofOption, Std.HashMap.getElem_insert]

def amm4SwapNewProductNat (out0 out1 : ByteArray) : Nat :=
  fromByteArrayBigEndian (out0.extract 0 32) *
    fromByteArrayBigEndian (out1.extract 0 32)

def amm4SwapOldProductNat (evm : EVM.State) : Nat :=
  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat *
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat

def amm4SwapAfterNewProductStore (evm4 : EVM.State)
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray)
    (a0 a1 : Nat) : Store :=
  (amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1).insert
    "newProduct" (.int (Int.ofNat (amm4SwapNewProductNat out0 out1)))

def amm4SwapSourcePrefixNewProduct : List Stmt :=
  amm4SwapSourcePrefixInputGuard ++
    [.letDecl "newProduct" (some uint256)
      (checkedMul (.var "balance0") (.var "balance1"))]

theorem amm4SwapSourceNewProductOk
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 } evm4))
    (hfit : amm4SwapNewProductNat out0 out1 < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixNewProduct
      (.ok { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4) := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 (checkedMul (.var "balance0") (.var "balance1")) =
      .ok (.int (Int.ofNat (amm4SwapNewProductNat out0 out1))) := by
    exact amm4EvalCheckedMul_ok amm4SwapEvalBalance0AfterInputs
      amm4SwapEvalBalance1AfterInputs hfit
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapInputStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 [.letDecl "newProduct" (some uint256)
        (checkedMul (.var "balance0") (.var "balance1"))]
      (.ok { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4) := by
    simpa [amm4SwapAfterNewProductStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4SwapEvalReserve0AfterNewProduct
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  exact amm4MintEvalReserve0
    (locals := amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1)
    (by simp [amm4SwapAfterNewProductStore, amm4SwapInputStore,
      amm4SwapAfterAmount1InStore, amm4SwapAfterReserve1Store,
      amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
      amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store, amm4SwapAfterTransfer0Store,
      amm4SwapStore])

theorem amm4SwapEvalReserve1AfterNewProduct
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  exact amm4MintEvalReserve1
    (locals := amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1)
    (by simp [amm4SwapAfterNewProductStore, amm4SwapInputStore,
      amm4SwapAfterAmount1InStore, amm4SwapAfterReserve1Store,
      amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
      amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store, amm4SwapAfterTransfer0Store,
      amm4SwapStore])

def amm4SwapAfterOldProductStore (evm4 : EVM.State)
    (I : ExecutionEnv) (b0 b1 : Bool) (out0 out1 : ByteArray)
    (a0 a1 : Nat) : Store :=
  (amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1).insert
    "oldProduct" (.int (Int.ofNat (amm4SwapOldProductNat evm4)))

def amm4SwapSourcePrefixOldProduct : List Stmt :=
  amm4SwapSourcePrefixNewProduct ++
    [.letDecl "oldProduct" (some uint256)
      (checkedMul (.storage reserve0Ref) (.storage reserve1Ref))]

theorem amm4SwapSourceOldProductOk
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixNewProduct
      (.ok { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4))
    (hfit : amm4SwapOldProductNat evm4 < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixOldProduct
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4) := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 (checkedMul (.storage reserve0Ref) (.storage reserve1Ref)) =
      .ok (.int (Int.ofNat (amm4SwapOldProductNat evm4))) := by
    exact amm4EvalCheckedMul_ok amm4SwapEvalReserve0AfterNewProduct
      amm4SwapEvalReserve1AfterNewProduct hfit
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterNewProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm4 [.letDecl "oldProduct" (some uint256)
        (checkedMul (.storage reserve0Ref) (.storage reserve1Ref))]
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4) := by
    simpa [amm4SwapAfterOldProductStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4SwapEvalNewProductLocal
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.var "newProduct") =
      .ok (.int (Int.ofNat (amm4SwapNewProductNat out0 out1))) := by
  simp [evalExpr?, amm4SwapAfterOldProductStore,
    amm4SwapAfterNewProductStore, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem amm4SwapEvalOldProductLocal
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.var "oldProduct") =
      .ok (.int (Int.ofNat (amm4SwapOldProductNat evm4))) := by
  simp [evalExpr?, amm4SwapAfterOldProductStore, EvalResult.ofOption]

theorem amm4SwapEvalKGuard_true
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat}
    (hle : amm4SwapOldProductNat evm4 ≤
      amm4SwapNewProductNat out0 out1) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.binary .ge (.var "newProduct") (.var "oldProduct")) =
      .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind,
    amm4SwapEvalNewProductLocal, amm4SwapEvalOldProductLocal, hle]

theorem amm4SwapEvalKGuard_false
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {a0 a1 : Nat}
    (hlt : amm4SwapNewProductNat out0 out1 <
      amm4SwapOldProductNat evm4) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 }
      evm (.binary .ge (.var "newProduct") (.var "oldProduct")) =
      .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind,
    amm4SwapEvalNewProductLocal, amm4SwapEvalOldProductLocal]
  omega

def amm4SwapSourcePrefixKGuard : List Stmt :=
  amm4SwapSourcePrefixOldProduct ++
    [.require (.binary .ge (.var "newProduct") (.var "oldProduct"))]

theorem amm4SwapSourceKGuardOk
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (a0 a1 : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixOldProduct
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4))
    (hle : amm4SwapOldProductNat evm4 ≤
      amm4SwapNewProductNat out0 out1) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixKGuard
      (.ok { contract := contract, locals :=
        amm4SwapAfterOldProductStore evm4 I b0 b1 out0 out1 a0 a1 } evm4) := by
  apply execBlock_append hprefix
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (amm4SwapEvalKGuard_true hle)) ExecBlock.nil

end Benchmarks.ActAmm4
