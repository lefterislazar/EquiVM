import Benchmarks.ActAmm4.SwapSourceBalances

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapEvalAmount0AfterBalances
    {evm : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
      evm (.var "amount0Out") =
      .ok (.int (Int.ofNat (amm4SwapAmount0Word I).toNat)) := by
  simp [evalExpr?, amm4SwapAfterBalance1Store,
    amm4SwapAfterBalance0Store, amm4SwapAfterTransfer1Store,
    amm4SwapAfterTransfer0Store, amm4SwapStore, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem amm4SwapEvalReserve0AfterBalances
    {evm : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  exact amm4MintEvalReserve0
    (locals := amm4SwapAfterBalance1Store I b0 b1 out0 out1)
    (by simp [amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store, amm4SwapAfterTransfer0Store,
      amm4SwapStore])

theorem amm4SwapEvalReserve0AfterOut
    {evm : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray}
    (hle : (amm4SwapAmount0Word I).toNat ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
      evm (checkedSub (.storage reserve0Ref) (.var "amount0Out")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat -
          (amm4SwapAmount0Word I).toNat))) := by
  exact amm4EvalCheckedSub_ok
    amm4SwapEvalReserve0AfterBalances
    amm4SwapEvalAmount0AfterBalances hle
    (by exact (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).val.isLt)

def amm4SwapAfterReserve0Store (evm : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) : Store :=
  (amm4SwapAfterBalance1Store I b0 b1 out0 out1).insert
    "reserve0AfterOut" (.int (Int.ofNat
      ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat -
        (amm4SwapAmount0Word I).toNat)))

def amm4SwapSourcePrefixReserve0 : List Stmt :=
  amm4SwapSourcePrefixBalance1 ++
    [.letDecl "reserve0AfterOut" (some uint256)
      (checkedSub (.storage reserve0Ref) (.var "amount0Out"))]

theorem amm4SwapSourceReserve0Ok
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixBalance1
      (.ok { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 } evm4))
    (hle : (amm4SwapAmount0Word I).toNat ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 } evm4) := by
  have heval := amm4SwapEvalReserve0AfterOut
    (evm := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) hle
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterBalance1Store I b0 b1 out0 out1 }
      evm4 [.letDecl "reserve0AfterOut" (some uint256)
        (checkedSub (.storage reserve0Ref) (.var "amount0Out"))]
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 } evm4) := by
    simpa [amm4SwapAfterReserve0Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4SwapEvalBalance0AfterReserve0
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out0.extract 0 32)))) := by
  simp [evalExpr?, amm4SwapAfterReserve0Store,
    amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
    EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem amm4SwapEvalReserve0AfterOutLocal
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm (.var "reserve0AfterOut") =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
          (amm4SwapAmount0Word I).toNat))) := by
  simp [evalExpr?, amm4SwapAfterReserve0Store, EvalResult.ofOption]

theorem amm4SwapEvalAmount0InGuard_true
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray}
    (hgt : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨5⟩).toNat -
        (amm4SwapAmount0Word I).toNat <
      fromByteArrayBigEndian (out0.extract 0 32)) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm (.binary .gt (.var "balance0") (.var "reserve0AfterOut")) =
      .ok (.bool true) := by
  exact amm4EvalNatGt_true amm4SwapEvalBalance0AfterReserve0
    amm4SwapEvalReserve0AfterOutLocal hgt

theorem amm4SwapEvalAmount0InGuard_false
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray}
    (hle : fromByteArrayBigEndian (out0.extract 0 32) ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
        (amm4SwapAmount0Word I).toNat) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm (.binary .gt (.var "balance0") (.var "reserve0AfterOut")) =
      .ok (.bool false) := by
  exact amm4EvalNatGt_false amm4SwapEvalBalance0AfterReserve0
    amm4SwapEvalReserve0AfterOutLocal hle

def amm4SwapAmount0InPosNat (evm4 : EVM.State)
    (I : ExecutionEnv) (out0 : ByteArray) : Nat :=
  fromByteArrayBigEndian (out0.extract 0 32) -
    ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
      (amm4SwapAmount0Word I).toNat)

def amm4SwapAfterAmount0InStore (evm4 : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (amount0In : Nat) : Store :=
  (amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1).insert
    "amount0In" (.int (Int.ofNat amount0In))

def amm4SwapSourcePrefixAmount0In : List Stmt :=
  amm4SwapSourcePrefixReserve0 ++
    [.ite (.binary .gt (.var "balance0") (.var "reserve0AfterOut"))
      [.letDecl "amount0In" (some uint256)
        (checkedSub (.var "balance0") (.var "reserve0AfterOut"))]
      [.letDecl "amount0In" (some uint256) (.intLit 0)]]

theorem amm4SwapSourceAmount0InPositive
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 } evm4))
    (hlo : 32 ≤ out0.size)
    (hgt : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨5⟩).toNat -
        (amm4SwapAmount0Word I).toNat <
      fromByteArrayBigEndian (out0.extract 0 32)) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount0In
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1
          (amm4SwapAmount0InPosNat evm4 I out0)) } evm4) := by
  have hcond := amm4SwapEvalAmount0InGuard_true (evm := evm4)
    (evm4 := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) hgt
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm4 (checkedSub (.var "balance0") (.var "reserve0AfterOut")) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out0.extract 0 32) -
          ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
            (amm4SwapAmount0Word I).toNat)))) := by
    exact amm4EvalCheckedSub_ok
      amm4SwapEvalBalance0AfterReserve0
      amm4SwapEvalReserve0AfterOutLocal
      (Nat.le_of_lt hgt)
      (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hthen : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm4 [.letDecl "amount0In" (some uint256)
        (checkedSub (.var "balance0") (.var "reserve0AfterOut"))]
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1
          (amm4SwapAmount0InPosNat evm4 I out0)) } evm4) := by
    simpa [amm4SwapAfterAmount0InStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm4 [.ite (.binary .gt (.var "balance0") (.var "reserve0AfterOut"))
        [.letDecl "amount0In" (some uint256)
          (checkedSub (.var "balance0") (.var "reserve0AfterOut"))]
        [.letDecl "amount0In" (some uint256) (.intLit 0)]]
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1
          (amm4SwapAmount0InPosNat evm4 I out0)) } evm4) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4SwapSourceAmount0InZero
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve0
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 } evm4))
    (hle : fromByteArrayBigEndian (out0.extract 0 32) ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨5⟩).toNat -
        (amm4SwapAmount0Word I).toNat) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount0In
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 0 } evm4) := by
  have hcond := amm4SwapEvalAmount0InGuard_false (evm := evm4)
    (evm4 := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) hle
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm4 (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have helse : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm4 [.letDecl "amount0In" (some uint256) (.intLit 0)]
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 0 } evm4) := by
    simpa [amm4SwapAfterAmount0InStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve0Store evm4 I b0 b1 out0 out1 }
      evm4 [.ite (.binary .gt (.var "balance0") (.var "reserve0AfterOut"))
        [.letDecl "amount0In" (some uint256)
          (checkedSub (.var "balance0") (.var "reserve0AfterOut"))]
        [.letDecl "amount0In" (some uint256) (.intLit 0)]]
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 0 } evm4) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcond helse) ExecBlock.nil
  exact execBlock_append hprefix htail

def amm4SwapAfterReserve1Store (evm4 : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (amount0In : Nat) : Store :=
  (amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In).insert
    "reserve1AfterOut" (.int (Int.ofNat
      ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
        (amm4SwapAmount1Word I).toNat)))

def amm4SwapSourcePrefixReserve1 : List Stmt :=
  amm4SwapSourcePrefixAmount0In ++
    [.letDecl "reserve1AfterOut" (some uint256)
      (checkedSub (.storage reserve1Ref) (.var "amount1Out"))]

theorem amm4SwapEvalReserve1AfterAmount0In
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  exact amm4MintEvalReserve1
    (locals := amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In)
    (by simp [amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
      amm4SwapAfterBalance1Store, amm4SwapAfterBalance0Store,
      amm4SwapAfterTransfer1Store, amm4SwapAfterTransfer0Store,
      amm4SwapStore])

theorem amm4SwapEvalAmount1AfterAmount0In
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In }
      evm (.var "amount1Out") =
      .ok (.int (Int.ofNat (amm4SwapAmount1Word I).toNat)) := by
  simp [evalExpr?, amm4SwapAfterAmount0InStore,
    amm4SwapAfterReserve0Store, amm4SwapAfterBalance1Store,
    amm4SwapAfterBalance0Store, amm4SwapAfterTransfer1Store,
    amm4SwapAfterTransfer0Store, amm4SwapStore, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem amm4SwapSourceReserve1Ok
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (amount0In : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount0In
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In } evm4))
    (hle : (amm4SwapAmount1Word I).toNat ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve1
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In } evm4) := by
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In }
      evm4 (checkedSub (.storage reserve1Ref) (.var "amount1Out")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
          (amm4SwapAmount1Word I).toNat))) := by
    exact amm4EvalCheckedSub_ok
      amm4SwapEvalReserve1AfterAmount0In
      amm4SwapEvalAmount1AfterAmount0In hle
      (by exact (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).val.isLt)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterAmount0InStore evm4 I b0 b1 out0 out1 amount0In }
      evm4 [.letDecl "reserve1AfterOut" (some uint256)
        (checkedSub (.storage reserve1Ref) (.var "amount1Out"))]
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In } evm4) := by
    simpa [amm4SwapAfterReserve1Store, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem amm4SwapEvalBalance1AfterReserve1
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out1.extract 0 32)))) := by
  simp [evalExpr?, amm4SwapAfterReserve1Store,
    amm4SwapAfterAmount0InStore, amm4SwapAfterReserve0Store,
    amm4SwapAfterBalance1Store, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem amm4SwapEvalReserve1AfterOutLocal
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm (.var "reserve1AfterOut") =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
          (amm4SwapAmount1Word I).toNat))) := by
  simp [evalExpr?, amm4SwapAfterReserve1Store, EvalResult.ofOption]

theorem amm4SwapEvalAmount1InGuard_true
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In : Nat}
    (hgt : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨6⟩).toNat -
        (amm4SwapAmount1Word I).toNat <
      fromByteArrayBigEndian (out1.extract 0 32)) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm (.binary .gt (.var "balance1") (.var "reserve1AfterOut")) =
      .ok (.bool true) := by
  exact amm4EvalNatGt_true amm4SwapEvalBalance1AfterReserve1
    amm4SwapEvalReserve1AfterOutLocal hgt

theorem amm4SwapEvalAmount1InGuard_false
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In : Nat}
    (hle : fromByteArrayBigEndian (out1.extract 0 32) ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
        (amm4SwapAmount1Word I).toNat) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm (.binary .gt (.var "balance1") (.var "reserve1AfterOut")) =
      .ok (.bool false) := by
  exact amm4EvalNatGt_false amm4SwapEvalBalance1AfterReserve1
    amm4SwapEvalReserve1AfterOutLocal hle

def amm4SwapAmount1InPosNat (evm4 : EVM.State)
    (I : ExecutionEnv) (out1 : ByteArray) : Nat :=
  fromByteArrayBigEndian (out1.extract 0 32) -
    ((Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
      (amm4SwapAmount1Word I).toNat)

def amm4SwapAfterAmount1InStore (evm4 : EVM.State) (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (amount0In amount1In : Nat) : Store :=
  (amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In).insert
    "amount1In" (.int (Int.ofNat amount1In))

def amm4SwapSourcePrefixAmount1In : List Stmt :=
  amm4SwapSourcePrefixReserve1 ++
    [.ite (.binary .gt (.var "balance1") (.var "reserve1AfterOut"))
      [.letDecl "amount1In" (some uint256)
        (checkedSub (.var "balance1") (.var "reserve1AfterOut"))]
      [.letDecl "amount1In" (some uint256) (.intLit 0)]]

theorem amm4SwapSourceAmount1InPositive
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (amount0In : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve1
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In } evm4))
    (hlo : 32 ≤ out1.size)
    (hgt : (Solm.EVM.storageLoad evm4
      evm4.executionEnv.codeOwner ⟨6⟩).toNat -
        (amm4SwapAmount1Word I).toNat <
      fromByteArrayBigEndian (out1.extract 0 32)) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount1In
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In
          (amm4SwapAmount1InPosNat evm4 I out1)) } evm4) := by
  have hcond := amm4SwapEvalAmount1InGuard_true (evm := evm4)
    (evm4 := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) (amount0In := amount0In) hgt
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm4 (checkedSub (.var "balance1") (.var "reserve1AfterOut")) =
      .ok (.int (Int.ofNat (amm4SwapAmount1InPosNat evm4 I out1))) := by
    exact amm4EvalCheckedSub_ok
      amm4SwapEvalBalance1AfterReserve1
      amm4SwapEvalReserve1AfterOutLocal
      (Nat.le_of_lt hgt)
      (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hthen : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm4 [.letDecl "amount1In" (some uint256)
        (checkedSub (.var "balance1") (.var "reserve1AfterOut"))]
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In
          (amm4SwapAmount1InPosNat evm4 I out1)) } evm4) := by
    simpa [amm4SwapAfterAmount1InStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm4 [.ite (.binary .gt (.var "balance1") (.var "reserve1AfterOut"))
        [.letDecl "amount1In" (some uint256)
          (checkedSub (.var "balance1") (.var "reserve1AfterOut"))]
        [.letDecl "amount1In" (some uint256) (.intLit 0)]]
      (.ok { contract := contract, locals :=
        (amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In
          (amm4SwapAmount1InPosNat evm4 I out1)) } evm4) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4SwapSourceAmount1InZero
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray) (amount0In : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixReserve1
      (.ok { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In } evm4))
    (hle : fromByteArrayBigEndian (out1.extract 0 32) ≤
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨6⟩).toNat -
        (amm4SwapAmount1Word I).toNat) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount1In
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In 0 } evm4) := by
  have hcond := amm4SwapEvalAmount1InGuard_false (evm := evm4)
    (evm4 := evm4) (I := I) (b0 := b0) (b1 := b1)
    (out0 := out0) (out1 := out1) (amount0In := amount0In) hle
  have heval : evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm4 (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have helse : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm4 [.letDecl "amount1In" (some uint256) (.intLit 0)]
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In 0 } evm4) := by
    simpa [amm4SwapAfterAmount1InStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4SwapAfterReserve1Store evm4 I b0 b1 out0 out1 amount0In }
      evm4 [.ite (.binary .gt (.var "balance1") (.var "reserve1AfterOut"))
        [.letDecl "amount1In" (some uint256)
          (checkedSub (.var "balance1") (.var "reserve1AfterOut"))]
        [.letDecl "amount1In" (some uint256) (.intLit 0)]]
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In 0 } evm4) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcond helse) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem amm4SwapEvalAmount0InLocal
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In amount1In : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In amount1In }
      evm (.var "amount0In") = .ok (.int (Int.ofNat amount0In)) := by
  simp [evalExpr?, amm4SwapAfterAmount1InStore,
    amm4SwapAfterReserve1Store, amm4SwapAfterAmount0InStore,
    EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem amm4SwapEvalAmount1InLocal
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In amount1In : Nat} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In amount1In }
      evm (.var "amount1In") = .ok (.int (Int.ofNat amount1In)) := by
  simp [evalExpr?, amm4SwapAfterAmount1InStore, EvalResult.ofOption]

theorem amm4SwapEvalInputGuard_true
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} {amount0In amount1In : Nat}
    (hpos : 0 < amount0In ∨ 0 < amount1In) :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In amount1In }
      evm (.binary .or
        (.binary .gt (.var "amount0In") (.intLit 0))
        (.binary .gt (.var "amount1In") (.intLit 0))) =
      .ok (.bool true) := by
  rcases hpos with h0 | h1
  · exact amm4EvalOr_true_left
      (amm4EvalNatGt_true amm4SwapEvalAmount0InLocal
        (by simp [evalExpr?, pure]) h0)
  · by_cases h0 : 0 < amount0In
    · exact amm4EvalOr_true_left
        (amm4EvalNatGt_true amm4SwapEvalAmount0InLocal
          (by simp [evalExpr?, pure]) h0)
    · exact amm4EvalOr_true_right
        (amm4EvalNatGt_false (a := amount0In) (b := 0)
          amm4SwapEvalAmount0InLocal
          (by simp [evalExpr?, pure]) (by omega))
        (amm4EvalNatGt_true amm4SwapEvalAmount1InLocal
          (by simp [evalExpr?, pure]) h1)

theorem amm4SwapEvalInputGuard_false
    {evm evm4 : EVM.State} {I : ExecutionEnv} {b0 b1 : Bool}
    {out0 out1 : ByteArray} :
    evalExpr? config
      { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 0 0 }
      evm (.binary .or
        (.binary .gt (.var "amount0In") (.intLit 0))
        (.binary .gt (.var "amount1In") (.intLit 0))) =
      .ok (.bool false) := by
  exact amm4EvalOr_false
    (amm4EvalNatGt_false (a := 0) (b := 0) amm4SwapEvalAmount0InLocal
      (by simp [evalExpr?, pure]) (by omega))
    (amm4EvalNatGt_false (a := 0) (b := 0) amm4SwapEvalAmount1InLocal
      (by simp [evalExpr?, pure]) (by omega))

def amm4SwapSourcePrefixInputGuard : List Stmt :=
  amm4SwapSourcePrefixAmount1In ++
    [.require (.binary .or
      (.binary .gt (.var "amount0In") (.intLit 0))
      (.binary .gt (.var "amount1In") (.intLit 0)))]

theorem amm4SwapSourceInputGuardOk
    {evm evm4 : EVM.State} (I : ExecutionEnv)
    (b0 b1 : Bool) (out0 out1 : ByteArray)
    (amount0In amount1In : Nat)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixAmount1In
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In amount1In } evm4))
    (hpos : 0 < amount0In ∨ 0 < amount1In) :
    ExecBlock config
      { contract := contract, locals := amm4SwapStore I }
      evm amm4SwapSourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        amm4SwapAfterAmount1InStore evm4 I b0 b1 out0 out1 amount0In amount1In } evm4) := by
  apply execBlock_append hprefix
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (amm4SwapEvalInputGuard_true hpos)) ExecBlock.nil

end Benchmarks.ActAmm4
