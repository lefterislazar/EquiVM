import Benchmarks.ActAmm.Swap1ArithmeticTrace
import Benchmarks.ActAmm.Swap1Balance1Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1EvalBalance1AfterBalance1
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterBalance1Store I b ret out }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
  have hget : (ammSwap1AfterBalance1Store I b ret out).get? "balance1" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
    simp [ammSwap1AfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap1EvalReserve1AfterBalance1
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterBalance1Store I b ret out }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply ammMintEvalReserve1
  simp [ammSwap1AfterBalance1Store, ammSwap1AfterBalance0Store,
    ammSwap1AfterTransferStore, ammSwap1Store]

theorem ammSwap1EvalInputGuard_true
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray}
    (hgt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat <
      fromByteArrayBigEndian (out.extract 0 32)) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterBalance1Store I b ret out }
      evm (.binary .gt (.var "balance1") (.storage reserve1Ref)) =
      .ok (.bool true) :=
  ammEvalNatGt_true ammSwap1EvalBalance1AfterBalance1
    ammSwap1EvalReserve1AfterBalance1 hgt

theorem ammSwap1EvalInputGuard_false
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray}
    (hle : fromByteArrayBigEndian (out.extract 0 32) ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterBalance1Store I b ret out }
      evm (.binary .gt (.var "balance1") (.storage reserve1Ref)) =
      .ok (.bool false) :=
  ammEvalNatGt_false ammSwap1EvalBalance1AfterBalance1
    ammSwap1EvalReserve1AfterBalance1 hle

def ammSwap1SourcePrefixInputGuard : List Stmt :=
  ammSwap1SourcePrefixBalance1 ++
    [.require (.binary .gt (.var "balance1") (.storage reserve1Ref))]

theorem ammSwap1SourceInputGuardOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixBalance1
      (.ok { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out } evm2))
    (hgt : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat <
      fromByteArrayBigEndian (out.extract 0 32)) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out } evm2) := by
  apply execBlock_append hprefix
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (ammSwap1EvalInputGuard_true hgt)) ExecBlock.nil

theorem ammSwap1SourceInputGuardRevert
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixBalance1
      (.ok { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out } evm2))
    (hle : fromByteArrayBigEndian (out.extract 0 32) ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out }
      evm2 (swap1Transition.body.drop 7) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (ammSwap1EvalInputGuard_false hle))
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixBalance1,
      ammSwap1SourcePrefixBalance0, ammSwap1SourcePrefixTransfer,
      ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
      swap1Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap1AfterAmount1InStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 : UInt256) : Store :=
  (ammSwap1AfterBalance1Store I b ret out).insert "amount1In"
    (.int (Int.ofNat
      (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))

theorem ammSwap1EvalAmount1In
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray}
    (hretLo : 32 ≤ out.size)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (out.extract 0 32)) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterBalance1Store I b ret out }
      evm (checkedSub (.var "balance1") (.storage reserve1Ref)) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat))) := by
  exact ammEvalCheckedSub_ok ammSwap1EvalBalance1AfterBalance1
    ammSwap1EvalReserve1AfterBalance1 hle
    (fromByteArrayBigEndian_extract0_32_lt hretLo)

def ammSwap1SourcePrefixAmount1In : List Stmt :=
  ammSwap1SourcePrefixInputGuard ++
    [.letDecl "amount1In" (some uint256)
      (checkedSub (.var "balance1") (.storage reserve1Ref))]

theorem ammSwap1SourceAmount1InOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        ammSwap1AfterBalance1Store I b ret out } evm2))
    (hretLo : 32 ≤ out.size)
    (hle : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat ≤
      fromByteArrayBigEndian (out.extract 0 32)) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixAmount1In
      (.ok { contract := contract, locals := (ammSwap1AfterAmount1InStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        evm2) := by
  have heval := ammSwap1EvalAmount1In
    (I := I) (b := b) (ret := ret) (out := out) hretLo hle
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap1AfterBalance1Store I b ret out }
      evm2 [.letDecl "amount1In" (some uint256)
        (checkedSub (.var "balance1") (.storage reserve1Ref))]
      (.ok { contract := contract, locals := (ammSwap1AfterAmount1InStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        evm2) := by
    simpa [ammSwap1AfterAmount1InStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSwap1EvalAmount1InVar
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterAmount1InStore I b ret out r0 }
      evm (.var "amount1In") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))) := by
  simp [ammSwap1AfterAmount1InStore, evalExpr?, EvalResult.ofOption]

theorem ammSwap1EvalReserve0AfterAmount1In
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterAmount1InStore I b ret out r0 }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply ammMintEvalReserve1
  simp [ammSwap1AfterAmount1InStore, ammSwap1AfterBalance1Store,
    ammSwap1AfterBalance0Store, ammSwap1AfterTransferStore, ammSwap1Store]

theorem ammSwap1EvalDenominator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat +
      (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat) < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterAmount1InStore I b ret out r0 }
      evm (checkedAdd (.storage reserve1Ref) (.var "amount1In")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat +
          (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))) := by
  exact ammEvalCheckedAdd_ok ammSwap1EvalReserve0AfterAmount1In
    ammSwap1EvalAmount1InVar hfit

def ammSwap1AfterDenominatorStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 : UInt256) : Store :=
  (ammSwap1AfterAmount1InStore I b ret out r0).insert "kDenominator"
    (.int (Int.ofNat (r0.toNat +
      (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))))

def ammSwap1SourcePrefixDenominator : List Stmt :=
  ammSwap1SourcePrefixAmount1In ++
    [.letDecl "kDenominator" (some uint256)
      (checkedAdd (.storage reserve1Ref) (.var "amount1In"))]

theorem ammSwap1SourceDenominatorOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixAmount1In
      (.ok { contract := contract, locals := (ammSwap1AfterAmount1InStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat +
      (fromByteArrayBigEndian (out.extract 0 32) -
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) <
      UInt256.size) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixDenominator
      (.ok { contract := contract, locals := (ammSwap1AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have heval := ammSwap1EvalDenominator
    (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    hfit
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterAmount1InStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 [.letDecl "kDenominator" (some uint256)
        (checkedAdd (.storage reserve1Ref) (.var "amount1In"))]
      (.ok { contract := contract, locals := (ammSwap1AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simpa [ammSwap1AfterDenominatorStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSwap1EvalAmount1InAfterDenominator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterDenominatorStore I b ret out r0 }
      evm (.var "amount1In") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))) := by
  have hget : (ammSwap1AfterDenominatorStore I b ret out r0).get? "amount1In" =
      some (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))) := by
    unfold ammSwap1AfterDenominatorStore
    rw [store_get_ne (ammSwap1AfterAmount1InStore I b ret out r0)
      (k := "kDenominator") (a := "amount1In") _ (by decide)]
    simp [ammSwap1AfterAmount1InStore]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap1EvalReserve1AfterDenominator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterDenominatorStore I b ret out r0 }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  apply ammMintEvalReserve0
  simp [ammSwap1AfterDenominatorStore, ammSwap1AfterAmount1InStore,
    ammSwap1AfterBalance1Store, ammSwap1AfterBalance0Store,
    ammSwap1AfterTransferStore, ammSwap1Store]

theorem ammSwap1EvalNumerator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat *
      (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat) < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterDenominatorStore I b ret out r0 }
      evm (checkedMul (.storage reserve0Ref) (.var "amount1In")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat *
          (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))) := by
  exact ammEvalCheckedMul_ok ammSwap1EvalReserve1AfterDenominator
    ammSwap1EvalAmount1InAfterDenominator hfit

theorem ammSwap1EvalNumerator_revert
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256}
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat *
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterDenominatorStore I b ret out r0 }
      evm (checkedMul (.storage reserve0Ref) (.var "amount1In")) =
      .revert := by
  exact ammEvalCheckedMul_revert ammSwap1EvalReserve1AfterDenominator
    ammSwap1EvalAmount1InAfterDenominator hover

theorem ammSwap1SourceNumeratorOverflow
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixDenominator
      (.ok { contract := contract, locals := (ammSwap1AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat *
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat)) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have heval := ammSwap1EvalNumerator_revert
    (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    hover
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterDenominatorStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 (swap1Transition.body.drop 10) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixDenominator,
      ammSwap1SourcePrefixAmount1In, ammSwap1SourcePrefixInputGuard,
      ammSwap1SourcePrefixBalance1, ammSwap1SourcePrefixBalance0,
      ammSwap1SourcePrefixTransfer, ammSwap1SourcePrefixRecipient,
      ammSwap1SourcePrefixLiquidity, swap1Transition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap1AfterNumeratorStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 r1 : UInt256) : Store :=
  (ammSwap1AfterDenominatorStore I b ret out r0).insert "kNumerator"
    (.int (Int.ofNat (r1.toNat *
      (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))))

def ammSwap1SourcePrefixNumerator : List Stmt :=
  ammSwap1SourcePrefixDenominator ++
    [.letDecl "kNumerator" (some uint256)
      (checkedMul (.storage reserve0Ref) (.var "amount1In"))]

theorem ammSwap1SourceNumeratorOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixDenominator
      (.ok { contract := contract, locals := (ammSwap1AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat *
      (fromByteArrayBigEndian (out.extract 0 32) -
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat) <
      UInt256.size) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixNumerator
      (.ok { contract := contract, locals := (ammSwap1AfterNumeratorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have heval := ammSwap1EvalNumerator
    (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    hfit
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterDenominatorStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 [.letDecl "kNumerator" (some uint256)
        (checkedMul (.storage reserve0Ref) (.var "amount1In"))]
      (.ok { contract := contract, locals := (ammSwap1AfterNumeratorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simpa [ammSwap1AfterNumeratorStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSwap1EvalNumeratorVar
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterNumeratorStore I b ret out r0 r1 }
      evm (.var "kNumerator") =
      .ok (.int (Int.ofNat (r1.toNat *
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))) := by
  simp [ammSwap1AfterNumeratorStore, evalExpr?, EvalResult.ofOption]

theorem ammSwap1EvalDenominatorVar
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterNumeratorStore I b ret out r0 r1 }
      evm (.var "kDenominator") =
      .ok (.int (Int.ofNat (r0.toNat +
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))) := by
  have hget : (ammSwap1AfterNumeratorStore I b ret out r0 r1).get? "kDenominator" =
      some (.int (Int.ofNat (r0.toNat +
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))) := by
    unfold ammSwap1AfterNumeratorStore
    rw [store_get_ne (ammSwap1AfterDenominatorStore I b ret out r0)
      (k := "kNumerator") (a := "kDenominator") _ (by decide)]
    simp [ammSwap1AfterDenominatorStore]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

def ammSwap1AfterQuotientStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 r1 : UInt256) : Store :=
  (ammSwap1AfterNumeratorStore I b ret out r0 r1).insert "maxAmount0Out"
    (.int (Int.ofNat
      ((r1.toNat *
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)) /
       (r0.toNat +
        (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)))))

def ammSwap1SourcePrefixQuotient : List Stmt :=
  ammSwap1SourcePrefixNumerator ++
    checkedDivInto "maxAmount0Out" (.var "kNumerator") (.var "kDenominator")

theorem ammSwap1SourceQuotientOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixNumerator
      (.ok { contract := contract, locals := (ammSwap1AfterNumeratorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hdenom : 0 <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat +
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat)) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixQuotient
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have hnum := ammSwap1EvalNumeratorVar (evm := evm2) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
  have hden := ammSwap1EvalDenominatorVar (evm := evm2) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
  have hguard := ammEvalNatNeZero_true hden hdenom
  have hdiv := ammEvalNatDiv_ok hnum hden hdenom
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterNumeratorStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 (checkedDivInto "maxAmount0Out" (.var "kNumerator") (.var "kDenominator"))
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [ammSwap1AfterQuotientStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [ammSwap1SourcePrefixQuotient, List.append_assoc] using
    (execBlock_append hprefix htail)

theorem ammSwap1EvalAmountAfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm (.var "amount0Out") =
      .ok (.int (Int.ofNat (ammSwap1AmountWord I).toNat)) := by
  have hget : (ammSwap1AfterQuotientStore I b ret out r0 r1).get?
      "amount0Out" = some (.int (Int.ofNat (ammSwap1AmountWord I).toNat)) := by
    unfold ammSwap1AfterQuotientStore ammSwap1AfterNumeratorStore
      ammSwap1AfterDenominatorStore ammSwap1AfterAmount1InStore
      ammSwap1AfterBalance1Store ammSwap1AfterBalance0Store
      ammSwap1AfterTransferStore
    repeat rw [store_get_ne _ _ (by decide)]
    simp [ammSwap1Store, store_get_self]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap1EvalMaxAfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm (.var "maxAmount0Out") =
      .ok (.int (Int.ofNat
        ((r1.toNat *
          (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)) /
         (r0.toNat +
          (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))))) := by
  simp [ammSwap1AfterQuotientStore, evalExpr?, EvalResult.ofOption]

theorem ammSwap1EvalKGuard_true
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (hle : (ammSwap1AmountWord I).toNat ≤
      (r1.toNat * (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)) /
        (r0.toNat + (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat))) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm (.binary .le (.var "amount0Out") (.var "maxAmount0Out")) =
      .ok (.bool true) :=
  ammEvalNatLe_true ammSwap1EvalAmountAfterQuotient
    ammSwap1EvalMaxAfterQuotient hle

theorem ammSwap1EvalKGuard_false
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (hbad : (r1.toNat *
      (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)) /
      (r0.toNat + (fromByteArrayBigEndian (out.extract 0 32) - r0.toNat)) <
      (ammSwap1AmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm (.binary .le (.var "amount0Out") (.var "maxAmount0Out")) =
      .ok (.bool false) :=
  ammEvalNatLe_false ammSwap1EvalAmountAfterQuotient
    ammSwap1EvalMaxAfterQuotient hbad

def ammSwap1SourcePrefixKGuard : List Stmt :=
  ammSwap1SourcePrefixQuotient ++
    [.require (.binary .le (.var "amount0Out") (.var "maxAmount0Out"))]

theorem ammSwap1SourceKGuardOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixQuotient
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hle : (ammSwap1AmountWord I).toNat ≤
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat *
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat)) /
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat +
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat))) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixKGuard
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 [.require (.binary .le (.var "amount0Out") (.var "maxAmount0Out"))]
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (ammSwap1EvalKGuard_true hle)) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem ammSwap1SourceKGuardRevert
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixQuotient
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hbad :
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat *
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat)) /
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat +
        (fromByteArrayBigEndian (out.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat)) <
      (ammSwap1AmountWord I).toNat) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 (swap1Transition.body.drop 13) .reverted := by
    simp only [swap1Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (ammSwap1EvalKGuard_false hbad))
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm swap1Transition.body .reverted := by
    simpa [ammSwap1SourcePrefixQuotient,
      ammSwap1SourcePrefixNumerator, ammSwap1SourcePrefixDenominator,
      ammSwap1SourcePrefixAmount1In, ammSwap1SourcePrefixInputGuard,
      ammSwap1SourcePrefixBalance1, ammSwap1SourcePrefixBalance0,
      ammSwap1SourcePrefixTransfer, ammSwap1SourcePrefixRecipient,
      ammSwap1SourcePrefixLiquidity, swap1Transition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop,
      List.append_assoc] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap1EvalBalance0AfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) := by
  have hget : (ammSwap1AfterQuotientStore I b ret out r0 r1).get?
      "balance0" = some (.int (Int.ofNat
        (fromByteArrayBigEndian (ret.extract 0 32)))) := by
    unfold ammSwap1AfterQuotientStore ammSwap1AfterNumeratorStore
      ammSwap1AfterDenominatorStore ammSwap1AfterAmount1InStore
      ammSwap1AfterBalance1Store
    repeat rw [store_get_ne _ _ (by decide)]
    simp [ammSwap1AfterBalance0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap1EvalBalance1AfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
  have hget : (ammSwap1AfterQuotientStore I b ret out r0 r1).get?
      "balance1" = some (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32)))) := by
    unfold ammSwap1AfterQuotientStore ammSwap1AfterNumeratorStore
      ammSwap1AfterDenominatorStore ammSwap1AfterAmount1InStore
    repeat rw [store_get_ne _ _ (by decide)]
    simp [ammSwap1AfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

def ammSwap1AfterReserve0 (evm : EVM.State) (ret : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))

theorem ammSwap1AssignReserve0
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (hretLo : 32 ≤ ret.size) :
    assignStorageRef? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        ammSwap1AfterQuotientStore I b ret out r0 r1 },
        ammSwap1AfterReserve0 evm ret) := by
  have hword : (UInt256.ofNat
      (fromByteArrayBigEndian (ret.extract 0 32))).toNat =
      fromByteArrayBigEndian (ret.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hretLo)
  have hstore : storageLocStore evm (wordLoc ⟨5⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) =
      some (ammSwap1AfterReserve0 evm ret) := by
    simpa [ammSwap1AfterReserve0, hword] using
      ammStorageLocStore_uint256 evm ⟨5⟩
        (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      ammSwap1AfterQuotientStore I b ret out r0 r1 })
    (evm := evm) (evm' := ammSwap1AfterReserve0 evm ret)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))
    (by simp [ammSwap1AfterQuotientStore, ammSwap1AfterNumeratorStore,
      ammSwap1AfterDenominatorStore, ammSwap1AfterAmount1InStore,
      ammSwap1AfterBalance1Store, ammSwap1AfterBalance0Store,
      ammSwap1AfterTransferStore, ammSwap1Store, reserve0Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

def ammSwap1SourcePrefixReserve0 : List Stmt :=
  ammSwap1SourcePrefixKGuard ++
    [.assign .storage reserve0Ref (.var "balance0")]

theorem ammSwap1SourceReserve0Ok
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixKGuard
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hretLo : 32 ≤ ret.size) :
    ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixReserve0
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        (ammSwap1AfterReserve0 evm2 ret)) := by
  have heval := ammSwap1EvalBalance0AfterQuotient
    (evm := evm2) (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
  have hassign := ammSwap1AssignReserve0
    (evm := evm2) (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    hretLo
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 [.assign .storage reserve0Ref (.var "balance0")]
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        (ammSwap1AfterReserve0 evm2 ret)) := by
    exact ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

def ammSwap1AfterReserve1 (evm : EVM.State) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))

theorem ammSwap1AssignReserve1
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (houtLo : 32 ≤ out.size) :
    assignStorageRef? config
      { contract := contract, locals := ammSwap1AfterQuotientStore I b ret out r0 r1 }
      evm .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        ammSwap1AfterQuotientStore I b ret out r0 r1 },
        ammSwap1AfterReserve1 evm out) := by
  have hword : (UInt256.ofNat
      (fromByteArrayBigEndian (out.extract 0 32))).toNat =
      fromByteArrayBigEndian (out.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt houtLo)
  have hstore : storageLocStore evm (wordLoc ⟨6⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      some (ammSwap1AfterReserve1 evm out) := by
    simpa [ammSwap1AfterReserve1, hword] using
      ammStorageLocStore_uint256 evm ⟨6⟩
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      ammSwap1AfterQuotientStore I b ret out r0 r1 })
    (evm := evm) (evm' := ammSwap1AfterReserve1 evm out)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (by simp [ammSwap1AfterQuotientStore, ammSwap1AfterNumeratorStore,
      ammSwap1AfterDenominatorStore, ammSwap1AfterAmount1InStore,
      ammSwap1AfterBalance1Store, ammSwap1AfterBalance0Store,
      ammSwap1AfterTransferStore, ammSwap1Store, reserve1Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem ammSwap1SourceSuccess
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap1Store I }
      evm ammSwap1SourcePrefixKGuard
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hretLo : 32 ≤ ret.size) (houtLo : 32 ≤ out.size) :
    ExecTransitionBody config contract evm (ammSwap1Store I)
      swap1Transition.body
      (.returned { contract := contract, locals := (ammSwap1AfterQuotientStore
          I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        (ammSwap1AfterReserve1 (ammSwap1AfterReserve0 evm2 ret) out) none) := by
  have hreserve0 := ammSwap1SourceReserve0Ok I b ret out hprefix hretLo
  have heval := ammSwap1EvalBalance1AfterQuotient
    (evm := ammSwap1AfterReserve0 evm2 ret) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
  have hassign := ammSwap1AssignReserve1
    (evm := ammSwap1AfterReserve0 evm2 ret) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    houtLo
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      (ammSwap1AfterReserve0 evm2 ret)
      [.assign .storage reserve1Ref (.var "balance1")]
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        (ammSwap1AfterReserve1 (ammSwap1AfterReserve0 evm2 ret) out)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  have hblock := execBlock_append hreserve0 htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap1Store I } evm
      swap1Transition.body
      (.ok { contract := contract, locals := (ammSwap1AfterQuotientStore
          I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        (ammSwap1AfterReserve1 (ammSwap1AfterReserve0 evm2 ret) out)) := by
    simpa [ammSwap1SourcePrefixReserve0, ammSwap1SourcePrefixKGuard,
      ammSwap1SourcePrefixQuotient, ammSwap1SourcePrefixNumerator,
      ammSwap1SourcePrefixDenominator, ammSwap1SourcePrefixAmount1In,
      ammSwap1SourcePrefixInputGuard, ammSwap1SourcePrefixBalance1,
      ammSwap1SourcePrefixBalance0, ammSwap1SourcePrefixTransfer,
      ammSwap1SourcePrefixRecipient, ammSwap1SourcePrefixLiquidity,
      swap1Transition, nonpayable, checkedDivInto,
      tokenTransfer, tokenBalance, List.cons_append,
      List.nil_append, List.append_assoc] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hbody

end Benchmarks.ActAmm
