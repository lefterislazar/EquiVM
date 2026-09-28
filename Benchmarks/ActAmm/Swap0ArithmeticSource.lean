import Benchmarks.ActAmm.Swap0ArithmeticTrace
import Benchmarks.ActAmm.Swap0Balance1Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap0EvalBalance0AfterBalance1
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterBalance1Store I b ret out }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) := by
  have hget : (ammSwap0AfterBalance1Store I b ret out).get? "balance0" =
      some (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) := by
    unfold ammSwap0AfterBalance1Store
    rw [store_get_ne (ammSwap0AfterBalance0Store I b ret)
      (k := "balance1") (a := "balance0") _ (by decide)]
    simp [ammSwap0AfterBalance0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap0EvalReserve0AfterBalance1
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterBalance1Store I b ret out }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  apply ammMintEvalReserve0
  simp [ammSwap0AfterBalance1Store, ammSwap0AfterBalance0Store,
    ammSwap0AfterTransferStore, ammSwap0Store]

theorem ammSwap0EvalInputGuard_true
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray}
    (hgt : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat <
      fromByteArrayBigEndian (ret.extract 0 32)) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterBalance1Store I b ret out }
      evm (.binary .gt (.var "balance0") (.storage reserve0Ref)) =
      .ok (.bool true) :=
  ammEvalNatGt_true ammSwap0EvalBalance0AfterBalance1
    ammSwap0EvalReserve0AfterBalance1 hgt

theorem ammSwap0EvalInputGuard_false
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray}
    (hle : fromByteArrayBigEndian (ret.extract 0 32) ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterBalance1Store I b ret out }
      evm (.binary .gt (.var "balance0") (.storage reserve0Ref)) =
      .ok (.bool false) :=
  ammEvalNatGt_false ammSwap0EvalBalance0AfterBalance1
    ammSwap0EvalReserve0AfterBalance1 hle

def ammSwap0SourcePrefixInputGuard : List Stmt :=
  ammSwap0SourcePrefixBalance1 ++
    [.require (.binary .gt (.var "balance0") (.storage reserve0Ref))]

theorem ammSwap0SourceInputGuardOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance1
      (.ok { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out } evm2))
    (hgt : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat <
      fromByteArrayBigEndian (ret.extract 0 32)) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out } evm2) := by
  apply execBlock_append hprefix
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (ammSwap0EvalInputGuard_true hgt)) ExecBlock.nil

theorem ammSwap0SourceInputGuardRevert
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixBalance1
      (.ok { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out } evm2))
    (hle : fromByteArrayBigEndian (ret.extract 0 32) ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out }
      evm2 (swap0Transition.body.drop 7) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (ammSwap0EvalInputGuard_false hle))
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixBalance1,
      ammSwap0SourcePrefixBalance0, ammSwap0SourcePrefixTransfer,
      ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      List.cons_append, List.nil_append, List.drop] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap0AfterAmount0InStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 : UInt256) : Store :=
  (ammSwap0AfterBalance1Store I b ret out).insert "amount0In"
    (.int (Int.ofNat
      (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))

theorem ammSwap0EvalAmount0In
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray}
    (hretLo : 32 ≤ ret.size)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat ≤
      fromByteArrayBigEndian (ret.extract 0 32)) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterBalance1Store I b ret out }
      evm (checkedSub (.var "balance0") (.storage reserve0Ref)) =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat))) := by
  exact ammEvalCheckedSub_ok ammSwap0EvalBalance0AfterBalance1
    ammSwap0EvalReserve0AfterBalance1 hle
    (fromByteArrayBigEndian_extract0_32_lt hretLo)

def ammSwap0SourcePrefixAmount0In : List Stmt :=
  ammSwap0SourcePrefixInputGuard ++
    [.letDecl "amount0In" (some uint256)
      (checkedSub (.var "balance0") (.storage reserve0Ref))]

theorem ammSwap0SourceAmount0InOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixInputGuard
      (.ok { contract := contract, locals :=
        ammSwap0AfterBalance1Store I b ret out } evm2))
    (hretLo : 32 ≤ ret.size)
    (hle : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat ≤
      fromByteArrayBigEndian (ret.extract 0 32)) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixAmount0In
      (.ok { contract := contract, locals := (ammSwap0AfterAmount0InStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        evm2) := by
  have heval := ammSwap0EvalAmount0In
    (I := I) (b := b) (ret := ret) (out := out) hretLo hle
  have htail : ExecBlock config
      { contract := contract, locals := ammSwap0AfterBalance1Store I b ret out }
      evm2 [.letDecl "amount0In" (some uint256)
        (checkedSub (.var "balance0") (.storage reserve0Ref))]
      (.ok { contract := contract, locals := (ammSwap0AfterAmount0InStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
        evm2) := by
    simpa [ammSwap0AfterAmount0InStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSwap0EvalAmount0InVar
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterAmount0InStore I b ret out r0 }
      evm (.var "amount0In") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))) := by
  simp [ammSwap0AfterAmount0InStore, evalExpr?, EvalResult.ofOption]

theorem ammSwap0EvalReserve0AfterAmount0In
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterAmount0InStore I b ret out r0 }
      evm (.storage reserve0Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  apply ammMintEvalReserve0
  simp [ammSwap0AfterAmount0InStore, ammSwap0AfterBalance1Store,
    ammSwap0AfterBalance0Store, ammSwap0AfterTransferStore, ammSwap0Store]

theorem ammSwap0EvalDenominator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat +
      (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat) < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterAmount0InStore I b ret out r0 }
      evm (checkedAdd (.storage reserve0Ref) (.var "amount0In")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat +
          (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))) := by
  exact ammEvalCheckedAdd_ok ammSwap0EvalReserve0AfterAmount0In
    ammSwap0EvalAmount0InVar hfit

def ammSwap0AfterDenominatorStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 : UInt256) : Store :=
  (ammSwap0AfterAmount0InStore I b ret out r0).insert "kDenominator"
    (.int (Int.ofNat (r0.toNat +
      (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))))

def ammSwap0SourcePrefixDenominator : List Stmt :=
  ammSwap0SourcePrefixAmount0In ++
    [.letDecl "kDenominator" (some uint256)
      (checkedAdd (.storage reserve0Ref) (.var "amount0In"))]

theorem ammSwap0SourceDenominatorOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixAmount0In
      (.ok { contract := contract, locals := (ammSwap0AfterAmount0InStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat +
      (fromByteArrayBigEndian (ret.extract 0 32) -
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) <
      UInt256.size) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixDenominator
      (.ok { contract := contract, locals := (ammSwap0AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
  have heval := ammSwap0EvalDenominator
    (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    hfit
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterAmount0InStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 [.letDecl "kDenominator" (some uint256)
        (checkedAdd (.storage reserve0Ref) (.var "amount0In"))]
      (.ok { contract := contract, locals := (ammSwap0AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2) := by
    simpa [ammSwap0AfterDenominatorStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSwap0EvalAmount0InAfterDenominator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterDenominatorStore I b ret out r0 }
      evm (.var "amount0In") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))) := by
  have hget : (ammSwap0AfterDenominatorStore I b ret out r0).get? "amount0In" =
      some (.int (Int.ofNat
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))) := by
    unfold ammSwap0AfterDenominatorStore
    rw [store_get_ne (ammSwap0AfterAmount0InStore I b ret out r0)
      (k := "kDenominator") (a := "amount0In") _ (by decide)]
    simp [ammSwap0AfterAmount0InStore]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap0EvalReserve1AfterDenominator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterDenominatorStore I b ret out r0 }
      evm (.storage reserve1Ref) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  apply ammMintEvalReserve1
  simp [ammSwap0AfterDenominatorStore, ammSwap0AfterAmount0InStore,
    ammSwap0AfterBalance1Store, ammSwap0AfterBalance0Store,
    ammSwap0AfterTransferStore, ammSwap0Store]

theorem ammSwap0EvalNumerator
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256}
    (hfit : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat *
      (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat) < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterDenominatorStore I b ret out r0 }
      evm (checkedMul (.storage reserve1Ref) (.var "amount0In")) =
      .ok (.int (Int.ofNat
        ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat *
          (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))) := by
  exact ammEvalCheckedMul_ok ammSwap0EvalReserve1AfterDenominator
    ammSwap0EvalAmount0InAfterDenominator hfit

theorem ammSwap0EvalNumerator_revert
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 : UInt256}
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat *
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterDenominatorStore I b ret out r0 }
      evm (checkedMul (.storage reserve1Ref) (.var "amount0In")) =
      .revert := by
  exact ammEvalCheckedMul_revert ammSwap0EvalReserve1AfterDenominator
    ammSwap0EvalAmount0InAfterDenominator hover

theorem ammSwap0SourceNumeratorOverflow
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixDenominator
      (.ok { contract := contract, locals := (ammSwap0AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat *
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat)) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have heval := ammSwap0EvalNumerator_revert
    (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    hover
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterDenominatorStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 (swap0Transition.body.drop 10) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert heval)
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixDenominator,
      ammSwap0SourcePrefixAmount0In, ammSwap0SourcePrefixInputGuard,
      ammSwap0SourcePrefixBalance1, ammSwap0SourcePrefixBalance0,
      ammSwap0SourcePrefixTransfer, ammSwap0SourcePrefixRecipient,
      ammSwap0SourcePrefixLiquidity, swap0Transition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop]
      using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

def ammSwap0AfterNumeratorStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 r1 : UInt256) : Store :=
  (ammSwap0AfterDenominatorStore I b ret out r0).insert "kNumerator"
    (.int (Int.ofNat (r1.toNat *
      (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))))

def ammSwap0SourcePrefixNumerator : List Stmt :=
  ammSwap0SourcePrefixDenominator ++
    [.letDecl "kNumerator" (some uint256)
      (checkedMul (.storage reserve1Ref) (.var "amount0In"))]

theorem ammSwap0SourceNumeratorOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixDenominator
      (.ok { contract := contract, locals := (ammSwap0AfterDenominatorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) } evm2))
    (hfit : (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat *
      (fromByteArrayBigEndian (ret.extract 0 32) -
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat) <
      UInt256.size) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixNumerator
      (.ok { contract := contract, locals := (ammSwap0AfterNumeratorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have heval := ammSwap0EvalNumerator
    (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    hfit
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterDenominatorStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)) }
      evm2 [.letDecl "kNumerator" (some uint256)
        (checkedMul (.storage reserve1Ref) (.var "amount0In"))]
      (.ok { contract := contract, locals := (ammSwap0AfterNumeratorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simpa [ammSwap0AfterNumeratorStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil)
  exact execBlock_append hprefix htail

theorem ammSwap0EvalNumeratorVar
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterNumeratorStore I b ret out r0 r1 }
      evm (.var "kNumerator") =
      .ok (.int (Int.ofNat (r1.toNat *
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))) := by
  simp [ammSwap0AfterNumeratorStore, evalExpr?, EvalResult.ofOption]

theorem ammSwap0EvalDenominatorVar
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterNumeratorStore I b ret out r0 r1 }
      evm (.var "kDenominator") =
      .ok (.int (Int.ofNat (r0.toNat +
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))) := by
  have hget : (ammSwap0AfterNumeratorStore I b ret out r0 r1).get? "kDenominator" =
      some (.int (Int.ofNat (r0.toNat +
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))) := by
    unfold ammSwap0AfterNumeratorStore
    rw [store_get_ne (ammSwap0AfterDenominatorStore I b ret out r0)
      (k := "kNumerator") (a := "kDenominator") _ (by decide)]
    simp [ammSwap0AfterDenominatorStore]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

def ammSwap0AfterQuotientStore (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray) (r0 r1 : UInt256) : Store :=
  (ammSwap0AfterNumeratorStore I b ret out r0 r1).insert "maxAmount1Out"
    (.int (Int.ofNat
      ((r1.toNat *
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)) /
       (r0.toNat +
        (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)))))

def ammSwap0SourcePrefixQuotient : List Stmt :=
  ammSwap0SourcePrefixNumerator ++
    checkedDivInto "maxAmount1Out" (.var "kNumerator") (.var "kDenominator")

theorem ammSwap0SourceQuotientOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixNumerator
      (.ok { contract := contract, locals := (ammSwap0AfterNumeratorStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hdenom : 0 <
      (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat +
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat)) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixQuotient
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have hnum := ammSwap0EvalNumeratorVar (evm := evm2) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
  have hden := ammSwap0EvalDenominatorVar (evm := evm2) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
  have hguard := ammEvalNatNeZero_true hden hdenom
  have hdiv := ammEvalNatDiv_ok hnum hden hdenom
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterNumeratorStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 (checkedDivInto "maxAmount1Out" (.var "kNumerator") (.var "kDenominator"))
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    simp only [checkedDivInto]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [ammSwap0AfterQuotientStore, collapseReturns] using
      (ExecBlock.consNormal (ExecStmt.letDecl hdiv) ExecBlock.nil)
  simpa [ammSwap0SourcePrefixQuotient, List.append_assoc] using
    (execBlock_append hprefix htail)

theorem ammSwap0EvalAmountAfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm (.var "amount1Out") =
      .ok (.int (Int.ofNat (ammSwap0AmountWord I).toNat)) := by
  have hget : (ammSwap0AfterQuotientStore I b ret out r0 r1).get?
      "amount1Out" = some (.int (Int.ofNat (ammSwap0AmountWord I).toNat)) := by
    unfold ammSwap0AfterQuotientStore ammSwap0AfterNumeratorStore
      ammSwap0AfterDenominatorStore ammSwap0AfterAmount0InStore
      ammSwap0AfterBalance1Store ammSwap0AfterBalance0Store
      ammSwap0AfterTransferStore
    repeat rw [store_get_ne _ _ (by decide)]
    simp [ammSwap0Store, store_get_self]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap0EvalMaxAfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm (.var "maxAmount1Out") =
      .ok (.int (Int.ofNat
        ((r1.toNat *
          (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)) /
         (r0.toNat +
          (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))))) := by
  simp [ammSwap0AfterQuotientStore, evalExpr?, EvalResult.ofOption]

theorem ammSwap0EvalKGuard_true
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (hle : (ammSwap0AmountWord I).toNat ≤
      (r1.toNat * (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)) /
        (r0.toNat + (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat))) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm (.binary .le (.var "amount1Out") (.var "maxAmount1Out")) =
      .ok (.bool true) :=
  ammEvalNatLe_true ammSwap0EvalAmountAfterQuotient
    ammSwap0EvalMaxAfterQuotient hle

theorem ammSwap0EvalKGuard_false
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (hbad : (r1.toNat *
      (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)) /
      (r0.toNat + (fromByteArrayBigEndian (ret.extract 0 32) - r0.toNat)) <
      (ammSwap0AmountWord I).toNat) :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm (.binary .le (.var "amount1Out") (.var "maxAmount1Out")) =
      .ok (.bool false) :=
  ammEvalNatLe_false ammSwap0EvalAmountAfterQuotient
    ammSwap0EvalMaxAfterQuotient hbad

def ammSwap0SourcePrefixKGuard : List Stmt :=
  ammSwap0SourcePrefixQuotient ++
    [.require (.binary .le (.var "amount1Out") (.var "maxAmount1Out"))]

theorem ammSwap0SourceKGuardOk
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixQuotient
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hle : (ammSwap0AmountWord I).toNat ≤
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat *
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat)) /
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat +
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat))) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixKGuard
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 [.require (.binary .le (.var "amount1Out") (.var "maxAmount1Out"))]
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2) := by
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue (ammSwap0EvalKGuard_true hle)) ExecBlock.nil
  exact execBlock_append hprefix htail

theorem ammSwap0SourceKGuardRevert
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixQuotient
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hbad :
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩).toNat *
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat)) /
      ((Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat +
        (fromByteArrayBigEndian (ret.extract 0 32) -
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩).toNat)) <
      (ammSwap0AmountWord I).toNat) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body .reverted := by
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 (swap0Transition.body.drop 13) .reverted := by
    simp only [swap0Transition, nonpayable, checkedDivInto,
      tokenBalance, List.cons_append, List.nil_append, List.drop]
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (ammSwap0EvalKGuard_false hbad))
  have hblock := execBlock_append hprefix htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm swap0Transition.body .reverted := by
    simpa [ammSwap0SourcePrefixQuotient,
      ammSwap0SourcePrefixNumerator, ammSwap0SourcePrefixDenominator,
      ammSwap0SourcePrefixAmount0In, ammSwap0SourcePrefixInputGuard,
      ammSwap0SourcePrefixBalance1, ammSwap0SourcePrefixBalance0,
      ammSwap0SourcePrefixTransfer, ammSwap0SourcePrefixRecipient,
      ammSwap0SourcePrefixLiquidity, swap0Transition, nonpayable,
      checkedDivInto, List.cons_append, List.nil_append, List.drop,
      List.append_assoc] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hbody

theorem ammSwap0EvalBalance0AfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm (.var "balance0") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) := by
  have hget : (ammSwap0AfterQuotientStore I b ret out r0 r1).get?
      "balance0" = some (.int (Int.ofNat
        (fromByteArrayBigEndian (ret.extract 0 32)))) := by
    unfold ammSwap0AfterQuotientStore ammSwap0AfterNumeratorStore
      ammSwap0AfterDenominatorStore ammSwap0AfterAmount0InStore
      ammSwap0AfterBalance1Store
    repeat rw [store_get_ne _ _ (by decide)]
    simp [ammSwap0AfterBalance0Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

theorem ammSwap0EvalBalance1AfterQuotient
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256} :
    evalExpr? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm (.var "balance1") =
      .ok (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
  have hget : (ammSwap0AfterQuotientStore I b ret out r0 r1).get?
      "balance1" = some (.int (Int.ofNat
        (fromByteArrayBigEndian (out.extract 0 32)))) := by
    unfold ammSwap0AfterQuotientStore ammSwap0AfterNumeratorStore
      ammSwap0AfterDenominatorStore ammSwap0AfterAmount0InStore
    repeat rw [store_get_ne _ _ (by decide)]
    simp [ammSwap0AfterBalance1Store]
  rw [Std.HashMap.get?_eq_getElem?] at hget
  simp [evalExpr?, hget, EvalResult.ofOption]

def ammSwap0AfterReserve0 (evm : EVM.State) (ret : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))

theorem ammSwap0AssignReserve0
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (hretLo : 32 ≤ ret.size) :
    assignStorageRef? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        ammSwap0AfterQuotientStore I b ret out r0 r1 },
        ammSwap0AfterReserve0 evm ret) := by
  have hword : (UInt256.ofNat
      (fromByteArrayBigEndian (ret.extract 0 32))).toNat =
      fromByteArrayBigEndian (ret.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hretLo)
  have hstore : storageLocStore evm (wordLoc ⟨5⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))) =
      some (ammSwap0AfterReserve0 evm ret) := by
    simpa [ammSwap0AfterReserve0, hword] using
      ammStorageLocStore_uint256 evm ⟨5⟩
        (UInt256.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      ammSwap0AfterQuotientStore I b ret out r0 r1 })
    (evm := evm) (evm' := ammSwap0AfterReserve0 evm ret)
    (slot := reserve0Ref)
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32)))
    (by simp [ammSwap0AfterQuotientStore, ammSwap0AfterNumeratorStore,
      ammSwap0AfterDenominatorStore, ammSwap0AfterAmount0InStore,
      ammSwap0AfterBalance1Store, ammSwap0AfterBalance0Store,
      ammSwap0AfterTransferStore, ammSwap0Store, reserve0Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

def ammSwap0SourcePrefixReserve0 : List Stmt :=
  ammSwap0SourcePrefixKGuard ++
    [.assign .storage reserve0Ref (.var "balance0")]

theorem ammSwap0SourceReserve0Ok
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixKGuard
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hretLo : 32 ≤ ret.size) :
    ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixReserve0
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        (ammSwap0AfterReserve0 evm2 ret)) := by
  have heval := ammSwap0EvalBalance0AfterQuotient
    (evm := evm2) (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
  have hassign := ammSwap0AssignReserve0
    (evm := evm2) (I := I) (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    hretLo
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      evm2 [.assign .storage reserve0Ref (.var "balance0")]
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        (ammSwap0AfterReserve0 evm2 ret)) := by
    exact ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  exact execBlock_append hprefix htail

def ammSwap0AfterReserve1 (evm : EVM.State) (out : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))

theorem ammSwap0AssignReserve1
    {evm : EVM.State} {I : ExecutionEnv} {b : Bool}
    {ret out : ByteArray} {r0 r1 : UInt256}
    (houtLo : 32 ≤ out.size) :
    assignStorageRef? config
      { contract := contract, locals := ammSwap0AfterQuotientStore I b ret out r0 r1 }
      evm .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      .ok ({ contract := contract, locals :=
        ammSwap0AfterQuotientStore I b ret out r0 r1 },
        ammSwap0AfterReserve1 evm out) := by
  have hword : (UInt256.ofNat
      (fromByteArrayBigEndian (out.extract 0 32))).toNat =
      fromByteArrayBigEndian (out.extract 0 32) := by
    exact ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt houtLo)
  have hstore : storageLocStore evm (wordLoc ⟨6⟩)
      (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) =
      some (ammSwap0AfterReserve1 evm out) := by
    simpa [ammSwap0AfterReserve1, hword] using
      ammStorageLocStore_uint256 evm ⟨6⟩
        (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
  exact assignStorageRef_storage_scalar
    (cfg := config)
    (solm := { contract := contract, locals :=
      ammSwap0AfterQuotientStore I b ret out r0 r1 })
    (evm := evm) (evm' := ammSwap0AfterReserve1 evm out)
    (slot := reserve1Ref)
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (n := Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (by simp [ammSwap0AfterQuotientStore, ammSwap0AfterNumeratorStore,
      ammSwap0AfterDenominatorStore, ammSwap0AfterAmount0InStore,
      ammSwap0AfterBalance1Store, ammSwap0AfterBalance0Store,
      ammSwap0AfterTransferStore, ammSwap0Store, reserve1Ref])
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl) hstore

theorem ammSwap0SourceSuccess
    {evm evm2 : EVM.State} (I : ExecutionEnv) (b : Bool)
    (ret out : ByteArray)
    (hprefix : ExecBlock config
      { contract := contract, locals := ammSwap0Store I }
      evm ammSwap0SourcePrefixKGuard
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) } evm2))
    (hretLo : 32 ≤ ret.size) (houtLo : 32 ≤ out.size) :
    ExecTransitionBody config contract evm (ammSwap0Store I)
      swap0Transition.body
      (.returned { contract := contract, locals := (ammSwap0AfterQuotientStore
          I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        (ammSwap0AfterReserve1 (ammSwap0AfterReserve0 evm2 ret) out) none) := by
  have hreserve0 := ammSwap0SourceReserve0Ok I b ret out hprefix hretLo
  have heval := ammSwap0EvalBalance1AfterQuotient
    (evm := ammSwap0AfterReserve0 evm2 ret) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
  have hassign := ammSwap0AssignReserve1
    (evm := ammSwap0AfterReserve0 evm2 ret) (I := I)
    (b := b) (ret := ret) (out := out)
    (r0 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
    (r1 := Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)
    houtLo
  have htail : ExecBlock config
      { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
        (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
      (ammSwap0AfterReserve0 evm2 ret)
      [.assign .storage reserve1Ref (.var "balance1")]
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        (ammSwap0AfterReserve1 (ammSwap0AfterReserve0 evm2 ret) out)) :=
    ExecBlock.consNormal (ExecStmt.assign heval hassign) ExecBlock.nil
  have hblock := execBlock_append hreserve0 htail
  have hbody : ExecBlock config
      { contract := contract, locals := ammSwap0Store I } evm
      swap0Transition.body
      (.ok { contract := contract, locals := (ammSwap0AfterQuotientStore
          I b ret out
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨5⟩)
          (Solm.EVM.storageLoad evm2 evm2.executionEnv.codeOwner ⟨6⟩)) }
        (ammSwap0AfterReserve1 (ammSwap0AfterReserve0 evm2 ret) out)) := by
    simpa [ammSwap0SourcePrefixReserve0, ammSwap0SourcePrefixKGuard,
      ammSwap0SourcePrefixQuotient, ammSwap0SourcePrefixNumerator,
      ammSwap0SourcePrefixDenominator, ammSwap0SourcePrefixAmount0In,
      ammSwap0SourcePrefixInputGuard, ammSwap0SourcePrefixBalance1,
      ammSwap0SourcePrefixBalance0, ammSwap0SourcePrefixTransfer,
      ammSwap0SourcePrefixRecipient, ammSwap0SourcePrefixLiquidity,
      swap0Transition, nonpayable, checkedDivInto,
      tokenTransfer, tokenBalance, List.cons_append,
      List.nil_append, List.append_assoc] using hblock
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockOK hbody

end Benchmarks.ActAmm
