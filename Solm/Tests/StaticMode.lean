import Solm.Equiv

/-! Regression checks for static-mode failures and propagation. -/

namespace Solm.Tests.StaticMode

private theorem eval_pure (x : α) : (pure x : EvalResult α) = .ok x := rfl

-- Runtime and both constructor relations accept the EVM exception.
example (rc : ReturnConvention) :
    execResultsEquiv (.error .StaticModeViolation) .reverted rc :=
  .staticModeViolation rfl rfl

example (code : ByteArray) :
    ctorResultEquiv (.error .StaticModeViolation) .reverted code :=
  .staticModeViolation rfl rfl

example (codeOf : Store → Option ByteArray) :
    ctorResultEquivWith (.error .StaticModeViolation) .reverted codeOf :=
  .staticModeViolation rfl rfl

-- Hooks cannot bypass the static check, regardless of layout or hook implementation.
example (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (bs : ByteArray)
    (hp : evm.executionEnv.perm = false) :
    writeStorage? cfg evm er .bytes (.bytes bs) = .revert ∧
    writeStorage? cfg evm er .string (.bytes bs) = .revert ∧
    clearStorage? cfg evm er .bytes = .revert ∧
    clearStorage? cfg evm er .string = .revert := by
  simp [writeStorage?, clearStorage?, storageWriteHookToEval, hp]

-- The guard also applies to a hook reached through a structured assignment.
example (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) (bs : ByteArray)
    (hp : evm.executionEnv.perm = false) :
    writeStorage? cfg evm er (.array .bytes 1) (.array [.bytes bs]) = .revert := by
  simp [writeStorage?, writeArrayElems?, storageWriteHookToEval, hp]

-- A writable hook still returns its chosen state.
example (cfg : Config) (evm evm' : EVM.State) (er : EvaledStorageRef) (bs : ByteArray)
    (hp : evm.executionEnv.perm = true)
    (hw : cfg.storage.writeValue? er .bytes (.bytes bs) evm = some (.ok evm')) :
    writeStorage? cfg evm er .bytes (.bytes bs) = .ok evm' := by
  simp [writeStorage?, storageWriteHookToEval, storagePrepareResultToEval, hp, hw]

-- Invalid hooks remain model errors in writable mode.
example (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef)
    (hp : evm.executionEnv.perm = true)
    (hw : cfg.storage.clearValue? er .bytes evm = none) :
    clearStorage? cfg evm er .bytes = .error .storageError := by
  simp [clearStorage?, storageWriteHookToEval, hp, hw]

-- A no-op mapping deletion is still allowed: no storage write is attempted.
example (cfg : Config) (evm : EVM.State) (er : EvaledStorageRef) :
    clearStorage? cfg evm er (.mapping .bool .bytes) = .ok evm := by
  simp [clearStorage?]

private theorem call_permission {evm target value calldata result perm}
    (h : callViaEVM evm target value calldata result perm) :
    callPermissionAllowed evm value perm := by
  cases h <;> assumption

private theorem typed_call_permission {cfg evm target name value args result perm}
    (h : typedCallViaEVM cfg evm target name value args result perm) :
    callPermissionAllowed evm value perm := by
  obtain ⟨_, _, hc⟩ := h
  exact call_permission hc

private theorem static_value_denied (evm : EVM.State) (perm : Bool)
    (hp : evm.executionEnv.perm = false) : ¬ callPermissionAllowed evm 1 perm := by
  simpa [callPermissionAllowed, hp] using (show EVM.wordOfInt 1 ≠ ⟨0⟩ by decide)

-- Neither bridge constructor may turn a forbidden transfer into a normal call result,
-- including the insufficient-balance/depth failure path.
example (evm : EVM.State) (target : EVM.Address) (calldata : EVM.Bytes)
    (result : Bool × EVM.State × EVM.Bytes) (perm : Bool)
    (hp : evm.executionEnv.perm = false) :
    ¬ callViaEVM evm target 1 calldata result perm := by
  intro h
  exact static_value_denied evm perm hp (call_permission h)

-- Zero-value calls are allowed in either mode; writable CALL may transfer value.
example (evm : EVM.State) (perm : Bool) : callPermissionAllowed evm 0 perm :=
  Or.inr rfl

example (evm : EVM.State) (value : Int) (hp : evm.executionEnv.perm = true) :
    callPermissionAllowed evm value true := by
  simp [callPermissionAllowed, hp]

-- In a static caller, ordinary CALL has exactly the same bridge behavior as STATICCALL.
-- In particular, the Theta witness must use a read-only callee in both directions.
example (evm : EVM.State) (target : EVM.Address) (value : Int) (calldata : EVM.Bytes)
    (result : Bool × EVM.State × EVM.Bytes) (hp : evm.executionEnv.perm = false) :
    callViaEVM evm target value calldata result true ↔
      callViaEVM evm target value calldata result false := by
  constructor <;> intro h <;> cases h with
  | callMade ha hv hc he hb hd =>
      exact .callMade (by simpa [callPermissionAllowed, hp] using ha) hv
        (by simpa [hp] using hc) he hb hd
  | callNotMade ha hs he hn =>
      exact .callNotMade (by simpa [callPermissionAllowed, hp] using ha) hs he hn

-- STATICCALL cannot send value even from a writable caller.
example (evm : EVM.State) : ¬ callPermissionAllowed evm 1 false := by
  simpa [callPermissionAllowed] using (show EVM.wordOfInt 1 ≠ ⟨0⟩ by decide)

-- A low-level CALL's own permission failure reverts instead of binding `ok = false`.
example (cfg : Config) (frame : Frame) (evm : EVM.State)
    (hp : evm.executionEnv.perm = false) :
    ExecStmt cfg frame evm
      (.lowLevelCall (.env .this) (.intLit 1) (.bytesLit .empty) "ok" "data") .reverted := by
  refine .lowLevelCallPermissionRevert (target := evm.executionEnv.codeOwner)
    (sendVal := 1) (calldata := .empty) ?_ ?_ ?_ (static_value_denied evm true hp)
  all_goals simp [evalExpr?, envValue, eval_pure]

example (cfg : Config) (frame : Frame) (evm : EVM.State) (result : ExecResult)
    (hp : evm.executionEnv.perm = false)
    (hr : ExecStmt cfg frame evm
      (.lowLevelCall (.env .this) (.intLit 1) (.bytesLit .empty) "ok" "data") result) :
    result = .reverted := by
  cases hr <;> simp_all [evalExpr?, envValue, eval_pure]
  all_goals
    subst_vars
    have hallowed := call_permission (by assumption)
    exact False.elim (static_value_denied evm true hp hallowed)

-- The checked-call failure likewise cannot enter either user branch.
example (cfg : Config) (frame : Frame) (evm : EVM.State) (yes no : List Stmt)
    (hp : evm.executionEnv.perm = false) :
    ExecStmt cfg frame evm
      (.checkedCall (.env .this) "f" (.intLit 1) [] "ret" yes "err" no) .reverted := by
  refine .checkedCallPermissionRevert (target := evm.executionEnv.codeOwner)
    (sendVal := 1) (argVals := []) ?_ ?_ ?_ (static_value_denied evm true hp)
  all_goals simp [evalExpr?, evalExprs?, envValue, eval_pure]

example (cfg : Config) (frame : Frame) (evm : EVM.State) (yes no : List Stmt)
    (result : ExecResult) (hp : evm.executionEnv.perm = false)
    (hr : ExecStmt cfg frame evm
      (.checkedCall (.env .this) "f" (.intLit 1) [] "ret" yes "err" no) result) :
    result = .reverted := by
  cases hr <;> simp_all [evalExpr?, evalExprs?, envValue, eval_pure]
  all_goals
    subst_vars
    have hallowed := typed_call_permission (by assumption)
    exact False.elim (static_value_denied evm true hp hallowed)

example (cfg : Config) (frame : Frame) (evm : EVM.State)
    (hp : evm.executionEnv.perm = false) :
    ExecStmt cfg frame evm
      (.externalCall (.env .this) "f" (.intLit 1) [] "ret") .reverted := by
  refine .externalCallPermissionRevert (target := evm.executionEnv.codeOwner)
    (sendVal := 1) (argVals := []) ?_ ?_ ?_ (static_value_denied evm true hp)
  all_goals simp [evalExpr?, evalExprs?, envValue, eval_pure]

-- Both CREATE and CREATE2 fail without changing any state, for any endowment/code/salt.
example (cfg : Config) (evm : EVM.State) (name : Ident) (value : Int) (args : List Value)
    (salt : Option ByteArray) (hp : evm.executionEnv.perm = false) :
    newViaEVM cfg evm name value args salt (EVM.address 0, evm, false) :=
  .staticModeViolation hp

example (cfg : Config) (evm : EVM.State) (name : Ident) (value : Int) (args : List Value)
    (salt : Option ByteArray) (result : EVM.Address × EVM.State × Bool)
    (hp : evm.executionEnv.perm = false)
    (hr : newViaEVM cfg evm name value args salt result) :
    result = (EVM.address 0, evm, false) := by
  cases hr <;> simp_all

example (cfg : Config) (frame : Frame) (evm : EVM.State) (salt : Option Expr)
    (saltBytes : Option ByteArray) (hp : evm.executionEnv.perm = false)
    (hs : evalSalt? cfg frame evm salt = .ok saltBytes) :
    ExecStmt cfg frame evm (.new "C" (.intLit 0) [] "address" salt) .reverted := by
  refine .newRevert (sendVal := 0) (argVals := []) ?_ ?_ hs (.staticModeViolation hp)
  all_goals simp [evalExpr?, evalExprs?, eval_pure]

end Solm.Tests.StaticMode
