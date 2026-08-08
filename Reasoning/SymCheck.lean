import Reasoning.ReachExact
import Reasoning.MemCascade
import Lean
import Mathlib.Tactic.Ring.RingNF

/-!
# SymCheck proof declarations

This module contains the small trusted-by-the-kernel (but otherwise untrusted) declaration layer
used by generated SymCheck block files.  SymCheck emits a typed starting cursor and an `evm_run`
term.  Lean infers the exact result of that term and this command records it as an opaque theorem.
-/

open Lean Elab Command Term Meta

register_option symcheck.compactIndices : Bool := {
  defValue := true
  descr := "normalize inferred RDx step and gas indices in evm_theorem declarations"
}

private def normalizeNatIndex (e : Expr) : MetaM Simp.Result := do
  try
    let cfg : Mathlib.Tactic.RingNF.Config := { failIfUnchanged := false }
    let result ← Mathlib.Tactic.AtomM.run cfg.red (Mathlib.Tactic.RingNF.evalExpr e)
    Mathlib.Tactic.RingNF.cleanup cfg result
  catch _ =>
    pure { expr := e }

private def simpResultProof (original : Expr) (result : Simp.Result) : MetaM Expr :=
  result.proof?.getDM (mkEqRefl original)

/-- Normalize only the trailing step/cost indices of an inferred exact-reachability result.

The proof is transported through the corresponding opaque normalization theorem. Other result
arguments—including stack and memory expressions—are never passed to the ring normalizer. -/
private def compactReachabilityResult (value : Expr) : MetaM Expr := do
  let type ← inferType value
  let fn := type.getAppFn
  let args := type.getAppArgs
  let some name := fn.constName? | return value
  if name == ``Reasoning.Reach.RDx && args.size == 12 then
    let rawK := args[10]!
    let rawC := args[11]!
    let normK ← normalizeNatIndex rawK
    let normC ← normalizeNatIndex rawC
    if normK.proof?.isNone && normC.proof?.isNone then return value
    let hk ← simpResultProof rawK normK
    let hC ← simpResultProof rawC normC
    mkAppM ``Reasoning.Reach.RDx.withIndices #[value, hk, hC]
  else if name == ``Reasoning.Reach.RDxRet && args.size == 6 then
    let rawC := args[5]!
    let normC ← normalizeNatIndex rawC
    if normC.proof?.isNone then return value
    let hC ← simpResultProof rawC normC
    mkAppM ``Reasoning.Reach.RDxRet.withCost #[value, hC]
  else if name == ``Reasoning.Reach.RDxRev && args.size == 4 then
    let rawC := args[3]!
    let normC ← normalizeNatIndex rawC
    if normC.proof?.isNone then return value
    let hC ← simpResultProof rawC normC
    mkAppM ``Reasoning.Reach.RDxRev.withCost #[value, hC]
  else if name == ``Reasoning.Reach.RDxErr && args.size == 5 then
    let rawC := args[4]!
    let normC ← normalizeNatIndex rawC
    if normC.proof?.isNone then return value
    let hC ← simpResultProof rawC normC
    mkAppM ``Reasoning.Reach.RDxErr.withCost #[value, hC]
  else
    pure value

/-- Simplify the consumer-facing conclusion of an `RDx` trace.

This deliberately leaves generated replay theorems untouched.  In a path theorem, `evm_simp`
normalizes accumulated natural-number step/gas expressions, basic `UInt256` arithmetic identities,
and the safe exact/disjoint memory-read rules from `Reasoning.MemCascade`.  Local hypotheses are
available to the simplifier, while `omega` discharges concrete window and bounds side conditions.
`ring_nf` is applied only after those semantic rewrites, primarily to collect the natural-number
constants introduced by a chain of opcode steppers.
-/
macro "evm_simp" : tactic =>
  `(tactic|
    simp (disch := omega) only [*,
        Nat.add_assoc,
        Nat.add_comm,
        Nat.add_left_comm,
        Reasoning.Theory.u256_add_assoc,
        Reasoning.Theory.u256_add_comm,
        Reasoning.Theory.u256_zero_add,
        Reasoning.Theory.u256_sub_self,
        Reasoning.Theory.u256_lor_zero,
        Reasoning.Theory.writeWord_read_back,
        Reasoning.Theory.writeWord_read_preserved,
        Reasoning.Theory.writeCascade_read_word_of_head,
        Reasoning.Theory.writeCascade_read_preserved,
        Reasoning.Theory.writeCascade_mload_word_of_head,
        Reasoning.Theory.fromByteArrayBigEndian_toByteArray,
        Reasoning.Theory.u256_ofNat_toNat,
        not_false_eq_true,
        if_neg,
        or_false,
        if_false] at * <;>
      ring_nf at * <;>
      try assumption)

/-- Discharge a deterministic not-taken branch condition recognized locally by SymCheck. -/
macro "evm_branch_zero" : tactic =>
  `(tactic|
    first
    | native_decide
    | exact Reasoning.Theory.ugt_zero (by first | rfl | (change 0 ≤ _; omega))
    | exact Reasoning.Theory.ult_zero (by first | rfl | (change 0 ≤ _; omega)))

/-- Declare an opaque theorem whose proposition is inferred from its proof term.

Lean's builtin `theorem` command resolves all holes in the declaration header before elaborating
the proof, so it deliberately cannot infer a missing result type.  Generated RDx traces already
have a uniquely determined result type.  `evm_theorem` elaborates them as Lean would elaborate an
inferred `def`, checks that the result is a proposition, and registers a `thmDecl`.

Before registration it ring-normalizes only the final `RDx` step/gas indices, or the final cost of
an `RDxRet`, `RDxRev`, or `RDxErr`. The original proof is transported through `withIndices` or
`withCost`; stack, memory, and returndata expressions are not normalized. Set
`symcheck.compactIndices` to `false` to retain the raw inferred arithmetic, primarily for
performance comparison and debugging.
-/
syntax (name := evmTheoremCmd)
  "evm_theorem " ident bracketedBinder* " := " term : command

elab_rules : command
  | `(evm_theorem $declId:ident $binders* := $valueStx:term) => do
      Command.liftTermElabM do
        let currNamespace ← getCurrNamespace
        let declName := currNamespace ++ declId.getId
        checkNotAlreadyDeclared declName
        Term.withDeclName declName <| Term.withAutoBoundImplicit do
          Term.elabBinders binders fun xs => do
            let value ← Term.elabTerm valueStx none
            Term.synthesizeSyntheticMVarsNoPostponing
            let value ← instantiateMVars value
            let compactIndices := (← getOptions).getBool `symcheck.compactIndices true
            let value ← if compactIndices then
              let valueType ← inferType value
              forallTelescope valueType fun innerArgs _ => do
                let applied := mkAppN value innerArgs
                let compacted ← compactReachabilityResult applied
                mkLambdaFVars innerArgs compacted
            else
              pure value
            let value ← mkLambdaFVars xs value
            let type ← inferType value
            Term.synthesizeSyntheticMVarsNoPostponing
            let value ← instantiateMVars value
            let type ← instantiateMVars type
            if value.hasMVar || type.hasMVar then
              throwErrorAt valueStx
                "`evm_theorem` left metavariables after elaboration:\nvalue: {value}\ntype: {type}"
            unless (← isProp type) do
              throwErrorAt valueStx "`evm_theorem` proof has non-propositional type:\n{type}"
            let decl := Declaration.thmDecl {
              name := declName
              levelParams := []
              type := type
              value := value
            }
            Term.ensureNoUnassignedMVars decl
            addDecl decl
            addDeclarationRangesFromSyntax declName (← getRef) declId
            Term.addTermInfo' declId (mkConst declName) (isBinder := true)
