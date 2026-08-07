import Reasoning.ReachExact
import Lean

/-!
# SymCheck proof declarations

This module contains the small trusted-by-the-kernel (but otherwise untrusted) declaration layer
used by generated SymCheck block files.  SymCheck emits a typed starting cursor and an `evm_run`
term.  Lean infers the exact result of that term and this command records it as an opaque theorem.
-/

open Lean Elab Command Term Meta

/-- Declare an opaque theorem whose proposition is inferred from its proof term.

Lean's builtin `theorem` command resolves all holes in the declaration header before elaborating
the proof, so it deliberately cannot infer a missing result type.  Generated RDx traces already
have a uniquely determined result type.  `evm_theorem` elaborates them as Lean would elaborate an
inferred `def`, checks that the result is a proposition, and registers a `thmDecl`.
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
