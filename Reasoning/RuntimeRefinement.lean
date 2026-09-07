import Reasoning.Refinement

/-!
# From body refinement to runtime equivalence

The RD anchor is the transaction's initial EVM state, while the body-entry cursor may
already be past the bytecode dispatcher. `runtimeExit` compares transaction endpoints,
including the final accounts and return encoding. The bridge consumes incoming RD and
the entry relation; out-of-gas is eliminated inside the bridge.
-/

namespace Reasoning.Refinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

/-- Apply the same function-boundary convention as `ExecFuncBody`: fallthrough (and
escaping break/continue) becomes a return without explicit values. -/
def functionResult : ExecResult → ExecResult
  | .ok frame evm | .break frame evm | .continue frame evm => .returned frame evm none
  | result => result

theorem execFuncBody_of_execBlock {cfg frame evm body result}
    (h : ExecBlock cfg frame evm body result) :
    ExecFuncBody cfg frame evm body (functionResult result) := by
  cases result with
  | ok => exact .execBlockOK h
  | returned => exact .execBlockRet h
  | reverted => exact .execBlockRevert h
  | «break» => exact .execBlockBreak h
  | «continue» => exact .execBlockContinue h

/-- The observable relation required at a transaction boundary. A reached cursor is
not yet a transaction result: any bytecode return epilogue must be proved first.
Supports ABI and raw fallback return conventions, and arbitrary account changes. -/
def runtimeExit (convention : ReturnConvention) (result : ExecResult)
    (endpoint : Endpoint) : Prop :=
  match functionResult result, endpoint with
  | .returned _ evm value, .returned world out =>
      world.1 = evm.createdAccounts ∧ accountMapEquiv world.2 evm.accountMap ∧
        returnDataEquiv out value convention
  | .reverted, .reverted => True
  | _, _ => False

/-- Dispatch-independent bridge. `hexec` lifts the proved body execution into the
chosen selector, receive, or fallback execution. A stronger body postcondition can
be used by supplying `hpost`. The source and EVM witnesses remain available until
this final conversion to `runtimeEquivalenceFor`. -/
theorem BlockProgress.toRuntimeEquivalenceFor
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code ee frame evm body Q convention}
    (h : BlockProgress code ee g (initState cA gh bl σ_evm σ₀ g A I)
      cfg frame evm body Q)
    (hcode : I.code = code)
    (hexec : ∀ result, ExecFuncBody cfg frame evm body result →
      solmExec cfg contract cA gh bl σ_solm σ₀ g.toUInt256 A I result convention)
    (hpost : ∀ result endpoint, Q result endpoint → runtimeExit convention result endpoint) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  rcases h with ⟨result, endpoint, hblock, hreach, hQ⟩
  have hsolm := hexec _ (execFuncBody_of_execBlock hblock)
  have hmatch := hpost _ _ hQ
  unfold runtimeExit at hmatch
  cases endpoint with
  | reached cur =>
    cases hresult : functionResult result <;> simp only [hresult] at hmatch
  | returned world out =>
    rcases hreach with hoog | ⟨s, hX, hworld⟩
    · exact .outOfGas (Xi_error_of_X (g := g.toUInt256) (by
        rw [← hcode] at hoog
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
    · have hxi := Xi_success_of_X (g := g.toUInt256) (by
        rw [← hcode] at hX
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
      cases hresult : functionResult result <;> simp only [hresult] at hmatch hsolm
      rcases hmatch with ⟨hcreated, haccounts, hreturn⟩
      refine .execution hxi hsolm (.success rfl rfl ?_ ?_ hreturn)
      · exact (congrArg Prod.fst hworld).trans hcreated
      · simpa only [← congrArg Prod.snd hworld] using haccounts
  | reverted =>
    rcases hreach with hoog | ⟨gas, out, hX⟩
    · exact .outOfGas (Xi_error_of_X (g := g.toUInt256) (by
        rw [← hcode] at hoog
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
    · have hxi := Xi_revert_of_X (g := g.toUInt256) (by
        rw [← hcode] at hX
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
      cases hresult : functionResult result <;> simp only [hresult] at hmatch hsolm
      exact .execution hxi hsolm (.revert rfl rfl)

/-- Local body refinement with an explicit dispatch lift. Incoming RD ties the
body cursor to the same initial EVM state used by the runtime judgement. -/
theorem BlockRefinesFrom.toRuntimeEquivalenceForOfExec
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code ee cur k C frame evm P body Q convention}
    (hbody : BlockRefinesFrom code ee g (initState cA gh bl σ_evm σ₀ g A I)
      cfg cur k C frame evm P body Q)
    (hRD : RD code ee g (initState cA gh bl σ_evm σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP : P cur frame evm)
    (hcode : I.code = code)
    (hexec : ∀ result, ExecFuncBody cfg frame evm body result →
      solmExec cfg contract cA gh bl σ_solm σ₀ g.toUInt256 A I result convention)
    (hpost : ∀ result endpoint, Q result endpoint → runtimeExit convention result endpoint) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I :=
  (hbody hRD hP).toRuntimeEquivalenceFor hcode hexec hpost

/-- A selector-dispatched function body refines the runtime at fixed transaction
inputs. The source starts with decoded arguments and its initial transaction state;
the EVM starts the body at any cursor reached by `hRD`. No restrictions on whether
the contract also declares receive/fallback functions are needed. -/
theorem BlockRefinesFrom.toRuntimeEquivalenceFor
    {cfg contract cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    {code ee cur k C P Q} {transition : TransitionDecl} {callargs : Store}
    (hbody : BlockRefinesFrom code ee g (initState cA gh bl σ_evm σ₀ g A I)
      cfg cur k C { contract := contract, locals := callargs }
      (initState cA gh bl σ_solm σ₀ g A I) P transition.body Q)
    (hRD : RD code ee g (initState cA gh bl σ_evm σ₀ g A I)
      cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hP : P cur { contract := contract, locals := callargs }
      (initState cA gh bl σ_solm σ₀ g A I))
    (hcode : I.code = code)
    (hdispatch : selectorDispatchMsg contract I.calldata = some transition)
    (hdecode : decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
      (transitionSignature transition).paramTypes I.calldata = some callargs)
    (hpost : ∀ result endpoint, Q result endpoint →
      runtimeExit (.abi transition.returnType) result endpoint := by intros; assumption) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g.toUInt256 A I := by
  apply hbody.toRuntimeEquivalenceForOfExec hRD hP hcode (convention := .abi transition.returnType)
  · intro result hfunc
    exact .intro hdispatch rfl hdecode (by
      simp [initState, Sat256.ofUInt256, Sat256.toUInt256]) hfunc
  · exact hpost

end Reasoning.Refinement
