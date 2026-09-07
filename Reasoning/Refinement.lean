import Reasoning.Reach
import Reasoning.SolmBody

/-!
# Statement refinement over RD

`BlockProgress` packages a concrete paired result: a Solm execution, an EVM endpoint,
and their relation. Out-of-gas stays inside EVM reachability; the source execution
and relation are always established. It can be assembled from separate RD
and source proofs, preserving the actual state witnesses for subsequent reasoning.

`BlockRefinesFrom` fixes a starting cursor, RD counters, and source state. It takes
incoming RD evidence and a starting relation and produces `BlockProgress`.
`StmtsRefine code ee g s0 cfg pc P stmts Q` universally quantifies this local judgement
over starting pairs at `pc`. Sequencing passes the prefix's actual intermediate cursor,
source state, RD evidence and relation to the continuation.

The endpoint relation chooses the bytecode exits for each source result: fallthrough,
`break`, `continue`, return, or revert. In particular, a source return can correspond to
an internal return cursor as well as a transaction halt. State agreement, including
account-map equivalence, is supplied by the relations rather than fixed by the judgement.

This is a refinement with an existential source execution, not a requirement that every
Solm execution match the EVM. Calls can therefore choose their existential gas and
substate to match the bytecode. The execution context `code`, `ee`, `g`, and `s0` stays
fixed across a proof, as it does for `RD`; reusable rules can quantify over that context.
-/

namespace Reasoning.Refinement

open Solm Ethereum Ethereum.EVM Reasoning.Reach

/-- A relation between a bytecode cursor and the source frame and EVM-backed state.
Entry/exit PCs, stack and memory encodings, and world agreement belong in this relation.
It does not require the two account maps to be syntactically equal. -/
abbrev StateRel := Cursor → Frame → State → Prop

/-- An EVM endpoint at a statement boundary. A reached cursor need not be a transaction
halt: it can be the next statement, a loop exit, or an internal return address.
Terminal reverts forget their bytes, matching `RDrev` and Solm's stateless `.reverted`. -/
inductive Endpoint where
  | reached (cur : Cursor)
  | returned (world : Batteries.RBSet AccountAddress compare × AccountMap) (out : ByteArray)
  | reverted

/-- Relates a source result to an EVM endpoint. The source result retains its frame,
state, and return values where present. The relation specifies both the endpoint mapping
and the required post-state agreement; unsupported outcomes can be mapped to `False`. -/
abbrev ExitRel := ExecResult → Endpoint → Prop

/-- The out-of-gas alternative for the fixed EVM run underlying an `RD` proof. -/
def OutOfGas (code : ByteArray) (g : Sat256) (s0 : State) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass

/-- Lift the existing RD cursor and terminal judgements to a common endpoint type.
Step and gas counters at a reached endpoint are existential, so source postconditions
need not mention them. Like the underlying RD judgements, this admits out-of-gas. -/
def ReachesEndpoint (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State) :
    Endpoint → Prop
  | .reached cur =>
      ∃ k C, RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C
  | .returned world out => RDret code g s0 world out
  | .reverted => RDrev code g s0

/-- Concrete paired progression from a particular source frame and state. The witnesses
are the source result (including its resulting state), the EVM endpoint, execution
evidence on both sides, and their relation. They can be constructed from separate RD
and Solm proofs or obtained by applying a reusable refinement theorem. -/
def BlockProgress (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (frame : Frame) (evm : State) (stmts : List Stmt) (Q : ExitRel) : Prop :=
  ∃ result endpoint,
    ExecBlock cfg frame evm stmts result ∧
    ReachesEndpoint code ee g s0 endpoint ∧ Q result endpoint

/-- Refinement from a particular starting pair. Incoming RD evidence connects `cur`
to the execution anchored at `s0`; `P` connects that cursor to the source frame/state.
The starting pair and counters are fixed, while the resulting states remain exposed
through `BlockProgress`. Prove this judgement with `intro hRD hP`, then advance the
bytecode and source executions separately or apply a paired rule. -/
def BlockRefinesFrom (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (cur : Cursor) (k C : ℕ) (frame : Frame) (evm : State)
    (P : StateRel) (stmts : List Stmt) (Q : ExitRel) : Prop :=
  RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C →
  P cur frame evm →
  BlockProgress code ee g s0 cfg frame evm stmts Q

/-- Advance only the EVM, preserving the source frame and state. The witness can
contain a cursor, counters, or values discovered by RD; no gas split is exposed. -/
theorem BlockRefinesFrom.ofRD {code ee g s0 cfg cur k C frame evm P stmts Q R}
    {α : Type} {next : α → Cursor} {steps costs : α → ℕ}
    (hstep : RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C →
      P cur frame evm → ∃ a, RD code ee g s0 (next a).pc (next a).stack
        (next a).mem (next a).aw (next a).rdata (next a).world (steps a) (costs a) ∧
        R (next a) frame evm)
    (hnext : ∀ a, BlockRefinesFrom code ee g s0 cfg (next a) (steps a) (costs a)
      frame evm R stmts Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P stmts Q := by
  intro rd hp
  obtain ⟨a, rd', hr⟩ := hstep rd hp
  exact hnext a rd' hr

/-- The EVM cursor after GAS, with its concrete result exposed to the continuation. -/
def gasCursor (cur : Cursor) (gas : UInt256) : Cursor :=
  { cur with pc := cur.pc + ⟨1⟩, stack := gas :: cur.stack }

/-- Execute GAS without advancing the source. The entry relation is retained at
the old cursor; the continuation can inspect the new cursor and pushed gas word. -/
theorem BlockRefinesFrom.gas {code ee g s0 cfg cur k C frame evm P stmts Q}
    (hdec : decode code cur.pc = some (.GAS, .none)) (hov : cur.stack.length + 1 ≤ 1024)
    (hnext : ∀ gas, BlockRefinesFrom code ee g s0 cfg (gasCursor cur gas) (k + 1) (C + 2)
      frame evm (fun _ f e => P cur f e) stmts Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P stmts Q := by
  apply BlockRefinesFrom.ofRD (next := gasCursor cur) (steps := fun _ => k + 1)
    (costs := fun _ => C + 2) (R := fun _ f e => P cur f e) ?_ hnext
  intro rd hp
  obtain ⟨gas, rd'⟩ := rd.rawGas hdec hov
  exact ⟨gas, rd', hp⟩

/-- Package separately proved Solm and RD block effects, after comparing their states. -/
theorem BlockProgress.ofRD {code ee g s0 cfg frame evm stmts result Q}
    {cur : Cursor} {k C : ℕ}
    (hblock : ExecBlock cfg frame evm stmts result)
    (hRD : RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hQ : Q result (.reached cur)) :
    BlockProgress code ee g s0 cfg frame evm stmts Q :=
  ⟨result, .reached cur, hblock, ⟨k, C, hRD⟩, hQ⟩

/-- Package a separately proved source statement and EVM endpoint as block progression. -/
theorem BlockProgress.ofStmt {code ee g s0 cfg frame evm stmt result endpoint Q}
    (hstmt : ExecStmt cfg frame evm stmt result)
    (hreach : ReachesEndpoint code ee g s0 endpoint) (hQ : Q result endpoint) :
    BlockProgress code ee g s0 cfg frame evm [stmt] Q := by
  refine ⟨result, endpoint, ?_, hreach, hQ⟩
  cases result with
  | ok => exact ExecBlock.consNormal hstmt ExecBlock.nil
  | returned => exact ExecBlock.consReturn hstmt
  | reverted => exact ExecBlock.consRevert hstmt
  | «break» => exact ExecBlock.consBreak hstmt
  | «continue» => exact ExecBlock.consContinue hstmt

/-- Prepend a normally completing source statement to concrete paired progression.
The EVM prefix is already included in the RD evidence anchored at `s0`. -/
theorem BlockProgress.cons {code ee g s0 cfg frame evm frame' evm' stmt stmts Q}
    (hstmt : ExecStmt cfg frame evm stmt (.ok frame' evm'))
    (hrest : BlockProgress code ee g s0 cfg frame' evm' stmts Q) :
    BlockProgress code ee g s0 cfg frame evm (stmt :: stmts) Q := by
  rcases hrest with ⟨r, ep, hblock, hreach, hQ⟩
  exact ⟨r, ep, ExecBlock.consNormal hstmt hblock, hreach, hQ⟩

/-- Bind a word exposed by an RD summary to a source `gasleft()` declaration,
without stepping the EVM again. The summary may already have moved the word off
the stack. Solm permits any gas word; its agreement with the bytecode belongs in
the continuation's postcondition. Preserve the entry relation at the original
source frame, since inserting the local need not preserve an arbitrary `P`. -/
theorem BlockRefinesFrom.letGasOfRD {code ee g s0 cfg cur k C frame evm P name stmts Q}
    (gas : UInt256)
    (hnext : BlockRefinesFrom code ee g s0 cfg cur k C
      { frame with locals := frame.locals.insert name (.int (Int.ofNat gas.toNat)) }
      evm (fun c _ e => P c frame e) stmts Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P (.letGas name :: stmts) Q := by
  intro rd hp
  exact BlockProgress.cons (ExecStmt.letGas gas) (hnext rd hp)

/-- Pair EVM GAS with a source `gasleft()` declaration. The continuation receives
the same word on the EVM stack and in the source local, with counters advanced by
one step and two gas. The entry relation is retained at the original cursor and
frame. Out-of-gas remains inside RD, without a gas case split in the continuation. -/
theorem BlockRefinesFrom.letGas {code ee g s0 cfg cur k C frame evm P name stmts Q}
    (hdec : decode code cur.pc = some (.GAS, .none)) (hov : cur.stack.length + 1 ≤ 1024)
    (hnext : ∀ gas, BlockRefinesFrom code ee g s0 cfg (gasCursor cur gas) (k + 1) (C + 2)
      { frame with locals := frame.locals.insert name (.int (Int.ofNat gas.toNat)) }
      evm (fun _ _ e => P cur frame e) stmts Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P (.letGas name :: stmts) Q := by
  apply BlockRefinesFrom.gas hdec hov
  intro gas
  exact BlockRefinesFrom.letGasOfRD gas (hnext gas)

/-- Attach a normally completing source prefix to paired suffix progression.
The suffix's RD evidence already includes the bytecode prefix, anchored at `s0`. -/
theorem BlockProgress.prepend {code ee g s0 cfg frame evm frame' evm' front tail Q}
    (hfront : ExecBlock cfg frame evm front (.ok frame' evm'))
    (htail : BlockProgress code ee g s0 cfg frame' evm' tail Q) :
    BlockProgress code ee g s0 cfg frame evm (front ++ tail) Q := by
  rcases htail with ⟨r, ep, hb, hr, hQ⟩
  exact ⟨r, ep, Reasoning.Theory.execBlock_append hfront hb, hr, hQ⟩

/-- Sequence a manually proved prefix with a refinement from its concrete endpoint.
Supply the source execution, intermediate RD and state agreement separately. The
continuation fixes that exact cursor, counters and source state; it need not be a
universally quantified `StmtsRefine`. This is useful after introducing a local
refinement's incoming RD and extracting intermediate witnesses during manual stepping. -/
theorem BlockProgress.seqOfRD {code ee g s0 cfg frame evm front tail Q R}
    {cur' : Cursor} {k' C' : ℕ} {frame' : Frame} {evm' : State}
    (hsource : ExecBlock cfg frame evm front (.ok frame' evm'))
    (hRD : RD code ee g s0 cur'.pc cur'.stack cur'.mem cur'.aw cur'.rdata cur'.world k' C')
    (hR : R cur' frame' evm')
    (htail : BlockRefinesFrom code ee g s0 cfg cur' k' C' frame' evm' R tail Q) :
    BlockProgress code ee g s0 cfg frame evm (front ++ tail) Q :=
  BlockProgress.prepend hsource (htail hRD hR)

/-- Fixed-start sequencing using raw RD and source execution for the prefix.
The prefix derives source execution, intermediate RD and agreement from the incoming
RD and `P`. RD handles out-of-gas internally; the source evidence is always required.
The intermediate pair is fixed,
so the continuation is one `BlockRefinesFrom` judgement rather than `StmtsRefine`.
If manual stepping discovers existential intermediate states or counters, introduce
the incoming hypotheses first and use `BlockProgress.seqOfRD` on those witnesses. -/
theorem BlockRefinesFrom.seqOfRD {code ee g s0 cfg cur k C frame evm P front tail Q R}
    {cur' : Cursor} {k' C' : ℕ} {frame' : Frame} {evm' : State}
    (hfront :
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C →
      P cur frame evm →
      ExecBlock cfg frame evm front (.ok frame' evm') ∧
      RD code ee g s0 cur'.pc cur'.stack cur'.mem cur'.aw cur'.rdata cur'.world k' C' ∧
      R cur' frame' evm')
    (htail : BlockRefinesFrom code ee g s0 cfg cur' k' C' frame' evm' R tail Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P (front ++ tail) Q := by
  intro rd hP
  rcases hfront rd hP with ⟨hsource, rd', hR⟩
  exact BlockProgress.seqOfRD hsource rd' hR htail

/-- Replace a source prefix by a statement implementing that prefix. This is used by
checked calls: their selected handler runs before the enclosing block's tail, while
return, revert, break and continue skip that tail. -/
theorem BlockProgress.wrapPrefix {code ee g s0 cfg frame evm branchFrame branchEvm stmt stmts Q}
    {branch : List Stmt}
    (hwrap : ∀ result, ExecBlock cfg branchFrame branchEvm branch result →
      ExecStmt cfg frame evm stmt result)
    (h : BlockProgress code ee g s0 cfg branchFrame branchEvm (branch ++ stmts) Q) :
    BlockProgress code ee g s0 cfg frame evm (stmt :: stmts) Q := by
  have lift : ∀ branch branchFrame branchEvm result,
      (∀ r, ExecBlock cfg branchFrame branchEvm branch r → ExecStmt cfg frame evm stmt r) →
      ExecBlock cfg branchFrame branchEvm (branch ++ stmts) result →
      ExecBlock cfg frame evm (stmt :: stmts) result := by
    intro branch
    induction branch with
    | nil =>
        intro f e r hw hb
        exact ExecBlock.consNormal (hw _ ExecBlock.nil) hb
    | cons head tail ih =>
        intro f e r hw hb
        cases hb with
        | consNormal hs ht =>
            exact ih _ _ _ (fun r hr => hw r (ExecBlock.consNormal hs hr)) ht
        | consReturn hs => exact ExecBlock.consReturn (hw _ (ExecBlock.consReturn hs))
        | consRevert hs => exact ExecBlock.consRevert (hw _ (ExecBlock.consRevert hs))
        | consBreak hs => exact ExecBlock.consBreak (hw _ (ExecBlock.consBreak hs))
        | consContinue hs => exact ExecBlock.consContinue (hw _ (ExecBlock.consContinue hs))
  rcases h with ⟨r, ep, hb, hr, hQ⟩
  exact ⟨r, ep, lift branch branchFrame branchEvm r hwrap hb, hr, hQ⟩

/-- Bytecode at `pc` refines `stmts`, from the starting relation `P` to the endpoint
relation `Q`, within the fixed RD execution context.

For each related starting pair, a matching source execution is constructed together
with its EVM endpoint. `Q` handles all five `ExecResult` constructors, including
`break` and `continue`, without imposing a particular loop or return convention.

Out-of-gas is handled by the EVM endpoint judgement. Source execution and `Q` are
required even then. World and execution-environment agreement needed by individual
rules must be included in `P` and preserved through `Q` where required. -/
def StmtsRefine (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (cfg : Config) (pc : UInt256) (P : StateRel) (stmts : List Stmt) (Q : ExitRel) : Prop :=
  ∀ cur k C frame evm,
    cur.pc = pc →
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P stmts Q

/-- Normal completion at a specified bytecode PC, with a related source state. -/
def fallthrough (pc : UInt256) (R : StateRel) : ExitRel
  | .ok frame evm, .reached cur => cur.pc = pc ∧ R cur frame evm
  | _, _ => False

/-- Sequence after a normally completing prefix. The continuation receives the
actual intermediate cursor, source frame/state, RD counters and starting relation. -/
theorem BlockProgress.seq {code ee g s0 cfg frame evm front tail pc R Q}
    (hfront : BlockProgress code ee g s0 cfg frame evm front (fallthrough pc R))
    (htail : StmtsRefine code ee g s0 cfg pc R tail Q) :
    BlockProgress code ee g s0 cfg frame evm (front ++ tail) Q := by
  rcases hfront with ⟨result, endpoint, hb, hr, hrel⟩
  cases result <;> cases endpoint <;> simp only [fallthrough] at hrel
  rename_i frame' evm' cur
  obtain ⟨hpc, hR⟩ := hrel
  obtain ⟨k, C, rd⟩ := hr
  exact BlockProgress.prepend hb (htail cur k C frame' evm' hpc rd hR)

/-- Fixed-start sequencing: prove the prefix from the incoming RD and `P`, then
prove the suffix from each intermediate pair satisfying `R` at `pc`. -/
theorem BlockRefinesFrom.seq {code ee g s0 cfg cur k C frame evm P front tail pc R Q}
    (hfront : BlockRefinesFrom code ee g s0 cfg cur k C frame evm P front (fallthrough pc R))
    (htail : StmtsRefine code ee g s0 cfg pc R tail Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P (front ++ tail) Q := by
  intro rd hP
  exact BlockProgress.seq (hfront rd hP) htail

/-- A prefix's normal result reaches the suffix entry and satisfies `R`. Every
non-normal result already satisfies the enclosing `Q` and bypasses the suffix. -/
def sequenceExit (pc : UInt256) (R : StateRel) (Q : ExitRel) : ExitRel
  | .ok frame evm, endpoint => fallthrough pc R (.ok frame evm) endpoint
  | result, endpoint => Q result endpoint

/-- Sequence a prefix that may return, revert, break or continue before the suffix.
Only normal completion invokes the continuation; other outcomes keep their endpoint. -/
theorem BlockProgress.seqOrExit {code ee g s0 cfg frame evm front tail pc R Q}
    (hfront : BlockProgress code ee g s0 cfg frame evm front (sequenceExit pc R Q))
    (htail : StmtsRefine code ee g s0 cfg pc R tail Q) :
    BlockProgress code ee g s0 cfg frame evm (front ++ tail) Q := by
  rcases hfront with ⟨result, endpoint, hb, hr, hrel⟩
  cases result with
  | ok frame' evm' =>
      cases endpoint <;> simp only [sequenceExit, fallthrough] at hrel
      rename_i cur
      obtain ⟨hpc, hR⟩ := hrel
      obtain ⟨k, C, rd⟩ := hr
      exact BlockProgress.prepend hb (htail cur k C frame' evm' hpc rd hR)
  | returned f e value =>
      exact ⟨_, endpoint,
        Reasoning.Theory.execBlock_append_term hb (by intros; intro h; cases h), hr, hrel⟩
  | reverted =>
      exact ⟨_, endpoint,
        Reasoning.Theory.execBlock_append_term hb (by intros; intro h; cases h), hr, hrel⟩
  | «break» f e =>
      exact ⟨_, endpoint,
        Reasoning.Theory.execBlock_append_term hb (by intros; intro h; cases h), hr, hrel⟩
  | «continue» f e =>
      exact ⟨_, endpoint,
        Reasoning.Theory.execBlock_append_term hb (by intros; intro h; cases h), hr, hrel⟩

/-- Fixed-start sequencing with early exits from the prefix. -/
theorem BlockRefinesFrom.seqOrExit {code ee g s0 cfg cur k C frame evm P front tail pc R Q}
    (hfront : BlockRefinesFrom code ee g s0 cfg cur k C frame evm P front (sequenceExit pc R Q))
    (htail : StmtsRefine code ee g s0 cfg pc R tail Q) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm P (front ++ tail) Q := by
  intro rd hP
  exact BlockProgress.seqOrExit (hfront rd hP) htail

/-- Route a loop body's normal/continue outcomes to the post-step. A break becomes
normal loop completion; returns and reverts use the enclosing loop's exit relation. -/
def forBodyExit (postHeader : UInt256) (PostInv : StateRel) (Q : ExitRel) : ExitRel
  | .ok frame evm, endpoint | .continue frame evm, endpoint =>
      fallthrough postHeader PostInv (.ok frame evm) endpoint
  | .break frame evm, endpoint => Q (.ok frame evm) endpoint
  | .returned frame evm values, endpoint => Q (.returned frame evm values) endpoint
  | .reverted, endpoint => Q .reverted endpoint

/-- Route a successful post-step back to the header with the decreased invariant.
Solm permits a post-step to fall through or revert, but not to return, break, or continue. -/
def forPostExit (header : UInt256) (Inv : StateRel) (Q : ExitRel) : ExitRel
  | .ok frame evm, endpoint => fallthrough header Inv (.ok frame evm) endpoint
  | .reverted, endpoint => Q .reverted endpoint
  | _, _ => False

section ForLoop

variable {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State} {cfg : Config}
    (header bodyHeader postHeader : UInt256) (cond : Expr) (post body : List Stmt)
    (Inv BodyInv PostInv : ℕ → StateRel) (Q : ExitRel)
    (hfalse : ∀ cur frame evm, Inv 0 cur frame evm →
      evalExpr? cfg frame evm cond = .ok (.bool false))
    (htrue : ∀ v cur frame evm, Inv (v + 1) cur frame evm →
      evalExpr? cfg frame evm cond = .ok (.bool true))
    (hexit : StmtsRefine code ee g s0 cfg header (Inv 0) [] Q)
    (henter : ∀ v, StmtsRefine code ee g s0 cfg header (Inv (v + 1)) []
      (fallthrough bodyHeader (BodyInv v)))
    (hbody : ∀ v, StmtsRefine code ee g s0 cfg bodyHeader (BodyInv v) body
      (forBodyExit postHeader (PostInv v) Q))
    (hpost : ∀ v, StmtsRefine code ee g s0 cfg postHeader (PostInv v) post
      (forPostExit header (Inv v) Q))

include hfalse htrue hexit henter hbody hpost

/-- Variant-indexed paired loop progression, using statement refinements for its
bytecode segments. `hexit` and `henter` refine empty source blocks: they execute the
bytecode guard without changing the source state. At variant `v + 1`, the body and
post-step use `BodyInv v` and `PostInv v`, and a successful post-step restores `Inv v`.

Normal/continue body outcomes run the post-step; break skips it and exits normally.
Body returns/reverts and post-step reverts propagate through `Q`. The guard is required
to evaluate successfully, as in `RD.execForLoopOrRevertCarryFull`. All cursor fields,
including accounts and return data, may change through the supplied relations. -/
theorem execForLoop :
    ∀ v cur k C frame evm,
      cur.pc = header →
      RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C →
      Inv v cur frame evm →
      ∃ result endpoint,
        ExecForLoop cfg frame evm cond post body result ∧
        ReachesEndpoint code ee g s0 endpoint ∧ Q result endpoint := by
  intro v
  induction v with
  | zero =>
      intro cur k C frame evm hpc hRD hInv
      rcases hexit cur k C frame evm hpc hRD hInv with ⟨r, ep, hnil, hreach, hQ⟩
      cases hnil
      exact ⟨_, ep, ExecForLoop.falseDone (hfalse cur frame evm hInv), hreach, hQ⟩
  | succ v ih =>
      intro cur k C frame evm hpc hRD hInv
      have hcond := htrue v cur frame evm hInv
      rcases henter v cur k C frame evm hpc hRD hInv with
        ⟨r, ep, hnil, hreach, hEntry⟩
      cases hnil
      cases ep with
      | returned => exact False.elim hEntry
      | reverted => exact False.elim hEntry
      | reached curBody =>
          obtain ⟨hpcBody, hInvBody⟩ := hEntry
          obtain ⟨kBody, CBody, rdBody⟩ := hreach
          -- Share the post-step and recursive tail between normal and continue outcomes.
          have resume : ∀ frame1 evm1 ep1,
              (ExecBlock cfg frame evm body (.ok frame1 evm1) ∨
                ExecBlock cfg frame evm body (.continue frame1 evm1)) →
              ReachesEndpoint code ee g s0 ep1 →
              fallthrough postHeader (PostInv v) (.ok frame1 evm1) ep1 →
              ∃ result endpoint,
                ExecForLoop cfg frame evm cond post body result ∧
                ReachesEndpoint code ee g s0 endpoint ∧ Q result endpoint := by
            intro frame1 evm1 ep1 hBody hReach hPostInv
            cases ep1 with
            | returned => exact False.elim hPostInv
            | reverted => exact False.elim hPostInv
            | reached curPost =>
                obtain ⟨hpcPost, hInvPost⟩ := hPostInv
                obtain ⟨kPost, CPost, rdPost⟩ := hReach
                rcases hpost v curPost kPost CPost frame1 evm1 hpcPost rdPost hInvPost with
                  ⟨r2, ep2, hPost, hReach2, hExit2⟩
                cases r2 with
                | returned => exact False.elim hExit2
                | «break» => exact False.elim hExit2
                | «continue» => exact False.elim hExit2
                | reverted =>
                    rcases hBody with hOk | hCont
                    · exact ⟨_, ep2, ExecForLoop.iteratePostRevert hcond hOk hPost,
                        hReach2, hExit2⟩
                    · exact ⟨_, ep2, ExecForLoop.continuePostRevert hcond hCont hPost,
                        hReach2, hExit2⟩
                | ok frame2 evm2 =>
                    cases ep2 with
                    | returned => exact False.elim hExit2
                    | reverted => exact False.elim hExit2
                    | reached curNext =>
                        obtain ⟨hpcNext, hInvNext⟩ := hExit2
                        obtain ⟨kNext, CNext, rdNext⟩ := hReach2
                        rcases ih curNext kNext CNext frame2 evm2 hpcNext rdNext hInvNext with
                          ⟨r3, ep3, hLoop, hReach3, hExit3⟩
                        rcases hBody with hOk | hCont
                        · exact ⟨r3, ep3, ExecForLoop.iterate hcond hOk hPost hLoop,
                            hReach3, hExit3⟩
                        · exact ⟨r3, ep3, ExecForLoop.continueIter hcond hCont hPost hLoop,
                            hReach3, hExit3⟩
          rcases hbody v curBody kBody CBody frame evm hpcBody rdBody hInvBody with
            ⟨r1, ep1, hBody, hReach1, hExit1⟩
          cases r1 with
          | ok frame1 evm1 => exact resume frame1 evm1 ep1 (Or.inl hBody) hReach1 hExit1
          | «continue» frame1 evm1 => exact resume frame1 evm1 ep1 (Or.inr hBody) hReach1 hExit1
          | «break» frame1 evm1 =>
              exact ⟨_, ep1, ExecForLoop.bodyBreak hcond hBody, hReach1, hExit1⟩
          | returned frame1 evm1 values =>
              exact ⟨_, ep1, ExecForLoop.bodyReturn hcond hBody, hReach1, hExit1⟩
          | reverted =>
              exact ⟨_, ep1, ExecForLoop.bodyRevert hcond hBody, hReach1, hExit1⟩

/-- A loop at `header` refines the singleton Solm `for` block, using the same
statement-refinement interface as its body and post-step. The initializer is empty:
this rule starts at the loop header after initialization, just like the RD loop rule. -/
theorem BlockProgress.forLoop (v : ℕ) (cur : Cursor) (k C : ℕ) (frame : Frame) (evm : State)
    (hpc : cur.pc = header)
    (hRD : RD code ee g s0 cur.pc cur.stack cur.mem cur.aw cur.rdata cur.world k C)
    (hInv : Inv v cur frame evm) :
    BlockProgress code ee g s0 cfg frame evm [.for [] cond post body] Q := by
  rcases execForLoop header bodyHeader postHeader cond post body Inv BodyInv PostInv Q
      hfalse htrue hexit henter hbody hpost v cur k C frame evm hpc hRD hInv with
    ⟨result, endpoint, hLoop, hReach, hQ⟩
  exact BlockProgress.ofStmt (ExecStmt.for ExecBlock.nil hLoop) hReach hQ

/-- The paired loop rule as a refinement from a fixed entry pair. -/
theorem BlockRefinesFrom.forLoop (v : ℕ) (cur : Cursor) (k C : ℕ) (frame : Frame) (evm : State)
    (hpc : cur.pc = header) :
    BlockRefinesFrom code ee g s0 cfg cur k C frame evm (Inv v) [.for [] cond post body] Q :=
  BlockProgress.forLoop header bodyHeader postHeader cond post body Inv BodyInv PostInv Q
    hfalse htrue hexit henter hbody hpost v cur k C frame evm hpc

/-- Universally quantify the concrete loop progression over related starting pairs. -/
theorem StmtsRefine.forLoop (v : ℕ) :
    StmtsRefine code ee g s0 cfg header (Inv v) [.for [] cond post body] Q :=
  BlockRefinesFrom.forLoop header bodyHeader postHeader cond post body Inv BodyInv PostInv Q
    hfalse htrue hexit henter hbody hpost v

end ForLoop

end Reasoning.Refinement
