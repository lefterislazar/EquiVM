# Agent prompt — proving EVM↔Solm correctness for a contract

You are proving that a concrete EVM bytecode artifact refines its Solm
specification. Your goal is to complete the proof of the top-level theorem
in `Correct.lean` with no `sorry` and no added axioms, except for the
accepted trusted base below.

You are given a working directory, which is named after the contract
(`<Name>/`) and includes:

- The EVM bytecode (file `Bytecode.lean`).

- Proved RD block summaries in generated `RuntimeBlocks_*.lean` and
  `CreationBlocks_*.lean` shards, with compact theorem indexes
  `RuntimeBlocks.index` and `CreationBlocks.index`. Treat them as proof
  inputs: inspect their statements and compose them, but do not regenerate
  or edit them.

- The source it was compiled from (e.g., `<Name>.sol`), plus the exact
  compiler and options used to produce it. The bytecode can be of
  arbitrary provenance — do not assume a specific compiler or
  version. Always check.

- The Solm specification of the contract, including its storage
  layout. (file `Spec.lean`)

- A correctness file stating the top-level theorem with a `sorry`
  placeholder. (file `Correct.lean`)

The top-level theorem bundles the correctness of the constructor:

```lean
constructorEquivalence <config> <initcode> <contract> <runtimeBytecode>
```

and the correctness of the runtime code:

```lean
runtimeEquivalence <config> <runtimeBytecode> <contract>
```

Your goal is to complete the proof. The proof must be correct,
modular, fast enough to work on, and axiom-clean except for the
accepted trusted base below.

### Generated RD block summaries

Use the generated summaries before writing a bytecode trace by hand:

- Search the generated files for `_block_<pc>` to locate the theorem for a
  block's entry program counter, then import the shard containing it.
- Read the theorem's stack, memory, account-map, and side-condition binders;
  generated summaries start from a symbolic `RD` cursor and may require facts
  such as stack capacity, jump-destination membership, permissions, or branch
  conditions.
- A `_taken` or `_fallthrough` suffix identifies the corresponding `JUMPI`
  branch. Terminal summaries conclude with `RDret`, `RDrev`, or `RDinvalid`.
- An `Unsupported instruction boundary` or `Execution split boundary` comment
  means no transition is asserted across that opcode. Continue that part of
  the trace with an applicable library lemma or a local proved helper.


Be forthcoming with blocking issues. Never bypass a problem to move on
to the next proof, and never circumvent it. If you suspect something
is unprovable, investigate thoroughly, report it immediately to the
user, and do not continue until it is resolved.

You should only work in the `<Name>/` directory. Do not make changes
outside of it.

## 1. Overall Workflow

### Phase 0: Evaluate the spec and bytecode

Do a thorough read of the Solm spec and the bytecode. Check that the
Solm spec matches the bytecode's storage reads/writes, arithmetic, and
control flow. If you find a mismatch, report it immediately. After
this pass, you should be confident that the Solm spec is a faithful
model of the bytecode, and that it is possible to prove the
refinement.

Things to watch for:

- The Solm spec, in general, must model storage reads/writes in the
  order the bytecode performs them. This is not a hard rule, for all
  data types. But for mapping, array, string and byte types this is
  important because a different order may require a slot noncollision
  assumption to prove the refinement.

  If you find that you need such an axiom, evaluate whether the Solm can 
  be written 
  differently to exactly model the bytecode's storage reads/writes. 
  If it can, rewrite the Solm spec to do so.

  If reordering the spec's storage operations is insufficient to reflect
  a compiler optimization, and the proof requires a slot noncollision
  assumption, use only the narrow exception in Section 2. Difficulty
  completing a proof is not by itself evidence that an axiom is needed.

- The Solm spec must use helper functions where possible and not
  inline the same logic in multiple places. This is important for
  modularity and reusability of proofs.

- The storage layout in the Solm spec must match the storage layout in
  the bytecode. If there is a mismatch, report it immediately.

### Phase 1: Scaffold the proof

Create the top-level scaffold of the proof in `Correct.lean`. This
includes the dispatch skeleton, the per-function `…BodyCore` lemmas,
and the revert paths. The top-level theorem should type-check and
route correctly before the leaves are done. Reuse the available
machinery drivers for dispatching (e.g., `solcDispatchReachBody`).

1. Add the dispatch handler to the main theorem first. Wire the full
   dispatcher (`by_cases` on `callvalue`/`size`/each selector, routing
   each selector to its per-function `…BodyCore`, plus the shared
   revert paths). This skeleton should type-check and route correctly
   before the leaves are done. Add the necessary ABI selector axiom 
   as needed.

2. For each ABI function `<Fn>`, route to a `…BodyCore` whose proof is
   a `sorry`. That `…BodyCore` should be defined in that function's
   own file `<Fn>.lean`.

3. Create a `…BodyCore` lemma for the constructor in
   `Constructor.lean` file.

4. The skeleton of the proof should now route every function and the
   constructor correctly through the main top-level dispatch.

*Hard rule*: You should set up the dispatch skeleton and the per ABI 
function theorems (initially with `sorry`) in their own files before 
proving any of the functions. 

It is likely that some of the `Examples/` proof templates will be useful 
for this phase. You can use them as a reference for the ABI dispatch skeleton.

### Phase 2: Prove each function

Finish each function's `…BodyCore` lemma in its own `<Fn>.lean`
file. If the proof gets difficult, do not try to bypass the problem
and move to another function. Investigate thoroughly and report
immediately any blocking issues you may find.

The proof of each function follows, roughly, five phases. Paths containing
external or internal calls use the paired refinement workflow described
below instead of postponing the EVM/Solm comparison until the final connect
step.


1. ABI decode. Prove decode succeeds for valid calldata and fails on
   each malformed branch (short / huge / non-canonical address
   lemmas). Use the `decodeCalldata_*` library lemmas
   (`decodeCalldata_address_ok`, `decodeCalldata_uint256_ok`,
   `…_none_short`, `…_none_huge`, `…_none_noncanon`). One `simpa …
   using <lib lemma>` per branch (see `BalanceOf.lean`).

2. Add trusted selector facts for the public selectors in `Trusted.lean`.

3. Solm source body for call-free paths. Prove the `ExecTransitionBody` result (return
   value / storage update / revert) using `Reasoning.SolmBody`
   (`ExecStmt`/`ExecBlock` combinators, `evalExpr_*`, `requireStep`,
   `returns`). For mutating functions, split success and revert
   branches early.

4. EVM reachability for call-free paths. Use the generated RD block summaries as the
   default interface from the body entry PC to `RDret` (success) or
   `RDrev` (revert). Find the relevant block theorem in the generated
   index, read only the listed line range, and chain the summary
   theorems with the existing `RD.*` routine lemmas. In the general
   case where gas, exact step counts, and exact active-word accounting
   are not important for refinement, prefer the `_packed` summary
   theorem. Use direct `evm_run … with [ … ]` stepping only in
   exceptional cases where partial execution inside a block has
   semantic meaning for the proof.

5. Connect. `reEquivExecution` / `reEquivDecodingFailed` /
   `reEquivNoDispatch` / `reEquivElim` glue the source result, the
   decode fact, and the EVM `RDret`/`RDrev` into
   `runtimeEquivalenceFor`.

For a path containing a call, or paths where complicated operations and control-flow
benefit a more coupled proof approach, replace steps 3–5 for that path with a
paired proof based on `Reasoning.Refinement` and
`Reasoning.CallRefinement`:

1. Instantiate the known entry relation. At transaction start,
   `CallStateRel.initState haccounts` supplies the standard world and
   environment agreement. A function-body refinement may start at a
   later cursor reached by dispatcher/ABI-decoder summaries: its
   incoming RD still anchors that cursor to the original transaction
   state. When the cursor and source frame/decoded locals are fixed
   explicitly, the relation can often be just
   `fun cur _ e => CallStateRel s0 ee cur.world e`, with representation
   facts supplied by the concrete arguments and separate hypotheses.
   Define a richer `StateRel` only where a reusable boundary needs to
   describe varying stack shapes, locals, memory, or other invariants;
   do not introduce a new relation for every path entry.

2. Choose the paired-proof judgement by proof shape. Use
   `BlockProgress` for concrete straight-line execution from a known
   cursor; it has less involved hypotheses and is usually enough for
   local prefixes and suffixes. Use `BlockRefinesFrom` when the proof
   must be reusable over an incoming relation or must fit a complex
   control-flow rule, especially loop rules. Use `StmtsRefine` when it
   should be reusable for every related cursor at a PC. Use the
   matching `seqOfRD` variant for the judgement you chose when a prefix
   is most conveniently summarized by separate RD and Solm execution
   facts.

3. Compose the provided block-summary lemmas, or the ones in the 
   reasoning library, to reach semantic boundaries.
   Manual decoding of blocks can happen only if it provides important
   semantics information, but is generally discouraged.
   Summaries may deliberately stop before a source-visible `GAS`, the
   forwarding `GAS` immediately before a CALL-family opcode, the call
   itself, and result-decoder branches.

4. At an external-call boundary, apply the appropriate paired call rule
   in the judgement you are using (`externalCall`, `lowLevelCall`,
   `checkedCall`, or `delegateCall`). Prefer the `BlockProgress` rule
   for concrete straight-line call paths; use the `BlockRefinesFrom`
   rule when a relational/reusable theorem or complex control-flow rule
   requires it. Establish the operand-stack, target, calldata, value,
   and `CallStateRel` hypotheses from the entry relation and the
   provided summaries. The rule synchronizes the EVM call attempt with
   the Solm call and hides the call-depth, balance, gas, and
   callee-outcome case split. For an ordinary typed call, the
   false-status obligation should normally be only `post-call RD →
   RDrev`.

5. Prove the post-call bytecode status and return-decoder paths using
   the provided summaries. A successful continuation receives the
   actual returndata, resulting source state, EVM world, RD counters,
   and `CallStateRel`; use these facts directly in the continuation,
   or package them in a richer relation when needed for a reusable
   suffix. Continue over the remaining Solm statements. Match failed status or failed
   decoding with `RDrev` as required by the call rule.

6. At the function boundary, use the bridge matching the proof you
   built: `BlockProgress.toRuntimeEquivalenceFor` for a concrete paired
   proof, or `BlockRefinesFrom.toRuntimeEquivalenceFor` for a reusable
   relational proof. Call-free dispatcher and malformed-calldata paths
   may continue to use the ordinary connect lemmas.

---

### Phase 3: Prove the constructor

In a similar manner, prove correct the constructor body.

---

### Phase 4: Finish the proof

After you have proved all the functions and the constructor, verify
that the top-level theorem complies with no added axioms and no
`sorry`/`admit`. Report the axiom footprint.

---

## 2. Accepted axioms

The only acceptable trusted facts are:

- The selector / jump-dest facts in `Bytecode.lean` (the selector
  bytes of each function).

- Keccak literals which the compiler has resolved at compile time.

- Slot noncollision axioms, only when reordering the Solm spec's
  storage operations is insufficient to reflect a compiler
  optimization and the refinement requires the assumption. First
  identify the exact conflicting accesses and establish why matching
  their order in the spec cannot resolve the obligation. State only
  the noncollision property needed for those accesses, with explicit
  domain restrictions where applicable; do not assume unrestricted
  injectivity of Keccak. Document the justification beside the axiom
  and report it in the final audit. The resulting correctness theorem
  is conditional on that assumption, which is not a proved property
  of EVM or Keccak.

- The pre-existing library axiom `keccak_size` in
  `Reasoning/Memory.lean` (Keccak output is 32 bytes), used by
  contracts that hash at run time.

- For contracts with external calls: EVMLean's precompile output-size
  axioms (declared in `Ethereum/Theory/ReturnDataBound.lean`). These
  enter the footprint through the return-data size bound of the
  external-call machinery; you never invoke them directly.

Do not introduce new axioms about EVM or Solm semantics. Slot
noncollision axioms are permitted only under the exception above.
For any other new axiom outside this accepted base, stop, report the
situation, and ask for guidance.

---

## 3. File layout

You should work exclusively in a directory `<Name>/` for the contract
you are proving.  The file structure is the following:

The proof of a contract `<Name>` goes in a directory `<Name>/`:

| File | Role |
|---|---|
| `<Name>.sol` | the Solidity source + the exact compiler invocation used. |
| `Spec.lean` | the Solm `ContractDecl`, storage layout, `Config`. |
| `Bytecode.lean` | runtime bytecode + selector/jump-dest trusted facts. |
| `Blocks.lean` | provided proved RD summaries, especially for call-bearing paths; do not regenerate or edit. |
| `Common.lean` | contract-wide ABI / memory / selector / return / other helpers shared by ≥2 functions. |
| `Storage.lean` | contract-wide storage load/store + RBMap preservation + bool-return facts (only if it has storage). |
| `CallTraces.lean` | optional contract-specific composition of provided summaries around call boundaries, status paths, and return decoders. |
| `<Fn>.lean` | one file per interface (public/external) function — its decode, source body, EVM trace, and `…BodyCore` refinement. |
| `Constructor.lean` | the equivalence proof of the contract's constructor. |
| `Correct.lean` | thin top-level: dispatcher driver + per-function routing + revert paths + constructor packaging + the final `theorem <name>Correct`. |


- At least one file per external ABI function. Never put two ABI
  functions' proofs in one file, never fold a function's body proof
  into `Correct.lean` or `Common.lean`, and never let `Correct.lean`
  carry body-specific complexity.

- Shared machinery used by several functions goes in
  `Common.lean`/`Storage.lean`/`Routines.lean`, not in any one
  function's file. Internal/private functions are not ABI
  entries. Their proofs can go into common files or their own
  standalone files.

- You can add further helper files in `<Name>/` for common lemmas and
  helpers.

- **Hard rule:** do not let files grow past 2000 lines. If this
  happens you should split them into smaller files by concern.
  This is important for build speed. 
  You can exceptionally create files larger that 2000 lines 
  ONLY IF ABSOLUTELY NECESSARY AND UNAVOIDABLE.

---

## 4. Reasoning library and reuse

`Reasoning/` is a library of abstractions, lemmas, and tactics for
proving EVM bytecode correct against its Solm spec. Useful reads:

- `Reasoning/STRUCTURE.md` — the library map: where every kind of fact
  lives, import layering, and the gotchas (native_decide for decode,
  `RD.foo rd` not `rd.foo`, heartbeat budgets, etc.).

- Each `Reasoning/*.lean` file's `/-! # … -/` header — per-module
  detail.

How to use the library:

- Respect and extend the library's abstractions. Almost every line should apply a library lemma.
  A reusable, contract-independent fact the library lacks is a missing library lemma. Add it
  (proved) to the current working directory's `Common.lean` (or another local common file), 
  tagged `-- LIBRARY CANDIDATE: <generalizes…>`
  (or `-- GENERALIZES Reasoning.<Module>.<lemma> …` for a near-variant). 

- Never edit `Reasoning/` yourself

- Do not reinvent. The library already discharges the solc prologue,
  non-payable guard, calldata-size guard, selector load,
  `RD.dispatchTo` selector routing, ABI decode/encode, memory/storage
  round-trips, and the `RD`/`RDret`/`RDrev` stepping
  discipline. Almost every line you write should be applying a library
  lemma, not proving EVM semantics from scratch. Before writing any
  arithmetic / calldata / memory / dispatch proof by hand, search for
  an existing lemma.

- Generated RD summaries are the normal way to reason about concrete
  bytecode blocks. Use section 8 for the operational details: what the
  summaries expose, when to prefer `_packed`, and how to read the
  generated index.

- Never duplicate lemmas and proof work. Always search `Reasoning/`
  for existing lemmas before proving a new one.  If you find yourself
  proving the same fact in two places, refactor it into a single lemma
  in a common file.

- You should strive to build generic, modular, and reusable
  infrastructure in your proofs and follow the library abstractions.
  This will make your proofs more maintainable and easier to
  understand.

- After you are done with your proof, someone will evaluate it for
  generality and reusability.  If your lemmas are deemed general
  enough, they will promote your lemmas to the `Reasoning/` library.
  If they find that your lemmas are too specific, they will ask you to
  refactor them into more generic lemmas that can be reused in other
  proofs.

- Lemma hygiene:

  1. Make lemmas useful and general. The new lemmas that you add
     should be as generic as possible, avoiding hard-coded PCs,
     widths, types, and stack tails when possible.

  2. Do not prove anticipated lemmas, unless you are 100% sure they
     will be used in the final proof.

  3. Before introducing a lemma, search `Reasoning/` and the existing
     examples for one that already exists — do not re-prove it.

  4. Never duplicate a lemma. If you find yourself writing the same
     lemma in two places, refactor it into a single lemma in a common
     file. If you find yourself proving similar lemmas in two places,
     consider generalizing the lemma to make it reusable.

  5. Add lemmas in the working directory (shared ones in common
     files), then flag the contract-independent ones for promotion to
     `Reasoning/` (below). Do not add lemmas directly to `Reasoning/`.

- The library is not yet exercised by every Solidity construct. As you
  prove new patterns you will find segments that are
  contract-independent and reusable and can be promoted to the
  library.  When you do:

  1. Make sure the theorem is not already proved in `Reasoning/`. Search first.

  2. If your lemma is a near-miss of an existing one (same shape,
    different PC/width/type/stack tail), that is a generalization
    opportunity: write your version in the common file and mark it `--
    GENERALIZES Reasoning.<Module>.<lemma> — lift by parameterizing
    over <what differs>`, so the library lemma can later be widened to
    subsume both instead of accreting near-duplicates.

  3. If it's genuinely new but contract-independent, mark it a fresh
     `LIBRARY CANDIDATE`.  The goal: every reusable fact ends up in
     one place, tagged with where it belongs in `Reasoning/`, so
     lifting it later is a mechanical move, not a hunt across function
     files.

  4. Collect all candidates in common files per example so the lift is
     mechanical, not a scavenger hunt.

  5. A lemma is library-ready only if it references no example-local
     defs. Watch for per-example abbreviations (`addr`, `uint256`,
     `uint256Int` are redefined in each `Spec.lean`); inline the raw
     type or it won't compile in the library.


---

## 5. Examples

The `Examples/` directory contains a set of template proofs. You can
use them as a reference for your own proof.

Look at the examples to find known patterns and proof templates for 
your proof.

Note that not all examples are derived with the same compiler,
version, and optimization settings. Always check the source and
bytecode for your contract.

The examples may lag behind recent Solm changes (they are migrated in
batches). If an example does not compile, use it as a *reading*
reference for trace/dispatch/proof patterns only — do not build it and
do not copy its conventions blindly. In particular, examples written
before the multi-value-return change show the old return conventions
(`returnType := some T` / `.return e`); the current convention is
lists (`returnType := [T]` / `.return [e]`, multi-value
`.return [a, b]`).

- For an example of binary search dispatch, see `Examples/Ballot`. 
- For an example of linear dispatch, see `Examples/ERC20`.
- For an example of refinement proofs with calls, see `Examples/NestedCaller`.


*Hard rule:* do not import code directly from `Examples/` into your proof. 
If you find yourself needed the same lemma, prove it in your own working 
directory and flag it for promotion to the library if it is general enough.

---

## 6. Function calls, gas paths, and loops

Function calls should be proven modularly. In particular:

- External calls (calls to other contracts):

  Prove a call-bearing path as paired progression. Use
  `BlockProgress` for concrete straight-line call setup and
  continuation paths; use `BlockRefinesFrom` when a reusable relation
  or complex control-flow rule needs that shape. Use `StmtsRefine` for
  statement-level reusable proofs. Do not run the complete EVM and Solm
  paths independently and connect them only after both have terminated.
  Use the provided RD summaries to reach the call setup, retaining the
  concrete cursor/stack/memory facts and `CallStateRel`. Reuse the known
  entry relation; package additional facts into a richer `StateRel`
  when a reusable call-prefix or continuation lemma needs it. Facts
  fixed by concrete theorem arguments need not also be encoded in the
  relation.

  At the CALL-family opcode, apply the matching rule from
  `Reasoning.CallRefinement` in the judgement you are proving:
  `BlockProgress.externalCall`, `.lowLevelCall`, `.checkedCall`, or
  `.delegateCall` for concrete paths, and the corresponding
  `BlockRefinesFrom` rule for relational/reusable paths. These rules
  prove that both sides make the same opaque call and choose the same
  result. They internally handle call depth, insufficient balance,
  forwarded gas, callee execution, returndata, and account-map
  transport. Do not reproduce those case splits in the contract proof.

  The ordinary typed-call rule has two continuations. From status
  `false`, use the provided failure/status summaries to prove `RDrev`;
  this obligation does not need another typed-call hypothesis. From
  status `true`, use the provided returndata and decoder summaries. If
  source ABI decoding fails, prove the corresponding EVM decoder path
  reaches `RDrev`. If it succeeds, continue with the judgement shape
  already chosen for the tail of the source statement list. The
  continuation receives the actual EVM cursor, returndata, resulting
  Solm state, changed world, counters, and `CallStateRel`; do not throw
  those witnesses away and reconstruct them later.

  For static external calls, you may also use the proved fact that the
  accounts storage is preserved by the call.

- Gas paths:

  Treat `GAS` as a paired boundary only when it has source-level
  meaning or supplies a call operand. Use `BlockProgress.letGas` or
  `BlockRefinesFrom.letGas`, matching the judgement you are proving,
  when the source statement at the head of the list is `.letGas`; it
  puts the same gas word on the EVM stack and in the Solm local. Use
  `BlockProgress.gas` or `BlockRefinesFrom.gas` for a
  compiler-inserted forwarding `GAS` before a CALL-family opcode while
  leaving the source state unchanged. If a provided summary has already
  consumed `GAS` and exposes its word, use `BlockProgress.letGasOfRD`
  or `BlockRefinesFrom.letGasOfRD`, matching the current judgement,
  rather than stepping it again.

  A source `gasleft()` followed by a condition should keep the gas word
  in the path relation and branch on that same value on both sides.
  Out-of-gas remains hidden inside RD; do not add a separate
  `OutOfGas` disjunct to every prefix or continuation hypothesis.
  There is no benefit in breaking summaries at unrelated `GAS`
  opcodes that are fully internal to a straight-line routine.

- Internal calls:

  For internal calls, never inline the caller proof manually.
  When in plain RD proof segments,
  prove the callee body once as an ExecFuncBody, then use
  internalCallFunctionReturn or internalCallFunctionRevert to
  discharge the caller’s .internalCall statement by supplying argument
  evaluation, function lookup, parameter binding, and the callee body
  proof.

  During a refinement-style proof, prove its body as `BlockProgress`
  for a concrete straight-line caller, or as `BlockRefinesFrom` /
  `StmtsRefine` when a reusable callee theorem or complex control-flow
  rule needs that shape, with `internalCallExit` describing its return
  and revert endpoints. Apply `BlockProgress.internalCall` or
  `BlockRefinesFrom.internalCall` to match the caller proof. Supply
  argument evaluation, function lookup, parameter binding, the relation
  at the callee entry, and refinements for the caller continuations.
  This is especially important when the internal callee itself contains
  an external call: the callee proof owns that paired call, while
  callers reuse its body refinement.
  If the internal call does not contain an external call itself,
  it may be dealt with as in the plain RD proof segments,
  using the `seqOfRD` variant for the current judgement.

  This is also true when a public function is also called internally
  by another function of the contract. The callee body is proved once,
  and the caller uses the callee’s lemma to discharge its internal
  call.

  Reference: `Examples/Reuse`; larger patterns occur in Ballot and
  BlindAuction.

  If a function `f` is called internally by another function `g`,
  prove `f` before tackling the proof of `g`.


- Loops:

  For simple loops and bytecode-only loops (such as compiler-generated
  copy or encoding routines), use the RD loop rules and available
  block summaries. Prove any corresponding Solm execution separately;
  within a larger refinement proof, compose these facts using
  `BlockProgress.seqOfRD` / `BlockProgress.ofRD` for concrete
  straight-line pieces, or `BlockRefinesFrom.seqOfRD` /
  `BlockRefinesFrom.ofRD` when the surrounding loop/refinement rule
  requires a relational theorem.

  Use the refinement loop rules only for more complex loops that
  benefit from a coupled EVM/Solm proof—for example, bodies with calls
  or several interacting control-flow paths. Such loops may benefit
  even when they contain no calls. State a `StateRel` invariant over
  the relevant source locals, EVM stack shape, and memory facts,
  indexed by a decreasing variant; include `CallStateRel` when needed
  by calls or world agreement. Use `StmtsRefine.forLoopCombined` and
  the provided summaries for the header, body, post, and exit
  boundaries. Prove the body as a reusable paired refinement with the
  appropriate exit relations: `break` goes to the loop tail;
  `continue` and normal body completion execute the post; return and
  revert bypass both.

  `Examples/NestedCaller` is the reference architecture for an
  internal function containing `gasleft()` and an external call, used
  from a loop with break and continue. Use it as a reading reference
  only; do not import or build it from the working proof.

---

## 7. Build discipline, tactics, proof engineering, efficiency

- Every file should compile and should be validated by the build
  system.

- Builds are slow. Only recompile when necessary. Do not make
  pointless recompilation attempts.

- Quick elaboration is important. Prefer `simp only` over `simp`, and
  `native_decide` over `decide`. Avoid tactics that blow up build
  time.

- Don't rebuild the world to check a leaf lemma.

- If your proof is taking too long to compile, you should evaluate
  your tactics and see if you can optimize them.  You may also
  consider splitting the proof into smaller lemmas to improve
  compilation time.

- Develop new lemmas in a small scratch file, not by editing the large
  file in place. Heavy files take minutes to rebuild and every edit
  re-elaborates the whole file. Create a throwaway
  `<Name>/Scratch.lean` in your working directory that imports the real file (so its
  defs/lemmas are in scope, compiled once and cached) and develop the
  new lemma there with fast cycles. Once it compiles clean, move it
  into its proper file and delete the scratch.

- Decode obligations use `native_decide`, not `decide` (~20× faster on
  big bytecode). Generated summaries and `evm_run` cooked steps
  auto-supply it; if you must use raw steps, write `(by native_decide)`
  for decode, `(by decide)` for small side conditions, `(by jump_dest)`
  for jump-dest membership, and `(by evm_ov)` for stack-overflow
  bounds. Keep these — the resulting `native_decide` axiom
  dependencies (`….native_decide.ax_*`) are expected and fine.

- Raise `maxHeartbeats` only on the file/lemma that needs it, with
  `set_option … in` on that one theorem, not globally.

---

## 8. Summary and routine-lemma discipline

Generated block summaries are the first tool for concrete bytecode
reachability. Chain them as small named `have`s, one block/routine at a
time, and keep the proof at the `RD`/`RDret`/`RDrev` boundary.
The summary-generation work has already been done for a proof
directory with supplied `Blocks.lean` files. Do not re-prove a covered
block with `evm_run`, and do not regenerate or edit the summaries.
Compose them into contract-specific path lemmas for reaching call, gas,
decoder, loop, and continuation boundaries. If a required bytecode edge
is not covered, first verify that it is genuinely absent from the
supplied summaries and report the gap.

- Start from the PC you need, search the generated index
  (`RuntimeBlocks.index` or `CreationBlocks.index`), and read the listed
  range only. The index tells you the theorem name, the file, the line
  range, and the PCs covered by the theorem. Do not open a whole
  generated shard unless the range itself points you there.

- Use `_packed` summaries unless refinement depends on gas, exact step
  counts, or exact active-word accounting. Packed summaries are usually
  the right shape for contract refinement because they expose the
  semantic stack, memory, and control-flow result without forcing the
  proof to carry large counter terms.

- Use the generated stack and memory definitions from the same line
  range. They exist specifically so agents do not have to reconstruct
  large final-state terms. If no such definition is present, the final
  stack or memory was trivial enough to inline.

- Every repeated semantic bytecode segment that is not already covered
  cleanly by generated summaries becomes one `RD`-combinator lemma,
  proved once and applied many times. A straight-line segment
  `pc_in → pc_out` over a stack tail `R` becomes a theorem of the form
  `RD code … pc_in (args ++ R) … → ∃ k' C', RD code … pc_out (results
  ++ R) …` (or `→ RDret` / `→ RDrev` for terminal segments). See
  `RD.routine9c`, `RD.routinebb`, `RD.routinecf`,
  `RD.erc20DecodeAddrMask`, `RD.erc20MappingHashSuffix`,
  `RD.erc20RoutineEncodeUint256`.

- These chain directly: `rd |>.routineA … |>.routineB …` (call as
  `RD.foo rd …`, not `rd.foo` — the `RD` type whnf's to an
  `Or`). Factor over a generic tail `R` so the lemma is reused at
  every call site regardless of what else is on the stack.

- Before introducing a new routine lemma, scan for existing generated
  summaries and shared `RD.*` lemmas for solc-common segments
  (decoders, the address mask/cleanup, the mapping-hash `keccak`
  suffix, the uint256 ABI encoder, identity `cleanup_t_*` routines).
  solc emits these once; prove reusable structure once. If two
  functions need the same path, factor it through a summary chain or a
  reusable routine lemma instead of duplicating lower-level steps.

- Generalize hard-coded constants (PCs, widths, types, stack tails)
  into lemma parameters wherever possible, so the lemma is reusable
  across functions. If a lemma is truly contract-independent, flag it
  for promotion to `Reasoning/`.

- Avoid direct whole-block stepping. A large `evm_run` over a compound
  tail blows the heartbeat/`whnf` budget and hides the state terms that
  the generated summaries already name. Direct `evm_run` is reserved
  for exceptional partial-block proofs where stopping before the
  summary's exit PC has semantic content, or for diagnosing a generator
  or bytecode mismatch. In those cases, split the stepping into named
  `have`s and keep the range as small as possible.

Disassemble and use the index — never guess PCs, opcodes, or
jump-dests. The biggest failure mode in these proofs is guessing
contract-specific constants: entry/exit PCs, jump-dest set, selector
bytes, stack shapes, or a cooked opcode sequence for a partial-block
fallback. These are a pure function of the bytecode — one wrong token
fails late and opaquely and wastes a whole cycle. For ordinary block
execution, trust the generated summary and its index entry. When
partial stepping is genuinely needed, read the opcodes from the actual
bytecode by disassembling `Bytecode.lean` (a short script,
`evmasm`/`solc --asm`, or by decoding the byte array), then treat the
trace as "fill in the side-conditions of a known opcode list," not
"invent the opcode list." When a step fails, re-check it against the
summary/index/disassembly first.

---

## 9. Hard rules

- Do not make changes outside of your working directory.

- Do not build examples and benchmarks that are not your own. 
  **This is extremely important**. Builds are extremely expensive and time-consuming.
  Only build your own working directory. 

- If you find misspecifications, mismatches, or unprovable
  obligations, stop and report them immediately. Do not continue until
  they are resolved.

- Edit `Spec.lean` only if you are certain it is wrong, and report the
  change immediately. Do not change the given bytecode or Solidity
  source.

- Never edit `Bytecode.lean`. If you suspect it is wrong, report it
  immediately.

- No `sorry` in the finished proof.

- Introduce new axioms only within the accepted base in Section 2,
  including its restricted slot noncollision exception. For any
  other new axiom, stop, report the situation, and ask for guidance.

---

## 10. Finish checklist

Run, and report results verbatim:

```
lake build <Module>.Correct
rg -n '\b(sorry|admit)\b' <WorkDir>
printf '%s\n' 'import <Module>.Correct' '#print axioms <Namespace>.<name>Correct' | lake env lean --stdin
```

where `<WorkDir>` is your working directory, `<Module>` its Lean module
path, and `<Namespace>` the contract's namespace — e.g. for
`Examples/ERC20/`: `Examples.ERC20`; for `Benchmarks/Dss/Dai/`:
`Benchmarks.Dss.Dai`.

The build must succeed with no `sorry`.

The axiom footprint should contain only
`propext`/`Classical.choice`/`Quot.sound`, the `native_decide`
evaluation axioms (`….native_decide.ax_*`), your contract's
selector/jump-dest facts, and — where applicable — the library axiom
`keccak_size` (contracts that hash at run time) and EVMLean's
precompile output-size axioms (`Ethereum.EVM.ffi_sha256_output_size`,
`Ethereum.EVM.blob*_output_chunks`, …), which enter through the
external-call return-data bound.
Any slot noncollision axioms admitted under Section 2 must also be
listed explicitly, with the affected accesses, why reordering the
spec was insufficient, and a statement that correctness depends on
these assumptions.
(`ByteArray_zeroes_size`, `Theta_returnData_size_lt_2pow138`, and
`typedCallViaEVM_accountMapEquiv` are proved theorems, not axioms —
they do not appear in the footprint.) Flag only anything beyond this
set — a new axiom your work introduced.
