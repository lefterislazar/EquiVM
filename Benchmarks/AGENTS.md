# Refinement proof benchmarks

These instructions apply when the user assigns a benchmark proof or rerun under
`Benchmarks/`. They do not turn an explicit repository development, review, or
benchmark-maintenance request into a proof run. The assigned contract directory
is `<WorkDir>`; paths below are relative to the repository root unless stated
otherwise. Starting in `Benchmarks/` does not authorize editing every benchmark.

This is the benchmark adaptation of `Misc/prompt.md`. Read that file at the start
for detailed proof guidance, and consult relevant sections as needed. For
benchmark runs, this file replaces its rigid phase order, file-size limits, and
requirement to stop all work on a blocked branch. The correctness requirements
and tool guidance remain in force; the benchmark input restrictions below take
precedence over its permission to adjust the specification.

## Objective and boundaries

Complete the supplied top-level theorem in `<WorkDir>/Correct.lean`, proving
`constructorEquivalence` and `runtimeEquivalence` for the supplied bytecode and
Solm specification. Preserve its statement, hypotheses, and coverage. A build
with unfinished proofs is progress, not a completed benchmark.

- Edit proof files and working notes only inside `<WorkDir>`. Read the shared
  libraries and allowed references as needed. Normal Lake build outputs in
  build-cache directories are permitted; do not modify dependency sources,
  toolchains, shared libraries, or build configuration.
- Keep `Bytecode.lean`, Solidity sources, compiler artifacts, and supplied
  `RuntimeBlocks_*.lean` / `CreationBlocks_*.lean` summaries and their indexes
  unchanged. Do not regenerate supplied summaries.
- Treat `Spec.lean`, storage layout, and the target theorem as fixed benchmark
  inputs unless the run explicitly allows specification corrections. Report
  concrete mismatches and the proposed correction; do not silently weaken the
  problem or add assumptions to make a proof pass. Record any authorized change
  as a change to the benchmark input in the final report.
- No `sorry`, `admit`, `sorryAx`, or unapproved axioms in the finished proof or
  its transitive dependencies. Temporary proof holes are allowed during
  development and must remain visible in progress reports.
- Do not edit these instructions or `Misc/prompt.md` during a proof run.

## Benchmark integrity

Use only the inputs supplied for this run, shared library source, and permitted
example templates. General library reuse is expected.

- Do not inspect or recover Git history, objects, refs, reflogs, stashes, other
  branches, or other worktrees. This includes `git log`, `git show`, historical
  diffs, and direct reads of `.git` or an external Git object directory.
- Do not retrieve previous solutions through remotes, the web, connectors,
  other checkouts, backups, agent transcripts, or prior benchmark outputs.
  Do not seek an earlier solution in cached Lean artifacts. Ordinary compilation
  against the supplied shared-library dependencies is allowed.
- Do not read or import other benchmark solutions unless the run explicitly
  lists them as allowed inputs. Restrict searches to `<WorkDir>`, shared
  libraries, and allowed example directories instead of searching the whole
  repository for a solved target.
- The examples listed below are reading references for general patterns. An
  earlier solution of the assigned target remains excluded even if stored under
  `Examples/`. Do not import proof code directly from `Examples/`; prove needed
  helpers locally using the shared library.
- If an excluded solution is exposed accidentally, report the source and extent
  of exposure promptly. Do not present the run as uncontaminated.
- Respect the runner's filesystem and network restrictions. Do not request
  expanded access to recover excluded material. These instructions express the
  evaluation policy; the runner must enforce access restrictions separately.

## Start and resume

At the start, identify `<WorkDir>`, its Lean module path `<Module>`, and the exact
fully qualified target theorem `<Theorem>`. Read the supplied spec, theorem,
bytecode definitions, and compiler metadata. Check storage layout, arithmetic,
control flow, and storage-access order against the actual artifact; do not
assume a compiler version or optimization setting.

Read `Reasoning/STRUCTURE.md` for the library map and relevant module headers
for API details. Use `rg` to find existing lemmas before writing new ones.

Maintain `<WorkDir>/PROOF_STATE.md` throughout this run. Keep it concise and
record the target, input restrictions, completed lemmas, remaining proof holes,
current blocker or failed approach, next concrete steps, accepted assumptions,
and the latest validation commands and results. Update it at meaningful
milestones and before a handoff or compaction when possible. Notes from earlier
benchmark attempts are excluded inputs unless explicitly supplied for this run.

After compaction or resuming this run, reread this `AGENTS.md` and the current
run's `PROOF_STATE.md` before editing. Reopen the relevant `Misc/prompt.md`
sections and theorem statements when details are missing. Check recorded claims
against the files; do not treat a conversation summary as proof evidence. Pass
the same target, input restrictions, and guidance to any delegated agents.

## Proof workflow

Build a thin dispatch scaffold in `Correct.lean` and manageable per-function
`...BodyCore` lemmas, preferably in separate function files. Put constructor
reasoning in `Constructor.lean`; put shared helpers in local `Common.lean`,
`Storage.lean`, `Routines.lean`, or `CallTraces.lean` as appropriate. Choose the
proof order to suit dependencies; prove internal callees once and reuse them.
There is no mandatory scaffold-first gate or numerical file-size limit.

For call-free paths, prove ABI decoding, Solm execution, and EVM reachability,
then connect them. Include malformed calldata, non-payable guards, unknown
selectors, revert paths, and constructor obligations required by the theorem.
For paths with calls, use paired refinement as described below.

Investigate blockers and report concrete mismatches, unsupported boundaries,
or missing library support with evidence. You may continue independent
obligations while a branch is blocked. Never hide the blocked obligation,
claim it is proved, or change the semantics to bypass it. Proof difficulty
alone does not establish that the theorem is false or needs an axiom.

## Available libraries and tools

Use the APIs in the checked-out library; inspect their actual statements before
applying them. `Misc/prompt.md` and `Reasoning/STRUCTURE.md` provide more detail.

| Task | Tools and references |
| --- | --- |
| Library navigation | `Reasoning/STRUCTURE.md`, module headers, and `rg` searches in `Reasoning/`. |
| Dispatcher | `Reasoning.Solc`, `Reasoning.Dispatch`, `solcDispatchReachBody`, and `RD.dispatchTo`. |
| ABI decode and encode | `Reasoning.ABI`; `decodeCalldata_address_ok`, `decodeCalldata_uint256_ok`, and the `_none_short`, `_none_huge`, `_none_noncanon` families. |
| Solm execution | `Reasoning.SolmBody`; `ExecTransitionBody`, `ExecStmt`, `ExecBlock`, `evalExpr_*`, `requireStep`, and `returns`. |
| Concrete EVM reachability | Supplied block summaries, `Reasoning.Reach`, and reusable `RD.*` routine lemmas, ending in `RDret`, `RDrev`, or `RDinvalid`. |
| Connect call-free proofs | `reEquivExecution`, `reEquivDecodingFailed`, `reEquivNoDispatch`, and `reEquivElim` for `runtimeEquivalenceFor`. |
| Paired proofs | `Reasoning.Refinement`, `Reasoning.CallRefinement`, and `Reasoning.RuntimeRefinement`; `BlockProgress`, `BlockRefinesFrom`, and `StmtsRefine`. |
| Word, memory, storage facts | `Reasoning.EVMWord`, `Reasoning.Memory`, `Reasoning.MemCascade`, and `Reasoning.Storage`. |
| Constructor | `Reasoning.Constructor`, `Reasoning.Initcode`, and supplied creation summaries. |
| Small stepping gaps | `evm_run ... with [ ... ]`, `Reasoning.Reach`, and `Reasoning.Stepping`, after checking existing summaries and routines. |
| Side conditions | `native_decide` for bytecode decode, `decide` for small propositions, `jump_dest` for jump membership, and `evm_ov` for stack-capacity bounds. |
| Bytecode inspection | Supplied indexes and actual bytecode disassembly using a local script, `evmasm`, `solc --asm` with the recorded settings, or byte-array decoding, as available. |
| Validation | Targeted `lake build <Module>`, `lake env lean <File>`, `rg`, and Lean's `#print axioms`. |

Reading references from the original prompt: `Examples/Ballot` for binary
dispatch, `Examples/ERC20` for linear dispatch and ABI patterns such as
`BalanceOf.lean`, `Examples/Reuse` for internal-call reuse, `Examples/BlindAuction`
for larger internal-call patterns, and `Examples/NestedCaller` for paired
calls, gas, and loops. Do not build these examples. They may lag behind the
library; current Solm returns use lists (`returnType := [T]`, `.return [e]`).

### Generated RD summaries

- Search `RuntimeBlocks.index` or `CreationBlocks.index` for the required PC;
  read the indicated theorem and line range in its shard. Avoid loading whole
  large generated files. Use the generated stack and memory definitions.
- Read stack, memory, account-map, permission, branch, jump-destination, and
  capacity hypotheses. `_taken` and `_fallthrough` distinguish `JUMPI` branches.
  Prefer `_packed` summaries when exact gas, steps, and active-word counts do
  not matter for refinement.
- Chain summaries as small named facts using existing routine lemmas. Call
  `RD.foo rd ...` rather than `rd.foo`; `RD` unfolds to an `Or`.
- An `Unsupported instruction boundary` or `Execution split boundary` asserts
  no transition across that opcode. Check for an applicable library lemma or
  prove a local helper for the gap. Report missing summaries if required inputs
  were not supplied; do not assume the gap executes successfully.
- Reserve direct `evm_run` stepping for uncovered edges, meaningful partial-block
  boundaries, or diagnosis. Do not re-prove already covered blocks. Disassemble
  actual bytecode before a fallback; never guess PCs, opcodes, jump destinations,
  selectors, or stack shapes.

### Calls, gas, and loops

- Use `BlockProgress` for concrete straight-line paired proofs;
  `BlockRefinesFrom` for proofs over an incoming relation or complex control
  flow; `StmtsRefine` for reusable statement proofs over related cursors.
  Compose separate RD and source facts with the matching `seqOfRD` / `ofRD`.
- Start world agreement with `CallStateRel.initState haccounts` when applicable.
  Keep the RD anchor at the original transaction state. Reuse the entry relation;
  add a richer `StateRel` only when varying stack, locals, memory, or loop
  invariants require it.
- At external calls, apply the matching `externalCall`, `lowLevelCall`,
  `checkedCall`, or `delegateCall` rule from `Reasoning.CallRefinement` in the
  current judgement. Use the appropriate static-call rule for `STATICCALL`.
  These rules synchronize the opaque call and handle depth, balance, gas,
  callee results, and account-map transport. Retain the actual post-call
  witnesses in continuations. Prove status-failure and typed-decoder-failure
  paths reach `RDrev`; continue successful paths using supplied summaries.
- For source `.letGas`, use `letGas`; for compiler forwarding `GAS`, use `gas`;
  when a summary already consumed it, use `letGasOfRD`. Match the judgement and
  branch on the same gas word on both sides. Out-of-gas stays inside RD.
- For internal calls, reuse `ExecFuncBody` with `internalCallFunctionReturn` /
  `internalCallFunctionRevert` on plain RD segments. For paired proofs, use
  `internalCallExit` and the matching `internalCall` rule, proving the callee
  once. A callee containing external calls owns their paired proof.
- Use RD loop rules for simple or bytecode-only loops. For complex coupled
  loops, use `whileLoopCombined` or `forLoopCombined` (empty initializer), a
  related-state invariant, and a decreasing variant. In `for`, normal completion
  and `continue` execute the post; `break` reaches the tail. Return and revert
  bypass the tail. Use summaries for header, body, post, and exit boundaries.
- Close paired function proofs with `BlockProgress.toRuntimeEquivalenceFor`
  or `BlockRefinesFrom.toRuntimeEquivalenceFor`, matching the proof shape.

## Reuse and build discipline

Search the library first. Prove missing helpers locally, parameterizing PCs,
widths, types, and stack tails when useful. Factor repeated routines once.
Tag reusable helpers `-- LIBRARY CANDIDATE: ...` or
`-- GENERALIZES Reasoning.<Module>.<lemma>: ...`; keep them independent of
contract-local definitions when practical. Do not edit `Reasoning/` in a run.

Use a small `<WorkDir>/Scratch.lean` for experiments importing already compiled
dependencies, then move successful lemmas to their proper files. Prefer
`simp only`, and use `native_decide` for expensive concrete decode obligations.
Raise `maxHeartbeats` locally with `set_option ... in` only where needed.

Run Lake commands from the repository root containing `lakefile.toml`. Build
only the target module and required dependencies. Never run a whole-suite
`lake build Benchmarks`, `lake build Examples`, or unrelated benchmark builds.
Avoid repeated expensive builds without a relevant change or diagnostic reason.

## Accepted trusted base

Retain the accepted base from `Misc/prompt.md`, Section 2:

- Contract selector and jump-destination facts, and compile-time Keccak literals.
  Put any necessary new concrete trusted facts in local `Trusted.lean`, recording
  their provenance; do not edit the supplied bytecode to add them.
- The existing `keccak_size` library axiom for contracts hashing at runtime.
- EVMLean precompile output-size axioms from
  `Ethereum/Theory/ReturnDataBound.lean` when introduced by external-call
  machinery, such as `Ethereum.EVM.ffi_sha256_output_size` and
  `Ethereum.EVM.blob*_output_chunks`.
- Only the narrow slot noncollision exception in that section: identify exact
  conflicting accesses and why matching the spec's storage-operation order
  cannot resolve a compiler optimization. State only the needed noncollision
  property, with domain restrictions, and document it beside the axiom. Never
  assume unrestricted Keccak injectivity. A frozen spec does not itself justify
  this exception; evaluate whether reordering would suffice without changing
  the benchmark input. Report correctness as conditional on these assumptions.

Lean's `propext`, `Classical.choice`, `Quot.sound`, and the expected
`native_decide.ax_*` evaluation dependencies are also accepted. No additional
axioms about EVM or Solm semantics are allowed. Report any required assumption
outside this base and leave its obligation explicitly unresolved.

## Completion and reporting

Replace placeholders with the recorded paths and theorem name. Run from the
repository root and report the commands, exit status, and output:

```sh
lake build <Module>.Correct
rg -n '\b(sorry|admit)\b' <WorkDir> -g '*.lean'
printf '%s\n' 'import <Module>.Correct' '#print axioms <Theorem>' | lake env lean --stdin
```

For example, `Benchmarks/Dss/Dai` maps to module `Benchmarks.Dss.Dai`; discover
the theorem's actual namespace and name from the supplied `Correct.lean`.
`rg` exits 1 when no matches are found; distinguish that from a search error.
Review matches to distinguish proof holes from comments. The text search alone
does not establish completeness: the top-level axiom audit must also exclude
`sorryAx` and all unaccepted dependencies.

The final report must state complete or incomplete, which theorem was checked,
remaining obligations or blockers, the actual axiom footprint, and any input
changes or exposure to excluded material. List slot noncollision assumptions
explicitly with their justification and conditional-correctness caveat.
`ByteArray_zeroes_size`, `Theta_returnData_size_lt_2pow138`, and
`typedCallViaEVM_accountMapEquiv` are proved theorems, not extra axioms.
Do not claim success when validation was not run, failed, or used a different
target. Leave `PROOF_STATE.md` consistent with the final report.
