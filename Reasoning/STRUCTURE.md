# Reasoning/ — structure

Shared, contract-agnostic infrastructure for proving that compiled EVM bytecode refines its Solm
specification. Every per-contract proof in `Examples/` and `Benchmarks/` is assembled from these
files plus contract-specific facts (bytecode literals, selectors, storage layout).

Most modules use namespace `Reasoning.Theory`. The EVM trace layer (`RD`, `evm_run`, and the
`RD.*` lemma halves of `Solc.lean` and `Dispatch.lean`) is in `Reasoning.Reach`.
The paired proof layer in `Refinement.lean`, `CallRefinement.lean`, and
`RuntimeRefinement.lean` is in `Reasoning.Refinement`.
`JumpDest.lean` has no namespace (it defines a tactic and an attribute).

One axiom in the whole library: `keccak_size` in `Memory.lean` (a keccak digest is 32 bytes —
trusted spec of the FFI hash; asserts nothing about collision resistance).

## Files

| File | Contents |
|---|---|
| `Stepping.lean` | Base layer. Trace drivers — `initState` (the fresh EVM state), the `Ξ`-to-iterator bridge (`Xi_*_of_X`), single-step peeling (`X_peel`, `stepContinue`, `stepOOG`, `stepHalt*`) — plus one lemma per opcode (`<op>_xstep`) evaluating a single `Xstep` to an explicit gas-guarded successor state (`st<Op>` definitions). |
| `EVMWord.lean` | `UInt256` arithmetic: no-wrap `toNat` lemmas, bitwise normalization, unsigned comparisons, signed `SLT`, `compare` order instances, the word-rounding used by solc memory allocation. |
| `SolmBody.lean` | The Solm side: `ExecTransitionBody`/`ExecStmt`/`ExecBlock` lemmas. Non-payable guard, call wrappers (external/checked/low-level/delegate), loop rules, block sequencing (`execBlock_append`), locals lookup, storage-access collapse. |
| `Memory.lean` | Byte-level memory: little-endian word arithmetic, `MSTORE`/`MLOAD` read-write facts, scratch memory for mapping hashes, selector extraction, calldata decode coupling, mapping-slot keccak facts. Home of the `keccak_size` axiom. |
| `Reach.lean` | The EVM trace layer. `RD` (reached-or-out-of-gas invariant) and its canonical forward rules (`RD.<op>`) expose deterministic memory, hashing, storage-map, gas, and terminal results directly as symbolic terms. Warm/cold rules retain existential counters; `RD.pack`, `RD.normalizePC`, and `RD.normalizeCounters` support generated blocks. The module also contains opaque-`Θ` call rules, terminal `RDret`/`RDrev` forms, `Cursor`/`RDc`, and the `evm_run` chain builder. Low-level alias-parameterized proof kernels remain explicitly named `RD.raw*` for legacy handwritten proofs, rather than competing for the standard opcode names. |
| `ABI.lean` | Calldata decoding and return-value encoding: per-shape decode lemmas (address/uint256/bool/bytes32/string/dynamic-array combinations), decode-mode variants, failure cases (short, huge, non-canonical), return encodings. |
| `MemCascade.lean` | Collapsing chains of memory writes into a canonical form. |
| `JumpDest.lean` | The `@[valid_jumps]` attribute and `jump_dest` tactic discharging jump-target validity (via `native_decide`, deliberately). |
| `Initcode.lean` | Constructor-time facts: decode of the initcode prefix, jump-table survival, constructor-argument arithmetic. |
| `Solc.lean` | Compiler-emitted code shapes, proved once: selector dispatch, ABI length checks, free-memory-pointer and revert memory, the 160-bit address mask, getter/store routines, reentrancy locks, checked arithmetic, event logs, high-level call combinators. |
| `Storage.lean` | Storage maps: red-black-map lookup/update facts, `StorageLoc` load/store for the Solidity value encodings, the bytes/string storage layout, `accountMapEquiv`/`EVMStateEquiv` with `SLOAD`/`SSTORE` preservation. |
| `Dispatch.lean` | Solm dispatcher facts: `dispatchMsg` as a list walk (`dispatchList`), single-transition instances, `SingleSelectorDispatch`, and the `RDret`/`RDrev.reEquiv*` bridges that connect a finished trace to the equivalence statement. |
| `ExternalCall.lean` | The `CALL` ↔ Solm `externalCall` boundary: both sides invoke the same `Θ`, so results coincide (`callCoincides`); transport of call results across equivalent account maps. |
| `Refinement.lean` | Paired progression over RD: `StateRel`, `ExitRel`, `BlockProgress`, fixed-start `BlockRefinesFrom`, and reusable `StmtsRefine`. Sequencing with separate RD/source prefixes, EVM-only advancement, paired `GAS`/`gasleft()`, and coupled loop rules covering normal completion, break, continue, return, and revert. |
| `CallRefinement.lean` | Paired CALL, STATICCALL, and DELEGATECALL boundaries (`PairedCall`) and statement rules for typed, low-level, checked, delegate, and internal calls. `CallStateRel` connects source state to the RD world; call rules hide gas/substate witnesses and depth/balance cases while exposing the actual post-call states to continuations. Creation is outside this module's scope. |
| `RuntimeRefinement.lean` | Function-body refinement to `runtimeEquivalenceFor`: `runtimeExit` describes matching transaction endpoints; `BlockProgress.ofRDret`/`.ofRDrev` close paired proofs, and `BlockRefinesFrom.toRuntimeEquivalenceFor` combines body refinement with incoming RD, entry agreement, dispatch, and ABI decoding. |
| `Constructor.lean` | Skeletons for constructor (creation-code) equivalence proofs. |

## Dependencies

External: `Ethereum.*` (evmlean — EVM semantics and opcode lemmas), `Solm` (the spec language and
its semantics), `ABI.Decode`, Mathlib (EVMWord and Memory only).

Within `Reasoning/`, imports flow upward:

```
Stepping   EVMWord ── SolmBody
    │         │
    ├── Memory ── MemCascade
    │      │
    │      ├── ABI
    │      └── Reach
    │           │
    └───────── Solc
                │
            Storage
             ├── Dispatch      (also Reach)
             └── ExternalCall  (also SolmBody)

Constructor ← Reach, SolmBody     Initcode ← EVMWord     JumpDest ← (Ethereum only)

Refinement        ← Reach, SolmBody
CallRefinement    ← Refinement, ExternalCall
RuntimeRefinement ← Refinement, ABI
```

## Where to look

- Run one opcode of a concrete trace → `Stepping` (`<op>_xstep`), chained via `Reach` (`evm_run`).
- Generate straight-line block summaries from bytecode → `scripts/generate_rd_blocks.py`; its output
  imports `Reach` and is ordinary checkable Lean source. The generated `ReachGenerated*Test.lean`
  modules cover deterministic arithmetic/memory, `SSTORE` → `SLOAD` continuation, deep stack
  operations, and splitting around unsupported instructions.
- Word arithmetic side condition → `EVMWord`.
- Memory read/write or keccak slot → `Memory` (chains of writes: `MemCascade`).
- Decode calldata / encode a return value → `ABI` (solc-specific length checks: `Solc`).
- A code shape the compiler always emits → `Solc`.
- Storage read/write, packed values, bytes/string layout, account-map equivalence → `Storage`.
- Selector dispatch, connecting a trace to `runtimeEquivalence` → `Dispatch`.
- A path containing an external call → `CallRefinement` over `Refinement`; the underlying
  call coupling and account-map transport live in `ExternalCall` and the opcode rules in `Reach`.
- Concrete paired states, a reusable statement-block refinement, or mixed RD/source prefixes →
  `Refinement` (`BlockProgress`, `BlockRefinesFrom`, `StmtsRefine`, `seqOfRD`).
- Source `gasleft()` or a compiler's forwarding `GAS` → `Refinement`
  (`BlockRefinesFrom.letGas`, `.letGasOfRD`, `.gas`).
- Simple or bytecode-only loops → RD loop rules in `Reach`; complex loops that benefit from
  coupled EVM/Solm reasoning → `Refinement` (`StmtsRefine.forLoopCombined`).
- Close a paired function-body proof as `runtimeEquivalenceFor` → `RuntimeRefinement`.
- Stronger returndata bounds in call continuations → `ExternalCall`
  (`typedCallViaEVM_returnData_size_lt_2pow138` and its raw-call counterpart).
- Constructor proofs → `Constructor`, `Initcode`.
- Jump-target validity → `JumpDest`.

## Paired refinement over RD

Use this layer for paths containing calls or source-visible gas reads, and for complex loops
where comparing the executions incrementally simplifies the proof. Simple loops and
compiler-generated bytecode-only loops should use the RD loop rules. RD remains the EVM
stepping interface throughout; provided block summaries compose directly into paired proofs.

The three judgements have different roles:

| Judgement | Role |
|---|---|
| `BlockProgress` | Concrete result witnesses: Solm block execution, an EVM endpoint reached through RD, and their `ExitRel`. Resulting states remain available for subsequent reasoning. |
| `BlockRefinesFrom` | Fixes the entry cursor, RD counters, source frame/state, and starting `StateRel`. Incoming RD and that relation produce `BlockProgress`. |
| `StmtsRefine` | Quantifies `BlockRefinesFrom` over related starting pairs at a specified PC; useful for reusable bodies, loop invariants, and continuations. |

The RD anchor `s0` stays fixed at the transaction's initial EVM state even when a body proof
starts after dispatch and ABI decoding. At initial related transaction states,
`CallStateRel.initState haccounts` establishes world/environment agreement. A concrete
body-entry theorem can often use only `fun cur _ e => CallStateRel s0 ee cur.world e`, with
stack, memory, and local facts supplied by its arguments. Define richer relations when reusable
boundaries need to describe varying representations. Out-of-gas stays inside RD and the
endpoint reachability judgements; clients still provide source execution and the exit relation,
without adding an out-of-gas alternative to every prefix obligation.

For a prefix, combine separately proved RD and Solm execution with
`BlockRefinesFrom.seqOfRD`. If manual stepping discovers existential intermediate cursors or
counters, introduce the incoming RD and relation, then use `BlockProgress.seqOfRD` on those
witnesses. Use `BlockRefinesFrom.ofRD` to advance only the EVM. Generated summaries can supply
these RD steps, including reaching a call boundary and following status/decoder branches.

At an ordinary CALL, `BlockRefinesFrom.externalCall` connects the operands and encoded calldata
to the source call at the head of a statement list. For STATICCALL, obtain `PairedCall` with
`staticCallPaired` and use `externalCallOfPaired` with the source permission set to `false`.
The shared attempt handles depth/balance cases and chooses gas/substate witnesses internally.
The successful continuation receives the actual returndata, source state, EVM world/cursor,
RD counters, call evidence, and state agreement. It proves the decoder path and refines the
remaining statements. Raw failure needs only post-call RD implying `RDrev`; failed typed
decoding also requires EVM reversion. Low-level and delegate calls continue for either status;
checked calls execute the selected handler. Follow the corresponding rule's obligations.

Continuations can obtain `out.size < 2 ^ 138` from the supplied call evidence using the
`ExternalCall` bound lemmas after proving the required calldata-size bound. The paired rules
already expose `out.size < UInt256.size`. The stronger theorem wraps the underlying Θ bound,
so contract proofs need not reopen call-attempt cases.

For internal calls, prove the callee body once with `internalCallExit`, then compose it with
`BlockRefinesFrom.internalCall`. For complex loops, `forLoopCombined` uses a decreasing variant,
related-state invariants, and body/post/continuation obligations: normal completion and continue
execute post, break reaches the loop tail, and return/revert bypass both. Separately proved RD
and Solm effects can still discharge individual obligations.

At the function boundary, `runtimeExit` requires matching transaction returns or reverts;
a reached cursor alone must first pass through any return epilogue. Use
`BlockRefinesFrom.toRuntimeEquivalenceFor` with the body-entry RD, its relation, and the
dispatch/ABI facts. `toRuntimeEquivalenceForOfExec` accepts an explicit source execution lift
for other dispatch conventions, including receive/fallback paths.

Reading references: `Examples/Caller/CorrectRefined.lean` for a call followed by a storage
continuation; `Examples/NestedCaller/` for internal calls, external calls, gas reads, loop control,
and generated summaries. Focused usage checks include `RefinementTest.lean`,
`CallRefinementTest.lean`, `CallVariantsTest.lean`, `GasRefinementTest.lean`,
`ForLoopCombinedTest.lean`, and `RuntimeRefinementTest.lean`.

## Build

`lake build Reasoning` builds the complete reasoning library. A bare `lake build` builds only `Solm`
(the default target) — use explicit targets.

## Generated RD block summaries

For an inline bytecode literal:

```console
python3 scripts/generate_rd_blocks.py \
  --hex 6001600055600054600201604052 --name storageDemo \
  --output StorageDemoBlocks.lean
lake env lean StorageDemoBlocks.lean
```

The input can instead be a raw binary, hex file, solc JSON artifact, stdin, or a Lean source file
containing a `ByteArray` literal (hex or decimal bytes). To summarize an existing Lean bytecode
definition, pass `--code-term Contract.bytecode --import Contract.Bytecode`; the input is still
used to discover instruction and block boundaries. Standard length-suffixed solc CBOR metadata is
excluded from block discovery while the full byte array remains in every theorem; use
`--keep-metadata` to override that. An unsupported instruction splits its basic block into maximal
supported segments. The generator emits summaries for every segment before and after the boundary,
restarting the suffix from a fresh symbolic RD state, and leaves a prominent comment for the one
unproved transition. Use `--fail-on-unsupported` when CI should reject any such boundary.

For creation bytecode, add `--creation-code`. In this mode `--code-term` denotes the fixed
compiler-produced creation prefix, each theorem quantifies an arbitrary `tail : ByteArray`, and all
RD states use `codeTerm ++ tail`. Decode facts and prefix jump destinations are lifted across the
append, while `CODESIZE` and `CODECOPY` continue to observe the full prefix-plus-tail byte array.
Each generated module binds the prefix-specialized lifting lemmas once as the private aliases `d`
and `j`, keeping repeated block proofs compact.
Constructor proofs can therefore specialize `tail` to their symbolic ABI encoding without
regenerating summaries for each argument value.

Every nonterminal theorem has the form `RD entry ... → RD exit ...`. Deterministic blocks retain
exact counters and combine all fixed gas into one constant plus the remaining symbolic costs.
Warm/cold operations (`SLOAD`, `SSTORE`, and `EXTCODESIZE`) switch only the counters to
`∃ k' C'`; the generated proof immediately destructs that result and continues applying steppers,
so storage does not split the basic block. `JUMPI` produces separate taken and fallthrough
summaries, and halting blocks produce `RDret`/`RDrev`.
