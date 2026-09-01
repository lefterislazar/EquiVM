# Reasoning/ — structure

Shared, contract-agnostic infrastructure for proving that compiled EVM bytecode refines its Solm
specification. Every per-contract proof in `Examples/` and `Benchmarks/` is assembled from these
files plus contract-specific facts (bytecode literals, selectors, storage layout).

Everything is in namespace `Reasoning.Theory`, except the EVM trace layer (`RD`, `evm_run`, and the
`RD.*` lemma halves of `Solc.lean` and `Dispatch.lean`), which is in `Reasoning.Reach`.
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
- An external call inside a function body → `ExternalCall` (EVM side: `RD.call` in `Reach`;
  Solm side: `SolmBody`).
- Constructor proofs → `Constructor`, `Initcode`.
- Jump-target validity → `JumpDest`.

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

Every nonterminal theorem has the form `RD entry ... → RD exit ...`. Deterministic blocks retain
exact counters and combine all fixed gas into one constant plus the remaining symbolic costs.
Warm/cold operations (`SLOAD`, `SSTORE`, and `EXTCODESIZE`) switch only the counters to
`∃ k' C'`; the generated proof immediately destructs that result and continues applying steppers,
so storage does not split the basic block. `JUMPI` produces separate taken and fallthrough
summaries, and halting blocks produce `RDret`/`RDrev`.
