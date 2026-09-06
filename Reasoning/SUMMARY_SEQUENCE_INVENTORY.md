# RD summary sequence inventory

This is the curated migration list for sequence theorems that may be invoked by
`scripts/generate_rd_blocks.py`.  The generated
[`BYTECODE_SEQUENCE_REPORT.md`](BYTECODE_SEQUENCE_REPORT.md) remains the exhaustive source audit;
this file records the stricter summariser decision.

## Admission rule

A sequence is admitted only when it:

- is wholly contained in one EVM basic block;
- is recognized by exact opcodes and exact PUSH widths/values;
- needs no semantic premise beyond its incoming `RD` cursor and stack capacity; and
- preserves the same final state, stack, counters, and hypotheses as primitive stepping (except
  for terminal information intentionally forgotten by `RDrev` or `RDret`).

Matches are ordered longest-first. Summary splitting may move a 64-instruction boundary so it
never cuts an admitted sequence. `--no-sequence-patterns` provides the primitive-step baseline.

## Migrated

| Summary theorem | Exact sequence | DSS matches | Result/information retained |
|---|---|---:|---|
| `RD.solcSummaryReturnDataCopyRevert` | `RETURNDATASIZE PUSH0 PUSH0 RETURNDATACOPY RETURNDATASIZE PUSH0 REVERT` | 0 | `RDrev`; the copied memory and counters are irrelevant after revert |
| `RD.solcSummaryLegacyReturnDataCopyRevert` | `RETURNDATASIZE PUSH1 0 DUP1 RETURNDATACOPY RETURNDATASIZE PUSH1 0 REVERT` | 234 | `RDrev`; discharges the full-return-data bounds fact internally |
| `RD.solcSummarySelectorLoad` | `PUSH0 CALLDATALOAD PUSH1 224 SHR` | 0 | exact selector word, `k + 4`, `C + 11` |
| `RD.solcSummaryLegacySelectorLoad` | `PUSH1 0 CALLDATALOAD PUSH1 224 SHR` | 38 | exact selector word, `k + 4`, `C + 12` |
| `RD.solcSummaryRevert0` | `PUSH0 PUSH0 REVERT` | 0 | `RDrev` |
| `RD.solcSummaryLegacyRevert0` | `PUSH1 0 DUP1 REVERT` | 961 | `RDrev` |
| `RD.solcSummaryFreeMemoryPointer` | `PUSH1 128 PUSH1 64 MSTORE` | 55 | exact memory, active words, `k + 3`, and symbolic expansion cost |
| `RD.solcSummaryAddressMask` | `PUSH1 1 PUSH1 1 PUSH1 160 SHL SUB` | 1,090 | canonical `solcAddrMask`, `k + 5`, `C + 15` |
| `RD.solcSummaryFreeMemoryPointerLoad` | `PUSH1 64 DUP1 MLOAD` | 868 | exact symbolic load, active words, and expansion cost |
| `RD.solcSummaryErrorSelectorStore` | `PUSH3 0x461bcd PUSH1 229 SHL DUP2 MSTORE` | 594 | canonical `solcErrorStringSelector`, exact memory, active words, and cost |
| `RD.solcSummaryErrorRevertFinalizer` | `PUSH1 68 DUP3 ADD MSTORE SWAP1 MLOAD SWAP1 DUP2 SWAP1 SUB PUSH1 100 ADD SWAP1 REVERT` | 570 | `RDrev`; no payload-layout premise is needed |

The admitted patterns live in [`SummaryPatterns.lean`](SummaryPatterns.lean). Their reducible `...Wf`
predicates package the incoming cursor, decode facts, and stack-capacity fact. Existing theorems
in `Reasoning.Solc` are unchanged.

## Good next candidates

| Sequence/family | Why it is plausible | Work still needed |
|---|---|---|
| Remaining fixed ABI scratch-memory writes | Straight-line PUSH/MSTORE fragments can retain symbolic memory and cost exactly | Select only byte-identical, frequent fragments; avoid overlapping the error-selector/finalizer patterns |
| Full return-data copy without terminal revert | The bounds condition follows from `RETURNDATASIZE` | Requires an exact memory/active-word/counter result; the existing existential helper would lose information mid-block |

## Not currently admissible

- Selector arms, calldata guards, checked arithmetic, and call-success guards: a `JUMPI` outcome
  needs a condition and a taken jump needs destination validity.
- `JUMP` thunks and internal-call setup: they require `D_J` membership and often encode a return
  convention that the raw byte sequence alone cannot establish.
- Storage, account-access, calls, and logs: permission, warm/cold, balance, or environment facts
  remain semantic requirements. They should continue through the block as generated hypotheses,
  not be hidden by a pattern.
- Memory-return and error-string families with read-back or layout premises: these carry useful
  semantic information that an opcode-only matcher cannot infer.
- Sequences spanning `JUMPDEST`, a terminator, an unsupported opcode boundary, or two generated
  summary shards.

## Re-evaluation checklist

Before adding another registry entry, add an exact/near-miss matcher test, an overlap test against
longer entries, an artificial shard-boundary test, an elaborating Lean fixture, and a comparison
showing that pattern-enabled and primitive modes emit identical theorem statements.
