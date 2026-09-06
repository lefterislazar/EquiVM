# RD summary sequence inventory

This is the curated migration list for sequence theorems that may be invoked by
`scripts/generate_rd_blocks.py`.  The generated
[`BYTECODE_SEQUENCE_REPORT.md`](BYTECODE_SEQUENCE_REPORT.md) remains the exhaustive source audit;
this file records the stricter summariser decision.

## Admission rule

A sequence is admitted only when it:

- is wholly contained in one EVM basic block;
- is recognized by exact opcodes, while theorem-valid PUSH operands are captured (including
  the actual PUSH width);
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
| `RD.solcSummaryLowMask` | `PUSH1 1 PUSH1 1 PUSH1 bits SHL SUB` | 1,134 / 38 artifacts | canonical `solcLowMask bits` |
| `RD.solcSummarySelectorCondition` | `DUP1 PUSH4 selector EQ PUSHw target` | 654 / 38 | target, selector-match word, and selector; `JUMPI` remains primitive |
| `RD.solcSummaryCallSuccessCondition` | `ISZERO DUP1 ISZERO PUSHw target` | 482 / 30 | both call-status Boolean words and target |
| `RD.solcSummaryStaticArgsCondition` | static ABI argument-length prefix through target push | 386 / 38 | canonical sufficient-length word and exact retained stack |
| `RD.solcSummarySelectorSplitCondition` | `DUP1 PUSH4 pivot GT PUSHw target` | 106 / 34 | split condition, target, and selector |
| `RD.solcSummaryCallvalueCondition` | `CALLVALUE DUP1 ISZERO` | 57 / 38 | value and canonical zero-test word |
| `RD.solcSummaryLeftAlignedSelector` | `PUSH4 0xffffffff AND PUSH1 224 SHL` | 56 / 18 | canonical left-aligned ABI selector word |
| `RD.solcSummaryReturnDataSizeCondition` | returndata word-length guard prefix | 51 / 16 | returndata size and canonical availability word |
| `RD.solcSummaryCalldataSizeCondition` | selector-length guard prefix | 38 / 38 | canonical short-calldata word and target |
| `RD.solcSummaryMappingHashKeyFirst` | key-at-0 then slot-at-32 scratch hash | 58 / 12 | exact memory/active words/cost and `solcMappingSlot` |
| `RD.solcSummaryMappingHashSlotFirst` | slot-at-32 then key-at-0 scratch hash | 30 / 14 | exact memory/active words/cost and `solcMappingSlot` |
| `RD.solcSummaryBoolNormalize` | `ISZERO ISZERO` | 22 / 14 | canonical EVM Boolean word |
| `RD.solcSummaryUintMax` | `PUSH1 0 NOT` | 22 / 12 | canonical maximum UInt256 word |
| `RD.solcSummaryCheckedSubCondition` | checked-sub condition-producing prefix | 20 / 20 | exact subtraction and canonical success word |
| `RD.solcSummaryCheckedAddCondition` | checked-add condition-producing prefix | 18 / 18 | exact sum and canonical success word |
| `RD.solcSummaryNestedMappingInnerHash` | nested-mapping inner scratch hash | 10 / 6 | arbitrary incoming memory; canonical inner slot |
| `RD.solcSummaryNestedMappingOuterHash` | nested-mapping outer scratch hash | 10 / 6 | composes with inner summary; canonical outer slot |

The admitted patterns live in [`SummaryPatterns.lean`](SummaryPatterns.lean). Their reducible `...Wf`
predicates package the incoming cursor, decode facts, and stack-capacity fact. Existing theorems
in `Reasoning.Solc` are unchanged.

## Audit disposition

Every report family at the 10-occurrence/two-artifact threshold is either represented above or
falls into one of the rejection classes below. Condition-producing prefixes are admitted; their
branch instruction is deliberately excluded. The nested inner prefix carries only its 14 decode
facts, including the Vat variant whose later getter tail differs. The outer entry is applied only
when the symbolic stack carries the required `64`, `32`, and `0` scratch constants.

## Not currently admissible

- Full selector, calldata, checked-arithmetic, and call-success branches: their condition-producing
  prefixes are migrated, while `JUMPI` keeps condition and destination-validity hypotheses visible.
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
