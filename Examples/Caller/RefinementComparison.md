# Caller: paired refinement and generic helpers

`CorrectRefined.lean` independently proves the same runtime, constructor and full-contract
correctness statements as `Correct.lean`, in namespace `Caller.Refined`. It imports the
same bytecode and specification, without importing the original correctness proof. The
original correctness file is unchanged.

## Current proof structure

The existing RD prefix proves that the initial transaction reaches PC 142 with the call
arguments prepared. `callerBodyRefinesFrom` takes that concrete cursor, its RD counters,
the initial source state and decoded locals. Its entry relation is `CallStateRel`; its
postcondition is `runtimeExit (.abi [])`.

`BlockRefinesFrom.gas` steps the EVM to CALL and exposes the resulting gas operand. The
source non-payable guard and the incoming RD are composed with the call rule through
`BlockProgress.seqOfRD`. There is no example-specific post-GAS cursor definition, manual
call-gas/substate extraction, or manual source-call transport between account maps.

`BlockRefinesFrom.externalCall` supplies the actual source post-state and related EVM world:

- Failed status requires only the EVM revert tail.
- Successful status with `32 ≤ returndata.size < 2^255` proves ABI decoding, the source
  storage assignment, and the EVM `SSTORE`/`STOP`. `CallStateRel.storageStore_codeOwner`
  compares the updated worlds, and `BlockProgress.ofRDret` packages the terminal result.
- Short or oversized return data requires the corresponding EVM decoder-revert proof.
  The call rule supplies the source revert and skips the assignment.

`callerExec_canonical` closes the transaction with `BlockRefinesFrom.toRuntimeEquivalenceFor`.
It has no depth restriction or separate depth-limit branch. Out-of-gas stays inside RD
and the runtime bridge. The compiler's status-check jumps and decoder traces remain
contract-specific.

## Generic interfaces extracted

| Capability | Public interface | Location |
| --- | --- | --- |
| EVM-only progression with discovered witnesses | `BlockRefinesFrom.ofRD`, `BlockRefinesFrom.gas`, `gasCursor` | `Reasoning/Refinement.lean` |
| Terminal block results | `BlockProgress.ofRDret`, `BlockProgress.ofRDrev`, `abiVoidReturn`, `abiVoidFallthrough` | `Reasoning/RuntimeRefinement.lean` |
| Initial and updated world agreement | `CallStateRel.initState`, `.storageStore`, `.storageStore_codeOwner` | `Reasoning/CallRefinement.lean` |
| Scalar ABI decoding and empty encoding | `decodeReturnValues_uint256_eq`, its success/short/huge lemmas, `encodeReturnValues_nil` | `Reasoning/ABI.lean` |
| CALL output and active-memory facts | `callOutputFacts`, `callCopyLength_toNat`, `callActiveWords_eq` | `Reasoning/CallMemory.lean` |

The GAS wrapper preserves the source state and the entry predicate at the original cursor.
The generic progression rule can instead establish a new relation at a witness-selected cursor.
The terminal constructors retain the source execution even when the RD evidence admits OOG.

The memory bundle takes arbitrary offsets and capacities with a bound placing the requested
output region inside the existing byte array. It exposes the copied length, unchanged size,
preserved word reads below/above the region, and first-word readback. Empty and short returns
are included. The separate active-word lemma handles empty regions even with offsets outside
active memory. These facts assume no Solidity free-pointer layout; Caller supplies its own
addresses and allocation bounds.

The stale `Reasoning.DelegateCall` import was also removed: the RD delegate-call bridges
are already in `Reasoning.Reach` in the current repository.

## Size and accounting

The first paired proof is the version before these generic extractions; the current proof
uses all five helper families.

| Measure | Original | First paired proof | Current factored proof |
| --- | ---: | ---: | ---: |
| Whole file, physical lines | 1,417 | 1,252 | 1,154 |
| Whole file, nonblank lines | 1,298 | 1,138 | 1,046 |
| Whole file, nonblank noncomment lines | 1,147 | 1,006 | 916 |
| Call-composition declarations, code lines | 291 | 150 | 128 |
| Same assembly excluding original unused `callerX_afterCall` | 271 | 150 | 128 |

The new factoring removes **90 code lines (8.9%)** from the first paired proof. Relative
to the original file, the current Caller proof has **231 fewer code lines (20.1%)**.

The extraction adds **207 code lines** to shared reasoning modules: ABI 51, call-state
relations 21, progression 24, terminal helpers 19, and CALL memory 92. Thus the combined
Caller-plus-library code grows by **117 lines** in this factoring step. This is an investment
in reuse across contracts; moving code into the library is not counted as a global reduction.
Test and documentation lines are excluded from these code totals.

Counts strip line comments and nested block comments while preserving strings. Declaration
counts cover each declaration through the next, including local option commands. The call
assembly includes the original three source-body lemmas, call-coupling lemmas, depth-limit
lemma and dispatch assembly; the first paired version includes its two cursor definitions,
free-pointer helper, body refinement and runtime/dispatch wrappers; the current version has
one cursor definition plus the body refinement and runtime/dispatch wrappers. Copied ABI,
bytecode and memory helpers are included in whole-file totals. The old unused helper accounts
for 20 code lines separately.

## Validation

```sh
lake build Examples.Caller.Correct Examples.Caller.CorrectRefined \
  Reasoning.RuntimeRefinementTest Reasoning.RefinementTest \
  Reasoning.CallRefinementTest Reasoning.CallVariantsTest \
  Reasoning.RefinementHelpersTest
```

All targets pass. A separate Lean check imports both correctness modules together and checks
both runtime statements and the refined constructor/full-contract statements against the same
specification and bytecode. The non-call and constructor proofs remain unchanged.

The tests exercise actual GAS/POP/STOP progression, explicit and implicit void returns, and
source/EVM reversion under a raw return convention, with arbitrary initial gas. ABI boundary
checks cover lengths 31, 32 and `2^255`. Memory checks use a different offset and a 64-byte
capacity, empty/short/oversized returned data, zero output capacity, preserved reads on both
sides of the region, first-word readback, and empty regions with distant offsets. Existing
call-variant tests remain green. Caller itself transfers zero value, so the Caller experiment
alone does not exercise nonzero-value balance failure or other call types.

There are no new handwritten axioms or `sorry` admissions. The original and current refined
runtime/full-contract proofs have the same 11 non-native axiom dependencies. The refined
runtime proof has 459 generated native-decision axioms versus 460 originally; full-contract
counts are 468 versus 469. The shared empty ABI encoding lemma replaces one native decision
with an ordinary proof. No `sorryAx` appears in the dependency audit.

## Module checking time

Measured on 2026-09-07 with Lean 4.29.0. Three sequential runs of each module used
`lake env lean Examples/Caller/Correct.lean` and the corresponding command for
`CorrectRefined.lean`, with dependencies already built. The order was original/refined,
refined/original, original/refined. All six checks succeeded without warnings.

| Module | Three runs (seconds) | Median (seconds) |
| --- | --- | ---: |
| Original | 27.122, 26.380, 26.872 | 26.872 |
| Current factored proof | 25.789, 26.205, 25.887 | 25.887 |

The factored median is 3.7% lower in this small sample. These are elapsed module-checking
times including startup, imports and native decisions, and excluding dependency builds.

The main benefit is smaller contract-local reasoning and direct reusable theorem applications.
Most of the file still proves compiler-specific dispatch, byte operations, ABI checks and
storage behavior; these obligations remain necessary.
