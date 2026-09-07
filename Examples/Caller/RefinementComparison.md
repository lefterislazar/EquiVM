# Caller: paired refinement comparison

`CorrectRefined.lean` independently proves the same runtime, constructor and full-contract
correctness statements as `Correct.lean`, in namespace `Caller.Refined`. It imports the
same bytecode and specification, but does not import the original correctness proof.
The original file is unchanged. No changes to the shared refinement infrastructure were needed.

## Proof structure

The existing RD prefix still proves that the initial transaction reaches PC 142 with
the call arguments prepared. `callerBodyRefinesFrom` takes that concrete cursor, its
RD counters, the initial source state and decoded locals. Its entry relation is
`CallStateRel`; its postcondition is `runtimeExit (.abi [])`.

The body proof executes the source non-payable guard and the EVM `GAS` instruction,
then uses `BlockProgress.seqOfRD` to enter `BlockRefinesFrom.externalCall` at PC 143.
The gas word is an EVM operand; the proof no longer extracts call-gas/substate witnesses
to construct a source call or transports that call manually between account maps.

The failed-status continuation proves only the EVM revert tail. The successful-status
continuation receives the actual source state and related EVM world:

- For `32 ≤ returndata.size < 2^255`, it proves ABI decoding, the source storage
  assignment and the EVM `SSTORE`/`STOP`, then compares the final account maps.
- Short or oversized return data requires only the EVM decoder's revert proof;
  the call rule supplies the matching source revert and skips the assignment.

`callerPostCallFreePtr` shares the memory calculation across these decoder cases.
`callerExec_canonical` then uses `BlockRefinesFrom.toRuntimeEquivalenceFor` to close the
transaction proof. It has no depth restriction, so the dispatch assembly has no separate
depth-limit branch. Out-of-gas remains inside RD and the runtime bridge.

## Size

| Measure | Original | Refined | Reduction |
| --- | ---: | ---: | ---: |
| Whole file, physical lines | 1,417 | 1,252 | 165 (11.6%) |
| Whole file, nonblank lines | 1,298 | 1,138 | 160 (12.3%) |
| Whole file, nonblank noncomment lines | 1,147 | 1,006 | 141 (12.3%) |
| Changed call-related declarations, nonblank noncomment lines | 291 | 150 | 141 (48.5%) |
| Same comparison excluding the original's unused `callerX_afterCall` | 271 | 150 | 121 (44.6%) |

The last row is the more conservative measure of the technique's benefit. Removing
`callerX_afterCall` accounts for 20 code lines separately; that lemma was already unused
by the original correctness theorem.

The call-related comparison includes complete declarations and every new helper:

| Original declaration(s) | Code lines | Refined declaration(s) | Code lines |
| --- | ---: | --- | ---: |
| Three `callerBody…` source execution lemmas | 61 | `callerPreCallCursor`, `callerCallEntry` | 11 |
| `callerX_postCall` | 46 | `callerPostCallFreePtr` | 13 |
| `callerExec_canonical` | 100 | `callerBodyRefinesFrom` | 79 |
| `callerX_callDepthLimit` | 12 | `callerExec_canonical` | 16 |
| `callerReEquiv_callvalueZero` | 52 | `callerReEquiv_callvalueZero` | 31 |
| Unused `callerX_afterCall` | 20 | — | 0 |

Rows inventory the two implementations, rather than asserting one-to-one replacements.
Counts remove line comments and nested block comments while preserving strings. The
declaration counts cover spans from each declaration to the next, including local option
commands. Unchanged bytecode stepping, ABI, memory and storage helpers are excluded from
both call-related totals and included in both whole-file totals. Shared infrastructure
was already present and is not counted as new Caller proof code.

## Validation

Both correctness modules and the four refinement test modules build successfully:

```sh
lake build Examples.Caller.Correct Examples.Caller.CorrectRefined \
  Reasoning.RuntimeRefinementTest Reasoning.RefinementTest \
  Reasoning.CallRefinementTest Reasoning.CallVariantsTest
```

A separate Lean check imports both correctness modules together and checks the original
and refined runtime statements, plus the refined constructor and full-contract statements,
against the same specification and bytecode. The copied constructor section is identical
apart from the closing namespace. Non-call branches retain their original proofs.

The canonical theorem covers every call depth and arbitrary related initial account maps.
The proof covers failed status, successful storage updates, short and oversized return
data, and out-of-gas without adding assumptions about the callee. Caller transfers zero
value, so this experiment does not exercise nonzero-value balance failure or other call types.

There are no new handwritten axioms or `sorry` admissions. `#print axioms` reports the
same 11 non-native axioms for both runtime and full-contract proofs. Each runtime proof
also has 460 generated native-decision axioms; each full-contract proof has 469. After
normalizing the namespace, the only generated dependency change moves the empty-return
encoding decision from `callerExec_canonical` to `callerBodyRefinesFrom`. No `sorryAx`
appears in either proof's dependencies.

## Elaboration time

Measured on 2026-09-07 with Lean 4.29.0, using three sequential runs of each module
with dependencies already built:

```sh
lake env lean Examples/Caller/Correct.lean
lake env lean Examples/Caller/CorrectRefined.lean
```

The run order was original/refined, refined/original, original/refined. These are elapsed
module-checking times, including startup, imports and native decisions, excluding
dependency builds. All six runs succeeded without warnings.

| Module | Three runs (seconds) | Median (seconds) |
| --- | --- | ---: |
| Original | 29.467, 29.282, 28.705 | 29.282 |
| Refined | 30.126, 29.332, 29.859 | 29.859 |

The refined median is about 2% slower in this small sample. Compilation time is
comparable; there is no observed speedup to accompany the proof-size reduction.

The improvement is concentrated in call composition and state comparison. Most of the
remaining file still proves compiler-specific dispatch, byte operations, ABI checks and
storage behavior; paired refinement does not eliminate those obligations.
