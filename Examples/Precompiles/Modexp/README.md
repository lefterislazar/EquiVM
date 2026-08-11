# ModExp precompile bytecode proof status

The Solidity source snapshot corresponding to the proved runtime is kept in [`Solidity/`](Solidity/).
Its [`SOURCE.md`](Solidity/SOURCE.md) records the upstream commit, compiler settings, source
hashes, and the proof-driven `LimbMath.schoolbookDiv` correction.

## Saturated schoolbook-estimate correction

The proof found a valid, fully aligned `96/1/64`-byte ModExp input for which the original
`LimbMath.schoolbookDiv` runtime reverted with Solidity arithmetic panic `0x11`.  After the first
quotient digit, the remainder is `modulus - 1`; the next Knuth saturated estimate has
`uLo = vTop = 2^255`, so `uLo + vTop` is exactly `2^256`.

The following source expression was therefore changed from checked addition to intentional word
wrapping:

```solidity
unchecked {
    rHat = uLo + vTop;
}
```

This is required by the immediately following `rHat >= uLo` test, which distinguishes a wrapped
sum and disables refinement.  It does not exclude the input or bypass division; it restores the
intended Algorithm D path.  SymCheck reaches the corrected no-refinement join from the same public
input with exact SMT and no overapproximation.  The aligned operand facts and trusted-model result
are checked in `MultiLimbSchoolbookOverflowCounterexample.lean`, and the Solidity differential
suite contains `test_identical_schoolbook_saturated_estimate_wrap`.

## Invalid-trace revert observation

The invalid EIP-7823 length path ends in `REVERT(0, 0)`, not `INVALID`. Its expected public result
was therefore changed only for invalid traces from the generic exceptional `.failure` observation
to `BytecodeResult.reverted`, retaining the empty revert payload, remaining gas, and exact
108-gas threshold. `RDxRevOutput`, `ExactRevertPost`, and `invalidLengthExactRevert` make that
distinction explicit. This change is required because a resolved revert preserves unused gas and
return data whereas `INVALID` consumes the call exceptionally; treating both as the same expected
output would prove the wrong observable behavior. No accepted computation or valid-path output
was changed.

## Leading-zero proof decomposition

The deployed `_clz` helper is proved one binary-search stage at a time, with separate artifacts for
exact execution and arithmetic semantics.  This decomposition was needed because composing all
eight generated branch traces into one Lean declaration produced a proof term too deep for routine
kernel checking.  Each prefix theorem preserves and accumulates the exact EVM state, step count,
and gas expression; the split is therefore proof organization only and does not abstract, merge,
or omit any execution path.  `MultiLimbClzExecutable.lean` exposes the complete exact execution
contract, while `MultiLimbClzSemantic.lean` proves that its result is `255 - Nat.log2 x` for every
nonzero input word.

`CoveredSpec.lean` is the current proved union of branch-local bytecode specs.  It proves exact-gas
functional correctness against `Model.output` for:

- the all-single-word path;
- wide fast exits: exponent zero and base ≤ 1;
- zero declared modulus-length exits;
- positive one-word small-modulus-value exits: modulus value zero or one;
- one-word odd-modulus Montgomery;
- one-word even-modulus Barrett, both direct and normalized.

`Spec.lean` states the intended general ModExp proof interface:

- `modexpAccepts`: the ModExp-level input predicate (`weiValue = 0` and Osaka operand-length
  validity);
- `modexpSomeExactGasEnsures`: functional correctness against `Model.output`, with some exact
  bytecode gas threshold;
- `modexpSomeExactGasSpec_of_coverage`: the formal reduction showing that full coverage of
  `coveredAccepts` over `modexpAccepts` is sufficient for a general ModExp bytecode spec.

The remaining proof obligation is `missingModexpCases`: accepted ModExp inputs not yet covered by
the completed branch predicates.  `Spec.lean` proves that bounded-calldata missing cases are in the
wide, nontrivial backend region: not all-single-word, exponent nonzero, and base > 1.

It also factors the one-word nontrivial backend shape:

- `wideOneWordBackendInputs`;
- `wideModulusNat`;
- `wideModulusParity`;
- `wideBarrettDirectSelector`.

For that shape, `Spec.lean` proves that an odd modulus is already covered by Montgomery, and that
the two completed even-modulus Barrett selectors are already covered.  Thus a bounded missing
one-word case is reduced to the branch-selection gap around the Barrett normalization predicate.
The scanner-control part of that gap is now also explicit:
`wideOneWordBarrett_not_direct_hnorm` proves that a nontrivial one-word Barrett input not selected
by the direct path must enter the normalization branch.  The remaining one-word normalization
obligations are now factored as `WideBarrettNormalizedWordMemoryFacts`, with
`wideBarrettNormalizedWordFacts_of_hnorm_memory` reconstructing the backend predicate and
`wideOneWordBarrettNormalizedMemory_coveredAccepts` giving the coverage theorem once those memory
facts are proved.

The raw normalized-memory facts are also connected to pure payload facts:
`WideBarrettNormalizedWordModelFacts` states that the normalized payload is neither zero nor one and
has an accepted first-byte shape, while `wideBarrettNormalizedWordMemoryFacts_of_model` uses the
existing `memoryZeroResult_eq_reference`/`memoryOneResult_eq_reference` lemmas to derive the
operational scanner facts from those pure predicates plus `wideBarrettNormalizedMemoryBounds`.
`wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs` proves those bounds automatically for
the one-word backend shape, and `wideOneWordBarrettNormalizedModelAuto_coveredAccepts` is the
corresponding coverage theorem.  The one-word direct-false residual is now only
`WideBarrettNormalizedWordModelFacts`.

This has been reduced one step further: `WideBarrettNormalizedWordPayloadFacts` packages payload
equality with the original modulus plus the normalized first-byte shape.
`wideBarrettNormalizedWordModelFacts_of_oneWordPayload` derives the previous model facts from these
payload facts and the already-known `wideModulusNat > 1`, and
`wideOneWordBarrettNormalizedPayload_coveredAccepts` is the coverage theorem in that form.

The generic parity fact is now discharged by `wideModulusParityCoverage_of_landOne`: because the
bytecode computes parity by `land x 1`, the result is always either `0` or `1`.

The full nontrivial one-word backend is now packaged by
`wideOneWordBackend_coveredAccepts_of_payload`.  It needs only `wideOneWordPayloadCoverage`: in the
even/direct-false Barrett case, the normalized payload facts hold.
The arithmetic part of that payload proof is factored out by
`wideBarrettNormalizedPayloadNat_eq_wideModulusNat_of_read_prefix`: once the normalized result
payload read is shown to be the significant suffix of the original modulus and the skipped prefix
is shown to decode to zero, the normalized payload Nat is exactly `wideModulusNat`.
Those lower-level facts are now packaged as `WideBarrettNormalizedWordReadFacts`, and
`wideOneWordBackend_coveredAccepts_of_readFacts` is the corresponding one-word coverage theorem.
The `k + normalizedLen = modulusSize` read-facts field is now discharged for the canonical skipped
prefix by `wideBarrettNormalizedSkippedPrefix_add_len`, backed by the generic scanner theorem
`barrettNormalizedSkippedPrefix_add_len`.
The skipped-prefix-zero field is discharged by `wideBarrettNormalizedSkippedPrefix_zero`, and the
canonical normalized payload read-preservation field is discharged by
`wideBarrettNormalizedResultMem_read_canonical_payload`.  Consequently
`wideBarrettNormalizedWordReadFacts_of_canonical` builds read facts from only the normalized
first-byte shape, and `wideBarrettNormalizedWordFirstByteShape_of_notDirect` discharges that shape
from the scanner stop theorem plus the canonical payload-read bridge.

`missing_bounded_oneWord_impossible_of_payload` is the no-missing-cases form of that same one-word
result; `missing_bounded_oneWord_impossible_of_readFacts` is the lower-level read-facts form, and
`missing_bounded_oneWord_impossible` closes the bounded nontrivial one-word backend.

The positive one-word small-modulus-value path is now proved directly by
`wideSmallModulusValueBytecodeSpec`; it composes the operand-copy prelude, the zero/one
dispatcher exits, and the Solidity bytes return suffix with exact gas.

The zero declared modulus-length path is also proved directly by
`wideZeroModulusLengthBytecodeSpec`; it composes the operand-copy prelude, the dispatcher
empty-bytes return path, and the Solidity bytes return suffix with exact gas.

The formal residual after this closure is `wideBackendResidualInputs`, proved by
`missing_bounded_backendResidualInputs`: any bounded missing case is now a multi-limb nontrivial
backend (`wideMultiLimbBackendInputs`).  `modexpSomeExactGasSpec_of_bounded_residualCoverage`
packages the remaining route to the intended general theorem: provide the calldata-size bound
required by the current wide proofs and prove coverage for `wideBackendResidualInputs`.

`Spec.lean` also splits this residual along the bytecode's actual odd/even dispatcher:
`wideMultiLimbOddMontgomeryInputs` and `wideMultiLimbEvenBarrettInputs`, with
`modexpSomeExactGasSpec_of_bounded_multiLimbBranchCoverage` packaging the corresponding route to
the general theorem.  `MultiLimbPrefix.lean` proves the exact-gas prefix from the normal precompile
entry to those backend entry PCs:

- `wideMultiLimbOddDispatcherPrefixExact`: reaches PC 1925, the Montgomery backend entry;
- `wideMultiLimbEvenDispatcherPrefixExact`: reaches PC 1549, the Barrett backend entry.

`MultiLimbPrefix.lean` also defines the final backend-suffix interface:
`WideMultiLimbOddBackendSuffixExact` and `WideMultiLimbEvenBackendSuffixExact`.  These start from
the exact backend cursor, assume a backend-local gas expression, and return `RDxRet` against
`Model.output`.  The theorem `modexpSomeExactGasSpec_of_bounded_multiLimbBackendSuffix` composes
those two suffix proofs with all existing covered branches into the intended general
`BytecodeSpec`.

The shared result-allocation blocks for both residual branches are now proved as well:

- `wideMultiLimbOddAllocationPrefixExact`: reaches PC 1946 after Montgomery result allocation;
- `wideMultiLimbEvenAllocationPrefixExact`: reaches PC 1570 after Barrett result allocation.

The shared result-array allocation interface is:
`WideMultiLimbOddPostAllocationSuffixExact` and
`WideMultiLimbEvenPostAllocationSuffixExact`.  The theorem
`modexpSomeExactGasSpec_of_bounded_multiLimbPostAllocationSuffix` composes those narrower suffix
proofs with the checked dispatcher/allocation prefixes and all previously covered branches.

The odd Montgomery residual has now been pushed through the first temporary word-array allocation,
the first loop-entry test, the first copy-loop call-frame setup, the concrete checked-add helper for
the first index increment, the jump into the read-offset helper, and the checked
`modulusSize - 32` subtraction, the first full-word copy store, the subsequent loop guard, the
taken guard branch's call-frame setup for the second copy iteration, and that iteration's
checked-add helper, jump back to the read-offset helper, and checked `modulusSize - 64`
subtraction, the second full-word copy store, the subsequent loop guard, and the call-frame setup
for the third copy iteration, that iteration's checked-add helper, the jump back into the
read-offset helper, the checked `modulusSize - 96` subtraction, the third full-word copy store, and
the subsequent loop guard, and the taken guard branch's call-frame setup for the fourth copy
iteration, its checked-add helper, and the jump back into the read-offset helper.
The preferred current full-spec reduction is
`modexpSomeExactGasSpec_of_bounded_multiLimbFourthCopyReadSuffixes`; its remaining backend
obligations start at:

- odd Montgomery, if `3 < modulusSize / 32`: PC 1903, at the read-offset helper for the fourth
  copy iteration, with `i = 4` and three copied words committed to memory;
- odd Montgomery, if `2 < modulusSize / 32` and not `3 < modulusSize / 32`: PC 2865, the
  fall-through path after the third full-word copy;
- odd Montgomery, if `1 < modulusSize / 32` and not `2 < modulusSize / 32`: PC 2865, the
  fall-through path after the second full-word copy;
- odd Montgomery, otherwise: PC 2865, the fall-through path after the first full-word copy;
- even Barrett: PC 1603, at the leading-zero scan loop cursor.

The next substantial work is proving the residual multi-limb backend paths with their exact gas
expressions, and finally replacing the existential gas postcondition with a total bytecode gas
selector.

## Direct multi-limb Barrett dispatch

`MultiLimbBarrettDispatch.lean` fills the successor that the earlier Barrett caller development
did not need: after a direct leading-zero scan exit, a modulus longer than 32 bytes must reject the
one-word branch and enter the limb backend.  The theorem is separate because this keeps the
data-dependent scanner reusable while letting generated PC-local traces fix the concrete stack and
cost of the dispatch.  It proves PC 1646 to PC 1675 in 30 steps and exactly 111 gas, and the composed
PC 1592 scan-and-dispatch prefix in exactly 239 gas.  `symcheck run` independently reproduced the
30-step PC trace with exact SMT and no overapproximation.  The same segment validation was then
used to expose the first modulus-conversion call frame: PC 1675 reaches PC 2836 in 15 steps and 50
gas, and the generic helper reaches its allocator at PC 1487 in another 7 steps and 24 gas.

`MultiLimbBytesToLimbsCall.lean` extracts the PC 2847 length-load wrapper from the earlier
odd-backend-specific proof.  The extraction is needed because Barrett calls the same deployed
helper with a different continuation stack.  It does not weaken the contract: the new theorem
loads the concrete bytes length from active EVM memory and composes with every generated full-word
iteration plus the optional partial limb, retaining exact steps, memory, active words, and gas.

`MultiLimbBarrettConversionContract.lean` specializes those shared pieces to Barrett's first
modulus conversion.  It carries the direct backend from PC 1675 through allocation and all
`bytesToLimbs` iterations to the actual continuation at PC 1700.  The contract keeps allocator and
copied-memory facts explicit because those are layout obligations, not arithmetic assumptions;
the computation itself has no abstract callback or skipped loop.  Its fixed overhead is 109 steps
and 98 gas, plus the executable allocator and per-input conversion gas expressions.

`MultiLimbBarrettReduceBaseContract.lean` connects that continuation to the already complete
`reduceBase` prefix. PC 1700 reaches the helper entry at PC 2957 in exactly five steps and 18 gas,
with stack `base, n, k, 1707, n, ...`; `symcheck run` independently produced that stack and cost
solver-free with no overapproximation. The composed nonempty theorem then executes the selected
base-width allocation, every base conversion iteration, and the concrete remainder allocation to
the actual schoolbook entry at PC 5199. This bridge was needed because leaving the two contracts
separate did not prove that the converted modulus and preserved continuation words supplied the
operands consumed by `reduceBase`.

`MultiLimbReduceBaseContract.lean` continues the even-modulus execution through Solidity's
`reduceBase`.  This file was added because the Barrett route must not assume that the base already
fits in `k` limbs: it computes `baseK = max(ceil(baseLen / 32), k)`, converts every base byte, and
then enters the real schoolbook division.  The nonempty contract reaches PC 5199 after both the
`baseK`-limb conversion allocation and the `k`-limb remainder allocation.  Its exact setup is 28
steps/103 gas, or 34 steps/123 gas when the `baseK < k` assignment executes; the remaining cost is
given by the two concrete allocator costs and generated `bytesToLimbs` loop cost.  The empty-base
contract separately proves the zero-array allocation and return in 99 steps and exactly
`71 + newWordArrayGas` gas.  Independent `symcheck run` traces were used to validate all four
continuation stacks (PCs 2995, 3005, 3023, and 5199) with exact SMT and no overapproximation.

`MultiLimbSchoolbookZeroContract.lean` closes the zero-effective-dividend exit after the division's
leading-zero trim.  The separate contract is necessary because Solidity first allocates a
one-limb zero quotient even though `schoolbookRem` ultimately discards it.  It proves PC 5229
through the internal return in 65 steps with the concrete quotient memory and exact
`42 + shortAllocationGas` cost; a matching `symcheck run` reached the return continuation in the
same 65 instructions with exact SMT and no overapproximation.

`MultiLimbSchoolbookDivisorExitContract.lean` adds the previously missing normal exit from the
divisor-leading-zero scan.  SymCheck fixed its PC 5237 to PC 5266 trace at 55 instructions; the
Lean contract proves exactly 202 gas while loading the concrete top divisor limb.  This segment is
needed to use the source-level Barrett invariant that the converted modulus has a nonzero top
limb, rather than silently assuming the scan has already happened.

`MultiLimbSchoolbookNonzeroPrefix.lean` composes both scans from the actual PC 5199 entry. It
accepts any number of explicitly allocated high zero base limbs, proves the next effective base
limb takes the nonzero exit, transfers the positive length, and proves the converted modulus's
concrete top limb takes the nonzero divisor exit. The result reaches PC 5266 in exactly
`118 + 72*zeroLimbs` steps and `431 + 270*zeroLimbs` gas. This composition was needed because the
Barrett caller allocates `max(ceil(baseLen/32), k)` base words, so skipping the scans would either
exclude valid padded bases or assume the effective length consumed by division.

That file also exposes `sizeBranchPc`, an executable selector for the next deployed branch:
`m < k` selects the short-copy cursor at PC 6214 and the complementary case selects Knuth setup at
PC 5287. `selectedSizeBranchExact` proves either selection from PC 5266 in exactly 16 steps and 60
gas, and the composed scanner-plus-selector theorem has exact cost
`134 + 72*zeroLimbs` steps and `491 + 270*zeroLimbs` gas. Exposing the selected PC was necessary
to keep later path-sensitive composition executable instead of existentially choosing a branch or
gas value.

`MultiLimbSchoolbookShortFunction.lean` then composes both scans with the complete short-dividend
implementation.  For every positive effective dividend of `m < k` limbs, including any number of
allocated zero limbs above it, the theorem executes the one-limb quotient allocation and all `m`
remainder-copy iterations through the internal return.  Its exact cost is
`202 + 58*m + 72*zeroLimbs` steps and
`540 + 208*m + 270*zeroLimbs + shortAllocationGas` gas.

`MultiLimbSchoolbookKnuthPrefixContract.lean` begins the remaining `k <= m` branch at the actual
post-size-check PC.  It composes quotient allocation, the `(m + 1)`-word normalized-dividend
allocation, the real `MCOPY`, the checked top-divisor address/load, and the deployed `_clz` helper
through PC 5368, with concrete memory and exact path-sensitive steps and gas.  Supporting this
prefix required widening `newWordArrayExact` from 32 to 33 words.  This is not an input-bound
relaxation: a valid maximum 32-limb dividend makes Solidity allocate a 33-word `u` temporary, so
retaining the old proof-only allocator bound would incorrectly exclude that valid computation.
The underlying byte-allocation execution theorem was correspondingly widened from 1024 to 1056
payload bytes; the bytecode and allocation model are unchanged.

While composing the following normalization phase, the interface of
`shiftAllDividendLimbsExact` was corrected to distinguish the divisor-loop carry from `kEff`.
The old theorem statement reused one Lean variable for both stack positions and therefore imposed
an unintended equality between unrelated runtime values.  The deployed code pops the carry before
the dividend loop, so the corrected contract accepts an arbitrary carry and leaves execution,
memory, steps, and gas unchanged.

The same composition showed that `loadNormalizedTopExact` unnecessarily fixed the carried
normalization marker to `1`.  That block does not inspect the marker, while the actual zero-shift
path carries `0`; its contract now quantifies the marker so both deployed paths can reach the same
outer-loop cursor without misrepresenting either branch.

`MultiLimbSchoolbookNormalizationFunction.lean` composes the corrected contracts into both full
PC 5368 to PC 5450 normalization paths.  For `shift = 0`, it executes the deployed `MCOPY` in 152
steps with exact allocator, expansion, and copy gas.  For `shift > 0`, it executes all `kEff`
divisor shifts, all `m` in-place dividend shifts, the extra-limb carry store, and the normalized
top-limb load; its cost is the two executable loop recurrences plus 182 fixed steps and 337 fixed
gas, in addition to the concrete `v` allocation.  The split records genuinely different control
flow and gas while both paths arrive at the same outer quotient-loop cursor.

The normalized division contracts now quantify the carried zero/nonzero-shift marker instead of
fixing it to `1`.  The quotient loop never examines this word, and the earlier fixed statements
incorrectly excluded the valid zero-shift Knuth path.  The marker remains concrete and is consumed
by the deployed post-loop denormalization dispatch.  `skipAddBackExact` was also added for the
previously absent nonnegative top-subtraction edge from PC 5600 to PC 5601; it proves the real
one-instruction branch at exactly 10 gas.  An independent `symcheck run` reproduced the
`5600:JUMPI -> 5601:JUMPDEST` path in one step with exact SMT and no overapproximation.

The quotient operand loader was factored at its actual shared entry, PC 5458.  The first digit
reaches it through the six-instruction PC 5450 loop header, while every later nonterminal digit
falls through a single `JUMPI` from PC 5457.  The new common-body contract proves PC 5458 to
PC 5516 in 108 steps and 387 gas; its first-entry and continuation wrappers prove 114/410 and
109/397 respectively.  This split is required for the arbitrary-digit induction: reusing the
first-entry theorem for later digits would describe control flow the bytecode does not take and
would add five fictitious steps and 13 gas to each continuation.

`MultiLimbSchoolbookEstimateFunction.lean` composes the q-hat phase to the common
multiply-subtract cursor.  It executes the nonzero-high or zero-high 512-by-256 helper, checked
second-limb address calculations and loads, every state in an explicit generated refinement path,
and the multiply-subtract setup.  The fixed costs before refinement-cycle terms are 316 steps/1090
gas for a nonzero high word, 239/815 for a zero high word, and 201/678 for a nonwrapping saturated
estimate, starting at their respective estimate cursors.  The wrapping saturated estimate already
reaches the same cursor in the proved 40-step/115-gas source-fix branch.  Refinement contributes
exactly 55 steps and 185 gas per executed state.

The estimate composition also now covers `_refineQhat`'s distinct overflow break.  A taken
refinement condition decrements `qHat`, adds `vTop` to `rHat`, and returns immediately when that
addition wraps; it does not pass through the normal false-condition exit represented by the
earlier path certificate.  `qhatOverflowReturnExact` proves the decrement, taken overflow guard,
and dynamic return in 28 steps/97 gas, and `refinedOverflowExact` composes the second-limb loads
and multiply-subtract setup for a total of 192 steps/648 gas from PC 5792.  This path cannot be
excluded for arbitrary inputs because it is an explicit source-level Algorithm D control path.
An independent `symcheck run` with a wrapping `rHat + vTop` reproduced the complete
`8511:JUMPI -> 8537:JUMPI -> 8567:JUMPDEST -> 5846:JUMPDEST` route in exactly 28 steps, with
exact SMT and no overapproximation.

The overflow contract is generalized to an explicit non-overflowing refinement prefix followed
by the break.  This is needed because a normalized estimate can complete one ordinary decrement
and then wrap while attempting the next one; modeling only an overflow on the first attempted
decrement would omit that valid Algorithm D path.  The generalized estimate theorem charges
`55*states.length + 192` steps and `185*states.length + 648` gas from PC 5792, so both the normal
and overflow exits retain the exact number of executed refinement cycles.

`MultiLimbSchoolbookEstimateSelector.lean` closes the branch point at PC 5516 with a seven-case
certificate: ordinary nonzero/zero estimates with normal or overflow refinement exits,
nonwrapping saturated estimates with normal or overflow refinement exits, and the wrapping
saturated shortcut.  Every constructor fixes the actual computed `qHat` and exact path cost, and
`estimateExact` proves all constructors reach PC 5563.  A closed arithmetic certificate is used
instead of accepting an execution/result callback, because the latter would allow the outer loop
to assume the very estimate computation that the proof is intended to verify.

`MultiLimbSchoolbookDigitFunction.lean` completes an accepted quotient digit from that common
cursor through PC 5457.  The direct path executes all `kEff` multiply-subtract limbs, top
subtraction, and the concrete quotient write in `78*kEff + 67` steps.  If the computed top
subtraction is negative, the correction path additionally executes all `kEff` add-back limbs,
the saved-top carry addition, and writes `qHat - 1`, for `134*kEff + 109` steps.  Both gas formulas
retain every memory-expansion and per-iteration term rather than replacing the arithmetic update
with a postulated result.

`MultiLimbSchoolbookIterationFunction.lean` closes one complete quotient digit by pairing a
certified estimate with the computed direct or add-back outcome.  Its `ValidDigit` constructors
fix the exact post-subtraction memory, active-word count, quotient store, steps, and gas, and
`iterationExact` composes that result from PC 5516 through PC 5457.  Carrying the concrete memory
in the result is necessary for the outer induction: every later estimate must load the `u` limbs
written by all earlier multiply-subtract and add-back iterations.

`MultiLimbSchoolbookOuterLoopFunction.lean` performs that memory-threading induction for an
arbitrary quotient length.  Its base case is the real terminal stack at PC 5457; every step takes
the single deployed continuation `JUMPI`, reloads `u[cursor-1+kEff]` and its lower neighbor from
the current memory, executes one closed iteration certificate, and recurses on `cursor-1` using
the resulting memory and active-word count.  `divisionLoopExact` adds the distinct one-time
PC 5450 entry.  The split preserves 114 steps/410 gas for the first operand load and 109/397 for
each continuation, while retaining every estimate, refinement, multiplication, correction, and
memory-expansion term in the accumulated exact result.  This recurrence is required to establish
the deployed multi-digit computation; a collection of isolated one-digit theorems would not show
that later digits consume the writes produced by earlier digits.

`MultiLimbSchoolbookDivisionFunction.lean` composes the arbitrary quotient loop through the
internal return for both normalization outcomes.  The positive-shift theorem runs the complete
right-shift/neighbor-merge recurrence and has fixed overhead 143 steps/509 gas around the first
digit, continuation result, and denormalization recurrence.  The zero-shift theorem runs the
direct-copy recurrence and has exact total overhead `144 + 58*kEff` steps and
`510 + 208*kEff` gas around the per-digit result.  Keeping two theorems is necessary because the
Solidity source has two different remainder loops with different operations and exact gas.

`MultiLimbSchoolbookZeroShiftRemainderContract.lean` closes the marker-0 quotient-loop exit that
the normalized right-shift contract cannot cover.  It proves the actual direct `u[i] -> rem[i]`
copy loop for arbitrary `kEff`, including both array checks, the concrete load/store, index update,
loop exit, and dynamic return.  From PC 5457 the complete branch costs exactly
`58*kEff + 30` steps and `208*kEff + 100` gas under the already allocated-array layout.  A
`symcheck run` separately established the dispatch prefix as the 17-step/58-gas
`5457:JUMPI -> 5911:JUMPI -> 6032:JUMPDEST` path with exact SMT and no overapproximation.  This
separate proof is necessary because zero shift is a valid Knuth input path, not a Solidity input
alignment exception, and it executes a different source loop from denormalization.

`MultiLimbSchoolbookIterationSemantic.lean` begins the concrete-to-pure bridge for an accepted
quotient digit. It records the exact divisor and dividend words loaded by every evolving-memory
multiply-subtract state and proves, for an arbitrary limb count, that the produced low words,
final carry, and final borrow are exactly `knuthSubtractDigits`. It likewise proves that every
concrete add-back state is exactly the pure `evmAddLimbs` recurrence. This observation layer is
needed because the loops update `u` in place: appealing directly to a fixed initial list would
silently assume that later loads are unaffected. The following layout lemmas will prove that the
observed words are the intended initial array slices and that the produced words occupy the final
window; the arithmetic equalities themselves are already derived from the executed recurrence,
not supplied through a result callback.

`MultiLimbSchoolbookQhatSemantic.lean` now proves the Algorithm D estimate bounds for the
refinement overflow exit as well as the normal exit. The new proof converts the taken generated
`(rHat + vTop) < vTop` guard into the unbounded fact
`2^256 <= rHat + vTop` via the EVM addition-carry equation, proves that the concrete returned word
is `qHat - 1`, and derives both the never-too-low and at-most-one-overestimate inequalities. This
was necessary because executing the overflow branch alone did not justify feeding its q-hat into
the pure accepted-window theorem; excluding it would omit a valid normalized Algorithm D path.

`MultiLimbSchoolbookEstimateSemantic.lean` closes the arithmetic side of the seven-case estimate
selector. Ordinary cases derive the top-two-word equation and proper remainder from the verified
`div512by256` model; normal and overflow refinement exits then use their corresponding q-hat
semantic theorems. Saturated cases use the outer loop's reduced-window bound, including the
source shortcut where `uLo + vTop` wraps before any second-limb comparison. The context also ties
the selector's existential second-limb values back to the same concrete memory loads used to form
the pure divisor and window. That identification is required: without it, a selector certificate
could establish a path for unrelated second digits while claiming bounds for the real arrays.

The iteration semantic bridge also proves the exact natural addresses for the bytecode's `v[i]`
and wrapped `u[current + i - 1]` expressions, preserves active words and memory size over
arbitrary loop ranges (including the valid 33-word `u` allocation boundary), and supplies generic
above/below frame theorems for all in-place multiply-subtract writes. These facts are needed to
replace the observed-word arithmetic recurrence with initial array slices and final memory slices.

The same bridge now carries the multiply-subtract result through the saved top-word subtraction:
an induction over the ascending writes identifies every pre-write operand with the original
divisor/current-window slices, a second induction identifies every produced word with the final
concrete memory slice, and the top load, stored top word, and negative flag are proved equal to
`knuthSubtractWindow`. Collector-free statements are necessary here because later quotient digits
consume memory, not the proof-only lists used to describe the recurrence; merely proving the list
recurrence would not establish that the deployed code stored its result.

The correction add-back loop has an analogous concrete-memory proof. Its generated `v[i]` and
wrapped `u[current+i-1]` addresses are shown to remain in the existing allocation, active words and
memory size remain fixed, earlier ascending writes preserve every future operand, and later writes
preserve every earlier result. Consequently `evmAddLimbs` over the correction-entry slices is
exactly the final concrete lower window and carry. This separate argument is needed because the
negative subtraction path mutates `u` a second time; treating add-back as a pure postcondition
would skip the very correction computation whose equivalence must be proved.

The correction proof now also spans the phase boundaries around that loop. It proves that the
multiply-subtract and saved-top subtraction leave the divisor and memory size unchanged, that the
add-back leaves the saved top word untouched, and that the deployed final top-carry write stores
exactly `knuthAddBack.top`. Together with the lower-slice theorem, `correctionTop` now matches the
pure add-back result in concrete memory. This was required to cover the negative estimate path
without replacing either the lower correction loop or its discarded top overflow with a model
callback. While establishing this result, the unused `htopFit` premise was removed from
`topResult_eq_knuthSubtractWindow`: the existing pointer-fit bound plus the top word's memory and
active-word bounds already prove every access fact, so retaining the extra premise would overstate
the valid-input exclusions.

`MultiLimbSchoolbookDigitSemantic.lean` composes these memory theorems with the seven-path
estimate selector. `concreteCoreResult_eq_acceptedWindowResult` proves that the direct and
corrected concrete memories denote the same quotient digit and remainder as the pure
`acceptedWindowResult`; `validEstimateConcreteCore_eq_div_mod` then uses the selector's proved
never-low/at-most-one-overestimate bounds to obtain ordinary natural division and remainder for
the concrete window. This layer is necessary to connect trace execution to the pure model: an
exact PC/gas theorem plus an independently correct Algorithm D theorem would not establish that
the words loaded and stored by this execution are the model's operands and results.

The same file verifies the final quotient store rather than stopping at `correctionTop`. It proves
that the checked `qHat--` word has natural value `qHat-1`, that an allocated quotient write below
`u` preserves every lower and top remainder word, and that both `ValidDigit` constructors store
the quotient component of `concreteCoreResult` while preserving its remainder component, active
words, and byte-array size. The explicit quotient-below-`u` premise records allocator separation;
it does not bypass arithmetic and is needed because the final store mutates the same byte array
threaded into the next outer iteration.

`MultiLimbSchoolbookIterationComplete.lean` packages one exact execution certificate with the
concrete array-layout facts that identify its divisor and dividend slices. It proves that the
stored quotient word and updated `u` window are exactly natural division and remainder, and adds
a frame theorem for an already-written higher quotient word. This sidecar is needed because the
execution certificate intentionally fixes PCs, memory, steps, and gas but does not by itself say
which natural-number operands those bytes represent; combining the two avoids weakening the
execution theorem with a model-result callback.

`MultiLimbSchoolbookOuterComplete.lean` folds those complete iterations in the deployed descending
quotient-index order. The new induction proves that each lower write retains all higher quotient
words, reconstructs the final little-endian quotient array from the pure MSB-first division fold,
and identifies it with ordinary natural division. A separate nonempty-chain induction identifies
the final low `u` window with the fold remainder and hence ordinary modulo. The remainder theorem
is separate because the last iteration writes a fixed low window whereas intermediate iterations
write successively shifted windows; merely accumulating quotient digits would leave the executed
remainder and the later denormalization loop unrelated.

The same chain now carries exact continuation steps and gas as type indices and includes the
outer operand-layout certificate used by the generated load trace. Forgetting the semantic fields
therefore produces `ValidContinuations` with the same final memory and explicit aggregate cost.
`semanticDivisionLoopExact` runs that certificate from PC 5450 and exposes exactly
`chainSteps + 5` steps and `chainGas + 13` gas: five steps and thirteen gas are the measured
difference between the first operand-load prefix and a later PC 5457 continuation prefix. Costs
were made indices rather than existential outputs so callers receive an exact path-sensitive gas
expression and cannot satisfy the theorem by choosing an unspecified gas witness.

`MultiLimbSchoolbookNormalizationSemantic.lean` supplies the previously missing arithmetic
meaning of the positive-shift setup loops. It proves the exact one-word carry equation for the
generated `shiftedWord`/`shiftedCarry` operations, lifts it to arbitrary little-endian word lists,
and independently lifts it over collectors defined by the concrete evolving-memory
`shiftDivisor` recurrence. Appending the returned carry therefore yields the observed source value
multiplied by `2^shift`. Defining the second theorem over the execution recurrence is necessary:
a pure list-shift lemma alone would not show that the bytecode's in-place dividend pass and
separate divisor pass perform that list transformation.

That normalization bridge now also proves the concrete memory identifications. Generic guarded
store lemmas show that ascending writes preserve every future source word for both allocator
orders: the in-place `u` pass writes below later reads, while the separately allocated `v` pass
writes above the original divisor. A second induction proves every emitted word remains in the
final destination slice. The explicit `u[m]` carry store is then shown to materialize the appended
carry as the real extra dividend limb. Finally, the recurrence's divisor carry is traced back to
the original top source word and proved zero from the executed CLZ model's positive shift. These
steps are needed to rule out treating normalized arrays or the no-overflow top condition as
postconditions supplied by the caller.

`MultiLimbSchoolbookDenormalizationSemantic.lean` now connects the already proved
`denormalizeRange` execution recurrence to final memory. A two-step induction mirrors the
bytecode's terminal one-store cycle and nonterminal low-store/neighbor-load/final-store cycle;
allocator separation proves writes to `rem` preserve every source word in `u`, while ascending
destination order preserves earlier outputs. The final concrete `rem` slice is therefore exactly
`denormalizeWords` of the terminal normalized `u` slice, and its natural value is division by
`2^shift`. This memory theorem is necessary because the earlier pure cross-limb shift theorem did
not establish that the trace recurrence read those source words or left its outputs in the array
returned to the caller.

`MultiLimbSchoolbookZeroShiftRemainderSemantic.lean` supplies the corresponding final-memory
proof for the marker-0 branch. Induction over the actual `copyRange` recurrence proves each source
word in `u` survives earlier `rem` writes, each copied word remains after later writes, and the
final concrete remainder slice equals the terminal `u` slice word for word. This separate theorem
is required because shift zero executes direct copies rather than the cross-limb right-shift model;
folding it into the positive-shift theorem would either misstate the code path or lose exact gas.

`MultiLimbSchoolbookCompleteSemantic.lean` closes the quotient-loop/remainder-loop boundary. It
proves the cursor-1 generated addresses are exactly `u[0..count]`, derives the divisor-list length
from the concrete `v` slice, and combines reduced modulo with the radix bound to force the extra
terminal `u[count]` word to zero. The lower `u` slice is consequently the exact normalized modulo
consumed by both return branches. The same file cancels the positive normalization factor from
the proved quotient and from the concrete denormalized remainder, while the marker-0 copy returns
the unscaled modulo directly. Deriving the top zero is necessary because the deployed return loops
copy only `count` words; assuming it would leave a possible discarded high word unverified.

The iteration certificate also now exposes a frame theorem for lower, not-yet-consumed `u` words.
Its only additional premise is the concrete address ordering between the quotient destination and
the selected source word. This was needed for the overlapping-window composition: an iteration
updates its current high window, while every later iteration introduces one lower original word.
The address premise records the allocator layout and supplies no arithmetic result; the preserved
word equality is derived through the complete direct/add-back digit execution and final quotient
store.

`MultiLimbSchoolbookOuterComplete.lean` now uses that frame result to close the overlapping-window
input gap. Generated addresses are proved equal to ordinary array addresses, each executed modulo
is shown to fit in the low `count` output words with a zero high word, and a telescoping induction
identifies the fold's entire MSB-first input value with the initial normalized `u` array. The only
new composition premise orders quotient writes before lower `u` sources, which follows from the
deployed consecutive allocations. This change was needed to remove the earlier caller-supplied
equality for `digitsToNatMSB inputs`; retaining that equality would have allowed an unrelated digit
list to stand in for the words actually consumed by the quotient loop.

`MultiLimbSchoolbookCompleteSemantic.lean` now uses the overlap theorem at the public schoolbook
composition boundary. Its positive-shift quotient and remainder results no longer accept abstract
equalities for either the fold input list or the divisor list. They require equalities about the
actual normalized `u` and `v` memory slices, which are exactly the conclusions of the concrete
normalization recurrences proved above; the zero-shift copy theorem likewise uses the concrete
unscaled slices. The first iteration's generated divisor loads are also proved identical to the
ordinary `v` array slice. This change was needed so callers cannot choose model operands unrelated
to the bytes read by division while still allowing the allocator's pointer-order facts to remain
explicit alignment premises.

`MultiLimbSchoolbookShortSemantic.lean` closes the arithmetic side of the selected
short-dividend branch. It proves that the deployed copy loop leaves every higher remainder word
unchanged, that the final fixed-width remainder denotes exactly the concrete effective dividend,
and that this value is ordinary modulo the concrete divisor. The proof uses the nonzero concrete
top divisor limb to derive the required size inequality, rather than accepting a caller-provided
`dividend < divisor` fact. Its high-word-zero premise records the actual zero initialization of the
preallocated remainder array; this premise is necessary because the bytecode deliberately copies
only the `m` effective dividend words into a `k`-word result, and it is an allocator/memory-layout
condition rather than an arithmetic-result callback.

`MultiLimbReduceBaseShortSemantic.lean` discharges that zero-initialization premise for the real
nested `reduceBase` allocations. Immediately after the remainder allocation only its header is
materialized and the payload is EVM zero padding; the short branch then allocates a one-word
quotient beyond the payload, extending the concrete byte array across the gap. The new proof shows
that the later header/free-pointer writes preserve every padded remainder word and derives all
`k` words as zero from allocator sizes and active-memory bounds. This file was needed because
assuming an abstract zero-filled remainder would leave the untouched high words disconnected from
the actual allocation trace.

`MultiLimbBarrettConstantContract.lean` continues the executed even-modulus path after
`reduceBase`. SymCheck measured the PC 3010 return trampoline as five steps/17 gas and showed that
it discards only schoolbook division's unused quotient pointer before returning the concrete
remainder at PC 1707. The Lean contract then enters `_computeBarrettConstant` and proves both
checked-arithmetic non-revert edges used to form `dLen = 2*k+1` for every `k <= 32`, reaching
PC 3094 in another 28 steps/99 gas with the exact continuation stack. This segment was needed to
avoid assuming the Barrett dividend length or skipping Solidity's overflow checks; it also exposes
the genuine next proof obligation, an allocation of up to 65 words rather than the 33-word maximum
needed by the earlier normalized-dividend temporary.

`Allocation.lean` therefore now proves the unchanged compiler word-array allocator for up to 65
words and its underlying aligned byte allocation for up to 2080 payload bytes. The existing
33-word and 32-word theorem interfaces remain wrappers around the wider result, so previous
callers retain their original bounds. This proof-interface change is required specifically by
`_computeBarrettConstant` at valid `k = 32`, where `2*k+1 = 65`; excluding that allocation would
discard a valid public ModExp input rather than represent a Solidity alignment restriction.
The zero-byte allocator call in `Dispatcher.lean` now supplies the corresponding widened
`0 <= 2080` proof instead of the old `0 <= 1056` proof. This caller update is required only
because that proof argument was annotated positionally; the call still allocates zero bytes and
its execution, memory, and gas theorem are unchanged.

`MultiLimbOddCompareContract.lean` now also exposes a fit-based form of the ordinary Solidity
array-element address theorem. The original comparison-loop wrapper remains capped at 32 limbs,
but `_computeBarrettConstant` writes dividend element `2*k`, whose valid maximum is 64. The new
form removes that unrelated loop bound and derives non-wrapping solely from the full address-fit
premise; this is a proof-interface extension only and does not change bytecode or memory layout.

The Barrett-constant contract now records the exact PC 3094 allocation setup boundary separately:
eight instructions and 29 gas place `dLen = 2*k+1`, the post-allocation element-store
continuations, and the outer return address on the allocator stack. Isolating this generated-trace
segment is needed so the existing allocator theorem can be composed without hiding or recounting
the caller's path-sensitive stack and gas behavior.

That setup is now composed with `newWordArrayExact65`, reaching PC 3111 after exactly 86
instructions with gas `29 + newWordArrayGas aw fp (2*k+1)`. The theorem carries the allocator's
actual header-only concrete memory and expanded active-word count, so the forthcoming high-limb
store must be proved against the real zero-initialized EVM allocation rather than an abstract
dividend supplied by the caller.

`MultiLimbBarrettConstantContract.lean` now derives the allocated header load and final-element
geometry from that concrete allocation. The bounds-check helper reads `dLen`, proves
`2*k < dLen`, and reaches PC 3118 in exactly 21 steps/76 gas. The following MSTORE is proved to
target `fp + 32*(2*k+1)`, the last payload word, and to incur no memory expansion; it writes the
single high limb of `B^(2*k)` and reaches the `k`-word remainder allocator at PC 1487 in another
13 steps/45 gas. These links are necessary to establish that schoolbook division receives the
actual sparse power-of-radix dividend constructed by bytecode, rather than a modeled numerator
assumed at its entry.

The same contract now derives the second allocator's full concrete precondition set from the first
allocation and high store: memory extends exactly to the advanced free pointer, the `0x40` word
contains that pointer, and the active-word product is both above 64 bytes and non-wrapping. The
composed `divisionEntryExact` theorem reaches schoolbook PC 5199 after exactly 198 steps with gas
`150 + newWordArrayGas aw fp (2*k+1) + newWordArrayGas dividendAw remainderPtr k`. Its stack is the
real `(remainder, 2*k+1, dividend, 3124, k, modulus)` call frame. This composition is needed to
expose the verified divider without existential gas or an assumed intermediate allocator state.

`MultiLimbBarrettConstantSemantic.lean` begins the representation proof required at that divider
entry. It derives every dividend element address from the allocated geometry, proves the second
allocation preserves the complete first payload, proves indices below `2*k` still read as zero
padding, and proves index `2*k` reads the one written at PC 3119. This separate semantic layer is
needed because the exact execution theorem alone identifies byte-array writes but does not yet
establish that their little-endian limb value is the pure numerator `B^(2*k)`.

That semantic layer now also proves both generated allocators' active-word geometry, so the
divider's guarded MLOADs are shown to take their concrete-memory branches rather than merely
having the expected bytes underneath an unproved guard. It lifts the preserved zero words and the
stored high one to schoolbook `arrayWord` values and evaluates the complete `2*k+1`-limb array to
exactly `UInt256.size^(2*k)`. The positive-`k` premise is required by the real multi-limb Barrett
branch and by the second nonempty allocation; the two address-fit premises are the allocator's
existing non-wrapping conditions. No arithmetic input or computation path is excluded by these
conditions.

`MultiLimbSchoolbookKnuthSetupSemantic.lean` now gives the Knuth setup's generated `MCOPY` its
missing per-word semantics. For every index in the copied range, the destination `u` word is
byte-for-byte the corresponding dividend word; the proof treats `ByteArray.write` as reading from
the original source snapshot, so it remains valid when source and destination ranges overlap as
required by EIP-5656. This bridge is needed to carry the concrete Barrett numerator into the
normalized division arrays instead of assuming the copied `u` value at PC 5368.

`Allocation.lean` now extends the same unchanged allocator proof one further word, from 65 to 66
words (`2112` payload bytes and `2144` bytes including the array header). The 65-, 33-, and 32-word
interfaces remain wrappers. This additional word is required after the Barrett numerator enters
Knuth division: a maximum `2*k+1 = 65`-word dividend is normalized into Solidity's `m+1 = 66`-word
`u` temporary. Excluding that allocation would drop valid `k = 32` inputs, so the bound is widened
instead; allocation execution and exact gas formulas are unchanged. `Dispatcher.lean` again only
updates its positional zero-byte proof annotation to the widened byte bound. When the shared
allocator interface was subsequently widened to 68 words (`2176` payload bytes), that annotation
also had to use `0 ≤ 2176`: its argument is still the concrete zero-length allocation, and the
change only matches the theorem's new proof-level bound rather than changing dispatcher execution.

The corresponding schoolbook proof interfaces now admit the internally constructed Barrett
sizes: dividend trimming and size dispatch accept 65 words, Knuth quotient allocation accepts up
to 65 words, and normalized-`u` allocation accepts 66. The original divisor remains capped at 32
words because it comes directly from the accepted ModExp modulus. These edits only replace prior
proof bounds and route the larger temporaries through `newWordArrayExact66`; all generated trace
segments, selected PCs, step counts, gas formulas, and memory definitions are unchanged. The
widening is necessary because `_computeBarrettConstant` deliberately calls the same schoolbook
divider with a numerator larger than any public operand array.

`MultiLimbBarrettConstantSemantic.lean` now specializes the schoolbook quotient pointer,
quotient length (`k+2`), and normalized-`u` pointer to the exact successive allocator layout. It
proves both allocations preserve every Barrett dividend word and then applies the overlap-safe
`MCOPY` theorem to show all `2*k+1` words at the copied `u` destination equal the original concrete
numerator. This bridge is required before normalization because the quotient and `u` allocations
write headers and advance `0x40` between the divider entry and the copy; skipping those memory
frames would leave the pure numerator disconnected from the actual PC 5368 state.

The same semantic module now computes the exact active-memory word count after those allocations
and the generated `MCOPY`. It proves that the counter covers the entire `2*k+1`-word copied
numerator and remains below the EVM address modulus. This lemma is needed because schoolbook's
`arrayWord` loads are guarded by active memory: byte equality alone would not show that the
deployed execution takes the concrete-load branch instead of returning its out-of-range default.

It now also proves the concrete `u` memory size after `MCOPY`, derives the ordinary element
addresses under the 66-word allocation fit condition, and lifts every copied word through those
guarded loads. The low `2*k` limbs are zero, limb `2*k` is one, and the complete copied input
therefore denotes exactly `UInt256.size^(2*k)`. These results are required to instantiate the
normalization and Knuth-division models with the bytecode-built Barrett numerator; no abstract
numerator or quotient is assumed at the divider boundary.

`MultiLimbBarrettConstantContract.lean` now also exposes the PC 3124 return continuation that will
close `_computeBarrettConstant`: it discards schoolbook division's remainder and returns the
quotient in exactly four instructions and 14 gas. A fresh `symcheck run --pc 3124
--target-pc 1718` independently reached the caller with only the quotient on the stack and no
solver weakening or over-approximation. Recording this small segment is necessary so the final
constant theorem has an exact, path-sensitive return cost and does not stop at an internal PC.

The Barrett semantic module now specializes the complete arbitrary Knuth quotient theorem to the
real dimensions `m = 2*k+1`, `uCount = 2*k+2`, and `numQ = k+2`. Once the deployed normalization
arrays are proved to be the concrete numerator and modulus multiplied by their common `2^shift`
factor, the concrete quotient array is forced to denote `UInt256.size^(2*k) / modulus`. This is a
composition boundary, not an assumption of the final result: the remaining work is to derive
those normalized-array equalities from the copied memory and instantiate the executed semantic
continuation, whose certificate includes every quotient-digit computation and exact gas total.

The concrete memory chain now continues through allocation of normalized divisor `v`. Its fresh
pointer is exactly one word beyond the bytes copied into `u`; allocating the `v` header therefore
materializes the otherwise implicit extra `u[m]` word as zero padding. The proof derives the new
active-word range, preserves every prior zero/one numerator limb under guarded loads, proves the
extra top limb is a guarded zero, and evaluates all `2*k+2` pre-normalization `u` words to
`UInt256.size^(2*k)`. This step is needed because Knuth normalization consumes `m+1` words, while
`MCOPY` deliberately copies only the original `m`-word dividend.

This extension also identifies a required semantic generalization for the next step. Existing
`MultiLimbSchoolbookNormalizationSemantic` slice theorems assume every destination word already
lies inside the concrete `ByteArray`; the generated Solidity allocator initially writes only the
fresh `v` header, and the normalization loop materializes its payload low-to-high by appending at
the current end. The Barrett proof will add an append-aware form of that semantic argument rather
than assuming a pre-materialized payload or excluding valid inputs. Execution and gas are
unchanged; only the proof model must reflect the allocator's actual concrete-memory representation.

That shared semantic generalization is now implemented. A frontier store is proved to extend the
concrete byte array by exactly 32 bytes, read back as the shifted word through the deployed active
memory guard, and preserve every earlier concrete source word. Induction over `shiftDivisor` then
shows that its operational input collector is the original source slice, its final appended
destination slice is the complete output collector, and the slice plus returned carry denotes the
source multiplied by `2^shift`. This change was needed because the former in-bounds-only theorem
could not describe Solidity's real header-only fresh allocation; it does not alter bytecode,
selected paths, recurrence arithmetic, steps, or gas.

The append-aware proof is now specialized to the positive-CLZ Barrett layout. It derives every
fresh `v[j]` address and active-memory bound from the allocator, proves CLZ makes the outgoing top
carry zero, and evaluates the actual normalized divisor as `modulus * 2^shift`. It then proves the
appended `v` pass preserves all original `u` words, computes the exact enlarged concrete memory,
and applies the in-place shift plus final carry store to show the execution contract's
`positiveMemory` dividend is `UInt256.size^(2*k) * 2^shift`. The proof distinguishes the `m`
source words shifted by the loop from the extra preallocated `u[m]` carry destination; this was
needed to match the bytecode recurrence rather than treating all `m+1` words as source input.

The zero-CLZ branch is now connected to the same concrete values. Its generated `MCOPY` is proved
to preserve the complete normalized-`u` array, copy every modulus limb into `v`, maintain the exact
active-word coverage, and leave the two slices denoting `UInt256.size^(2*k)` and `modulus`
respectively. This separate proof is required because zero normalization executes a copy while
positive normalization executes limb shifts; keeping those paths distinct preserves their exact
path-sensitive execution and gas without weakening the common arithmetic result.

The positive branch also required a missing memory-frame fact after the divisor had been
normalized. `MultiLimbSchoolbookNormalizationSemantic.lean` now proves that a source word above
every in-bounds normalization store survives the complete low-to-high shift loop. The Barrett
specialization applies it to show that the later in-place `u` shift and final carry store, both
strictly below `v`, preserve every normalized modulus limb in the final memory passed to Knuth.
This change is needed to rule out aliasing from the actual allocator geometry rather than silently
reusing the divisor value from an earlier memory state; it changes neither bytecode nor gas.

Finally, `barrettPositiveConstantQuotient_eq` and `barrettZeroConstantQuotient_eq` instantiate the
common-shift arithmetic theorem on the two concrete final normalization memories. In either real
branch, any completed schoolbook semantic continuation is forced to store exactly
`UInt256.size^(2*k) / modulus` in the `k+2`-word quotient array. The continuation is deliberately
still explicit at this boundary: the next proof step must construct it from the PC 5450 quotient
loop, including every quotient-digit computation and its exact gas, rather than treating the
computed quotient as an input assumption.

`MultiLimbBarrettReduceBaseComplete.lean` now closes the corresponding base-reduction boundary.
Its exposed `Selection` has four constructors matching the deployed PC 5199 dispatch: an all-zero
dividend, a positive short dividend, zero-CLZ Knuth division, and positive-CLZ Knuth division. The
two Knuth constructors contain the actual generated quotient/correction selector, and selector
projections expose the final memory, active-word count, exact steps, and exact gas. The common
`Selection.exact` theorem reaches PC 1707 for every constructor, while
`Selection.result_eq_entry_mod` proves that the same selected execution stores the full original
dividend modulo the full original divisor. In particular, high trimmed zero limbs are reconnected
to the entry value instead of changing the semantic input to the shorter observed array.

Constructive selection requires one additional premise, `fp + 32 * 69 < 2^64`. This is the
largest branch-local allocator extent: quotient, `(m+1)`-word normalized dividend, and divisor
allocations use at most 69 EVM words, including headers, when `m <= 32`. The premise was added
because the generated allocation contracts model Solidity's checked 64-bit memory arithmetic and
the previous one-word bound did not imply the later three allocations. It is only a minor
Solidity allocator/alignment exclusion: it does not constrain operand values, CLZ outcomes,
q-hat estimates, correction branches, quotient digits, or the modulo computation itself.

`MultiLimbSchoolbookEstimateExecutable.lean` now constructs the previously explicit q-hat
execution certificate for every normalized divisor top word. It follows the generated loop's
actual comparison and overflow guards: immediate completion, overflow on the first attempted
decrement, one non-overflowing decrement followed by completion, or overflow on the second
attempt. The existing normalized-path bound rules out a second successful decrement. This
constructor is then split across the bytecode's ordinary-zero, ordinary-nonzero, saturated, and
wrapped-sum selectors, returning the concrete `EstimateResult` whose fields retain exact
path-sensitive steps and gas. The change is needed to derive execution for arbitrary limb values
instead of requiring callers to provide a refinement trace; no estimate branch is merged or
excluded.

`MultiLimbSchoolbookDigitExecutable.lean` now constructs the direct-or-corrected quotient-digit
certificate from the concrete multiply-subtract borrow flag. On the correction branch it connects
that flag to the pure subtraction borrow bit and proves `qHat` is nonzero before Solidity's checked
`qHat - 1`; this prevents the proof from assuming away a possible panic. It also applies the
generated loop's byte-level below-window frame to prove that all in-place `u` writes preserve the
earlier quotient-array header, then carries the unchanged active-word counter through the selected
store. The existential result therefore contains the actual direct or corrected memory and the
corresponding exact branch gas, rather than an abstract accepted digit.

`MultiLimbSchoolbookIterationExecutable.lean` composes those two constructors into a complete
`SemanticIteration`. Its premises are only the concrete operand/allocator geometry, identified
divisor and window slices, and the reduced-window arithmetic invariant already required by Knuth
division. The theorem internally selects an `EstimateResult`, executes the matching digit branch,
and returns both concrete results with the semantic certificate that proves their quotient and
remainder observations. This composition is needed so the outer-loop proof can recurse on actual
post-write memory and accumulate exact per-iteration gas without accepting either an estimate
trace or result memory from its caller.

The recursive loop additionally needs to reload the normalized divisor header after each digit.
The existing semantic frame only covered words below the current `u` window because that was
enough to prove quotient retention. `MultiLimbSchoolbookIterationSemantic.lean` and
`MultiLimbSchoolbookDigitSemantic.lean` now provide the symmetric above-window frame through the
multiply-subtract loop, optional add-back loop, final top-word store, and quotient store. This is
needed because the actual allocator places `v` immediately above `u`; proving the frame rules out
aliasing at every concrete write and allows the next generated selector to reuse the header. It
does not assume immutable memory or alter any selected path, step count, or gas expression.

`MultiLimbSchoolbookIterationExecutable.lean` now specializes those frames to the three array
headers retained by a quotient digit and to the complete normalized-divisor payload. The quotient
header proof uses the allocator's non-wrapping payload bound directly, so the valid Barrett case
`k = 32` can store quotient index 33 without the former 32-index helper restriction. The divisor
slice proof follows every concrete divisor reload and shows it is unchanged across both the direct
and corrected digit memories. These facts are needed by the recursive constructor: every next
generated selector must re-establish its headers and actual divisor loads from post-write memory,
not inherit an abstract immutable-divisor assumption. They only prove memory framing and leave the
selected execution paths and their exact gas unchanged.

`MultiLimbSchoolbookContinuationExecutable.lean` begins the constructive outer-loop proof with
the arithmetic transition used between adjacent cursors. It proves that a reduced `count`-word
result has a top limb no greater than the normalized divisor top, and that prefixing the next
concrete lower input limb keeps the next `(count+1)`-word window below radix times the divisor.
This bridge is needed to feed the executable q-hat selector at every recursive cursor; without it,
only the first iteration's reduced-window premise would be available. The theorem is pure
arithmetic over the exact remainder produced by the preceding concrete digit and does not exclude
any estimate or correction branch.

The constructive continuation is now complete as a generic executable theorem.
`ContinuationGeometry` records only cursor-independent non-wrapping, active-memory, and allocator
separation facts, while `ContinuationMemory` records the concrete headers, divisor loads, and byte
extent that must survive each mutation. `semanticIterationAt_exists` derives all current `u`
operands from generated loads and invokes the executable estimate/digit selectors. The result
memory is then proved to satisfy the same dynamic package, including all three array headers and
the complete normalized-divisor payload. This split was needed because the loop mutates `u` and
the quotient at every cursor, but its allocator relationships are fixed; mixing both kinds of
facts into one supplied iteration certificate would merely hide the execution being proved.

`semanticContinuations_exists` performs strong induction over every descending quotient cursor.
It identifies the next generated window with one preserved lower source word followed by the
exact concrete remainder just written, proves that window remains below radix times the divisor,
constructs the next selected estimate and direct/corrected digit execution, and continues to the
terminal guard. The returned `SemanticContinuations` contains the actual memories and adds each
selected branch's exact `steps` and `gas`; gas is not existentially abstracted independently of
the path. This change removes the arbitrary continuation-certificate assumption at the generic
schoolbook level. The remaining Barrett work is to discharge `ContinuationGeometry` and the
initial-window facts for its positive- and zero-normalization memories, then feed the constructed
chain into the already proved quotient-value theorem.

Instantiating that constructor for Barrett exposed an incorrect proof-only range inherited from
the earlier partial development. A valid 32-limb modulus has `quotientCount = k + 2`, so the
normalized dividend window spans at most `(k + 2) + k = 66` words and its largest zero-based
address index is 65; the former aggregate bound of 33 would have excluded valid inputs above the
small-modulus cases. The schoolbook semantic and executable interfaces now use the allocator's
non-wrapping address theorem for this 66-word span, while retaining the separate explicit
`count <= 32` premise for the divisor. This correction broadens no Solidity input bound and
changes no bytecode, branch selection, step count, or gas expression. It is needed solely so the
proof covers the full already-supported Barrett layout instead of silently proving only a prefix
of its valid limb range.

`MultiLimbBarrettContinuationExecutable.lean` now instantiates the cursor-independent
continuation geometry with the concrete Barrett quotient, normalized-dividend, and
normalized-divisor pointers. It derives every guarded header and element-load active-word
identity from the allocator fit bounds. Separate positive- and zero-CLZ corollaries retain the
actual `barrettVWords` and post-`MCOPY` `barrettZeroWords` counters, respectively, because those
paths have different memory-expansion gas even though their array layout is the same. The
schoolbook instance explicitly requires `2 <= k`; `k = 1` is not excluded from Modexp but belongs
to the already separate short-division selector and does not execute this Knuth loop.

The same file proves that positive normalization's final concrete memory ends exactly after the
fresh `v` payload. The divisor shift extends the header-only allocation one word at a time, while
the subsequent in-place `u` shift and top-carry store are proved in bounds and preserve that
extent. This theorem is needed to supply the recursive loop's real memory guards rather than an
assumed oversized byte array. The zero path uses its existing exact post-`MCOPY` size theorem; no
execution step, selected branch, or gas expression is changed by either memory proof.

The Barrett continuation instance now derives its divisor decomposition from the concrete
generated loads, including proofs that `vSecond` and `vTop` are the actual final array words. It
also proves the initial cursor bound rather than accepting it: the full dividend is split after
`quotientCount - 1` low limbs, the remaining segment is identified with the guarded bytecode
window, and the common normalization factor is retained on both the exact numerator and divisor.
The pure bound uses the ordinary `k`-limb modulus lower bound
`UInt256.size^(k-1) <= modulus`; no numerator or normalization computation is discarded.

`barrettSemanticContinuations_exists_of_values` now turns those exact normalized values and final
memory facts into every quotient-loop execution witness, including selected q-hat refinements,
direct/corrected digit paths, intermediate memories, exact steps, and exact gas.
`barrettQuotient_exists_of_values` applies the already proved long-division semantics to that same
witness and proves its concrete quotient array equals `UInt256.size^(2*k) / modulus`. This removes
the former caller-supplied `SemanticContinuations` assumption at the value-theorem boundary. The
remaining path specialization must prove the final headers and normalized top-word fact for the
positive-shift and zero-copy memories, then connect the resulting witness to the PC-level loop
contract.

The zero-CLZ specialization is now constructive through the full schoolbook quotient loop.
Raw-read frame lemmas follow the actual allocation sequence: quotient allocation writes its
header, `u` allocation preserves it and writes its own, numerator `MCOPY` preserves both, and `v`
allocation writes its header while retaining the earlier two. The zero-normalization `MCOPY`
starts exactly after the `v` header and preserves all three. Guarded-header theorems then apply the
exact post-copy active-word counter, so no final header is assumed.

For the same path, `clz(top) = 0` and the concrete nonzero top limb prove the Knuth normalization
bound `UInt256.size <= 2 * top`. `barrettZeroQuotient_exists` combines that fact, the exact copied
dividend/divisor values, exact final memory size, and the constructed header package. It returns a
real `SemanticContinuations` witness with all selected quotient-digit paths, final memory, exact
steps, and exact gas, and proves that witness stores `UInt256.size^(2*k) / modulus`. The only
remaining schoolbook normalization branch is positive CLZ; the subsequent Barrett reduction and
exponentiation integration still remain after that branch is constructed.

The positive-CLZ specialization is now constructive through the same complete schoolbook quotient
loop. The normalization writes first extend the fresh `v` payload, then shift `u` in place, and
finally store `u`'s carry. `barrettPositiveMemory_headers` converts the previously proved raw-byte
frames into the three guarded array headers using the exact final byte extent and actual
`barrettVWords` active counter. This conversion is needed because the generated loop performs
guarded loads; preserving bytes alone would not establish that those loads take their active
branches.

`barrettPositiveMemory_normalizedTop` derives Knuth's top-limb bound from the actual arithmetic
rather than accepting it as a normalization premise. It splits the complete source modulus at its
top limb, applies the generated CLZ relation `normalizedTop = top * 2^shift`, rewrites the complete
final divisor with `barrettPositiveDivisor_final_value`, and uses the lower limbs' radix bound to
infer the final stored top word is at least `2^255`. This proof is needed to justify every q-hat
estimate branch for the concrete shifted divisor; it neither drops the lower-limb computation nor
introduces an extra input restriction beyond the already required nonzero trimmed top limb.

`barrettPositiveQuotient_exists` combines those derived headers and top bound with the exact
shifted numerator, shifted modulus, memory extent, and allocator geometry. Like the zero-CLZ
theorem, it constructs all estimate choices, direct or corrected digit executions, intermediate
memories, final memory, steps, and path-sensitive gas, then proves the quotient payload is exactly
`UInt256.size^(2*k) / modulus`. Thus both long-division normalization selectors are now executable
and pure-equivalent. The remaining work is PC-level composition of these witnesses with the
generated normalization and outer-loop contracts, followed by Barrett reduction and modular
exponentiation integration.

`barrettQuotientExecution_exists_of_values` now performs the first PC-level composition. It uses
the same constructed `SemanticContinuations` witness both to prove the pure quotient and, through
`semanticDivisionLoopExact`, to execute the deployed loop from PC 5450 to its terminal guard at
PC 5457. Its conclusion retains the selected final memory and active-word count and charges
`initialSteps + steps + 5` and `initialGas + gas + 13`; the five-step/thirteen-gas adjustment is
the real difference between entering the first cursor at PC 5450 and re-entering later cursors at
PC 5457, not an existentially chosen gas value.

This adjustment and the terminal edge were independently rechecked with the portable SymCheck
binary against the exact 8,626-byte `runtimeBytecode`. With a nonzero concrete cursor,
`summarize --pc 5450 --target-pc 5458 --fail-on-overapproximation` reported a solver-free
6-step/23-gas prefix, while the equivalent continuation entry at PC 5457 reported 1 step/10 gas.
The measured difference is exactly 5 steps/13 gas. With cursor zero, PC 5457 reached the real
denormalization dispatcher at PC 5894 in one `JUMPI`, again solver-free at 1 step/10 gas. These
checks are needed to independently validate the generated boundary and exact-cost accounting used
by the Lean composition; they do not replace any memory or arithmetic proof.

PC-level positive normalization exposed a distinction absent from the earlier generated validity
helper. The fresh normalized-divisor payload starts at the current byte-array frontier, so each
`MSTORE` extends memory; `validDivisorShiftOfLayout` only covered writes already within the current
extent. `validDivisorShiftOfFrontier` was added to follow the real extending recurrence. At each
word it proves the exact 32-byte size increase, preserves both guarded headers from the unchanged
raw reads below the store, advances the frontier equation, and constructs the next
`ValidDivisorShift` node. This change is needed to feed `positiveExact` without asking its caller
for a normalization trace, and it does not weaken any write, address, or active-memory guard.

`barrettPositiveDivisorValid` instantiates that constructor for the concrete Barrett `v` pointer,
while `barrettPositiveDividendValid` derives the post-divisor-shift `u` header and uses the ordinary
in-bounds constructor for the subsequent in-place dividend shift. Together they select every
generated positive-normalization iteration from allocator geometry and source-array observations;
neither the shifted words nor a validity certificate is supplied as an opaque witness.

Constructing the post-division return exposed one false proof-only header premise in both return
loop contracts. The normalized dividend `u` retains its allocated `m + 1` header; for the Barrett
constant division this is `2*k + 2`, whereas the remainder loops deliberately return only
`kEff = k` limbs. `ValidDenormalize` and `ValidCopy` therefore now track the actual `uCount`
separately and require `kEff <= uCount`. Their generated array guards use the real `uCount`
header while their loop bounds and remainder allocation continue to use `kEff`. This correction
is required to cover every nontrivial Barrett constant computation instead of assuming an
impossible `u` header. It changes no bytecode path, memory write, trace step count, gas expression,
or accepted Solidity input. Lake builds of both return contracts, the composed schoolbook
division function, and `MultiLimbBarrettContinuationExecutable` succeed with the corrected
interface.

The quotient-digit frame library previously covered a retained word above the quotient store or
a higher quotient word whose store ordering is reversed. The Barrett remainder header lies below
both the quotient array and every mutable `u` window, so neither theorem applied.
`validDigit_read_below_frame` now follows both direct and corrected digit paths, uses the existing
multiply/subtract and add-back lower frames, and also proves the final quotient store is disjoint
on the upper side. `semanticIteration_read_below_frame` and
`semanticContinuations_read_below_frame` lift that fact over the exact selected continuation.
This addition is needed to retain the real preallocated remainder header through all quotient
computations; it does not abstract away any arithmetic write.

The same continuation induction now proves that final memory size and active words equal their
initial values. A companion induction preserves the normalized `u` header across all selected
digits. `semanticContinuations_returnHeaders` packages these results: from an initial guarded
`u`/remainder header and concrete allocator ordering, it derives both final guarded headers in the
same final memory used by the pure quotient theorem and PC-level execution. This prevents the
return trace from assuming an unrelated post-state or existentially choosing its memory and gas.

The original remainder header is now derived from its `barrettDivisionMemory` allocation and
framed through every later setup operation: quotient allocation, normalized-dividend allocation,
numerator `MCOPY`, and normalized-divisor allocation. Separate positive- and zero-normalization
theorems then retain it through, respectively, all divisor/dividend shift writes plus the carry
store, or the zero-shift divisor `MCOPY`. The resulting guarded-header theorems use each path's
exact final memory size and active-word count. This derivation is necessary because accepting a
late remainder-header premise would disconnect the return proof from the allocator execution.

`validCopyRangeOfLayout` and `validDenormalizeRangeOfLayout` construct the generated return-loop
certificates recursively from concrete in-bounds layout. The zero path proves one copy store per
limb. The positive path distinguishes the real terminal cycle from nonterminal cycles and proves
both writes in each nonterminal cycle, including the intermediate remainder word read back by the
bytecode. Every recursive state retains the actual `uCount = 2*k+2` header and the `k`-limb
remainder header; no loop-validity witness is supplied by the caller.

`barrettZeroDivisionReturn_exists` and `barrettPositiveDivisionReturn_exists` now execute the
complete schoolbook continuation from PC 5450 through the deployed dispatcher and return to the
concrete caller PC. Both conclusions retain the quotient equality
`B^(2*k) / modulus` from the same selected continuation and expose exact path gas. The zero return
adds exactly `208*k + 100` gas after PC 5457. The positive return adds the generated 73-gas setup,
the exact recursively selected denormalization gas, and the 26-gas loop exit; it does not replace
that cost with an existential gas value. The remaining arbitrary-input work is the subsequent
Barrett multiply/reduction computation and exponentiation integration, not the Montgomery or
schoolbook constant computation.

`MultiLimbBarrettAccumulatorContract.lean` closes the next caller segment, from the Barrett
constant's return at PC 1718 to `_barrettModexpLoop` at PC 3154. The deployed code allocates a
`k`-limb array, executes Solidity's checked access for element zero, stores the initial accumulator
value one, and dynamically jumps into the loop. The proof derives the array header and active-word
coverage from that concrete allocation rather than assuming a preinitialized accumulator. It
preserves the exact initialized memory and charges 104 instructions and
`newWordArrayGas aw fp k + 97` gas. This bridge is needed so the eventual exponentiation invariant
starts from bytecode-built `r = 1`, not an abstract pure initial value.

`MultiLimbSchoolbookMulTrace.lean` begins the concrete `_barrettMulMod` arithmetic at its separate
`LimbMath.schoolbookMul` implementation (PC 5016), rather than reusing the Montgomery CIOS loop at
PC 4440. The generated PC 5117 trace is wrapped as one exact product-plus-carry transition and
linked to `evmSchoolbookStep_recompose`. Recursive execution now covers an arbitrary positive
`bCount`: it proves each continuing and terminal `j` guard from the actual natural index, performs
all evolving-memory loads and low-word stores, and executes the final carry addition. A complete
nonzero row reaches the outer guard in exactly `55 + 68*bCount` instructions with a recursively
defined gas expression containing every memory-expansion delta. The nonzero-row theorem requires
the real ten-word temporary stack-depth allowance, three words more than row entry; this is a VM
stack-safety condition, not a Solidity input exclusion. These additions are needed because Barrett
reduction makes two calls to this standalone multiplier and their product equality cannot be
obtained from the already proved Montgomery multiplication path.

`MultiLimbSchoolbookMulOuter.lean` composes that row theorem across the standalone multiplier's
actual PC 5046 outer guard. `rowExact` inspects the word loaded from evolving memory and selects
either the 23-instruction zero-row skip or the full nonzero row, so the caller supplies no zero
pattern. `rowsFromZeroReturnExact` derives every taken guard from `i = 0..aCount-1`, proves the
terminal guard false at `i = aCount`, removes the assembly locals, and dynamically returns the
same result pointer. Its instruction and gas totals are recursive expressions over the selected
rows, with one real 10-gas `JUMPI` per row and the exact seven-instruction/28-gas return suffix.
This layer is needed to cover arbitrary source arrays rather than only a single multiplication row
or an assumed branch schedule.

`MultiLimbSchoolbookMulFunction.lean` now covers the complete deployed standalone function from
PC 5016: Solidity's checked `aLen+bLen`, result allocation and zero initialization, assembly-loop
setup, all rows, and dynamic return. SymCheck independently confirmed the tagged calling convention
and the solver-free prefix costs: PC 5016 reaches allocator PC 1487 in 23 instructions/85 gas, and
PC 5036 reaches the first outer guard in eight instructions/19 gas. The composed theorem exposes
`116 + rowsSteps` instructions and `132 + newWordArrayGas + rowsGas`, preserving every selected
memory-expansion term.

The same work exposed a proof-bound mismatch at the maximum accepted width. Barrett's second
product has `q1Len+muLen = 2*k+4`, hence 68 result limbs when `k=32`; `Allocation.lean` previously
proved the identical allocator only through 66 limbs. Its proof bounds were extended from
2,112/2,144 payload/allocation bytes to 2,176/2,208 bytes, and the main theorem is now
`newWordArrayExact68`. The bytecode and allocation formulas are unchanged. This extension is
needed to include the 1,024-byte modulus boundary instead of imposing an artificial `k<32`
restriction; the narrower 65-, 33-, and 32-word wrappers continue to use the same proof.

`MultiLimbSchoolbookMulSemantic.lean` identifies the standalone PC 5117 recurrence with the pure
`evmSchoolbookRow` model. Its collectors follow the actual evolving memory and record every
operand limb, prior result limb, stored low word, and propagated carry. The resulting theorem
proves the unbounded radix equation with the final carry appended; it does not replace the loop by
an uninterpreted product. The remaining semantic step for this helper is to identify those
collectors with the concrete contiguous input/result array slices using allocator geometry.

`MultiLimbBarrettMulContract.lean` composes the first complete multiplier call into the real
`_barrettMulMod` caller. A generated/SymCheck-validated 14-instruction, 45-gas prefix maps PC 6446's
`a,b,n,mu,k,returnPc` frame to `schoolbookMul(a,k,b,k)`. `firstProductExact` then executes the
allocation and every selected product row and returns the resulting memory to PC 6468 with exact
gas. This is the first executed Barrett-reduction product; the later `q1*mu`, truncated `q3*n`,
subtraction, and correction phases remain to be composed.

The same Barrett contract now continues through q1 slicing to the second standalone
multiplication entry. The PC 6490 prefix invokes the compiler's real checked-add helper to compute
`k+1` in 17 instructions and 64 gas. The PC 6500 prefix then executes the generated trace's actual
`MCOPY`, loads `mu.length` from the post-copy memory, and reaches PC 5016 in 24 instructions with an
explicit path-sensitive gas expression containing both memory expansions and the copy-word charge.
The new `q1Copy*` definitions expose the exact source, destination, length, memory, active-word, and
gas states. They are necessary because replacing this segment with an assumed q1 value or opaque
intermediate memory would avoid proving both the Barrett slice computation and preservation of the
concrete `mu` header. The composed theorem reaches the second multiplication in 41 instructions
and `64 + q1SliceGas`, without an existential gas variable. SymCheck's target-PC summary
independently reported the same 24-opcode PC 6500-to-5016 path and identified the copied-memory
`mu` read used by the Lean contract.

`secondProductExact` now applies the full standalone multiplier contract to that concrete state and
returns the complete `q1*mu` product to PC 6530. The caller frame records the loaded `mu.length`
twice because the bytecode uses it both as the multiplication argument and as a later Barrett
local; exposing this duplicate corrected an earlier hand-inferred stack description. At the
maximum `k=32`, this call allocates all 68 result limbs and executes all `k+2` rows. The composed
`q1ProductExact` theorem therefore covers PC 6490 through PC 6530 in `157 + rowsSteps`
instructions, with the exact copy, allocation, memory-expansion, and selected row gas. This was
needed to ensure the second Barrett product is computed by the deployed loops rather than supplied
as a pure or existential intermediate result.

The Barrett caller now also executes the complete q3 length and allocation setup. Starting at PC
6530, it uses the deployed checked-add helper to prove `q2Len=2*k+4`, computes checked `k+1`, proves
the actual long-q2 branch from positive `k`, and uses the deployed checked-subtract helper to obtain
`q3Len=k+3`. It reaches allocator PC 1487 in exactly 76 instructions/288 gas, matching the
concrete SymCheck boundary summaries, then allocates the real `k+3`-limb q3 array and returns to PC
6582 in 154 instructions with `288 + newWordArrayGas`. The explicit branch proof is needed to
exclude only the unreachable fallback for valid Barrett widths, not to assume the quotient slice
or skip its arithmetic. The helper-level decomposition also records why all additions and the
subtraction are nonwrapping at the accepted 32-limb boundary.

The q3 continuation now recomputes the deployed copy length instead of reusing the proof-level
formula. `q3CopySetupExact` proves both length comparisons and reaches PC 6626 in 61
instructions/234 gas with `copyLen=q3Len=k+3`. `q3CopyAndRLenExact` executes the real `MCOPY` from
`q2[k+1..]` into q3, exposes the resulting memory and active-word state, and computes checked
`rLen=k+1` with exact dynamic copy gas. `r2AllocationExact` then allocates the actual zeroed
`k+1`-limb r2 array and enters PC 6666. These states are explicit because the truncated `q3*n`
loop must read the bytes produced by this copy and accumulate into the allocator-produced zero
array; assuming either array would bypass the central Barrett computation.

`MultiLimbBarrettTruncatedMulContract.lean` begins that concrete `q3*n` computation. Its first
theorem executes the assembly's defensive q3-length cap: because the allocated q3 has `k+3` limbs
while r2 has `k+1`, the deployed comparison is true and the loop cap becomes exactly `k+1`. The
proof follows the generated PC 6666 branch and reaches PC 6675 in 13 instructions/46 gas. This
step is kept explicit because assuming the cap would hide a real selected bytecode branch and
would make the later outer-loop bound disconnected from the EVM stack value that controls it.
The same module now exposes the actual q3 address, loaded word, active-word update, and dynamic
load gas. A zero q3 limb is proved to take the deployed skip and return to the outer guard in 18
instructions. For nonzero limbs, `innerBodyExact` wraps the generated PC 7079 trace as the same
full-width product-plus-carry recurrence used by the pure schoolbook model: it reads `n[j]` and
the evolving `r2[i+j]`, stores the low word, propagates the high word and carries, and reaches the
next inner guard in 67 instructions with all three memory-expansion deltas. Reusing the proved
recurrence here is necessary to establish arithmetic equivalence while retaining this loop's
different stack layout and truncated bounds; it does not replace any deployed computation.
`innerIterationsExact` and `innerThroughExitExact` compose that column transition for an arbitrary
selected row width. Every continuing and terminal guard remains part of the execution, giving 68
instructions per column and a recursive exact-gas expression over the evolving memory. This
composition is needed before the proof can derive `jMax` from each outer index and identify the
whole truncated product with multiplication modulo `B^(k+1)`.
The deployed `jMax` setup is now proved on both arithmetic paths. At `i=0`, the comparison
`k+1>k` takes the cap branch and enters the inner body with `jMax=k` in 27 instructions/89 gas.
For `1≤i≤k`, checked word arithmetic gives the positive bound `jMax=k+1-i`; its comparison with
`k` is false, so that path enters in 21 instructions/69 gas. Splitting only on the actual outer
index is required to account for the path-sensitive gas and the first row's final-carry store.
The two row cleanups are also explicit. `carryCleanupExact` performs the deployed load/add/store
at `r2[i+jMax]`, tracks both memory-expansion deltas, removes the assembly locals, and increments
`i` in 30 instructions. `noCarryCleanupExact` proves the corresponding 12-instruction path when
the final index equals `rLen`. Keeping these distinct records the real 76-base-gas difference
instead of hiding it in an existential gas result.
`firstRowFinishExact` and `laterRowFinishExact` connect the completed inner-loop state to those
cleanups. They prove the branch conditions from `i+jMax`: the first row stores at limb `k` and
costs 43 instructions plus the dynamic carry gas, while every later row has final index exactly
`k+1` and finishes in 25 instructions/83 gas without a write. This closes the bytecode control
flow for one nonzero row without assuming which cleanup branch was selected.
Complete nonzero-row contracts now compose all of these segments. The first row executes in
`82+68*k` instructions and includes its concrete carry write; a later row `i` executes in
`58+68*(k+1-i)` instructions and intentionally drops the carry beyond the `k+1`-limb result.
Their gas definitions retain the q3 load, every evolving-memory column, and the selected cleanup.
The loop width and output memory are computed from the bytecode state, which is needed for the
eventual modulo-`B^(k+1)` product proof rather than an assumed intermediate r2 value.
`TruncatedOuterState` and `truncatedRowExact` now select among the zero, first-nonzero, and
later-nonzero row contracts using the q3 word read from the current memory. The state transition,
instruction count, and gas are all branch-sensitive functions of that read. This selector is
needed to support arbitrary q3 arrays without requiring a proof caller to prescribe a zero pattern
or a control-flow schedule.
The outer recursion now executes all `k+1` q3 rows from the assembly's concrete `i=0`. Each row
includes the real six-instruction/23-gas guard, and natural-index lemmas prove every continuing
guard and the terminal false guard at `i=k+1`. `truncatedRowsFromZeroExitExact` reaches PC 6685
with the fully computed r2 memory and recursively exact selected-row gas. This is the complete
deployed truncated `q3*n` execution, prior to its pure modulo-product semantic identification.
During compiler verification, the truncated-product composition was tightened in two places.
The generated traces leave several stack expressions in their literal EVM forms (`x-0`, `0+x`,
and word subtraction before conversion back to a natural width), so the contracts now prove and
apply those word equalities explicitly instead of relying on an unbounded global simplifier. The
outer-row contracts also require room for the two caller continuation words that they prepend to
the row-local tail. Consequently their stack-depth premise is `tail.length+13<=1016`, rather than
the earlier `+11` premise that only counted row locals. Neither change excludes calldata or skips
arithmetic: the first makes the generated-trace normalization deterministic, and the second
states the actual EVM stack-safety condition used by the composed execution.

`MultiLimbBarrettSubtractContract.lean` continues at PC 6685. It removes the completed q3-loop
locals, calls the real allocator with length `k`, and returns the zeroed final-result array to PC
6696 in 85 instructions with `23+newWordArrayGas`. It then initializes the assembly subtraction's
`borrow=0,i=0`, proves the `0<k+1` guard, and reaches PC 6940 in 10 instructions/31 gas, matching
a SymCheck `summarize` boundary. This allocation and setup are explicit because the later result
copy must target the concrete allocated pointer and the subtraction must consume the computed r2,
not proof-level stand-ins.
Compiler verification also changed the subtraction entry to pass its existing seven-word
stack-depth premise directly to the generated PC 6696 theorem. The generated theorem has exactly
the same tail shape, so the previous attempted list-length simplification had no expression to
rewrite. This is only a theorem-application correction; it does not alter the accepted EVM state,
the selected branch, or the exact 10-instruction/31-gas result.
The subtraction body is now a concrete named transition over `i`, `borrow`, `product`, and the
computed r2 array. `subtractionBodyExact` executes PC 6940 through the next guard at PC 6707 in
43 instructions, loads `product[i]` and `r2[i]`, applies the same `evmSubBorrow` primitive used by
the pure list model, writes the digit back to `r2[i]`, and records all load/store memory-expansion
deltas in `subtractionBodyGas`. A separate SymCheck `summarize` run with abstract memory and
pre-expanded active words reported a solver-free 43-instruction/130-gas segment, the stack order
`i,borrow,product,...`, and the in-place r2 write. Naming the actual in-place transition is needed
to compose all `k+1` columns and then identify their memory slice with `evmSubLimbs`; treating the
subtraction result as an input would skip Step 7's arithmetic.
`BarrettSubtractionState` now carries the natural loop index, propagated borrow, concrete memory,
and active-word count. Separate continuing and terminal contracts prove the real guard at each
column: indices below `k` jump back to PC 6940, while the `i=k` column increments to `k+1` and
takes the false `JUMPI` fallthrough at PC 6708. The latter PC was corrected from an initial 6710
boundary after Lean exposed the generated theorem's literal `6707+1`; the two setup opcodes after
6708 have therefore not been silently included or skipped. `subtractionFromZeroExact` composes
`k` continuing columns and one terminal column from `i=0,borrow=0`, giving exactly
`44*(k+1)` instructions and `subtractionThroughExitGas`, a recurrence over every selected
load/store expansion. This is the complete deployed `product-r2` execution before correction.
`MultiLimbBarrettSubtractSemantic.lean` identifies that executed recurrence with the shared pure
`evmSubLimbs` model. Three evolving-memory collectors record every product limb, prior r2 limb,
and stored output limb; induction proves that their output and final borrow are exactly the pure
equal-width subtraction result. The module also instantiates the pure modulo-`B^count` value
theorem from the deployed zero-borrow state. This bridge proves arithmetic equivalence for the
words actually loaded and stored by the trace. It deliberately does not yet claim the stronger
array-level theorem: allocator-derived non-aliasing and write-coverage facts are still needed to
identify the collectors with contiguous initial product/r2 slices and the final r2 memory slice.
The correction prefix is now explicit as `correctionSetupExact`. From PC 6708 it removes the
completed subtraction index, borrow, and product locals, initializes correction iteration zero,
takes the proved `0<2` outer guard, and loads the actual extra word `r2[k]`. It reaches PC 6756 in
24 instructions with `correctionSetupGas`, including the load expansion. The contract exposes the
compiler's exact Boolean form: `iszero(r2[k])` selects the lexicographic comparison block, while
`iszero(iszero(r2[k]))` is the initial `geq` value. This representation was retained because it is
what the generated trace computes; its equivalence to `r2[k]>0` belongs in the semantic proof.
For the nonzero-extra-word branch, `correctionTopNonzeroEntryExact` follows the false top-word
test, proves the retained `geq` word true, and enters the correction subtraction loop at PC 6780
with `i=0,brw=0,iter=0` in exactly 12 instructions/49 gas. SymCheck independently reports this
path as solver-free. Additional SymCheck boundaries distinguish the correction columns: the
ordinary `i<k` body at PC 6794 loads `n[i]` and returns to PC 6780 in 53 instructions/166 gas when
memory is pre-expanded; the `i=k` body uses zero and costs 42/132. The shared true loop guard is
6/23 and the final false guard is 6/23. These separate costs are required for exact path-sensitive
gas and will be represented by distinct transition contracts rather than one existential total.
Those correction-column contracts are now implemented. `correctionOrdinaryColumnExact` executes
one `i<k` limb from PC 6794, loads the evolving `r2[i]` and `n[i]`, applies `evmSubBorrow`, writes
back to r2, includes the next true guard, and returns to PC 6794 in 59 instructions with exact
dynamic gas. `correctionTerminalColumnExact` executes `i=k` with the source-mandated zero right
limb, stores the extra word, includes the final false guard, and reaches PC 6788 in 48 instructions.
The two contracts are separate because the terminal path omits the modulus load and has a
different exact cost; merging them would hide the path distinction the user required.
`CorrectionSubtractionState` and `correctionPassFromZeroExact` now compose one complete selected
modulus subtraction. Starting at PC 6794 with zero index and borrow, the proof executes exactly
`k` ordinary `r2[i]-n[i]` columns and the terminal `r2[k]-0` column, reaching PC 6788 in
`59*k+48` instructions. `correctionPassGas` retains every evolving-memory expansion from both
column forms. This proves a full correction pass rather than supplying a corrected remainder;
the remaining correction work is the outer compare/second-pass selector and final result copy.
`MultiLimbBarrettCompareContract.lean` begins the surrounding correction control-flow proof. It
names the deployed final `MCOPY` memory, active-word update, byte count, and opcode gas separately
from comparison gas, because a below-modulus comparison exits through the copy while a selected
subtraction does not. The module proves the zero-extra-limb entry into the descending comparison,
the exact first-pass transition into correction iteration one, the repeated top-limb load, and the
second-pass exit through the concrete low-`k`-limb copy. These boundaries retain exact branch gas
and ensure the final result is copied from the computed r2 buffer rather than introduced as an
assumed output. They are preparatory contracts for the recursive greater/equal/less selector.
Compiler checking clarified that `trace_6788_notTaken` ends at the outer-loop fallthrough PC6721;
the final copy is the following `trace_6721_body` segment. The composed contract now applies both
generated traces explicitly. Its stack-depth premise is instantiated with the six retained Barrett
locals, and the `MCOPY` word-rounding expression is parenthesized as `Gcopy*((bytes+31)/32)` to
match the EVM gas rule. These changes correct theorem composition and gas syntax only; they do not
weaken the selected path or replace the concrete copy.
The descending comparison now has explicit contracts for all four control-flow outcomes. Equal
nonterminal limbs continue at PC6882 with `i-1`; equality at `i=1` and a greater first differing
limb enter the actual correction subtraction at PC6794; a smaller limb executes the source's
`geq=0,iter=2` early exit and the final `MCOPY` to PC6737. Their exact fixed costs are respectively
125, 200, 219, and 286 gas before the shared two-load expansion and, for the smaller branch, the
copy opcode cost. SymCheck solver-free concrete-memory runs independently reported 36/125,
56/200, 62/219, and 84/295 for a pre-expanded two-word copy (the last nine gas is `MCOPY`). The
separate theorems are required because merging these outcomes would lose the requested exact
path-sensitive gas and could hide the actual comparison computation.
Lean's generated PC6882 state preserves two compiler-level forms that are now normalized
explicitly: decrement is `not(0)+i` (not `i+not(0)`), and the first test is the `GT` expression
`r2Word.gt(nWord)`. A left-oriented decrement lemma and explicit pointer-commutativity rewrites
connect those forms to `compareIndex`, `compareLeft`, and `compareRight`. This adjustment is needed
for deterministic trace elaboration and does not impose any arithmetic restriction on the limbs.
The execution module now also names `comparePtr` in the bytecode's literal
`array+(index<<5)+32` order. The semantic layer will identify it with the shared commuted
`elementPtr`; retaining the literal form here prevents every generated memory condition from
expanding during simplification while still reading exactly the same array address.
`selectBarrettCompare` now exposes the correction comparison choice as executable data. It reads
the same evolving-memory words as the trace, returns either a subtraction or copied-result state,
and accumulates the exact branch cost while recurring only across equal limbs. The accompanying
`barrettCompareExact` theorem proves every successful selection reaches its corresponding deployed
PC and concrete memory state; `selectedBarrettCompareExact` rules out treating selector failure as
a proof result. Natural word comparisons are converted back to the exact EVM `GT`/`LT` Booleans
inside the proof, so exposing the selector does not let a caller prescribe or skip a branch.
The top-limb entry contracts are now iteration-polymorphic: both the zero path into descending
comparison and the nonzero shortcut into subtraction retain the actual `iter` stack word. The
earlier contract only needed iteration zero, but the deployed second correction iteration reuses
the same bytecode with `iter=1`; generalization is necessary to compose both passes without
duplicating or abstracting away that execution.
`selectBarrettDecision` now combines the loaded extra limb with the exposed descending selector.
A nonzero top word selects PC6794 directly in 12 instructions/49 gas; a zero top word adds the
exact nine-instruction/36-gas comparison entry and then follows `selectBarrettCompare`. Its exact
theorem therefore has a single public result type: `doSub=true` is ready for the concrete pass,
while `doSub=false` has already executed the deployed early exit and final copy. This composition
is needed twice by the at-most-two-pass correction loop.
The nonzero decision now additionally executes the shared PC6780 loop guard, making its complete
cost 18 instructions/72 gas and its endpoint PC6794. The earlier 12/49 helper remains as the exact
pre-guard boundary. This composition was necessary because comparison-selected subtraction had
already taken the guard; using PC6780 for only one selector outcome would prevent a uniform pass
contract and would undercount six instructions/23 gas on that path.
`MultiLimbBarrettCorrectionContract.lean` introduces the complete two-pass selector. A
`BarrettPassResult` computes the concrete memory, active words, final borrow, `59*k+48` steps, and
exact pass gas already proved by `correctionPassFromZeroExact`. `selectBarrettCorrection` then
combines initial setup, the first exposed decision, an actually selected pass, the deployed
iteration increment and repeated setup, the second decision, an optional second concrete pass,
and the final copy. No corrected remainder is supplied to the selector: every later decision reads
the memory produced by the preceding subtraction. The two-pass and early-copy totals remain
separate data, preserving exact path-sensitive gas.
`selectedBarrettCorrectionExact` now consumes a successful two-pass selector equation and proves
the entire deployed correction from PC6708 to the final-copy jump at PC6737. Its three proof cases
are the actual early copy, one selected pass followed by a below-modulus copy, and two selected
passes followed by the unconditional outer-loop exit copy. Each case composes the generated setup,
decision, concrete pass, iteration increment, repeated setup, and copy contracts, then normalizes
to the selector's exact step/gas record. This closes the correction execution control flow without
existential gas or an assumed intermediate remainder.
`MultiLimbBarrettSubtractSemantic.lean` now also records the exact ordinary correction inputs and
outputs and the source's terminal `r2[k]-0-borrow` column.  The new complete-pass theorem proves
that these concrete loaded and stored words are `evmSubLimbs` of r2 and the modulus extended by a
zero top limb.  This bridge is needed because the execution contract previously established the
PC path and writes but did not yet identify the arithmetic performed by a selected correction
pass; it introduces no replacement remainder and preserves the final borrow produced by bytecode.
The terminal composition uses a proved `evmSubLimbs_append_one` lemma rather than relying on list
simplification.  This was necessary because the terminal zero column is outside the ordinary loop;
stating the append law explicitly ensures its input borrow is exactly the ordinary loop's output
borrow and prevents the extra limb from being treated as an unrelated subtraction.
`MultiLimbBarrettCorrectionSemantic.lean` begins the selector-to-value bridge.  It proves the
comparison trace's literal `array+(index<<5)+32` address equals the shared Solidity element
pointer, constructs complete little-endian candidate and modulus vectors from the actual evolving
loads, and proves that every successful `selectBarrettCompare` result requests subtraction exactly
when the observed candidate value is at least the observed modulus value.  The collectors retain
the changing active-memory word count because omitting it could silently replace an out-of-range
EVM load with an assumed array value; allocator coverage will discharge that distinction next.
That coverage bridge is now proved.  Given explicit `MemoryCovered`, active-word
representability, and complete in-bounds r2/modulus payload ranges, every descending load equals
the corresponding word in `memoryWordsFrom`; coverage is propagated through both loads at each
index.  Consequently the exposed comparison selector requests subtraction iff the concrete r2
payload value is at least the concrete modulus payload value.  These premises are needed to rule
out EVM zero-on-inactive-memory behavior and address wrap, not to exclude any base, exponent, or
modulus values.
`MultiLimbBarrettModel.lean` now states the pure quotient estimate independently of EVM memory.
For `q1=floor(x/b)`, `mu=floor(b*R/n)`, and `q3=floor(q1*mu/R)`, the new bound proves
`q3*n <= x < q3*n + 3*n` from the normalized-divisor condition `b<=n` and product range
`x<b*R`.  This theorem is needed to justify the source's at-most-two correction loop rather than
assuming it; its abstract `b,R` form will be instantiated with the adjacent Barrett radix powers.
The pure model now also defines the source-equivalent two conditional subtractions and proves that
they return `candidate % n` for every candidate below `3*n`.  Combining this with the quotient
bound proves that the approximate quotient, nonnegative candidate, and at-most-two corrections
equal `x % n`.  This separate executable correction model is needed to match the exposed
zero/one/two bytecode selector cases without existentially choosing a reduced result.
The abstract result is now instantiated with the deployed radix powers
`b=B^(k-1)` and `R=B^(k+1)`.  A proved exponent identity identifies `b*R` with `B^(2k)`, so the
instantiated `mu=B^(2k)/n`, `q1=x/B^(k-1)`, and `q3=(q1*mu)/B^(k+1)` are exactly the source
quantities.  The resulting theorem proves the deployed pure candidate and two corrections equal
`x%n` for every positive normalized `k`-limb modulus and every product below `B^(2k)`.
Importing the shared UInt256 subtraction model into the pure Barrett file brings Ethereum's
scoped parser names into scope, so the pre-existing exponent theorem's local function parameter
was renamed from `raw` to `repr`.  This is a binder-only change required for parsing; the theorem
statement and semantics are otherwise unchanged.
The correction-pass collector layer now proves the stronger selected-pass result: from the
bytecode's zero-borrow entry, whenever the observed r2-plus-top vector is at least the observed
modulus-plus-zero vector, the complete stored vector is their ordinary natural difference.  This
condition is intentionally the same comparison established by the exposed selector; it is needed
to rule out interpreting the EVM limb subtraction as its wrapped `B^(k+1)` alternative.
The correction semantic module now proves its ordinary-loop array invariant.  One correction
advance preserves `MemoryCovered`, active-word representability, and the allocated memory size;
induction then identifies all observed r2 and modulus collectors with their original contiguous
memory windows.  The proof explicitly uses that earlier r2 writes are below later r2 reads and
that the allocated modulus ends before r2 begins.  These frame conditions are required to exclude
self-aliasing, not to constrain arithmetic inputs.
The write-side correction invariant is now explicit as well.  A frame lemma proves later
higher-index writes preserve each completed lower word, a store lemma identifies each written
word with `correctionStep`, and induction proves the ordinary output collector equals the final
contiguous r2 memory range.  This change is required to connect `evmSubLimbs` results to memory
that subsequent selector iterations and the final copy actually read.
The terminal correction column is now linked to memory too.  Its in-bounds store is proved to
contain the exact `r2[k]-0-borrow` output, its write leaves the lower `k` words unchanged, and the
full pass output collector is proved equal to the final contiguous `k+1` r2 words.  This separate
terminal proof is necessary because the Solidity loop deliberately omits the modulus load at
`i=k` and therefore has different execution and memory behavior from ordinary columns.
The pass-input bridge now propagates coverage and fixed memory size through every ordinary
column, proves all lower r2 writes preserve the later top word, and identifies the complete pass
inputs with the original `k+1` r2 payload and the original `k` modulus payload extended by zero.
This is required because the terminal load occurs after all ordinary in-place writes; treating it
as an initial-memory word without the frame proof would skip an actual memory dependency.
The correction semantic pieces are now composed for one selected pass.  Under the allocator's
covered, in-bounds, non-aliasing geometry and the selector's concrete `r2>=n` condition, the
actual final `k+1`-word r2 memory value is proved equal to the prior concrete r2 value minus the
concrete modulus value.  All per-iteration write bounds and the terminal write bound are derived
from the same geometry, so this theorem does not assume a separately supplied output window.
The combined correction decision is now numerically characterized over the complete candidate.
The proof identifies the loaded top word with `r2[k]`: a nonzero top dominates every `k`-word
modulus and must select subtraction, while a zero top reduces the decision to the already proved
descending low-limb comparison.  Thus every successful `selectBarrettDecision` result has
`doSub=true` iff the actual `k+1`-word r2 value is at least the actual modulus value.
A complete pass now also preserves `MemoryCovered`, active-word representability, and concrete
memory size through its terminal load/store, which is needed to apply the same decision theorem
to the second evolving state.  Separately, the final `MCOPY` is proved to place exactly the low
`k` corrected r2 words in the result payload, with shift and pointer arithmetic proved nonwrapping;
this connects correction memory to the value returned by `_barrettMulMod`.
The pass frame now also proves the complete modulus payload is unchanged after every ordinary r2
write and the terminal r2 write.  The proof uses the established prefix coverage/size invariant
at each write and the allocator ordering `end(n)<=r2`; this is needed because the second decision
and second pass read modulus from the evolved memory rather than from an abstract saved value.
The early-copy selector cases are now constrained semantically too.  Recursive selector analysis
proves every successful `doSub=false` decision's memory is exactly `barrettFinalMemory`, and a
radix-split lemma proves a full candidate below any concrete `k`-word modulus equals its low
`k`-word value.  These facts are needed so zero- and one-pass exits cannot return an unrelated
copied value or silently discard a nonzero top limb.
The subtraction-selected comparison geometry is now proved explicitly.  Every successful
`doSub=true` descending comparison leaves memory unchanged while propagating covered,
representable active-memory words through both loads, and the top-word decision preserves the
same facts through its initial load.  This is required because comparison changes `activeWords`
even though it does not write memory; reusing the pre-comparison coverage directly would skip
the EVM memory-expansion state consumed by the following subtraction pass.
A true decision and its following correction pass are now packaged as one semantic transition.
The transition proves exact subtraction of one concrete modulus, preserves memory coverage and
size for a second decision, and frames the modulus payload unchanged.  This factoring is needed
to compose the source's two evolving passes without re-assuming that either selector's reads or
either pass's in-place writes operate on the initial memory.
The complementary false-decision result is now proved once for both early exits.  It combines
the selector's exact final-copy memory with the below-modulus zero-top result, proving that the
result payload contains the complete candidate rather than merely an unchecked low-limb slice.
This lemma is needed for both the zero-pass and one-pass branches of the final selector proof.
The complete correction selector is now linked to the pure two-correction model.  Its zero-pass,
one-pass, and two-pass outcomes each prove the concrete result payload equals the corresponding
conditional subtraction value; the second decision reads the first pass's evolved memory, and
the two-pass case uses the proved `candidate<3*n` bound to show the copied result is below the
modulus.  This closes correction semantics without replacing any executed comparison,
subtraction, or `MCOPY` with an existential result.
`MultiLimbBarrettSliceSemantic.lean` now proves the deployed q1 and q3 `MCOPY` operations expose
the intended high-limb windows: q1 copies `k+1` product words beginning at limb `k-1`, and q3
copies `k+3` q2 words beginning at limb `k+1`.  The checked predecessor, shifts, source and
destination additions, copy lengths, and full source ranges are all proved nonwrapping.  This
bridge is needed to identify the bytecode's concrete quotient slices with division by the
corresponding radix powers rather than assuming pointer arithmetic describes those slices.
The slice bridge now includes the numeric quotient identities.  Splitting the complete source
limb ranges and bounding each discarded low prefix by its radix power proves q1's copied value is
the full product divided by `B^(k-1)`, while q3's copied value is q2 divided by `B^(k+1)`.
These are exact natural divisions derived from the executed copies, not abstract slice axioms.
`MultiLimbSchoolbookMulMemorySemantic.lean` now establishes the standalone multiplier's core
memory invariant.  A concrete inner column propagates `MemoryCovered`, active-word
representability, and fixed byte-array size through both operand loads and the result store; the
invariant is iterated for arbitrary row width and separately proved for the final carry
load/store.  This is required before identifying loaded limb collectors with allocated arrays,
because the standalone loop derives every address from evolving `(i,j)` indices.
The standalone inner recurrence is now formally reinterpreted as the existing generic
multiply-pass recurrence: under proved one-word pointer progression, its carry, memory, active
words, operand collector, prior-result collector, and output collector are identical.  The output
collector is consequently linked to final contiguous memory, and
`MultiLimbSchoolbookMulInputSemantic.lean` proves the two input collectors equal their initial
source and destination ranges when the source allocation precedes the result allocation.  The
input theorem uses the allocator's full 32-byte read-fit bound (one word stronger than pointer
start fit); this is necessary to exclude UInt256 address wrap during the actual EVM loads and
does not restrict operand values.
The standalone row proof now includes the executed carry load/add/store.  When the allocated
word above the row is initially zero, `MultiLimbSchoolbookMulRowSemantic.lean` proves the inner
stores followed by that carry store produce exactly `evmSchoolbookRow`, and separately proves
the represented destination value increases by the selected source limb times the fixed operand
value.  The zero-top premise is an allocator initialization fact needed by the concrete load; it
is not an arithmetic shortcut or a restriction on either input.
`MultiLimbSchoolbookMulOuterSemantic.lean` now composes arbitrary concrete selected rows into the
pure `SchoolbookRows` relation.  Starting from the function's zero-initialized destination, the
exact outer recurrence consequently represents the product of the source limbs actually read
and the fixed operand vector.  This composition is required to turn local column arithmetic into
the complete products used by q1, q2, and q3; it still leaves each zero/nonzero bytecode row to be
connected to the row relation under the proved allocator geometry.
The concrete zero-source selector is now connected to that relation.  The pure model proves from
its exact word-recomposition equation that multiplying a row by zero preserves every segment word
and produces zero carry, and `rowAdvance_zero_schoolbookRowUpdate` applies this identity to the
bytecode's unchanged-memory branch.  This is required to justify the executed row skip without
assuming arbitrary multiplication rows may be omitted.
The standalone nonzero-row memory proof now has explicit frame induction for both sides of its
write window.  Every executed inner store preserves complete ranges wholly below and wholly above
the selected row, and separate lemmas establish the same facts for the final carry store.  These
facts are required to splice the already proved exact `bCount+1` output window back into the full
zero-initialized product array without treating untouched prefix or suffix words as assumptions.
`rowAdvance_nonzero_schoolbookRowUpdate` now performs that splice for the actual selected
standalone row.  It combines the concrete operand/prior/output collectors, the executed fresh-top
carry load/store, and the proved prefix/suffix frames to establish the exact shifted
`SchoolbookRowUpdate` over the full product payload.  This closes the local nonzero arithmetic
bridge; its remaining premises are concrete allocator address, coverage, and zero-initialization
facts to be discharged uniformly for every outer iteration.
The standalone allocation was then checked against these premises and exposed an important
concrete-memory detail: Solidity's allocator writes the result-array length word at `fp`, so the
initial `ByteArray` ends at `fp+32`; the zero result payload exists through padded EVM reads but is
not yet materialized in the byte array.  Moreover, skipped zero source rows can leave several
payload words implicit before a later nonzero row writes.  The earlier frontier-only premise
`destination <= memory.size` was therefore not valid for arbitrary inputs.  The schoolbook
memory, input-collector, complete-row, and outer-row layers now use the byte-array library's
actual bounded-gap condition `destination - memory.size < USize.size`, prove the corresponding
maximum-size growth, and preserve padded ranges on both sides of every write.  The zero/nonzero
outer selector and exact row arithmetic are unchanged.  This correction is required to cover
arbitrary patterns of zero source limbs; it is an allocator representation fact, not an input
alignment exclusion or a way to avoid executing any multiplication.
`MultiLimbSchoolbookMulFunctionSemantic.lean` now discharges the uniform index and access geometry
for that bounded-gap model.  Assuming the two existing input-array allocations end before the
new result allocation at `fp`, every outer index is exactly `q`, every inner index is exactly
`p`, and the concrete result and carry addresses are the expected
`fp + 32*(q+p+1)` and `fp + 32*(q+bCount+1)`.  Their starts are below the allocator's `2^64`
limit, while the EVM memory-rounding access condition is proved separately against the UInt256
`2^256` limit; no extra 31-byte allocation margin was added.  These facts establish bounded-gap
write safety, coverage propagation, and monotone memory growth for every loop prefix.  A new
outer-row frame induction then proves all result stores preserve any padded range ending before
`fp`, in particular the complete `a` and `b` payloads.  The end-before-`fp` premises are ordinary
non-aliasing allocation geometry that the Barrett callers must instantiate, not limb-value or
alignment restrictions.
The same function-semantic layer now closes the standalone multiplier's full numeric result.
It carries a pure zero-tail invariant through every concrete row, uses that invariant to discharge
the fresh carry slot for both the generated zero-row skip and nonzero inner loop, and packages all
rows as `SchoolbookRowUpdate`s.  A covered-memory source lemma proves the generated source-word
collector is exactly the immutable initial `a` payload, while `b` is framed below `fp`; composing
these facts with the allocator's padded-zero payload proves the final concrete result represents
`wordLimbsToNat(a) * wordLimbsToNat(b)` for arbitrary limb contents.  This explicit zero-tail and
source-collector work is necessary because treating skipped rows or implicit allocator zeros as
already-materialized multiplication output would bypass the actual execution behavior that the
Barrett q1-by-mu and q3-by-modulus products must use.
`MultiLimbBarrettMulSemantic.lean` specializes that complete standalone theorem to both full
products executed by `_barrettMulMod`: the `2*k`-word `a*b` result and the `2*k+4`-word
`q1*mu` result.  It also composes known concrete source-product values with the already executed
q1 and q3 `MCOPY` semantics, yielding division by `B^(k-1)` and `B^(k+1)` respectively.  The copy
lemmas deliberately retain source/destination memory extents as caller premises because those are
facts about the successive Solidity allocations; replacing them with an abstract product array
would disconnect the quotient slices from the memory returned by the real multiplication calls.
`MultiLimbBarrettTruncatedMulSemantic.lean` now supplies the arithmetic core for the executed
`q3*n` truncation.  The first nonzero row reuses the complete schoolbook-row theorem and proves
the concrete carry store produces the exact `k+1`-limb row.  Every later nonzero row proves the
shortened inner loop updates the concrete result suffix modulo `B^(k+1)`; its omitted carry is an
exact multiple of that radix.  A separate prefix lemma proves the shortened modulus input can be
replaced by all `k` modulus limbs under the same modulus.  Coverage, address-fit, bounded-gap, and
fresh-zero carry-read premises are discharged in stages by the concrete outer allocator invariant.
The exact `r2` allocation is proved to end at its length header (`fp+32`), so all `k+1` logical
payload words are padded zero reads.  Exact inner-index/address lemmas show every write is at
`r2+32*(i+j+1)` and the allocator's existing 64-bit end bound proves the bounded-gap premise even
when preceding zero rows leave several words implicit.  Row coverage and monotone byte-array
growth then compose over arbitrary zero/nonzero q3 patterns, while a below-`r2` frame theorem
keeps both q3 and modulus allocations immutable.  Consequently the words selected by the outer
loop are proved to be exactly the copied q3 payload rather than an abstract source sequence.
These bounded-gap and frame lemmas are necessary because the deployed first row stores a carry
while later rows deliberately drop the carry beyond `r2`, and because Solidity does not
materialize a newly allocated zero payload; treating all rows as full multiplication over an
already-zero concrete buffer would not describe the bytecode that was executed.
The truncated-product semantic layer now closes the complete outer computation.  It derives the
first row's untouched top-word load as zero from the header-only allocation, proves later rows use
the immutable full modulus even though their deployed loops read only the in-range prefix, and
composes zero, first-nonzero, and later-nonzero cases over all `k+1` q3 limbs.  The resulting
theorem states that the final concrete `r2` payload is exactly
`(wordLimbsToNat(q3) * wordLimbsToNat(n)) mod B^(k+1)`.  A final specialization instantiates this
theorem with `r2AllocatedMemory` and `r2AllocatedWords`, so its memory and active-word state are
literally those returned by `r2AllocationExact`; no abstract zero buffer or unexecuted product is
substituted at the composition boundary.
`MultiLimbBarrettSubtractSemantic.lean` now connects the following executed in-place subtraction
to that value. It proves that the loop's left and right collectors are the initial contiguous
product and `r2` windows, that each later store preserves earlier output words, and that the final
`r2` memory window is their equal-width difference modulo `B^(k+1)`. The pure Barrett model adds
the corresponding wrapped-residue lemma and proves the extra limb is sufficient: the quotient
bound gives `candidate < 3*n`, while a normalized `k`-limb modulus has `n < B^k`, hence the
candidate is strictly below `B^(k+1)`. This establishes that the concrete modular subtraction is
exactly `deployedBarrettCandidate`, rather than merely congruent to it. The upper modulus bound is
an ordinary limb-representation fact, not a value exclusion.
Finally, `selectedBarrettCorrection_resultValue_eq_mod` composes that concrete candidate with the
exposed zero/one/two-pass correction selector. For every successful selected path it proves the
result payload equals `x % n`; the existing `BarrettCorrectionSelection.gas` remains the exact
path-sensitive gas expression. Keeping the selector and candidate memory equalities explicit is
necessary to show that the actual comparisons and subtractions ran, rather than existentially
choosing a correction count or a remainder.
`MultiLimbBarrettTruncatedMulSemantic.lean` also records the matching concrete-memory upper
bound: each inner store, the first row's carry store, each selected row, and the complete outer
prefix remain within the allocated `r2` payload. This was needed because the earlier coverage
theorem only proved monotone growth; monotonicity alone cannot justify that the following result
allocation starts after the final materialized byte. The new invariant follows the addresses of
the executed stores and does not exclude zero limbs, add alignment assumptions, or replace the
truncated multiplication with a pure computation.
`MultiLimbBarrettReductionContract.lean` now composes the real PC 6666 defensive cap, all `k+1`
truncated rows, result allocation, all `k+1` product-minus-r2 columns, and the exposed correction
selector through PC 6737. Its step count and gas are exact functions of the selected row and
correction paths. The companion semantic theorem frames the actual product and modulus windows
through both intervening computations, derives the concrete `r2` value from q3-by-modulus
multiplication, and proves the selected result payload equals `x % n`. Thus this boundary no
longer accepts the truncated product as an assumed arithmetic value; the remaining work is to
compose the already proved full products and q1/q3 copies into its allocator-layout premises.
The same composition has now been specialized back through the literal `r2` allocator and the
q3 `MCOPY`, reaching from PC 6626 to PC 6737. A new raw 32-byte frame proof shows that every
truncated row preserves Solidity's free-pointer word at offset 64, including gap-extending stores
and the first-row carry; together with the concrete memory upper bound this discharges every
premise of the following result allocator from execution. The corresponding numeric theorem
frames product, q3, and modulus through `r2AllocatedMemory` and still returns `x % n`.
On the pure side, `barrettQ3_lt_radix` proves the estimate is below `B^(k+1)`. This closes the
last slice-width issue: the low `k+1` copied q3 limbs used by the deployed truncated multiply are
the whole `barrettQ3`, while the low `k+1` first-product limbs used by subtraction are exactly
`x mod B^(k+1)`. Neither result assumes away high limbs; both are derived from the already proved
full products and the actual copied windows.
The portable SymCheck `run`/`summarize` interface was also applied directly to the deployed segment
from PC 7079 to PC 7032 with symbolic stack and memory.  It confirmed a solver-free 67-instruction
path, preservation of the selected `qi`, increment of `j`, and exactly one write to
`r2[i+j]` with the generated product-plus-prior-plus-carry expression, with no overapproximation.
The Lean theorem still proves the arithmetic relation independently; this check was used to
validate that the generated trace endpoint and recurrence matched the intended invariant.
The exact reduction composition now reaches further upstream, from PC 6530 through PC 6737.  It
executes q3's concrete allocation and setup before the existing q3 `MCOPY`/r2/reduction theorem.
The supporting geometry proves that the copy begins exactly at q3's header end, materializes all
`k+3` payload words, leaves the free-pointer word unchanged, and yields a covered,
representable active-word frontier.  These facts derive the following r2 allocator's size, gap,
free-pointer, and active-word guards rather than adding them as assumptions.  This extension was
needed because a header-only Solidity allocation followed by `MCOPY` changes both concrete memory
size and EVM active words; knowing only the copied q3 arithmetic value is insufficient to justify
the next allocation or its exact expansion gas.
The exact composition now reaches PC 6490, before q1's deployed slice copy and the complete
`q1*mu` multiplication.  A reusable standalone-product geometry theorem proves that every inner
column and row-carry store remains below the logical result allocation, while zero source rows may
correctly leave concrete payload bytes implicit.  It also proves raw preservation of Solidity's
free-pointer word, covered and representable active words, and the bounded gap to the successor
allocation.  This distinction is required: asserting that every product result has a fully
materialized byte-array payload would be false for skipped zero rows, while an upper bound alone
would not establish the free-pointer or active-word guards needed by q3's allocator.  With those
facts, PC 6490 through PC 6737 has one exact path-sensitive step/gas theorem covering q1 `MCOPY`,
all second-product rows, q3 allocation/copy, truncated reduction, subtraction, and the exposed
correction selection.
The exact composition now also reaches PC 6446, the entry to the first `a*b` multiplication.
The new theorem derives the first product's successor geometry, q1 allocation and copy geometry,
the `mu.length` load guards, and the complete second-product geometry before reusing the PC
6490--6737 result.  Its step count and gas expression include both standalone products and every
intervening allocator/copy path, and its result still carries the exposed correction selector.
This extension was needed because composing only from PC 6490 left the most delicate memory facts
as premises rather than consequences of the actual first-product execution.

The q1 copy semantics were additionally generalized to end-of-memory copies whose source suffix
may be represented by EVM implicit zero memory.  `ByteArray.write` materializes only the available
source prefix while active-memory expansion still covers the requested range; padded destination
reads nevertheless equal padded source reads.  In the concrete Barrett path q1 allocation then
zero-fills any skipped high product suffix before `MCOPY`, so the stronger concrete-source theorem
also applies.  Recording both facts avoids relying on a false general claim that zero schoolbook
rows always materialize their result bytes, and documents why concrete byte-array size and EVM
active memory must be tracked separately.

The numeric composition now reaches the same PC 6446 boundary as exact execution.
`firstThroughQ3_values` follows the executed first schoolbook product, q1 allocation and copy,
complete `q1*mu` product, and q3 allocation and copy, proving their concrete payloads are the pure
Barrett operands.  `selectedBarrettFromFirstProduct_resultValue_eq_mod` then supplies those values
and the derived memory frames to the already executable truncated product, subtraction, and
exposed zero/one/two-pass correction selector.  For every successful selector it proves the
selected result payload is `x % n`; it does not assume an intermediate quotient, candidate, or
remainder.  This wrapper was needed because the earlier PC 6446 theorem established exact steps
and path-sensitive gas but did not itself connect the final bytes to the pure model.

Caller integration has started at the deployed Barrett exponent loop.  A portable
`symcheck summarize --pc 3379 --target-pc 6446` run with symbolic stack and memory reached the
square call solver-free in 20 steps, with no over-approximation, stack
`r,r,n,mu,k,3406,...`, memory changed only by `mstore(0x40, freeMemBase)`, and cost
`62 + (C_m(new)-C_m(old))`.  `MultiLimbBarrettExponentTrace.lean` kernel-checks that boundary and
also exposes the one-step, 8-gas dynamic return at PC 6737 plus the shared PC 3406 copy-back.
Writing these boundaries explicitly is necessary to connect each exponent bit to the completed
Barrett computation without guessing compiler stack order or hiding the allocator reset.

The same caller module now covers the conditional multiply entry at PC 3448.  An independent
SymCheck summary reached PC 6446 solver-free in 12 steps with stack `r,a,n,mu,k,3406,...`, only
the free-pointer reset in memory, no over-approximation, and exact cost
`39 + (C_m(new)-C_m(old))`.  The reusable `selectedBarrettCallAndCopyExact` theorem then composes
either prepared call with all of PC 6446--6737, executes the real 8-gas dynamic return, and uses
the deployed PC 3406 `MCOPY` continuation to update the persistent accumulator.  Its transparent
cost definitions retain both schoolbook products, q1/q3 slices, truncated rows, subtraction,
the exposed correction selection, return, and copy gas; no existential gas total is introduced.

Repeated Barrett calls exposed a concrete-memory distinction that the original fresh-allocation
contract did not cover. Solidity restores `mem[0x40]` before each square or multiply, but an EVM
`MSTORE` does not shrink memory: scratch bytes materialized by the preceding Barrett call remain
above the restored free pointer. The old `newWordArrayExact68` theorem required `mem.size <= fp`
and represented a newly zeroed payload by implicit zero padding, so using it recursively would
have silently excluded every second and later exponent-loop call.

`Allocation.lean` now factors the same generated PC 1487-to-return execution through a raw exact
allocator theorem. Its original fresh-memory corollary is unchanged, while
`newWordArrayExact68Reused` records the actual in-place
`CALLDATACOPY(calldatasize(), fp+32, 32*n)`: stale payload bytes are zeroed and later scratch bytes
are preserved. A `symcheck run` from PC 1487 to PC 6468 with 2048 bytes of materialized memory,
`fp=256`, a two-word allocation, and `0xff` stale scratch reached the continuation in exactly 78
steps with exact SMT and no over-approximation. The trace changed the free pointer to 352, wrote
the length at 256, zeroed bytes 288--351, and preserved the `0xff` suffix beginning at 352. This
run validated the generalized concrete-memory result before it was encoded in Lean.

`MultiLimbSchoolbookMulFunction.lean`, `MultiLimbBarrettReusedContract.lean`, and
`MultiLimbBarrettReusedCall.lean` propagate that result through both complete schoolbook products
and all six Barrett allocation sites. The latter kernel-checks one reused PC 6446--6737 call
through q1/q3 copying, truncated multiplication, result allocation, every subtraction column, and
the selected zero/one/two-pass correction path. Its `callSteps` and `callGas` remain transparent
computations over the selected trace; expanded memory changes memory-expansion terms naturally
and does not introduce an existential gas value. `ScratchInvariant.selectedStateGeometry` and
`selectedResultValue` now derive the reused call's complete local validity certificate from the
fixed-size scratch invariant and prove the selected result is the pure remainder. In particular,
the truncated products use explicit zero payload words after Solidity's reused allocator has
materialized them; treating those words only as implicit fresh-memory padding would not describe
the recursive execution.

`MultiLimbBarrettExponentSemantic.lean` now interprets that complete call/copy boundary.  Under
the same allocator, limb-value, normalized-modulus, and in-bounds copy geometry used by the
concrete reduction, `selectedBarrettCallAndCopy_value` proves that the persistent accumulator is
exactly `(aValue * bValue) % nValue`.  This separate layer was needed because the PC 3406 trace
establishes byte relocation and exact gas, while the reduction theorem establishes the source
payload's numeric remainder; neither fact alone identifies the copied accumulator with the pure
model.

`MultiLimbBarrettExponentLoop.lean` adds executable, exposed selectors for every Barrett square,
conditional multiply, bit, and exponent byte.  Successful selections retain each concrete
zero/one/two-pass correction record and therefore have transparent path-sensitive step and gas
totals.  Independent SymCheck runs fixed the deployed control boundaries before they were encoded:
the unset post-square path is 33 steps/99 gas, set-bit dispatch is 15/50, multiply-result cleanup is
27/79, the byte guard is 6/23, the checked byte load/setup is 62 steps with
`214 + MLOAD expansion deltas` gas, and the byte backedge is 12/41.  All runs reported no
over-approximation.  The resulting kernel-checked recursive theorem executes the real square and
optional multiply for every selected bit and proves the accumulator is the MSB-first modular-power
scan of the selected exponent bytes.

The exponent selector was changed from the fresh-scratch Barrett selector to
`MultiLimbBarrettReusedCall.selectCall`. This was required for semantics as well as gas: the
materialized scratch determines the concrete correction state and therefore the chosen
zero/one/two-pass trace, not just memory-expansion charges. `BarrettExponentInvariant.afterCall`
now carries the covered memory, immutable base/modulus/constant arrays, exact headers and payloads,
and accumulator value through every selected call. The square and multiply constructors prove
each deployed computation is respectively `r*r % n` and `r*a % n`; the recursive bit and byte
theorems then prove the final accumulator is the pure exponent model without square or multiply
geometry callbacks. The only remaining external hypotheses at that boundary are the checked,
non-wrapping Solidity exponent-array load alignments.

Two direct `symcheck run` validations checked the corrected reused-scratch call frames against the
runtime bytecode. PC 3379 reached the square helper at PC 6446 in exactly 20 steps with stack
`r,r,n,mu,k,3406,...`; PC 3448 reached the multiply helper in exactly 12 steps with stack
`r,a,n,mu,k,3406,...`. With 64 active memory words both runs changed only word 64 to the restored
free pointer, produced no path constraints or over-approximations, and did not use weakened SMT.
These runs caught the distinction between the apparent fresh call frame and the actual persistent
scratch state before the recursive proof was finalized.

The caller contracts now also distinguish the accumulator header pointer `r` from the scratch
base read from Solidity's free-memory word. After `new uint256[](k)`, `r` is the allocator's entry
pointer while the scratch base is `r + wordArrayAllocationSize k`; the earlier interface passed
`r` for both. That did not alter the already generated execution trace, but it made the recursive
layout invariant impossible (`r` plus its complete array could not be at or below `r`) and would
have selected calls against the wrong restored free pointer. The corrected signatures in the
exponent, result, semantic-result, and constant-composition modules use the post-allocation
pointer. Their selected gas remains exact because each correction record already computes memory
expansion from that concrete scratch base.

The first exponent reduction needs a separate fresh-to-reused bridge. Before that call, Solidity's
result allocation has materialized only its 32-byte header; the final correction `MCOPY` is the
operation that extends the concrete `ByteArray` through the result payload and therefore through
the complete scratch end. The older correction geometry required that target payload to be
materialized already, which is correct for later reused calls but would exclude the real first
call. `finalCopy_coverage_from_start`, the corresponding Barrett correction lemmas, and
`selectedBarrettFromFirstProduct_stateGeometry` now prove this exact extension, active-word
coverage, and preservation of persistent words below the scratch base across the complete
zero/one/two-pass selector. This changes no selector, bytecode path, or gas expression; it only
distinguishes the real header-only initial allocation from the materialized state it produces.

The Barrett byte loader differs slightly from the Montgomery loop: after masking the source word
and shifting its high byte down, the optimizer omits a redundant final `AND 0xff`.  The trace model
records that executed value in `barrettExponentByteValue`; branch-bit and calldata-matching
theorems use `(byte & 0xff)`, exactly as the deployed bit test does.  This change is documented
explicitly because reusing the Montgomery helper definition would make the stacks syntactically
different even though the byte meanings agree, and assuming the omitted instruction would hide a
real bytecode difference.

`MultiLimbBarrettExponentSetup.lean` now exposes the remaining `_barrettModexpLoop` setup choices:
the arbitrary leading-zero byte scan, the bounded top-bit scan, and the all-zero exponent return.
The selected setup composes from PC 3154 through the existing selected byte loop and dynamic
return, with an executable exact gas total. Fresh SymCheck runs established the deployed constants:
the initial frame is 8 steps with `21 + MLOAD expansion` gas; an in-range byte test is 41 steps
with `146 + both checked-load expansion deltas`; a skipped zero byte adds 22/88; the first nonzero
exit adds 4/17; each positive top-bit decrement is 40/149; a set-bit exit is 33/108; and cursor zero
uses a distinct 21/70 exit. SymCheck also corrected the exhausted scan-guard cost from an initial
source-level estimate of 40 gas to the bytecode's 43 gas because the compiler retains an additional
`ISZERO`. These distinctions are recorded because collapsing the scans or charging one uniform
top-bit path would make exact gas false, while existential gas would fail to expose the bytecode's
actual path-sensitive cost.

`MultiLimbLimbsToBytes.lean` now replays the generated traces for the deployed result serializer
from PC 3559 through its dynamic return.  It executes the checked loop arithmetic, array-header and
payload loads, reversed full-limb stores, and the non-aligned Solidity shift/mask merge.  For
`q = dataLen / 32`, the exposed suffix selector chooses 14 steps/48 gas for aligned lengths and
60 steps/185 gas for a partial final word; the complete helper therefore takes
`14 + 95*q + suffixSteps` steps and `44 + 347*q + suffixGas` gas.  SymCheck concrete runs at
lengths 0, 32, 33, 64, and 1024 agreed with these formulas without over-approximation.  The
per-access theorems specialize generated memory-expansion expressions to unchanged active words
because the real caller has already allocated both arrays and all helper accesses are within that
frontier.  Those equalities remain explicit proof obligations, so the specialization excludes no
input and does not skip any `MLOAD` or `MSTORE`; it avoids only repeatedly normalizing the same
large symbolic `MachineState.M` terms.

`MultiLimbBarrettResultContract.lean` composes that serializer with the complete selected exponent
contract.  The deployed multi-limb continuation returns at PC 1745 with
`(limbs, resultBytes, modulusSize, 805, ...)`; PC 1745 contributes a three-instruction trampoline
to PC 3559 and PC 805 contributes the final dynamic jump, adding exactly 5 steps and 21 gas around
the helper.  PC 1750 is not skipped work: it is the separate one-word Barrett continuation and is
unreachable from this multi-limb stack.  The combined PC 1718-to-caller theorem retains the
exposed exponent/correction selections, all serializer validity obligations, and one exact gas
expression rather than existentially quantifying a gas result.

`MultiLimbLimbsToBytesSemantic.lean` proves the non-aligned mask rather than treating it as an
alignment exception.  For every remainder `1..31`, a fitted top limb shifted into the high bytes,
ANDed with the generated complement mask, ORed with arbitrary preexisting low bytes, and shifted
back is exactly the original limb.  A concrete `ByteArray.write` read-back theorem then shows the
leading remainder bytes have that trusted numeric value.  The module also defines the recursive
big-endian output-window invariant and proves its value is `wordLimbsToNat` of the little-endian
source limbs.  This bit/byte bridge is needed because trace replay alone exposes the exact mask
expression but does not establish its equivalence to the pure fixed-width encoding.

The serializer's `PartialValid`, existing-output-word, and partial-fit premises are conditional on
`dataLen % 32 != 0`.  This is a proof-interface correction, not an excluded alignment case: for an
aligned result the deployed trace takes the 14-step aligned suffix and never computes or reads the
partial source address.  Requiring that inactive address to be valid unnecessarily rejected a
fully aligned 1024-byte result whose hypothetical next limb lies just outside the allocated
array.  Non-aligned lengths still execute and prove the complete shift/mask/merge path.

`MultiLimbBarrettResultSemantic.lean` now derives every full-word and conditional partial trace
premise from the caller's allocation geometry and accumulator header.  It proves that the actual
reversed source loads are precisely the selected accumulator limbs, including aligned, sub-word,
and mixed lengths; derives the top-limb fit from the whole accumulator bound; and identifies the
final concrete result window with `Model.natToBytes` at the requested width.  The
`exact_of_serializerGeometry` wrapper composes those derived obligations with the exact PC 1718
execution, so callers no longer need to postulate one validity fact per serializer iteration.
The same module proves that all payload stores preserve the preallocated result header and memory
extent, then composes PC 1718 through the wrapper `RETURN`.  Its terminal theorem returns
`Model.natToBytes value dataLen` and charges the selected exponent/serializer gas plus the exact
16-gas wrapper suffix.

`MultiLimbBarrettReduceBaseExecutable.lean` connects the previously separate schoolbook branches
back to Barrett's real PC 3010 continuation.  The all-zero and positive short-dividend branches
now return to PC 1707 with their exact scan, allocation, copy, and 17-gas continuation costs.  For
the normalized branch, `KnuthSelection` exposes the complete constructed quotient-digit trace,
including every estimate/correction choice, final memory, steps, and gas.  Its zero- and
positive-shift theorems execute that same selector through direct remainder copy or
denormalization and prove the resulting concrete limb array is the pure dividend modulo divisor.
This selector record is used instead of existentially quantifying only a gas number.

Compiling those complete branch functions after the shared schoolbook scan bound was widened to
65 words exposed two stale proof annotations that still passed a `<= 32` fact by simplification.
They now discharge the immediate `<= 65` implication arithmetically.  This change affects no
bytecode, input condition, branch, memory state, or gas expression; it only updates callers to the
documented wider internal dividend interface.

`MultiLimbOddConversionSemantic.lean` now proves the missing numeric semantics of the generated
`bytesToLimbs` helper.  It normalizes every generated source and destination address, proves every
full-word store and the optional right-shifted partial store against the original big-endian source
window, identifies the complete concrete payload with `bytesToLimbsPure`, and concludes that its
little-endian limb value is `Model.bytesToNatPadded` of the source object.  The proof covers both
aligned and non-aligned lengths; the partial premise is conditional only because the aligned trace
does not execute that store.

Two memory-shape variants are recorded deliberately.  A pre-materialized destination uses ordinary
in-bounds write framing.  The actual Solidity `new uint256[]` state initially materializes only the
32-byte array header while its payload is already covered by the EVM active-word frontier, so the
deployed conversion stores extend the concrete `ByteArray` contiguously one word at a time.  The
`*_contiguous` theorems prove that exact growth and do not assume zero payload bytes were already
present.  This distinction was required to apply the semantics to the real allocator output;
pretending the payload was materialized would have excluded the actual execution state even though
the active EVM memory was correctly allocated.  `MultiLimbBarrettConversionContract.lean` derives
the contiguous geometry and source preservation from the allocator writes and now proves that the
concrete converted modulus array equals the pre-allocation source value.

`MultiLimbArrayReadSemantic.lean` closes the representation boundary between those concrete
payload words and the guarded `arrayReadWords` observer used by schoolbook arithmetic.  The bridge
uses the generated load guard and active-memory counter, including padded words beyond the current
`ByteArray` frontier, and proves that its `wordLimbsToNat` value is the shared `memoryLimbs` value.
The padded case is necessary for `reduceBase`: Solidity allocates
`max(ceil(baseSize / 32), k)` limbs but `bytesToLimbs` writes only `ceil(baseSize / 32)` limbs.
The unwritten suffix is real zero EVM memory, not an excluded width or an assumed input value.

`MultiLimbReduceBaseSemantic.lean` proves that the natural converted base equals its source byte
object, extending it through that implicit zero suffix without changing the value.  It then carries
the full selected-width dividend through the concrete remainder allocation and proves the exact
guarded array at PC 5199 still denotes the source base.  The semantic proof is in a separate module
from `MultiLimbReduceBaseContract.lean` so the large execution contract can be reused as a compiled
dependency; this is an elaboration boundary only and changes neither bytecode execution nor proof
assumptions.

The conversion preservation argument was also generalized from one 32-byte word to arbitrary
bounded padded slices.  `MultiLimbBarrettReduceBaseSemantic.lean` uses it to carry both copied input
objects through modulus allocation, modulus conversion, base allocation/conversion, and remainder
allocation.  Consequently the two guarded arrays consumed by the final `schoolbookDiv` entry are
proved equal to the original pure base and modulus models after every intervening memory write.

`MultiLimbArrayReadSemantic.lean` now also constructs complete guarded array layouts from ordinary
allocator geometry and proves word/slice equality across allocations whose `activeWords` counters
differ.  This extension is needed because the zero and short division branches allocate a fresh
one-word quotient: the allocation preserves the earlier operand bytes but intentionally advances
the EVM memory frontier.  Reusing a same-counter congruence lemma would therefore assume away a
real state change.  The two-counter bridge unfolds the generated load guards, proves both accesses
active and in bounds, and then uses equality of the actual padded reads.

`MultiLimbBarrettReduceBaseSemantic.lean` packages the final PC 5199 size, free-pointer word, all
three array headers, complete active extents, and dividend/divisor/remainder layouts.  The fresh
remainder payload is treated as covered implicit zero memory; it is not modeled as prewritten
bytes.  `MultiLimbBarrettReduceBaseSelection.lean` derives a compact `DivisionEntryFacts` record
from that real allocator chain and from the exact first modulus byte tested by the deployed scan.
It then constructs a total exposed `allZero`/`short`/`knuth` selector from concrete guarded limb
reads.  The all-zero branch executes through PC 1707 with exact path gas and has entry value zero.
The short branch executes both scans, the real size dispatch, quotient allocation, copy loop, and
PC 3010 return with exact path gas; its returned concrete array is proved equal to the complete
original base value modulo the complete original modulus value.  The proof explicitly accounts
for both the scanned high zero base limbs and the allocator-provided high zero remainder limbs.

`MultiLimbBarrettConstantComplete.lean` now exposes one exact selector for the complete PC
1707-to-1718 Barrett-constant call.  It selects only on the concrete CLZ result, retains the exact
quotient-loop witnesses and branch gas, and proves that the quotient array in the actual returned
memory is `B^(2*k) / modulus`.  The returned selector also records the exact memory extent,
Solidity free-pointer word at `0x40`, and active-word coverage at the end of the normalized-divisor
workspace.  These fields were added because the following accumulator allocation consumes that
post-call allocator state; assuming the old entry pointer or stating the quotient only in the
pre-denormalization memory would skip a real state transition.  The supporting frame lemmas prove
that quotient words above the remainder stores and the allocator word below them survive both
positive denormalization and zero-shift copy.  This is a proof-interface strengthening only: no
input, trace branch, memory write, or gas component was removed.

The constant selector is now indexed by its actual source memory and returns a quantified frame
for every complete word from `0x60` up to the first fresh allocation.  This indexing change was
needed to connect the converted base and modulus arrays to the post-division memory without an
unrelated source-memory witness.  The allocator word at `0x40` remains a separate theorem because
it intentionally changes.  Both normalization branches also prove that the returned quotient
header is `k + 2`, and the quotient observer is identified with the same `memoryWordsFrom`
representation used by the exponent invariant.  Consequently
`MultiLimbBarrettComposition.Selection.initializedInvariant` derives the freshly initialized
accumulator, preserved base and modulus, and computed Barrett constant in one persistent
invariant; none of these values is re-assumed after the constant computation.

Trace generation was checked independently at the fresh exponent boundary with the portable
SymCheck binary.  From PC 3154, a concrete `k = 2`, one-byte exponent with top bit set reached PC
3304 in 131 instructions and 451 gas, with exact SMT and no overapproximation.  Reusing the exact
target stack, PC 3304 reached the first fresh Barrett square call at PC 6446 in 89 instructions
and 309 gas without solver approximation.  The observed PC 3304 stack contained the expected
zero byte index, exponent pointer, top-bit index `7`, Barrett-constant pointer, free pointer, base
pointer, `k`, exponent length, modulus pointer, accumulator pointer, and caller return.  These runs
were useful for fixing selector boundaries, stack order, and fixed path costs; the generated trace
does not replace the Lean arithmetic argument that the selected square/multiply sequence equals
the pure modular-power model.

`MultiLimbBarrettReduceBaseComplete.lean` now closes the selected reduction state for every
all-zero, short, zero-shift Knuth, and positive-shift Knuth branch.  It proves the returned
remainder payload is the original dividend modulo the original divisor, preserves the concrete
divisor and remainder headers and payloads, and records the exact branch-dependent Solidity free
pointer and active-memory coverage.  The positive normalization proof needed a general frame for
every read below the quotient workspace; this is a proof of the writes actually performed by the
normalization path, not an assumption that the memory was unchanged.

`MultiLimbBarrettComposition.lean` uses those facts to construct the complete Barrett-constant
selector at the real PC 1707 reduction return and to compose the selected reduction and constant
paths from PC 5199.  The resulting initial exponent invariant obtains the reduced base and
`B^(2*k)/modulus` from the two concrete computations.  `reducedFreshAccumulator_eq_modelPow`
then proves that the exposed fresh all-zero/nonzero exponent selector leaves the accumulator equal
to the original base raised to the complete padded calldata exponent modulo the original modulus.
The selector-indexed `FreshBarrettModelAlignment` relation contains only the Solidity dynamic-array
and calldata-window correspondence; it contains no arithmetic result, reduced-base, constant, or
gas premise.

The fresh selector is retained through result serialization.  `MultiLimbBarrettResultContract`
adds exact fresh execution/serialization step and gas selectors, and
`MultiLimbBarrettResultSemantic.freshExactReturn_of_serializerGeometry` proves the concrete result
bytes and wrapper `RETURN`.  `MultiLimbBarrettComposition.Selection.freshExactReturn` starts at a
completed concrete constant selector and returns `Model.natToBytes` with exact gas equal to the
selected constant path, accumulator setup, selected fresh exponent path, serializer path, and
16-gas wrapper suffix.  Gas is never existentially quantified in this chain.

`FreshBarrettLoopSetupValid.finalGeometry` now derives the selected final memory coverage,
active-word representability, and accumulator header from that same concrete initial invariant on
both all-zero and nonzero exponent paths.  The corresponding
`Selection.freshExactReturn_of_invariant` therefore no longer accepts those facts as serializer
assumptions.  The serializer boundary distinguishes active source memory from concrete output
bytes: on the all-zero path Solidity materializes only `r[0] = 1`, while the remaining accumulator
limbs are EVM zero padding.
Treating the entire `k`-limb payload as already present in the `ByteArray` would be false.
The serializer semantics now uses the generated guarded padded-load theorem instead: source
validity requires the real allocated active-memory extent, while numeric source reads agree with
`memoryWordsFrom` both before and beyond the concrete byte-array frontier.  Thus zero exponents
are not excluded and no fictitious concrete accumulator payload is assumed.  Concrete bounds are
retained only for output writes, which really do modify bytes.

The padded serializer boundary was independently checked with `symcheck run` from PC 3559 to PC
1745 using `dataLen = 33`, a two-limb accumulator at `0x200`, and concrete memory ending at
`0x240` immediately after the materialized `r[0] = 1`.  The second source limb therefore began
exactly beyond the concrete frontier while remaining inside 19 active words.  SymCheck completed
the full-word and masked-partial paths in 169 instructions, wrote the 33-byte encoding ending in
`1`, and reported no overapproximation or weakened SMT.  This trace directly validates the EVM
padding behavior used by the generalized Lean serializer theorem.

The final even-modulus integration also rechecked both deployed leading-byte scan exits directly
with SymCheck. A 64-byte modulus whose first payload byte was nonzero reached the two-limb body
from PC 1603 to PC 1675 in 61 instructions, corresponding to exactly `239 - 27 = 212` gas after
the already-accounted PC 1592 setup. A second run with eight leading zero payload bytes reached
PC 1765 in 167 instructions with `delta = 8` and `offset = 40`; its exact segment cost is
`60 * 8 + 101 = 581` gas. Both runs used the complete deployed runtime bytecode, reported no
overapproximation, and did not use weakened SMT. They validate the generated scan-loop traces,
the arbitrary-length Lean scan recurrence, and the direct-versus-normalize stack boundary.

`MultiLimbBarrettComposition.baseToConstantSelection_exists` now connects PC 1700 to the completed
backend: it executes the selected-width base conversion and remainder allocation, constructs the
exposed `allZero`/`short`/Knuth PC 5199 selector, executes that selector, and constructs the exposed
Barrett-constant selector. The selector type records the exact cumulative step and gas indices,
so this bridge does not replace path gas by an existential quantity. The existing
`reducedInitializedInvariant`, `reducedFreshAccumulator_eq_modelPow`, and
`Selection.freshExactReturn_of_invariant` theorems then derive the exponent invariant and pure
modular power from those same selectors before invoking the exact serializer and wrapper return;
the reduced base and Barrett constant are not independent arithmetic premises.

The deployed multi-limb caller does not return from the serializer directly to PC 173. Its stack
contains PC 1271, whose `JUMPDEST; SWAP1; JUMP` trampoline then enters the external wrapper. The
earlier direct-PC173 result theorem remains useful for internal callers, but using it for this
path would assert the wrong continuation stack and omit 12 gas. Therefore
`freshExactReturnVia1271_of_serializerGeometry` and
`Selection.freshExactReturnVia1271_of_invariant` explicitly execute PC 1271 and state the real
28-gas post-serialization suffix: 12 gas for the trampoline plus 16 gas for the wrapper return.

While connecting the arithmetic result to that return theorem, the invariant-driven interface was
corrected to distinguish `baseValue`, the already reduced input stored before exponentiation, from
`value`, the accumulator after the selected square/multiply trace. The earlier single-value
interface accidentally required those two values to coincide and therefore could only instantiate
special executions. This was a theorem-signature bug, not a bytecode or model change. The direct
and normalized callers now pass the reduced base to the initial invariant and the independently
proved modular-power value to serialization.

`MultiLimbBarrettComposition.DirectSelection` now starts at the real PC 1592 direct branch and
retains the exact scan, modulus conversion, base conversion, selected reduction, and constant
generation indices. It also carries proofs that the concrete division arrays denote the original
source base and modulus bytes. `DirectSelection.freshExactReturnVia1271` consumes that same exposed
selector plus the exposed exponent selector and proves the returned bytes equal the trusted pure
modular-power model. Its gas is the explicit sum of every selected prefix, reduction, constant,
exponent, serializer, trampoline, and wrapper component; no arbitrary gas witness is introduced.

This final composition exposed that the earlier 234-word reserve estimate covered constant
construction but not the later accumulator and one complete reused-scratch Barrett call. Expanding
the deployed allocation formulas gives `7*k+10` words through the constant workspace,
`k+1` words for the accumulator allocation before scratch, and `8*k+16` scratch words. Thus the
maximum from the constant-entry pointer is `16*k+27 = 539` words at `k = 32`. The generic direct
selector address-space premise was strengthened to this exact structural maximum. This excludes
only impossible `2^64` pointer overflow; it does not constrain operand values, select an arithmetic
branch, or avoid any computation.

Normalized multi-limb recursion uses the same direct selector but returns to PC 1808 rather than
the external wrapper. `DirectSelection.freshReturn` therefore executes the complete selected
reduction, constant, exponent, and serializer paths to an arbitrary valid deployed continuation,
retaining exact final memory, active words, steps, gas, and the pure modular-power accumulator
equation derived from that same selector. The normalized composition instantiates
that theorem at PC 1808 and `freshRestoreToRetBar` executes the real restore `MCOPY` before jumping
to the saved Barrett continuation. `restoreMemory_bytes_eq_natToBytes` proves independently that a
zero original prefix followed by the copied normalized encoding is exactly `natToBytes` at the
original modulus width.

The PC 1808 restore boundary was also checked with a fresh concrete `symcheck run` over the deployed
runtime bytecode. With `temp=1024`, `offset=40`, `len=64`, `result=256`, and return PC 173, it
executed PCs 1808, 1809, 1811, 1812, 1813, 1814, 1815, 1816, and 1817, then reached PC 173 in nine
instructions and 36 gas. The resulting symbolic memory was exactly a 64-byte copy from 1056
(`temp+32`) to 296 (`result+offset`), and the stack was `[result, ret]`. The run reported no
overapproximation and no weakened SMT. An earlier invocation that lacked `jq` passed empty bytecode
and stopped out of bounds at PC 1808; it was discarded and is not used as validation evidence.

The normalized caller allocator is now derived from the actual aligned Solidity frontier rather
than supplied as a collection of independent memory assumptions. `wideWordResultMemory_read64`
exposes the result allocation's exact free-pointer update, and
`normalizeReentryGeometry_of_aligned` proves both following `bytes` allocations, their active-word
frontiers, headers, copied significant suffix, and preserved original operand region. The concrete
`preparedNormalizeReentryGeometry` specialization derives the required alignment equalities from
`operandFreePtr` and `wideWordResultWords`; they exclude no calldata or operand value. The recursive
`preparedNormalizedSelection_exists` then exposes the actual normalization and direct selectors
while retaining `barrettNormalizeReentryChecksGas` as an exact path expression.

A separate short-suffix construction covers originally wide moduli whose normalized significant
suffix has at most 32 bytes. `normalizedResult_modulusValue_eq_original` proves the copied suffix
has the complete original modulus value. The first significant byte, Solidity `isZeroBytes`, and
`isOneBytes` outcomes are derived from that value and from the deployed scan, including the
one-byte sentinel case. `runPreparedBarrettNormalizedWordExactAny` was generalized from an
original-modulus bound of 32 to the existing valid-input bound of 1024; its independent premise
still requires the normalized suffix to fit one word. The only changed address estimate is
`p + modulusSize + 31 <= 3295`, replacing the 32-byte-only estimate `<= 2303`. This is needed to
execute the real normalization computation for a wide original input and does not remove any
branch or arithmetic work. `runPreparedBarrettNormalizedToWordExact` constructs all remaining
headers, guards, restore bounds, and exact gas from the prepared operand state.

The normalization setup stack was independently checked with `symcheck run` from PC 1765 through
the internal setup call to PC 1784. With `offset=40`, original modulus length 64, exponent pointer
256, modulus pointer 512, temporary result 768, and original return PC 1271, the 24-step exact trace
reached PC 1784 with stack `[56,256,512,1808,40,128,768,1271,173]`. Thus the deployed mapping is
normalized length 56, recursive return PC 1808, saved offset 40, and the original result/return
continuation beneath them. The run used exact SMT with no overapproximation or weakened solving.

The recursive normalized exponent path is now constructive as well.
`BarrettExponentAccessFrame` fixes one concrete exponent header and the checked address range;
`selectFreshBarrettLoopSetup_modelAlignmentFramed` follows the generated leading-byte, top-bit,
first-byte, and remaining-byte selections and proves that every selected byte is the corresponding
padded calldata byte. `BarrettLeadingScanValid.exhaustionStart` derives the exhausted and
non-exhausted guards from the selected scan recursion itself, and
`selectFreshBarrettLoopSetup_validInvariantFramedAllocated` derives executable validity from that
scan, the concrete frame, and the allocator word at `0x40`. The prepared specialization
`NormalizedSelection.exponentSelection` exposes the canonical complete selector together with both
validity and `FreshBarrettModelAlignment`; its fuel is the concrete exponent length and limb count,
and its gas remains the exact selector-indexed expression.

The normalized specialization deliberately keeps `reducedInitializedInvariant` as a locally
inferred concrete witness. Giving the same witness a separately repeated, fully expanded dependent
type caused Lean to spend more than twelve minutes elaborating duplicate normalized-memory terms;
the inferred form checks in seconds and has the identical proposition. This is an elaboration-only
choice, not an axiom, input restriction, or compressed execution argument. The nearby prepared
wide-input proof also uses the actual `modulusSize <= 1024` fact (`hm1024`) where the old local name
referred to a different modulus proposition; that correction changes no accepted input or runtime
behavior.

## Arbitrary-width even-Barrett closure

`BarrettMultiLimbSpec.lean` closes the nontrivial even-modulus Barrett backend from the real public
entry. `WideBarrettSelection` exposes the bytecode's four actual outcomes: direct word,
normalized word, direct multi-limb, and normalized multi-limb. The multi-limb constructors retain
the complete reduction, constant, exponent, serializer, and restore selections. Its `gas`
projection is definitionally the exact static word-path cost or the exact selected multi-limb cost;
the final theorem does not existentially choose an unrelated gas value.

`wideBarrettFromEntrySelectedExact` proves the exhaustive PC 62 split. It branches first on the
deployed direct selector (`modulusSize == 1` or a nonzero first byte), and otherwise proves that the
real leading-zero scan selects normalization. The normalization branch then splits only on the
computed significant suffix length at 32 bytes. `wideBarrettSelectedModelExactGas` composes this
with `reachWideEntry`, starts at PC 0, returns the unchanged `Model.output`, and exposes the selected
branch and its exact gas. Its length-record equality is only the parser/stack alignment supplied by
`reachWideEntry`; it excludes no calldata value and bypasses no arithmetic computation.

The normalized word theorem in `BarrettSpec.lean` was generalized from an original modulus length
of at most 32 bytes to the Osaka bound of 1024 bytes plus the precise condition that the scanned
significant suffix is at most 32 bytes. The former one-word decoder was replaced with the existing
arbitrary-length operand-copy/read bridge before proving equality with the pure calldata value.
Allocator constants were increased from the old 32-byte geometry to the actual 1024-byte maximum.
Likewise, `preparedNormalizeReentryGeometryAny` records that the allocator proof never depended on
the old `modulusSize > 32` hypothesis; compatibility specializations keep that fact available to
multi-limb callers. These changes are necessary for wide inputs with enough leading zero bytes to
re-enter the word backend, and they do not change bytecode, gas, branch conditions, or model output.

The final selector construction also exposes the active-word multiplication no-wrap fact used by
the wrapper return. This is a representation guard required to identify `activeWords * 32` with
its natural-number byte frontier, not an input-value restriction. The existing structural reserve
change from 234 to 539 words remains documented above: 539 is the maximum actually required by the
constant workspace, accumulator, and one complete reused-scratch Barrett call.

Fresh `symcheck run` validations used the deployed 8,626-byte runtime from
`GeneratedTraces.json`, `--fail-on-overapproximation`, and `--no-smt-weakening`. From PC 1592, a
64-byte modulus with a nonzero first payload byte reached the two-limb body at PC 1675 in 70
instructions (61 after PC 1603), with stack `[512,1271,2,64,128,256]`. With eight leading zero
bytes it reached PC 1765 in 176 instructions (167 after PC 1603), exposing `delta = 8` and
`offset = 40`. A restore run from PC 1808 reached PC 173 in nine instructions and produced exactly
`MCOPY(296,1056,64)` while retaining result pointer 256. All three successful runs reported exact
SMT and no overapproximation. Two earlier local invocations that lacked a JSON parser supplied
empty bytecode and stopped out of bounds; they were discarded, just like the previously documented
empty-bytecode invocation.

Trace generation was highly useful for the execution layer: it fixed continuation stacks, branch
targets, instruction counts, memory-copy orientation, and every fixed gas suffix, and it exposed
the PC 1271 trampoline and PC 1808 restore that would otherwise be easy to omit. It was not a
substitute for the semantic proof. The difficult obligations remained the pure equivalence of
copied byte arrays and limbs, Barrett reduction and exponent invariants, normalization prefix
zeros, serializer padding, allocator separation, and no-wrap address arithmetic. In practical
terms, traces removed most uncertainty about what the bytecode executes, while Lean still carried
the decisive work of proving that those computations equal the pure model for arbitrary values.
