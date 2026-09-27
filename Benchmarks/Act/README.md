# Act compatibility reductions

The [original DSS call graph](original-dss-call-graph.md) highlights the three
cyclic contract groups that have to be broken in the Act reductions.

This directory contains standalone Solidity 0.8.28 reductions of the DSS and
WETH9 benchmarks together with Act specifications. The original benchmark
sources are not modified.

Each `mocked` case is a two-contract system: the reduced target and one typed,
acyclic leaf mock. Calls that were dynamic in the original source are redirected
to that fixed mock. Mock actions have no application-storage effects and mock
reads return deterministic path-enabling values. WETH9's payable mock necessarily
receives the transferred EVM balance.

Each `standalone` case keeps calls to known DSS contracts when they can be put in
an acyclic Act system. The adjacent Solidity file contains the reduced target
plus concrete, typed, stateful reductions of its callees. Those callees record
the accounting action (for example moved, minted, grabbed, or auction counts),
and the Act target transitions update their storage. They are therefore not
no-op mocks. A cycle-closing back-edge is removed from the reduced leaf: for
example, the Cat system contains a leaf Flipper with no callback to Cat, while
the Flipper system contains a leaf Cat with no callback to Flipper.

Calls to dynamically selected targets are fixed to one concrete system member
or removed; unsupported generic callbacks are removed. A standalone is
call-free only when the original has no eligible known DSS edge. Run the mocked
cases first, as the runner does, so the per-contract
call-cost experiments finish before the connected-system sweep.

## Confirmed Act constraints

- Unknown call targets become partial symbolic executions and cannot pass full
  equivalence. Concrete callees need bytecode and matching Act contract blocks.
- Contract-reference state must form an acyclic, non-aliasing ownership tree.
- Structs and multi-return transitions are unavailable for this use. Struct
  fields are therefore represented by separate scalar mappings.
- Dynamic ABI data and dynamic arrays are unsupported. Fixed arrays reach
  incomplete equivalence-backend paths, so this suite avoids all arrays.
- Data-dependent loops cannot be discharged by symbolic execution. The DSS
  exponentiation routines are removed.
- The usable environment is limited to caller, call value, origin, this address,
  and contract balances. Timestamp-dependent behavior is removed.
- Strings, runtime hashing, signature recovery, and Solidity wrapping behavior
  do not have suitable Act expressions here. Dai's mocked permit uses a typed
  boolean checker instead.
- Act arithmetic is mathematical and requires explicit `inRange` conditions for
  every Solidity operation that may overflow or underflow.

## Compatibility matrix

| Target | Standalone reduction / retained DSS edges | Mocked-call reduction |
| --- | --- | --- |
| Cat | Auth, limits, bite; Cat → Vat, Vow, leaf Flipper | Adds flip reconfiguration and a fixed-size bite call sequence |
| Clipper | Auth, kick, redo, yank; Clipper → Vat, leaf Dog | Adds kick, redo, upchost, and yank; `take` is omitted after reproducibly deadlocking Act's input-space worker |
| Cure | Auth and wait configuration | Replaces the source array with membership/count mappings and adds load/tell/cage |
| Dai | Auth and reduced ERC-20 core | Adds a permit with the original parameter shape and a mock signature check |
| DaiJoin | Auth, cage, join, exit; DaiJoin → Vat, Dai | Adds join and exit calls |
| Dog | Auth, limits, digs, bark; Dog → Vat, Vow, leaf Clipper | Adds clip configuration and a fixed-size bark call sequence |
| End | Auth, wait, global cage; End → Vat, Cat, Dog | Adds reduced cage, per-ilk cage, snip, skip, skim, free, thaw, flow, pack, and cash |
| ExponentialDecrease | Auth and cut configuration; price removed | Not applicable |
| Flapper | Auth, limits, kick, cage; Flapper → Vat | Adds kick and cage call paths; symbolic fresh-ID multi-map writes were removed |
| Flipper | Auth, kick, yank; Flipper → Vat, leaf Cat | Adds kick and yank calls with bid mappings treated as read-only inputs |
| Flopper | Auth, kick, deal, cage, yank; Flopper → Vat and its fixed Gem token | Adds kick, deal, and yank with bid mappings treated as read-only inputs |
| GemJoin | Auth, cage, join, exit; GemJoin → Vat. The non-DSS gem-token calls are removed | Adds constructor decimals read, join, and exit |
| Jug | Auth, global configuration, drip; Jug → Vat | Adds ilk configuration and a reduced rate-read/fold drip with a logical step counter |
| LinearDecrease | Full call-free price behavior | Not applicable |
| Pot | Auth, time-free join and exit; Pot → Vat | Adds time-free join and exit |
| Spot | Auth, flattened ratios, scalarized poke; Spot → Vat. The dynamic oracle read becomes explicit inputs | Adds scalar oracle reads and a no-op Vat write |
| StairstepExponentialDecrease | Auth, step/cut configuration; price removed | Not applicable |
| Vat | Flattened state plus auth, permissions, configuration, cage, heal | Not applicable; signed accounting and expensive nested-map transfer operations are removed |
| Vow | Auth, numeric configuration, heal/flop/flap/cage; Vow → Vat, leaf Flapper, leaf Flopper | Adds constructor authorization and reduced settlement/auction calls; time queue removed |
| WETH9 | Deposit, balance supply, approvals, transfers; strings/fallback/withdraw removed | Adds withdrawal to a fixed payable mock |

The reductions are equivalent to their adjacent Act specifications, not to the
complete production contracts. The matrix intentionally identifies semantic
reductions so timing results are not mistaken for whole-contract proofs.

## Validation and timing

From the EquiVM repository root:

```sh
bash Benchmarks/Act/run.sh check
bash Benchmarks/Act/run.sh bench
```

`ACT_REPO`, `SOLVER`, `SMT_TIMEOUT`, `NUM_SOLVERS`, and `REPEATS` are configurable.
The default Act checkout is `/home/lazar/act`; the default benchmark repetition
count is three. Act is built once before timing. Output is TSV with target,
variant, repetition, pass/fail status, and elapsed milliseconds. Compare the
mocked and standalone rows for the same target. The mocked measurement includes
one deliberately stateless leaf and approximates per-contract call cost. The
standalone measurement includes all stateful contracts listed in that row and
therefore measures the reduced acyclic system, not just the target.

All pairs were checked with CVC5, one solver process, and an SMT timeout of
`100000000` from the Act checkout's Nix development environment.
