# SymCheck

Prototype symbolic EVM side-condition checker, built as a small Haskell package on top of a pinned `hevm` checkout.

Current scope:

- construct a symbolic EVM VM from an arbitrary midpoint,
- run a bounded segment for a fixed amount of fuel,
- stop cleanly at a target `pc`, a normal VM halt, or an unresolved hevm effect.

This is intentionally an untrusted proof-design tool, not part of the Lean kernel.

## Build

```bash
cd Tools/SymCheck
./nix-develop
cabal build
```

Portable Linux bundle:

```bash
nix build 'path:.#portable-bundle' --extra-experimental-features 'nix-command flakes'
```

That produces `result/bin/symcheck`, a launcher that uses bundled shared
libraries and dynamic loader so it can be moved outside the originating Nix
environment on a compatible `x86_64-linux` host.

Tarball form:

```bash
nix build 'path:.#portable-tarball' --extra-experimental-features 'nix-command flakes'
```

The local `cabal.project` pins `hevm` via
`source-repository-package`, and `flake.nix` pins the same repository as a
flake input. The shell still builds a shared Haskell package set containing
both `hevm` and `symcheck`, which keeps dependency resolution aligned
without relying on machine-local relative paths.

After changing `flake.nix`, exit and re-enter the shell once:

```bash
exit
./nix-develop
```

`./nix-develop` resolves the flake through an explicit `path:` URI rooted at
this checkout, which avoids relative flake resolution edge cases.

## Smoke tests

```bash
cd Tools/SymCheck
./nix-develop
cabal run symcheck -- smoke-all
```

Available smoke commands:

- `smoke-all`: run the full built-in smoke suite
- `smoke-add`: midpoint arithmetic sanity check
- `smoke-target-pc`: stopping cleanly at a target `pc`
- `smoke-postconditions`: simple postcondition checking with exact SMT and no
  execution overapproximation
- `smoke-call-metadata`: call-boundary capture and postcondition access to
  `call[...]` facts
- `smoke-static-call-split`: symbolic branch split for static-context
  value-transfer failure
- `smoke-balance-split`: symbolic branch split for insufficient-balance
  failure/continuation
- `smoke-smt-weakening`: conservative weakening fallback on a symbolic-size
  `CopySlice` query

Example:

```bash
cabal run symcheck -- smoke-call-metadata
```

There is also a small CLI regression test suite for `run` argument parsing and
pre/post condition behavior:

```bash
cabal test cli-smoke
```

## Solver-backed bounded runs

`run` explores a bounded segment, may split symbolic branches, and uses SMT for
branch feasibility and postcondition checking.

### Minimal CLI

```bash
./nix-develop
cabal run symcheck -- run --code 600160020100 --pc 2 --stack 0x1 --fuel 3
```

### Run-specific options

- `--post COND` (repeatable; checks a postcondition on each final branch)
- `--fail-on-overapproximation` (fail if execution uses model overapproximation)
- `--no-smt-weakening` (disable conservative weakening for unsupported SMT queries)
- `--quiet-smt-weakening` (suppress weakening notes)

### Condition language

First-pass condition syntax:

- `stack[0]==7`
- `stack[1]>=var:x`
- `memory[0]==42`
- `storage[0]==42`
- `calldata[0]==9`
- `returndata[0]==0`
- `len(memory)>=32`
- `pc==5`
- `stop==success`
- `smt==exact`
- `overapprox==none`

Supported comparison operators are `==`, `!=`, `<`, `<=`, `>`, `>=`.
Supported stop predicates are `success`, `failure`, `partial`, `target`, and
`fuel`.

Supported SMT modes are:

- `exact`
- `weakened`

Supported overapproximation modes are:

- `none`
- `some`

`smt` and `overapprox` only support `==` and `!=`.

Supported symbolic word terms are:

- `stack[N]`
- `var:NAME`
- integer literals such as `7` or `0x2a`
- address literals and symbols such as `0xabcd` or `sym:callee`
- `address`, `code-address`, `caller`, `origin`, `coinbase`
- `callvalue`, `block-number`, `timestamp`
- `call-count`
- `call[N].gas`, `call[N].to`, `call[N].value`
- `call[N].input-offset`, `call[N].input-size`
- `call[N].output-offset`, `call[N].output-size`
- `call[N].returndata-len`
- `call[N].returndata[WORD_TERM]`
- `call[N].post-storage-base`
- `call[N].constraint-count`
- `call[N].opcode`
- `call[N].outcome`
- `call[N].failure-mode`
- `memory[WORD_TERM]`
- `calldata[WORD_TERM]`
- `returndata[WORD_TERM]`
- `storage[WORD_TERM]`
- `len(memory)`, `len(calldata)`, `len(returndata)`

Supported call outcomes are:

- `continued`
- `failed-deterministic`
- `failed-symbolic`

`call[N].outcome` only supports `==` and `!=`.

Supported call failure modes are:

- `returns-zero`
- `stops-frame`

`call[N].failure-mode` only supports `==` and `!=`, and it is undefined for
continued calls.

Supported call opcodes are:

- `call`
- `callcode`
- `delegatecall`
- `staticcall`

`call[N].opcode` only supports `==` and `!=`.

### Examples

Example:

```bash
cabal run symcheck -- run \
  --code 600160020100 \
  --pc 2 \
  --fuel 3 \
  --pre 'var:stack_0==5' \
  --post 'stack[0]==7'
```

Example with a call-boundary postcondition:

```bash
cabal run symcheck -- run \
  --code f100 \
  --fuel 2 \
  --stack 5 --stack 0x1234 --stack 0 --stack 0 --stack 0 --stack 0 --stack 0 \
  --post 'call-count==1' \
  --post 'call[0].to==0x1234'
```

### Run output

Final branch output, both in text mode and `--json`, includes:

- final `pc`, `stack`, `memory`, and `returndata`
- per-branch `pc` traces
- final current-contract `storage`, `transientStorage`, `originalStorage`, and
  `balance`
- known contract balances
- final path-constraint count and the rendered path constraints themselves
- call-boundary metadata, SMT mode, and overapproximation markers

### Call boundaries

`CALL`, `CALLCODE`, `DELEGATECALL`, and `STATICCALL` are treated as segment
cutpoints. SymCheck records the call facts, synthesizes an abstract post-call
continuation state, and continues execution from after the opcode.

Warning:

- after `CALL`, `CALLCODE`, and `DELEGATECALL`, current storage is replaced by a
  fresh abstract post-call store
- multiple successive post-call storage states are distinguished from each
  other
- however, each such state is still a fully abstract store rather than a
  precise update of the previous one
- later `SLOAD` facts therefore describe reads from a versioned but
  unconstrained post-call store
- deterministic pre-call failures are handled for a few concrete cases
  (`CALL` with concrete nonzero value in static context, concrete memory-range
  overflow, concrete call-depth failure, concrete insufficient balance)
- if pre-call failure depends on symbolic facts, SymCheck can now split into
  separate failure/continuation branches for some local checks
- currently this symbolic split is implemented for:
  `CALL`/`CALLCODE` in static context with symbolic value, and value-transfer
  calls with a known sender-balance expression
- more complex pre-call failure conditions still fall back to the abstract
  continuation path
- `GAS` is handled by hevm's symbolic gas state rather than a local SymCheck
  overapproximation
- `call[N].value` is only defined for `CALL` and `CALLCODE`; using it on
  `DELEGATECALL` or `STATICCALL` reports a postcondition error
- after a post-call abstraction, `EXTCODECOPY` now preserves bytes outside a
  concrete destination slice instead of abstracting all memory
- if the `EXTCODECOPY` destination range is not concrete, SymCheck still falls
  back to coarse memory abstraction and later `MSIZE` is treated abstractly
- text output reports branch-local execution overapproximation as `overapprox: ...`
- JSON output includes an `overapproximations` list per branch
- call-boundary output includes `call-outcome` / `outcome` to distinguish
  `continued`, `failed-deterministic`, and `failed-symbolic`
- call-boundary output also includes `call-failure-mode` / `failureMode` to
  distinguish failures that `returns-zero` from failures that `stops-frame`
- `--fail-on-overapproximation` treats these execution-model overapproximations
  as an immediate error
- SMT query weakening is controlled separately via `--no-smt-weakening`

This is currently a deliberate overapproximation for segment work. Treat any
storage-sensitive result after call boundaries with caution.

### SMT weakening

When a satisfiability query mentions a symbolic-size `CopySlice`, `hevm` cannot
encode it directly for SMT. SymCheck can conservatively weaken such queries by
replacing the unsupported buffer expression with a fresh abstract buffer.

- this fallback is used for branch-feasibility queries and postcondition checks
- `qed (weakened)` is still sound
- weakened satisfiable results are not trusted as exact counterexamples, so
  postcondition output reports them as `unknown`
- solution-finding queries used for concretization stay exact-only
- text output marks each branch as `smt: exact` or `smt: weakened`
- JSON output includes `usedWeakenedSmt` per branch

## Solver-free straight-line summaries

`summarize` starts at the same arbitrary midpoint as `run`, but follows only a
single path and never constructs or consults an SMT solver:

```bash
cabal run symcheck -- summarize \
  --code 600160020100 \
  --pc 2 \
  --stack 0x1 \
  --active-words 0 \
  --gas 100 \
  --fuel 32
```

The summary follows the cursor carried by `RD` in EquiVM's
`Reasoning/Reach.lean`: it reports `pc`, stack, memory, active memory words,
returndata, local storage and transient storage, completed-step count, and
cumulative symbolic gas cost. It also reports the available gas. The emitted
summary intentionally omits the broader account world, environment fields, the
original state, and any equality back to the start state.

hevm's local expression simplifier is applied throughout execution and when
rendering the summary. If an apparent SMT request simplifies to a literal
condition, `summarize` selects that path locally. If it remains symbolic, or an
opcode needs another unresolved effect or external datum, the command stops at
the cursor before that opcode; its step and gas cost are therefore not included.
For an unresolved `JUMPI`, the stop output includes both possible next
addresses, labelled `not-taken` and `taken`.
Calls and creates are also explicit boundaries, because recursively entering a
callee would no longer describe the caller's straight-line cursor. `--fuel`
remains a safety bound for concrete loops.

`summarize` accepts `--pre` constraints as annotations on the initial cursor,
but it does not use them to prove branch conditions. It rejects `--post`, since
postcondition checking is solver-backed; use `run` for that workflow.

For `summarize`, values supplied with `--stack` form a known top-of-stack prefix
above an abstract initial tail. The executor materializes `initial_stack_N`
words lazily whenever a reached opcode reads deeper than the known prefix. Pushes
and other produced values remain above the untouched tail, so a result may look
like:

```text
stack: [(Add (Var "initial_stack_0") (Var "initial_stack_1"))]
       ++ drop 2 initial-stack-tail
initial-stack-depth: 2 <= depth <= 1024
```

The lower bound prevents stack underflow and the upper bound prevents stack
overflow on every completed instruction. Use `--stack-depth N` to state an exact
total initial depth; then a definite underflow or overflow is reported at the
cursor before the failing opcode. Without it, the summary is conditional on the
reported valid depth interval. The solver-backed `run` command retains its
existing finite-stack auto-padding behavior.

### Summary options

- `--code HEX`
- `--pc N`
- `--stack WORD` (repeatable; known top-of-stack prefix)
- `--fuel N`
- `--target-pc N`
- `--memory HEX|sym:NAME`
- `--stack-depth N` (`summarize` only)
- `--active-words WORD`
- `--gas WORD`
- `--calldata HEX|sym:NAME`
- `--returndata HEX|sym:NAME`
- `--address ADDR|sym:NAME`
- `--code-address ADDR|sym:NAME`
- `--caller ADDR|sym:NAME`
- `--override-caller ADDR|sym:NAME`
- `--origin ADDR|sym:NAME`
- `--coinbase ADDR|sym:NAME`
- `--callvalue WORD`
- `--block-number WORD`
- `--timestamp WORD`
- `--static`
- `--empty-base`
- `--abstract-base`
- `--store SLOT=VALUE` (repeatable; switches current storage to concrete)
- `--pre COND` (repeatable; records an initial annotation without solver use)
- `--json` (machine-readable output)
- `--trace-opcodes` (include opcode annotations alongside `pc` traces)

## EquiVM RDx block catalogs

EquiVM's translation layer intentionally lives outside this Haskell package.  After building the
`symcheck` executable, `../generate_rdx_blocks.py` repeatedly calls the existing solver-free JSON
summary command and emits three reviewable artifact sets:

- a kernel-checked Lean block catalog, optionally split into part modules;
- a JSON coverage manifest for tools and agents;
- a Markdown catalog preserving every raw SymCheck summary for human/agent inspection.

For example:

```bash
python3 ../generate_rdx_blocks.py \
  --symcheck "$(cabal list-bin symcheck)" \
  --code 60806040525f5ffd \
  --lean-code ctorStoreRuntimeBytecode \
  --lean-import Examples.CtorStore.Bytecode \
  --namespace CtorStore.GeneratedBlocks \
  --output /tmp/CtorStoreGenerated.lean \
  --manifest /tmp/CtorStoreGenerated.json \
  --summaries /tmp/CtorStoreGenerated.md
```

Catalogs of at most 100 blocks retain the single-file layout above.  Larger catalogs are split at
block boundaries, so a body theorem and all of its edge helpers always remain together.  The path
given by `--output` becomes a small aggregator containing the single bytecode-equality check, and
the theorem files are written as `OUTPUT_STEM/Part000.lean`, `Part001.lean`, and so on.  Because
Lean imports are module names rather than paths, split generation also requires the module name of
the aggregator.  For an output at `Generated/ModexpBlocks.lean`, use:

```bash
  --output Generated/ModexpBlocks.lean \
  --output-module Generated.ModexpBlocks
```

Set `--blocks-per-file N` to choose another threshold, or `--blocks-per-file 0` to force the old
single-file layout.  The unified JSON manifest records every emitted Lean file and the part that
contains each block; the Markdown catalog likewise lists the files while retaining all summaries
in one place.

The generator returns status 2 after writing the artifacts when some block is only partially
covered.  The manifest and Markdown catalog identify the first unsupported PC/opcode.  Lake checks
committed generated Lean files but never invokes SymCheck, Cabal, Nix, or this Python script.
Generated Lean catalogs set `maxRecDepth 100000`, which is needed for closed bytecode checks on
large runtimes such as Modexp.
Terminal and control-flow edges receive generated helper theorems.  A `JUMP` helper exposes its
decode and valid-destination hypotheses.  A `JUMPI` body gets both taken and not-taken helpers; Lean
infers their exact target and condition directly from the opaque body theorem's post-state.  Agents
therefore combine blocks without translating SymCheck expression syntax into theorem headers.

Two committed catalogs exercise the integration without making Lake run Haskell:

- `Fixtures/SymCheckGeneratedSmoke.lean` and `Fixtures/ctor_store_runtime.{json,md}` use the real
  `CtorStore` runtime and cover memory growth plus a reverting terminal edge;
- `Fixtures/SymCheckGeneratedBranchSmoke.lean` and `Fixtures/dynamic_branch.{json,md}` cover
  symbolic taken/not-taken edges and the deepest shared `DUP`/`SWAP` wrappers.

`python3 -B ../test_generate_rdx_blocks.py` checks the generator and retained catalogs.  Compile
the kernel-checked fixtures with:

```bash
lake build Tools.SymCheck.Fixtures.SymCheckGeneratedSmoke \
  Tools.SymCheck.Fixtures.SymCheckGeneratedBranchSmoke
```

## Next low-hanging fruit

Small follow-up features that look useful without changing the core executor:

- add `call[N].exists` or an equivalent predicate so specs can talk about
  optional call boundaries directly instead of encoding this indirectly through
  `call-count`
- expose finer-grained overapproximation predicates in the condition language,
  not just `overapprox==none|some`; for example, let specs distinguish
  call-storage abstraction from coarse `EXTCODECOPY` memory abstraction
- improve weakening diagnostics so text/JSON output records not just that SMT
  weakening happened, but also which query used it and why
- add more world-query terms to conditions, especially balance/code facts such
  as `balance[address]`
