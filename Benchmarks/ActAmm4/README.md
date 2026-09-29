# Act `sand/amm4` Amm EquiVM benchmark

This benchmark targets only `Amm` from Act's `sand/amm4/amm.act` and `amm.sol` fixture. The
fixture has no multisource JSON. Its corresponding Act equivalence invocation is:

```sh
act equiv --spec sand/amm4/amm.act --sol sand/amm4/amm.sol
```

`Token0` and `Token1` appear in the Solidity compilation unit, but this EquiVM target contains
only the `Amm` artifact. The inherited portion of `Token` is represented in the Amm specification;
calls through the stored `token0` and `token1` addresses remain opaque typed EVM calls.

## Exact bytecode provenance

For `--sol`, Act passes the source contents to hevm as `solc Solidity source False`. Hevm invokes
`solc --standard-json` with source unit `hevm.sol`, optimizer settings absent (optimizer off), and
`viaIR: false`. The source-unit name is metadata-sensitive.

`generate.sh` reproduces this compiler input inside `/home/lazar/act`'s Nix environment, checks
that `amm.sol` remains byte-for-byte identical to the live fixture, requires the pinned compiler
`0.8.28+commit.7893614a.Linux.g++`, and extracts only
`contracts["hevm.sol"].Amm`.

The exact results are:

- runtime: 6,330 bytes; raw-byte SHA-256
  `6169549980e9475ad2b69b0ab55f4aea506f652ad10e8a45cacea41b52bdaceb`
- creation: 8,188 bytes; raw-byte SHA-256
  `4c342e66fba9b86f567c947a87e6468d544ba2a3b413c4ff23de09d057660248`

`compiler-input.json` preserves the precise Standard JSON request. The raw hex, ABI, storage
layout, AST, and SHA-256 manifest are retained alongside `Bytecode.lean`.

Regenerate or verify from the EquiVM root:

```sh
bash Benchmarks/ActAmm4/generate.sh write
bash Benchmarks/ActAmm4/generate.sh check
```

Both commands enter Act's Nix environment automatically. Set `ACT_REPO` if the Act checkout is
elsewhere.

## EquiVM target

- `Spec.lean` models all nine Amm ABI functions, including the inherited Token surface.
- It models Solidity 0.8 checked arithmetic and the emitted slots 0 through 6.
- The `swap` implementation performs both token transfers, computes both possible input amounts,
  and enforces the unadjusted product invariant from the Solidity source.
- The external transfer selector is the fixture's nonstandard
  `transfer(uint256,address)` selector `b7760c8f`.
- `Constructor.lean` and `Correct.lean` contain the completed constructor and runtime proofs.

Build the complete correctness theorem with:

```sh
lake build Benchmarks.ActAmm4.Correct
```

The primary theorem is `Benchmarks.ActAmm4.amm4ContractCorrect`. The constructor proof reuses
the matching Act AMM creation-code trace after accounting for this fixture's shorter runtime.
