# Act multisource AMM Token EquiVM benchmark

This benchmark targets only `Token` as selected by Act's
`tests/hevm/pass/multisource/amm/amm.json`. The JSON resolves `Token` to
`../erc20/erc20.sol`; this is compiled independently from `amm.sol` by Act/hevm.

This distinction matters: the selected ERC implementation has nine public functions and includes
`mint`, `burn`, and `burnFrom`. It is not the shorter `Token` base declaration embedded in
`amm.sol` and inherited by `Amm`.

## Exact Act bytecode provenance

Act passes the contents of each selected Solidity source independently to hevm. Hevm invokes
`solc --standard-json` with source unit `hevm.sol`, optimizer settings absent (optimizer off), and
`viaIR: false`. The source-unit name is retained because it affects Solidity metadata.

`generate.sh` reproduces that request in `/home/lazar/act`'s Nix development environment. It:

- verifies that the live AMM JSON still selects `../erc20/erc20.sol` for `Token`;
- verifies that the checked-in `erc20.sol` is byte-for-byte identical to Act's source;
- requires Act's pinned `solc 0.8.28+commit.7893614a.Linux.g++`;
- extracts only `contracts["hevm.sol"].Token`.

The exact artifacts are:

- runtime: 3,621 bytes; raw-byte SHA-256
  `a5be1f3bc5d7415b58698e033ffeb54951a0a678f60c6a6a327eb386dc2e0856`
- creation: 3,845 bytes; raw-byte SHA-256
  `a499d02feae37cc29d835b0d97dfeeef7a4454fb059ee74d7a0d5d5a4fedc9d1`

`compiler-input.json` records the exact Standard JSON request. The raw hex, ABI, storage layout,
AST, and SHA-256 manifest are retained alongside the generated Lean byte arrays.

Regenerate or verify everything from the EquiVM root:

```sh
bash Benchmarks/ActAmmToken/generate.sh write
bash Benchmarks/ActAmmToken/generate.sh check
```

Both commands enter Act's Nix environment automatically. Set `ACT_REPO` to use another Act
checkout.

## EquiVM proof target

- `Spec.lean` models all nine ABI functions, Solidity 0.8 checked arithmetic, and the emitted
  storage layout: `totalSupply` at slot 0, `balanceOf` at slot 1, and `allowance` at slot 2.
- `Bytecode.lean` contains the exact creation/runtime arrays and generated `JUMPDEST` tables.
- `Correct.lean` proves the runtime dispatch routing and shared revert paths. All nine ABI
  functions are proved in their own files. `Constructor.lean` proves deployment argument
  decoding, both storage writes, runtime return, and constructor equivalence.
- There are no external calls in this Token target.

Build the completed proof with:

```sh
lake build Benchmarks.ActAmmToken.Correct
```

The primary theorem is `Benchmarks.ActAmmToken.tokenContractCorrect`. The proof has no
placeholders. Its axiom footprint consists of Lean's standard axioms, the nine trusted
selector facts, and generated `native_decide` axioms.
