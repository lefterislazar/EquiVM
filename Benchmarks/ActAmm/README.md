# Act multisource AMM EquiVM benchmark

This benchmark targets only `Amm` from Act's
`tests/hevm/pass/multisource/amm/amm.json`. `Token` is present in `amm.sol` because `Amm` inherits
it, but there is no separate EquiVM target for the `Token` artifact. Calls from `Amm` to `token0`
and `token1` remain real external EVM calls in the Solm model.

## Exact Act bytecode provenance

Act reads the JSON, compiles each selected Solidity source independently through hevm, and asks
hevm to run `solc --standard-json` with the source unit named `hevm.sol`, optimizer settings absent
(optimizer off), and `viaIR: false`. The source-unit name matters because it is included in the
Solidity metadata.

`generate.sh` duplicates that compiler request under `/home/lazar/act`'s Nix development
environment, requires Act's pinned compiler
`0.8.28+commit.7893614a.Linux.g++`, verifies that the local `amm.sol` is byte-for-byte identical to
the Act fixture, and extracts only `contracts["hevm.sol"].Amm`.

The checked-in results are:

- runtime: 7,063 bytes; raw-byte SHA-256
  `cf1ad938898cd680b4318188bf29a85114bbc8632ff47e83745206928586dfba`
- creation: 8,921 bytes; raw-byte SHA-256
  `955af2de6074024c31d43eded511cde59ba65c4e669c43156f6a2fe8e7446db5`

`compiler-input.json` is the precise standard-JSON input. `runtime.hex`, `creation.hex`, the ABI,
storage layout, AST, and their manifest are retained so the byte arrays are independently
auditable. `act-config.json` is a snapshot of the source-selection JSON; Act's live copy remains
the authority checked by the generator.

Regenerate or verify the artifacts from the EquiVM root:

```sh
bash Benchmarks/ActAmm/generate.sh write
bash Benchmarks/ActAmm/generate.sh check
```

Both commands enter Act's Nix environment automatically. Override `ACT_REPO` if the Act checkout
is elsewhere.

## EquiVM target

- `Spec.lean` models the full public `Amm` surface, including the inherited `Token` functions,
  Solidity 0.8 checked arithmetic, the actual storage slots, and typed calls to reserve tokens.
- The reserve-token transfer selector is `b7760c8f` for this fixture's unusual
  `transfer(uint256,address)` parameter order.
- `Bytecode.lean` contains exact creation/runtime arrays and their `JUMPDEST` tables.
- `Correct.lean` proves the ten-way runtime dispatch and its shared revert paths.
  `TotalSupply.lean`, `BalanceOf.lean`, `Allowance.lean`, `Approve.lean`, `Transfer.lean`,
  `TransferFrom.lean`, `Mint.lean`, `Burn.lean`, `Swap0.lean`, and `Swap1.lean` prove all ten
  runtime bodies. `Constructor.lean` proves the creation bytecode against the constructor
  specification, and `Correct.lean` combines both results into `ammContractCorrect`.
- `Trusted.lean` records the ten concrete function selectors as trusted facts. The EVMLean
  Keccak FFI is opaque to Lean's kernel, so the selector equalities cannot be reduced by Lean.

Build the benchmark proof with:

```sh
lake build Benchmarks.ActAmm.Correct
```

The primary target is `Benchmarks.ActAmm.ammContractCorrect`.
