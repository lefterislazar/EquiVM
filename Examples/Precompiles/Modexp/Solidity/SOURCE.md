# Modexp Solidity source snapshot

This directory is a self-contained snapshot of `evmification/src/modexp` used by the Modexp
bytecode proof.

Upstream repository commit:

```text
c0aabf32aa4682925836044948a204da8cd62e9f
```

`ModexpDeployed.sol` is the entry contract for `runtimeBytecode`. Its transitive source set is:

- `ModexpDeployed.sol`
- `Modexp.sol`
- `ModexpBarrett.sol`
- `ModexpMontgomery.sol`
- `LimbMath.sol`

`ModexpPrecompile.sol` is included because it is part of the same upstream source directory,
although it is not a dependency of `ModexpDeployed.sol`.

## Local source correction

The snapshot includes the proof-driven correction in `LimbMath.schoolbookDiv`: the saturated
Algorithm D estimate computes `rHat = uLo + vTop` inside `unchecked`. The following
`rHat >= uLo` test intentionally detects whether that addition wrapped. Checked Solidity addition
would instead panic on a valid input and make the intended test unreachable. The reason and
counterexample are documented in the parent `README.md`.

## Compiler

The runtime was reproduced with:

```text
solc 0.8.30+commit.73712a01
--via-ir --optimize --optimize-runs 10000 --evm-version osaka
```

Expected runtime bytecode SHA-256:

```text
23dc6e1138819cdfd3c383e21a37470d83f3bedea8299e7e263d05c6acd8868a
```

## Source hashes

```text
4157c4ec232e82ead0e2fcfd5d5b4374c6367fd640966d20682297b876965d7c  LimbMath.sol
56d18dfe017339b28d08abb081835763eadfe622c0468608bd84eec100591bd4  Modexp.sol
845f1b6b0fdf9884e5f60f438cd1928aef5338dde745644226d2ba02a6f10ed8  ModexpBarrett.sol
de8ed392b2e727ccd8e60725df9ec687e79f80ece8ad99eeffb0a3d0e606f50b  ModexpDeployed.sol
c249a85866cb98ff9221e14f94797f14b90f4dddfef9d5841f68f6ee9ca5d909  ModexpMontgomery.sol
75d016206303b4a4d0f70d8e3ba41b2a003e7d0cf38ff23e7d3b33cdb829d763  ModexpPrecompile.sol
```
