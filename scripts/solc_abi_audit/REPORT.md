# ABI decoding and encoding across solc 0.8.13–0.8.37

**Question.** How do solc's ABI decoder and encoder behave across recent releases and the two code
generators, how does decoding differ between `memory` and `calldata` (reference) parameters, and
what must a decoder/encoder for the Solidity semantics reproduce to match solc 0.8.37? (0.8.38 is
not released; `bugs.json` already lists fixes for it, none of them ABI-related.)

**Answer.**
- **Across 0.8.13–0.8.37, ABI behaviour changes at three releases only:**
  - **0.8.14:** re-encoding a nested calldata array validates the inner length (the
    `NestedCalldataArrayAbiReencodingSizeValidation` fix).
  - **0.8.16:** `abi.encode(<dynamic>, <static calldata array>)` no longer corrupts its output (the
    `AbiReencodingHeadOverflowWithStaticArrayCleanup` fix).
  - **0.8.37 (via-IR only):** `require(c, E({b: …, a: …}))` encodes named arguments in declaration
    order (the `MisorderedNamedParametersInRequireWithCustomErrors` fix).
- **The two code generators agree everywhere except:**
  - re-encoding a one-dimensional calldata array of value types with a dirty element (`return x`,
    `x[a:b]`): legacy masks the element, via-IR reverts;
  - the `require` bug above;
  - `require` with a custom error, which legacy only compiles from 0.8.27.
- **Memory and calldata parameters differ systematically:** a memory parameter is decoded and
  validated in full on entry, a calldata parameter only in its head.

## Method

- **Probes** (`probes/`, 6 contracts, 87 external functions):
  - value-type parameters and returns (including dirty stack values)
  - memory and calldata parameters of every shape: arrays, fixed arrays, nested arrays,
    `bytes`/`string`, `bytes[]`, structs with dynamic members, arrays of structs
  - accesses to calldata references: index, length, slices, struct members, copy to memory,
    re-encoding
  - `abi.decode` of memory and calldata bytes
  - `abi.encode`, `encodePacked`, `encodeWithSelector`, `encodeWithSignature`, `encodeCall`
  - `revert`/`require` with strings and custom errors, `assert`
- **Static** (`abi_matrix.py`, `abi_analyze.py`): each external function's Yul closure is rooted at
  `external_fun_*`, so it includes the ABI decoder, the body and the ABI encoder. Closures are
  normalized and compared across versions with the storage audit's structural hashing.
- **Dynamic** (`abi_calldata.py`, `abi_cases.py`, `abi_dynamic.py`):
  - 96 calls are expanded into 1,824 cases. `abi_calldata.py` encodes each call itself and labels
    every word (value, offset, length, data); the encoder is checked against `cast abi-encode`.
  - Each case targets one word:
    - dirty value words (bits above the type width, a non-sign-extended `intN`, `bool = 2`, an
      enum out of range, `bytesN` low bits)
    - offsets of 2^64, 2^256−32, past the end, unaligned, zero
    - lengths of 2^64, 2^256−1, +1, 2^32
    - truncation by one byte or one word, and a trailing word
    - for `abi.decode` probes, the same mutations inside the encoded `bytes` argument
  - Every case runs on 0.8.13–0.8.37 × {legacy, via-IR} (91,200 calls).
- **Conformance** (`gen_solidity_tests.py`): the probes, all cases and solc 0.8.37 bytecode of
  both pipelines become `solidity-diff` scenarios for the Solidity semantics (`Abi/<contract>/<pipeline>`).

## Findings

### Version boundaries (both methods agree)

| release | static change | dynamic effect |
|---|---|---|
| 0.8.14 | `calldata_access` of a nested calldata array bounds-checks from the data pointer instead of the base | `abi.encode(x)` of a `uint8[][] calldata` with truncated calldata or an inner length +1 reverted only from 0.8.14 (before, it read past the end) |
| 0.8.16 | `copy_calldata_to_memory` stops writing a zero word after the copy; memory copies always clear the word after the data | `abi.encode(bytes calldata, uint256[2] calldata)` output changes (head-overflow corruption fixed) |
| 0.8.25 | `mcopy` | none (memory only) |
| 0.8.26 | formatting of `require_helper` | none |
| 0.8.37 | via-IR passes named `require` error arguments in declaration order | `reqNamed` revert data changes (via-IR) |

Everything else is identical, release to release, in both pipelines: value-type validation,
offset/length checks, panic codes, the encoders, and error data.

### Legacy vs via-IR

| case | legacy | via-IR |
|---|---|---|
| `return x` / `x[a:b]` for `uint8[] calldata` or `uint8[3] calldata` with a dirty element (`0x102`) | succeeds, element masked (`2`) | `revert()` |
| the same for nested arrays and structs | `revert()` | `revert()` |
| `require(c, E({b: b, a: a}))`, 0.8.27–0.8.36 | correct order | arguments swapped |
| `require(c, E(...))` | from 0.8.27 | from 0.8.26 |
| unoptimized `mix(uint8, bytes calldata, bool)` | compiles | stack too deep up to 0.8.20 |

### Memory vs calldata parameters (0.8.37, both pipelines)

A memory parameter is copied by `abi_decode_*` on entry: every offset and length is checked, every
value word is validated, and an oversized length fails the memory allocation. A calldata parameter
is checked only as far as its head (offset and length within the calldata); its content is checked
when it is read (`calldata_array_index_access`, `access_calldata_tail`, the validators), copied to
memory or re-encoded.

| malformed input | memory | calldata |
|---|---|---|
| length 2^64 or 2^256−1 | `Panic(0x41)` | `revert()` (entry bounds check) |
| dirty element, or a malformed inner offset/length, in data never read | `revert()` on entry | succeeds |
| out-of-range index with another element dirty | `revert()` (decoding first) | `Panic(0x32)` |
| reading the dirty element | `revert()` | `revert()` at the read |
| element offset 2^256−32 of a nested dynamic element | `revert()`: memory decoders reject offsets above 2^64−1 | accepted when not read: the access helper adds the offset modulo 2^256 |

## Conformance of the Solidity semantics (solc 0.8.37 fixtures)

| scenario | legacy | via-IR |
|---|---|---|
| `AbiValue` (91 cases) | OK | OK |
| `AbiMem` (433) | 2 fail | 2 fail |
| `AbiCd` (669) | OK | 8 fail |
| `AbiDecode` (270) | OK | OK |
| `AbiEncode` (307) | 2 fail | 2 fail |
| `AbiRequireError` (48) | OK | OK |

- **Both pipelines:** a `bytes[]` element offset of 2^256−32, in a memory parameter (`AbiMem.bb`)
  or a memory argument re-encoded (`AbiEncode.eNested`), reverts in solc but is accepted by the
  semantics. Its argument decoding uses the shared `ABI.decodeCalldata` in `modern` mode, which
  deliberately adds nested element offsets modulo 2^256. That is right for calldata references,
  but memory decoding caps them at 2^64−1.
- **via-IR only:** the dirty-element re-encoding row above. The semantics masks the element, as
  legacy does.

The Solidity semantics now decodes with `Solidity/Semantics/Abi.lean` (branch `solidity-faithful`
of the `solidity` remote), which adds the memory offset bound; all legacy scenarios agree. It
models the legacy code generator, so `gen_solidity_tests.py` marks the cases where the two code
generators differ at 0.8.37 (the 8 dirty-element re-encodings) as known deviations of the via-IR
scenarios.

## Reproducing

```
python3 abi_matrix.py            # out/raw/<pipeline>/<version>, out/closures (≈15 s)
python3 abi_analyze.py           # out/analysis.json, out/diffs
python3 abi_dynamic.py           # out/dynamic.json (needs anvil, cast; ≈75 s)
python3 gen_solidity_tests.py <EquiVM checkout>   # Solidity/Test/{Fixtures,Scenarios}/AbiProbes*
```
