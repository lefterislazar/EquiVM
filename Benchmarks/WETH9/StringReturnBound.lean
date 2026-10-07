import Benchmarks.WETH9.StringReturnLong2
import Benchmarks.WETH9.StringReturnSymbol2

/-!
# WETH9 storage well-formedness: dynamic-string return-size bound

`name()`/`symbol()` read a Solidity compact dynamic string from storage and ABI-return it.  Over the
refinement's arbitrary-`σ` quantification, a slot header can decode to a length `≥ 2^64` bytes, and for
a return of that size the evmlean model is **unfaithful**: `ByteArray.readWithPadding`
(`evmlean/Ethereum/Wheels.lean`) does `if len ≥ 2^64 then panic!` → `default` = `ByteArray.empty`, and
`RETURN` (`evmlean/Ethereum/MachineStateOps.lean` `evmReturn`) sets `H_return :=
memory.readWithPadding mstart s`.  So a `RETURN` of `≥ 2^64` bytes yields **empty** instead of running
out of gas, while Solm returns the full decoded string — the refinement is false in that single regime.

That regime is physically unreachable: no real contract holds an `≥ 2^64`-byte (~18 exabyte) string,
and a real EVM out-of-gases on the memory expansion long before reaching such a `RETURN`.  Rather than
trusting this as an axiom, the bound is the contract's storage well-formedness precondition
(`runtimeRefinementWithWF`, as in `Benchmarks.Dss.Cure.cureStorageWF`), required only of the calls
that reach that `RETURN`: each getter's ABI-encoded string return fits in 64-bit memory addressing
(its byte size is `< 2^64`).  `96 + 32·wc` is the encoder's return-object byte size for the long case
(offset word + length word + `wc` data words + the encoder's scratch base).
-/

open Solm ABI Ethereum

namespace Benchmarks.WETH9

/-- Storage well-formedness for WETH9: a zero-value `name()` (slot 0) or `symbol()` (slot 1) call
    has an ABI string return that fits in 64-bit memory addressing (`< 2^64` bytes).  Excludes
    exactly the physically-unreachable `≥ 2^64`-byte regime where evmlean's `RETURN` truncates to
    empty; every other call (including a non-zero-value getter call, which reverts) is unconstrained.

    The size bound itself is tight: the long-string `RETURN` size is exactly `96 + 32·wc`, and
    `readWithPadding` truncates iff that is `≥ 2^64`.  Gas is quantified up to `2^256`, which covers
    the memory-expansion cost, so the refinement should fail on every excluded `(σ, I)` for a large
    enough `g` (argued, not proved here). -/
def weth9StorageWF (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  (selIs I (weth9SelBytes 0) → I.weiValue = ⟨0⟩ → 96 + 32 * weth9LongWC σ I < 2 ^ 64) ∧
  (selIs I (weth9SelBytes 7) → I.weiValue = ⟨0⟩ → 96 + 32 * weth9SymLongWC σ I < 2 ^ 64)

theorem weth9StorageWF_nameReturnSizeBound {σ : AccountMap} {I : ExecutionEnv}
    (hwf : weth9StorageWF σ I) (hsel : selIs I (weth9SelBytes 0)) (hwv : I.weiValue = ⟨0⟩) :
    96 + 32 * weth9LongWC σ I < 2 ^ 64 :=
  hwf.1 hsel hwv

theorem weth9StorageWF_symbolReturnSizeBound {σ : AccountMap} {I : ExecutionEnv}
    (hwf : weth9StorageWF σ I) (hsel : selIs I (weth9SelBytes 7)) (hwv : I.weiValue = ⟨0⟩) :
    96 + 32 * weth9SymLongWC σ I < 2 ^ 64 :=
  hwf.2 hsel hwv

end Benchmarks.WETH9
