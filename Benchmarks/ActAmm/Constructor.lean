import Benchmarks.ActAmm.Bytecode
import Solm.Equiv

/-!
# Act AMM constructor-equivalence target

The creation code includes the inherited `Token` constructor and the four reserve-token
`balanceOf` calls made by `Amm` construction.  The proof is intentionally the benchmark task.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.ActAmm

theorem ammConstructorCorrect :
    constructorEquivalence config ammCreationBytecode contract ammBytecode := by
  sorry

end Benchmarks.ActAmm
