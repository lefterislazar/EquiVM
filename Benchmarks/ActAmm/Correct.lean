import Benchmarks.ActAmm.Constructor
import Solm.Equiv

/-!
# Act AMM EquiVM benchmark target

Runtime equivalence for only the `Amm` bytecode selected by Act's multisource JSON.  Reserve-token
interactions remain external EVM calls; no `Token` runtime bytecode is part of this theorem.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.ActAmm

theorem ammRuntimeCorrect :
    runtimeEquivalence config ammBytecode contract := by
  sorry

theorem ammContractCorrect :
    contractEquivalence config ammCreationBytecode ammBytecode contract :=
  contractEquivalence.intro ammConstructorCorrect ammRuntimeCorrect

end Benchmarks.ActAmm
