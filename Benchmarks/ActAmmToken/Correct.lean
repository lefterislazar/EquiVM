import Benchmarks.ActAmmToken.Constructor
import Solm.Equiv

/-! # Act AMM Token EquiVM benchmark target -/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.ActAmmToken

theorem tokenRuntimeCorrect :
    runtimeEquivalence config tokenBytecode contract := by
  sorry

theorem tokenContractCorrect :
    contractEquivalence config tokenCreationBytecode tokenBytecode contract :=
  contractEquivalence.intro tokenConstructorCorrect tokenRuntimeCorrect

end Benchmarks.ActAmmToken
