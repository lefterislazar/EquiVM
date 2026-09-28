import Benchmarks.ActAmmToken.Bytecode
import Solm.Equiv

/-! # Act AMM Token constructor-equivalence target -/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.ActAmmToken

theorem tokenConstructorCorrect :
    constructorEquivalence config tokenCreationBytecode contract tokenBytecode := by
  sorry

end Benchmarks.ActAmmToken
