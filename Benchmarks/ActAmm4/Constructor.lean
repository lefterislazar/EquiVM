import Benchmarks.ActAmm4.Bytecode
import Solm.Equiv

/-! # Act sand/amm4 constructor-equivalence target -/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.ActAmm4

theorem amm4ConstructorCorrect :
    constructorEquivalence config amm4CreationBytecode contract amm4Bytecode := by
  sorry

end Benchmarks.ActAmm4
