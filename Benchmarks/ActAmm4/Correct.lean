import Benchmarks.ActAmm4.Constructor
import Solm.Equiv

/-! # Act sand/amm4 EquiVM benchmark target -/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.ActAmm4

theorem amm4RuntimeCorrect :
    runtimeEquivalence config amm4Bytecode contract := by
  sorry

theorem amm4ContractCorrect :
    contractEquivalence config amm4CreationBytecode amm4Bytecode contract :=
  contractEquivalence.intro amm4ConstructorCorrect amm4RuntimeCorrect

end Benchmarks.ActAmm4
