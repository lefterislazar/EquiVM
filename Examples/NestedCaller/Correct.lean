import Examples.NestedCaller.Bytecode
import Examples.NestedCaller.Run
import Solm.Equiv

/-! Full runtime refinement of the bounded nested-caller example. The dispatcher
and ABI failures are included; neither the target's code nor call outcomes are
assumed. The body proof uses the paired GAS/CALL, internal-call and combined-loop
rules, with generated RD summaries for bytecode segments. -/
namespace NestedCaller
open Solm ABI Ethereum Ethereum.EVM

/-- Runtime equivalence for every input, gas budget and related account maps.
The bound on count is enforced by both programs, not imposed on this theorem. -/
theorem nestedCallerCorrect : runtimeEquivalence nestedCallerConfig nestedCallerBytecode nestedCallerContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : I.calldata.size < 4
    · exact nestedCallerShortRevert hcode hsize hperm hwv hsz
    · have hsz4 : 4 ≤ I.calldata.size := by omega
      by_cases hsel : (runSelector == I.calldata.extract 0 4) = true
      · exact nestedCallerRunBodyCore hcode hsize hperm hwv hsel
          (nestedCallerReachBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
          hAccounts
      · rw [Bool.not_eq_true] at hsel
        exact nestedCallerNoDispatch hcode hsize hperm hwv hsel
  · exact nestedCallerNonPayable hcode hwv

end NestedCaller
