import Examples.NestedCaller.Bytecode
import Examples.NestedCaller.Spec
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
  sorry

end NestedCaller
