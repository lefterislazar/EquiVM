import Examples.Precompiles.Modexp.MultiLimbQhatTrace

/-! # Generated q-hat refinement exits -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Exit the generated refinement loop when the full-product inequality is false. -/
theorem qhatRefinementExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {returnAddr vTop vSecond uSecond : UInt256}
    (state : QhatState)
    (hdepth : tail.length + 8 ≤ 1024)
    (hdone : qhatNeedsRefinement state.qHat state.rHat vSecond uSecond = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack state vTop vSecond uSecond (returnAddr :: tail))
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8518⟩
      (returnAddr :: state.qHat :: tail)
      mem aw rdata acc (k + 7) (C + 22) := by
  have rd8519 := h.jumpiNT (by native_decide) hdone
    (by simp only [List.length_cons]; omega)
  have rd8525 := GeneratedTraces.trace_8512_body (by omega) rd8519
  exact rd8525.withIndices (by omega) (by omega)

/-- Take the source-level overflow break after one q-hat decrement. -/
theorem qhatRefinementOverflowExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {returnAddr vTop vSecond uSecond : UInt256}
    (state : QhatState)
    (hdepth : tail.length + 8 ≤ 1020)
    (hrefine : qhatNeedsRefinement state.qHat state.rHat vSecond uSecond ≠ ⟨0⟩)
    (hoverflow : (qhatAdvance vTop state).rHat.lt vTop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack state vTop vSecond uSecond (returnAddr :: tail))
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8518⟩
      (returnAddr :: (qhatAdvance vTop state).qHat :: tail)
      mem aw rdata acc (k + 27) (C + 89) := by
  have rd8526 := h.jumpiT (by native_decide) hrefine
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd8544 := qhatDecrementBody (by simp only [List.length_cons]; omega) rd8526
  have rd8574 := rd8544.jumpiT (by native_decide) hoverflow
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd8525 := GeneratedTraces.trace_8567_body
    (by omega) rd8574
  exact rd8525.withIndices (by omega) (by omega)

end Modexp.MultiLimbDivisionTrace
