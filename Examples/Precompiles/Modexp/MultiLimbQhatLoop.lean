import Examples.Precompiles.Modexp.MultiLimbQhatExit

/-!
# Arbitrary generated q-hat refinement paths

This module composes the exact one-cycle trace separately from the large generated segment terms.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

def qhatPathEnd : QhatState → List QhatState → QhatState
  | state, [] => state
  | _, next :: rest => qhatPathEnd next rest

inductive QhatRefinementPath (vTop vSecond uSecond : UInt256) :
    QhatState → List QhatState → Prop
  | nil (state : QhatState) : QhatRefinementPath vTop vSecond uSecond state []
  | cons (state : QhatState) (rest : List QhatState)
      (hrefine : qhatNeedsRefinement state.qHat state.rHat vSecond uSecond ≠ ⟨0⟩)
      (hnoOverflow : (qhatAdvance vTop state).rHat.lt vTop = ⟨0⟩)
      (tail : QhatRefinementPath vTop vSecond uSecond (qhatAdvance vTop state) rest) :
      QhatRefinementPath vTop vSecond uSecond state (qhatAdvance vTop state :: rest)

/-- Compose an arbitrary explicit path of generated q-hat refinement cycles. -/
theorem qhatRefinementIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {states : List QhatState}
    {vTop vSecond uSecond : UInt256}
    (state : QhatState)
    (hdepth : tail.length + 7 ≤ 1020)
    (path : QhatRefinementPath vTop vSecond uSecond state states)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack state vTop vSecond uSecond tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack (qhatPathEnd state states) vTop vSecond uSecond tail)
      mem aw rdata acc (k + 55 * states.length) (C + 185 * states.length) := by
  induction path generalizing k C with
  | nil => simpa [qhatPathEnd]
  | cons state rest hrefine hnoOverflow path ih =>
      have rdNext := qhatRefinementCycle state hdepth hrefine hnoOverflow h
      have rdRest := ih (k := k + 55) (C := C + 185) rdNext
      have normalized := rdRest.withIndices
        (k' := k + 55 * (qhatAdvance vTop state :: rest).length)
        (C' := C + 185 * (qhatAdvance vTop state :: rest).length)
        (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega)
      simpa only [qhatPathEnd] using normalized

/-- Execute an arbitrary refinement path and its normal false-condition exit. -/
theorem qhatRefinementPathExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {states : List QhatState}
    {returnAddr vTop vSecond uSecond : UInt256}
    (state : QhatState)
    (hdepth : tail.length + 8 ≤ 1020)
    (path : QhatRefinementPath vTop vSecond uSecond state states)
    (hdone : qhatNeedsRefinement
      (qhatPathEnd state states).qHat (qhatPathEnd state states).rHat
      vSecond uSecond = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack state vTop vSecond uSecond (returnAddr :: tail))
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8518⟩
      (returnAddr :: (qhatPathEnd state states).qHat :: tail)
      mem aw rdata acc (k + 55 * states.length + 7)
        (C + 185 * states.length + 22) := by
  have rdEnd := qhatRefinementIterations state (by
      simp only [List.length_cons]
      omega) path h
  have rdExit := qhatRefinementExit (qhatPathEnd state states) (by omega) hdone rdEnd
  exact rdExit.withIndices (by omega) (by omega)

/-- Unbounded arithmetic invariant of an arbitrary generated refinement path. -/
theorem qhatRefinementPath_arithmetic
    {vTop vSecond uSecond : UInt256} {state : QhatState} {states : List QhatState}
    (path : QhatRefinementPath vTop vSecond uSecond state states) :
    (qhatPathEnd state states).qHat.toNat + states.length = state.qHat.toNat ∧
      (qhatPathEnd state states).rHat.toNat =
        state.rHat.toNat + states.length * vTop.toNat := by
  induction path with
  | nil state => simp [qhatPathEnd]
  | cons state rest hrefine hnoOverflow path ih =>
      have hpos := qhatRefinement_qHat_positive _ _ _ _ hrefine
      have hq := qhatAdvance_qHat_toNat vTop state hpos
      have hr := qhatAdvance_rHat_toNat vTop state hnoOverflow
      constructor
      · simp only [qhatPathEnd, List.length_cons]
        omega
      · simp only [qhatPathEnd, List.length_cons]
        rw [ih.2, hr]
        simp only [Nat.add_mul, one_mul]
        omega

end Modexp.MultiLimbDivisionTrace
