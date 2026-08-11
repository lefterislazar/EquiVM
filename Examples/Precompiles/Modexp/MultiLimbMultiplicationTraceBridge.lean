import Examples.Precompiles.Modexp.MultiLimbArithmeticTrace
import Examples.Precompiles.Modexp.MultiLimbMultiplicationModel

/-!
# Generated multiplication-loop semantic bridge

The exact trace loop evolves memory between iterations.  These collectors expose the operand,
prior-result, and output words observed along that evolving state, and identify them with the pure
schoolbook-row function.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def schoolbookOperandWords (a : UInt256) : Nat → SchoolbookState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.operandPtr
        state.resultPtr state.carry).1 ::
      schoolbookOperandWords a n (schoolbookAdvance a state)

def schoolbookPriorResultWords (a : UInt256) : Nat → SchoolbookState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.operandPtr
        state.resultPtr state.carry).2.1 ::
      schoolbookPriorResultWords a n (schoolbookAdvance a state)

def schoolbookOutputWords (a : UInt256) : Nat → SchoolbookState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookStep state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry).1 ::
      schoolbookOutputWords a n (schoolbookAdvance a state)

@[simp] theorem schoolbookOperandWords_length
    (a : UInt256) (n : Nat) (state : SchoolbookState) :
    (schoolbookOperandWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [schoolbookOperandWords, ih]

@[simp] theorem schoolbookPriorResultWords_length
    (a : UInt256) (n : Nat) (state : SchoolbookState) :
    (schoolbookPriorResultWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [schoolbookPriorResultWords, ih]

/-- The words produced by the generated evolving-memory loop are exactly one pure schoolbook row,
including its final carry. -/
theorem schoolbookCollectors_eq_row
    (a : UInt256) (n : Nat) (state : SchoolbookState) :
    Modexp.evmSchoolbookRow a
      (schoolbookOperandWords a n state)
      (schoolbookPriorResultWords a n state) state.carry =
      (schoolbookOutputWords a n state, (schoolbookIterate a n state).carry) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [schoolbookOperandWords, schoolbookPriorResultWords,
        schoolbookOutputWords, Modexp.evmSchoolbookRow, schoolbookIterate]
      let step := schoolbookStep state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry
      change
        (step.1 ::
            (Modexp.evmSchoolbookRow a
              (schoolbookOperandWords a n (schoolbookAdvance a state))
              (schoolbookPriorResultWords a n (schoolbookAdvance a state)) step.2).1,
          (Modexp.evmSchoolbookRow a
            (schoolbookOperandWords a n (schoolbookAdvance a state))
            (schoolbookPriorResultWords a n (schoolbookAdvance a state)) step.2).2) =
        (step.1 :: schoolbookOutputWords a n (schoolbookAdvance a state),
          (schoolbookIterate a n (schoolbookAdvance a state)).carry)
      have hcarry : step.2 = (schoolbookAdvance a state).carry := by
        rfl
      rw [hcarry, ih (schoolbookAdvance a state)]

/-- Consequently, every exact generated inner-loop run satisfies the unbounded row equation over
the words it actually loaded and stored. -/
theorem schoolbookCollectors_recompose
    (a : UInt256) (n : Nat) (state : SchoolbookState) :
    Modexp.wordLimbsToNat (schoolbookOutputWords a n state) +
        UInt256.size ^ n * (schoolbookIterate a n state).carry.toNat =
      Modexp.wordLimbsToNat (schoolbookPriorResultWords a n state) +
        a.toNat * Modexp.wordLimbsToNat (schoolbookOperandWords a n state) +
        state.carry.toNat := by
  have hrow := Modexp.evmSchoolbookRow_recompose a
    (schoolbookOperandWords a n state)
    (schoolbookPriorResultWords a n state) state.carry
    (by simp)
  rw [schoolbookCollectors_eq_row] at hrow
  simpa using hrow

/-- Exact generated execution and its pure row equation, exposed together for backend callers. -/
theorem schoolbookIterations_exact_recompose
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (state : SchoolbookState)
    (hdepth : tail.length + 14 ≤ 1014)
    (hcontinue : ∀ j, j < n →
      (schoolbookAdvance a (schoolbookIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4440⟩
      (schoolbookLoopStack state a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4440⟩
        (schoolbookLoopStack (schoolbookIterate a n state) a
          (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
        (schoolbookIterate a n state).memory
        (schoolbookIterate a n state).activeWords rdata acc
        (k + 61 * n) (C + schoolbookIterationsGas a n state) ∧
      Modexp.wordLimbsToNat (schoolbookOutputWords a n state) +
          UInt256.size ^ n * (schoolbookIterate a n state).carry.toNat =
        Modexp.wordLimbsToNat (schoolbookPriorResultWords a n state) +
          a.toNat * Modexp.wordLimbsToNat (schoolbookOperandWords a n state) +
          state.carry.toNat := by
  exact ⟨schoolbookIterations state hdepth hcontinue h,
    schoolbookCollectors_recompose a n state⟩

end Modexp.MultiLimbArithmeticTrace
