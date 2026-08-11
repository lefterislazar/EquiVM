import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulFunction
import Examples.Precompiles.Modexp.MultiLimbMultiplicationRowsModel

/-!
# Standalone schoolbook-multiplication semantics

The collectors in this module expose the exact words loaded and stored along the evolving-memory
PC 5117 recurrence and identify that recurrence with the pure schoolbook-row model.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def innerOperandWords (a bPtr resultPtr i : UInt256) : Nat → InnerState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (operands state.memory state.activeWords bPtr resultPtr i state.j state.carry).1 ::
        innerOperandWords a bPtr resultPtr i n (advance a bPtr resultPtr i state)

def innerPriorWords (a bPtr resultPtr i : UInt256) : Nat → InnerState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (operands state.memory state.activeWords bPtr resultPtr i state.j state.carry).2.1 ::
        innerPriorWords a bPtr resultPtr i n (advance a bPtr resultPtr i state)

def innerOutputWords (a bPtr resultPtr i : UInt256) : Nat → InnerState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1 ::
        innerOutputWords a bPtr resultPtr i n (advance a bPtr resultPtr i state)

@[simp] theorem innerOperandWords_length
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    (innerOperandWords a bPtr resultPtr i n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [innerOperandWords, ih]

@[simp] theorem innerPriorWords_length
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    (innerPriorWords a bPtr resultPtr i n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [innerPriorWords, ih]

@[simp] theorem innerOutputWords_length
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    (innerOutputWords a bPtr resultPtr i n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [innerOutputWords, ih]

/-- The exact standalone inner recurrence is the pure schoolbook row over the words it actually
loads from `b` and the current result segment. -/
theorem innerCollectors_eq_row
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    Modexp.evmSchoolbookRow a
      (innerOperandWords a bPtr resultPtr i n state)
      (innerPriorWords a bPtr resultPtr i n state) state.carry =
      (innerOutputWords a bPtr resultPtr i n state,
        (iterate a bPtr resultPtr i n state).carry) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [innerOperandWords, innerPriorWords, innerOutputWords,
        Modexp.evmSchoolbookRow, iterate]
      let digit := step state.memory state.activeWords a bPtr resultPtr i state.j state.carry
      change
        (digit.1 ::
            (Modexp.evmSchoolbookRow a
              (innerOperandWords a bPtr resultPtr i n
                (advance a bPtr resultPtr i state))
              (innerPriorWords a bPtr resultPtr i n
                (advance a bPtr resultPtr i state)) digit.2).1,
          (Modexp.evmSchoolbookRow a
            (innerOperandWords a bPtr resultPtr i n
              (advance a bPtr resultPtr i state))
            (innerPriorWords a bPtr resultPtr i n
              (advance a bPtr resultPtr i state)) digit.2).2) =
        (digit.1 :: innerOutputWords a bPtr resultPtr i n
            (advance a bPtr resultPtr i state),
          (iterate a bPtr resultPtr i n
            (advance a bPtr resultPtr i state)).carry)
      have hcarry : digit.2 = (advance a bPtr resultPtr i state).carry := by
        rfl
      rw [hcarry, ih (advance a bPtr resultPtr i state)]

/-- Unbounded radix equality for all concrete products, additions, low-word stores, and carry
propagations in one complete inner recurrence. -/
theorem innerCollectors_recompose
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    Modexp.wordLimbsToNat (innerOutputWords a bPtr resultPtr i n state) +
        UInt256.size ^ n * (iterate a bPtr resultPtr i n state).carry.toNat =
      Modexp.wordLimbsToNat (innerPriorWords a bPtr resultPtr i n state) +
        a.toNat * Modexp.wordLimbsToNat
          (innerOperandWords a bPtr resultPtr i n state) + state.carry.toNat := by
  have hrow := Modexp.evmSchoolbookRow_recompose a
    (innerOperandWords a bPtr resultPtr i n state)
    (innerPriorWords a bPtr resultPtr i n state) state.carry
    (by simp)
  rw [innerCollectors_eq_row] at hrow
  simpa using hrow

/-- Appending the final carry gives the ordinary radix value of the complete stored row. -/
theorem innerCollectors_withCarry
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    Modexp.wordLimbsToNat
        (innerOutputWords a bPtr resultPtr i n state ++
          [(iterate a bPtr resultPtr i n state).carry]) =
      Modexp.wordLimbsToNat (innerPriorWords a bPtr resultPtr i n state) +
        a.toNat * Modexp.wordLimbsToNat
          (innerOperandWords a bPtr resultPtr i n state) + state.carry.toNat := by
  rw [Modexp.wordLimbsToNat_append, innerOutputWords_length]
  simp only [List.length_singleton, Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero,
    innerOperandWords_length]
  simpa using innerCollectors_recompose a bPtr resultPtr i n state

end Modexp.MultiLimbSchoolbookMulTrace
