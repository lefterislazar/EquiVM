import Examples.Precompiles.Modexp.GeneratedTraces
import Examples.Precompiles.Modexp.MultiLimbArithmeticModel
import Examples.Precompiles.Modexp.MultiLimbMemoryModel

/-!
# Generated schoolbook arithmetic segment

This file gives the 60-opcode segment at PC 4440 a compact state transition.  SymCheck generated
the instruction trace; Lean replays it and the pure arithmetic model proves the resulting limb and
carry represent the full unbounded column value.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbArithmeticTrace

open Modexp.MultiLimbMemoryModel

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def readWord (mem : ByteArray) (aw ptr : UInt256) : UInt256 :=
  if ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32))

def readWords1 (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def schoolbookOperands (mem : ByteArray) (aw operandPtr resultPtr carry : UInt256) :
    UInt256 × UInt256 × UInt256 :=
  let b := readWord mem aw operandPtr
  let result := readWord mem (readWords1 aw operandPtr) resultPtr
  (b, result, carry)

def schoolbookStep (mem : ByteArray) (aw operandPtr resultPtr a carry : UInt256) :
    UInt256 × UInt256 :=
  let operands := schoolbookOperands mem aw operandPtr resultPtr carry
  evmSchoolbookStep a operands.1 operands.2.1 operands.2.2

def schoolbookWritePtr (resultPtr : UInt256) : UInt256 :=
  resultPtr + UInt256.lnot ⟨31⟩

def schoolbookMemory (mem : ByteArray) (aw operandPtr resultPtr a carry : UInt256) : ByteArray :=
  let step := schoolbookStep mem aw operandPtr resultPtr a carry
  step.1.toByteArray.write 0 mem (schoolbookWritePtr resultPtr).toNat 32

def schoolbookAw (aw operandPtr resultPtr : UInt256) : UInt256 :=
  let aw1 := readWords1 aw operandPtr
  let aw2 := readWords1 aw1 resultPtr
  UInt256.ofNat (MachineState.M aw2.toNat (schoolbookWritePtr resultPtr).toNat 32)

def schoolbookGas (aw operandPtr resultPtr : UInt256) : Nat :=
  let aw1 := readWords1 aw operandPtr
  let aw2 := readWords1 aw1 resultPtr
  let aw3 := schoolbookAw aw operandPtr resultPtr
  187 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)

private theorem lnotZero_eq_max :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

/-- One generated schoolbook body segment, including both `MLOAD`s, full product recovery, two
carry tests, result `MSTORE`, loop-pointer updates, and exact instruction/memory gas. -/
theorem schoolbookBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {operandPtr a resultPtr carry s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (hdepth : tail.length + 14 ≤ 1014)
    (h : RDx runtimeBytecode ee g s0 ⟨4440⟩
      (operandPtr :: a :: resultPtr :: carry :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 ::
        s10 :: s11 :: s12 :: stop :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4400⟩
      (⟨4440⟩ :: (resultPtr + ⟨32⟩).lt stop :: (operandPtr + ⟨32⟩) :: a ::
        (resultPtr + ⟨32⟩) :: (schoolbookStep mem aw operandPtr resultPtr a carry).2 ::
        s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail)
      (schoolbookMemory mem aw operandPtr resultPtr a carry)
      (schoolbookAw aw operandPtr resultPtr)
      rdata acc (k + 60) (C + schoolbookGas aw operandPtr resultPtr) := by
  have rd := GeneratedTraces.trace_4440_body hdepth h
  simpa [schoolbookStep, schoolbookOperands, schoolbookMemory, schoolbookAw,
    schoolbookGas, readWord, readWords1, schoolbookWritePtr, evmSchoolbookStep,
    evmMulHigh, lnotZero_eq_max, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- Arithmetic meaning of the exact limb and carry emitted by `schoolbookBody`. -/
theorem schoolbookStep_recompose (mem : ByteArray)
    (aw operandPtr resultPtr a carry : UInt256) :
    let operands := schoolbookOperands mem aw operandPtr resultPtr carry
    let step := schoolbookStep mem aw operandPtr resultPtr a carry
    step.1.toNat + UInt256.size * step.2.toNat =
      a.toNat * operands.1.toNat + operands.2.1.toNat + operands.2.2.toNat := by
  dsimp only [schoolbookStep, schoolbookOperands]
  exact Modexp.evmSchoolbookStep_recompose _ _ _ _

/-- The generated body stores its recomposed low limb at the source-selected result slot. -/
theorem schoolbookMemory_word (mem : ByteArray)
    (aw operandPtr resultPtr a carry : UInt256)
    (hgap : (schoolbookWritePtr resultPtr).toNat - mem.size < USize.size) :
    memoryWordNat (schoolbookMemory mem aw operandPtr resultPtr a carry)
        (schoolbookWritePtr resultPtr).toNat =
      (schoolbookStep mem aw operandPtr resultPtr a carry).1.toNat := by
  unfold schoolbookMemory memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

structure SchoolbookState where
  operandPtr : UInt256
  resultPtr : UInt256
  carry : UInt256
  memory : ByteArray
  activeWords : UInt256

def schoolbookAdvance (a : UInt256) (s : SchoolbookState) : SchoolbookState where
  operandPtr := s.operandPtr + ⟨32⟩
  resultPtr := s.resultPtr + ⟨32⟩
  carry := (schoolbookStep s.memory s.activeWords s.operandPtr s.resultPtr a s.carry).2
  memory := schoolbookMemory s.memory s.activeWords s.operandPtr s.resultPtr a s.carry
  activeWords := schoolbookAw s.activeWords s.operandPtr s.resultPtr

def schoolbookIterate (a : UInt256) : Nat → SchoolbookState → SchoolbookState
  | 0, s => s
  | n + 1, s => schoolbookIterate a n (schoolbookAdvance a s)

def schoolbookIterationsGas (a : UInt256) : Nat → SchoolbookState → Nat
  | 0, _ => 0
  | n + 1, s => schoolbookGas s.activeWords s.operandPtr s.resultPtr + 10 +
      schoolbookIterationsGas a n (schoolbookAdvance a s)

def schoolbookLoopStack (s : SchoolbookState) (a : UInt256)
    (fixed : List UInt256) : List UInt256 :=
  s.operandPtr :: a :: s.resultPtr :: s.carry :: fixed

@[simp] theorem schoolbookIterate_advance (a : UInt256) (n : Nat) (s : SchoolbookState) :
    schoolbookIterate a n (schoolbookAdvance a s) = schoolbookIterate a (n + 1) s := by
  rfl

theorem schoolbookAdvance_iterate (a : UInt256) (n : Nat) (s : SchoolbookState) :
    schoolbookAdvance a (schoolbookIterate a n s) = schoolbookIterate a (n + 1) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change schoolbookAdvance a (schoolbookIterate a n (schoolbookAdvance a s)) =
        schoolbookIterate a (n + 1) (schoolbookAdvance a s)
      exact ih (schoolbookAdvance a s)

theorem schoolbookIterate_operandPtr_toNat
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hbound : state.operandPtr.toNat + 32 * n < UInt256.size) :
    (schoolbookIterate a n state).operandPtr.toNat =
      state.operandPtr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => simp [schoolbookIterate]
  | succ n ih =>
      rw [show schoolbookIterate a (n + 1) state =
        schoolbookIterate a n (schoolbookAdvance a state) by rfl]
      have hstep : (schoolbookAdvance a state).operandPtr.toNat =
          state.operandPtr.toNat + 32 := by
        exact uadd_word_lit32_toNat _ (by omega)
      rw [ih]
      · rw [hstep]
        omega
      · rw [hstep]
        omega

theorem schoolbookIterate_resultPtr_toNat
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hbound : state.resultPtr.toNat + 32 * n < UInt256.size) :
    (schoolbookIterate a n state).resultPtr.toNat =
      state.resultPtr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => simp [schoolbookIterate]
  | succ n ih =>
      rw [show schoolbookIterate a (n + 1) state =
        schoolbookIterate a n (schoolbookAdvance a state) by rfl]
      have hstep : (schoolbookAdvance a state).resultPtr.toNat =
          state.resultPtr.toNat + 32 := by
        exact uadd_word_lit32_toNat _ (by omega)
      rw [ih]
      · rw [hstep]
        omega
      · rw [hstep]
        omega

theorem schoolbookGuardFacts
    (a stop : UInt256) (columns : Nat) (state : SchoolbookState)
    (hcolumns : 0 < columns)
    (hbound : state.resultPtr.toNat + 32 * columns < UInt256.size)
    (hstop : stop.toNat = state.resultPtr.toNat + 32 * columns) :
    (∀ j, j < columns - 1 →
      (schoolbookAdvance a (schoolbookIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩) ∧
    (schoolbookAdvance a
      (schoolbookIterate a (columns - 1) state)).resultPtr.lt stop = ⟨0⟩ := by
  have hiter (j : Nat) (hj : j < columns) :
      (schoolbookAdvance a (schoolbookIterate a j state)).resultPtr.toNat =
        state.resultPtr.toNat + 32 * (j + 1) := by
    rw [schoolbookAdvance_iterate]
    rw [schoolbookIterate_resultPtr_toNat]
    omega
  constructor
  · intro j hj
    have hlt :
        (schoolbookAdvance a (schoolbookIterate a j state)).resultPtr.toNat <
          stop.toNat := by
      rw [hiter j (by omega), hstop]
      omega
    rw [ult_one hlt]
    decide
  · have heq :
        (schoolbookAdvance a
          (schoolbookIterate a (columns - 1) state)).resultPtr.toNat = stop.toNat := by
      rw [hiter (columns - 1) (by omega), hstop]
      congr 1
      omega
    apply ult_zero
    omega

/-- Execute any number of generated schoolbook bodies for which the inner-loop guard continues.
Every iteration includes the 60-opcode body and its 10-gas back-edge `JUMPI`. -/
theorem schoolbookIterations
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
      (k + 61 * n) (C + schoolbookIterationsGas a n state) := by
  induction n generalizing state k C with
  | zero => simpa [schoolbookIterate, schoolbookIterationsGas]
  | succ n ih =>
      have rd4400 := schoolbookBody hdepth h
      have rdNext := rd4400.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (schoolbookAdvance a
            (schoolbookIterate a j (schoolbookAdvance a state))).resultPtr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [schoolbookIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := schoolbookAdvance a state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 61 * (n + 1)) (by omega) rfl
      simpa [schoolbookLoopStack, schoolbookIterate, schoolbookAdvance,
        schoolbookIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using normalized

def schoolbookThroughExitGas (a : UInt256) (n : Nat) (state : SchoolbookState) : Nat :=
  schoolbookIterationsGas a n state +
    schoolbookGas (schoolbookIterate a n state).activeWords
      (schoolbookIterate a n state).operandPtr
      (schoolbookIterate a n state).resultPtr + 10

/-- Execute the continuing reduction columns and the final column whose guard exits at PC 4401. -/
theorem schoolbookThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 s8 s9 s10 s11 s12 stop : UInt256}
    (state : SchoolbookState)
    (hdepth : tail.length + 14 ≤ 1014)
    (hcontinue : ∀ j, j < n →
      (schoolbookAdvance a (schoolbookIterate a j state)).resultPtr.lt stop ≠ ⟨0⟩)
    (hexit :
      (schoolbookAdvance a (schoolbookIterate a n state)).resultPtr.lt stop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4440⟩
      (schoolbookLoopStack state a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    let final := schoolbookAdvance a (schoolbookIterate a n state)
    RDx runtimeBytecode ee g s0 ⟨4401⟩
      (schoolbookLoopStack final a
        (s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: s12 :: stop :: tail))
      final.memory final.activeWords rdata acc
      (k + 61 * (n + 1)) (C + schoolbookThroughExitGas a n state) := by
  have rdIterations := schoolbookIterations state hdepth hcontinue h
  have rdBody := schoolbookBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 61 * (n + 1)) (by omega) rfl
  simpa [schoolbookLoopStack, schoolbookAdvance, schoolbookThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

end Modexp.MultiLimbArithmeticTrace
