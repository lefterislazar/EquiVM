import Examples.Precompiles.Modexp.MultiLimbMontgomeryTrace

/-!
# Generated SOS Montgomery trace segments

The SOS squaring backend first accumulates the off-diagonal products, doubles the resulting
scratch words, adds the diagonal products, and finally performs Montgomery reduction.  This file
packages the generated off-diagonal, doubling, and reduction bodies as exact reusable loops.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSTrace

open Modexp.MultiLimbMemoryModel
open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem lnotZero_eq_max :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

/-! ## Off-diagonal accumulation -/

def sosOffDiagonalGas (aw operandPtr resultPtr : UInt256) : Nat :=
  multiplyPassGas aw operandPtr resultPtr

/-- One generated SOS off-diagonal product accumulation.  The transition is the same exact
schoolbook column equation as the CIOS multiply pass. -/
theorem sosOffDiagonalBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {a operandPtr resultPtr carry s4 s5 s6 s7 stop : UInt256}
    (hdepth : tail.length + 9 ≤ 1015)
    (h : RDx runtimeBytecode ee g s0 ⟨7831⟩
      (a :: operandPtr :: resultPtr :: carry :: s4 :: s5 :: s6 :: s7 :: stop :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7805⟩
      (⟨7831⟩ :: (operandPtr + ⟨32⟩).lt stop :: a :: (operandPtr + ⟨32⟩) ::
        (resultPtr + ⟨32⟩) ::
        (schoolbookStep mem aw operandPtr resultPtr a carry).2 ::
        s4 :: s5 :: s6 :: s7 :: stop :: tail)
      (multiplyPassMemory mem aw operandPtr resultPtr a carry)
      (multiplyPassAw aw operandPtr resultPtr)
      rdata acc (k + 55) (C + sosOffDiagonalGas aw operandPtr resultPtr) := by
  have rd := GeneratedTraces.trace_7831_body hdepth h
  simpa [schoolbookStep, schoolbookOperands, multiplyPassMemory, multiplyPassAw,
    multiplyPassGas, sosOffDiagonalGas, readWord, readWords1, evmSchoolbookStep, evmMulHigh,
    lnotZero_eq_max, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

structure SOSOffDiagonalState where
  operandPtr : UInt256
  resultPtr : UInt256
  carry : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosOffDiagonalAdvance (a : UInt256)
    (s : SOSOffDiagonalState) : SOSOffDiagonalState where
  operandPtr := s.operandPtr + ⟨32⟩
  resultPtr := s.resultPtr + ⟨32⟩
  carry := (schoolbookStep s.memory s.activeWords s.operandPtr s.resultPtr a s.carry).2
  memory := multiplyPassMemory s.memory s.activeWords s.operandPtr s.resultPtr a s.carry
  activeWords := multiplyPassAw s.activeWords s.operandPtr s.resultPtr

def sosOffDiagonalIterate (a : UInt256) : Nat → SOSOffDiagonalState → SOSOffDiagonalState
  | 0, s => s
  | n + 1, s => sosOffDiagonalIterate a n (sosOffDiagonalAdvance a s)

def sosOffDiagonalIterationsGas (a : UInt256) : Nat → SOSOffDiagonalState → Nat
  | 0, _ => 0
  | n + 1, s => sosOffDiagonalGas s.activeWords s.operandPtr s.resultPtr + 10 +
      sosOffDiagonalIterationsGas a n (sosOffDiagonalAdvance a s)

def sosOffDiagonalStack (s : SOSOffDiagonalState) (a : UInt256)
    (fixed : List UInt256) : List UInt256 :=
  a :: s.operandPtr :: s.resultPtr :: s.carry :: fixed

@[simp] theorem sosOffDiagonalIterate_advance (a : UInt256) (n : Nat)
    (s : SOSOffDiagonalState) :
    sosOffDiagonalIterate a n (sosOffDiagonalAdvance a s) =
      sosOffDiagonalIterate a (n + 1) s := by
  rfl

/-- Execute any finite number of generated SOS off-diagonal bodies whose guard continues. -/
theorem sosOffDiagonalIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 stop : UInt256}
    (state : SOSOffDiagonalState)
    (hdepth : tail.length + 9 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (sosOffDiagonalAdvance a
        (sosOffDiagonalIterate a j state)).operandPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7831⟩
      (sosOffDiagonalStack state a (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7831⟩
      (sosOffDiagonalStack (sosOffDiagonalIterate a n state) a
        (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      (sosOffDiagonalIterate a n state).memory
      (sosOffDiagonalIterate a n state).activeWords rdata acc
      (k + 56 * n) (C + sosOffDiagonalIterationsGas a n state) := by
  induction n generalizing state k C with
  | zero => simpa [sosOffDiagonalIterate, sosOffDiagonalIterationsGas]
  | succ n ih =>
      have rd7812 := sosOffDiagonalBody hdepth h
      have rdNext := rd7812.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (sosOffDiagonalAdvance a
            (sosOffDiagonalIterate a j
              (sosOffDiagonalAdvance a state))).operandPtr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [sosOffDiagonalIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := sosOffDiagonalAdvance a state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 56 * (n + 1)) (by omega) rfl
      simpa [sosOffDiagonalStack, sosOffDiagonalIterate, sosOffDiagonalAdvance,
        sosOffDiagonalIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using normalized

def sosOffDiagonalThroughExitGas
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) : Nat :=
  sosOffDiagonalIterationsGas a n state +
    sosOffDiagonalGas (sosOffDiagonalIterate a n state).activeWords
      (sosOffDiagonalIterate a n state).operandPtr
      (sosOffDiagonalIterate a n state).resultPtr + 10

/-- Execute the continuing off-diagonal columns and the final column that exits at PC 7806. -/
theorem sosOffDiagonalThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 stop : UInt256}
    (state : SOSOffDiagonalState)
    (hdepth : tail.length + 9 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (sosOffDiagonalAdvance a
        (sosOffDiagonalIterate a j state)).operandPtr.lt stop ≠ ⟨0⟩)
    (hexit :
      (sosOffDiagonalAdvance a
        (sosOffDiagonalIterate a n state)).operandPtr.lt stop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7831⟩
      (sosOffDiagonalStack state a (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    let final := sosOffDiagonalAdvance a (sosOffDiagonalIterate a n state)
    RDx runtimeBytecode ee g s0 ⟨7806⟩
      (sosOffDiagonalStack final a (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      final.memory final.activeWords rdata acc
      (k + 56 * (n + 1)) (C + sosOffDiagonalThroughExitGas a n state) := by
  have rdIterations := sosOffDiagonalIterations state hdepth hcontinue h
  have rdBody := sosOffDiagonalBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 56 * (n + 1)) (by omega) rfl
  simpa [sosOffDiagonalStack, sosOffDiagonalAdvance, sosOffDiagonalThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-! ## Doubling pass -/

def sosDoubleWord (mem : ByteArray) (aw ptr : UInt256) : UInt256 :=
  readWord mem aw ptr

def sosDoubleOutput (mem : ByteArray) (aw ptr carry : UInt256) : UInt256 :=
  carry.lor ((sosDoubleWord mem aw ptr).shiftLeft ⟨1⟩)

def sosDoubleCarry (mem : ByteArray) (aw ptr : UInt256) : UInt256 :=
  (sosDoubleWord mem aw ptr).shiftRight ⟨255⟩

def sosDoubleMemory (mem : ByteArray) (aw ptr carry : UInt256) : ByteArray :=
  (sosDoubleOutput mem aw ptr carry).toByteArray.write 0 mem ptr.toNat 32

def sosDoubleAw1 (aw ptr : UInt256) : UInt256 := readWords1 aw ptr

def sosDoubleAw (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (sosDoubleAw1 aw ptr).toNat ptr.toNat 32)

def sosDoubleGas (aw ptr : UInt256) : Nat :=
  87 + (Cₘ (sosDoubleAw1 aw ptr) - Cₘ aw) +
    (Cₘ (sosDoubleAw aw ptr) - Cₘ (sosDoubleAw1 aw ptr))

/-- One generated scratch-limb doubling body, including its exact carry bit and gas. -/
theorem sosDoubleBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {carry ptr stop s3 s4 s5 s6 s7 s8 s9 s10 s11 : UInt256}
    (hdepth : tail.length + 12 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨7747⟩
      (carry :: ptr :: stop :: s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7293⟩
      (⟨7747⟩ :: (ptr + ⟨32⟩).lt stop :: sosDoubleCarry mem aw ptr ::
        (ptr + ⟨32⟩) :: stop :: s3 :: s4 :: s5 :: s6 :: s11 :: s8 :: s9 :: s10 ::
        s11 :: tail)
      (sosDoubleMemory mem aw ptr carry) (sosDoubleAw aw ptr)
      rdata acc (k + 29) (C + sosDoubleGas aw ptr) := by
  have rd := GeneratedTraces.trace_7747_body hdepth h
  simpa [sosDoubleWord, sosDoubleOutput, sosDoubleCarry, sosDoubleMemory,
    sosDoubleAw1, sosDoubleAw, sosDoubleGas, readWord, readWords1,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

structure SOSDoubleState where
  carry : UInt256
  ptr : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosDoubleAdvance (s : SOSDoubleState) : SOSDoubleState where
  carry := sosDoubleCarry s.memory s.activeWords s.ptr
  ptr := s.ptr + ⟨32⟩
  memory := sosDoubleMemory s.memory s.activeWords s.ptr s.carry
  activeWords := sosDoubleAw s.activeWords s.ptr

def sosDoubleIterate : Nat → SOSDoubleState → SOSDoubleState
  | 0, s => s
  | n + 1, s => sosDoubleIterate n (sosDoubleAdvance s)

def sosDoubleIterationsGas : Nat → SOSDoubleState → Nat
  | 0, _ => 0
  | n + 1, s => sosDoubleGas s.activeWords s.ptr + 10 +
      sosDoubleIterationsGas n (sosDoubleAdvance s)

def sosDoubleStack (s : SOSDoubleState) (stop : UInt256)
    (fixed : List UInt256) : List UInt256 :=
  s.carry :: s.ptr :: stop :: fixed

@[simp] theorem sosDoubleIterate_advance (n : Nat) (s : SOSDoubleState) :
    sosDoubleIterate n (sosDoubleAdvance s) = sosDoubleIterate (n + 1) s := by
  rfl

/-- Execute any finite number of generated doubling bodies whose guard continues. -/
theorem sosDoubleIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {stop s3 s4 s5 s6 s7 s8 s9 s10 s11 : UInt256}
    (state : SOSDoubleState)
    (hdepth : tail.length + 12 ≤ 1021)
    (hfixed : s7 = s11)
    (hcontinue : ∀ j, j < n →
      (sosDoubleAdvance (sosDoubleIterate j state)).ptr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7747⟩
      (sosDoubleStack state stop (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7747⟩
      (sosDoubleStack (sosDoubleIterate n state) stop
        (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      (sosDoubleIterate n state).memory (sosDoubleIterate n state).activeWords
      rdata acc (k + 30 * n) (C + sosDoubleIterationsGas n state) := by
  induction n generalizing state k C with
  | zero => simpa [sosDoubleIterate, sosDoubleIterationsGas]
  | succ n ih =>
      have rd7300 := sosDoubleBody hdepth h
      have rdNext := rd7300.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (sosDoubleAdvance
            (sosDoubleIterate j (sosDoubleAdvance state))).ptr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [sosDoubleIterate_advance] using hcontinue (j + 1) (by omega)
      have rdNext' : RDx runtimeBytecode ee g s0 ⟨7747⟩
          (sosDoubleStack (sosDoubleAdvance state) stop
            (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
          (sosDoubleAdvance state).memory (sosDoubleAdvance state).activeWords
          rdata acc (k + 29 + 1) (C + sosDoubleGas state.activeWords state.ptr + 10) := by
        simpa [sosDoubleStack, sosDoubleAdvance, hfixed] using rdNext
      have rdRest := ih (state := sosDoubleAdvance state) hcontinue' rdNext'
      have normalized := rdRest.withIndices (k' := k + 30 * (n + 1)) (by omega) rfl
      simpa [sosDoubleStack, sosDoubleIterate, sosDoubleAdvance,
        sosDoubleIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add, hfixed] using normalized

def sosDoubleThroughExitGas (n : Nat) (state : SOSDoubleState) : Nat :=
  sosDoubleIterationsGas n state +
    sosDoubleGas (sosDoubleIterate n state).activeWords
      (sosDoubleIterate n state).ptr + 10

/-- Execute the continuing doubling words and the final word that exits at PC 7294. -/
theorem sosDoubleThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {stop s3 s4 s5 s6 s7 s8 s9 s10 s11 : UInt256}
    (state : SOSDoubleState)
    (hdepth : tail.length + 12 ≤ 1021)
    (hfixed : s7 = s11)
    (hcontinue : ∀ j, j < n →
      (sosDoubleAdvance (sosDoubleIterate j state)).ptr.lt stop ≠ ⟨0⟩)
    (hexit : (sosDoubleAdvance (sosDoubleIterate n state)).ptr.lt stop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7747⟩
      (sosDoubleStack state stop
        (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      state.memory state.activeWords rdata acc k C) :
    let final := sosDoubleAdvance (sosDoubleIterate n state)
    RDx runtimeBytecode ee g s0 ⟨7294⟩
      (sosDoubleStack final stop
        (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      final.memory final.activeWords rdata acc
      (k + 30 * (n + 1)) (C + sosDoubleThroughExitGas n state) := by
  have rdIterations := sosDoubleIterations state hdepth hfixed hcontinue h
  have rdBody := sosDoubleBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 30 * (n + 1)) (by omega) rfl
  simpa [sosDoubleStack, sosDoubleAdvance, sosDoubleThroughExitGas, hfixed,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-! ## Diagonal products -/

def sosDiagonalAi (mem : ByteArray) (aw aOff : UInt256) : UInt256 :=
  readWord mem aw aOff

def sosDiagonalAw1 (aw aOff : UInt256) : UInt256 := readWords1 aw aOff

def sosDiagonalLowPrior
    (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  readWord mem (sosDiagonalAw1 aw aOff) sOff

def sosDiagonalAw2 (aw sOff aOff : UInt256) : UInt256 :=
  readWords1 (sosDiagonalAw1 aw aOff) sOff

def sosDiagonalLow (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  sosDiagonalLowPrior mem aw sOff aOff +
    UInt256.mul (sosDiagonalAi mem aw aOff) (sosDiagonalAi mem aw aOff)

def sosDiagonalLowCarry (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  (sosDiagonalLow mem aw sOff aOff).lt (sosDiagonalLowPrior mem aw sOff aOff)

def sosDiagonalMemory1 (mem : ByteArray) (aw sOff aOff : UInt256) : ByteArray :=
  (sosDiagonalLow mem aw sOff aOff).toByteArray.write 0 mem sOff.toNat 32

def sosDiagonalAw3 (aw sOff aOff : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (sosDiagonalAw2 aw sOff aOff).toNat sOff.toNat 32)

def sosDiagonalHighPrior
    (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  readWord (sosDiagonalMemory1 mem aw sOff aOff)
    (sosDiagonalAw3 aw sOff aOff) (sOff + ⟨32⟩)

def sosDiagonalAw4 (aw sOff aOff : UInt256) : UInt256 :=
  readWords1 (sosDiagonalAw3 aw sOff aOff) (sOff + ⟨32⟩)

def sosDiagonalHigh1 (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  sosDiagonalHighPrior mem aw sOff aOff +
    evmMulHigh (sosDiagonalAi mem aw aOff) (sosDiagonalAi mem aw aOff)

def sosDiagonalHighCarry1 (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  (sosDiagonalHigh1 mem aw sOff aOff).lt (sosDiagonalHighPrior mem aw sOff aOff)

def sosDiagonalHigh (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  sosDiagonalHigh1 mem aw sOff aOff + sosDiagonalLowCarry mem aw sOff aOff

def sosDiagonalHighCarry2 (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  (sosDiagonalHigh mem aw sOff aOff).lt (sosDiagonalHigh1 mem aw sOff aOff)

def sosDiagonalCarry (mem : ByteArray) (aw sOff aOff : UInt256) : UInt256 :=
  sosDiagonalHighCarry1 mem aw sOff aOff + sosDiagonalHighCarry2 mem aw sOff aOff

def sosDiagonalMemory (mem : ByteArray) (aw sOff aOff : UInt256) : ByteArray :=
  (sosDiagonalHigh mem aw sOff aOff).toByteArray.write
    0 (sosDiagonalMemory1 mem aw sOff aOff) (sOff + ⟨32⟩).toNat 32

def sosDiagonalAw (aw sOff aOff : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (sosDiagonalAw4 aw sOff aOff).toNat (sOff + ⟨32⟩).toNat 32)

def sosDiagonalGas (aw sOff aOff : UInt256) : Nat :=
  let aw1 := sosDiagonalAw1 aw aOff
  let aw2 := sosDiagonalAw2 aw sOff aOff
  let aw3 := sosDiagonalAw3 aw sOff aOff
  let aw4 := sosDiagonalAw4 aw sOff aOff
  let aw5 := sosDiagonalAw aw sOff aOff
  199 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) +
    (Cₘ aw3 - Cₘ aw2) + (Cₘ aw4 - Cₘ aw3) + (Cₘ aw5 - Cₘ aw4)

/-- Add one full-width diagonal square to adjacent scratch limbs and enter carry propagation. -/
theorem sosDiagonalBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {sOff aOff s2 s3 s4 drop s6 : UInt256}
    (hdepth : tail.length + 7 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7636⟩
      (sOff :: aOff :: s2 :: s3 :: s4 :: drop :: s6 :: tail)
      mem aw rdata acc k C) :
    let carry := sosDiagonalCarry mem aw sOff aOff
    let propOff := sOff + ⟨64⟩
    RDx runtimeBytecode ee g s0 ⟨7706⟩
      (⟨7725⟩ :: carry :: carry :: propOff :: propOff ::
        aOff :: s2 :: s6 :: s3 :: s4 :: tail)
      (sosDiagonalMemory mem aw sOff aOff) (sosDiagonalAw aw sOff aOff)
      rdata acc (k + 66) (C + sosDiagonalGas aw sOff aOff) := by
  have rd := GeneratedTraces.trace_7636_body hdepth h
  simpa [sosDiagonalAi, sosDiagonalAw1, sosDiagonalLowPrior, sosDiagonalAw2,
    sosDiagonalLow, sosDiagonalLowCarry, sosDiagonalMemory1, sosDiagonalAw3,
    sosDiagonalHighPrior, sosDiagonalAw4, sosDiagonalHigh1, sosDiagonalHighCarry1,
    sosDiagonalHigh, sosDiagonalHighCarry2, sosDiagonalCarry, sosDiagonalMemory,
    sosDiagonalAw, sosDiagonalGas, readWord, readWords1, evmMulHigh,
    lnotZero_eq_max, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-! ## Carry propagation shared by diagonal addition -/

def sosPropagateWord (mem : ByteArray) (aw ptr : UInt256) : UInt256 :=
  readWord mem aw ptr

def sosPropagateValue (mem : ByteArray) (aw ptr carry : UInt256) : UInt256 :=
  sosPropagateWord mem aw ptr + carry

def sosPropagateCarry (mem : ByteArray) (aw ptr carry : UInt256) : UInt256 :=
  (sosPropagateValue mem aw ptr carry).lt (sosPropagateWord mem aw ptr)

def sosPropagateMemory (mem : ByteArray) (aw ptr carry : UInt256) : ByteArray :=
  (sosPropagateValue mem aw ptr carry).toByteArray.write 0 mem ptr.toNat 32

def sosPropagateAw1 (aw ptr : UInt256) : UInt256 := readWords1 aw ptr

def sosPropagateAw (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (sosPropagateAw1 aw ptr).toNat ptr.toNat 32)

def sosPropagateGas (aw ptr : UInt256) : Nat :=
  64 + (Cₘ (sosPropagateAw1 aw ptr) - Cₘ aw) +
    (Cₘ (sosPropagateAw aw ptr) - Cₘ (sosPropagateAw1 aw ptr))

/-- The EVM overflow flag emitted by carry propagation is its exact unbounded carry. -/
theorem sosPropagate_recompose (mem : ByteArray) (aw ptr carry : UInt256) :
    (sosPropagateValue mem aw ptr carry).toNat +
        UInt256.size * (sosPropagateCarry mem aw ptr carry).toNat =
      (sosPropagateWord mem aw ptr).toNat + carry.toNat := by
  exact evmAddCarry_recompose (sosPropagateWord mem aw ptr) carry

/-- One generated carry-propagation word, including its next loop condition and exact gas. -/
theorem sosPropagateBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {carry ptr : UInt256}
    (hdepth : tail.length + 2 ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨7725⟩
      (carry :: ptr :: tail) mem aw rdata acc k C) :
    let carry' := sosPropagateCarry mem aw ptr carry
    RDx runtimeBytecode ee g s0 ⟨7706⟩
      (⟨7725⟩ :: carry' :: carry' :: (ptr + ⟨32⟩) :: tail)
      (sosPropagateMemory mem aw ptr carry) (sosPropagateAw aw ptr)
      rdata acc (k + 21) (C + sosPropagateGas aw ptr) := by
  have rd := GeneratedTraces.trace_7725_body hdepth h
  simpa [sosPropagateWord, sosPropagateValue, sosPropagateCarry,
    sosPropagateMemory, sosPropagateAw1, sosPropagateAw, sosPropagateGas,
    readWord, readWords1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

structure SOSPropagateState where
  carry : UInt256
  ptr : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosPropagateAdvance (s : SOSPropagateState) : SOSPropagateState where
  carry := sosPropagateCarry s.memory s.activeWords s.ptr s.carry
  ptr := s.ptr + ⟨32⟩
  memory := sosPropagateMemory s.memory s.activeWords s.ptr s.carry
  activeWords := sosPropagateAw s.activeWords s.ptr

def sosPropagateIterate : Nat → SOSPropagateState → SOSPropagateState
  | 0, s => s
  | n + 1, s => sosPropagateIterate n (sosPropagateAdvance s)

def sosPropagateIterationsGas : Nat → SOSPropagateState → Nat
  | 0, _ => 0
  | n + 1, s => sosPropagateGas s.activeWords s.ptr + 10 +
      sosPropagateIterationsGas n (sosPropagateAdvance s)

@[simp] theorem sosPropagateIterate_advance (n : Nat) (s : SOSPropagateState) :
    sosPropagateIterate n (sosPropagateAdvance s) =
      sosPropagateIterate (n + 1) s := by
  rfl

/-- Execute any finite run of nonzero carry propagation. -/
theorem sosPropagateIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    (state : SOSPropagateState)
    (hdepth : tail.length + 2 ≤ 1020)
    (hcontinue : ∀ j, j < n →
      (sosPropagateAdvance (sosPropagateIterate j state)).carry ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7725⟩
      (state.carry :: state.ptr :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7725⟩
      ((sosPropagateIterate n state).carry ::
        (sosPropagateIterate n state).ptr :: tail)
      (sosPropagateIterate n state).memory
      (sosPropagateIterate n state).activeWords rdata acc
      (k + 22 * n) (C + sosPropagateIterationsGas n state) := by
  induction n generalizing state k C with
  | zero => simpa [sosPropagateIterate, sosPropagateIterationsGas]
  | succ n ih =>
      have rd7713 := sosPropagateBody hdepth h
      have rdNext := rd7713.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (sosPropagateAdvance
            (sosPropagateIterate j (sosPropagateAdvance state))).carry ≠ ⟨0⟩ := by
        intro j hj
        simpa [sosPropagateIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := sosPropagateAdvance state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 22 * (n + 1)) (by omega) rfl
      simpa [sosPropagateIterate, sosPropagateAdvance, sosPropagateIterationsGas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

def sosPropagateThroughExitGas (n : Nat) (state : SOSPropagateState) : Nat :=
  sosPropagateIterationsGas n state +
    sosPropagateGas (sosPropagateIterate n state).activeWords
      (sosPropagateIterate n state).ptr + 10

/-- Execute nonzero carry words and the final word whose carry becomes zero at PC 7707. -/
theorem sosPropagateThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    (state : SOSPropagateState)
    (hdepth : tail.length + 2 ≤ 1020)
    (hcontinue : ∀ j, j < n →
      (sosPropagateAdvance (sosPropagateIterate j state)).carry ≠ ⟨0⟩)
    (hexit : (sosPropagateAdvance (sosPropagateIterate n state)).carry = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7725⟩
      (state.carry :: state.ptr :: tail)
      state.memory state.activeWords rdata acc k C) :
    let final := sosPropagateAdvance (sosPropagateIterate n state)
    RDx runtimeBytecode ee g s0 ⟨7707⟩
      (final.carry :: final.ptr :: tail)
      final.memory final.activeWords rdata acc
      (k + 22 * (n + 1)) (C + sosPropagateThroughExitGas n state) := by
  have rdIterations := sosPropagateIterations state hdepth hcontinue h
  have rdBody := sosPropagateBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 22 * (n + 1)) (by omega) rfl
  simpa [sosPropagateAdvance, sosPropagateThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-! ## SOS reduction pass -/

def sosPeeledValue (mem : ByteArray) (aw sBase : UInt256) : UInt256 :=
  readWord mem aw sBase

def sosPeeledAw1 (aw sBase : UInt256) : UInt256 := readWords1 aw sBase

def sosPeeledN0 (mem : ByteArray) (aw sBase nP : UInt256) : UInt256 :=
  readWord mem (sosPeeledAw1 aw sBase) nP

def sosPeeledAw (aw sBase nP : UInt256) : UInt256 :=
  readWords1 (sosPeeledAw1 aw sBase) nP

def sosPeeledFactor (mem : ByteArray) (aw sBase n0inv : UInt256) : UInt256 :=
  UInt256.mul (sosPeeledValue mem aw sBase) n0inv

def sosPeeledCarry
    (mem : ByteArray) (aw sBase nP n0inv : UInt256) : UInt256 :=
  let m := sosPeeledFactor mem aw sBase n0inv
  let n0 := sosPeeledN0 mem aw sBase nP
  let low := UInt256.mul m n0
  evmMulHigh m n0 + (low + sosPeeledValue mem aw sBase).lt low

def sosPeeledGas (aw sBase nP : UInt256) : Nat :=
  let aw1 := sosPeeledAw1 aw sBase
  let aw2 := sosPeeledAw aw sBase nP
  144 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1)

/-- The peeled low reduction column is an exact unbounded radix quotient column. -/
theorem sosPeeled_recompose
    (mem : ByteArray) (aw sBase nP n0inv : UInt256)
    (hinv :
      (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat % UInt256.size =
        UInt256.size - 1) :
    UInt256.size * (sosPeeledCarry mem aw sBase nP n0inv).toNat =
      (sosPeeledValue mem aw sBase).toNat +
        (sosPeeledFactor mem aw sBase n0inv).toNat *
          (sosPeeledN0 mem aw sBase nP).toNat := by
  simpa only [sosPeeledCarry, sosPeeledFactor] using
    evmMontgomeryPeeled_recompose
      (sosPeeledValue mem aw sBase) (sosPeeledN0 mem aw sBase nP) n0inv hinv

/-- Compute `m`, cancel the low scratch limb, and enter the remaining reduction columns. -/
theorem sosPeeledBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {n0inv nBefore s2 sBase s4 nEnd s6 nP : UInt256}
    (hdepth : tail.length + 8 ≤ 1018)
    (h : RDx runtimeBytecode ee g s0 ⟨7486⟩
      (n0inv :: nBefore :: s2 :: sBase :: s4 :: nEnd :: s6 :: nP :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7537⟩
      (⟨7581⟩ :: (nBefore + ⟨64⟩).lt nEnd :: (nBefore + ⟨64⟩) ::
        sosPeeledFactor mem aw sBase n0inv ::
        sosPeeledCarry mem aw sBase nP n0inv :: (sBase + ⟨32⟩) ::
        sBase :: n0inv :: nBefore :: s2 :: nEnd :: s6 :: nP :: tail)
      mem (sosPeeledAw aw sBase nP) rdata acc
      (k + 47) (C + sosPeeledGas aw sBase nP) := by
  have rd := GeneratedTraces.trace_7486_body hdepth h
  simpa [sosPeeledValue, sosPeeledAw1, sosPeeledN0, sosPeeledAw,
    sosPeeledFactor, sosPeeledCarry, sosPeeledGas, readWord, readWords1,
    evmMulHigh, lnotZero_eq_max,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- The reduction phase uses the same exact propagation recurrence at a second bytecode loop. -/
theorem sosReductionPropagateBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {carry ptr : UInt256}
    (hdepth : tail.length + 2 ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨7559⟩
      (carry :: ptr :: tail) mem aw rdata acc k C) :
    let carry' := sosPropagateCarry mem aw ptr carry
    RDx runtimeBytecode ee g s0 ⟨7545⟩
      (⟨7559⟩ :: carry' :: carry' :: (ptr + ⟨32⟩) :: tail)
      (sosPropagateMemory mem aw ptr carry) (sosPropagateAw aw ptr)
      rdata acc (k + 21) (C + sosPropagateGas aw ptr) := by
  have rd := GeneratedTraces.trace_7559_body hdepth h
  simpa [sosPropagateWord, sosPropagateValue, sosPropagateCarry,
    sosPropagateMemory, sosPropagateAw1, sosPropagateAw, sosPropagateGas,
    readWord, readWords1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- Execute any finite run of nonzero reduction carry propagation. -/
theorem sosReductionPropagateIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    (state : SOSPropagateState)
    (hdepth : tail.length + 2 ≤ 1020)
    (hcontinue : ∀ j, j < n →
      (sosPropagateAdvance (sosPropagateIterate j state)).carry ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7559⟩
      (state.carry :: state.ptr :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7559⟩
      ((sosPropagateIterate n state).carry ::
        (sosPropagateIterate n state).ptr :: tail)
      (sosPropagateIterate n state).memory
      (sosPropagateIterate n state).activeWords rdata acc
      (k + 22 * n) (C + sosPropagateIterationsGas n state) := by
  induction n generalizing state k C with
  | zero => simpa [sosPropagateIterate, sosPropagateIterationsGas]
  | succ n ih =>
      have rd7552 := sosReductionPropagateBody hdepth h
      have rdNext := rd7552.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (sosPropagateAdvance
            (sosPropagateIterate j (sosPropagateAdvance state))).carry ≠ ⟨0⟩ := by
        intro j hj
        simpa [sosPropagateIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := sosPropagateAdvance state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 22 * (n + 1)) (by omega) rfl
      simpa [sosPropagateIterate, sosPropagateAdvance, sosPropagateIterationsGas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-- Execute reduction carry words through the final zero carry at PC 7546. -/
theorem sosReductionPropagateThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    (state : SOSPropagateState)
    (hdepth : tail.length + 2 ≤ 1020)
    (hcontinue : ∀ j, j < n →
      (sosPropagateAdvance (sosPropagateIterate j state)).carry ≠ ⟨0⟩)
    (hexit : (sosPropagateAdvance (sosPropagateIterate n state)).carry = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7559⟩
      (state.carry :: state.ptr :: tail)
      state.memory state.activeWords rdata acc k C) :
    let final := sosPropagateAdvance (sosPropagateIterate n state)
    RDx runtimeBytecode ee g s0 ⟨7546⟩
      (final.carry :: final.ptr :: tail)
      final.memory final.activeWords rdata acc
      (k + 22 * (n + 1)) (C + sosPropagateThroughExitGas n state) := by
  have rdIterations := sosReductionPropagateIterations state hdepth hcontinue h
  have rdBody := sosReductionPropagateBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 22 * (n + 1)) (by omega) rfl
  simpa [sosPropagateAdvance, sosPropagateThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-- With no upper carry, skip propagation and advance the SOS reduction outer pointer. -/
theorem sosReductionBoundaryNoCarry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {modulusPtr factor resultPtr sBase x3 x4 sKEnd nEnd x7 nP x9 : UInt256}
    (hdepth : tail.length + 12 ≤ 1022)
    (h : RDx runtimeBytecode ee g s0 ⟨7538⟩
      (modulusPtr :: factor :: ⟨0⟩ :: resultPtr :: sBase :: x3 :: x4 :: sKEnd ::
        nEnd :: x7 :: nP :: x9 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7328⟩
      (⟨7486⟩ :: (⟨32⟩ + sBase).lt sKEnd :: x3 :: x4 :: sKEnd ::
        (⟨32⟩ + sBase) :: x9 :: nEnd :: x7 :: nP :: x9 :: tail)
      mem aw rdata acc (k + 21) (C + 67) := by
  have rd7552 := GeneratedTraces.trace_7538_body
    (tail := resultPtr :: sBase :: x3 :: x4 :: sKEnd :: nEnd :: x7 :: nP :: x9 :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd7553 := rd7552.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons]; omega)
  have rd7335 := GeneratedTraces.trace_7546_body
    (tail := tail) (by omega) rd7553
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7335

/-- Propagate a nonzero upper carry through any number of scratch words, then advance the outer
reduction pointer. -/
theorem sosReductionBoundaryWithCarry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {modulusPtr factor carry resultPtr sBase x3 x4 sKEnd nEnd x7 nP x9 : UInt256}
    (hdepth : tail.length + 12 ≤ 1022)
    (hcarry : carry ≠ ⟨0⟩)
    (hcontinue : ∀ j, j < n →
      (sosPropagateAdvance (sosPropagateIterate j
        { carry := carry, ptr := resultPtr, memory := mem, activeWords := aw })).carry ≠ ⟨0⟩)
    (hexit :
      (sosPropagateAdvance (sosPropagateIterate n
        { carry := carry, ptr := resultPtr, memory := mem, activeWords := aw })).carry = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7538⟩
      (modulusPtr :: factor :: carry :: resultPtr :: sBase :: x3 :: x4 :: sKEnd ::
        nEnd :: x7 :: nP :: x9 :: tail)
      mem aw rdata acc k C) :
    let state : SOSPropagateState :=
      { carry := carry, ptr := resultPtr, memory := mem, activeWords := aw }
    let final := sosPropagateAdvance (sosPropagateIterate n state)
    RDx runtimeBytecode ee g s0 ⟨7328⟩
      (⟨7486⟩ :: (⟨32⟩ + sBase).lt sKEnd :: x3 :: x4 :: sKEnd ::
        (⟨32⟩ + sBase) :: x9 :: nEnd :: x7 :: nP :: x9 :: tail)
      final.memory final.activeWords rdata acc
      (k + 21 + 22 * (n + 1))
      (C + 67 + sosPropagateThroughExitGas n state) := by
  let state : SOSPropagateState :=
    { carry := carry, ptr := resultPtr, memory := mem, activeWords := aw }
  have rd7552 := GeneratedTraces.trace_7538_body
    (tail := resultPtr :: sBase :: x3 :: x4 :: sKEnd :: nEnd :: x7 :: nP :: x9 :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd7566 := rd7552.jumpiT (by native_decide) hcarry
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd7553 := sosReductionPropagateThroughExit
    (tail := sBase :: x3 :: x4 :: sKEnd :: nEnd :: x7 :: nP :: x9 :: tail) state
    (by simp only [List.length_cons]; omega) hcontinue hexit (by
      simpa [state] using rd7566)
  have rd7335 := GeneratedTraces.trace_7546_body
    (tail := tail) (by omega) rd7553
  have normalized := rd7335.withIndices
    (k' := k + 21 + 22 * (n + 1)) (by omega) rfl
  have hgas :
      46 + (11 + C + 10 + sosPropagateThroughExitGas n state) =
        C + 67 + sosPropagateThroughExitGas n state := by
    omega
  rw [hgas] at normalized
  exact normalized

def sosReductionMemory
    (mem : ByteArray) (aw modulusPtr resultPtr factor carry : UInt256) : ByteArray :=
  multiplyPassMemory mem aw modulusPtr resultPtr factor carry

def sosReductionAw (aw modulusPtr resultPtr : UInt256) : UInt256 :=
  multiplyPassAw aw modulusPtr resultPtr

def sosReductionGas (aw modulusPtr resultPtr : UInt256) : Nat :=
  let aw1 := readWords1 aw modulusPtr
  let aw2 := readWords1 aw1 resultPtr
  let aw3 := sosReductionAw aw modulusPtr resultPtr
  178 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)

/-- One generated non-peeled SOS Montgomery reduction column. -/
theorem sosReductionBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {modulusPtr factor carry resultPtr s4 s5 s6 s7 stop : UInt256}
    (hdepth : tail.length + 9 ≤ 1015)
    (h : RDx runtimeBytecode ee g s0 ⟨7581⟩
      (modulusPtr :: factor :: carry :: resultPtr :: s4 :: s5 :: s6 :: s7 :: stop :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7537⟩
      (⟨7581⟩ :: (modulusPtr + ⟨32⟩).lt stop :: (modulusPtr + ⟨32⟩) ::
        factor :: (schoolbookStep mem aw modulusPtr resultPtr factor carry).2 ::
        (resultPtr + ⟨32⟩) :: s4 :: s5 :: s6 :: s7 :: stop :: tail)
      (sosReductionMemory mem aw modulusPtr resultPtr factor carry)
      (sosReductionAw aw modulusPtr resultPtr)
      rdata acc (k + 57) (C + sosReductionGas aw modulusPtr resultPtr) := by
  have rd := GeneratedTraces.trace_7581_body hdepth h
  simpa [schoolbookStep, schoolbookOperands, sosReductionMemory, sosReductionAw,
    sosReductionGas, multiplyPassMemory, multiplyPassAw, readWord, readWords1,
    evmSchoolbookStep, evmMulHigh, lnotZero_eq_max,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

structure SOSReductionState where
  modulusPtr : UInt256
  resultPtr : UInt256
  carry : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosReductionAdvance (factor : UInt256)
    (s : SOSReductionState) : SOSReductionState where
  modulusPtr := s.modulusPtr + ⟨32⟩
  resultPtr := s.resultPtr + ⟨32⟩
  carry := (schoolbookStep s.memory s.activeWords s.modulusPtr s.resultPtr factor s.carry).2
  memory := sosReductionMemory s.memory s.activeWords s.modulusPtr s.resultPtr factor s.carry
  activeWords := sosReductionAw s.activeWords s.modulusPtr s.resultPtr

def sosReductionIterate (factor : UInt256) : Nat → SOSReductionState → SOSReductionState
  | 0, s => s
  | n + 1, s => sosReductionIterate factor n (sosReductionAdvance factor s)

def sosReductionIterationsGas (factor : UInt256) : Nat → SOSReductionState → Nat
  | 0, _ => 0
  | n + 1, s => sosReductionGas s.activeWords s.modulusPtr s.resultPtr + 10 +
      sosReductionIterationsGas factor n (sosReductionAdvance factor s)

def sosReductionStack (s : SOSReductionState) (factor : UInt256)
    (fixed : List UInt256) : List UInt256 :=
  s.modulusPtr :: factor :: s.carry :: s.resultPtr :: fixed

@[simp] theorem sosReductionIterate_advance (factor : UInt256) (n : Nat)
    (s : SOSReductionState) :
    sosReductionIterate factor n (sosReductionAdvance factor s) =
      sosReductionIterate factor (n + 1) s := by
  rfl

/-- Execute any finite number of generated SOS reduction columns whose guard continues. -/
theorem sosReductionIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {factor s4 s5 s6 s7 stop : UInt256}
    (state : SOSReductionState)
    (hdepth : tail.length + 9 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (sosReductionAdvance factor
        (sosReductionIterate factor j state)).modulusPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7581⟩
      (sosReductionStack state factor (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7581⟩
      (sosReductionStack (sosReductionIterate factor n state) factor
        (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      (sosReductionIterate factor n state).memory
      (sosReductionIterate factor n state).activeWords rdata acc
      (k + 58 * n) (C + sosReductionIterationsGas factor n state) := by
  induction n generalizing state k C with
  | zero => simpa [sosReductionIterate, sosReductionIterationsGas]
  | succ n ih =>
      have rd7544 := sosReductionBody hdepth h
      have rdNext := rd7544.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (sosReductionAdvance factor
            (sosReductionIterate factor j
              (sosReductionAdvance factor state))).modulusPtr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [sosReductionIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := sosReductionAdvance factor state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 58 * (n + 1)) (by omega) rfl
      simpa [sosReductionStack, sosReductionIterate, sosReductionAdvance,
        sosReductionIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using normalized

def sosReductionThroughExitGas
    (factor : UInt256) (n : Nat) (state : SOSReductionState) : Nat :=
  sosReductionIterationsGas factor n state +
    sosReductionGas (sosReductionIterate factor n state).activeWords
      (sosReductionIterate factor n state).modulusPtr
      (sosReductionIterate factor n state).resultPtr + 10

/-- Execute the continuing SOS reduction columns and the final column that exits at PC 7545. -/
theorem sosReductionThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {factor s4 s5 s6 s7 stop : UInt256}
    (state : SOSReductionState)
    (hdepth : tail.length + 9 ≤ 1015)
    (hcontinue : ∀ j, j < n →
      (sosReductionAdvance factor
        (sosReductionIterate factor j state)).modulusPtr.lt stop ≠ ⟨0⟩)
    (hexit :
      (sosReductionAdvance factor
        (sosReductionIterate factor n state)).modulusPtr.lt stop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7581⟩
      (sosReductionStack state factor (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    let final := sosReductionAdvance factor (sosReductionIterate factor n state)
    RDx runtimeBytecode ee g s0 ⟨7538⟩
      (sosReductionStack final factor (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      final.memory final.activeWords rdata acc
      (k + 58 * (n + 1)) (C + sosReductionThroughExitGas factor n state) := by
  have rdIterations := sosReductionIterations state hdepth hcontinue h
  have rdBody := sosReductionBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 58 * (n + 1)) (by omega) rfl
  simpa [sosReductionStack, sosReductionAdvance, sosReductionThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

end Modexp.MultiLimbMontgomerySOSTrace
