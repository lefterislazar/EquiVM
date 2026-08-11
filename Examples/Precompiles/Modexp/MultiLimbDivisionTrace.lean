import Examples.Precompiles.Modexp.GeneratedTraces
import Examples.Precompiles.Modexp.MultiLimbArithmeticModel
import Examples.Precompiles.Modexp.MultiLimbMemoryModel
import Examples.Precompiles.Modexp.MultiLimbSubtractionModel

/-!
# Generated Knuth q-hat refinement segment

The generated segment at PC 8475 computes `qHat * vSecond` as a full two-word product and compares
it with `(rHat, uSecond)`.  The arithmetic bridge below turns that word-level branch condition into
the unbounded inequality used by Knuth Algorithm D.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbDivisionTrace

open Modexp.MultiLimbMemoryModel

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

def qhatNeedsRefinement
    (qHat rHat vSecond uSecond : UInt256) : UInt256 :=
  let high := evmMulHigh qHat vSecond
  let low := UInt256.mul qHat vSecond
  UInt256.lor (UInt256.gt high rHat)
    (UInt256.land (UInt256.eq high rHat) (UInt256.gt low uSecond))

private theorem lnotZero_eq_max :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

/-- SymCheck's generated 34-opcode product-and-compare block, with exact gas. -/
theorem qhatCompareBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {qHat rHat vTop vSecond uSecond : UInt256}
    (hdepth : tail.length + 5 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨8475⟩
      (qHat :: rHat :: vTop :: vSecond :: uSecond :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8511⟩
      (⟨8519⟩ :: qhatNeedsRefinement qHat rHat vSecond uSecond ::
        vTop :: vSecond :: uSecond :: rHat :: qHat :: tail)
      mem aw rdata acc (k + 34) (C + 104) := by
  have rd := GeneratedTraces.trace_8475_body hdepth h
  simpa [qhatNeedsRefinement, evmMulHigh, lnotZero_eq_max, Nat.add_comm] using rd

private theorem eq_zero_of_ne {a b : UInt256} (h : a ≠ b) : UInt256.eq a b = ⟨0⟩ := by
  apply uInt256_eq_zero_of_ne
  intro hone
  exact h (uInt256_eq_one_eq hone)

private theorem land_zero_left (x : UInt256) : UInt256.land ⟨0⟩ x = ⟨0⟩ := by
  apply u256_inj
  rw [u256_land_toNat]
  change Nat.land 0 x.toNat % UInt256.size = 0
  have hland : Nat.land 0 x.toNat = 0 := by
    rw [nat_land_comm]
    exact Nat.eq_zero_of_le_zero (nat_land_le_right x.toNat 0)
  rw [hland]
  rfl

private theorem lor_zero_left (x : UInt256) : UInt256.lor ⟨0⟩ x = x := by
  rw [u256_lor_comm]
  exact u256_lor_zero x

private theorem trueCondition :
    UInt256.lor ⟨0⟩ (UInt256.land ⟨1⟩ ⟨1⟩) = ⟨1⟩ := by
  native_decide

/-- The generated branch condition is nonzero exactly when Knuth's q-hat estimate must be
decremented. -/
theorem qhatNeedsRefinement_iff
    (qHat rHat vSecond uSecond : UInt256) :
    qhatNeedsRefinement qHat rHat vSecond uSecond ≠ ⟨0⟩ ↔
      rHat.toNat * UInt256.size + uSecond.toNat < qHat.toNat * vSecond.toNat := by
  rw [← Modexp.evmMulHigh_lex_gt_iff qHat vSecond rHat uSecond]
  let high := evmMulHigh qHat vSecond
  let low := UInt256.mul qHat vSecond
  unfold qhatNeedsRefinement
  change UInt256.lor (UInt256.gt high rHat)
      (UInt256.land (UInt256.eq high rHat) (UInt256.gt low uSecond)) ≠ ⟨0⟩ ↔
    rHat.toNat < high.toNat ∨
      rHat.toNat = high.toNat ∧ uSecond.toNat < low.toNat
  by_cases hhi : rHat.toNat < high.toNat
  · have hgt : UInt256.gt high rHat = ⟨1⟩ := ugt_one hhi
    have hne : high ≠ rHat := by
      intro heq
      have := congrArg UInt256.toNat heq
      omega
    have heq : UInt256.eq high rHat = ⟨0⟩ := eq_zero_of_ne hne
    rw [hgt, heq]
    rw [land_zero_left, u256_lor_zero]
    constructor
    · intro _
      exact Or.inl hhi
    · intro _
      decide
  · have hle : high.toNat ≤ rHat.toNat := by omega
    have hgt : UInt256.gt high rHat = ⟨0⟩ := ugt_zero hle
    by_cases heqNat : rHat.toNat = high.toNat
    · have heqWord : high = rHat := u256_inj heqNat.symm
      have heq : UInt256.eq high rHat = ⟨1⟩ := by simpa [heqWord] using uInt256_eq_self rHat
      by_cases hlo : uSecond.toNat < low.toNat
      · have hlowGt : UInt256.gt low uSecond = ⟨1⟩ := ugt_one hlo
        rw [hgt, heq, hlowGt]
        rw [trueCondition]
        constructor
        · intro _
          exact Or.inr ⟨heqNat, hlo⟩
        · intro _
          decide
      · have hlowGt : UInt256.gt low uSecond = ⟨0⟩ := ugt_zero (by omega)
        rw [hgt, heq, hlowGt]
        constructor
        · intro hzero
          exact (hzero rfl).elim
        · intro hcase
          rcases hcase with hcase | ⟨_, hcase⟩ <;> omega
    · have hne : high ≠ rHat := by
        intro heq
        apply heqNat
        exact congrArg UInt256.toNat heq.symm
      have heq : UInt256.eq high rHat = ⟨0⟩ := eq_zero_of_ne hne
      rw [hgt, heq]
      rw [land_zero_left, lor_zero_left]
      constructor
      · intro hzero
        exact (hzero rfl).elim
      · intro hcase
        rcases hcase with hcase | ⟨hcase, _⟩ <;> omega

def readWord (mem : ByteArray) (aw ptr : UInt256) : UInt256 :=
  if ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32))

def readWords1 (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def subtractionStep (mem : ByteArray) (aw leftPtr rightPtr borrow : UInt256) :
    UInt256 × UInt256 :=
  let left := readWord mem aw leftPtr
  let right := readWord mem (readWords1 aw leftPtr) rightPtr
  evmSubBorrow left right borrow

def subtractionMemory (mem : ByteArray) (aw leftPtr rightPtr borrow : UInt256) : ByteArray :=
  (subtractionStep mem aw leftPtr rightPtr borrow).1.toByteArray.write
    0 mem leftPtr.toNat 32

def subtractionAw (aw leftPtr rightPtr : UInt256) : UInt256 :=
  let aw1 := readWords1 aw leftPtr
  let aw2 := readWords1 aw1 rightPtr
  readWords1 aw2 leftPtr

def subtractionGas (aw leftPtr rightPtr : UInt256) : Nat :=
  let aw1 := readWords1 aw leftPtr
  let aw2 := readWords1 aw1 rightPtr
  let aw3 := subtractionAw aw leftPtr rightPtr
  103 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)

/-- SymCheck's generated subtraction-with-borrow memory body, including the next loop guard. -/
theorem subtractionBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {leftPtr borrow rightPtr stop : UInt256}
    (hdepth : tail.length + 4 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨7383⟩
      (leftPtr :: borrow :: rightPtr :: stop :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7377⟩
      (⟨7383⟩ :: (leftPtr + ⟨32⟩).lt stop :: (leftPtr + ⟨32⟩) ::
        (subtractionStep mem aw leftPtr rightPtr borrow).2 :: (rightPtr + ⟨32⟩) ::
        stop :: tail)
      (subtractionMemory mem aw leftPtr rightPtr borrow)
      (subtractionAw aw leftPtr rightPtr) rdata acc
      (k + 34) (C + subtractionGas aw leftPtr rightPtr) := by
  have rd := GeneratedTraces.trace_7383_body hdepth h
  simpa [subtractionStep, subtractionMemory, subtractionAw, subtractionGas,
    readWord, readWords1, evmSubBorrow, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- Arithmetic meaning of the exact digit and borrow emitted by `subtractionBody`. -/
theorem subtractionStep_recompose (mem : ByteArray)
    (aw leftPtr rightPtr borrow : UInt256)
    (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    let left := readWord mem aw leftPtr
    let right := readWord mem (readWords1 aw leftPtr) rightPtr
    let step := subtractionStep mem aw leftPtr rightPtr borrow
    step.1.toNat + right.toNat + borrow.toNat =
      left.toNat + UInt256.size * step.2.toNat := by
  dsimp only [subtractionStep]
  exact Modexp.evmSubBorrow_recompose _ _ _ hborrow

/-- The generated subtraction body stores exactly its arithmetic output digit. -/
theorem subtractionMemory_word
    (mem : ByteArray) (aw leftPtr rightPtr borrow : UInt256)
    (hgap : leftPtr.toNat - mem.size < USize.size) :
    memoryWordNat (subtractionMemory mem aw leftPtr rightPtr borrow) leftPtr.toNat =
      (subtractionStep mem aw leftPtr rightPtr borrow).1.toNat := by
  unfold subtractionMemory memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

structure SubtractionState where
  leftPtr : UInt256
  rightPtr : UInt256
  borrow : UInt256
  memory : ByteArray
  activeWords : UInt256

def subtractionAdvance (s : SubtractionState) : SubtractionState where
  leftPtr := s.leftPtr + ⟨32⟩
  rightPtr := s.rightPtr + ⟨32⟩
  borrow := (subtractionStep s.memory s.activeWords s.leftPtr s.rightPtr s.borrow).2
  memory := subtractionMemory s.memory s.activeWords s.leftPtr s.rightPtr s.borrow
  activeWords := subtractionAw s.activeWords s.leftPtr s.rightPtr

def subtractionIterate : Nat → SubtractionState → SubtractionState
  | 0, s => s
  | n + 1, s => subtractionIterate n (subtractionAdvance s)

def subtractionLeftWords : Nat → SubtractionState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      readWord state.memory state.activeWords state.leftPtr ::
      subtractionLeftWords n (subtractionAdvance state)

def subtractionRightWords : Nat → SubtractionState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      readWord state.memory (readWords1 state.activeWords state.leftPtr)
        state.rightPtr ::
      subtractionRightWords n (subtractionAdvance state)

def subtractionOutputWords : Nat → SubtractionState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (subtractionStep state.memory state.activeWords state.leftPtr
        state.rightPtr state.borrow).1 ::
      subtractionOutputWords n (subtractionAdvance state)

@[simp] theorem subtractionLeftWords_length (n : Nat) (state : SubtractionState) :
    (subtractionLeftWords n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [subtractionLeftWords, ih]

@[simp] theorem subtractionRightWords_length (n : Nat) (state : SubtractionState) :
    (subtractionRightWords n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [subtractionRightWords, ih]

/-- The words observed by the concrete evolving-memory loop are exactly the pure limbwise
subtraction, including the final borrow. -/
theorem subtractionCollectors_eq_subLimbs (n : Nat) (state : SubtractionState) :
    Modexp.evmSubLimbs (subtractionLeftWords n state)
      (subtractionRightWords n state) state.borrow =
      (subtractionOutputWords n state, (subtractionIterate n state).borrow) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [subtractionLeftWords, subtractionRightWords, subtractionOutputWords,
        Modexp.evmSubLimbs, subtractionIterate]
      let step := subtractionStep state.memory state.activeWords state.leftPtr
        state.rightPtr state.borrow
      change
        (step.1 ::
            (Modexp.evmSubLimbs
              (subtractionLeftWords n (subtractionAdvance state))
              (subtractionRightWords n (subtractionAdvance state)) step.2).1,
          (Modexp.evmSubLimbs
            (subtractionLeftWords n (subtractionAdvance state))
            (subtractionRightWords n (subtractionAdvance state)) step.2).2) =
        (step.1 :: subtractionOutputWords n (subtractionAdvance state),
          (subtractionIterate n (subtractionAdvance state)).borrow)
      have hborrow : step.2 = (subtractionAdvance state).borrow := by rfl
      rw [hborrow, ih (subtractionAdvance state)]

/-- Complete unbounded subtraction equation over every word loaded and stored by the trace. -/
theorem subtractionCollectors_recompose
    (n : Nat) (state : SubtractionState)
    (hborrow : state.borrow = ⟨0⟩ ∨ state.borrow = ⟨1⟩) :
    Modexp.wordLimbsToNat (subtractionOutputWords n state) +
        Modexp.wordLimbsToNat (subtractionRightWords n state) + state.borrow.toNat =
      Modexp.wordLimbsToNat (subtractionLeftWords n state) +
        UInt256.size ^ n * (subtractionIterate n state).borrow.toNat := by
  have hsub := Modexp.evmSubLimbs_recompose
    (subtractionLeftWords n state) (subtractionRightWords n state)
    state.borrow (by simp) hborrow
  rw [subtractionCollectors_eq_subLimbs] at hsub
  simpa using hsub

def subtractionIterationsGas : Nat → SubtractionState → Nat
  | 0, _ => 0
  | n + 1, s => subtractionGas s.activeWords s.leftPtr s.rightPtr + 10 +
      subtractionIterationsGas n (subtractionAdvance s)

def subtractionLoopStack (s : SubtractionState) (stop : UInt256)
    (tail : List UInt256) : List UInt256 :=
  s.leftPtr :: s.borrow :: s.rightPtr :: stop :: tail

@[simp] theorem subtractionIterate_advance (n : Nat) (s : SubtractionState) :
    subtractionIterate n (subtractionAdvance s) = subtractionIterate (n + 1) s := by
  rfl

/-- Execute any number of generated subtraction bodies whose loop guard continues. -/
theorem subtractionIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256} {stop : UInt256}
    (state : SubtractionState)
    (hdepth : tail.length + 4 ≤ 1017)
    (hcontinue : ∀ j, j < n →
      (subtractionAdvance (subtractionIterate j state)).leftPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7383⟩
      (subtractionLoopStack state stop tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7383⟩
      (subtractionLoopStack (subtractionIterate n state) stop tail)
      (subtractionIterate n state).memory
      (subtractionIterate n state).activeWords rdata acc
      (k + 35 * n) (C + subtractionIterationsGas n state) := by
  induction n generalizing state k C with
  | zero => simpa [subtractionIterate, subtractionIterationsGas]
  | succ n ih =>
      have rd7384 := subtractionBody hdepth h
      have rdNext := rd7384.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (subtractionAdvance
            (subtractionIterate j (subtractionAdvance state))).leftPtr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [subtractionIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := subtractionAdvance state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 35 * (n + 1)) (by omega) rfl
      simpa [subtractionLoopStack, subtractionIterate, subtractionAdvance,
        subtractionIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using normalized

end Modexp.MultiLimbDivisionTrace
