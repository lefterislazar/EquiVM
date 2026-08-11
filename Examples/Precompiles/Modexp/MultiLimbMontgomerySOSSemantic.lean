import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFull
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSModel

/-! # Semantic bridge for the executable SOS arithmetic body -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomerySOSFinalize

set_option maxRecDepth 50000
set_option maxHeartbeats 0

private theorem sosDoubleShiftLeft_toNat (word : UInt256) :
    (word.shiftLeft ⟨1⟩).toNat = 2 * (word.toNat % 2 ^ 255) := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨1⟩ : UInt256).val ≥ 256))]
  change (word.toNat <<< 1) % UInt256.size = _
  rw [Nat.shiftLeft_eq]
  norm_num
  rw [show UInt256.size = 2 * 2 ^ 255 by norm_num [UInt256.size]]
  simpa [Nat.mul_comm] using Nat.mul_mod_mul_left 2 word.toNat (2 ^ 255)

private theorem sosDoubleCarry_toNat (word : UInt256) :
    (word.shiftRight ⟨255⟩).toNat = word.toNat / 2 ^ 255 := by
  simpa using shiftRight_toNat_of_lt256 word ⟨255⟩ (by decide)

private theorem ult_toNat_le_one' (a b : UInt256) : (a.lt b).toNat ≤ 1 := by
  by_cases h : a.toNat < b.toNat
  · rw [ult_one h]
    decide
  · rw [ult_zero (by omega)]
    decide

/-- One generated doubling transition is exact unbounded multiplication by two. -/
theorem sosDoubleStep_recompose
    (mem : ByteArray) (aw ptr carry : UInt256) (hcarry : carry.toNat < 2) :
    (sosDoubleOutput mem aw ptr carry).toNat +
        UInt256.size * (sosDoubleCarry mem aw ptr).toNat =
      2 * (sosDoubleWord mem aw ptr).toNat + carry.toNat := by
  let word := sosDoubleWord mem aw ptr
  have hword : word.toNat < UInt256.size := word.val.isLt
  have hrem : word.toNat % 2 ^ 255 < 2 ^ 255 :=
    Nat.mod_lt _ (by positivity)
  have hshift : 2 * (word.toNat % 2 ^ 255) < UInt256.size := by
    rw [show UInt256.size = 2 * 2 ^ 255 by norm_num [UInt256.size]]
    omega
  have hor : Nat.lor carry.toNat (2 * (word.toNat % 2 ^ 255)) =
      carry.toNat + 2 * (word.toNat % 2 ^ 255) := by
    simpa [Nat.mul_comm] using nat_lor_shift_add carry.toNat
      (word.toNat % 2 ^ 255) 1 hcarry
  have horBound : carry.toNat + 2 * (word.toNat % 2 ^ 255) < UInt256.size := by
    rw [show UInt256.size = 2 * 2 ^ 255 by norm_num [UInt256.size]]
    omega
  have hdiv := Nat.mod_add_div word.toNat (2 ^ 255)
  unfold sosDoubleOutput sosDoubleCarry
  change (carry.lor (word.shiftLeft ⟨1⟩)).toNat +
      UInt256.size * (word.shiftRight ⟨255⟩).toNat =
        2 * word.toNat + carry.toNat
  rw [u256_lor_toNat, sosDoubleShiftLeft_toNat, sosDoubleCarry_toNat]
  change Nat.lor carry.toNat (2 * (word.toNat % 2 ^ 255)) % UInt256.size +
      UInt256.size * (word.toNat / 2 ^ 255) = _
  rw [hor, Nat.mod_eq_of_lt horBound]
  rw [show UInt256.size = 2 * 2 ^ 255 by norm_num [UInt256.size]]
  omega

def sosDoubleInputWords : Nat → SOSDoubleState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      sosDoubleWord state.memory state.activeWords state.ptr ::
        sosDoubleInputWords n (sosDoubleAdvance state)

def sosDoubleOutputWords : Nat → SOSDoubleState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      sosDoubleOutput state.memory state.activeWords state.ptr state.carry ::
        sosDoubleOutputWords n (sosDoubleAdvance state)

@[simp] theorem sosDoubleInputWords_length (n : Nat) (state : SOSDoubleState) :
    (sosDoubleInputWords n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosDoubleInputWords, ih]

@[simp] theorem sosDoubleOutputWords_length (n : Nat) (state : SOSDoubleState) :
    (sosDoubleOutputWords n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosDoubleOutputWords, ih]

/-- The generated doubling loop recomposes to twice the collected scratch value. -/
theorem sosDoubleCollectors_recompose
    (n : Nat) (state : SOSDoubleState) (hcarry : state.carry.toNat < 2) :
    Modexp.wordLimbsToNat (sosDoubleOutputWords n state) +
        UInt256.size ^ n * (sosDoubleIterate n state).carry.toNat =
      2 * Modexp.wordLimbsToNat (sosDoubleInputWords n state) + state.carry.toNat := by
  induction n generalizing state with
  | zero => simp [sosDoubleInputWords, sosDoubleOutputWords, sosDoubleIterate,
      Modexp.wordLimbsToNat]
  | succ n ih =>
      have hstep := sosDoubleStep_recompose state.memory state.activeWords state.ptr
        state.carry hcarry
      have hnextCarry : (sosDoubleAdvance state).carry.toNat < 2 := by
        dsimp only [sosDoubleAdvance]
        unfold sosDoubleCarry
        rw [sosDoubleCarry_toNat]
        have hword := (sosDoubleWord state.memory state.activeWords state.ptr).val.isLt
        have hword' :
            (sosDoubleWord state.memory state.activeWords state.ptr).toNat < 2 ^ 256 := by
          exact lt_of_lt_of_eq hword (by decide)
        omega
      have hrest := ih (sosDoubleAdvance state) hnextCarry
      simp only [sosDoubleInputWords, sosDoubleOutputWords, Modexp.wordLimbsToNat,
        sosDoubleIterate]
      let next := sosDoubleAdvance state
      change
        Modexp.wordLimbsToNat (sosDoubleOutputWords n next) +
            UInt256.size ^ n * (sosDoubleIterate n next).carry.toNat =
          2 * Modexp.wordLimbsToNat (sosDoubleInputWords n next) + next.carry.toNat
        at hrest
      change
        (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * Modexp.wordLimbsToNat (sosDoubleOutputWords n next) +
            UInt256.size ^ (n + 1) * (sosDoubleIterate n next).carry.toNat =
          2 * ((sosDoubleWord state.memory state.activeWords state.ptr).toNat +
            UInt256.size * Modexp.wordLimbsToNat (sosDoubleInputWords n next)) +
            state.carry.toNat
      calc
        _ = (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * (Modexp.wordLimbsToNat (sosDoubleOutputWords n next) +
              UInt256.size ^ n * (sosDoubleIterate n next).carry.toNat) := by
                rw [pow_succ]
                ring
        _ = (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * (2 * Modexp.wordLimbsToNat (sosDoubleInputWords n next) +
              next.carry.toNat) := by rw [hrest]
        _ = (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * (sosDoubleCarry state.memory state.activeWords state.ptr).toNat +
            2 * UInt256.size *
              Modexp.wordLimbsToNat (sosDoubleInputWords n next) := by
                change _ + UInt256.size * (_ +
                  (sosDoubleCarry state.memory state.activeWords state.ptr).toNat) = _
                ring
        _ = (2 * (sosDoubleWord state.memory state.activeWords state.ptr).toNat +
            state.carry.toNat) + 2 * UInt256.size *
              Modexp.wordLimbsToNat (sosDoubleInputWords n next) := by rw [hstep]
        _ = _ := by ring

/-! ## Shared carry propagation -/

def sosPropagateInputWords : Nat → SOSPropagateState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      sosPropagateWord state.memory state.activeWords state.ptr ::
        sosPropagateInputWords n (sosPropagateAdvance state)

def sosPropagateOutputWords : Nat → SOSPropagateState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      sosPropagateValue state.memory state.activeWords state.ptr state.carry ::
        sosPropagateOutputWords n (sosPropagateAdvance state)

@[simp] theorem sosPropagateInputWords_length (n : Nat) (state : SOSPropagateState) :
    (sosPropagateInputWords n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosPropagateInputWords, ih]

@[simp] theorem sosPropagateOutputWords_length (n : Nat) (state : SOSPropagateState) :
    (sosPropagateOutputWords n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosPropagateOutputWords, ih]

/-- Carry propagation adds the incoming carry to the collected little-endian word sequence. -/
theorem sosPropagateCollectors_recompose (n : Nat) (state : SOSPropagateState) :
    Modexp.wordLimbsToNat (sosPropagateOutputWords n state) +
        UInt256.size ^ n * (sosPropagateIterate n state).carry.toNat =
      Modexp.wordLimbsToNat (sosPropagateInputWords n state) + state.carry.toNat := by
  induction n generalizing state with
  | zero => simp [sosPropagateInputWords, sosPropagateOutputWords, sosPropagateIterate,
      Modexp.wordLimbsToNat]
  | succ n ih =>
      have hstep := sosPropagate_recompose state.memory state.activeWords state.ptr state.carry
      have hrest := ih (sosPropagateAdvance state)
      simp only [sosPropagateInputWords, sosPropagateOutputWords,
        Modexp.wordLimbsToNat, sosPropagateIterate]
      let next := sosPropagateAdvance state
      change
        Modexp.wordLimbsToNat (sosPropagateOutputWords n next) +
            UInt256.size ^ n * (sosPropagateIterate n next).carry.toNat =
          Modexp.wordLimbsToNat (sosPropagateInputWords n next) + next.carry.toNat
        at hrest
      change
        (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * Modexp.wordLimbsToNat (sosPropagateOutputWords n next) +
            UInt256.size ^ (n + 1) * (sosPropagateIterate n next).carry.toNat =
          (sosPropagateWord state.memory state.activeWords state.ptr).toNat +
            UInt256.size * Modexp.wordLimbsToNat (sosPropagateInputWords n next) +
            state.carry.toNat
      calc
        _ = (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * (Modexp.wordLimbsToNat (sosPropagateOutputWords n next) +
              UInt256.size ^ n * (sosPropagateIterate n next).carry.toNat) := by
                rw [pow_succ]
                ring
        _ = (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * (Modexp.wordLimbsToNat (sosPropagateInputWords n next) +
              next.carry.toNat) := by rw [hrest]
        _ = (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size *
              (sosPropagateCarry state.memory state.activeWords state.ptr state.carry).toNat +
            UInt256.size * Modexp.wordLimbsToNat
              (sosPropagateInputWords n next) := by
                change _ + UInt256.size * (_ +
                  (sosPropagateCarry state.memory state.activeWords state.ptr state.carry).toNat) = _
                ring
        _ = ((sosPropagateWord state.memory state.activeWords state.ptr).toNat +
            state.carry.toNat) + UInt256.size *
              Modexp.wordLimbsToNat (sosPropagateInputWords n next) := by rw [hstep]
        _ = _ := by ring

/-! ## Diagonal square addition -/

/-- One generated diagonal update adds the full unbounded square to two adjacent scratch limbs. -/
theorem sosDiagonal_recompose (mem : ByteArray) (aw sOff aOff : UInt256) :
    (sosDiagonalLow mem aw sOff aOff).toNat +
        UInt256.size * (sosDiagonalHigh mem aw sOff aOff).toNat +
        UInt256.size ^ 2 * (sosDiagonalCarry mem aw sOff aOff).toNat =
      (sosDiagonalLowPrior mem aw sOff aOff).toNat +
        UInt256.size * (sosDiagonalHighPrior mem aw sOff aOff).toNat +
        (sosDiagonalAi mem aw aOff).toNat ^ 2 := by
  let ai := sosDiagonalAi mem aw aOff
  let lowPrior := sosDiagonalLowPrior mem aw sOff aOff
  let highPrior := sosDiagonalHighPrior mem aw sOff aOff
  let lo := UInt256.mul ai ai
  let hi := evmMulHigh ai ai
  let low := lowPrior + lo
  let c1 := low.lt lowPrior
  let high1 := highPrior + hi
  let c2 := high1.lt highPrior
  let high := high1 + c1
  let c3 := high.lt high1
  have hmul := evmMulHigh_recompose ai ai
  have hlow := evmAddCarry_recompose lowPrior lo
  have hhigh1 := evmAddCarry_recompose highPrior hi
  have hhigh2 := evmAddCarry_recompose high1 c1
  have hc2 : c2.toNat ≤ 1 := ult_toNat_le_one' high1 highPrior
  have hc3 : c3.toNat ≤ 1 := ult_toNat_le_one' high high1
  have hcarryBound : c2.toNat + c3.toNat < UInt256.size := by
    have hsize : 2 < UInt256.size := by decide
    omega
  have hcarry : (c2 + c3).toNat = c2.toNat + c3.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hcarryBound]
  have heq :
      low.toNat + UInt256.size * high.toNat + UInt256.size ^ 2 * (c2 + c3).toNat =
        lowPrior.toNat + UInt256.size * highPrior.toNat + ai.toNat ^ 2 := by
    rw [hcarry]
    calc
      low.toNat + UInt256.size * high.toNat +
          UInt256.size ^ 2 * (c2.toNat + c3.toNat) =
        low.toNat + UInt256.size * (high.toNat + UInt256.size * c3.toNat) +
          UInt256.size ^ 2 * c2.toNat := by ring
      _ = low.toNat + UInt256.size * (high1.toNat + c1.toNat) +
          UInt256.size ^ 2 * c2.toNat := by rw [hhigh2]
      _ = (low.toNat + UInt256.size * c1.toNat) +
          UInt256.size * (high1.toNat + UInt256.size * c2.toNat) := by ring
      _ = (lowPrior.toNat + lo.toNat) +
          UInt256.size * (highPrior.toNat + hi.toNat) := by rw [hlow, hhigh1]
      _ = lowPrior.toNat + UInt256.size * highPrior.toNat +
          (lo.toNat + UInt256.size * hi.toNat) := by ring
      _ = lowPrior.toNat + UInt256.size * highPrior.toNat + ai.toNat ^ 2 := by
        rw [hmul]
        simp only [pow_two]
  simpa [ai, lowPrior, highPrior, lo, hi, low, c1, high1, c2, high, c3,
    sosDiagonalLow, sosDiagonalLowCarry, sosDiagonalHigh1,
    sosDiagonalHighCarry1, sosDiagonalHigh, sosDiagonalHighCarry2,
    sosDiagonalCarry] using heq

/-! ## Off-diagonal schoolbook rows -/

def sosOffDiagonalOperandWords (a : UInt256) : Nat → SOSOffDiagonalState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.operandPtr
        state.resultPtr state.carry).1 ::
      sosOffDiagonalOperandWords a n (sosOffDiagonalAdvance a state)

def sosOffDiagonalPriorWords (a : UInt256) : Nat → SOSOffDiagonalState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.operandPtr
        state.resultPtr state.carry).2.1 ::
      sosOffDiagonalPriorWords a n (sosOffDiagonalAdvance a state)

def sosOffDiagonalOutputWords (a : UInt256) : Nat → SOSOffDiagonalState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookStep state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry).1 ::
      sosOffDiagonalOutputWords a n (sosOffDiagonalAdvance a state)

@[simp] theorem sosOffDiagonalOperandWords_length
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    (sosOffDiagonalOperandWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosOffDiagonalOperandWords, ih]

@[simp] theorem sosOffDiagonalPriorWords_length
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    (sosOffDiagonalPriorWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosOffDiagonalPriorWords, ih]

/-- An SOS upper-triangle row is exactly the pure schoolbook-row operation. -/
theorem sosOffDiagonalCollectors_eq_row
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    Modexp.evmSchoolbookRow a
      (sosOffDiagonalOperandWords a n state)
      (sosOffDiagonalPriorWords a n state) state.carry =
      (sosOffDiagonalOutputWords a n state,
        (sosOffDiagonalIterate a n state).carry) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosOffDiagonalOperandWords, sosOffDiagonalPriorWords,
        sosOffDiagonalOutputWords, Modexp.evmSchoolbookRow,
        sosOffDiagonalIterate]
      let step := schoolbookStep state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry
      change
        (step.1 ::
            (Modexp.evmSchoolbookRow a
              (sosOffDiagonalOperandWords a n (sosOffDiagonalAdvance a state))
              (sosOffDiagonalPriorWords a n (sosOffDiagonalAdvance a state)) step.2).1,
          (Modexp.evmSchoolbookRow a
            (sosOffDiagonalOperandWords a n (sosOffDiagonalAdvance a state))
            (sosOffDiagonalPriorWords a n (sosOffDiagonalAdvance a state)) step.2).2) =
        (step.1 :: sosOffDiagonalOutputWords a n (sosOffDiagonalAdvance a state),
          (sosOffDiagonalIterate a n (sosOffDiagonalAdvance a state)).carry)
      have hcarry : step.2 = (sosOffDiagonalAdvance a state).carry := by rfl
      rw [hcarry, ih (sosOffDiagonalAdvance a state)]

/-- Every generated off-diagonal row satisfies the unbounded product-accumulation equation. -/
theorem sosOffDiagonalCollectors_recompose
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    Modexp.wordLimbsToNat (sosOffDiagonalOutputWords a n state) +
        UInt256.size ^ n * (sosOffDiagonalIterate a n state).carry.toNat =
      Modexp.wordLimbsToNat (sosOffDiagonalPriorWords a n state) +
        a.toNat * Modexp.wordLimbsToNat (sosOffDiagonalOperandWords a n state) +
        state.carry.toNat := by
  have hrow := Modexp.evmSchoolbookRow_recompose a
    (sosOffDiagonalOperandWords a n state)
    (sosOffDiagonalPriorWords a n state) state.carry
    (by simp)
  rw [sosOffDiagonalCollectors_eq_row] at hrow
  simpa using hrow

/-! ## Montgomery reduction columns -/

def sosReductionModulusWords (factor : UInt256) : Nat → SOSReductionState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.modulusPtr
        state.resultPtr state.carry).1 ::
      sosReductionModulusWords factor n (sosReductionAdvance factor state)

def sosReductionPriorWords (factor : UInt256) : Nat → SOSReductionState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookOperands state.memory state.activeWords state.modulusPtr
        state.resultPtr state.carry).2.1 ::
      sosReductionPriorWords factor n (sosReductionAdvance factor state)

def sosReductionOutputWords (factor : UInt256) : Nat → SOSReductionState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      (schoolbookStep state.memory state.activeWords state.modulusPtr
        state.resultPtr factor state.carry).1 ::
      sosReductionOutputWords factor n (sosReductionAdvance factor state)

@[simp] theorem sosReductionModulusWords_length
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    (sosReductionModulusWords factor n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosReductionModulusWords, ih]

@[simp] theorem sosReductionPriorWords_length
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    (sosReductionPriorWords factor n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosReductionPriorWords, ih]

theorem sosReductionCollectors_eq_row
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    Modexp.evmSchoolbookRow factor
      (sosReductionModulusWords factor n state)
      (sosReductionPriorWords factor n state) state.carry =
      (sosReductionOutputWords factor n state,
        (sosReductionIterate factor n state).carry) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosReductionModulusWords, sosReductionPriorWords,
        sosReductionOutputWords, Modexp.evmSchoolbookRow, sosReductionIterate]
      let step := schoolbookStep state.memory state.activeWords state.modulusPtr
        state.resultPtr factor state.carry
      change
        (step.1 ::
            (Modexp.evmSchoolbookRow factor
              (sosReductionModulusWords factor n (sosReductionAdvance factor state))
              (sosReductionPriorWords factor n (sosReductionAdvance factor state)) step.2).1,
          (Modexp.evmSchoolbookRow factor
            (sosReductionModulusWords factor n (sosReductionAdvance factor state))
            (sosReductionPriorWords factor n (sosReductionAdvance factor state)) step.2).2) =
        (step.1 :: sosReductionOutputWords factor n (sosReductionAdvance factor state),
          (sosReductionIterate factor n (sosReductionAdvance factor state)).carry)
      have hcarry : step.2 = (sosReductionAdvance factor state).carry := by rfl
      rw [hcarry, ih (sosReductionAdvance factor state)]

theorem sosReductionCollectors_recompose
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    Modexp.wordLimbsToNat (sosReductionOutputWords factor n state) +
        UInt256.size ^ n * (sosReductionIterate factor n state).carry.toNat =
      Modexp.wordLimbsToNat (sosReductionPriorWords factor n state) +
        factor.toNat * Modexp.wordLimbsToNat (sosReductionModulusWords factor n state) +
        state.carry.toNat := by
  have hrow := Modexp.evmSchoolbookRow_recompose factor
    (sosReductionModulusWords factor n state)
    (sosReductionPriorWords factor n state) state.carry
    (by simp)
  rw [sosReductionCollectors_eq_row] at hrow
  simpa using hrow

/-- The peeled cancellation and all remaining generated columns form one exact radix-scaled
Montgomery reduction equation. -/
theorem sosReductionPassColumns_recompose
    (mem : ByteArray) (aw sBase nP n0inv nBefore : UInt256) (n : Nat)
    (hinv : (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat % UInt256.size =
      UInt256.size - 1) :
    let factor := sosPeeledFactor mem aw sBase n0inv
    let initial := Modexp.MultiLimbMontgomerySOSLoop.sosReductionInitialState
      mem aw sBase nP n0inv nBefore
    UInt256.size *
        (Modexp.wordLimbsToNat (sosReductionOutputWords factor n initial) +
          UInt256.size ^ n * (sosReductionIterate factor n initial).carry.toNat) =
      (sosPeeledValue mem aw sBase).toNat +
        UInt256.size * Modexp.wordLimbsToNat (sosReductionPriorWords factor n initial) +
        factor.toNat *
          ((sosPeeledN0 mem aw sBase nP).toNat + UInt256.size *
            Modexp.wordLimbsToNat (sosReductionModulusWords factor n initial)) := by
  dsimp only
  let factor := sosPeeledFactor mem aw sBase n0inv
  let initial := Modexp.MultiLimbMontgomerySOSLoop.sosReductionInitialState
    mem aw sBase nP n0inv nBefore
  have hpeeled := sosPeeled_recompose mem aw sBase nP n0inv hinv
  have hcolumns := sosReductionCollectors_recompose factor n initial
  have hinitialCarry : initial.carry = sosPeeledCarry mem aw sBase nP n0inv := by rfl
  rw [hinitialCarry] at hcolumns
  calc
    UInt256.size *
        (Modexp.wordLimbsToNat (sosReductionOutputWords factor n initial) +
          UInt256.size ^ n * (sosReductionIterate factor n initial).carry.toNat) =
      UInt256.size *
        (Modexp.wordLimbsToNat (sosReductionPriorWords factor n initial) +
          factor.toNat * Modexp.wordLimbsToNat
            (sosReductionModulusWords factor n initial) +
          (sosPeeledCarry mem aw sBase nP n0inv).toNat) := by rw [hcolumns]
    _ = UInt256.size * Modexp.wordLimbsToNat
            (sosReductionPriorWords factor n initial) +
          UInt256.size * factor.toNat * Modexp.wordLimbsToNat
            (sosReductionModulusWords factor n initial) +
          UInt256.size * (sosPeeledCarry mem aw sBase nP n0inv).toNat := by ring
    _ = UInt256.size * Modexp.wordLimbsToNat
            (sosReductionPriorWords factor n initial) +
          UInt256.size * factor.toNat * Modexp.wordLimbsToNat
            (sosReductionModulusWords factor n initial) +
          ((sosPeeledValue mem aw sBase).toNat +
            factor.toNat * (sosPeeledN0 mem aw sBase nP).toNat) := by
              rw [hpeeled]
    _ = _ := by ring

/-! ## Selected final subtraction -/

def sosSubtractionSelectedState (selected : SOSSubtractionSelection) : SubtractionState where
  leftPtr := selected.leftPtr
  rightPtr := selected.rightPtr
  borrow := selected.borrow
  memory := selected.memory
  activeWords := selected.activeWords

/-- A successful executable subtraction selection is a positive number of pure subtraction
transitions over the same evolving memory. -/
theorem selectSOSSubtraction_eq_iterate
    {fuel : Nat} {stop : UInt256} {mem : ByteArray}
    {aw leftPtr borrow rightPtr : UInt256} {selected : SOSSubtractionSelection}
    (hselect : selectSOSSubtraction fuel stop mem aw leftPtr borrow rightPtr = some selected) :
    ∃ n, 0 < n ∧
      sosSubtractionSelectedState selected = subtractionIterate n {
        leftPtr := leftPtr
        rightPtr := rightPtr
        borrow := borrow
        memory := mem
        activeWords := aw } := by
  induction fuel generalizing mem aw leftPtr borrow rightPtr selected with
  | zero => simp [selectSOSSubtraction] at hselect
  | succ fuel ih =>
      simp only [selectSOSSubtraction] at hselect
      let step := subtractionStep mem aw leftPtr rightPtr borrow
      let nextLeft := leftPtr + ⟨32⟩
      let nextRight := rightPtr + ⟨32⟩
      let nextMem := subtractionMemory mem aw leftPtr rightPtr borrow
      let nextAw := subtractionAw aw leftPtr rightPtr
      let next : SubtractionState := {
        leftPtr := nextLeft
        rightPtr := nextRight
        borrow := step.2
        memory := nextMem
        activeWords := nextAw }
      by_cases hcontinue : nextLeft.lt stop ≠ ⟨0⟩
      · rw [if_pos hcontinue] at hselect
        cases hrest : selectSOSSubtraction fuel stop nextMem nextAw nextLeft step.2
            nextRight with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            obtain ⟨n, hn, hstate⟩ := ih hrest
            refine ⟨n + 1, by omega, ?_⟩
            change sosSubtractionSelectedState rest = subtractionIterate (n + 1) {
              leftPtr := leftPtr
              rightPtr := rightPtr
              borrow := borrow
              memory := mem
              activeWords := aw }
            simpa [subtractionIterate, subtractionAdvance, next, nextLeft, nextRight,
              nextMem, nextAw, step] using hstate
      · rw [if_neg hcontinue] at hselect
        injection hselect with heq
        subst selected
        refine ⟨1, by omega, ?_⟩
        rfl

end Modexp.MultiLimbMontgomerySOSSemantic
