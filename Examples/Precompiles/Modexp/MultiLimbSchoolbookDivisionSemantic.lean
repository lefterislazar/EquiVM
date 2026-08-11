import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisionContract
import Examples.Precompiles.Modexp.MultiLimbMultiplicationModel

/-!
# Arithmetic semantics of one Knuth quotient-digit subtraction

The bytecode propagates the high half of `qHat * v[i]` as `carry` while independently
propagating subtraction underflow as `borrow`.  This file combines those two word-level streams
into the unbounded radix equation used by Algorithm D.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookDivisionSemantic

set_option maxRecDepth 50000
set_option maxHeartbeats 0

structure KnuthSubtractResult where
  digits : List UInt256
  carry : UInt256
  borrow : UInt256

/-- Pure list form of the exact multiply-subtract body. -/
def knuthSubtractDigits (qHat : UInt256) :
    List UInt256 → List UInt256 → UInt256 → UInt256 → KnuthSubtractResult
  | [], _, carry, borrow => ⟨[], carry, borrow⟩
  | _ :: _, [], carry, borrow => ⟨[], carry, borrow⟩
  | uDigit :: uDigits, vDigit :: vDigits, carry, borrow =>
      let product := evmSchoolbookStep qHat vDigit ⟨0⟩ carry
      let subtraction := evmSubBorrow uDigit product.1 borrow
      let rest := knuthSubtractDigits qHat uDigits vDigits product.2 subtraction.2
      ⟨subtraction.1 :: rest.digits, rest.carry, rest.borrow⟩

theorem knuthSubtractDigits_length
    (qHat : UInt256) (uDigits vDigits : List UInt256) (carry borrow : UInt256)
    (hlength : uDigits.length = vDigits.length) :
    (knuthSubtractDigits qHat uDigits vDigits carry borrow).digits.length =
      uDigits.length := by
  induction uDigits generalizing vDigits carry borrow with
  | nil => simp [knuthSubtractDigits]
  | cons uDigit uDigits ih =>
      cases vDigits with
      | nil => simp at hlength
      | cons vDigit vDigits =>
          have htail : uDigits.length = vDigits.length := by
            simp only [List.length_cons] at hlength
            exact Nat.add_right_cancel hlength
          simp only [knuthSubtractDigits, List.length_cons]
          rw [ih vDigits _ _ htail]

theorem knuthSubtractDigits_borrow_bit
    (qHat : UInt256) (uDigits vDigits : List UInt256) (carry borrow : UInt256)
    (hlength : uDigits.length = vDigits.length)
    (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    let result := knuthSubtractDigits qHat uDigits vDigits carry borrow
    result.borrow = ⟨0⟩ ∨ result.borrow = ⟨1⟩ := by
  induction uDigits generalizing vDigits carry borrow with
  | nil =>
      have hv : vDigits = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst vDigits
      simpa [knuthSubtractDigits] using hborrow
  | cons uDigit uDigits ih =>
      cases vDigits with
      | nil => simp at hlength
      | cons vDigit vDigits =>
          have htail : uDigits.length = vDigits.length := by
            simp only [List.length_cons] at hlength
            exact Nat.add_right_cancel hlength
          simp only [knuthSubtractDigits]
          exact ih vDigits _ _ htail
            (evmSubBorrow_borrow_bit uDigit
              (evmSchoolbookStep qHat vDigit ⟨0⟩ carry).1 borrow)

/-- Exact arbitrary-length equation for the bytecode's combined product carry and subtraction
borrow. -/
theorem knuthSubtractDigits_recompose
    (qHat : UInt256) (uDigits vDigits : List UInt256) (carry borrow : UInt256)
    (hlength : uDigits.length = vDigits.length)
    (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    let result := knuthSubtractDigits qHat uDigits vDigits carry borrow
    wordLimbsToNat result.digits + qHat.toNat * wordLimbsToNat vDigits +
        carry.toNat + borrow.toNat =
      wordLimbsToNat uDigits + UInt256.size ^ uDigits.length *
        (result.carry.toNat + result.borrow.toNat) := by
  induction uDigits generalizing vDigits carry borrow with
  | nil =>
      have hv : vDigits = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst vDigits
      simp [knuthSubtractDigits, wordLimbsToNat]
  | cons uDigit uDigits ih =>
      cases vDigits with
      | nil => simp at hlength
      | cons vDigit vDigits =>
          have htail : uDigits.length = vDigits.length := by
            simp only [List.length_cons] at hlength
            exact Nat.add_right_cancel hlength
          let product := evmSchoolbookStep qHat vDigit ⟨0⟩ carry
          let subtraction := evmSubBorrow uDigit product.1 borrow
          let rest := knuthSubtractDigits qHat uDigits vDigits product.2 subtraction.2
          have hproduct := evmSchoolbookStep_recompose qHat vDigit ⟨0⟩ carry
          have hsubtraction := evmSubBorrow_recompose uDigit product.1 borrow hborrow
          have hnextBorrow := evmSubBorrow_borrow_bit uDigit product.1 borrow
          have hrest := ih vDigits product.2 subtraction.2 htail hnextBorrow
          have hscaled := congrArg (fun x => UInt256.size * x) hrest
          dsimp only [product, subtraction, rest] at hproduct hsubtraction hrest hscaled ⊢
          simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.add_zero] at hproduct
          simp only [knuthSubtractDigits, wordLimbsToNat, List.length_cons, pow_succ,
            Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hscaled ⊢
          ring_nf at hscaled ⊢
          omega

structure KnuthWindowResult where
  lower : List UInt256
  top : UInt256
  negative : UInt256

def knuthSubtractWindow
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256) :
    KnuthWindowResult :=
  let lower := knuthSubtractDigits qHat uLower vDigits ⟨0⟩ ⟨0⟩
  let top := evmSubBorrow uTop lower.carry lower.borrow
  ⟨lower.digits, top.1, top.2⟩

/-- After the saved top-limb subtraction, the final borrow is exactly the radix underflow of
`uWindow - qHat * v`. -/
theorem knuthSubtractWindow_recompose
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length) :
    let result := knuthSubtractWindow qHat uLower vDigits uTop
    wordLimbsToNat result.lower + UInt256.size ^ uLower.length * result.top.toNat +
        qHat.toNat * wordLimbsToNat vDigits =
      wordLimbsToNat uLower + UInt256.size ^ uLower.length * uTop.toNat +
        UInt256.size ^ (uLower.length + 1) * result.negative.toNat := by
  let lower := knuthSubtractDigits qHat uLower vDigits ⟨0⟩ ⟨0⟩
  let top := evmSubBorrow uTop lower.carry lower.borrow
  have hlower := knuthSubtractDigits_recompose qHat uLower vDigits ⟨0⟩ ⟨0⟩
    hlength (Or.inl rfl)
  have hborrow := knuthSubtractDigits_borrow_bit qHat uLower vDigits ⟨0⟩ ⟨0⟩
    hlength (Or.inl rfl)
  have htop := evmSubBorrow_recompose uTop lower.carry lower.borrow hborrow
  have hscaled := congrArg (fun x => UInt256.size ^ uLower.length * x) htop
  dsimp only [lower, top] at hlower hborrow htop hscaled ⊢
  simp only [knuthSubtractWindow, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.add_zero, Nat.mul_add, pow_succ] at hlower hscaled ⊢
  ring_nf at hscaled ⊢
  omega

theorem evmAddLimbs_carry_bit
    (left right : List UInt256) (carry : UInt256)
    (hlength : left.length = right.length)
    (hcarry : carry = ⟨0⟩ ∨ carry = ⟨1⟩) :
    let result := evmAddLimbs left right carry
    result.2 = ⟨0⟩ ∨ result.2 = ⟨1⟩ := by
  induction left generalizing right carry with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      simpa [evmAddLimbs] using hcarry
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simp only [List.length_cons] at hlength
            exact Nat.add_right_cancel hlength
          simp only [evmAddLimbs]
          exact ih rights (evmAddCarryStep left right carry).2 htail
            (evmAddCarryStep_carry_bit left right carry)

theorem evmAddLimbs_length
    (left right : List UInt256) (carry : UInt256)
    (hlength : left.length = right.length) :
    (evmAddLimbs left right carry).1.length = left.length := by
  induction left generalizing right carry with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      simp [evmAddLimbs]
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simp only [List.length_cons] at hlength
            exact Nat.add_right_cancel hlength
          simp only [evmAddLimbs, List.length_cons]
          rw [ih rights _ htail]

structure KnuthAddBackResult where
  lower : List UInt256
  top : UInt256
  overflow : UInt256

def knuthAddBack
    (lower vDigits : List UInt256) (top : UInt256) : KnuthAddBackResult :=
  let lowerResult := evmAddLimbs lower vDigits ⟨0⟩
  let topResult := evmAddCarryStep top ⟨0⟩ lowerResult.2
  ⟨lowerResult.1, topResult.1, topResult.2⟩

/-- Exact radix equation for the correction loop and its final top-carry write. -/
theorem knuthAddBack_recompose
    (lower vDigits : List UInt256) (top : UInt256)
    (hlength : lower.length = vDigits.length) :
    let result := knuthAddBack lower vDigits top
    wordLimbsToNat result.lower + UInt256.size ^ lower.length * result.top.toNat +
        UInt256.size ^ (lower.length + 1) * result.overflow.toNat =
      wordLimbsToNat lower + UInt256.size ^ lower.length * top.toNat +
        wordLimbsToNat vDigits := by
  let lowerResult := evmAddLimbs lower vDigits ⟨0⟩
  let topResult := evmAddCarryStep top ⟨0⟩ lowerResult.2
  have hlower := evmAddLimbs_recompose lower vDigits ⟨0⟩ hlength (Or.inl rfl)
  have hcarry := evmAddLimbs_carry_bit lower vDigits ⟨0⟩ hlength (Or.inl rfl)
  have htop := evmAddCarryStep_recompose top ⟨0⟩ lowerResult.2 hcarry
  have hscaled := congrArg (fun x => UInt256.size ^ lower.length * x) htop
  dsimp only [lowerResult, topResult] at hlower hcarry htop hscaled ⊢
  simp only [knuthAddBack, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.add_zero, zero_add, pow_succ] at hlower hscaled ⊢
  ring_nf at hscaled ⊢
  omega

def windowNat (lower : List UInt256) (top : UInt256) : Nat :=
  wordLimbsToNat lower + UInt256.size ^ lower.length * top.toNat

/-- If the top subtraction does not borrow, the selected quotient digit gives an ordinary exact
subtraction of `qHat * divisor` from the current window. -/
theorem knuthSubtractWindow_nonnegative
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length)
    (hnonnegative : (knuthSubtractWindow qHat uLower vDigits uTop).negative = ⟨0⟩) :
    let result := knuthSubtractWindow qHat uLower vDigits uTop
    windowNat result.lower result.top + qHat.toNat * wordLimbsToNat vDigits =
      windowNat uLower uTop := by
  have h := knuthSubtractWindow_recompose qHat uLower vDigits uTop hlength
  have hresultLength :
      (knuthSubtractWindow qHat uLower vDigits uTop).lower.length = uLower.length := by
    dsimp only [knuthSubtractWindow]
    exact knuthSubtractDigits_length qHat uLower vDigits ⟨0⟩ ⟨0⟩ hlength
  dsimp only at h ⊢
  rw [hnonnegative] at h
  simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.mul_zero,
    Nat.add_zero] at h
  simp only [windowNat]
  rw [hresultLength]
  exact h

/-- If the estimate was one too large, the bytecode's decrement and add-back produce the exact
window for `(qHat - 1) * divisor`.  `hoverflow` is the carry discarded by the top-word store; the
Algorithm D estimate bounds will establish that it is one. -/
theorem knuthSubtractWindow_corrected
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length)
    (hqHat : 0 < qHat.toNat)
    (hnegative : (knuthSubtractWindow qHat uLower vDigits uTop).negative = ⟨1⟩)
    (hoverflow :
      (knuthAddBack (knuthSubtractWindow qHat uLower vDigits uTop).lower vDigits
        (knuthSubtractWindow qHat uLower vDigits uTop).top).overflow = ⟨1⟩) :
    let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
    let corrected := knuthAddBack subtracted.lower vDigits subtracted.top
    windowNat corrected.lower corrected.top +
        (qHat.toNat - 1) * wordLimbsToNat vDigits =
      windowNat uLower uTop := by
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  let corrected := knuthAddBack subtracted.lower vDigits subtracted.top
  have hsub := knuthSubtractWindow_recompose qHat uLower vDigits uTop hlength
  have hsubLength : subtracted.lower.length = vDigits.length := by
    dsimp only [subtracted, knuthSubtractWindow]
    exact (knuthSubtractDigits_length qHat uLower vDigits ⟨0⟩ ⟨0⟩ hlength).trans
      hlength
  have hadd := knuthAddBack_recompose subtracted.lower vDigits subtracted.top hsubLength
  have hcorrectedLength : corrected.lower.length = uLower.length := by
    dsimp only [corrected, knuthAddBack]
    exact (evmAddLimbs_length subtracted.lower vDigits ⟨0⟩ hsubLength).trans
      (hsubLength.trans hlength.symm)
  have hq : qHat.toNat = (qHat.toNat - 1) + 1 := by omega
  have hproduct :
      wordLimbsToNat vDigits + (qHat.toNat - 1) * wordLimbsToNat vDigits =
        qHat.toNat * wordLimbsToNat vDigits := by
    conv_rhs => rw [hq]
    rw [Nat.add_mul, one_mul]
    omega
  dsimp only [subtracted, corrected] at hsub hsubLength hadd hnegative hoverflow ⊢
  rw [hnegative] at hsub
  rw [hoverflow] at hadd
  simp only [windowNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
    Nat.mul_one] at hsub hadd ⊢
  rw [hsubLength, ← hlength] at hadd
  rw [hcorrectedLength]
  omega

/-- Every `(lower, top)` window is strictly below the next radix power. -/
theorem windowNat_lt_pow (lower : List UInt256) (top : UInt256) :
    windowNat lower top < UInt256.size ^ (lower.length + 1) := by
  have hlower := wordLimbsToNat_lt_pow lower
  have htop : top.toNat < UInt256.size := top.val.isLt
  simp only [windowNat, pow_succ]
  calc
    wordLimbsToNat lower + UInt256.size ^ lower.length * top.toNat <
        UInt256.size ^ lower.length + UInt256.size ^ lower.length * top.toNat := by
          omega
    _ = UInt256.size ^ lower.length * (top.toNat + 1) := by ring
    _ ≤ UInt256.size ^ lower.length * UInt256.size := by
      exact Nat.mul_le_mul_left _ (by omega)

theorem knuthAddBack_overflow_bit
    (lower vDigits : List UInt256) (top : UInt256)
    (hlength : lower.length = vDigits.length) :
    let result := knuthAddBack lower vDigits top
    result.overflow = ⟨0⟩ ∨ result.overflow = ⟨1⟩ := by
  let lowerResult := evmAddLimbs lower vDigits ⟨0⟩
  have htopCarry := evmAddCarryStep_carry_bit top ⟨0⟩ lowerResult.2
  simpa [knuthAddBack, lowerResult] using htopCarry

/-- A negative subtraction together with the standard at-most-one-overestimate bound forces the
add-back carry to be one.  This discharges the carry premise used by the corrected-window
equation from arithmetic, rather than assuming a bytecode outcome. -/
theorem knuthAddBack_overflow_one
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length)
    (hnegative : (knuthSubtractWindow qHat uLower vDigits uTop).negative = ⟨1⟩)
    (hatMostOne :
      qHat.toNat * wordLimbsToNat vDigits ≤
        windowNat uLower uTop + wordLimbsToNat vDigits) :
    (knuthAddBack (knuthSubtractWindow qHat uLower vDigits uTop).lower vDigits
      (knuthSubtractWindow qHat uLower vDigits uTop).top).overflow = ⟨1⟩ := by
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  let corrected := knuthAddBack subtracted.lower vDigits subtracted.top
  have hsub := knuthSubtractWindow_recompose qHat uLower vDigits uTop hlength
  have hsubLength : subtracted.lower.length = vDigits.length := by
    dsimp only [subtracted, knuthSubtractWindow]
    exact (knuthSubtractDigits_length qHat uLower vDigits ⟨0⟩ ⟨0⟩ hlength).trans
      hlength
  have hadd := knuthAddBack_recompose subtracted.lower vDigits subtracted.top hsubLength
  have hcorrectedLength : corrected.lower.length = uLower.length := by
    dsimp only [corrected, knuthAddBack]
    exact (evmAddLimbs_length subtracted.lower vDigits ⟨0⟩ hsubLength).trans
      (hsubLength.trans hlength.symm)
  have hoverflowBit := knuthAddBack_overflow_bit subtracted.lower vDigits
    subtracted.top hsubLength
  have hcorrectedBound := windowNat_lt_pow corrected.lower corrected.top
  dsimp only [subtracted, corrected] at hsub hsubLength hadd hnegative hoverflowBit hcorrectedLength hcorrectedBound ⊢
  rw [hnegative] at hsub
  simp only [show (⟨1⟩ : UInt256).toNat = 1 by decide,
    Nat.mul_one, windowNat] at hsub hadd hatMostOne hcorrectedBound
  rw [hsubLength, ← hlength] at hadd
  rw [hcorrectedLength] at hcorrectedBound
  rcases hoverflowBit with hoverflowZero | hoverflowOne
  · rw [hoverflowZero] at hadd
    simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide,
      Nat.mul_zero, Nat.add_zero] at hadd
    exfalso
    omega
  · exact hoverflowOne

/-- A negative subtraction cannot arise from a zero quotient estimate. -/
theorem knuthNegative_qHat_positive
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length)
    (hnegative : (knuthSubtractWindow qHat uLower vDigits uTop).negative = ⟨1⟩) :
    0 < qHat.toNat := by
  have hsub := knuthSubtractWindow_recompose qHat uLower vDigits uTop hlength
  have hsubLength :
      (knuthSubtractWindow qHat uLower vDigits uTop).lower.length = uLower.length := by
    dsimp only [knuthSubtractWindow]
    exact knuthSubtractDigits_length qHat uLower vDigits ⟨0⟩ ⟨0⟩ hlength
  have hsubBound := windowNat_lt_pow
    (knuthSubtractWindow qHat uLower vDigits uTop).lower
    (knuthSubtractWindow qHat uLower vDigits uTop).top
  simp only [windowNat] at hsubBound
  rw [hsubLength] at hsubBound
  dsimp only at hsub
  rw [hnegative] at hsub
  simp only [show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mul_one] at hsub
  by_contra hnotPositive
  have hzero : qHat.toNat = 0 := by omega
  rw [hzero] at hsub
  simp only [zero_mul, Nat.add_zero] at hsub
  omega

/-- The two standard estimate inequalities are sufficient for either bytecode branch to produce
the exact accepted quotient digit and a window strictly below the divisor. -/
theorem knuthAcceptedWindow
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length)
    (hdivisorPos : 0 < wordLimbsToNat vDigits)
    (hnotLow :
      windowNat uLower uTop < (qHat.toNat + 1) * wordLimbsToNat vDigits)
    (hatMostOne :
      qHat.toNat * wordLimbsToNat vDigits ≤
        windowNat uLower uTop + wordLimbsToNat vDigits) :
    let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
    if subtracted.negative = ⟨0⟩ then
      windowNat subtracted.lower subtracted.top +
          qHat.toNat * wordLimbsToNat vDigits = windowNat uLower uTop ∧
        windowNat subtracted.lower subtracted.top < wordLimbsToNat vDigits
    else
      let corrected := knuthAddBack subtracted.lower vDigits subtracted.top
      windowNat corrected.lower corrected.top +
          (qHat.toNat - 1) * wordLimbsToNat vDigits = windowNat uLower uTop ∧
        windowNat corrected.lower corrected.top < wordLimbsToNat vDigits := by
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  have hnegativeBit := evmSubBorrow_borrow_bit uTop
    (knuthSubtractDigits qHat uLower vDigits ⟨0⟩ ⟨0⟩).carry
    (knuthSubtractDigits qHat uLower vDigits ⟨0⟩ ⟨0⟩).borrow
  change subtracted.negative = ⟨0⟩ ∨ subtracted.negative = ⟨1⟩ at hnegativeBit
  rcases hnegativeBit with hnonnegative | hnegative
  · rw [if_pos hnonnegative]
    have heq := knuthSubtractWindow_nonnegative qHat uLower vDigits uTop
      hlength hnonnegative
    constructor
    · exact heq
    · have hresultLength : subtracted.lower.length = uLower.length := by
        dsimp only [subtracted, knuthSubtractWindow]
        exact knuthSubtractDigits_length qHat uLower vDigits ⟨0⟩ ⟨0⟩ hlength
      dsimp only [subtracted] at heq ⊢
      have hproductSucc :
          (qHat.toNat + 1) * wordLimbsToNat vDigits =
            qHat.toNat * wordLimbsToNat vDigits + wordLimbsToNat vDigits := by
        ring
      rw [hproductSucc] at hnotLow
      omega
  · rw [if_neg (by exact fun hzero => by rw [hzero] at hnegative; contradiction)]
    have hqHat := knuthNegative_qHat_positive qHat uLower vDigits uTop hlength hnegative
    have hoverflow := knuthAddBack_overflow_one qHat uLower vDigits uTop hlength
      hnegative hatMostOne
    have heq := knuthSubtractWindow_corrected qHat uLower vDigits uTop hlength
      hqHat hnegative hoverflow
    constructor
    · exact heq
    · have hsub := knuthSubtractWindow_recompose qHat uLower vDigits uTop hlength
      have hsubLength :
          (knuthSubtractWindow qHat uLower vDigits uTop).lower.length = uLower.length := by
        dsimp only [knuthSubtractWindow]
        exact knuthSubtractDigits_length qHat uLower vDigits ⟨0⟩ ⟨0⟩ hlength
      have hsubBound := windowNat_lt_pow
        (knuthSubtractWindow qHat uLower vDigits uTop).lower
        (knuthSubtractWindow qHat uLower vDigits uTop).top
      have hproduct :
          qHat.toNat * wordLimbsToNat vDigits =
            (qHat.toNat - 1) * wordLimbsToNat vDigits + wordLimbsToNat vDigits := by
        have hq : qHat.toNat = qHat.toNat - 1 + 1 := by omega
        conv_lhs => rw [hq]
        ring
      dsimp only [subtracted] at heq hnegative hoverflow ⊢
      dsimp only at hsub
      rw [hnegative] at hsub
      simp only [show (⟨1⟩ : UInt256).toNat = 1 by decide,
        Nat.mul_one, windowNat] at hsub hsubBound
      rw [hsubLength] at hsubBound
      have hoverestimate :
          windowNat uLower uTop < qHat.toNat * wordLimbsToNat vDigits := by
        simp only [windowNat] at ⊢
        omega
      omega

private theorem lnotZero_eq_max :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

/-- The carry expression replayed at `PC 5722` is exactly the carry of the shared pure
schoolbook-product primitive with a zero result limb. -/
theorem multiplySubtractCarry_eq_schoolbook
    (qHat vDigit carry : UInt256) :
    let pLo := qHat * vDigit
    let pMM := UInt256.mulMod qHat vDigit (⟨0⟩ : UInt256).lnot
    let withCarry := pLo + carry
    (pMM - pLo - pMM.lt pLo) + withCarry.lt pLo =
      (evmSchoolbookStep qHat vDigit ⟨0⟩ carry).2 := by
  simp only [evmSchoolbookStep, evmMulHigh, lnotZero_eq_max]
  have hzero : UInt256.mul qHat vDigit + ⟨0⟩ = UInt256.mul qHat vDigit := by
    rw [u256_add_comm, u256_zero_add]
  have hself : (UInt256.mul qHat vDigit).lt (UInt256.mul qHat vDigit) = ⟨0⟩ :=
    ult_zero (Nat.le_refl _)
  rw [hzero, hself, u256_zero_add]
  ac_rfl

/-- The low product-plus-carry subtracted by `PC 5722` is the corresponding low limb of the
shared pure schoolbook-product primitive. -/
theorem multiplySubtractLow_eq_schoolbook
    (qHat vDigit carry : UInt256) :
    qHat * vDigit + carry = (evmSchoolbookStep qHat vDigit ⟨0⟩ carry).1 := by
  simp only [evmSchoolbookStep]
  have hzero : UInt256.mul qHat vDigit + ⟨0⟩ = UInt256.mul qHat vDigit := by
    rw [u256_add_comm, u256_zero_add]
  rw [hzero]
  rfl

end Modexp.MultiLimbSchoolbookDivisionSemantic
