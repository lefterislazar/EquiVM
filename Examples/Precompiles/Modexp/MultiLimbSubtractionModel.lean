import Examples.Precompiles.Modexp.MultiLimbArithmeticModel

/-!
# Multi-limb subtraction model

The generated division and Barrett loops use the same word subtraction primitive.  This module
lifts its exact one-word radix equation through an arbitrary equal-length little-endian vector.
-/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Limbwise subtraction with a propagated EVM borrow bit. -/
def evmSubLimbs : List UInt256 → List UInt256 → UInt256 → List UInt256 × UInt256
  | [], _, borrow => ([], borrow)
  | _ :: _, [], borrow => ([], borrow)
  | left :: lefts, right :: rights, borrow =>
      let digit := evmSubBorrow left right borrow
      let rest := evmSubLimbs lefts rights digit.2
      (digit.1 :: rest.1, rest.2)

/-- The word subtraction primitive always emits a Boolean borrow. -/
theorem evmSubBorrow_borrow_bit (left right borrow : UInt256) :
    (evmSubBorrow left right borrow).2 = ⟨0⟩ ∨
      (evmSubBorrow left right borrow).2 = ⟨1⟩ := by
  dsimp only [evmSubBorrow]
  by_cases hfirst : left.toNat < right.toNat
  · rw [ult_one hfirst]
    by_cases hsecond : (UInt256.sub left right).toNat < borrow.toNat
    · rw [ult_one hsecond]
      right
      native_decide
    · rw [ult_zero (by omega)]
      right
      native_decide
  · rw [ult_zero (by omega)]
    by_cases hsecond : (UInt256.sub left right).toNat < borrow.toNat
    · rw [ult_one hsecond]
      right
      native_decide
    · rw [ult_zero (by omega)]
      left
      native_decide

/-- The result vector has the same length as equal-length inputs. -/
theorem evmSubLimbs_result_length
    (left right : List UInt256) (borrow : UInt256)
    (hlength : left.length = right.length) :
    (evmSubLimbs left right borrow).1.length = left.length := by
  induction left generalizing right borrow with
  | nil => simp [evmSubLimbs]
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          simp [evmSubLimbs, ih rights
            (evmSubBorrow left right borrow).2 htail]

/-- Interpret a little-endian list of EVM words at radix `2^256`. -/
def wordLimbsToNat : List UInt256 → Nat
  | [] => 0
  | limb :: limbs => limb.toNat + UInt256.size * wordLimbsToNat limbs

/-- Word limbs are the generic radix interpretation at `2^256`. -/
theorem wordLimbsToNat_eq_limbsToNatAt (limbs : List UInt256) :
    wordLimbsToNat limbs =
      limbsToNatAt UInt256.size (limbs.map UInt256.toNat) := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp only [wordLimbsToNat, List.map_cons, limbsToNatAt, ih]

/-- The word-list interpretation is the shared pure limb interpretation. -/
theorem wordLimbsToNat_eq_limbsToNat (limbs : List UInt256) :
    wordLimbsToNat limbs = limbsToNat (limbs.map UInt256.toNat) := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp only [wordLimbsToNat, List.map_cons, limbsToNat, ih]
      have hbase : UInt256.size = 256 ^ 32 := by
        norm_num [UInt256.size, pow_mul]
      rw [hbase]

/-- An `n`-word vector denotes a value strictly below the `n`-word radix power. -/
theorem wordLimbsToNat_lt_pow (limbs : List UInt256) :
    wordLimbsToNat limbs < UInt256.size ^ limbs.length := by
  induction limbs with
  | nil => simp [wordLimbsToNat]
  | cons limb limbs ih =>
      simp only [wordLimbsToNat, List.length_cons, pow_succ]
      have hlimb : limb.toNat < UInt256.size := limb.val.isLt
      have hbase : 0 < UInt256.size := by norm_num [UInt256.size]
      calc
        limb.toNat + UInt256.size * wordLimbsToNat limbs <
            UInt256.size + UInt256.size * wordLimbsToNat limbs := by omega
        _ = UInt256.size * (wordLimbsToNat limbs + 1) := by ring
        _ ≤ UInt256.size * UInt256.size ^ limbs.length := by
          exact Nat.mul_le_mul_left UInt256.size (by omega)
        _ = UInt256.size ^ limbs.length * UInt256.size := Nat.mul_comm _ _

/-- Propagating word subtraction preserves the Boolean-borrow invariant. -/
theorem evmSubLimbs_final_borrow_bit
    (left right : List UInt256) (borrow : UInt256)
    (hlength : left.length = right.length)
    (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    (evmSubLimbs left right borrow).2 = ⟨0⟩ ∨
      (evmSubLimbs left right borrow).2 = ⟨1⟩ := by
  induction left generalizing right borrow with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      simpa [evmSubLimbs] using hborrow
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          simp only [evmSubLimbs]
          exact ih rights (evmSubBorrow left right borrow).2 htail
            (evmSubBorrow_borrow_bit left right borrow)

/-- Equal-length limb subtraction preserves one exact unbounded radix equation. -/
theorem evmSubLimbs_recompose
    (left right : List UInt256) (borrow : UInt256)
    (hlength : left.length = right.length)
    (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    let result := evmSubLimbs left right borrow
    wordLimbsToNat result.1 + wordLimbsToNat right + borrow.toNat =
      wordLimbsToNat left + UInt256.size ^ left.length * result.2.toNat := by
  induction left generalizing right borrow with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      simp [evmSubLimbs, wordLimbsToNat]
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          let digit := evmSubBorrow left right borrow
          let rest := evmSubLimbs lefts rights digit.2
          have hdigit := evmSubBorrow_recompose left right borrow hborrow
          have hnextBorrow := evmSubBorrow_borrow_bit left right borrow
          have hrest := ih rights digit.2 htail hnextBorrow
          have hscaled := congrArg (fun x => UInt256.size * x) hrest
          dsimp only [digit, rest] at hdigit hrest hscaled ⊢
          simp only [evmSubLimbs, wordLimbsToNat, List.length_cons, pow_succ,
            Nat.mul_add] at hscaled ⊢
          ring_nf at hscaled ⊢
          omega

/-- With zero initial borrow and `right ≤ left`, limb subtraction has no final borrow and is
ordinary natural subtraction. -/
theorem evmSubLimbs_eq_sub
    (left right : List UInt256)
    (hlength : left.length = right.length)
    (hge : wordLimbsToNat right ≤ wordLimbsToNat left) :
    let result := evmSubLimbs left right ⟨0⟩
    result.2 = ⟨0⟩ ∧
      wordLimbsToNat result.1 = wordLimbsToNat left - wordLimbsToNat right := by
  let result := evmSubLimbs left right ⟨0⟩
  have hrecompose := evmSubLimbs_recompose left right ⟨0⟩ hlength (Or.inl rfl)
  dsimp only [result] at hrecompose ⊢
  have hfinal := evmSubLimbs_final_borrow_bit left right ⟨0⟩ hlength (Or.inl rfl)
  have hresultLength := evmSubLimbs_result_length left right ⟨0⟩ hlength
  have hresultBound := wordLimbsToNat_lt_pow result.1
  dsimp only [result] at hresultBound
  rw [hresultLength] at hresultBound
  rcases hfinal with hzero | hone
  · constructor
    · exact hzero
    · rw [hzero] at hrecompose
      norm_num at hrecompose
      omega
  · rw [hone] at hrecompose
    norm_num at hrecompose
    rw [show (⟨1⟩ : UInt256).toNat = 1 by decide] at hrecompose
    omega

/-- When the right operand is larger, equal-width subtraction wraps through one omitted radix
word and reports final borrow one. -/
theorem evmSubLimbs_eq_add_pow_sub
    (left right : List UInt256)
    (hlength : left.length = right.length)
    (hlt : wordLimbsToNat left < wordLimbsToNat right) :
    let result := evmSubLimbs left right ⟨0⟩
    result.2 = ⟨1⟩ ∧
      wordLimbsToNat result.1 =
        wordLimbsToNat left + UInt256.size ^ left.length - wordLimbsToNat right := by
  let result := evmSubLimbs left right ⟨0⟩
  have hrecompose := evmSubLimbs_recompose left right ⟨0⟩ hlength (Or.inl rfl)
  dsimp only [result] at hrecompose ⊢
  have hfinal := evmSubLimbs_final_borrow_bit left right ⟨0⟩ hlength (Or.inl rfl)
  rcases hfinal with hzero | hone
  · rw [hzero] at hrecompose
    norm_num at hrecompose
    omega
  · constructor
    · exact hone
    · rw [hone] at hrecompose
      norm_num at hrecompose
      rw [show (⟨1⟩ : UInt256).toNat = 1 by decide] at hrecompose
      have hrightBound := wordLimbsToNat_lt_pow right
      rw [← hlength] at hrightBound
      omega

/-- Equal-width word subtraction is subtraction modulo the vector radix power. -/
theorem evmSubLimbs_value
    (left right : List UInt256)
    (hlength : left.length = right.length) :
    wordLimbsToNat (evmSubLimbs left right ⟨0⟩).1 =
      if wordLimbsToNat right ≤ wordLimbsToNat left then
        wordLimbsToNat left - wordLimbsToNat right
      else
        wordLimbsToNat left + UInt256.size ^ left.length - wordLimbsToNat right := by
  by_cases hge : wordLimbsToNat right ≤ wordLimbsToNat left
  · rw [if_pos hge]
    exact (evmSubLimbs_eq_sub left right hlength hge).2
  · rw [if_neg hge]
    exact (evmSubLimbs_eq_add_pow_sub left right hlength (by omega)).2

/-- The same subtraction equation stated in the representation used by the trusted byte model. -/
theorem evmSubLimbs_recompose_limbsToNat
    (left right : List UInt256) (borrow : UInt256)
    (hlength : left.length = right.length)
    (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    let result := evmSubLimbs left right borrow
    limbsToNat (result.1.map UInt256.toNat) +
        limbsToNat (right.map UInt256.toNat) + borrow.toNat =
      limbsToNat (left.map UInt256.toNat) +
        (256 ^ 32) ^ left.length * result.2.toNat := by
  have h := evmSubLimbs_recompose left right borrow hlength hborrow
  dsimp only at h ⊢
  rw [← wordLimbsToNat_eq_limbsToNat, ← wordLimbsToNat_eq_limbsToNat,
    ← wordLimbsToNat_eq_limbsToNat]
  rw [h]
  have hbase : 256 ^ 32 = UInt256.size := by
    norm_num [UInt256.size, pow_mul]
  rw [hbase]

end Modexp
