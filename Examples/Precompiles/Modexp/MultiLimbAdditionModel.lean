import Examples.Precompiles.Modexp.MultiLimbSubtractionModel

/-! # Multi-limb add-back arithmetic -/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- The add-back update used after an overestimated Knuth quotient digit. -/
def evmAddCarryStep (left right carry : UInt256) : UInt256 × UInt256 :=
  let sum := left + right
  let firstCarry := UInt256.lt sum left
  let sum2 := sum + carry
  let secondCarry := UInt256.lt sum2 sum
  (sum2, UInt256.lor firstCarry secondCarry)

private theorem ult_bit (a b : UInt256) :
    UInt256.lt a b = ⟨0⟩ ∨ UInt256.lt a b = ⟨1⟩ := by
  by_cases h : a.toNat < b.toNat
  · exact Or.inr (ult_one h)
  · exact Or.inl (ult_zero (by omega))

/-- One add-back word preserves the exact unbounded radix equation. -/
theorem evmAddCarryStep_recompose
    (left right carry : UInt256) (hcarry : carry = ⟨0⟩ ∨ carry = ⟨1⟩) :
    let step := evmAddCarryStep left right carry
    step.1.toNat + UInt256.size * step.2.toNat =
      left.toNat + right.toNat + carry.toNat := by
  let sum := left + right
  let c1 := UInt256.lt sum left
  let sum2 := sum + carry
  let c2 := UInt256.lt sum2 sum
  have hfirst := evmAddCarry_recompose left right
  have hsecond := evmAddCarry_recompose sum carry
  change sum.toNat + UInt256.size * c1.toNat = left.toNat + right.toNat at hfirst
  change sum2.toNat + UInt256.size * c2.toNat = sum.toNat + carry.toNat at hsecond
  have hcombined : sum2.toNat + UInt256.size * (c1.toNat + c2.toNat) =
      left.toNat + right.toNat + carry.toNat := by
    calc
      sum2.toNat + UInt256.size * (c1.toNat + c2.toNat) =
          (sum2.toNat + UInt256.size * c2.toNat) + UInt256.size * c1.toNat := by
            ring
      _ = (sum.toNat + carry.toNat) + UInt256.size * c1.toNat := by rw [hsecond]
      _ = (sum.toNat + UInt256.size * c1.toNat) + carry.toNat := by ring
      _ = left.toNat + right.toNat + carry.toNat := by rw [hfirst]
  have hleft : left.toNat < UInt256.size := left.val.isLt
  have hright : right.toNat < UInt256.size := right.val.isLt
  have hcarryNat : carry.toNat ≤ 1 := by rcases hcarry with rfl | rfl <;> decide
  have htotal : left.toNat + right.toNat + carry.toNat < 2 * UInt256.size := by
    omega
  have hcarrySum : c1.toNat + c2.toNat ≤ 1 := by
    by_contra hnot
    have hge : 2 ≤ c1.toNat + c2.toNat := by omega
    have hmul : 2 * UInt256.size ≤ UInt256.size * (c1.toNat + c2.toNat) := by
      nlinarith
    omega
  have hlor : (UInt256.lor c1 c2).toNat = c1.toNat + c2.toNat := by
    dsimp only [c1, c2] at hcarrySum ⊢
    rcases ult_bit sum left with hc1 | hc1 <;>
      rcases ult_bit sum2 sum with hc2 | hc2 <;> rw [hc1, hc2] at hcarrySum ⊢
    · native_decide
    · native_decide
    · native_decide
    · have hone : (⟨1⟩ : UInt256).toNat = 1 := rfl
      rw [hone] at hcarrySum
      omega
  dsimp only [evmAddCarryStep]
  change sum2.toNat + UInt256.size * (UInt256.lor c1 c2).toNat =
    left.toNat + right.toNat + carry.toNat
  rw [hlor]
  exact hcombined

theorem evmAddCarryStep_carry_bit (left right carry : UInt256) :
    (evmAddCarryStep left right carry).2 = ⟨0⟩ ∨
      (evmAddCarryStep left right carry).2 = ⟨1⟩ := by
  dsimp only [evmAddCarryStep]
  rcases ult_bit (left + right) left with h1 | h1 <;>
    rcases ult_bit ((left + right) + carry) (left + right) with h2 | h2 <;>
      rw [h1, h2]
  · left; native_decide
  · right; native_decide
  · right; native_decide
  · right; native_decide

def evmAddLimbs : List UInt256 → List UInt256 → UInt256 → List UInt256 × UInt256
  | [], _, carry => ([], carry)
  | _ :: _, [], carry => ([], carry)
  | left :: lefts, right :: rights, carry =>
      let digit := evmAddCarryStep left right carry
      let rest := evmAddLimbs lefts rights digit.2
      (digit.1 :: rest.1, rest.2)

/-- Equal-length add-back preserves one exact unbounded radix equation. -/
theorem evmAddLimbs_recompose
    (left right : List UInt256) (carry : UInt256)
    (hlength : left.length = right.length)
    (hcarry : carry = ⟨0⟩ ∨ carry = ⟨1⟩) :
    let result := evmAddLimbs left right carry
    wordLimbsToNat result.1 + UInt256.size ^ left.length * result.2.toNat =
      wordLimbsToNat left + wordLimbsToNat right + carry.toNat := by
  induction left generalizing right carry with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      simp [evmAddLimbs, wordLimbsToNat]
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          let digit := evmAddCarryStep left right carry
          let rest := evmAddLimbs lefts rights digit.2
          have hdigit := evmAddCarryStep_recompose left right carry hcarry
          have hnext := evmAddCarryStep_carry_bit left right carry
          have hrest := ih rights digit.2 htail hnext
          have hscaled := congrArg (fun x => UInt256.size * x) hrest
          dsimp only [digit, rest] at hdigit hrest hscaled ⊢
          simp only [evmAddLimbs, wordLimbsToNat, List.length_cons, pow_succ,
            Nat.mul_add] at hscaled ⊢
          ring_nf at hscaled ⊢
          omega

end Modexp
