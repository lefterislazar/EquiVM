import Examples.Precompiles.Modexp.MultiLimbMultiplicationOuterModel

/-! # Shifted schoolbook row update -/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Semantic relation for one source-level outer-loop row.  The zero word is the fresh top slot
that receives the final carry. -/
def SchoolbookRowUpdate (a : UInt256) (bs : List UInt256) (shift : Nat)
    (before after : List UInt256) : Prop :=
  ∃ pre segment suffix,
    pre.length = shift ∧ segment.length = bs.length ∧
    before = pre ++ segment ++ ⟨0⟩ :: suffix ∧
    let row := evmSchoolbookRow a bs segment ⟨0⟩
    after = pre ++ row.1 ++ row.2 :: suffix

/-- Multiplication by a selected zero source limb leaves the current row segment and its fresh
top word unchanged. -/
theorem evmSchoolbookRow_zero (bs segment : List UInt256)
    (hlength : bs.length = segment.length) :
    evmSchoolbookRow (⟨0⟩ : UInt256) bs segment ⟨0⟩ = (segment, ⟨0⟩) := by
  induction bs generalizing segment with
  | nil =>
      have hsegment : segment = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst segment
      rfl
  | cons b bs ih =>
      cases segment with
      | nil => simp at hlength
      | cons digit segment =>
          have htail : bs.length = segment.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          have hstep : evmSchoolbookStep (⟨0⟩ : UInt256) b digit ⟨0⟩ =
              (digit, ⟨0⟩) := by
            let output := evmSchoolbookStep (⟨0⟩ : UInt256) b digit ⟨0⟩
            have hmul : UInt256.mul (⟨0⟩ : UInt256) b = ⟨0⟩ := by
              apply u256_inj
              rw [u256_mul_toNat]
              simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, zero_mul,
                Nat.zero_mod]
            have hlow : output.1 = digit := by
              dsimp only [output, evmSchoolbookStep]
              rw [hmul, u256_zero_add, u256_add_comm digit ⟨0⟩, u256_zero_add]
            have hrecompose := evmSchoolbookStep_recompose
              (⟨0⟩ : UInt256) b digit ⟨0⟩
            have hcarryNat : output.2.toNat = 0 := by
              change output.1.toNat + UInt256.size * output.2.toNat =
                (⟨0⟩ : UInt256).toNat * b.toNat + digit.toNat +
                  (⟨0⟩ : UInt256).toNat at hrecompose
              rw [hlow] at hrecompose
              simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, zero_mul,
                zero_add] at hrecompose
              have hcancel : digit.toNat + UInt256.size * output.2.toNat =
                  digit.toNat + 0 := by
                simpa only [Nat.add_zero] using hrecompose
              have hproduct : UInt256.size * output.2.toNat = 0 :=
                Nat.add_left_cancel hcancel
              exact (Nat.mul_eq_zero.mp hproduct).resolve_left (by decide)
            apply Prod.ext hlow
            apply u256_inj
            simpa only [show (⟨0⟩ : UInt256).toNat = 0 by decide] using hcarryNat
          simp only [evmSchoolbookRow, hstep]
          rw [ih segment htail]

/-- The source-level skipped row is a valid shifted row update when its selected source limb is
zero and the destination has the required fresh top word. -/
theorem schoolbookRowUpdate_zero
    (bs pre segment suffix : List UInt256) (shift : Nat)
    (hpre : pre.length = shift) (hsegment : segment.length = bs.length) :
    SchoolbookRowUpdate (⟨0⟩ : UInt256) bs shift
      (pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix)
      (pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix) := by
  refine ⟨pre, segment, suffix, hpre, hsegment, rfl, ?_⟩
  rw [evmSchoolbookRow_zero bs segment hsegment.symm]

/-- One shifted source row adds exactly `a * b * B^shift` to the full result array. -/
theorem schoolbookRowUpdate_value
    {a : UInt256} {bs : List UInt256} {shift : Nat}
    {before after : List UInt256}
    (hupdate : SchoolbookRowUpdate a bs shift before after) :
    wordLimbsToNat after = wordLimbsToNat before +
      UInt256.size ^ shift * (a.toNat * wordLimbsToNat bs) := by
  rcases hupdate with ⟨pre, segment, suffix, hpre, hsegment, rfl, hafter⟩
  let row := evmSchoolbookRow a bs segment ⟨0⟩
  have hrow := evmSchoolbookRow_recompose a bs segment ⟨0⟩ hsegment.symm
  have hrowLength := evmSchoolbookRow_result_length a bs segment ⟨0⟩ hsegment.symm
  dsimp only [row] at hrow hrowLength hafter
  have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp only [hzero, add_zero] at hrow
  rw [hafter]
  simp only [wordLimbsToNat_append, List.length_append, List.length_cons,
    wordLimbsToNat, hzero, zero_add]
  rw [hpre, hrowLength, hsegment]
  simp only [pow_add]
  have hscaled := congrArg (fun x => UInt256.size ^ shift * x) hrow
  ring_nf at hscaled ⊢
  omega

end Modexp
