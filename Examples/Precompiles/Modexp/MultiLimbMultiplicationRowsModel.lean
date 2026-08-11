import Examples.Precompiles.Modexp.MultiLimbMultiplicationRowModel

/-! # Complete schoolbook outer-loop invariant -/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- A sequence of source outer-loop rows, starting at a specified limb shift. -/
inductive SchoolbookRows (bs : List UInt256) :
    Nat → List UInt256 → List UInt256 → List UInt256 → Prop
  | nil (shift : Nat) (state : List UInt256) :
      SchoolbookRows bs shift [] state state
  | cons (shift : Nat) (a : UInt256) (as : List UInt256)
      (before middle after : List UInt256)
      (head : SchoolbookRowUpdate a bs shift before middle)
      (tail : SchoolbookRows bs (shift + 1) as middle after) :
      SchoolbookRows bs shift (a :: as) before after

/-- All outer rows together add the exact product of the two represented limb vectors. -/
theorem schoolbookRows_value
    {bs as before after : List UInt256} {shift : Nat}
    (rows : SchoolbookRows bs shift as before after) :
    wordLimbsToNat after = wordLimbsToNat before +
      UInt256.size ^ shift * (wordLimbsToNat as * wordLimbsToNat bs) := by
  induction rows with
  | nil shift state => simp [wordLimbsToNat]
  | cons shift a as before middle after head tail ih =>
      rw [ih, schoolbookRowUpdate_value head]
      simp only [wordLimbsToNat, pow_succ]
      ring

@[simp] theorem wordLimbsToNat_replicate_zero (count : Nat) :
    wordLimbsToNat (List.replicate count (⟨0⟩ : UInt256)) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hzero : (⟨0⟩ : UInt256).toNat = 0 := rfl
      simp only [List.replicate_succ, wordLimbsToNat, ih, hzero,
        zero_add, Nat.mul_zero]

/-- A complete source-style schoolbook execution from its zero array returns the exact product. -/
theorem schoolbookRows_from_zero
    {bs as output : List UInt256} {resultLength : Nat}
    (rows : SchoolbookRows bs 0 as
      (List.replicate resultLength (⟨0⟩ : UInt256)) output) :
    wordLimbsToNat output = wordLimbsToNat as * wordLimbsToNat bs := by
  simpa using schoolbookRows_value rows

/-- Complete multiplication correctness in the representation connected to calldata bytes. -/
theorem schoolbookRows_from_zero_limbsToNat
    {bs as output : List UInt256} {resultLength : Nat}
    (rows : SchoolbookRows bs 0 as
      (List.replicate resultLength (⟨0⟩ : UInt256)) output) :
    limbsToNat (output.map UInt256.toNat) =
      limbsToNat (as.map UInt256.toNat) * limbsToNat (bs.map UInt256.toNat) := by
  rw [← wordLimbsToNat_eq_limbsToNat, ← wordLimbsToNat_eq_limbsToNat,
    ← wordLimbsToNat_eq_limbsToNat]
  exact schoolbookRows_from_zero rows

/-- A row prefix has materialized only its processed columns; all later carry slots remain zero. -/
def SchoolbookZeroTail (bs : List UInt256) (shift remaining : Nat)
    (state : List UInt256) : Prop :=
  ∃ front, front.length = shift + bs.length ∧
    state = front ++ List.replicate remaining (⟨0⟩ : UInt256)

/-- The all-zero product allocation has the zero-tail invariant before the first row. -/
theorem schoolbookZeroTail_initial
    (bs : List UInt256) (remaining resultLength : Nat)
    (hlength : resultLength = bs.length + remaining) :
    SchoolbookZeroTail bs 0 remaining
      (List.replicate resultLength (⟨0⟩ : UInt256)) := by
  refine ⟨List.replicate bs.length (⟨0⟩ : UInt256), by simp, ?_⟩
  rw [hlength, List.replicate_add]

/-- One valid row update consumes exactly one fresh zero carry slot and leaves the remaining zero
tail unchanged. -/
theorem schoolbookRowUpdate_zeroTail
    {a : UInt256} {bs before after : List UInt256} {shift remaining : Nat}
    (hupdate : SchoolbookRowUpdate a bs shift before after)
    (htail : SchoolbookZeroTail bs shift (remaining + 1) before) :
    SchoolbookZeroTail bs (shift + 1) remaining after := by
  rcases hupdate with ⟨pre, segment, suffix, hpre, hsegment, hbefore, hafter⟩
  rcases htail with ⟨front, hfrontLength, hstate⟩
  have hprefixLength : (pre ++ segment).length = front.length := by
    simp only [List.length_append, hpre, hsegment, hfrontLength]
  have hsplit : (⟨0⟩ : UInt256) :: suffix =
      (⟨0⟩ : UInt256) :: List.replicate remaining ⟨0⟩ := by
    have heq : (pre ++ segment) ++ (⟨0⟩ : UInt256) :: suffix =
        front ++ (⟨0⟩ : UInt256) :: List.replicate remaining ⟨0⟩ := by
      rw [← List.replicate_succ]
      simpa only [List.append_assoc] using hbefore.symm.trans hstate
    exact (List.append_inj heq hprefixLength).2
  have hsuffix : suffix = List.replicate remaining (⟨0⟩ : UInt256) :=
    List.tail_eq_of_cons_eq hsplit
  let row := evmSchoolbookRow a bs segment ⟨0⟩
  refine ⟨pre ++ row.1 ++ [row.2], ?_, ?_⟩
  · have hrowLength := evmSchoolbookRow_result_length a bs segment ⟨0⟩ hsegment.symm
    simp only [List.length_append, List.length_singleton, hpre, row, hrowLength]
    omega
  · rw [hafter, hsuffix]
    simp only [row, List.append_assoc, List.singleton_append]

/-- A nonempty zero tail exposes exactly the next row segment followed by its fresh zero carry
slot. -/
theorem schoolbookZeroTail_fresh_decomposition
    {bs state : List UInt256} {shift remaining : Nat}
    (htail : SchoolbookZeroTail bs shift remaining state)
    (hremaining : 0 < remaining) :
    ∃ pre segment suffix,
      pre.length = shift ∧ segment.length = bs.length ∧
      state = pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix := by
  rcases htail with ⟨front, hfront, hstate⟩
  let pre := front.take shift
  let segment := front.drop shift
  let suffix := List.replicate (remaining - 1) (⟨0⟩ : UInt256)
  have hshiftLe : shift ≤ front.length := by omega
  have hpre : pre.length = shift := by
    simp only [pre, List.length_take, Nat.min_eq_left hshiftLe]
  have hsegment : segment.length = bs.length := by
    simp only [segment, List.length_drop, hfront]
    omega
  refine ⟨pre, segment, suffix, hpre, hsegment, ?_⟩
  rw [hstate, show remaining = (remaining - 1) + 1 by omega, List.replicate_succ]
  simp only [suffix]
  rw [show pre ++ segment = front by
    simpa only [pre, segment] using front.take_append_drop shift]

end Modexp
