import Examples.Precompiles.Modexp.Bridge

/-!
# Pure multi-limb representation

This file gives the little-endian 256-bit limb representation used by both deployed multi-limb
backends a direct meaning in the unchanged trusted byte model.
-/

namespace Modexp

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Interpret a little-endian list of 256-bit limbs as a natural number. -/
def limbsToNat : List Nat → Nat
  | [] => 0
  | limb :: limbs => limb + 256 ^ 32 * limbsToNat limbs

/-- Radix-parametric little-endian interpretation, used to keep generic algebra independent of
the concrete `2^256` numeral. -/
def limbsToNatAt (radix : Nat) : List Nat → Nat
  | [] => 0
  | limb :: limbs => limb + radix * limbsToNatAt radix limbs

theorem limbsToNat_eq_limbsToNatAt (limbs : List Nat) :
    limbsToNat limbs = limbsToNatAt (256 ^ 32) limbs := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp only [limbsToNat, limbsToNatAt, ih]

/-- Generic radix interpretation distributes over append. -/
theorem limbsToNatAt_append (radix : Nat) (left right : List Nat) :
    limbsToNatAt radix (left ++ right) =
      limbsToNatAt radix left + radix ^ left.length * limbsToNatAt radix right := by
  induction left with
  | nil => simp [limbsToNatAt]
  | cons limb left ih =>
      simp only [List.cons_append, limbsToNatAt, List.length_cons, pow_succ, ih]
      rw [Nat.mul_add]
      ac_rfl

/-- Split a padded big-endian byte field into little-endian limbs, starting at its low end. -/
def bytesToLimbsPure (bs : ByteArray) (start : Nat) : Nat → List Nat
  | 0 => []
  | len + 1 =>
      if len + 1 ≤ 32 then
        [Model.bytesToNatPadded bs start (len + 1)]
      else
        Model.bytesToNatPadded bs (start + (len + 1 - 32)) 32 ::
          bytesToLimbsPure bs start (len + 1 - 32)
termination_by len => len
decreasing_by omega

@[simp] theorem bytesToLimbsPure_zero (bs : ByteArray) (start : Nat) :
    bytesToLimbsPure bs start 0 = [] := by
  rw [bytesToLimbsPure]

theorem bytesToLimbsPure_of_pos (bs : ByteArray) (start len : Nat)
    (hlen : 0 < len) :
    bytesToLimbsPure bs start len =
      if len ≤ 32 then
        [Model.bytesToNatPadded bs start len]
      else
        Model.bytesToNatPadded bs (start + (len - 32)) 32 ::
          bytesToLimbsPure bs start (len - 32) := by
  obtain ⟨len, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : len ≠ 0)
  rw [bytesToLimbsPure]

/-- The deployed limb orientation is exactly the trusted big-endian byte value. -/
theorem limbsToNat_bytesToLimbsPure (bs : ByteArray) (start len : Nat) :
    limbsToNat (bytesToLimbsPure bs start len) =
      Model.bytesToNatPadded bs start len := by
  induction len using Nat.strong_induction_on with
  | h len ih =>
    by_cases hzero : len = 0
    · subst len
      simp [limbsToNat]
    · have hpos : 0 < len := Nat.pos_of_ne_zero hzero
      rw [bytesToLimbsPure_of_pos bs start len hpos]
      by_cases hsmall : len ≤ 32
      · simp [hsmall, limbsToNat]
      · have hlarge : 32 < len := by omega
        have hlt : len - 32 < len := by omega
        have hsplit := model_bytesToNatPadded_split bs start (len - 32) 32
        rw [if_neg hsmall, limbsToNat, ih (len - 32) hlt]
        rw [show len - 32 + 32 = len by omega] at hsplit
        rw [hsplit]
        ring

/-- Every emitted full limb is a 256-bit value. -/
theorem bytesToLimbsPure_limb_lt
    (bs : ByteArray) (start len : Nat) {limb : Nat}
    (hmem : limb ∈ bytesToLimbsPure bs start len) :
    limb < 2 ^ 256 := by
  induction len using Nat.strong_induction_on with
  | h len ih =>
    by_cases hzero : len = 0
    · subst len
      simp at hmem
    · have hpos : 0 < len := Nat.pos_of_ne_zero hzero
      rw [bytesToLimbsPure_of_pos bs start len hpos] at hmem
      by_cases hsmall : len ≤ 32
      · simp only [hsmall, ↓reduceIte, List.mem_singleton] at hmem
        subst limb
        have hbound := model_bytesToNatPadded_lt_pow bs start len
        calc
          Model.bytesToNatPadded bs start len < 256 ^ len := hbound
          _ ≤ 256 ^ 32 := Nat.pow_le_pow_right (by decide : 0 < (256 : Nat)) hsmall
          _ = 2 ^ 256 := by norm_num [pow_mul]
      · have hlarge : 32 < len := by omega
        simp only [hsmall, ↓reduceIte, List.mem_cons] at hmem
        rcases hmem with rfl | htail
        · simpa [show 256 ^ 32 = 2 ^ 256 by norm_num [pow_mul]] using
            model_bytesToNatPadded_lt_pow bs (start + (len - 32)) 32
        · exact ih (len - 32) (by omega) htail

/-- The pure splitter emits exactly `ceil(len / 32)` limbs. -/
@[simp] theorem bytesToLimbsPure_length (bs : ByteArray) (start len : Nat) :
    (bytesToLimbsPure bs start len).length = (len + 31) / 32 := by
  induction len using Nat.strong_induction_on with
  | h len ih =>
    by_cases hzero : len = 0
    · subst len
      simp
    · have hpos : 0 < len := Nat.pos_of_ne_zero hzero
      rw [bytesToLimbsPure_of_pos bs start len hpos]
      by_cases hsmall : len ≤ 32
      · simp only [hsmall, ↓reduceIte, List.length_singleton]
        omega
      · simp only [hsmall, ↓reduceIte, List.length_cons, ih (len - 32) (by omega)]
        omega

/-- A full-limb lookup is the corresponding low-to-high 32-byte source chunk. -/
theorem bytesToLimbsPure_getElem_full
    (bs : ByteArray) (start len q : Nat) (hq : q < len / 32) :
    (bytesToLimbsPure bs start len)[q]'(by rw [bytesToLimbsPure_length]; omega) =
      Model.bytesToNatPadded bs (start + len - 32 * (q + 1)) 32 := by
  induction len using Nat.strong_induction_on generalizing q with
  | h len ih =>
    have hpos : 0 < len := by omega
    simp only [bytesToLimbsPure_of_pos bs start len hpos]
    by_cases hsmall : len ≤ 32
    · have hlen : len = 32 := by omega
      subst len
      have hq0 : q = 0 := by omega
      subst q
      simp
    · simp only [hsmall, ↓reduceIte]
      cases q with
      | zero =>
          simp only [List.getElem_cons_zero]
          congr 2
          omega
      | succ q =>
          simp only [List.getElem_cons_succ]
          have hdiv : len / 32 = (len - 32) / 32 + 1 := by
            calc
              len / 32 = ((len - 32) + 32) / 32 := by
                rw [Nat.sub_add_cancel (by omega : 32 ≤ len)]
              _ = (len - 32) / 32 + 1 := by
                convert Nat.add_mul_div_right (len - 32) 1 (by decide : 0 < 32) using 1 <;>
                  omega
          have hq' : q < (len - 32) / 32 := by omega
          rw [ih (len - 32) (by omega) q hq']
          have hmul := Nat.mul_div_le (len - 32) 32
          have hqmul : 32 * (q + 1) ≤ len - 32 := by
            calc
              32 * (q + 1) ≤ 32 * ((len - 32) / 32) :=
                Nat.mul_le_mul_left 32 (by omega)
              _ ≤ len - 32 := by simpa [Nat.mul_comm] using hmul
          rw [← Nat.add_sub_assoc (by omega : 32 ≤ len) start, Nat.sub_sub]
          congr 2
          omega

/-- On a non-aligned input, the final pure limb is the leading partial source prefix. -/
theorem bytesToLimbsPure_getElem_partial
    (bs : ByteArray) (start len : Nat) (hrem : len % 32 ≠ 0) :
    (bytesToLimbsPure bs start len)[len / 32]'(by
      rw [bytesToLimbsPure_length]
      omega) = Model.bytesToNatPadded bs start (len % 32) := by
  induction len using Nat.strong_induction_on with
  | h len ih =>
    have hpos : 0 < len := by omega
    simp only [bytesToLimbsPure_of_pos bs start len hpos]
    by_cases hsmall : len ≤ 32
    · have hlt : len < 32 := by omega
      simp only [hsmall, ↓reduceIte]
      have hdiv : len / 32 = 0 := by omega
      have hmod : len % 32 = len := by omega
      simp [hdiv, hmod]
    · simp only [hsmall, ↓reduceIte]
      have hlarge : 32 < len := by omega
      have hdivPos : 0 < len / 32 := by omega
      have hdiv : len / 32 = (len - 32) / 32 + 1 := by
        calc
          len / 32 = ((len - 32) + 32) / 32 := by
            rw [Nat.sub_add_cancel (by omega : 32 ≤ len)]
          _ = (len - 32) / 32 + 1 := by
            convert Nat.add_mul_div_right (len - 32) 1 (by decide : 0 < 32) using 1 <;>
              omega
      simp only [hdiv, List.getElem_cons_succ]
      have hrem' : (len - 32) % 32 ≠ 0 := by omega
      rw [ih (len - 32) (by omega) hrem']
      have hmod : (len - 32) % 32 = len % 32 := by
        conv_rhs => rw [← Nat.sub_add_cancel (by omega : 32 ≤ len)]
        rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
      rw [hmod]

end Modexp
