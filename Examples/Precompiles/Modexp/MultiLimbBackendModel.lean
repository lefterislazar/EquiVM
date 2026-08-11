import Examples.Precompiles.Modexp.LimbModel

/-!
# Backend-independent multi-limb exponentiation model

Both wide backends scan exponent bits from most to least significant.  This file proves that scan
once, parameterized by the representation and concrete modular-multiplication operation.  The
backend proofs therefore only need to establish their multiplication contract.
-/

namespace Modexp

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- State of an MSB-first exponent scan.  The natural component records the consumed prefix. -/
structure MsbPowState (A : Type) where
  value : A
  exponent : Nat

/-- Scan bits from most to least significant using a backend's modular multiplication. -/
def msbPowScan {A : Type} (mul : A → A → A) (base : A) :
    MsbPowState A → List Bool → MsbPowState A
  | state, [] => state
  | state, bit :: bits =>
      let square := mul state.value state.value
      let value := if bit then mul square base else square
      msbPowScan mul base
        { value := value, exponent := 2 * state.exponent + if bit then 1 else 0 }
        bits

/-- Natural value of a bit string written most-significant bit first. -/
def bitsToNatMSB (bits : List Bool) : Nat :=
  bits.foldl (fun acc bit => 2 * acc + if bit then 1 else 0) 0

/-- Scanning a suffix appends its bits to the already consumed exponent prefix. -/
theorem msbPowScan_exponent (mul : A → A → A) (base : A)
    (state : MsbPowState A) (bits : List Bool) :
    (msbPowScan mul base state bits).exponent =
      bits.foldl (fun acc bit => 2 * acc + if bit then 1 else 0) state.exponent := by
  induction bits generalizing state with
  | nil => rfl
  | cons bit bits ih =>
      unfold msbPowScan
      exact ih _

/-- A scan starting at exponent zero consumes exactly the represented MSB-first integer. -/
theorem msbPowScan_exponent_zero (mul : A → A → A) (base one : A)
    (bits : List Bool) :
    (msbPowScan mul base { value := one, exponent := 0 } bits).exponent = bitsToNatMSB bits := by
  rw [msbPowScan_exponent]
  rfl

@[simp] theorem msbPowScan_nil {A : Type} (mul : A → A → A) (base : A)
    (state : MsbPowState A) :
    msbPowScan mul base state [] = state := by
  rfl

/-- A modular multiplier preserves the usual power invariant of the MSB-first scan. -/
theorem msbPowScan_correct
    {A : Type} (repr : A → Nat) (mul : A → A → A) (base : A)
    (modulus : Nat) (hmod : 0 < modulus)
    (hmul : ∀ x y, repr (mul x y) = (repr x * repr y) % modulus)
    (state : MsbPowState A) (bits : List Bool)
    (hinv : repr state.value = repr base ^ state.exponent % modulus) :
    repr (msbPowScan mul base state bits).value =
      repr base ^ (msbPowScan mul base state bits).exponent % modulus := by
  induction bits generalizing state with
  | nil => exact hinv
  | cons bit bits ih =>
    unfold msbPowScan
    apply ih
    dsimp only
    have hr : repr state.value ≡ repr base ^ state.exponent [MOD modulus] := by
      unfold Nat.ModEq
      rw [hinv, Nat.mod_mod]
    have hsquare : repr (mul state.value state.value) ≡
        repr base ^ (2 * state.exponent) [MOD modulus] := by
      rw [hmul]
      have hproduct := (Nat.mod_modEq
        (repr state.value * repr state.value) modulus).trans (hr.mul hr)
      rw [show 2 * state.exponent = state.exponent + state.exponent by omega,
        pow_add]
      exact hproduct
    by_cases hbit : bit = true
    · subst bit
      simp only [ite_true]
      have hnext : repr (mul (mul state.value state.value) base) ≡
          repr base ^ (2 * state.exponent + 1) [MOD modulus] := by
        rw [hmul]
        have hproduct := (Nat.mod_modEq
          (repr (mul state.value state.value) * repr base) modulus).trans
            (hsquare.mul (Nat.ModEq.refl (repr base)))
        simpa [pow_add] using hproduct
      unfold Nat.ModEq at hnext
      have hnextLt : repr (mul (mul state.value state.value) base) < modulus := by
        rw [hmul]
        exact Nat.mod_lt _ hmod
      rw [Nat.mod_eq_of_lt hnextLt] at hnext
      exact hnext
    · have hfalse : bit = false := Bool.eq_false_of_not_eq_true hbit
      subst bit
      simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      unfold Nat.ModEq at hsquare
      have hsquareLt : repr (mul state.value state.value) < modulus := by
        rw [hmul]
        exact Nat.mod_lt _ hmod
      rw [Nat.mod_eq_of_lt hsquareLt] at hsquare
      exact hsquare

/-- The trusted right-to-left kernel is congruent to `acc * base^e` modulo `modulus`. -/
theorem model_modPowAux_modEq (base acc modulus e : Nat) :
    Model.modPowAux base acc modulus e ≡ acc * base ^ e [MOD modulus] := by
  by_cases hzero : e = 0
  · subst e
    simpa [Model.modPowAux] using
      (Nat.ModEq.refl acc : acc ≡ acc [MOD modulus])
  · rw [Model.modPowAux, dif_neg hzero]
    let acc' := if e % 2 = 1 then (acc * base) % modulus else acc
    have ih := model_modPowAux_modEq ((base * base) % modulus) acc' modulus (e / 2)
    apply ih.trans
    unfold acc'
    rcases Nat.mod_two_eq_zero_or_one e with heven | hodd
    · rw [if_neg (by omega : ¬ e % 2 = 1)]
      have hdecomp : e = 2 * (e / 2) := by
        have h := Nat.mod_add_div e 2
        omega
      have hbase : (base * base) % modulus ≡ base ^ 2 [MOD modulus] := by
        simpa [pow_two] using Nat.mod_modEq (base * base) modulus
      have hstep := (Nat.ModEq.refl acc).mul (hbase.pow (e / 2))
      have hp : (base ^ 2) ^ (e / 2) = base ^ e := by
        rw [← pow_mul, show 2 * (e / 2) = e by omega]
      rw [hp] at hstep
      exact hstep
    · rw [if_pos hodd]
      have hdecomp : e = 2 * (e / 2) + 1 := by
        have h := Nat.mod_add_div e 2
        omega
      have hbase : (base * base) % modulus ≡ base ^ 2 [MOD modulus] := by
        simpa [pow_two] using Nat.mod_modEq (base * base) modulus
      have hacc : (acc * base) % modulus ≡ acc * base [MOD modulus] :=
        Nat.mod_modEq _ _
      have hstep := hacc.mul (hbase.pow (e / 2))
      have hp : (acc * base) * (base ^ 2) ^ (e / 2) = acc * base ^ e := by
        calc
          (acc * base) * (base ^ 2) ^ (e / 2) =
              acc * (base ^ (2 * (e / 2)) * base) := by
                rw [← pow_mul]
                ring
          _ = acc * base ^ (2 * (e / 2) + 1) := by
                rw [pow_add, pow_one]
          _ = acc * base ^ e := by
                congr 2
                omega
      rw [hp] at hstep
      exact hstep
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by decide)

/-- The trusted kernel remains reduced when its accumulator starts reduced. -/
theorem model_modPowAux_lt
    {base acc modulus e : Nat} (hmod : 0 < modulus) (hacc : acc < modulus) :
    Model.modPowAux base acc modulus e < modulus := by
  by_cases hzero : e = 0
  · simpa [Model.modPowAux, hzero] using hacc
  · rw [Model.modPowAux, dif_neg hzero]
    apply model_modPowAux_lt hmod
    split
    · exact Nat.mod_lt _ hmod
    · exact hacc
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hzero) (by decide)

/-- For a nontrivial modulus, the unchanged trusted model is ordinary modular exponentiation. -/
theorem model_modPow_eq_pow_mod {base exponent modulus : Nat} (hmod : 1 < modulus) :
    Model.modPow base exponent modulus = base ^ exponent % modulus := by
  unfold Model.modPow
  rw [if_neg (by omega), if_neg (by omega)]
  have hcong := model_modPowAux_modEq (base % modulus) 1 modulus exponent
  have hlt := model_modPowAux_lt (base := base % modulus) (e := exponent)
    (by omega : 0 < modulus) (by omega : 1 < modulus)
  unfold Nat.ModEq at hcong
  rw [Nat.mod_eq_of_lt hlt] at hcong
  rw [hcong]
  simpa only [one_mul] using (Nat.mod_modEq base modulus).pow exponent

theorem model_modPow_mod_base {base exponent modulus : Nat} (hmod : 1 < modulus) :
    Model.modPow (base % modulus) exponent modulus =
      Model.modPow base exponent modulus := by
  rw [model_modPow_eq_pow_mod hmod, model_modPow_eq_pow_mod hmod]
  exact (Nat.mod_modEq base modulus).pow exponent

/-- A completed abstract backend scan computes the trusted model at its consumed exponent. -/
theorem msbPowScan_eq_model
    {A : Type} (repr : A → Nat) (mul : A → A → A) (base one : A)
    (modulus : Nat) (hmod : 1 < modulus)
    (hmul : ∀ x y, repr (mul x y) = (repr x * repr y) % modulus)
    (hone : repr one = 1)
    (bits : List Bool) :
    repr (msbPowScan mul base { value := one, exponent := 0 } bits).value =
      Model.modPow (repr base)
        (msbPowScan mul base { value := one, exponent := 0 } bits).exponent modulus := by
  rw [model_modPow_eq_pow_mod hmod]
  apply msbPowScan_correct repr mul base modulus (by omega) hmul
  simp [hone, Nat.mod_eq_of_lt hmod]

end Modexp
