import Examples.Precompiles.Modexp.MultiLimbBackendModel

/-!
# Pure Montgomery-domain bridge

This file specializes the backend-independent exponent scan to Montgomery multiplication.  It
accounts for conversion into the domain, every square/multiply, and conversion back out.  The
concrete bytecode proof must establish the stated raw multiplication contract for CIOS and SOS.
-/

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Mathematical value represented by a Montgomery-domain object. -/
def montgomeryDecode {A : Type} (raw : A → Nat) (rInv modulus : Nat) (x : A) : Nat :=
  raw x * rInv % modulus

/-- A raw Montgomery multiplication contract becomes ordinary modular multiplication after
decoding. -/
theorem montgomeryDecode_mul
    {A : Type} (raw : A → Nat) (mul : A → A → A) (rInv modulus : Nat)
    (hraw : ∀ x y, raw (mul x y) = (raw x * raw y * rInv) % modulus)
    (x y : A) :
    montgomeryDecode raw rInv modulus (mul x y) =
      (montgomeryDecode raw rInv modulus x * montgomeryDecode raw rInv modulus y) % modulus := by
  have hxy : raw (mul x y) ≡ raw x * raw y * rInv [MOD modulus] := by
    rw [hraw]
    exact Nat.mod_modEq _ _
  have hleft := hxy.mul (Nat.ModEq.refl rInv)
  have hx : montgomeryDecode raw rInv modulus x ≡ raw x * rInv [MOD modulus] := by
    unfold montgomeryDecode
    exact Nat.mod_modEq _ _
  have hy : montgomeryDecode raw rInv modulus y ≡ raw y * rInv [MOD modulus] := by
    unfold montgomeryDecode
    exact Nat.mod_modEq _ _
  have hright := hx.mul hy
  have hmiddle : raw x * raw y * rInv * rInv =
      (raw x * rInv) * (raw y * rInv) := by ring
  rw [hmiddle] at hleft
  have hcong := hleft.trans hright.symm
  unfold Nat.ModEq at hcong
  simpa only [montgomeryDecode] using hcong

/-- Decoding `x*R mod n` recovers `x mod n` when `rInv` is the inverse of `R`. -/
theorem montgomeryDecode_encoded
    {A : Type} (raw : A → Nat) (xM : A) (x R rInv modulus : Nat)
    (hraw : raw xM = x * R % modulus)
    (hinv : R * rInv % modulus = 1 % modulus) :
    montgomeryDecode raw rInv modulus xM = x % modulus := by
  have hR : R * rInv ≡ 1 [MOD modulus] := by
    unfold Nat.ModEq
    simp only [hinv]
  have hx := (Nat.ModEq.refl x).mul hR
  have hencoded : x * R % modulus ≡ x * R [MOD modulus] := Nat.mod_modEq _ _
  have hcong := (hencoded.mul (Nat.ModEq.refl rInv)).trans (by
    simpa [Nat.mul_assoc] using hx)
  unfold Nat.ModEq at hcong
  unfold montgomeryDecode
  rw [hraw]
  exact hcong

/-- The Montgomery representation of one decodes to one for a nontrivial modulus. -/
theorem montgomeryDecode_one
    {A : Type} (raw : A → Nat) (oneM : A) (R rInv modulus : Nat)
    (hmod : 1 < modulus) (hraw : raw oneM = R % modulus)
    (hinv : R * rInv % modulus = 1 % modulus) :
    montgomeryDecode raw rInv modulus oneM = 1 := by
  have h := montgomeryDecode_encoded raw oneM 1 R rInv modulus (by simpa using hraw) hinv
  simpa [Nat.mod_eq_of_lt hmod] using h

/-- The complete Montgomery-domain scan, before conversion out, decodes to the trusted model. -/
theorem montgomeryScan_eq_model
    {A : Type} (raw : A → Nat) (mul : A → A → A)
    (baseM oneM : A) (base R rInv modulus : Nat)
    (hmod : 1 < modulus)
    (hrawMul : ∀ x y, raw (mul x y) = (raw x * raw y * rInv) % modulus)
    (hrawBase : raw baseM = base * R % modulus)
    (hrawOne : raw oneM = R % modulus)
    (hinv : R * rInv % modulus = 1 % modulus)
    (bits : List Bool) :
    montgomeryDecode raw rInv modulus
        (msbPowScan mul baseM { value := oneM, exponent := 0 } bits).value =
      Model.modPow base
        (msbPowScan mul baseM { value := oneM, exponent := 0 } bits).exponent modulus := by
  have hmul := montgomeryDecode_mul raw mul rInv modulus hrawMul
  have hone := montgomeryDecode_one raw oneM R rInv modulus hmod hrawOne hinv
  have hscan := msbPowScan_eq_model
    (montgomeryDecode raw rInv modulus) mul baseM oneM modulus hmod hmul hone bits
  rw [montgomeryDecode_encoded raw baseM base R rInv modulus hrawBase hinv] at hscan
  rw [model_modPow_mod_base hmod] at hscan
  exact hscan

/-- Multiplication by the ordinary value one converts a Montgomery result back to its decoded
natural value. -/
theorem montgomeryConvertOut
    {A : Type} (raw : A → Nat) (mul : A → A → A) (ordinaryOne x : A)
    (rInv modulus : Nat)
    (hrawMul : ∀ a b, raw (mul a b) = (raw a * raw b * rInv) % modulus)
    (hone : raw ordinaryOne = 1) :
    raw (mul x ordinaryOne) = montgomeryDecode raw rInv modulus x := by
  rw [hrawMul, hone]
  simp [montgomeryDecode]

/-- End-to-end pure Montgomery result, including the final conversion out of the domain. -/
theorem montgomeryResult_eq_model
    {A : Type} (raw : A → Nat) (mul : A → A → A)
    (baseM oneM ordinaryOne : A) (base R rInv modulus : Nat)
    (hmod : 1 < modulus)
    (hrawMul : ∀ x y, raw (mul x y) = (raw x * raw y * rInv) % modulus)
    (hrawBase : raw baseM = base * R % modulus)
    (hrawOne : raw oneM = R % modulus)
    (hordinaryOne : raw ordinaryOne = 1)
    (hinv : R * rInv % modulus = 1 % modulus)
    (bits : List Bool) :
    raw (mul (msbPowScan mul baseM { value := oneM, exponent := 0 } bits).value
        ordinaryOne) =
      Model.modPow base
        (msbPowScan mul baseM { value := oneM, exponent := 0 } bits).exponent modulus := by
  rw [montgomeryConvertOut raw mul ordinaryOne _ rInv modulus hrawMul hordinaryOne]
  exact montgomeryScan_eq_model raw mul baseM oneM base R rInv modulus hmod
    hrawMul hrawBase hrawOne hinv bits

end Modexp
