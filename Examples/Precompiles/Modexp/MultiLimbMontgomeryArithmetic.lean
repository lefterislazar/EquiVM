import Examples.Precompiles.Modexp.MultiLimbMontgomeryModel
import Examples.Precompiles.Modexp.MultiLimbMultiplicationRowsModel

/-!
# CIOS Montgomery arithmetic

This is the unbounded recurrence implemented by the generated CIOS passes.  Trace-level loop
proofs only need to establish each recurrence step and its standard bound.
-/

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def montgomeryFactor (radix nInv x : Nat) : Nat :=
  (x % radix * nInv) % radix

def montgomeryCIOSStep (radix modulus nInv b t ai : Nat) : Nat :=
  (t + ai * b + montgomeryFactor radix nInv (t + ai * b) * modulus) / radix

def montgomeryCIOSScan (radix modulus nInv b : Nat) : Nat → List Nat → Nat
  | t, [] => t
  | t, ai :: as =>
      montgomeryCIOSScan radix modulus nInv b
        (montgomeryCIOSStep radix modulus nInv b t ai) as

/-- Exact algebra joining the deployed multiply columns, peeled low reduction column, remaining
reduction columns, and upper shift.  No modular reasoning is used here: the conclusion is the
unbounded numerator equation for one complete CIOS iteration. -/
theorem montgomeryCIOS_columns_recompose
    {radix q priorLow t0 ai b mulLowHigher mulCarry tk tk1 tkNew tk1New
      factor n0 nHigher reductionCarry0 reductionOut reductionCarryFinal
      shiftedTop newTop : Nat}
    (hmultiply :
      t0 + radix * mulLowHigher + radix ^ (q + 1) * mulCarry =
        priorLow + ai * b)
    (hmultiplyUpper : tkNew + radix * tk1New = tk + mulCarry + radix * tk1)
    (hpeeled : radix * reductionCarry0 =
      t0 + factor * n0)
    (hreduction : reductionOut + radix ^ q * reductionCarryFinal =
      mulLowHigher + factor * nHigher + reductionCarry0)
    (hshift : shiftedTop + radix * newTop =
      tkNew + reductionCarryFinal + radix * tk1New) :
    radix *
        (reductionOut + radix ^ q * shiftedTop + radix ^ (q + 1) * newTop) =
      (priorLow + radix ^ (q + 1) * tk + radix ^ (q + 2) * tk1) + ai * b +
        factor * (n0 + radix * nHigher) := by
  have hradixPow : radix ^ (q + 1) = radix ^ q * radix := by
    rw [pow_succ]
  have hradixPow2 : radix ^ (q + 2) = radix ^ (q + 1) * radix := by
    rw [pow_succ]
  have hmultiplyUpperScaled := congrArg
    (fun value => radix ^ (q + 1) * value) hmultiplyUpper
  have hreductionScaled := congrArg (fun value => radix * value) hreduction
  have hshiftScaled := congrArg (fun value => radix ^ (q + 1) * value) hshift
  ring_nf at hmultiply hpeeled hmultiplyUpperScaled hreductionScaled hshiftScaled ⊢
  omega

/-- The low-word inverse condition makes every CIOS numerator divisible by the radix. -/
theorem montgomeryFactor_divides
    {radix modulus nInv x : Nat} (hradix : 1 < radix)
    (hinv : modulus * nInv % radix = radix - 1) :
    radix ∣ x + montgomeryFactor radix nInv x * modulus := by
  have hpos : 0 < radix := by omega
  have hinvEq : modulus * nInv ≡ radix - 1 [MOD radix] := by
    unfold Nat.ModEq
    rw [hinv, Nat.mod_eq_of_lt (by omega)]
  have hinvEq' : nInv * modulus ≡ radix - 1 [MOD radix] := by
    simpa [Nat.mul_comm] using hinvEq
  have hm : montgomeryFactor radix nInv x ≡ (x % radix) * nInv [MOD radix] := by
    unfold montgomeryFactor
    exact Nat.mod_modEq _ _
  have hx : x % radix ≡ x [MOD radix] := Nat.mod_modEq _ _
  have hmn := hm.mul (Nat.ModEq.refl modulus)
  have hmn' : montgomeryFactor radix nInv x * modulus ≡
      x * (radix - 1) [MOD radix] := by
    apply hmn.trans
    have hp := (Nat.ModEq.refl (x % radix)).mul hinvEq'
    have hx' := hx.mul (Nat.ModEq.refl (radix - 1))
    simpa [Nat.mul_assoc] using hp.trans hx'
  have hsum : x + montgomeryFactor radix nInv x * modulus ≡
      x + x * (radix - 1) [MOD radix] :=
    (Nat.ModEq.refl x).add hmn'
  have hmultiple : x + x * (radix - 1) = x * radix := by
    calc
      x + x * (radix - 1) = x * ((radix - 1) + 1) := by ring
      _ = x * radix := by congr 1; omega
  rw [hmultiple] at hsum
  have hzero : x * radix ≡ 0 [MOD radix] := by
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_left radix x)
  have hz := hsum.trans hzero
  exact Nat.modEq_zero_iff_dvd.mp hz

/-- Exact, non-modular equation for one CIOS division step. -/
theorem montgomeryCIOSStep_scale
    {radix modulus nInv b t ai : Nat} (hradix : 1 < radix)
    (hinv : modulus * nInv % radix = radix - 1) :
    radix * montgomeryCIOSStep radix modulus nInv b t ai =
      t + ai * b +
        montgomeryFactor radix nInv (t + ai * b) * modulus := by
  unfold montgomeryCIOSStep
  have hdvd := montgomeryFactor_divides (x := t + ai * b) hradix hinv
  exact Nat.mul_div_cancel' hdvd

/-- One CIOS word step preserves the standard `t < modulus + b` bound. -/
theorem montgomeryCIOSStep_lt_sum
    {radix modulus nInv b t ai : Nat}
    (hradix : 1 < radix) (hmodulus : 0 < modulus)
    (hai : ai < radix) (ht : t < modulus + b) :
    montgomeryCIOSStep radix modulus nInv b t ai < modulus + b := by
  have hradixPos : 0 < radix := by omega
  have hfactor : montgomeryFactor radix nInv (t + ai * b) < radix := by
    exact Nat.mod_lt _ hradixPos
  have haiLe : ai ≤ radix - 1 := by omega
  have hfactorLe : montgomeryFactor radix nInv (t + ai * b) ≤ radix - 1 := by
    omega
  have haiMul : ai * b ≤ (radix - 1) * b :=
    Nat.mul_le_mul_right b haiLe
  have hfactorMul :
      montgomeryFactor radix nInv (t + ai * b) * modulus ≤
        (radix - 1) * modulus :=
    Nat.mul_le_mul_right modulus hfactorLe
  unfold montgomeryCIOSStep
  rw [Nat.div_lt_iff_lt_mul hradixPos]
  calc
    t + ai * b + montgomeryFactor radix nInv (t + ai * b) * modulus <
        (modulus + b) + (radix - 1) * b + (radix - 1) * modulus := by
      omega
    _ = (modulus + b) * ((radix - 1) + 1) := by ring
    _ = (modulus + b) * radix := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ radix)]

/-- A zero-multiplier REDC step lowers the remaining radix exponent while preserving the
`modulus * (radix^remaining + 1)` bound.  This is the intermediate SOS reduction invariant. -/
theorem montgomeryCIOSStep_zero_lt_mul_pow_add_one
    {radix modulus nInv t remaining : Nat}
    (hradix : 1 < radix) (hremaining : 0 < remaining)
    (ht : t < modulus * (radix ^ remaining + 1)) :
    montgomeryCIOSStep radix modulus nInv 0 t 0 <
      modulus * (radix ^ (remaining - 1) + 1) := by
  have hradixPos : 0 < radix := by omega
  have hfactor : montgomeryFactor radix nInv t < radix := by
    exact Nat.mod_lt _ hradixPos
  have hfactorLe : montgomeryFactor radix nInv t ≤ radix - 1 := by omega
  have hfactorMul : montgomeryFactor radix nInv t * modulus ≤
      (radix - 1) * modulus := Nat.mul_le_mul_right modulus hfactorLe
  have hpow : radix ^ remaining = radix ^ (remaining - 1) * radix := by
    calc
      radix ^ remaining = radix ^ ((remaining - 1) + 1) := by congr 1 <;> omega
      _ = radix ^ (remaining - 1) * radix := by rw [pow_succ]
  unfold montgomeryCIOSStep
  simp only [Nat.zero_mul, add_zero]
  rw [Nat.div_lt_iff_lt_mul hradixPos]
  calc
    t + montgomeryFactor radix nInv t * modulus <
        modulus * (radix ^ remaining + 1) + (radix - 1) * modulus := by omega
    _ = modulus * (radix ^ (remaining - 1) + 1) * radix := by
      rw [hpow]
      have hsub : radix - 1 + 1 = radix := Nat.sub_add_cancel (by omega)
      calc
        modulus * (radix ^ (remaining - 1) * radix + 1) +
            (radix - 1) * modulus =
            modulus * radix ^ (remaining - 1) * radix +
              (radix - 1 + 1) * modulus := by ring
        _ = modulus * radix ^ (remaining - 1) * radix + radix * modulus := by
          rw [hsub]
        _ = modulus * (radix ^ (remaining - 1) + 1) * radix := by ring

/-- Starting below `modulus + b`, every low-to-high CIOS step stays below that same bound. -/
theorem montgomeryCIOSScan_lt_sum
    {radix modulus nInv b t : Nat} (as : List Nat)
    (hradix : 1 < radix) (hmodulus : 0 < modulus)
    (hdigits : ∀ ai ∈ as, ai < radix)
    (ht : t < modulus + b) :
    montgomeryCIOSScan radix modulus nInv b t as < modulus + b := by
  induction as generalizing t with
  | nil => simpa [montgomeryCIOSScan] using ht
  | cons ai as ih =>
      have hai : ai < radix := hdigits ai (by simp)
      have htail : ∀ aj ∈ as, aj < radix := by
        intro aj haj
        exact hdigits aj (by simp [haj])
      exact ih htail (montgomeryCIOSStep_lt_sum hradix hmodulus hai ht)

/-- For a reduced multiplier, a zero-start CIOS scan has the `< 2n` bound needed by its single
final conditional subtraction. -/
theorem montgomeryCIOSScan_lt_two_mul
    {radix modulus nInv b : Nat} (as : List Nat)
    (hradix : 1 < radix) (hmodulus : 0 < modulus)
    (hdigits : ∀ ai ∈ as, ai < radix) (hb : b < modulus) :
    montgomeryCIOSScan radix modulus nInv b 0 as < 2 * modulus := by
  have hsum := montgomeryCIOSScan_lt_sum (nInv := nInv) as hradix hmodulus hdigits
    (by omega : 0 < modulus + b)
  omega

/-- Scanning low-to-high limbs accumulates the Montgomery congruence at the corresponding radix
power. -/
theorem montgomeryCIOSScan_modEq
    {radix modulus nInv b t : Nat} (as : List Nat)
    (hradix : 1 < radix)
    (hinv : modulus * nInv % radix = radix - 1) :
    radix ^ as.length * montgomeryCIOSScan radix modulus nInv b t as ≡
      t + limbsToNatAt radix as * b [MOD modulus] := by
  induction as generalizing t with
  | nil =>
      simpa [montgomeryCIOSScan, limbsToNatAt] using
        (Nat.ModEq.refl t : t ≡ t [MOD modulus])
  | cons ai as ih =>
      let next := montgomeryCIOSStep radix modulus nInv b t ai
      have hstep := montgomeryCIOSStep_scale
        (radix := radix) (modulus := modulus) (nInv := nInv)
        (b := b) (t := t) (ai := ai) hradix hinv
      have hstepMod : radix * next ≡ t + ai * b [MOD modulus] := by
        rw [hstep]
        have hz : montgomeryFactor radix nInv (t + ai * b) * modulus ≡
            0 [MOD modulus] := by
          exact Nat.modEq_zero_iff_dvd.mpr
            (dvd_mul_left modulus (montgomeryFactor radix nInv (t + ai * b)))
        simpa using (Nat.ModEq.refl (t + ai * b)).add hz
      have htail := ih (t := next)
      have hscaled := htail.mul (Nat.ModEq.refl radix)
      have hscaled' : radix ^ (as.length + 1) *
            montgomeryCIOSScan radix modulus nInv b next as ≡
          radix * next + radix * (limbsToNatAt radix as * b) [MOD modulus] := by
        simpa [pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
          Nat.mul_left_comm] using hscaled
      have hreplace := hstepMod.add
        (Nat.ModEq.refl (radix * (limbsToNatAt radix as * b)))
      simpa [montgomeryCIOSScan, limbsToNatAt, next, List.length_cons,
        pow_succ, Nat.mul_add, Nat.mul_assoc, Nat.add_mul, Nat.add_assoc] using
        hscaled'.trans hreplace

def montgomeryFinalize (value modulus : Nat) : Nat :=
  if modulus ≤ value then value - modulus else value

/-- The source's single final subtraction is ordinary reduction under the CIOS `< 2n` bound. -/
theorem montgomeryFinalize_eq_mod
    {value modulus : Nat} (hmodulus : 0 < modulus) (hbound : value < 2 * modulus) :
    montgomeryFinalize value modulus = value % modulus := by
  unfold montgomeryFinalize
  by_cases hge : modulus ≤ value
  · rw [if_pos hge, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt]
    omega
  · rw [if_neg hge, Nat.mod_eq_of_lt (by omega)]

/-- Cancel the Montgomery radix using its inverse modulo the modulus. -/
theorem montgomery_cancel_radix
    {radixPower rInv value product modulus : Nat}
    (hinv : radixPower * rInv % modulus = 1 % modulus)
    (hscaled : radixPower * value ≡ product [MOD modulus]) :
    value % modulus = product * rInv % modulus := by
  have hR : radixPower * rInv ≡ 1 [MOD modulus] := by
    unfold Nat.ModEq
    simpa using hinv
  have hmul := hscaled.mul (Nat.ModEq.refl rInv)
  have hcancel := (Nat.ModEq.refl value).mul hR
  have hmul' : value * (radixPower * rInv) ≡ product * rInv [MOD modulus] := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hresult : value ≡ product * rInv [MOD modulus] := by
    have hone : value ≡ value * (radixPower * rInv) [MOD modulus] := by
      simpa using hcancel.symm
    exact hone.trans hmul'
  exact hresult

/-- Complete CIOS contract from the inverse condition and standard output bound. -/
theorem montgomeryCIOS_contract
    {radix modulus nInv rInv a b : Nat} {as : List Nat}
    (hradix : 1 < radix) (hmodulus : 0 < modulus)
    (hinv0 : modulus * nInv % radix = radix - 1)
    (ha : limbsToNatAt radix as = a)
    (hinvR : radix ^ as.length * rInv % modulus = 1 % modulus)
    (hbound : montgomeryCIOSScan radix modulus nInv b 0 as < 2 * modulus) :
    montgomeryFinalize (montgomeryCIOSScan radix modulus nInv b 0 as) modulus =
      (a * b * rInv) % modulus := by
  rw [montgomeryFinalize_eq_mod hmodulus hbound]
  have hscan := montgomeryCIOSScan_modEq (b := b) (t := 0) as hradix hinv0
  simp only [zero_add, ha] at hscan
  rw [montgomery_cancel_radix hinvR hscan]

/-- Complete CIOS contract with the output bound discharged from reduced-input and digit bounds. -/
theorem montgomeryCIOS_contract_of_reduced
    {radix modulus nInv rInv a b : Nat} {as : List Nat}
    (hradix : 1 < radix) (hmodulus : 0 < modulus)
    (hinv0 : modulus * nInv % radix = radix - 1)
    (ha : limbsToNatAt radix as = a)
    (hinvR : radix ^ as.length * rInv % modulus = 1 % modulus)
    (hdigits : ∀ ai ∈ as, ai < radix) (hb : b < modulus) :
    montgomeryFinalize (montgomeryCIOSScan radix modulus nInv b 0 as) modulus =
      (a * b * rInv) % modulus := by
  exact montgomeryCIOS_contract hradix hmodulus hinv0 ha hinvR
    (montgomeryCIOSScan_lt_two_mul as hradix hmodulus hdigits hb)

end Modexp
