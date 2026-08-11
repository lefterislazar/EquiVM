import Examples.Precompiles.Modexp.MultiLimbMontgomeryArithmetic

/-! # Pure separated-operand-scanning Montgomery squaring model -/

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Contribution of all products strictly above the diagonal of the limb square. -/
def sosOffDiagonal (radix : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => radix * a * limbsToNatAt radix as + radix ^ 2 * sosOffDiagonal radix as

/-- Contribution of the diagonal products `a[i]^2`. -/
def sosDiagonal (radix : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a ^ 2 + radix ^ 2 * sosDiagonal radix as

/-- Upper triangle, doubled, plus the diagonal is the complete mathematical square. -/
theorem sos_square_decompose (radix : Nat) (limbs : List Nat) :
    2 * sosOffDiagonal radix limbs + sosDiagonal radix limbs =
      limbsToNatAt radix limbs ^ 2 := by
  induction limbs with
  | nil => simp [sosOffDiagonal, sosDiagonal, limbsToNatAt]
  | cons a as ih =>
      simp only [sosOffDiagonal, sosDiagonal, limbsToNatAt]
      calc
        2 * (radix * a * limbsToNatAt radix as +
              radix ^ 2 * sosOffDiagonal radix as) +
            (a ^ 2 + radix ^ 2 * sosDiagonal radix as) =
            a ^ 2 + 2 * radix * a * limbsToNatAt radix as +
              radix ^ 2 * (2 * sosOffDiagonal radix as + sosDiagonal radix as) := by ring
        _ = (a + radix * limbsToNatAt radix as) ^ 2 := by rw [ih]; ring

/-- SOS reduction applies the same low-word Montgomery cancellation repeatedly, but starts from
the complete square rather than integrating one multiplier limb per pass. -/
def montgomerySOSScan (radix modulus nInv value steps : Nat) : Nat :=
  montgomeryCIOSScan radix modulus nInv 0 value (List.replicate steps 0)

theorem limbsToNatAt_replicate_zero (radix count : Nat) :
    limbsToNatAt radix (List.replicate count 0) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, limbsToNatAt, ih, Nat.zero_add, Nat.mul_zero]

/-- After `k` concrete reduction passes, multiplication by `radix^k` recovers the original
square modulo the modulus. -/
theorem montgomerySOSScan_modEq
    {radix modulus nInv value steps : Nat}
    (hradix : 1 < radix)
    (hinv : modulus * nInv % radix = radix - 1) :
    radix ^ steps * montgomerySOSScan radix modulus nInv value steps ≡
      value [MOD modulus] := by
  have h := montgomeryCIOSScan_modEq
    (radix := radix) (modulus := modulus) (nInv := nInv)
    (b := 0) (t := value) (as := List.replicate steps 0) hradix hinv
  simpa [montgomerySOSScan, limbsToNatAt_replicate_zero] using h

/-- Complete mathematical SOS contract once the concrete reduction trace supplies its standard
`< 2n` output bound. -/
theorem montgomerySOS_contract
    {radix modulus nInv rInv a value steps : Nat}
    (hradix : 1 < radix) (hmodulus : 0 < modulus)
    (hinv0 : modulus * nInv % radix = radix - 1)
    (hvalue : value = a ^ 2)
    (hinvR : radix ^ steps * rInv % modulus = 1 % modulus)
    (hbound : montgomerySOSScan radix modulus nInv value steps < 2 * modulus) :
    montgomeryFinalize (montgomerySOSScan radix modulus nInv value steps) modulus =
      (a * a * rInv) % modulus := by
  subst value
  rw [montgomeryFinalize_eq_mod hmodulus hbound]
  have hscan := montgomerySOSScan_modEq
    (radix := radix) (modulus := modulus) (nInv := nInv)
    (value := a ^ 2) (steps := steps) hradix hinv0
  have hcancel := montgomery_cancel_radix hinvR hscan
  simpa [pow_two] using hcancel

/-- The source-level upper-triangle, doubling, and diagonal phases feed exactly the SOS reduction
target used by `montgomerySOS_contract`. -/
theorem sos_phases_value (radix : Nat) (limbs : List Nat) :
    2 * sosOffDiagonal radix limbs + sosDiagonal radix limbs =
      limbsToNatAt radix limbs * limbsToNatAt radix limbs := by
  simpa [pow_two] using sos_square_decompose radix limbs

end Modexp
