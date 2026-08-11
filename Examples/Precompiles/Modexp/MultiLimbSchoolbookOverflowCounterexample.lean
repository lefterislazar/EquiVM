import Examples.Precompiles.Modexp.MultiLimbBackendModel

/-!
# Reachable checked-add overflow in schoolbook division

These constants describe an aligned public ModExp input with declared base, exponent, and modulus
lengths `96`, `1`, and `64`.  The first schoolbook quotient digit leaves `modulus - 1` as the
current remainder.  The next saturated estimate therefore evaluates `uLo + vTop = 2^256` at
`LimbMath.sol:303`, which Solidity compiles as a checked addition.

SymCheck reaches the arithmetic-panic block at PC 1022 from this input without overapproximation or
SMT weakening.  The pure facts below record that the input is in range and that the trusted model
has a non-reverting, concrete result.
-/

namespace Modexp.MultiLimbSchoolbookOverflowCounterexample

def radix : Nat := 2 ^ 256
def halfRadix : Nat := 2 ^ 255

def base : Nat := halfRadix * radix ^ 2 + halfRadix * radix
def exponent : Nat := 1
def modulus : Nat := halfRadix * radix + (halfRadix + 1)
def expected : Nat := (halfRadix - 1) * radix + (halfRadix + 1)

/-- The values occupy exactly three base limbs and two modulus limbs. -/
theorem aligned_operand_ranges :
    256 ^ 64 ≤ base ∧ base < 256 ^ 96 ∧
      256 ^ 32 ≤ modulus ∧ modulus < 256 ^ 64 := by
  native_decide

/-- The input selects the nontrivial odd-modulus backend. -/
theorem modulus_nontrivial_odd : 1 < modulus ∧ modulus % 2 = 1 := by
  native_decide

/-- The saturated estimate's source-level addition overflows one EVM word. -/
theorem saturated_estimate_sum : halfRadix + halfRadix = radix := by
  native_decide

/-- With exponent one, the trusted model returns `base % modulus = modulus - radix`. -/
theorem trusted_model_result : Model.modPow base exponent modulus = expected := by
  native_decide

end Modexp.MultiLimbSchoolbookOverflowCounterexample
