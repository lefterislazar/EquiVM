import Examples.Precompiles.Modexp.MultiLimbSchoolbookQhatSemantic

/-!
# Arbitrary-length schoolbook division semantics

This module states the outer Knuth loop as a most-significant-digit-first radix fold.  Each
accepted bytecode window supplies one exact quotient digit and a reduced remainder; the fold then
reconstructs ordinary natural-number division and remainder for an arbitrary number of limbs.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookOuterSemantic

open Modexp.MultiLimbSchoolbookDivisionSemantic

set_option maxRecDepth 50000
set_option maxHeartbeats 0

/-- Natural value of digits supplied most significant first. -/
def digitsToNatMSB (radix : Nat) : List Nat → Nat
  | [] => 0
  | digit :: digits =>
      digit * radix ^ digits.length + digitsToNatMSB radix digits

theorem digitsToNatMSB_append (radix : Nat) (left right : List Nat) :
    digitsToNatMSB radix (left ++ right) =
      digitsToNatMSB radix left * radix ^ right.length +
        digitsToNatMSB radix right := by
  induction left with
  | nil => simp [digitsToNatMSB]
  | cons digit left ih =>
      simp only [List.cons_append, digitsToNatMSB, List.length_append,
        List.length_cons, pow_add, ih]
      ring

/-- Reversing little-endian EVM words gives the MSB-first value consumed by the outer fold. -/
theorem digitsToNatMSB_reverse_words (words : List UInt256) :
    digitsToNatMSB UInt256.size (words.reverse.map UInt256.toNat) =
      Modexp.wordLimbsToNat words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      rw [List.reverse_cons, List.map_append, digitsToNatMSB_append]
      simp only [List.map_singleton, digitsToNatMSB, List.length_singleton, pow_one,
        List.length_nil, pow_zero, Nat.mul_zero, Nat.add_zero, ih,
        Modexp.wordLimbsToNat]
      ring

structure DivisionFoldState where
  quotient : Nat
  remainder : Nat

/-- One ordinary long-division digit transition. -/
def divisionDigitStep (radix divisor digit : Nat)
    (state : DivisionFoldState) : DivisionFoldState :=
  let window := state.remainder * radix + digit
  {
    quotient := state.quotient * radix + window / divisor
    remainder := window % divisor
  }

/-- Process an arbitrary most-significant-first digit list. -/
def divisionDigits (radix divisor : Nat) :
    DivisionFoldState → List Nat → DivisionFoldState
  | state, [] => state
  | state, digit :: digits =>
      divisionDigits radix divisor (divisionDigitStep radix divisor digit state) digits

theorem divisionDigitStep_recompose
    (radix divisor digit value : Nat) (state : DivisionFoldState)
    (hdivisor : 0 < divisor)
    (hinvariant : value = state.quotient * divisor + state.remainder) :
    value * radix + digit =
      (divisionDigitStep radix divisor digit state).quotient * divisor +
        (divisionDigitStep radix divisor digit state).remainder := by
  have hdivision := Nat.mod_add_div
    (state.remainder * radix + digit) divisor
  simp only [divisionDigitStep]
  rw [hinvariant]
  nlinarith

theorem divisionDigitStep_remainder_lt
    (radix divisor digit : Nat) (state : DivisionFoldState)
    (hdivisor : 0 < divisor) :
    (divisionDigitStep radix divisor digit state).remainder < divisor := by
  simp only [divisionDigitStep]
  exact Nat.mod_lt _ hdivisor

/-- The radix fold preserves the quotient/remainder reconstruction equation across every digit. -/
theorem divisionDigits_recompose
    (radix divisor value : Nat) (state : DivisionFoldState) (digits : List Nat)
    (hdivisor : 0 < divisor)
    (hinvariant : value = state.quotient * divisor + state.remainder) :
    value * radix ^ digits.length + digitsToNatMSB radix digits =
      (divisionDigits radix divisor state digits).quotient * divisor +
        (divisionDigits radix divisor state digits).remainder := by
  induction digits generalizing state value with
  | nil => simpa [divisionDigits, digitsToNatMSB] using hinvariant
  | cons digit digits ih =>
      have hstep := divisionDigitStep_recompose radix divisor digit value state
        hdivisor hinvariant
      have hrest := ih (value * radix + digit)
        (divisionDigitStep radix divisor digit state) hstep
      simp only [divisionDigits, digitsToNatMSB, List.length_cons, pow_succ]
      rw [← hrest]
      ring

theorem divisionDigits_remainder_lt
    (radix divisor : Nat) (state : DivisionFoldState) (digits : List Nat)
    (hdivisor : 0 < divisor)
    (hinitial : state.remainder < divisor) :
    (divisionDigits radix divisor state digits).remainder < divisor := by
  induction digits generalizing state with
  | nil => simpa [divisionDigits] using hinitial
  | cons digit digits ih =>
      exact ih (divisionDigitStep radix divisor digit state)
        (divisionDigitStep_remainder_lt radix divisor digit state hdivisor)

/-- A reconstruction with a reduced remainder uniquely determines ordinary division. -/
theorem quotient_eq_div_of_recompose
    {value quotient remainder divisor : Nat}
    (hdivisor : 0 < divisor)
    (hrecompose : value = quotient * divisor + remainder)
    (hremainder : remainder < divisor) :
    quotient = value / divisor := by
  subst value
  rw [Nat.mul_comm quotient divisor, Nat.mul_add_div hdivisor,
    Nat.div_eq_of_lt hremainder, Nat.add_zero]

/-- A reconstruction with a reduced remainder uniquely determines ordinary remainder. -/
theorem remainder_eq_mod_of_recompose
    {value quotient remainder divisor : Nat}
    (hdivisor : 0 < divisor)
    (hrecompose : value = quotient * divisor + remainder)
    (hremainder : remainder < divisor) :
    remainder = value % divisor := by
  subst value
  simp [Nat.mul_comm quotient divisor, Nat.add_mod, Nat.mod_eq_of_lt hremainder]

/-- Starting at zero, arbitrary many long-division digits compute exact `Nat.div` and `Nat.mod`. -/
theorem divisionDigits_eq_div_mod
    (radix divisor : Nat) (digits : List Nat)
    (hdivisor : 0 < divisor) :
    let final := divisionDigits radix divisor ⟨0, 0⟩ digits
    final.quotient = digitsToNatMSB radix digits / divisor ∧
      final.remainder = digitsToNatMSB radix digits % divisor := by
  let final := divisionDigits radix divisor ⟨0, 0⟩ digits
  have hrecompose := divisionDigits_recompose radix divisor 0 ⟨0, 0⟩ digits
    hdivisor (by simp)
  have hremainder := divisionDigits_remainder_lt radix divisor ⟨0, 0⟩ digits
    hdivisor (by simpa using hdivisor)
  simp only [zero_mul, zero_add] at hrecompose
  constructor
  · exact quotient_eq_div_of_recompose hdivisor hrecompose hremainder
  · exact remainder_eq_mod_of_recompose hdivisor hrecompose hremainder

/-- Any accepted bytecode window is the unique natural quotient digit and remainder for that
window.  This is the local bridge consumed by the outer fold. -/
theorem acceptedWindow_eq_div_mod
    {window divisor quotient remainder : Nat}
    (hdivisor : 0 < divisor)
    (hrecompose : remainder + quotient * divisor = window)
    (hremainder : remainder < divisor) :
    quotient = window / divisor ∧ remainder = window % divisor := by
  have hrecompose' : window = quotient * divisor + remainder := by
    rw [← hrecompose]
    omega
  exact ⟨quotient_eq_div_of_recompose hdivisor hrecompose' hremainder,
    remainder_eq_mod_of_recompose hdivisor hrecompose' hremainder⟩

def acceptedWindowResult
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256) :
    Nat × Nat :=
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  if subtracted.negative = ⟨0⟩ then
    (qHat.toNat, windowNat subtracted.lower subtracted.top)
  else
    let corrected := knuthAddBack subtracted.lower vDigits subtracted.top
    (qHat.toNat - 1, windowNat corrected.lower corrected.top)

/-- The complete multiply-subtract and optional correction computation is exactly one natural
division digit. -/
theorem knuthAcceptedWindow_eq_div_mod
    (qHat : UInt256) (uLower vDigits : List UInt256) (uTop : UInt256)
    (hlength : uLower.length = vDigits.length)
    (hdivisorPos : 0 < Modexp.wordLimbsToNat vDigits)
    (hnotLow :
      windowNat uLower uTop <
        (qHat.toNat + 1) * Modexp.wordLimbsToNat vDigits)
    (hatMostOne :
      qHat.toNat * Modexp.wordLimbsToNat vDigits ≤
        windowNat uLower uTop + Modexp.wordLimbsToNat vDigits) :
    (acceptedWindowResult qHat uLower vDigits uTop).1 =
        windowNat uLower uTop / Modexp.wordLimbsToNat vDigits ∧
      (acceptedWindowResult qHat uLower vDigits uTop).2 =
        windowNat uLower uTop % Modexp.wordLimbsToNat vDigits := by
  have haccepted := knuthAcceptedWindow qHat uLower vDigits uTop hlength
    hdivisorPos hnotLow hatMostOne
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  by_cases hnegative : subtracted.negative = ⟨0⟩
  · rw [if_pos hnegative] at haccepted
    have hresult := acceptedWindow_eq_div_mod hdivisorPos haccepted.1 haccepted.2
    simpa [acceptedWindowResult, subtracted, hnegative] using hresult
  · rw [if_neg hnegative] at haccepted
    have hresult := acceptedWindow_eq_div_mod hdivisorPos haccepted.1 haccepted.2
    simpa [acceptedWindowResult, subtracted, hnegative] using hresult

/-- The arbitrary word list specialization computes ordinary division and remainder of its
little-endian natural value. -/
theorem divisionWords_eq_div_mod
    (divisor : Nat) (words : List UInt256) (hdivisor : 0 < divisor) :
    let final := divisionDigits UInt256.size divisor ⟨0, 0⟩
      (words.reverse.map UInt256.toNat)
    final.quotient = Modexp.wordLimbsToNat words / divisor ∧
      final.remainder = Modexp.wordLimbsToNat words % divisor := by
  have hresult := divisionDigits_eq_div_mod UInt256.size divisor
    (words.reverse.map UInt256.toNat) hdivisor
  simpa only [digitsToNatMSB_reverse_words] using hresult

end Modexp.MultiLimbSchoolbookOuterSemantic
