import Examples.Precompiles.Modexp.MultiLimbSubtractionModel

/-!
# Multi-limb schoolbook multiplication model

This lifts the exact generated inner-word update through one arbitrary schoolbook row.  It is the
pure arithmetic invariant consumed by both wide modular-arithmetic backends.
-/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Apply one multiplier limb across equal-length operand and result slices. -/
def evmSchoolbookRow (a : UInt256) :
    List UInt256 → List UInt256 → UInt256 → List UInt256 × UInt256
  | [], _, carry => ([], carry)
  | _ :: _, [], carry => ([], carry)
  | b :: bs, result :: results, carry =>
      let digit := evmSchoolbookStep a b result carry
      let rest := evmSchoolbookRow a bs results digit.2
      (digit.1 :: rest.1, rest.2)

theorem evmSchoolbookRow_result_length
    (a : UInt256) (bs results : List UInt256) (carry : UInt256)
    (hlength : bs.length = results.length) :
    (evmSchoolbookRow a bs results carry).1.length = bs.length := by
  induction bs generalizing results carry with
  | nil => simp [evmSchoolbookRow]
  | cons b bs ih =>
      cases results with
      | nil => simp at hlength
      | cons result results =>
          have htail : bs.length = results.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          simp [evmSchoolbookRow,
            ih results (evmSchoolbookStep a b result carry).2 htail]

/-- One arbitrary schoolbook row preserves the full unbounded radix value. -/
theorem evmSchoolbookRow_recompose
    (a : UInt256) (bs results : List UInt256) (carry : UInt256)
    (hlength : bs.length = results.length) :
    let output := evmSchoolbookRow a bs results carry
    wordLimbsToNat output.1 + UInt256.size ^ bs.length * output.2.toNat =
      wordLimbsToNat results + a.toNat * wordLimbsToNat bs + carry.toNat := by
  induction bs generalizing results carry with
  | nil =>
      have hresults : results = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst results
      simp [evmSchoolbookRow, wordLimbsToNat]
  | cons b bs ih =>
      cases results with
      | nil => simp at hlength
      | cons result results =>
          have htail : bs.length = results.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          let digit := evmSchoolbookStep a b result carry
          let rest := evmSchoolbookRow a bs results digit.2
          have hdigit := evmSchoolbookStep_recompose a b result carry
          have hrest := ih results digit.2 htail
          have hscaled := congrArg (fun x => UInt256.size * x) hrest
          dsimp only [digit, rest] at hdigit hrest hscaled ⊢
          simp only [evmSchoolbookRow, wordLimbsToNat, List.length_cons, pow_succ,
            Nat.mul_add, Nat.mul_assoc] at hscaled ⊢
          ring_nf at hscaled ⊢
          omega

/-- Row correctness in the shared `limbsToNat` representation. -/
theorem evmSchoolbookRow_recompose_limbsToNat
    (a : UInt256) (bs results : List UInt256) (carry : UInt256)
    (hlength : bs.length = results.length) :
    let output := evmSchoolbookRow a bs results carry
    limbsToNat (output.1.map UInt256.toNat) +
        (256 ^ 32) ^ bs.length * output.2.toNat =
      limbsToNat (results.map UInt256.toNat) +
        a.toNat * limbsToNat (bs.map UInt256.toNat) + carry.toNat := by
  have h := evmSchoolbookRow_recompose a bs results carry hlength
  dsimp only at h ⊢
  rw [← wordLimbsToNat_eq_limbsToNat, ← wordLimbsToNat_eq_limbsToNat,
    ← wordLimbsToNat_eq_limbsToNat]
  have hbase : 256 ^ 32 = UInt256.size := by
    norm_num [UInt256.size, pow_mul]
  rw [hbase]
  exact h

end Modexp
