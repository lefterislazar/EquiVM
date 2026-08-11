import Examples.Precompiles.Modexp.MultiLimbBackendModel
import Examples.Precompiles.Modexp.WordLoopBridge
import Reasoning.EVMWord

/-!
# Shared multi-limb arithmetic identities

The Solidity backends recover the high half of a 256-by-256-bit product from `MUL` and
`MULMOD(2^256 - 1)`.  This file proves that recovery formula before it is lifted through the
schoolbook, Barrett, and Montgomery loops.
-/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Natural-number form of solc's borrow-corrected high-product recovery. -/
def mulHighRecoveredAt (wordBase a b : Nat) : Nat :=
  let lo := a * b % wordBase
  let mmr := a * b % (wordBase - 1)
  if mmr < lo then wordBase + mmr - lo - 1 else mmr - lo

/-- `MULMOD(wordBase - 1)` and one borrow recover the quotient by `wordBase` for word-sized
operands.  The strict product bound is what excludes the otherwise ambiguous all-ones quotient. -/
theorem mulHighRecoveredAt_eq_div
    {wordBase a b : Nat} (hbase : 2 < wordBase) (ha : a < wordBase) (hb : b < wordBase) :
    mulHighRecoveredAt wordBase a b = a * b / wordBase := by
  let p := a * b
  let q := p / wordBase
  let lo := p % wordBase
  let mmr := p % (wordBase - 1)
  have hbasePos : 0 < wordBase := by omega
  have hmodPos : 0 < wordBase - 1 := by omega
  have hpBound : p < wordBase * (wordBase - 1) := by
    calc
      p = a * b := rfl
      _ ≤ (wordBase - 1) * (wordBase - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ < wordBase * (wordBase - 1) :=
        Nat.mul_lt_mul_of_pos_right (by omega) hmodPos
  have hq : q < wordBase - 1 := by
    dsimp [q]
    rw [Nat.div_lt_iff_lt_mul hbasePos]
    simpa [Nat.mul_comm] using hpBound
  have hlo : lo < wordBase := by
    exact Nat.mod_lt _ hbasePos
  have hp : lo + wordBase * q = p := by
    simpa [lo, q] using Nat.mod_add_div p wordBase
  have hmmr : mmr = (lo + q) % (wordBase - 1) := by
    dsimp [mmr]
    rw [← hp]
    have hbaseDecomp : wordBase = (wordBase - 1) + 1 := by omega
    rw [hbaseDecomp]
    simp [Nat.add_mul, Nat.add_mod, Nat.add_comm, Nat.add_left_comm]
  have hsum : lo + q < 2 * (wordBase - 1) := by omega
  unfold mulHighRecoveredAt
  change (if mmr < lo then wordBase + mmr - lo - 1 else mmr - lo) = q
  by_cases hwrap : wordBase - 1 ≤ lo + q
  · have hmmrValue : mmr = lo + q - (wordBase - 1) := by
      rw [hmmr, Nat.mod_eq_sub_mod hwrap, Nat.mod_eq_of_lt (by omega)]
    have hmmrLt : mmr < lo := by omega
    rw [if_pos hmmrLt, hmmrValue]
    omega
  · have hsumLt : lo + q < wordBase - 1 := by omega
    have hmmrValue : mmr = lo + q := by
      rw [hmmr, Nat.mod_eq_of_lt hsumLt]
    have hmmrNotLt : ¬ mmr < lo := by
      rw [hmmrValue]
      exact Nat.not_lt_of_ge (Nat.le_add_right lo q)
    rw [if_neg hmmrNotLt, hmmrValue]
    omega

/-- Concrete 256-bit specialization used by every deployed multi-limb multiplication routine. -/
theorem mulHighRecoveredAt_uint256 (a b : UInt256) :
    mulHighRecoveredAt UInt256.size a.toNat b.toNat =
      a.toNat * b.toNat / UInt256.size := by
  apply mulHighRecoveredAt_eq_div
  · norm_num [UInt256.size]
  · exact a.val.isLt
  · exact b.val.isLt

/-- The exact EVM word expression emitted for the high half of a product. -/
def evmMulHigh (a b : UInt256) : UInt256 :=
  let lo := UInt256.mul a b
  let mmr := UInt256.mulMod a b (UInt256.ofNat (UInt256.size - 1))
  UInt256.sub (UInt256.sub mmr lo) (UInt256.lt mmr lo)

private theorem mulModMax_toNat (a b : UInt256) :
    (UInt256.mulMod a b (UInt256.ofNat (UInt256.size - 1))).toNat =
      a.toNat * b.toNat % (UInt256.size - 1) := by
  have hmax : (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 :=
    ulit_toNat' _ (by norm_num [UInt256.size])
  rw [mulMod_toNat (by rw [hmax]; norm_num [UInt256.size]), hmax]

/-- The EVM expression has the natural meaning proved by `mulHighRecoveredAt_eq_div`. -/
theorem evmMulHigh_toNat (a b : UInt256) :
    (evmMulHigh a b).toNat = mulHighRecoveredAt UInt256.size a.toNat b.toNat := by
  let lo := UInt256.mul a b
  let mmr := UInt256.mulMod a b (UInt256.ofNat (UInt256.size - 1))
  have hlo : lo.toNat = a.toNat * b.toNat % UInt256.size := by
    exact u256_mul_toNat a b
  have hmmr : mmr.toNat = a.toNat * b.toNat % (UInt256.size - 1) := by
    exact mulModMax_toNat a b
  simp only [evmMulHigh, mulHighRecoveredAt]
  rw [← hlo, ← hmmr]
  change (UInt256.sub (UInt256.sub mmr lo) (UInt256.lt mmr lo)).toNat =
    if mmr.toNat < lo.toNat then UInt256.size + mmr.toNat - lo.toNat - 1
    else mmr.toNat - lo.toNat
  by_cases hborrow : mmr.toNat < lo.toNat
  · have hlt : UInt256.lt mmr lo = ⟨1⟩ := ult_one hborrow
    have hd : (UInt256.sub mmr lo).toNat = UInt256.size + mmr.toNat - lo.toNat :=
      usub_toNat_underflow hborrow
    have hloBound : lo.toNat < UInt256.size := lo.val.isLt
    have hone : (⟨1⟩ : UInt256).toNat ≤ (UInt256.sub mmr lo).toNat := by
      change 1 ≤ (UInt256.sub mmr lo).toNat
      rw [hd]
      omega
    rw [if_pos hborrow, hlt, usub_toNat hone, hd]
    rfl
  · have hle : lo.toNat ≤ mmr.toNat := by omega
    have hlt : UInt256.lt mmr lo = ⟨0⟩ := ult_zero hle
    have hd : (UInt256.sub mmr lo).toNat = mmr.toNat - lo.toNat := usub_toNat hle
    have hzero : (⟨0⟩ : UInt256).toNat ≤ (UInt256.sub mmr lo).toNat :=
      Nat.zero_le _
    rw [if_neg hborrow, hlt, usub_toNat hzero, hd]
    rfl

/-- Recombining the recovered high half and EVM `MUL` low half gives the full, untruncated
product. -/
theorem mulHighRecoveredAt_recompose (a b : UInt256) :
    (UInt256.mul a b).toNat + UInt256.size *
        mulHighRecoveredAt UInt256.size a.toNat b.toNat = a.toNat * b.toNat := by
  rw [u256_mul_toNat, mulHighRecoveredAt_uint256]
  exact Nat.mod_add_div _ _

/-- The actual EVM `MUL`/`MULMOD`/borrow sequence exactly decomposes the full product. -/
theorem evmMulHigh_recompose (a b : UInt256) :
    (UInt256.mul a b).toNat + UInt256.size * (evmMulHigh a b).toNat =
      a.toNat * b.toNat := by
  rw [evmMulHigh_toNat]
  exact mulHighRecoveredAt_recompose a b

/-- EVM's standard `sum < left` carry detector recomposes an unbounded addition. -/
theorem evmAddCarry_recompose (a b : UInt256) :
    (a + b).toNat + UInt256.size * (UInt256.lt (a + b) a).toNat =
      a.toNat + b.toNat := by
  have ha : a.toNat < UInt256.size := a.val.isLt
  have hb : b.toNat < UInt256.size := b.val.isLt
  by_cases hfit : a.toNat + b.toNat < UInt256.size
  · have hadd : (a + b).toNat = a.toNat + b.toNat := by
      rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
    have hcarry : UInt256.lt (a + b) a = ⟨0⟩ := by
      apply ult_zero
      rw [hadd]
      exact Nat.le_add_right _ _
    rw [hadd, hcarry]
    simp
  · have hover : UInt256.size ≤ a.toNat + b.toNat := by omega
    have hsumLt : a.toNat + b.toNat < 2 * UInt256.size := by omega
    have hadd : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
      rw [uadd_toNat, Nat.mod_eq_sub_mod hover, Nat.mod_eq_of_lt (by omega)]
    have hcarry : UInt256.lt (a + b) a = ⟨1⟩ := by
      apply ult_one
      rw [hadd]
      omega
    rw [hadd, hcarry]
    change a.toNat + b.toNat - UInt256.size + UInt256.size * 1 =
      a.toNat + b.toNat
    omega

private theorem ult_toNat_le_one (a b : UInt256) : (UInt256.lt a b).toNat ≤ 1 := by
  by_cases h : a.toNat < b.toNat
  · rw [ult_one h]
    decide
  · rw [ult_zero (by omega)]
    decide

/-- One inner schoolbook-multiplication update, in the same order as the Solidity assembly. -/
def evmSchoolbookStep (a b result carry : UInt256) : UInt256 × UInt256 :=
  let lo := UInt256.mul a b
  let hi := evmMulHigh a b
  let s1 := lo + result
  let c1 := UInt256.lt s1 lo
  let s2 := s1 + carry
  let c2 := UInt256.lt s2 s1
  (s2, hi + (c1 + c2))

/-- Before the final carry word is normalized, the schoolbook update preserves the exact
unbounded column value. -/
theorem evmSchoolbookStep_column
    (a b result carry : UInt256) :
    let step := evmSchoolbookStep a b result carry
    step.1.toNat + UInt256.size *
        ((evmMulHigh a b).toNat +
          (UInt256.lt (UInt256.mul a b + result) (UInt256.mul a b)).toNat +
          (UInt256.lt ((UInt256.mul a b + result) + carry)
            (UInt256.mul a b + result)).toNat) =
      a.toNat * b.toNat + result.toNat + carry.toNat := by
  dsimp only [evmSchoolbookStep]
  have hmul := evmMulHigh_recompose a b
  have hadd1 := evmAddCarry_recompose (UInt256.mul a b) result
  have hadd2 := evmAddCarry_recompose (UInt256.mul a b + result) carry
  simp only [Nat.mul_add]
  omega

/-- The source-level carry expression `hi + c1 + c2` is itself word-sized. -/
theorem evmSchoolbookStep_carry_lt (a b result carry : UInt256) :
    (evmMulHigh a b).toNat +
        (UInt256.lt (UInt256.mul a b + result) (UInt256.mul a b)).toNat +
        (UInt256.lt ((UInt256.mul a b + result) + carry)
          (UInt256.mul a b + result)).toNat < UInt256.size := by
  let c1 := UInt256.lt (UInt256.mul a b + result) (UInt256.mul a b)
  let c2 := UInt256.lt ((UInt256.mul a b + result) + carry)
    (UInt256.mul a b + result)
  let coeff := (evmMulHigh a b).toNat + c1.toNat + c2.toNat
  have hcolumn := evmSchoolbookStep_column a b result carry
  dsimp only [evmSchoolbookStep] at hcolumn
  have ha : a.toNat ≤ UInt256.size - 1 := Nat.le_pred_of_lt a.val.isLt
  have hb : b.toNat ≤ UInt256.size - 1 := Nat.le_pred_of_lt b.val.isLt
  have hr : result.toNat ≤ UInt256.size - 1 := by exact Nat.le_pred_of_lt result.val.isLt
  have hc : carry.toNat ≤ UInt256.size - 1 := by exact Nat.le_pred_of_lt carry.val.isLt
  have htotal : a.toNat * b.toNat + result.toNat + carry.toNat <
      UInt256.size * UInt256.size := by
    calc
      a.toNat * b.toNat + result.toNat + carry.toNat ≤
          (UInt256.size - 1) * (UInt256.size - 1) +
            (UInt256.size - 1) + (UInt256.size - 1) := by
              exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul ha hb) hr) hc
      _ < UInt256.size * UInt256.size := by norm_num [UInt256.size]
  change coeff < UInt256.size
  by_contra hnot
  have hge : UInt256.size ≤ coeff := by omega
  have hstepNonneg : 0 ≤ ((UInt256.mul a b + result) + carry).toNat := Nat.zero_le _
  change ((UInt256.mul a b + result) + carry).toNat + UInt256.size * coeff =
      a.toNat * b.toNat + result.toNat + carry.toNat at hcolumn
  have hmulGe : UInt256.size * UInt256.size ≤ UInt256.size * coeff :=
    Nat.mul_le_mul_left UInt256.size hge
  have hcoeffLe : UInt256.size * coeff ≤
      a.toNat * b.toNat + result.toNat + carry.toNat := by omega
  exact (Nat.not_le_of_lt htotal) (hmulGe.trans hcoeffLe)

/-- The pair stored by one Solidity schoolbook update exactly represents the full column. -/
theorem evmSchoolbookStep_recompose (a b result carry : UInt256) :
    let step := evmSchoolbookStep a b result carry
    step.1.toNat + UInt256.size * step.2.toNat =
      a.toNat * b.toNat + result.toNat + carry.toNat := by
  let lo := UInt256.mul a b
  let s1 := lo + result
  let c1 := UInt256.lt s1 lo
  let s2 := s1 + carry
  let c2 := UInt256.lt s2 s1
  have hc1 : c1.toNat ≤ 1 := ult_toNat_le_one _ _
  have hc2 : c2.toNat ≤ 1 := ult_toNat_le_one _ _
  have hc12 : c1.toNat + c2.toNat < UInt256.size := by
    norm_num [UInt256.size]
    omega
  have hc12Nat : (c1 + c2).toNat = c1.toNat + c2.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hc12]
  have hcarry := evmSchoolbookStep_carry_lt a b result carry
  change (evmMulHigh a b).toNat + c1.toNat + c2.toNat < UInt256.size at hcarry
  have hcarryNat : (evmMulHigh a b + (c1 + c2)).toNat =
      (evmMulHigh a b).toNat + c1.toNat + c2.toNat := by
    rw [uadd_toNat, hc12Nat, Nat.mod_eq_of_lt (by simpa [Nat.add_assoc] using hcarry)]
    omega
  have hcolumn := evmSchoolbookStep_column a b result carry
  dsimp only [evmSchoolbookStep] at hcolumn ⊢
  change s2.toNat + UInt256.size * (evmMulHigh a b + (c1 + c2)).toNat =
    a.toNat * b.toNat + result.toNat + carry.toNat
  rw [hcarryNat]
  simpa [lo, s1, s2, c1, c2] using hcolumn

private theorem radixPair_lt_iff {radix high low high' low' : Nat}
    (hlow : low < radix) (hlow' : low' < radix) :
    high * radix + low < high' * radix + low' ↔
      high < high' ∨ high = high' ∧ low < low' := by
  constructor
  · intro h
    by_cases hhigh : high < high'
    · exact Or.inl hhigh
    · right
      have hge : high' ≤ high := by omega
      have heq : high = high' := by
        by_contra hne
        have hstep : high' + 1 ≤ high := by omega
        have hbelow : high' * radix + low' < (high' + 1) * radix := by
          rw [Nat.add_mul, one_mul]
          exact Nat.add_lt_add_left hlow' _
        have habove : (high' + 1) * radix ≤ high * radix :=
          Nat.mul_le_mul_right radix hstep
        omega
      exact ⟨heq, by simpa [heq] using h⟩
  · intro h
    rcases h with hhigh | ⟨rfl, hlowPair⟩
    · have hstep : high + 1 ≤ high' := by omega
      have hbelow : high * radix + low < (high + 1) * radix := by
        rw [Nat.add_mul, one_mul]
        exact Nat.add_lt_add_left hlow _
      have habove : (high + 1) * radix ≤ high' * radix :=
        Nat.mul_le_mul_right radix hstep
      exact hbelow.trans_le (habove.trans (Nat.le_add_right _ _))
    · exact Nat.add_lt_add_left hlowPair _

/-- The `(high, low)` comparison used by Knuth q-hat refinement is exactly comparison with the
unbounded 512-bit product. -/
theorem evmMulHigh_lex_gt_iff (a b high low : UInt256) :
    (high.toNat < (evmMulHigh a b).toNat ∨
      high.toNat = (evmMulHigh a b).toNat ∧ low.toNat < (UInt256.mul a b).toNat) ↔
    high.toNat * UInt256.size + low.toNat < a.toNat * b.toNat := by
  have hrec := evmMulHigh_recompose a b
  have hrec' : (evmMulHigh a b).toNat * UInt256.size + (UInt256.mul a b).toNat =
      a.toNat * b.toNat := by
    calc
      (evmMulHigh a b).toNat * UInt256.size + (UInt256.mul a b).toNat =
          (UInt256.mul a b).toNat + UInt256.size * (evmMulHigh a b).toNat := by
            ac_rfl
      _ = a.toNat * b.toNat := hrec
  rw [← hrec']
  exact (radixPair_lt_iff low.val.isLt (UInt256.mul a b).val.isLt).symm

/-- The subtraction-with-borrow sequence shared by Knuth division and Barrett correction. -/
def evmSubBorrow (left right borrow : UInt256) : UInt256 × UInt256 :=
  let d := UInt256.sub left right
  let firstBorrow := UInt256.lt left right
  let d2 := UInt256.sub d borrow
  let borrowOut := UInt256.lor firstBorrow (UInt256.lt d borrow)
  (d2, borrowOut)

/-- One source-level subtraction limb preserves the exact radix equation. -/
theorem evmSubBorrow_recompose
    (left right borrow : UInt256) (hborrow : borrow = ⟨0⟩ ∨ borrow = ⟨1⟩) :
    let step := evmSubBorrow left right borrow
    step.1.toNat + right.toNat + borrow.toNat =
      left.toNat + UInt256.size * step.2.toNat := by
  dsimp only [evmSubBorrow]
  rcases hborrow with rfl | rfl
  · by_cases hlt : left.toNat < right.toNat
    · have hfirst : UInt256.lt left right = ⟨1⟩ := ult_one hlt
      have hd : (UInt256.sub left right).toNat =
          UInt256.size + left.toNat - right.toNat := usub_toNat_underflow hlt
      have hsecond : UInt256.lt (UInt256.sub left right) ⟨0⟩ = ⟨0⟩ :=
        ult_zero (Nat.zero_le _)
      rw [hfirst, hsecond]
      change (UInt256.sub (UInt256.sub left right) ⟨0⟩).toNat + right.toNat + 0 =
        left.toNat + UInt256.size * (UInt256.lor ⟨1⟩ ⟨0⟩).toNat
      rw [usub_toNat (Nat.zero_le _), hd]
      rw [show UInt256.lor ⟨1⟩ ⟨0⟩ = ⟨1⟩ by native_decide]
      change UInt256.size + left.toNat - right.toNat - 0 + right.toNat =
        left.toNat + UInt256.size * 1
      have hr : right.toNat < UInt256.size := right.val.isLt
      have hcancel : UInt256.size + left.toNat - right.toNat + right.toNat =
          UInt256.size + left.toNat := Nat.sub_add_cancel (by omega)
      rw [Nat.sub_zero]
      omega
    · have hle : right.toNat ≤ left.toNat := by omega
      have hfirst : UInt256.lt left right = ⟨0⟩ := ult_zero hle
      have hd : (UInt256.sub left right).toNat = left.toNat - right.toNat :=
        usub_toNat hle
      have hsecond : UInt256.lt (UInt256.sub left right) ⟨0⟩ = ⟨0⟩ :=
        ult_zero (Nat.zero_le _)
      rw [hfirst, hsecond]
      change (UInt256.sub (UInt256.sub left right) ⟨0⟩).toNat + right.toNat + 0 =
        left.toNat + UInt256.size * (UInt256.lor ⟨0⟩ ⟨0⟩).toNat
      rw [usub_toNat (Nat.zero_le _), hd]
      rw [show UInt256.lor ⟨0⟩ ⟨0⟩ = ⟨0⟩ by native_decide]
      change left.toNat - right.toNat - 0 + right.toNat = left.toNat + UInt256.size * 0
      omega
  · by_cases hlt : left.toNat < right.toNat
    · have hfirst : UInt256.lt left right = ⟨1⟩ := ult_one hlt
      have hd : (UInt256.sub left right).toNat =
          UInt256.size + left.toNat - right.toNat := usub_toNat_underflow hlt
      have hdPos : (⟨1⟩ : UInt256).toNat ≤ (UInt256.sub left right).toNat := by
        change 1 ≤ (UInt256.sub left right).toNat
        rw [hd]
        have hr : right.toNat < UInt256.size := right.val.isLt
        omega
      have hsecond : UInt256.lt (UInt256.sub left right) ⟨1⟩ = ⟨0⟩ :=
        ult_zero hdPos
      rw [hfirst, hsecond]
      change (UInt256.sub (UInt256.sub left right) ⟨1⟩).toNat + right.toNat + 1 =
        left.toNat + UInt256.size * (UInt256.lor ⟨1⟩ ⟨0⟩).toNat
      rw [usub_toNat hdPos, hd]
      rw [show UInt256.lor ⟨1⟩ ⟨0⟩ = ⟨1⟩ by native_decide]
      change UInt256.size + left.toNat - right.toNat - 1 + right.toNat + 1 =
        left.toNat + UInt256.size * 1
      have honeNat : 1 ≤ UInt256.size + left.toNat - right.toNat := by
        simpa [hd] using hdPos
      have honeCancel : UInt256.size + left.toNat - right.toNat - 1 + 1 =
          UInt256.size + left.toNat - right.toNat := Nat.sub_add_cancel honeNat
      have hrightCancel : UInt256.size + left.toNat - right.toNat + right.toNat =
          UInt256.size + left.toNat := Nat.sub_add_cancel (by omega)
      omega
    · have hle : right.toNat ≤ left.toNat := by omega
      by_cases heq : right.toNat = left.toNat
      · have hd : (UInt256.sub left right).toNat = 0 := by
          rw [usub_toNat hle]
          omega
        have hfirst : UInt256.lt left right = ⟨0⟩ := ult_zero hle
        have hsecond : UInt256.lt (UInt256.sub left right) ⟨1⟩ = ⟨1⟩ := by
          apply ult_one
          rw [hd]
          decide
        have hd2 : (UInt256.sub (UInt256.sub left right) ⟨1⟩).toNat =
            UInt256.size - 1 := by
          rw [usub_toNat_underflow (by rw [hd]; decide), hd]
          rfl
        rw [hfirst, hsecond]
        change (UInt256.sub (UInt256.sub left right) ⟨1⟩).toNat + right.toNat + 1 =
          left.toNat + UInt256.size * (UInt256.lor ⟨0⟩ ⟨1⟩).toNat
        rw [hd2]
        rw [show UInt256.lor ⟨0⟩ ⟨1⟩ = ⟨1⟩ by native_decide]
        change UInt256.size - 1 + right.toNat + 1 = left.toNat + UInt256.size * 1
        have hbase : 1 ≤ UInt256.size := by norm_num [UInt256.size]
        have hcancel : UInt256.size - 1 + 1 = UInt256.size :=
          Nat.sub_add_cancel hbase
        omega
      · have hstrict : right.toNat < left.toNat := by omega
        have hfirst : UInt256.lt left right = ⟨0⟩ := ult_zero hle
        have hd : (UInt256.sub left right).toNat = left.toNat - right.toNat :=
          usub_toNat hle
        have hdPos : (⟨1⟩ : UInt256).toNat ≤ (UInt256.sub left right).toNat := by
          change 1 ≤ (UInt256.sub left right).toNat
          rw [hd]
          omega
        have hsecond : UInt256.lt (UInt256.sub left right) ⟨1⟩ = ⟨0⟩ :=
          ult_zero hdPos
        rw [hfirst, hsecond]
        change (UInt256.sub (UInt256.sub left right) ⟨1⟩).toNat + right.toNat + 1 =
          left.toNat + UInt256.size * (UInt256.lor ⟨0⟩ ⟨0⟩).toNat
        rw [usub_toNat hdPos, hd]
        rw [show UInt256.lor ⟨0⟩ ⟨0⟩ = ⟨0⟩ by native_decide]
        change left.toNat - right.toNat - 1 + right.toNat + 1 =
          left.toNat + UInt256.size * 0
        omega

end Modexp
