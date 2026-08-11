import Examples.Precompiles.Modexp.MultiLimbClzShifts
import Examples.Precompiles.Modexp.MultiLimbClzStage1

/-! # Lower bounds maintained by the deployed leading-zero stages -/
open Ethereum
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stage128_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 128 ≤ (stage128 x).x.toNat := by
  unfold stage128
  split
  next hlt =>
    simp only
    rw [shiftLeft128_toNat_exact hlt]
    calc
      2 ^ 128 = 1 * 2 ^ 128 := by omega
      _ ≤ x.toNat * 2 ^ 128 := Nat.mul_le_mul_right _ (Nat.one_le_iff_ne_zero.mpr hx)
  next hge => simp only; omega

theorem stage64_lower {x : UInt256} {n : Nat} (hx : 2 ^ 128 ≤ x.toNat) :
    2 ^ 192 ≤ (stage64 x n).x.toNat := by
  unfold stage64
  split
  next hlt =>
    simp only
    rw [shiftLeft64_toNat_exact hlt]
    calc
      2 ^ 192 = 2 ^ 128 * 2 ^ 64 := by norm_num
      _ ≤ x.toNat * 2 ^ 64 := Nat.mul_le_mul_right _ hx
  next hge => simp only; omega

theorem stage32_lower {x : UInt256} {n : Nat} (hx : 2 ^ 192 ≤ x.toNat) :
    2 ^ 224 ≤ (stage32 x n).x.toNat := by
  unfold stage32
  split
  next hlt =>
    simp only
    rw [shiftLeft32_toNat_exact hlt]
    calc
      2 ^ 224 = 2 ^ 192 * 2 ^ 32 := by norm_num
      _ ≤ x.toNat * 2 ^ 32 := Nat.mul_le_mul_right _ hx
  next hge => simp only; omega

theorem stage16_lower {x : UInt256} {n : Nat} (hx : 2 ^ 224 ≤ x.toNat) :
    2 ^ 240 ≤ (stage16 x n).x.toNat := by
  unfold stage16
  split
  next hlt =>
    simp only
    rw [shiftLeft16_toNat_exact hlt]
    calc
      2 ^ 240 = 2 ^ 224 * 2 ^ 16 := by norm_num
      _ ≤ x.toNat * 2 ^ 16 := Nat.mul_le_mul_right _ hx
  next hge => simp only; omega

theorem stage8_lower {x : UInt256} {n : Nat} (hx : 2 ^ 240 ≤ x.toNat) :
    2 ^ 248 ≤ (stage8 x n).x.toNat := by
  unfold stage8
  split
  next hlt =>
    simp only
    rw [shiftLeft8_toNat_exact hlt]
    calc
      2 ^ 248 = 2 ^ 240 * 2 ^ 8 := by norm_num
      _ ≤ x.toNat * 2 ^ 8 := Nat.mul_le_mul_right _ hx
  next hge => simp only; omega

theorem stage4_lower {x : UInt256} {n : Nat} (hx : 2 ^ 248 ≤ x.toNat) :
    2 ^ 252 ≤ (stage4 x n).x.toNat := by
  unfold stage4
  split
  next hlt =>
    simp only
    rw [shiftLeft4_toNat_exact hlt]
    calc
      2 ^ 252 = 2 ^ 248 * 2 ^ 4 := by norm_num
      _ ≤ x.toNat * 2 ^ 4 := Nat.mul_le_mul_right _ hx
  next hge => simp only; omega

theorem stage2_lower {x : UInt256} {n : Nat} (hx : 2 ^ 252 ≤ x.toNat) :
    2 ^ 254 ≤ (stage2 x n).x.toNat := by
  unfold stage2
  split
  next hlt =>
    simp only
    rw [shiftLeft2_toNat_exact hlt]
    calc
      2 ^ 254 = 2 ^ 252 * 2 ^ 2 := by norm_num
      _ ≤ x.toNat * 2 ^ 2 := Nat.mul_le_mul_right _ hx
  next hge => simp only; omega

end Modexp.MultiLimbClz
