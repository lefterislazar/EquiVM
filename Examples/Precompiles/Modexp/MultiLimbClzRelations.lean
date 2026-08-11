import Examples.Precompiles.Modexp.MultiLimbClzShifts
import Examples.Precompiles.Modexp.MultiLimbClzStage1

/-! # Multiplicative invariants maintained by the deployed leading-zero stages -/
open Ethereum
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stage128_relation (x : UInt256) :
    (stage128 x).x.toNat = x.toNat * 2 ^ (stage128 x).n := by
  unfold stage128
  split
  next hlt => simp only; rw [shiftLeft128_toNat_exact hlt]
  next hge => simp

theorem stage64_relation {original x : UInt256} {n : Nat}
    (hrel : x.toNat = original.toNat * 2 ^ n) :
    (stage64 x n).x.toNat = original.toNat * 2 ^ (stage64 x n).n := by
  unfold stage64
  split
  next hlt => simp only; rw [shiftLeft64_toNat_exact hlt, hrel, Nat.pow_add]; ring
  next hge => simpa using hrel

theorem stage32_relation {original x : UInt256} {n : Nat}
    (hrel : x.toNat = original.toNat * 2 ^ n) :
    (stage32 x n).x.toNat = original.toNat * 2 ^ (stage32 x n).n := by
  unfold stage32
  split
  next hlt => simp only; rw [shiftLeft32_toNat_exact hlt, hrel, Nat.pow_add]; ring
  next hge => simpa using hrel

theorem stage16_relation {original x : UInt256} {n : Nat}
    (hrel : x.toNat = original.toNat * 2 ^ n) :
    (stage16 x n).x.toNat = original.toNat * 2 ^ (stage16 x n).n := by
  unfold stage16
  split
  next hlt => simp only; rw [shiftLeft16_toNat_exact hlt, hrel, Nat.pow_add]; ring
  next hge => simpa using hrel

theorem stage8_relation {original x : UInt256} {n : Nat}
    (hrel : x.toNat = original.toNat * 2 ^ n) :
    (stage8 x n).x.toNat = original.toNat * 2 ^ (stage8 x n).n := by
  unfold stage8
  split
  next hlt => simp only; rw [shiftLeft8_toNat_exact hlt, hrel, Nat.pow_add]; ring
  next hge => simpa using hrel

theorem stage4_relation {original x : UInt256} {n : Nat}
    (hrel : x.toNat = original.toNat * 2 ^ n) :
    (stage4 x n).x.toNat = original.toNat * 2 ^ (stage4 x n).n := by
  unfold stage4
  split
  next hlt => simp only; rw [shiftLeft4_toNat_exact hlt, hrel, Nat.pow_add]; ring
  next hge => simpa using hrel

theorem stage2_relation {original x : UInt256} {n : Nat}
    (hrel : x.toNat = original.toNat * 2 ^ n) :
    (stage2 x n).x.toNat = original.toNat * 2 ^ (stage2 x n).n := by
  unfold stage2
  split
  next hlt => simp only; rw [shiftLeft2_toNat_exact hlt, hrel, Nat.pow_add]; ring
  next hge => simpa using hrel

end Modexp.MultiLimbClz
