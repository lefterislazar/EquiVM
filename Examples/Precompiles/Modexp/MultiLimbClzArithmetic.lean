import Examples.Precompiles.Modexp.Bridge

/-! # Non-wrapping shift facts for the deployed leading-zero helper -/
open Ethereum Reasoning.Theory
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem shiftLeft_toNat_exact {x : UInt256} {shift : Nat}
    (hshift : shift < 256)
    (hx : x.toNat < 2 ^ (256 - shift)) :
    (x.shiftLeft (UInt256.ofNat shift)).toNat = x.toNat * 2 ^ shift := by
  rw [ushl_ofNat_toNat x shift hshift, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
  calc
    x.toNat * 2 ^ shift < 2 ^ (256 - shift) * 2 ^ shift :=
      Nat.mul_lt_mul_of_pos_right hx (by positivity)
    _ = 2 ^ 256 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    _ = UInt256.size := by norm_num [UInt256.size]

end Modexp.MultiLimbClz
