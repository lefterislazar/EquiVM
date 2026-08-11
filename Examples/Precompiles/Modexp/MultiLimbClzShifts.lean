import Examples.Precompiles.Modexp.MultiLimbClzArithmetic

/-! # Fixed-width instances of the non-wrapping shift theorem -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem shiftLeft128_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 128) :
    (x.shiftLeft ⟨128⟩).toNat = x.toNat * 2 ^ 128 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 128) (by omega) (by simpa using hx)

theorem shiftLeft64_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 192) :
    (x.shiftLeft ⟨64⟩).toNat = x.toNat * 2 ^ 64 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 64) (by omega) (by simpa using hx)

theorem shiftLeft32_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 224) :
    (x.shiftLeft ⟨32⟩).toNat = x.toNat * 2 ^ 32 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 32) (by omega) (by simpa using hx)

theorem shiftLeft16_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 240) :
    (x.shiftLeft ⟨16⟩).toNat = x.toNat * 2 ^ 16 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 16) (by omega) (by simpa using hx)

theorem shiftLeft8_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 248) :
    (x.shiftLeft ⟨8⟩).toNat = x.toNat * 2 ^ 8 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 8) (by omega) (by simpa using hx)

theorem shiftLeft4_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 252) :
    (x.shiftLeft ⟨4⟩).toNat = x.toNat * 2 ^ 4 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 4) (by omega) (by simpa using hx)

theorem shiftLeft2_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 254) :
    (x.shiftLeft ⟨2⟩).toNat = x.toNat * 2 ^ 2 := by
  simpa using shiftLeft_toNat_exact (x := x) (shift := 2) (by omega) (by simpa using hx)

theorem shiftLeft1_toNat_exact {x : UInt256} (hx : x.toNat < 2 ^ 255) :
    (x.shiftLeft ⟨1⟩).toNat = x.toNat * 2 := by
  have h := shiftLeft_toNat_exact (x := x) (shift := 1) (by omega) (by simpa using hx)
  simpa using h

end Modexp.MultiLimbClz
