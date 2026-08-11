import Examples.Precompiles.Modexp.MultiLimbClzSemantic16

/-! # Arithmetic invariants through the 8-bit Clz stage -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem through8_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 248 ≤ (through8 x).x.toNat := by
  have h := stage8_lower (n := (through16 x).n) (through16_lower hx)
  simpa only [through8] using h

theorem through8_relation (x : UInt256) :
    (through8 x).x.toNat = x.toNat * 2 ^ (through8 x).n := by
  have h := stage8_relation (through16_relation x)
  simpa only [through8] using h

end Modexp.MultiLimbClz
