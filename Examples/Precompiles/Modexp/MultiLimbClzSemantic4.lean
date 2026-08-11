import Examples.Precompiles.Modexp.MultiLimbClzSemantic8

/-! # Arithmetic invariants through the 4-bit Clz stage -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem through4_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 252 ≤ (through4 x).x.toNat := by
  have h := stage4_lower (n := (through8 x).n) (through8_lower hx)
  simpa only [through4] using h

theorem through4_relation (x : UInt256) :
    (through4 x).x.toNat = x.toNat * 2 ^ (through4 x).n := by
  have h := stage4_relation (through8_relation x)
  simpa only [through4] using h

end Modexp.MultiLimbClz
