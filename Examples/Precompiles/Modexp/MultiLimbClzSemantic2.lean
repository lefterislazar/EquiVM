import Examples.Precompiles.Modexp.MultiLimbClzSemantic4

/-! # Arithmetic invariants through the 2-bit Clz stage -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem through2_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 254 ≤ (through2 x).x.toNat := by
  have h := stage2_lower (n := (through4 x).n) (through4_lower hx)
  simpa only [through2] using h

theorem through2_relation (x : UInt256) :
    (through2 x).x.toNat = x.toNat * 2 ^ (through2 x).n := by
  have h := stage2_relation (through4_relation x)
  simpa only [through2] using h

end Modexp.MultiLimbClz
