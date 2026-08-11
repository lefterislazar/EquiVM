import Examples.Precompiles.Modexp.MultiLimbClzSemantic32

/-! # Arithmetic invariants through the 16-bit Clz stage -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem through16_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 240 ≤ (through16 x).x.toNat := by
  have h := stage16_lower (n := (through32 x).n) (through32_lower hx)
  simpa only [through16] using h

theorem through16_relation (x : UInt256) :
    (through16 x).x.toNat = x.toNat * 2 ^ (through16 x).n := by
  have h := stage16_relation (through32_relation x)
  simpa only [through16] using h

end Modexp.MultiLimbClz
