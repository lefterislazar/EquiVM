import Examples.Precompiles.Modexp.MultiLimbClzSemantic64

/-! # Arithmetic invariants through the 32-bit Clz stage -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem through32_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 224 ≤ (through32 x).x.toNat := by
  have h := stage32_lower (n := (through64 x).n) (through64_lower hx)
  simpa only [through32] using h

theorem through32_relation (x : UInt256) :
    (through32 x).x.toNat = x.toNat * 2 ^ (through32 x).n := by
  have h := stage32_relation (through64_relation x)
  simpa only [through32] using h

end Modexp.MultiLimbClz
