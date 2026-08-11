import Examples.Precompiles.Modexp.MultiLimbClzLower
import Examples.Precompiles.Modexp.MultiLimbClzRelations
import Examples.Precompiles.Modexp.MultiLimbClzPrefixes

/-! # Arithmetic invariants through the 64-bit Clz stage -/
open Ethereum
namespace Modexp.MultiLimbClz

theorem through64_lower {x : UInt256} (hx : x.toNat ≠ 0) :
    2 ^ 192 ≤ (through64 x).x.toNat := by
  have ha := stage128_lower hx
  have hb := stage64_lower (n := (stage128 x).n) ha
  simpa only [through64] using hb

theorem through64_relation (x : UInt256) :
    (through64 x).x.toNat = x.toNat * 2 ^ (through64 x).n := by
  have ha := stage128_relation x
  have hb := stage64_relation ha
  simpa only [through64] using hb

end Modexp.MultiLimbClz
