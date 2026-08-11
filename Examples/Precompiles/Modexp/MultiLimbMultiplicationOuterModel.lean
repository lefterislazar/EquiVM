import Examples.Precompiles.Modexp.MultiLimbMultiplicationModel

/-! # Full schoolbook multiplication invariant -/

open Ethereum Reasoning.Theory

namespace Modexp

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Radix interpretation distributes over list append. -/
theorem wordLimbsToNat_append (left right : List UInt256) :
    wordLimbsToNat (left ++ right) =
      wordLimbsToNat left + UInt256.size ^ left.length * wordLimbsToNat right := by
  rw [wordLimbsToNat_eq_limbsToNatAt, List.map_append,
    limbsToNatAt_append, ← wordLimbsToNat_eq_limbsToNatAt,
    ← wordLimbsToNat_eq_limbsToNatAt]
  simp only [List.length_map]

end Modexp
