import Examples.Precompiles.Modexp.MultiLimbClzStage8

/-! # Exact 4-bit stage of the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def stage4 (x : UInt256) (n : Nat) : StageResult :=
  if x.toNat < 2 ^ 252 then
    { x := x.shiftLeft ⟨4⟩, n := n + 4, steps := 29, gas := 108 }
  else
    { x := x, n := n, steps := 6, gas := 23 }

theorem stage4Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256} {x ret : UInt256}
    (hnWord : n + 4 < UInt256.size)
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8253⟩
      (x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat n :: tail)
      mem aw rdata acc k C) :
    let result := stage4 x n
    RDx runtimeBytecode ee g s0 ⟨8293⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  unfold stage4
  have hthreshold : (UInt256.ofNat (2 ^ 252)).toNat = 2 ^ 252 := by
    rw [UInt256.toNat_ofNat_of_lt]
    norm_num [UInt256.size]
  by_cases hlt : x.toNat < 2 ^ 252
  · rw [if_pos hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 252)) ≠ ⟨0⟩ := by
      rw [ult_one]
      · native_decide
      · simpa [hthreshold] using hlt
    have rd8376 := GeneratedTraces.trace_8253_taken
      (by simp only [List.length_cons]; omega) h
      (by native_decide) hcondition (by native_decide)
    have hn : n < UInt256.size := by omega
    have hadd : UInt256.ofNat n + ⟨4⟩ = UInt256.ofNat (n + 4) := by
      simpa using (ofNat_add_bounded hnWord)
    have hnoOverflow : UInt256.gt (UInt256.ofNat n) (UInt256.ofNat (n + 4)) = ⟨0⟩ := by
      apply ugt_zero
      rw [UInt256.toNat_ofNat_of_lt hn, UInt256.toNat_ofNat_of_lt hnWord]
      omega
    have rd1420 := GeneratedTraces.trace_8369_notTaken
      (by omega) rd8376 (by native_decide) (by
        simpa [hadd] using hnoOverflow)
    rw [hadd] at rd1420
    have rd8389 := GeneratedTraces.trace_1420_jump
      (by simp only [List.length_cons]; omega) rd1420
      (by native_decide) (by native_decide)
    have rd8300 := evm_run rd8389 with [
      jumpdest,
      swap3,
      pushCanonical 2 .PUSH2 ⟨8293⟩ (by decide),
      jump (by native_decide)
    ]
    have normalized := rd8300.withIndices
      (k' := k + 29) (C' := C + 108) (by omega) (by omega)
    simpa using normalized
  · rw [if_neg hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 252)) = ⟨0⟩ := by
      apply ult_zero
      rw [hthreshold]
      omega
    have rd8300 := GeneratedTraces.trace_8253_notTaken
      (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
    have normalized := rd8300.withIndices
      (k' := k + 6) (C' := C + 23) (by omega) (by omega)
    simpa using normalized

end Modexp.MultiLimbClz
