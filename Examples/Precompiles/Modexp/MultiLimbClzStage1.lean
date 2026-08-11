import Examples.Precompiles.Modexp.MultiLimbClzStage2

/-! # Exact final stage of the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def stage1 (x : UInt256) (n : Nat) : StageResult :=
  if x.toNat < 2 ^ 255 then
    { x := x, n := n + 1, steps := 24, gas := 93 }
  else
    { x := x, n := n, steps := 5, gas := 25 }

/-- Execute the final one-bit decision and return the accumulated count. -/
theorem stage1Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256} {x ret : UInt256}
    (hnWord : n + 1 < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (hdepth : tail.length ≤ 1018)
    (h : RDx runtimeBytecode ee g s0 ⟨8333⟩
      (x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat n :: tail)
      mem aw rdata acc k C) :
    let result := stage1 x n
    RDx runtimeBytecode ee g s0 ret (UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  unfold stage1
  have hthreshold : (UInt256.ofNat (2 ^ 255)).toNat = 2 ^ 255 := by
    rw [UInt256.toNat_ofNat_of_lt]
    norm_num [UInt256.size]
  by_cases hlt : x.toNat < 2 ^ 255
  · rw [if_pos hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 255)) ≠ ⟨0⟩ := by
      rw [ult_one]
      · native_decide
      · simpa [hthreshold] using hlt
    have rd8347 := GeneratedTraces.trace_8333_taken
      (by simp only [List.length_cons]; omega) h
      (by native_decide) hcondition (by native_decide)
    have hn : n < UInt256.size := by omega
    have hadd : UInt256.ofNat n + ⟨1⟩ = UInt256.ofNat (n + 1) := by
      simpa using (ofNat_add_bounded hnWord)
    have hnoOverflow : UInt256.gt (UInt256.ofNat n) (UInt256.ofNat (n + 1)) = ⟨0⟩ := by
      apply ugt_zero
      rw [UInt256.toNat_ofNat_of_lt hn, UInt256.toNat_ofNat_of_lt hnWord]
      omega
    have rd1336 := GeneratedTraces.trace_8340_notTaken
      (by omega) rd8347 (by native_decide) (by
        simpa [hadd] using hnoOverflow)
    rw [hadd] at rd1336
    have rd1271 := GeneratedTraces.trace_1336_jump
      (by simp only [List.length_cons]; omega) rd1336
      (by native_decide) (by native_decide)
    have rdret := GeneratedTraces.trace_1271_jump
      (by omega) rd1271
      (by native_decide) hret
    have normalized := rdret.withIndices
      (k' := k + 24) (C' := C + 93) (by omega) (by omega)
    simpa using normalized
  · rw [if_neg hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 255)) = ⟨0⟩ := by
      apply ult_zero
      rw [hthreshold]
      omega
    have rd8346 := GeneratedTraces.trace_8333_notTaken
      (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
    have rdret := GeneratedTraces.trace_8339_jump
      (by simp only [List.length_cons]; omega) rd8346
      (by native_decide) hret
    have normalized := rdret.withIndices
      (k' := k + 5) (C' := C + 25) (by omega) (by omega)
    simpa using normalized

end Modexp.MultiLimbClz
