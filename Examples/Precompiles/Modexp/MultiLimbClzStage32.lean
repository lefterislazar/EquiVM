import Examples.Precompiles.Modexp.MultiLimbClzStage64

/-! # Exact 32-bit stage of the deployed leading-zero helper -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def stage32 (x : UInt256) (n : Nat) : StageResult :=
  if x.toNat < 2 ^ 224 then
    { x := x.shiftLeft ⟨32⟩, n := n + 32, steps := 29, gas := 108 }
  else
    { x := x, n := n, steps := 6, gas := 23 }

/-- Execute the 32-bit `_clz` decision and rejoin at the 240-bit test. -/
theorem stage32Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {x ret : UInt256}
    (hnWord : n + 32 < UInt256.size)
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8137⟩
      (x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat n :: tail)
      mem aw rdata acc k C) :
    let result := stage32 x n
    RDx runtimeBytecode ee g s0 ⟨8174⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  unfold stage32
  have hthreshold : (UInt256.ofNat (2 ^ 224)).toNat = 2 ^ 224 := by
    rw [UInt256.toNat_ofNat_of_lt]
    norm_num [UInt256.size]
  by_cases hlt : x.toNat < 2 ^ 224
  · rw [if_pos hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 224)) ≠ ⟨0⟩ := by
      rw [ult_one]
      · native_decide
      · simpa [hthreshold] using hlt
    have rd8433 := GeneratedTraces.trace_8137_taken
      (by simp only [List.length_cons]; omega) h
      (by native_decide) hcondition (by native_decide)
    have hn : n < UInt256.size := by omega
    have hadd : UInt256.ofNat n + ⟨32⟩ = UInt256.ofNat (n + 32) := by
      simpa using (ofNat_add_bounded hnWord)
    have hnoOverflow : UInt256.gt (UInt256.ofNat n) (UInt256.ofNat (n + 32)) = ⟨0⟩ := by
      apply ugt_zero
      rw [UInt256.toNat_ofNat_of_lt hn, UInt256.toNat_ofNat_of_lt hnWord]
      omega
    have rd1378 := GeneratedTraces.trace_8426_notTaken
      (by omega) rd8433 (by native_decide) (by
        simpa [hadd] using hnoOverflow)
    rw [hadd] at rd1378
    have rd8446 := GeneratedTraces.trace_1378_jump
      (by simp only [List.length_cons]; omega) rd1378
      (by native_decide) (by native_decide)
    have rd8181 := evm_run rd8446 with [
      jumpdest,
      swap3,
      pushCanonical 2 .PUSH2 ⟨8174⟩ (by decide),
      jump (by native_decide)
    ]
    have normalized := rd8181.withIndices
      (k' := k + 29) (C' := C + 108) (by omega) (by omega)
    simpa using normalized
  · rw [if_neg hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 224)) = ⟨0⟩ := by
      apply ult_zero
      rw [hthreshold]
      omega
    have rd8181 := GeneratedTraces.trace_8137_notTaken
      (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
    have normalized := rd8181.withIndices
      (k' := k + 6) (C' := C + 23) (by omega) (by omega)
    simpa using normalized

end Modexp.MultiLimbClz
