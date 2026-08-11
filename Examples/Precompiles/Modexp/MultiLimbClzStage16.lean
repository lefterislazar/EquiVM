import Examples.Precompiles.Modexp.MultiLimbClzStage32

/-! # Exact 16-bit stage of the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def stage16 (x : UInt256) (n : Nat) : StageResult :=
  if x.toNat < 2 ^ 240 then
    { x := x.shiftLeft ⟨16⟩, n := n + 16, steps := 29, gas := 108 }
  else
    { x := x, n := n, steps := 6, gas := 23 }

theorem stage16Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256} {x ret : UInt256}
    (hnWord : n + 16 < UInt256.size)
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8174⟩
      (x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat n :: tail)
      mem aw rdata acc k C) :
    let result := stage16 x n
    RDx runtimeBytecode ee g s0 ⟨8213⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  unfold stage16
  have hthreshold : (UInt256.ofNat (2 ^ 240)).toNat = 2 ^ 240 := by
    rw [UInt256.toNat_ofNat_of_lt]
    norm_num [UInt256.size]
  by_cases hlt : x.toNat < 2 ^ 240
  · rw [if_pos hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 240)) ≠ ⟨0⟩ := by
      rw [ult_one]
      · native_decide
      · simpa [hthreshold] using hlt
    have rd8414 := GeneratedTraces.trace_8174_taken
      (by simp only [List.length_cons]; omega) h
      (by native_decide) hcondition (by native_decide)
    have hn : n < UInt256.size := by omega
    have hadd : UInt256.ofNat n + ⟨16⟩ = UInt256.ofNat (n + 16) := by
      simpa using (ofNat_add_bounded hnWord)
    have hnoOverflow : UInt256.gt (UInt256.ofNat n) (UInt256.ofNat (n + 16)) = ⟨0⟩ := by
      apply ugt_zero
      rw [UInt256.toNat_ofNat_of_lt hn, UInt256.toNat_ofNat_of_lt hnWord]
      omega
    have rd1392 := GeneratedTraces.trace_8407_notTaken
      (by omega) rd8414 (by native_decide) (by
        simpa [hadd] using hnoOverflow)
    rw [hadd] at rd1392
    have rd8427 := GeneratedTraces.trace_1392_jump
      (by simp only [List.length_cons]; omega) rd1392
      (by native_decide) (by native_decide)
    have rd8220 := evm_run rd8427 with [
      jumpdest,
      swap3,
      pushCanonical 2 .PUSH2 ⟨8213⟩ (by decide),
      jump (by native_decide)
    ]
    have normalized := rd8220.withIndices
      (k' := k + 29) (C' := C + 108) (by omega) (by omega)
    simpa using normalized
  · rw [if_neg hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 240)) = ⟨0⟩ := by
      apply ult_zero
      rw [hthreshold]
      omega
    have rd8220 := GeneratedTraces.trace_8174_notTaken
      (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
    have normalized := rd8220.withIndices
      (k' := k + 6) (C' := C + 23) (by omega) (by omega)
    simpa using normalized

end Modexp.MultiLimbClz
