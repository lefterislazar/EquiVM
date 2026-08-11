import Examples.Precompiles.Modexp.MultiLimbClzStage128

/-! # Exact 64-bit stage of the deployed leading-zero helper -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbClz

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def stage64 (x : UInt256) (n : Nat) : StageResult :=
  if x.toNat < 2 ^ 192 then
    { x := x.shiftLeft ⟨64⟩, n := n + 64, steps := 31, gas := 114 }
  else
    { x := x, n := n, steps := 8, gas := 29 }

/-- Execute the 64-bit `_clz` decision and rejoin at the 224-bit test. -/
theorem stage64Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {x ret : UInt256}
    (hnWord : n + 64 < UInt256.size)
    (hdepth : tail.length ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨8070⟩
      (x :: ret :: UInt256.ofNat n :: tail) mem aw rdata acc k C) :
    let result := stage64 x n
    RDx runtimeBytecode ee g s0 ⟨8137⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  unfold stage64
  have hthreshold : (UInt256.ofNat (2 ^ 192)).toNat = 2 ^ 192 := by
    rw [UInt256.toNat_ofNat_of_lt]
    norm_num [UInt256.size]
  by_cases hlt : x.toNat < 2 ^ 192
  · rw [if_pos hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 192)) ≠ ⟨0⟩ := by
      rw [ult_one]
      · native_decide
      · simpa [hthreshold] using hlt
    have rd8452 := GeneratedTraces.trace_8070_taken
      (by simp only [List.length_cons]; omega) h
      (by native_decide) hcondition (by native_decide)
    have hn : n < UInt256.size := by omega
    have hadd : UInt256.ofNat n + ⟨64⟩ = UInt256.ofNat (n + 64) := by
      simpa using (ofNat_add_bounded hnWord)
    have hnoOverflow : UInt256.gt (UInt256.ofNat n) (UInt256.ofNat (n + 64)) = ⟨0⟩ := by
      apply ugt_zero
      rw [UInt256.toNat_ofNat_of_lt hn, UInt256.toNat_ofNat_of_lt hnWord]
      omega
    have rd1364 := GeneratedTraces.trace_8445_notTaken
      (by omega) rd8452 (by native_decide) (by
        simpa [hadd] using hnoOverflow)
    rw [hadd] at rd1364
    have rd8465 := GeneratedTraces.trace_1364_jump
      (by simp only [List.length_cons]; omega) rd1364
      (by native_decide) (by native_decide)
    have rd8144 := evm_run rd8465 with [
      jumpdest,
      swap3,
      pushCanonical 2 .PUSH2 ⟨8137⟩ (by decide),
      jump (by native_decide)
    ]
    have normalized := rd8144.withIndices
      (k' := k + 31) (C' := C + 114) (by omega) (by omega)
    simpa using normalized
  · rw [if_neg hlt]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 192)) = ⟨0⟩ := by
      apply ult_zero
      rw [hthreshold]
      omega
    have rd8144 := GeneratedTraces.trace_8070_notTaken
      (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
    have normalized := rd8144.withIndices
      (k' := k + 8) (C' := C + 29) (by omega) (by omega)
    simpa using normalized

def through64 (x : UInt256) : StageResult :=
  let first := stage128 x
  let second := stage64 first.x first.n
  { second with
    steps := first.steps + second.steps
    gas := first.gas + second.gas }

/-- Compose the first two binary-search decisions without enumerating their four path pairs. -/
theorem through64Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {x ret : UInt256}
    (hdepth : tail.length ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩
      (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through64 x
    RDx runtimeBytecode ee g s0 ⟨8137⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := stage128 x
  let second := stage64 first.x first.n
  have rd8077 := stage128Exact (by omega) h
  have hnWord : first.n + 64 < UInt256.size := by
    unfold first stage128
    split <;> simp_all [UInt256.size]
  have rd8144 := stage64Exact hnWord hdepth rd8077
  simpa only [through64, first, second, Nat.add_assoc] using rd8144

end Modexp.MultiLimbClz
