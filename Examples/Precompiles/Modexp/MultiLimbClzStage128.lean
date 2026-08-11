import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupContract

/-! # Exact first stage of the deployed leading-zero helper -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbClz

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure StageResult where
  x : UInt256
  n : Nat
  steps : Nat
  gas : Nat

def stage128 (x : UInt256) : StageResult :=
  if x.toNat < 2 ^ 128 then
    { x := x.shiftLeft ⟨128⟩, n := 128, steps := 17, gas := 57 }
  else
    { x := x, n := 0, steps := 9, gas := 31 }

/-- Execute the first `_clz` decision and rejoin at the 192-bit test. -/
theorem stage128Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {x ret : UInt256}
    (hdepth : tail.length ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩
      (x :: ret :: tail) mem aw rdata acc k C) :
    let result := stage128 x
    RDx runtimeBytecode ee g s0 ⟨8070⟩
      (result.x :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  unfold stage128
  by_cases hlt : x.toNat < 2 ^ 128
  · rw [if_pos hlt]
    have hthreshold : (UInt256.ofNat (2 ^ 128)).toNat = 2 ^ 128 := by
      rw [UInt256.toNat_ofNat_of_lt]
      norm_num [UInt256.size]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 128)) ≠ ⟨0⟩ := by
      rw [ult_one]
      · native_decide
      · simpa [hthreshold] using hlt
    have rd8471 := GeneratedTraces.trace_8042_taken
      (by omega) h (by native_decide) hcondition (by native_decide)
    have rd8077 := evm_run rd8471 with [
      jumpdest,
      pushCanonical 1 .PUSH1 ⟨128⟩ (by decide),
      swap3,
      pop,
      dup3,
      shl,
      pushCanonical 2 .PUSH2 ⟨8070⟩ (by decide),
      jump (by native_decide)
    ]
    have normalized := rd8077.withIndices
      (k' := k + 17) (C' := C + 57) (by omega) (by omega)
    simpa using normalized
  · rw [if_neg hlt]
    have hthreshold : (UInt256.ofNat (2 ^ 128)).toNat = 2 ^ 128 := by
      rw [UInt256.toNat_ofNat_of_lt]
      norm_num [UInt256.size]
    have hcondition : UInt256.lt x (UInt256.ofNat (2 ^ 128)) = ⟨0⟩ := by
      apply ult_zero
      rw [hthreshold]
      omega
    have rd8077 := GeneratedTraces.trace_8042_notTaken
      (by omega) h (by native_decide) hcondition
    have normalized := rd8077.withIndices
      (k' := k + 9) (C' := C + 31) (by omega) (by omega)
    simpa using normalized

end Modexp.MultiLimbClz
