import Benchmarks.ActAmm4.SwapArithmeticSuccess
import Benchmarks.ActAmm4.SwapSourceFull
import Benchmarks.ActAmm4.SwapBalance1Transport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapInput0WordCase
    {σE : AccountMap} {I : ExecutionEnv}
    {evmS : EVM.State} {out0 : ByteArray}
    (hslot : solcSlotWord σE I ⟨5⟩ =
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨5⟩)
    (hlo : 32 ≤ out0.size)
    (hle : (amm4SwapAmount0Word I).toNat ≤
      (solcSlotWord σE I ⟨5⟩).toNat) :
    let q0 := amm4SwapAmount0Word I
    let v0 := UInt256.ofNat (fromByteArrayBigEndian (out0.extract 0 32))
    let a0 := UInt256.ofNat (amm4SwapInput0Nat evmS I out0)
    ((UInt256.sub (solcSlotWord σE I ⟨5⟩) q0).toNat < v0.toNat ∧
      a0 = UInt256.sub v0 (UInt256.sub (solcSlotWord σE I ⟨5⟩) q0)) ∨
    (v0.toNat ≤ (UInt256.sub (solcSlotWord σE I ⟨5⟩) q0).toNat ∧ a0 = ⟨0⟩) := by
  let q0 := amm4SwapAmount0Word I
  let v0 := UInt256.ofNat (fromByteArrayBigEndian (out0.extract 0 32))
  let a0 := UInt256.ofNat (amm4SwapInput0Nat evmS I out0)
  have hv0 : v0.toNat =
      fromByteArrayBigEndian (out0.extract 0 32) :=
    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hsub : (UInt256.sub (solcSlotWord σE I ⟨5⟩) q0).toNat =
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨5⟩).toNat -
        q0.toNat := by
    rw [usub_toNat hle, hslot]
  dsimp [q0] at hsub
  by_cases hgt : (Solm.EVM.storageLoad evmS
      evmS.executionEnv.codeOwner ⟨5⟩).toNat - q0.toNat <
      fromByteArrayBigEndian (out0.extract 0 32)
  all_goals dsimp [q0] at hgt
  · left
    constructor
    · rw [hsub, hv0]
      exact hgt
    · apply u256_inj
      have hle' : (UInt256.sub (solcSlotWord σE I ⟨5⟩) q0).toNat ≤
          v0.toNat := by rw [hsub, hv0]; omega
      rw [usub_toNat hle']
      have hinputLt : amm4SwapInput0Nat evmS I out0 < UInt256.size := by
        simp [amm4SwapInput0Nat, hgt, amm4SwapAmount0InPosNat]
        exact lt_of_le_of_lt (Nat.sub_le _ _)
          (fromByteArrayBigEndian_extract0_32_lt hlo)
      rw [show a0.toNat = amm4SwapInput0Nat evmS I out0 from
        ulit_toNat' _ hinputLt]
      simp [amm4SwapInput0Nat, hgt, amm4SwapAmount0InPosNat,
        hv0, hsub, q0]
  · right
    constructor
    · rw [hsub, hv0]
      omega
    · simp [a0, amm4SwapInput0Nat, hgt]
      decide

theorem amm4SwapInput1WordCase
    {σE : AccountMap} {I : ExecutionEnv}
    {evmS : EVM.State} {out1 : ByteArray}
    (hslot : solcSlotWord σE I ⟨6⟩ =
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨6⟩)
    (hlo : 32 ≤ out1.size)
    (hle : (amm4SwapAmount1Word I).toNat ≤
      (solcSlotWord σE I ⟨6⟩).toNat) :
    let q1 := amm4SwapAmount1Word I
    let v1 := UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))
    let a1 := UInt256.ofNat (amm4SwapInput1Nat evmS I out1)
    ((UInt256.sub (solcSlotWord σE I ⟨6⟩) q1).toNat < v1.toNat ∧
      a1 = UInt256.sub v1 (UInt256.sub (solcSlotWord σE I ⟨6⟩) q1)) ∨
    (v1.toNat ≤ (UInt256.sub (solcSlotWord σE I ⟨6⟩) q1).toNat ∧ a1 = ⟨0⟩) := by
  let q1 := amm4SwapAmount1Word I
  let v1 := UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))
  let a1 := UInt256.ofNat (amm4SwapInput1Nat evmS I out1)
  have hv1 : v1.toNat =
      fromByteArrayBigEndian (out1.extract 0 32) :=
    ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hsub : (UInt256.sub (solcSlotWord σE I ⟨6⟩) q1).toNat =
      (Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨6⟩).toNat -
        q1.toNat := by
    rw [usub_toNat hle, hslot]
  dsimp [q1] at hsub
  by_cases hgt : (Solm.EVM.storageLoad evmS
      evmS.executionEnv.codeOwner ⟨6⟩).toNat - q1.toNat <
      fromByteArrayBigEndian (out1.extract 0 32)
  all_goals dsimp [q1] at hgt
  · left
    constructor
    · rw [hsub, hv1]
      exact hgt
    · apply u256_inj
      have hle' : (UInt256.sub (solcSlotWord σE I ⟨6⟩) q1).toNat ≤
          v1.toNat := by rw [hsub, hv1]; omega
      rw [usub_toNat hle']
      have hinputLt : amm4SwapInput1Nat evmS I out1 < UInt256.size := by
        simp [amm4SwapInput1Nat, hgt, amm4SwapAmount1InPosNat]
        exact lt_of_le_of_lt (Nat.sub_le _ _)
          (fromByteArrayBigEndian_extract0_32_lt hlo)
      rw [show a1.toNat = amm4SwapInput1Nat evmS I out1 from
        ulit_toNat' _ hinputLt]
      simp [amm4SwapInput1Nat, hgt, amm4SwapAmount1InPosNat,
        hv1, hsub, q1]
  · right
    constructor
    · rw [hsub, hv1]
      omega
    · simp [a1, amm4SwapInput1Nat, hgt]
      decide

end Benchmarks.ActAmm4
