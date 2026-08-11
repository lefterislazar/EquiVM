import Examples.Precompiles.Modexp.MultiLimbBarrettExponentContract
import Examples.Precompiles.Modexp.MultiLimbLimbsToBytes

/-!
# Barrett result serialization

This module composes the deployed PC 1745 trampoline, arbitrary-length `limbsToBytes`, and the
PC 805 caller return.  PC 1750 is intentionally absent: it belongs to the one-word Barrett path.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettResult

open Modexp.MultiLimbLimbsToBytes
open Modexp.MultiLimbBarrettAccumulator
open Modexp.MultiLimbBarrettExponentSetup
open Modexp.MultiLimbExponentTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def serializationSteps (dataLen : Nat) : Nat :=
  5 + limbsToBytesSteps dataLen

def serializationGas (dataLen : Nat) : Nat :=
  21 + limbsToBytesGas dataLen

def resultMemory (mem : ByteArray) (aw limbs out : UInt256) (dataLen : Nat) : ByteArray :=
  limbsToBytesMemory mem aw limbs out dataLen

def executionSteps (selected : BarrettLoopSetupSelection) (dataLen : Nat) : Nat :=
  MultiLimbBarrettExponentContract.executionSteps selected + serializationSteps dataLen

def executionGas (aw : UInt256) (fp k : Nat) (exponent : UInt256)
    (selected : BarrettLoopSetupSelection) (dataLen : Nat) : Nat :=
  MultiLimbBarrettExponentContract.executionGas aw fp k exponent selected +
    serializationGas dataLen

def freshExecutionSteps (selected : FreshBarrettLoopSetupSelection) (dataLen : Nat) : Nat :=
  MultiLimbBarrettExponentContract.freshExecutionSteps selected + serializationSteps dataLen

def freshExecutionGas (aw : UInt256) (fp k : Nat) (exponent : UInt256)
    (selected : FreshBarrettLoopSetupSelection) (dataLen : Nat) : Nat :=
  MultiLimbBarrettExponentContract.freshExecutionGas aw fp k exponent selected +
    serializationGas dataLen

/-- Serialize the selected accumulator through the exact multi-limb caller continuation and
return the preallocated bytes pointer to the Barrett caller. -/
theorem serializeAndReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dataLen : Nat} {tail : List UInt256}
    {limbs out retBar ret : UInt256}
    (hdepth : tail.length + 9 ≤ 1014)
    (hlen : dataLen ≤ 1024)
    (hvalid : ∀ j, j < dataLen / 32 →
      ValidStep aw limbs (UInt256.ofNat dataLen) out
        (iterate aw limbs (UInt256.ofNat dataLen) out j (initialState mem)))
    (hpartial : dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState mem aw limbs out dataLen).memory
      aw limbs (UInt256.ofNat dataLen) out)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true)
    (h : RDx runtimeBytecode ee g s0 ⟨1745⟩
      (limbs :: out :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: out :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 retBar (out :: ret :: tail)
      (resultMemory mem aw limbs out dataLen) aw rdata acc
      (steps + serializationSteps dataLen)
      (gasUsed + serializationGas dataLen) := by
  have rd3559 := evm_run h with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨3559⟩ (by decide),
    jump (by native_decide)]
  have rd805 := totalOfNat (tail := retBar :: out :: ret :: tail)
    (by simp only [List.length_cons]; omega) hlen hvalid hpartial
    (by native_decide) (rd3559.withPC (pc' := ⟨3559⟩) (by native_decide))
  have rdReturn := GeneratedTraces.trace_805_jump
    (tail := out :: ret :: tail) (by simp only [List.length_cons]; omega)
    rd805 (by native_decide) hretBar
  have normalized := rdReturn.withIndices
    (k' := steps + serializationSteps dataLen) (by
      unfold serializationSteps
      omega)
    (C' := gasUsed + serializationGas dataLen) (by
      unfold serializationGas
      omega)
  simpa [resultMemory] using normalized

/-- Allocate the Barrett accumulator, execute the selected arbitrary exponent computation,
serialize all requested result bytes, and return the original result pointer. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel dataLen : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced retBar result ret : UInt256}
    {selected : BarrettLoopSetupSelection}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : BarrettLoopSetupValid I callFuel k (fp + wordArrayAllocationSize k)
      (UInt256.ofNat fp) baseReduced
      modulus mu exponent
      (exponentArrayLength (initializedMemory mem fp k) (allocatedWords aw fp k) exponent)
      (initializedMemory mem fp k) (allocatedWords aw fp k) selected)
    (hlen : dataLen ≤ 1024)
    (hserialize : ∀ j, j < dataLen / 32 →
      ValidStep selected.activeWords (UInt256.ofNat fp) (UInt256.ofNat dataLen) result
        (iterate selected.activeWords (UInt256.ofNat fp) (UInt256.ofNat dataLen) result j
          (initialState selected.memory)))
    (hpartial : dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState selected.memory selected.activeWords
        (UInt256.ofNat fp) result dataLen).memory
      selected.activeWords (UInt256.ofNat fp) (UInt256.ofNat dataLen) result)
    (hdepth : tail.length + 43 ≤ 1015)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) retBar
      (result :: ret :: tail)
      (resultMemory selected.memory selected.activeWords (UInt256.ofNat fp) result dataLen)
      selected.activeWords rdata acc
      (steps + executionSteps selected dataLen)
      (gasUsed + executionGas aw fp k exponent selected dataLen) := by
  have rd1745 := MultiLimbBarrettExponentContract.exact
    (tail := result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail)
    hkTwo hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hawFit hfit hread hcalldata
    valid (by simp only [List.length_cons]; omega) (by native_decide) h
  have rdone := serializeAndReturn (tail := tail) (limbs := UInt256.ofNat fp)
    (out := result) (ret := ret) (by omega) hlen hserialize hpartial hretBar rd1745
  have normalized := rdone.withIndices
    (k' := steps + executionSteps selected dataLen) (by
      unfold executionSteps
      omega)
    (C' := gasUsed + executionGas aw fp k exponent selected dataLen) (by
      unfold executionGas
      omega)
  exact normalized

/-- Fresh-scratch counterpart of `exact`, retaining the exposed first-call selector through
serialization and its exact path-sensitive gas. -/
theorem freshExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k callFuel dataLen : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced retBar result ret : UInt256}
    {selected : FreshBarrettLoopSetupSelection}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : FreshBarrettLoopSetupValid I callFuel k (fp + wordArrayAllocationSize k)
      (UInt256.ofNat fp) baseReduced modulus mu exponent
      (exponentArrayLength (initializedMemory mem fp k) (allocatedWords aw fp k) exponent)
      (initializedMemory mem fp k) (allocatedWords aw fp k) selected)
    (hlen : dataLen ≤ 1024)
    (hserialize : ∀ j, j < dataLen / 32 →
      ValidStep selected.activeWords (UInt256.ofNat fp) (UInt256.ofNat dataLen) result
        (iterate selected.activeWords (UInt256.ofNat fp) (UInt256.ofNat dataLen) result j
          (initialState selected.memory)))
    (hpartial : dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState selected.memory selected.activeWords
        (UInt256.ofNat fp) result dataLen).memory
      selected.activeWords (UInt256.ofNat fp) (UInt256.ofNat dataLen) result)
    (hdepth : tail.length + 43 ≤ 1015)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) retBar
      (result :: ret :: tail)
      (resultMemory selected.memory selected.activeWords (UInt256.ofNat fp) result dataLen)
      selected.activeWords rdata acc
      (steps + freshExecutionSteps selected dataLen)
      (gasUsed + freshExecutionGas aw fp k exponent selected dataLen) := by
  have rd1745 := MultiLimbBarrettExponentContract.freshExact
    (tail := result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail)
    hkTwo hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hawFit hfit hread hcalldata
    valid (by simp only [List.length_cons]; omega) (by native_decide) h
  have rdone := serializeAndReturn (tail := tail) (limbs := UInt256.ofNat fp)
    (out := result) (ret := ret) (by omega) hlen hserialize hpartial hretBar rd1745
  have normalized := rdone.withIndices
    (k' := steps + freshExecutionSteps selected dataLen) (by
      unfold freshExecutionSteps
      omega)
    (C' := gasUsed + freshExecutionGas aw fp k exponent selected dataLen) (by
      unfold freshExecutionGas
      omega)
  exact normalized

end Modexp.MultiLimbBarrettResult
