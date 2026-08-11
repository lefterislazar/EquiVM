import Examples.Precompiles.Modexp.Allocation
import Examples.Precompiles.Modexp.MultiLimbGenerated
import Examples.Precompiles.Modexp.Spec

/-!
# Arbitrary-length odd-backend modulus conversion

This module specializes the generated `bytesToLimbs` loop proof to the actual Montgomery caller
stack. It exposes the exact state at PC 2006 after all full and partial limbs have been copied.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp
namespace MultiLimbOddConversion

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def wordArrayLength (modulusSize : Nat) : Nat :=
  (modulusSize + 31) / 32

def resultPtr (baseSize exponentSize modulusSize : Nat) : Nat :=
  operandFreePtr baseSize exponentSize modulusSize

def wordArrayPtr (baseSize exponentSize modulusSize : Nat) : Nat :=
  resultPtr baseSize exponentSize modulusSize + bytesAllocationSize modulusSize

def continuationTail (baseSize exponentSize modulusSize : Nat) : List UInt256 :=
  [UInt256.ofNat operandBasePtr,
    UInt256.ofNat (wordArrayLength modulusSize),
    UInt256.ofNat (operandExponentPtr baseSize),
    UInt256.ofNat (resultPtr baseSize exponentSize modulusSize),
    UInt256.ofNat modulusSize,
    ⟨805⟩,
    ⟨1271⟩,
    UInt256.ofNat (resultPtr baseSize exponentSize modulusSize),
    ⟨173⟩]

def loopEntryStack (baseSize exponentSize modulusSize : Nat) : List UInt256 :=
  MultiLimbGenerated.fullWordLoopStack
    ⟨0⟩ (UInt256.ofNat (modulusSize / 32))
    (UInt256.ofNat (operandModulusPtr baseSize exponentSize))
    (UInt256.ofNat modulusSize) ⟨2006⟩
    (UInt256.ofNat (wordArrayPtr baseSize exponentSize modulusSize))
    (continuationTail baseSize exponentSize modulusSize)

def convertedStack (baseSize exponentSize modulusSize : Nat) : List UInt256 :=
  UInt256.ofNat (wordArrayPtr baseSize exponentSize modulusSize) ::
    continuationTail baseSize exponentSize modulusSize

def convertedMemory (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : ByteArray :=
  MultiLimbGenerated.bytesToLimbsMemory mem aw
    (UInt256.ofNat (operandModulusPtr baseSize exponentSize))
    (UInt256.ofNat (wordArrayPtr baseSize exponentSize modulusSize)) modulusSize

def convertedActiveWords (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : UInt256 :=
  MultiLimbGenerated.bytesToLimbsActiveWords mem aw
    (UInt256.ofNat (operandModulusPtr baseSize exponentSize))
    (UInt256.ofNat (wordArrayPtr baseSize exponentSize modulusSize)) modulusSize

def conversionSteps (modulusSize : Nat) : Nat :=
  MultiLimbGenerated.bytesToLimbsBodySteps modulusSize

def conversionGas (mem : ByteArray) (aw : UInt256)
    (baseSize exponentSize modulusSize : Nat) : Nat :=
  MultiLimbGenerated.bytesToLimbsBodyGas mem aw
    (UInt256.ofNat (operandModulusPtr baseSize exponentSize))
    (UInt256.ofNat (wordArrayPtr baseSize exponentSize modulusSize)) modulusSize

/-- Exact execution of the complete arbitrary-length modulus conversion after the caller has taken
the positive full-word guard. The incoming memory is unrestricted: the theorem computes the exact
memory and active-word result rather than assuming the copied limbs. -/
theorem exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C baseSize exponentSize modulusSize : Nat}
    (hmodulusBound : modulusSize ≤ 1024)
    (hmodulusLarge : 32 < modulusSize)
    (h : RDx runtimeBytecode ee g s0 ⟨2906⟩
      (loopEntryStack baseSize exponentSize modulusSize)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2006⟩
      (convertedStack baseSize exponentSize modulusSize)
      (convertedMemory mem aw baseSize exponentSize modulusSize)
      (convertedActiveWords mem aw baseSize exponentSize modulusSize)
      rdata acc (k + conversionSteps modulusSize)
      (C + conversionGas mem aw baseSize exponentSize modulusSize) := by
  have hfull : 0 < modulusSize / 32 :=
    Nat.div_pos (by omega) (by decide)
  have hret : (D_J runtimeBytecode 0).contains ⟨2006⟩ = true := by
    native_decide
  simpa [loopEntryStack, convertedStack, convertedMemory, convertedActiveWords,
    conversionSteps, conversionGas] using
    (MultiLimbGenerated.bytesToLimbsFromBodyOfNat
      (dataLen := modulusSize)
      (dataPtr := UInt256.ofNat (operandModulusPtr baseSize exponentSize))
      (ret := ⟨2006⟩)
      (limbsPtr := UInt256.ofNat (wordArrayPtr baseSize exponentSize modulusSize))
      (tail := continuationTail baseSize exponentSize modulusSize)
      (by simp [continuationTail]) hmodulusBound hfull hret h)

end MultiLimbOddConversion
end Modexp
