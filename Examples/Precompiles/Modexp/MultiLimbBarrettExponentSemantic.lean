import Examples.Precompiles.Modexp.MultiLimbBarrettExponentTrace
import Examples.Precompiles.Modexp.MultiLimbBarrettReusedCall

/-!
# Arithmetic contract for Barrett exponent-loop calls

This module interprets the exact `_barrettMulMod` call-and-copy boundary.  The reduction selector
still executes the two full products, q1/q3 slices, truncated product, subtraction, and selected
correction path; this layer only connects its concrete result limbs and the continuation's
`MCOPY` to the pure modular-product model.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbBarrettExponentSemantic

open Modexp.MultiLimbBarrettExponentTrace
open Modexp.MultiLimbBarrettCorrection
open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbBarrettReduction
open Modexp.MultiLimbBarrettReusedCall
open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbBarrettTruncatedMul
open Modexp.MultiLimbExponentTrace
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Interpret the payload of a persistent exponent accumulator as little-endian 256-bit limbs. -/
def barrettAccumulatorValue (kWords : Nat) (r : UInt256) (mem : ByteArray) : Nat :=
  Modexp.wordLimbsToNat (memoryWordsFrom mem (r + ⟨32⟩).toNat kWords)

/-- Numeric and memory geometry needed to interpret one selected Barrett call and its copy-back.
These are the allocator and normalized-modulus obligations used by the concrete reduction, not a
replacement for any part of that computation. -/
structure BarrettCallSemanticGeometry
    (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray) (aw a b n mu target : UInt256)
    (fp kWords : Nat) (selected : BarrettCorrectionSelection)
    (aValue bValue nValue : Nat) : Prop where
  scratch : ScratchInvariant I fuel mem aw a b n mu fp kWords selected
  aValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (a.toNat + 32) kWords) = aValue
  bValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (b.toNat + 32) kWords) = bValue
  nValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue
  muValueEq : Modexp.wordLimbsToNat
    (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
      UInt256.size ^ (2 * kWords) / nValue
  nPos : 0 < nValue
  nNormalized : UInt256.size ^ (kWords - 1) ≤ nValue
  nFits : nValue < UInt256.size ^ kWords
  productBound : aValue * bValue < UInt256.size ^ (2 * kWords)
  copySource :
    (UInt256.ofNat (barrettCallResultFp fp kWords) + ⟨32⟩).toNat + 32 * kWords ≤
      selected.memory.size
  copyTarget : (target + ⟨32⟩).toNat ≤ selected.memory.size

/-- The real selected Barrett reduction followed by PC 3406's `MCOPY` updates the persistent
accumulator with exactly the pure modular product of the two input arrays. -/
theorem selectedBarrettCallAndCopy_value
    {I : ExecutionEnv} {fuel : Nat} {mem : ByteArray} {aw a b n mu target : UInt256}
    {fp kWords : Nat} {selected : BarrettCorrectionSelection}
    {aValue bValue nValue : Nat}
    (geometry : BarrettCallSemanticGeometry I fuel mem aw a b n mu target fp kWords selected
      aValue bValue nValue) :
    barrettAccumulatorValue kWords target
        (exponentCopyMemory selected.memory
          (UInt256.ofNat (barrettCallResultFp fp kWords)) target (UInt256.ofNat kWords)) =
      (aValue * bValue) % nValue := by
  have hvalue := geometry.scratch.selectedResultValue geometry.aValueEq geometry.bValueEq
    geometry.nValueEq geometry.muValueEq (x := aValue * bValue) rfl geometry.nPos
    geometry.nNormalized geometry.nFits geometry.productBound
  let resultFp := barrettCallResultFp fp kWords
  have hresultFp64 : resultFp < 2 ^ 64 := by
    have hresultBound := geometry.scratch.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hresultBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound ⊢
    omega
  have hsource64 : resultFp + 32 < 2 ^ 64 := by
    have hresultBound := geometry.scratch.scratchBound
    dsimp only [resultFp, barrettCallResultFp]
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hresultBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound ⊢
    omega
  have hsourceNat : (UInt256.ofNat resultFp + ⟨32⟩).toNat = resultFp + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (hresultFp64.trans (by decide)),
      show (⟨32⟩ : UInt256).toNat = 32 by native_decide,
      Nat.mod_eq_of_lt (hsource64.trans (by decide))]
  have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp :=
    UInt256.toNat_ofNat_of_lt (hresultFp64.trans (by decide))
  have hbytes :
      (UInt256.shiftLeft (UInt256.ofNat kWords) ⟨5⟩).toNat = 32 * kWords :=
    ushl5_ofNat_toNat kWords (by
      have hwords := geometry.scratch.words
      omega)
  have hcopy := finalCopyMemory_words_eq_source kWords selected.memory
    (UInt256.ofNat resultFp + ⟨32⟩) (target + ⟨32⟩)
    (UInt256.shiftLeft (UInt256.ofNat kWords) ⟨5⟩)
    geometry.scratch.wordsPos hbytes (by simpa only [resultFp] using geometry.copySource)
    geometry.copyTarget
  unfold barrettAccumulatorValue exponentCopyMemory
  rw [hcopy, hsourceNat]
  have hcallResult : Modexp.MultiLimbBarrettReusedCall.callResultFp fp kWords = resultFp := rfl
  rw [hcallResult, hresultNat] at hvalue
  exact hvalue

end Modexp.MultiLimbBarrettExponentSemantic
