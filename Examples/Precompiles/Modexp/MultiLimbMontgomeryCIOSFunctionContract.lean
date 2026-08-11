import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSContract

/-! # Allocated CIOS Montgomery-multiplication function contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbMontgomeryCIOSCall
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Concrete layout and arithmetic facts needed to interpret a successful allocated `_montMul`.
The fields are the hypotheses of the complete CIOS scan and finalizer contract. -/
structure CIOSFunctionSemanticGeometry
    (words fp : Nat) (aBase bBase nBefore n0inv : UInt256)
    (selected : CIOSFunctionSelection) (modulus rInv left right : Nat) : Prop where
  layout : CIOSOuterLayout words selected.head.setup.bP selected.head.setup.tP
    selected.head.setup.tEnd (selected.head.setup.tEnd + ⟨32⟩) selected.head.setup.nP
    (selected.head.setup.tP + ⟨32⟩) nBefore
    (selected.head.setup.tEnd + UInt256.lnot ⟨31⟩) selected.head.setup.outer
  sourceFit : ∀ i, i ≤ words →
    (ciosOuterIterate words selected.head.setup.bP selected.head.setup.tP
      selected.head.setup.tEnd (selected.head.setup.tEnd + ⟨32⟩)
      selected.head.setup.nP n0inv (selected.head.setup.tP + ⟨32⟩) nBefore
      (selected.head.setup.tEnd + UInt256.lnot ⟨31⟩) i
      selected.head.setup.outer).aOff.toNat + 32 + 31 < UInt256.size
  extraZero : Modexp.MultiLimbMemoryModel.memoryWordNat selected.head.setup.outer.memory
    (selected.head.setup.tEnd + ⟨32⟩).toNat = 0
  scratchZero : ciosScratchValue words selected.head.setup.tP selected.head.setup.tEnd
    (selected.head.setup.tEnd + ⟨32⟩) selected.head.setup.outer = 0
  sourceEnd : selected.head.setup.outer.aOff.toNat + 32 * words =
    (aBase + selected.head.setup.kWords + ⟨32⟩).toNat
  sourceAddressFit : selected.head.setup.outer.aOff.toNat + 32 * words < UInt256.size
  sourceSeparate : selected.head.setup.outer.aOff.toNat + 32 * words ≤
    selected.head.setup.tP.toNat
  multiplierSeparate : selected.head.setup.bP.toNat + 32 * words ≤
    selected.head.setup.tP.toNat
  higherPtr : (nBefore + ⟨64⟩).toNat = selected.head.setup.nP.toNat + 32
  modulusSeparate : selected.head.setup.nP.toNat + 32 * words ≤
    selected.head.setup.tP.toNat
  inverse : Modexp.MultiLimbMemoryModel.memoryWordNat selected.head.setup.outer.memory
    selected.head.setup.nP.toNat * n0inv.toNat % UInt256.size = UInt256.size - 1
  finalize : CIOSFinalizeGeometry words selected.outer.final.memory
    selected.outer.final.activeWords nBefore selected.head.setup.tP selected.head.setup.kWords
    selected.head.setup.tEnd selected.head.setup.nP selected.head.setup.resultPtr
    (UInt256.ofNat fp)
  modulusPos : 0 < modulus
  radixInverse : UInt256.size ^ words * rInv % modulus = 1 % modulus
  multiplierReduced : right < modulus
  sourceValue : Modexp.wordLimbsToNat
    (memoryWordsFrom selected.head.setup.outer.memory
      selected.head.setup.outer.aOff.toNat words) = left
  multiplierValue : Modexp.wordLimbsToNat
    (memoryWordsFrom selected.head.setup.outer.memory selected.head.setup.bP.toNat words) = right
  modulusValue : Modexp.wordLimbsToNat
    (memoryWordsFrom selected.head.setup.outer.memory selected.head.setup.nP.toNat words) = modulus

/-- A successful exposed `_montMul` selector computes the pure Montgomery product. Exact execution,
steps, and gas are supplied by `selectedCIOSFunctionExact`. -/
theorem selectedCIOSFunction_value
    {zeroFuel outerFuel compareFuel subFuel words fp : Nat}
    {mem : ByteArray} {aw : UInt256} {aBase bBase nBefore n0inv returnPc : UInt256}
    {selected : CIOSFunctionSelection}
    (modulus rInv left right : Nat)
    (geometry : CIOSFunctionSemanticGeometry words fp aBase bBase nBefore n0inv selected
      modulus rInv left right)
    (hselect : selectCIOSFunction zeroFuel outerFuel compareFuel subFuel mem aw words fp
      aBase bBase nBefore n0inv returnPc = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalize.memory selected.head.setup.resultPtr.toNat words) =
      (left * right * rInv) % modulus := by
  unfold selectCIOSFunction at hselect
  cases hp : selectCIOSFunctionPrefix zeroFuel mem aw words fp aBase bBase nBefore n0inv
      returnPc with
  | none =>
      rw [hp] at hselect
      contradiction
  | some head =>
      rw [hp] at hselect
      let setup := head.setup
      let shiftedOut := setup.tEnd + UInt256.lnot ⟨31⟩
      let tk1Off := setup.tEnd + ⟨32⟩
      let tOff := setup.tP + ⟨32⟩
      let aEnd := aBase + setup.kWords + ⟨32⟩
      cases ho : selectCIOSOuter outerFuel words setup.bP setup.tP setup.tEnd tk1Off
          setup.nP n0inv tOff nBefore shiftedOut aEnd setup.outer with
      | none =>
          simp [setup, shiftedOut, tk1Off, tOff, aEnd, ho] at hselect
      | some outer =>
          simp only [setup, shiftedOut, tk1Off, tOff, aEnd, ho] at hselect
          cases hf : selectCIOSFinalize compareFuel subFuel outer.final.memory
              outer.final.activeWords nBefore setup.tP setup.kWords setup.tEnd setup.nP
              setup.resultPtr (UInt256.ofNat fp) with
          | none =>
              rw [hf] at hselect
              contradiction
          | some finalize =>
              rw [hf] at hselect
              injection hselect with heq
              subst selected
              have hmodulusValue : Modexp.wordLimbsToNat
                    (memoryWordsFrom setup.outer.memory setup.nP.toNat words) = modulus := by
                simpa [setup] using geometry.modulusValue
              have hmultiplierValue : Modexp.wordLimbsToNat
                    (memoryWordsFrom setup.outer.memory setup.bP.toNat words) = right := by
                simpa [setup] using geometry.multiplierValue
              have hvalue := selectedCIOSMultiLimb_value words setup.bP setup.tP setup.tEnd
                tk1Off setup.nP n0inv tOff nBefore shiftedOut aEnd setup.kWords
                setup.resultPtr (UInt256.ofNat fp) setup.outer outer finalize rInv
                geometry.layout geometry.sourceFit geometry.extraZero geometry.scratchZero
                geometry.sourceEnd geometry.sourceAddressFit geometry.sourceSeparate
                geometry.multiplierSeparate geometry.higherPtr geometry.modulusSeparate
                geometry.inverse (by simpa [setup, tk1Off, tOff, shiftedOut] using ho)
                geometry.finalize (by simpa [setup] using hf)
                (by rw [hmodulusValue]; exact geometry.modulusPos)
                (by rw [hmodulusValue]; exact geometry.radixInverse)
                (by rw [hmultiplierValue, hmodulusValue]; exact geometry.multiplierReduced)
              simpa [setup, geometry.sourceValue, geometry.multiplierValue,
                geometry.modulusValue]
                using hvalue

end Modexp.MultiLimbMontgomeryCIOSSemantic
