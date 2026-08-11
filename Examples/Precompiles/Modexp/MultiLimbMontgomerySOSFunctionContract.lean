import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSContract

/-! # Allocated SOS Montgomery-square function contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSCall
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sosFunctionAllocatedMemory (mem : ByteArray) (fp words : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words

def sosFunctionAllocatedAw (aw : UInt256) (fp words : Nat) : UInt256 :=
  newWordArrayWords aw fp words

def sosFunctionSP (fp words : Nat) : UInt256 :=
  UInt256.ofNat (fp + wordArrayAllocationSize words)

def sosFunctionKWord (words : Nat) : UInt256 := UInt256.ofNat words

def sosFunctionKWords (words : Nat) : UInt256 :=
  UInt256.shiftLeft (sosFunctionKWord words) ⟨5⟩

def sosFunctionAP (aBase : UInt256) : UInt256 := aBase + ⟨32⟩

def sosFunctionAEnd (aBase : UInt256) (words : Nat) : UInt256 :=
  ⟨32⟩ + (aBase + sosFunctionKWords words)

def sosFunctionResultPtr (fp : Nat) : UInt256 := UInt256.ofNat fp + ⟨32⟩

def sosFunctionNP (nBefore : UInt256) : UInt256 := nBefore + ⟨32⟩

def sosFunctionSEnd (fp words : Nat) : UInt256 :=
  sosFunctionSP fp words + UInt256.shiftLeft (sosFunctionKWord words) ⟨6⟩ + ⟨32⟩

def sosFunctionZeroState (mem : ByteArray) (aw : UInt256) (fp words : Nat) : SOSZeroState := {
  ptr := sosFunctionSP fp words
  memory := sosSetupMemory (sosFunctionAllocatedMemory mem fp words)
    (sosFunctionSEnd fp words)
  activeWords := sosSetupAw (sosFunctionAllocatedAw aw fp words) }

/-- Concrete allocation, pointer, memory, and Montgomery facts needed to interpret one successful
`selectSOSFunction`.  These are layout facts, not a replacement for the exposed selector. -/
structure SOSFunctionSemanticGeometry
    (mem : ByteArray) (aw : UInt256) (words fp : Nat)
    (nBefore n0inv aBase : UInt256) (selected : SOSFunctionSelection)
    (modulus rInv operand : Nat) : Prop where
  wordsPos : 0 < words
  zeroCovered : MemoryCovered (sosFunctionZeroState mem aw fp words).memory
    (sosFunctionZeroState mem aw fp words).activeWords
  zeroAwFit : (sosFunctionZeroState mem aw fp words).activeWords.toNat * 32 < UInt256.size
  zeroMem32 : 32 ≤ (sosFunctionZeroState mem aw fp words).memory.size
  zeroMemoryLe : (sosFunctionZeroState mem aw fp words).memory.size ≤
    (sosFunctionZeroState mem aw fp words).ptr.toNat
  zeroGap : (sosFunctionZeroState mem aw fp words).ptr.toNat -
    (sosFunctionZeroState mem aw fp words).memory.size < USize.size
  sEnd : (sosFunctionSEnd fp words).toNat =
    (sosFunctionSP fp words).toNat + 32 * (2 * words + 1)
  aEnd : (sosFunctionAEnd aBase words).toNat =
    (sosFunctionAP aBase).toNat + 32 * words
  aFit : (sosFunctionAP aBase).toNat + 32 * words + 31 < UInt256.size
  sFit : (sosFunctionSP fp words).toNat + 32 * (2 * words + 1) + 31 < UInt256.size
  aSeparate : (sosFunctionAEnd aBase words).toNat ≤ (sosFunctionSP fp words).toNat
  sKEnd : (sosFunctionSP fp words + sosFunctionKWords words).toNat =
    (sosFunctionSP fp words).toNat + 32 * words
  nNext : (sosFunctionNP nBefore + ⟨32⟩).toNat =
    (sosFunctionNP nBefore).toNat + 32
  nBeforeStep : (nBefore + ⟨64⟩).toNat = (sosFunctionNP nBefore + ⟨32⟩).toNat
  nEnd : (nBefore + sosFunctionKWords words + ⟨32⟩).toNat =
    (sosFunctionNP nBefore).toNat + 32 * words
  nFit : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) + 31 < UInt256.size
  nSeparate : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤
    (sosFunctionSP fp words).toNat + 32
  nScratchSeparate : (sosFunctionNP nBefore).toNat + 32 * words ≤
    (sosFunctionSP fp words).toNat
  modulusValue : Modexp.wordLimbsToNat
    (memoryWordsFrom (sosFunctionZeroState mem aw fp words).memory
      (sosFunctionNP nBefore).toNat words) = modulus
  modulusPos : 0 < modulus
  inverse : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1
  operandValue : Modexp.wordLimbsToNat
    (memoryWordsFrom (sosFunctionZeroState mem aw fp words).memory
      (sosFunctionAP aBase).toNat words) = operand
  operandReduced : operand < modulus
  radixInverse : UInt256.size ^ words * rInv % modulus = 1 % modulus
  finalize : SOSFinalizeGeometry words
    selected.setup.initialized.arithmetic.suffix.square.reduction.final.memory
    selected.setup.initialized.arithmetic.suffix.square.reduction.final.activeWords nBefore
    selected.setup.initialized.arithmetic.suffix.square.reduction.final.sBase
    (sosFunctionKWords words) (nBefore + sosFunctionKWords words + ⟨32⟩)
    (sosFunctionNP nBefore) (sosFunctionResultPtr fp) (UInt256.ofNat fp)

/-- A successful allocated `_montSqr` selector computes the pure Montgomery square.  Exact
execution and exact selector gas are supplied by `selectedSOSFunctionExact`. -/
theorem selectedSOSFunction_value
    {zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      compareFuel subFuel : Nat}
    {mem : ByteArray} {aw : UInt256} {words fp : Nat}
    {nBefore n0inv returnPc aBase : UInt256} {selected : SOSFunctionSelection}
    (modulus rInv operand : Nat)
    (geometry : SOSFunctionSemanticGeometry mem aw words fp nBefore n0inv aBase selected
      modulus rInv operand)
    (hselect : selectSOSFunction zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw words fp nBefore n0inv
      returnPc aBase = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.setup.initialized.arithmetic.suffix.copy.memory
          (sosFunctionResultPtr fp).toNat words) =
      (operand * operand * rInv) % modulus := by
  unfold selectSOSFunction at hselect
  dsimp only at hselect
  cases hs : selectSOSSetup zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel (sosFunctionAllocatedMemory mem fp words)
      (sosFunctionAllocatedAw aw fp words) (UInt256.ofNat fp) nBefore n0inv
      (sosFunctionKWord words) aBase (sosFunctionSP fp words) with
  | none =>
      simp only [sosFunctionAllocatedMemory, sosFunctionAllocatedAw, sosFunctionSP,
        sosFunctionKWord] at hs
      rw [hs] at hselect
      contradiction
  | some setup =>
      simp only [sosFunctionAllocatedMemory, sosFunctionAllocatedAw, sosFunctionSP,
        sosFunctionKWord] at hs
      rw [hs] at hselect
      have hselected : selected = {
          setup := setup
          steps := 89 + setup.steps
          gas := 36 + newWordArrayGas aw fp words + setup.gas } := by
        exact Option.some.inj hselect.symm
      subst selected
      unfold selectSOSSetup at hs
      dsimp only at hs
      cases hi : selectSOSInitialized zeroFuel rowFuel productFuel doubleFuel diagonalFuel
          reductionFuel columnFuel carryFuel compareFuel subFuel
          (sosFunctionZeroState mem aw fp words) (sosFunctionSEnd fp words)
          (sosFunctionAP aBase) (sosFunctionAEnd aBase words) (sosFunctionSP fp words)
          n0inv (sosFunctionKWords words) nBefore (sosFunctionResultPtr fp)
          (sosFunctionNP nBefore) (UInt256.ofNat fp) with
      | none =>
          simp only [sosFunctionAllocatedMemory, sosFunctionAllocatedAw, sosFunctionSP,
            sosFunctionKWord, sosFunctionKWords, sosFunctionAP, sosFunctionAEnd,
            sosFunctionResultPtr, sosFunctionNP, sosFunctionSEnd, sosFunctionZeroState] at hi
          rw [hi] at hs
          contradiction
      | some initialized =>
          simp only [sosFunctionAllocatedMemory, sosFunctionAllocatedAw, sosFunctionSP,
            sosFunctionKWord, sosFunctionKWords, sosFunctionAP, sosFunctionAEnd,
            sosFunctionResultPtr, sosFunctionNP, sosFunctionSEnd, sosFunctionZeroState] at hi
          rw [hi] at hs
          have hsetup : setup = {
              initialized := initialized
              steps := 42 + initialized.steps
              gas := sosSetupGas (sosFunctionAllocatedAw aw fp words) + initialized.gas } := by
            simpa only [sosFunctionAllocatedAw] using Option.some.inj hs.symm
          subst setup
          exact selectedSOSInitialized_value words modulus rInv operand geometry.wordsPos rfl
            geometry.sEnd geometry.aEnd geometry.aFit geometry.sFit geometry.aSeparate
            geometry.zeroCovered geometry.zeroAwFit geometry.zeroMem32 geometry.zeroMemoryLe
            geometry.zeroGap geometry.sKEnd geometry.nNext geometry.nBeforeStep geometry.nEnd
            geometry.nFit geometry.nSeparate geometry.nScratchSeparate geometry.modulusValue
            geometry.modulusPos geometry.inverse geometry.operandValue geometry.operandReduced
            geometry.radixInverse geometry.finalize hi

end Modexp.MultiLimbMontgomerySOSSemantic
