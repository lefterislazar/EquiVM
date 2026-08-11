import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeGeometry

/-! # Nonzero-top CIOS finalization contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- A nonzero top word forces the exact subtraction required by pure Montgomery finalization. -/
theorem selectedCIOSFinalizeNonzero_value
    (columns : Nat) {subFuel : Nat} (mem : ByteArray)
    (aw nBefore tP bytes tEnd nP resultPtr resultBase : UInt256)
    (copy : CIOSCopySelection)
    (geometry : CIOSFinalizeGeometry columns mem aw nBefore tP bytes tEnd nP
      resultPtr resultBase)
    (htop : finalTopWord mem aw tEnd ≠ ⟨0⟩)
    (hcopy : selectCIOSCopy subFuel mem (finalTopAw aw tEnd) tP bytes ⟨1⟩
      resultPtr nP resultBase = some copy) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom copy.memory resultPtr.toNat columns) =
      Modexp.montgomeryFinalize
        (limbsWithTop (memoryWordsFrom mem tP.toNat columns)
          (finalTopWord mem aw tEnd))
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) := by
  let candidate := memoryWordsFrom mem tP.toNat columns
  let modulus := memoryWordsFrom mem nP.toNat columns
  let top := finalTopWord mem aw tEnd
  have htopCoverage := readWords1_coverage mem aw tEnd geometry.hCovered
    geometry.hAwFit geometry.hTopFit
  have hcopyOutput := selectedCIOSCopy_memoryWords_eq
    (fuel := subFuel) columns mem (finalTopAw aw tEnd) tP bytes ⟨1⟩ resultPtr nP
    resultBase copy geometry.hColumnsPos geometry.hBytes geometry.hSource
    geometry.hResult geometry.hModulus geometry.hDisjoint geometry.hResultFit
    geometry.hNFit geometry.hCopyAccessFit geometry.hCopyStop htopCoverage.1
    htopCoverage.2 hcopy
  have hsub : memoryWordsFrom copy.memory resultPtr.toNat columns =
      (Modexp.evmSubLimbs candidate modulus ⟨0⟩).1 := by
    simpa [candidate, modulus, UInt256.size] using hcopyOutput
  rw [hsub]
  exact finalizeNonzeroTop_value candidate modulus top
    (by simp [candidate, modulus]) (by simpa [top] using htop)
    (by simpa [candidate, modulus, top] using geometry.hReduced)

end Modexp.MultiLimbMontgomeryCIOSSemantic
