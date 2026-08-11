import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeGeometry

/-! # Zero-top CIOS finalization contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCompareTrace
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- The zero-top comparison and conditional subtraction implement pure finalization. -/
theorem selectedCIOSFinalizeZero_value
    (columns : Nat) {compareFuel subFuel : Nat} (mem : ByteArray)
    (aw nBefore tP bytes tEnd nP resultPtr resultBase : UInt256)
    (comparison : CIOSCompareSelection) (copy : CIOSCopySelection)
    (geometry : CIOSFinalizeGeometry columns mem aw nBefore tP bytes tEnd nP
      resultPtr resultBase)
    (htop : finalTopWord mem aw tEnd = ⟨0⟩)
    (hcomparison : selectCIOSCompare compareFuel mem tP (finalTopAw aw tEnd) tEnd
      (⟨32⟩ + (bytes + nBefore)) (comparePrev tEnd) = some comparison)
    (hcopy : selectCIOSCopy subFuel mem comparison.activeWords tP bytes
      comparison.doSub resultPtr nP resultBase = some copy) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom copy.memory resultPtr.toNat columns) =
      Modexp.montgomeryFinalize
        (limbsWithTop (memoryWordsFrom mem tP.toNat columns)
          (finalTopWord mem aw tEnd))
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) := by
  let candidate := memoryWordsFrom mem tP.toNat columns
  let modulus := memoryWordsFrom mem nP.toNat columns
  let compareState : CompareState := {
    tOff := tEnd
    nOff := ⟨32⟩ + (bytes + nBefore)
    activeWords := finalTopAw aw tEnd }
  have htopCoverage := readWords1_coverage mem aw tEnd geometry.hCovered
    geometry.hAwFit geometry.hTopFit
  have hcomparison' : selectCIOSCompare compareFuel mem tP
      compareState.activeWords compareState.tOff compareState.nOff
      (comparePrev compareState.tOff) = some comparison := by
    simpa [compareState] using hcomparison
  have hdecision := selectedCIOSCompare_doSub_zero_iff_memoryWords
    (fuel := compareFuel) (mem := mem) (tP := tP) (state := compareState)
    (prevTOff := comparePrev compareState.tOff) (selected := comparison)
    columns tP.toNat nP.toNat geometry.hColumnsPos
    (by simpa [compareState] using geometry.hTEnd)
    (by simpa [compareState] using geometry.hNOff) rfl geometry.hTFit geometry.hNFit
    geometry.hSource geometry.hModulus htopCoverage.1 htopCoverage.2 rfl hcomparison'
  have hcomparisonCoverage := selectedCIOSCompare_coverage
    (fuel := compareFuel) (mem := mem) (tP := tP) (state := compareState)
    (prevTOff := comparePrev compareState.tOff) (selected := comparison)
    columns tP.toNat nP.toNat geometry.hColumnsPos
    (by simpa [compareState] using geometry.hTEnd)
    (by simpa [compareState] using geometry.hNOff) rfl geometry.hTFit geometry.hNFit
    htopCoverage.1 htopCoverage.2 rfl hcomparison'
  have hcopyOutput := selectedCIOSCopy_memoryWords_eq columns mem
    comparison.activeWords tP bytes comparison.doSub resultPtr nP resultBase copy
    geometry.hColumnsPos geometry.hBytes geometry.hSource geometry.hResult
    geometry.hModulus geometry.hDisjoint geometry.hResultFit geometry.hNFit
    geometry.hCopyAccessFit geometry.hCopyStop hcomparisonCoverage.1
    hcomparisonCoverage.2 hcopy
  have hfinalized : memoryWordsFrom copy.memory resultPtr.toNat columns =
      finalizeLimbs candidate modulus := by
    classical
    by_cases hlt : limbsLtMSB candidate modulus
    · have hdo : comparison.doSub = ⟨0⟩ :=
        hdecision.mpr (by simpa [candidate, modulus] using hlt)
      rw [hcopyOutput, if_pos hdo]
      simp [finalizeLimbs, hlt, candidate]
    · have hdo : comparison.doSub ≠ ⟨0⟩ := by
        intro hzero
        exact hlt (by simpa [candidate, modulus] using hdecision.mp hzero)
      rw [hcopyOutput, if_neg hdo]
      simp [finalizeLimbs, hlt, candidate, modulus]
  rw [hfinalized, finalizeLimbs_value candidate modulus (by simp [candidate, modulus])]
  simp [htop, limbsWithTop, candidate, modulus]

end Modexp.MultiLimbMontgomeryCIOSSemantic
