import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSSelectorLinks
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSMemoryLinks

/-! # Pure SOS finalization contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryCompareTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomeryCIOSCall
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- SOS comparison inherits the exact descending lexicographic decision from the shared
comparison transition. -/
theorem selectedSOSCompare_doSub_zero_iff_memoryWords
    (columns : Nat) {fuel : Nat} {mem : ByteArray} {tP : UInt256}
    {state : CompareState} {prevTOff : UInt256} {selected : SOSCompareSelection}
    (candidateBase modulusBase : Nat)
    (hcolumns : 0 < columns)
    (htOff : state.tOff.toNat = candidateBase + 32 * columns)
    (hnOff : state.nOff.toNat = modulusBase + 32 * columns)
    (htBase : candidateBase = tP.toNat)
    (htFit : candidateBase + 32 * columns + 31 < UInt256.size)
    (hnFit : modulusBase + 32 * columns + 31 < UInt256.size)
    (htMem : candidateBase + 32 * columns ≤ mem.size)
    (hnMem : modulusBase + 32 * columns ≤ mem.size)
    (hcovered : MemoryCovered mem state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectSOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    selected.doSub = ⟨0⟩ ↔
      limbsLtMSB (memoryWordsFrom mem candidateBase columns)
        (memoryWordsFrom mem modulusBase columns) := by
  obtain ⟨cios, hcios, relation⟩ := selectedSOSCompare_to_CIOS hselect
  have hdecision :=
    Modexp.MultiLimbMontgomeryCIOSSemantic.selectedCIOSCompare_doSub_zero_iff_memoryWords
      columns candidateBase modulusBase hcolumns htOff hnOff htBase htFit hnFit htMem
      hnMem hcovered hawFit hprev hcios
  rw [relation.doSub] at hdecision
  exact hdecision

/-- SOS comparison also inherits exact active-memory coverage after all descending loads. -/
theorem selectedSOSCompare_coverage
    (columns : Nat) {fuel : Nat} {mem : ByteArray} {tP : UInt256}
    {state : CompareState} {prevTOff : UInt256} {selected : SOSCompareSelection}
    (candidateBase modulusBase : Nat)
    (hcolumns : 0 < columns)
    (htOff : state.tOff.toNat = candidateBase + 32 * columns)
    (hnOff : state.nOff.toNat = modulusBase + 32 * columns)
    (htBase : candidateBase = tP.toNat)
    (htFit : candidateBase + 32 * columns + 31 < UInt256.size)
    (hnFit : modulusBase + 32 * columns + 31 < UInt256.size)
    (hcovered : MemoryCovered mem state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectSOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    MemoryCovered mem selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size := by
  obtain ⟨cios, hcios, relation⟩ := selectedSOSCompare_to_CIOS hselect
  have hcoverage :=
    Modexp.MultiLimbMontgomeryCIOSSemantic.selectedCIOSCompare_coverage
      columns candidateBase modulusBase hcolumns htOff hnOff htBase htFit hnFit
      hcovered hawFit hprev hcios
  rw [relation.activeWords] at hcoverage
  exact hcoverage

/-- SOS copy and optional subtraction store exactly the candidate or its pure subtraction. -/
theorem selectedSOSCopy_memoryWords_eq
    (columns : Nat) {fuel : Nat} (mem : ByteArray)
    (aw source bytes doSub resultPtr nP resultBase : UInt256)
    (selected : SOSCopySelection)
    (hcolumns : 0 < columns)
    (hbytes : bytes.toNat = 32 * columns)
    (hsource : source.toNat + 32 * columns ≤ mem.size)
    (hresult : resultPtr.toNat + 32 * columns ≤ mem.size)
    (hmodulus : nP.toNat + 32 * columns ≤ mem.size)
    (hdisjoint : nP.toNat + 32 * columns ≤ resultPtr.toNat)
    (hresultFit : resultPtr.toNat + 32 * columns + 31 < UInt256.size)
    (hmodulusFit : nP.toNat + 32 * columns + 31 < UInt256.size)
    (haccessFit : max resultPtr.toNat source.toNat + bytes.toNat + 31 < UInt256.size)
    (hstop : (⟨32⟩ + (bytes + resultBase)).toNat =
      resultPtr.toNat + 32 * columns)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectSOSCopy fuel mem aw source bytes doSub resultPtr nP resultBase =
      some selected) :
    memoryWordsFrom selected.memory resultPtr.toNat columns =
      if doSub = ⟨0⟩ then
        memoryWordsFrom mem source.toNat columns
      else
        (Modexp.evmSubLimbs (memoryWordsFrom mem source.toNat columns)
          (memoryWordsFrom mem nP.toNat columns) ⟨0⟩).1 := by
  obtain ⟨cios, hcios, hmemory, _⟩ := selectedSOSCopy_to_CIOS columns hcolumns
    hbytes hstop hselect
  have hvalue :=
    Modexp.MultiLimbMontgomeryCIOSSemantic.selectedCIOSCopy_memoryWords_eq
      columns mem aw source bytes doSub resultPtr nP resultBase cios hcolumns hbytes
      hsource hresult hmodulus hdisjoint hresultFit hmodulusFit haccessFit hstop
      hcovered hawFit hcios
  rw [hmemory] at hvalue
  exact hvalue

structure SOSFinalizeGeometry
    (columns : Nat) (mem : ByteArray)
    (aw nBefore sBase bytes nEnd nP resultPtr resultBase : UInt256) : Prop where
  base : CIOSFinalizeGeometry columns mem aw nBefore sBase bytes
    (sosFinalTopPtr sBase bytes) nP resultPtr resultBase
  nEndToNat : nEnd.toNat = nP.toNat + 32 * columns

/-- The finalizer's low-limbs-plus-top view is exactly the consecutive scratch word array. -/
theorem SOSFinalizeGeometry.candidate_eq_memoryWords
    {columns : Nat} {mem : ByteArray}
    {aw nBefore sBase bytes nEnd nP resultPtr resultBase : UInt256}
    (geometry : SOSFinalizeGeometry columns mem aw nBefore sBase bytes nEnd nP
      resultPtr resultBase) :
    limbsWithTop (memoryWordsFrom mem sBase.toNat columns)
        (sosFinalTopWord mem aw sBase bytes) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sBase.toNat (columns + 1)) := by
  let topPtr := sosFinalTopPtr sBase bytes
  have htop := readWord_toNat_of_covered mem aw topPtr geometry.base.hCovered
    geometry.base.hAwFit geometry.base.hTopMem
  have htop' : (sosFinalTopWord mem aw sBase bytes).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem topPtr.toNat := by
    simpa only [sosFinalTopWord, topPtr, sosFinalTopPtr] using htop
  have hsplit := memoryWordsFrom_add mem sBase.toNat columns 1
  rw [show sBase.toNat + 32 * columns = topPtr.toNat by
    simpa only [topPtr] using geometry.base.hTEnd.symm] at hsplit
  rw [show columns + 1 = columns + 1 by rfl, hsplit,
    Modexp.wordLimbsToNat_append, memoryWordsFrom_length]
  simp only [limbsWithTop, memoryWordsFrom, Modexp.wordLimbsToNat,
    memoryWordsFrom_length, htop']
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem topPtr.toNat)]
  simp

/-- The selected SOS top comparison and copy implement pure Montgomery finalization. -/
theorem selectedSOSFinalize_value
    (columns : Nat) {compareFuel subFuel : Nat} (mem : ByteArray)
    (aw nBefore sBase bytes nEnd nP resultPtr resultBase : UInt256)
    (compared : SOSFinalCompareSelection) (copy : SOSCopySelection)
    (geometry : SOSFinalizeGeometry columns mem aw nBefore sBase bytes nEnd nP
      resultPtr resultBase)
    (hcompare : selectSOSFinalCompare compareFuel mem aw sBase bytes nEnd =
      some compared)
    (hcopy : selectSOSCopy subFuel mem compared.activeWords sBase bytes compared.doSub
      resultPtr nP resultBase = some copy) :
    Modexp.wordLimbsToNat (memoryWordsFrom copy.memory resultPtr.toNat columns) =
      Modexp.montgomeryFinalize
        (limbsWithTop (memoryWordsFrom mem sBase.toNat columns)
          (sosFinalTopWord mem aw sBase bytes))
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) := by
  let topPtr := sosFinalTopPtr sBase bytes
  let topAw := sosFinalTopAw aw sBase bytes
  let candidate := memoryWordsFrom mem sBase.toNat columns
  let modulus := memoryWordsFrom mem nP.toNat columns
  have htopPtrNat : topPtr.toNat = sBase.toNat + 32 * columns := by
    simpa only [topPtr] using geometry.base.hTEnd
  have hcolumnsPos : 0 < columns := geometry.base.hColumnsPos
  have htopCoverage := readWords1_coverage mem aw topPtr geometry.base.hCovered
    geometry.base.hAwFit geometry.base.hTopFit
  have htopCoverage' : MemoryCovered mem topAw ∧
      topAw.toNat * 32 < UInt256.size := by
    simpa only [topAw, sosFinalTopAw, Modexp.MultiLimbDivisionTrace.readWords1,
      Modexp.MultiLimbArithmeticTrace.readWords1] using htopCoverage
  unfold selectSOSFinalCompare at hcompare
  dsimp only at hcompare
  by_cases htop : sosFinalTopWord mem aw sBase bytes ≠ ⟨0⟩
  · rw [if_pos htop] at hcompare
    injection hcompare with heq
    subst compared
    have hcopyOutput := selectedSOSCopy_memoryWords_eq columns mem topAw sBase bytes
      ⟨1⟩ resultPtr nP resultBase copy geometry.base.hColumnsPos
      geometry.base.hBytes geometry.base.hSource geometry.base.hResult
      geometry.base.hModulus geometry.base.hDisjoint geometry.base.hResultFit
      geometry.base.hNFit geometry.base.hCopyAccessFit geometry.base.hCopyStop
      htopCoverage'.1 htopCoverage'.2 hcopy
    have hsub : memoryWordsFrom copy.memory resultPtr.toNat columns =
        (Modexp.evmSubLimbs candidate modulus ⟨0⟩).1 := by
      simpa [candidate, modulus, UInt256.size] using hcopyOutput
    rw [hsub]
    exact finalizeNonzeroTop_value candidate modulus (sosFinalTopWord mem aw sBase bytes)
      (by simp [candidate, modulus]) htop
      (by simpa [candidate, modulus] using geometry.base.hReduced)
  · rw [if_neg htop] at hcompare
    have htopZero : sosFinalTopWord mem aw sBase bytes = ⟨0⟩ := by
      by_contra hne
      exact htop hne
    have htopPtrGt : topPtr.gt sBase ≠ ⟨0⟩ := by
      apply ne_of_eq_of_ne (ugt_one (by
        change sBase.toNat < topPtr.toNat
        rw [htopPtrNat]
        omega))
      decide
    rw [if_neg htopPtrGt] at hcompare
    cases hsos : selectSOSCompare compareFuel mem sBase topAw topPtr nEnd
        (comparePrev topPtr) with
    | none =>
        rw [hsos] at hcompare
        contradiction
    | some comparison =>
        rw [hsos] at hcompare
        injection hcompare with heq
        subst compared
        let compareState : CompareState := {
          tOff := topPtr
          nOff := nEnd
          activeWords := topAw }
        have htOff : compareState.tOff.toNat = sBase.toNat + 32 * columns := by
          exact htopPtrNat
        have hnOff : compareState.nOff.toNat = nP.toNat + 32 * columns := by
          exact geometry.nEndToNat
        have hsos' : selectSOSCompare compareFuel mem sBase compareState.activeWords
            compareState.tOff compareState.nOff (comparePrev compareState.tOff) =
              some comparison := by
          simpa only [compareState] using hsos
        have hdecision := selectedSOSCompare_doSub_zero_iff_memoryWords
          (fuel := compareFuel) (mem := mem) (tP := sBase) (state := compareState)
          (prevTOff := comparePrev compareState.tOff) (selected := comparison)
          columns sBase.toNat nP.toNat geometry.base.hColumnsPos htOff hnOff rfl
          geometry.base.hTFit geometry.base.hNFit geometry.base.hSource
          geometry.base.hModulus htopCoverage'.1 htopCoverage'.2 rfl hsos'
        have hcomparisonCoverage := selectedSOSCompare_coverage
          (fuel := compareFuel) (mem := mem) (tP := sBase) (state := compareState)
          (prevTOff := comparePrev compareState.tOff) (selected := comparison)
          columns sBase.toNat nP.toNat geometry.base.hColumnsPos htOff hnOff rfl
          geometry.base.hTFit geometry.base.hNFit htopCoverage'.1 htopCoverage'.2
          rfl hsos'
        have hcopyOutput := selectedSOSCopy_memoryWords_eq columns mem
          comparison.activeWords sBase bytes comparison.doSub resultPtr nP resultBase
          copy geometry.base.hColumnsPos geometry.base.hBytes geometry.base.hSource
          geometry.base.hResult geometry.base.hModulus geometry.base.hDisjoint
          geometry.base.hResultFit geometry.base.hNFit geometry.base.hCopyAccessFit
          geometry.base.hCopyStop hcomparisonCoverage.1 hcomparisonCoverage.2 hcopy
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
        rw [hfinalized, finalizeLimbs_value candidate modulus
          (by simp [candidate, modulus])]
        simp [htopZero, limbsWithTop, candidate, modulus]

end Modexp.MultiLimbMontgomerySOSSemantic
