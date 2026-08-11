import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSOuterLinks
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeContract

/-! # Complete multi-limb CIOS arithmetic contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- With the cleared extra scratch word, the concrete scratch interpretation is exactly the
low words together with the word loaded by the generated finalizer. -/
theorem ciosScratchValue_eq_limbsWithTop
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore shiftedOut
      state)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0) :
    ciosScratchValue columns tP tEnd tk1Off state =
      limbsWithTop (memoryWordsFrom state.memory tP.toNat columns)
        (finalTopWord state.memory state.activeWords tEnd) := by
  have htEndMem : tEnd.toNat + 32 ≤ state.memory.size := by
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have htop := readWord_toNat_of_covered state.memory state.activeWords tEnd
    layout.covered layout.activeFit htEndMem
  have htop' :
      (Modexp.MultiLimbDivisionTrace.readWord state.memory state.activeWords tEnd).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tEnd.toNat := by
    simpa only [Modexp.MultiLimbDivisionTrace.readWord,
      Modexp.MultiLimbArithmeticTrace.readWord] using htop
  unfold ciosScratchValue limbsWithTop finalTopWord
  rw [memoryWordsFrom_length, htop', hextra]
  simp

/-- The low radix digit of a nonempty concrete word array is its first memory word. -/
theorem wordLimbsToNat_memoryWordsFrom_mod_size
    (mem : ByteArray) (ptr words : Nat) (hwords : 0 < words) :
    Modexp.wordLimbsToNat (memoryWordsFrom mem ptr words) % UInt256.size =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : words ≠ 0)
  simp only [memoryWordsFrom, Modexp.wordLimbsToNat]
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem ptr)]
  rw [Nat.add_mod, Nat.mul_mod]
  simp only [Nat.mod_self, zero_mul, Nat.zero_mod, add_zero]
  rw [Nat.mod_mod]
  exact Nat.mod_eq_of_lt (memoryWordNat_lt_size mem ptr)

/-- A successful generated multi-limb CIOS scan and finalizer compute the standard Montgomery
product over the original source, multiplier, and modulus word arrays. -/
theorem selectedCIOSMultiLimb_value
    (words : Nat) {outerFuel compareFuel subFuel : Nat}
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut aEnd bytes resultPtr
      resultBase : UInt256)
    (initial : CIOSOuterState) (outer : CIOSOuterSelection)
    (finalize : CIOSFinalizeSelection) (rInv : Nat)
    (layout : CIOSOuterLayout words bP tP tEnd tk1Off nP tOff nBefore shiftedOut
      initial)
    (haFit : ∀ i, i ≤ words →
      (ciosOuterIterate words bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
        i initial).aOff.toNat + 32 + 31 < UInt256.size)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat initial.memory
      tk1Off.toNat = 0)
    (hzero : ciosScratchValue words tP tEnd tk1Off initial = 0)
    (hsourceEnd : initial.aOff.toNat + 32 * words = aEnd.toNat)
    (hsourceFit : initial.aOff.toNat + 32 * words < UInt256.size)
    (haEnd : initial.aOff.toNat + 32 * words ≤ tP.toNat)
    (hbEnd : bP.toNat + 32 * words ≤ tP.toNat)
    (hHigherPtr : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nP.toNat + 32 * words ≤ tP.toNat)
    (hinv0 : Modexp.MultiLimbMemoryModel.memoryWordNat initial.memory nP.toNat *
      n0inv.toNat % UInt256.size = UInt256.size - 1)
    (houter : selectCIOSOuter outerFuel words bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut aEnd initial = some outer)
    (geometry : CIOSFinalizeGeometry words outer.final.memory
      outer.final.activeWords nBefore tP bytes tEnd nP resultPtr resultBase)
    (hfinalize : selectCIOSFinalize compareFuel subFuel outer.final.memory
      outer.final.activeWords nBefore tP bytes tEnd nP resultPtr resultBase =
        some finalize)
    (hmodulusPos : 0 <
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory nP.toNat words))
    (hinvR : UInt256.size ^ words * rInv %
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory nP.toNat words) =
        1 % Modexp.wordLimbsToNat (memoryWordsFrom initial.memory nP.toNat words))
    (hb : Modexp.wordLimbsToNat (memoryWordsFrom initial.memory bP.toNat words) <
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory nP.toNat words)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom finalize.memory resultPtr.toNat words) =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory initial.aOff.toNat words) *
        Modexp.wordLimbsToNat (memoryWordsFrom initial.memory bP.toNat words) *
        rInv) %
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory nP.toNat words) := by
  have hcount := selectedCIOSOuter_iterations_eq_geometry outerFuel words words bP
    tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut aEnd initial outer
    layout.columnsGtOne (Nat.zero_lt_of_lt layout.columnsGtOne) hsourceEnd hsourceFit
    houter
  have houterEq := selectedCIOSOuter_final_eq_iterate outerFuel words bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut aEnd initial outer
    layout.columnsGtOne houter
  rw [hcount] at houterEq
  let iterated := ciosOuterIterate words bP tP tEnd tk1Off nP n0inv tOff nBefore
    shiftedOut words initial
  have hscan := ciosOuterIterate_eq_montgomeryCIOSScan_of_memoryOperands words words
    bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut initial layout haFit hextra
    haEnd hbEnd hHigherPtr hnEnd hinv0
  rw [hzero] at hscan
  have hfinalLayout := (ciosOuterIterate_layout words words bP tP tEnd tk1Off nP
    n0inv tOff nBefore shiftedOut initial layout haFit).1
  have hfinalExtra := ciosOuterIterate_extraWord_zero words words bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut initial layout haFit hextra
  have hscratch : ciosScratchValue words tP tEnd tk1Off iterated =
      limbsWithTop (memoryWordsFrom iterated.memory tP.toNat words)
        (finalTopWord iterated.memory iterated.activeWords tEnd) := by
    apply ciosScratchValue_eq_limbsWithTop words bP tP tEnd tk1Off nP tOff
      nBefore shiftedOut iterated
    · exact hfinalLayout
    · exact hfinalExtra
  have hmodulusFrame := ciosOuterIterate_memoryWords_below words words bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut initial nP.toNat words layout haFit hnEnd
  have hfinalValue := selectedCIOSFinalize_value words outer.final.memory
    outer.final.activeWords nBefore tP bytes tEnd nP resultPtr resultBase finalize
    geometry hfinalize
  rw [houterEq] at hfinalValue
  rw [← hscratch, hmodulusFrame] at hfinalValue
  rw [hscan] at hfinalValue
  rw [hfinalValue]
  apply Modexp.montgomeryCIOS_contract_of_reduced
  · norm_num [UInt256.size]
  · exact hmodulusPos
  · have hmod := wordLimbsToNat_memoryWordsFrom_mod_size initial.memory nP.toNat
      words (Nat.zero_lt_of_lt layout.columnsGtOne)
    rw [Nat.mul_mod, hmod]
    rw [Nat.mul_mod] at hinv0
    rw [Nat.mod_eq_of_lt (memoryWordNat_lt_size initial.memory nP.toNat)] at hinv0
    exact hinv0
  · symm
    exact Modexp.wordLimbsToNat_eq_limbsToNatAt _
  · simpa only [List.length_map, memoryWordsFrom_length] using hinvR
  · intro ai hai
    simp only [List.mem_map] at hai
    obtain ⟨word, _, rfl⟩ := hai
    exact word.val.isLt
  · exact hb

end Modexp.MultiLimbMontgomeryCIOSSemantic
