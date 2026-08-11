import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSReductionLinks
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSMemoryLinks

/-! # SOS selected reduction-column contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A selected run of non-peeled reduction columns is exactly the corresponding unbounded
multiply-accumulate over the original modulus and scratch windows. -/
theorem selectedSOSReductionColumns_value
    (columns : Nat) {fuel : Nat} {factor stop : UInt256}
    {state : SOSReductionState} {selected : SOSReductionColumnsSelection}
    (hcolumns : 0 < columns)
    (hstop : stop.toNat = state.modulusPtr.toNat + 32 * columns)
    (hoperandFit : state.modulusPtr.toNat + 32 * columns < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * columns < UInt256.size)
    (hseparate : state.modulusPtr.toNat + 32 * columns ≤ state.resultPtr.toNat)
    (hloadsModulus : ∀ j, j < columns →
      let current := sosReductionIterate factor j state
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat)
    (hloadsPrior : ∀ j, j < columns →
      let current := sosReductionIterate factor j state
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < columns →
      let current := sosReductionIterate factor j state
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hselect : selectSOSReductionColumns fuel factor stop state = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory state.resultPtr.toNat columns) +
        UInt256.size ^ columns * selected.final.carry.toNat =
      Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.resultPtr.toNat columns) +
        factor.toNat * Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.modulusPtr.toNat columns) +
        state.carry.toNat := by
  have hwords := selectedSOSReductionColumns_words_eq_geometry columns hcolumns hstop
    hoperandFit hselect
  have hfinal := selectedSOSReductionColumns_final_eq_iterate hselect
  rw [hwords] at hfinal
  have hmodulus := sosReductionModulusWords_eq_initialMemory factor columns state
    hoperandFit hresultFit hseparate hloadsModulus hwrites
  have hprior := sosReductionPriorWords_eq_initialMemory factor columns state
    hresultFit hloadsPrior hwrites
  have houtput := sosReductionOutputWords_eq_finalMemory factor columns state
    hresultFit hwrites
  have hrecompose := sosReductionCollectors_recompose factor columns state
  rw [hmodulus, hprior, houtput] at hrecompose
  rw [hfinal]
  exact hrecompose

/-- The peeled low column plus the remaining generated columns is one pure Montgomery step over
the concrete scratch and modulus memory windows. -/
theorem sosReductionPassMemory_eq_montgomeryStep
    (mem : ByteArray) (aw sBase nP n0inv nBefore : UInt256) (columns : Nat)
    (value modulus nextValue : Nat)
    (hinv : (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat % UInt256.size =
      UInt256.size - 1)
    (hvalue : value = (sosPeeledValue mem aw sBase).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (memoryWordsFrom mem (sBase + ⟨32⟩).toNat columns))
    (hmodulus : modulus = (sosPeeledN0 mem aw sBase nP).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (memoryWordsFrom mem (nP + ⟨32⟩).toNat columns))
    (hnext : nextValue =
      Modexp.wordLimbsToNat
        (memoryWordsFrom
          (sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) columns
            (sosReductionInitialState mem aw sBase nP n0inv nBefore)).memory
          (sBase + ⟨32⟩).toNat columns) +
      UInt256.size ^ columns *
        (sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) columns
          (sosReductionInitialState mem aw sBase nP n0inv nBefore)).carry.toNat)
    (hnPtr : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hoperandFit : (nBefore + ⟨64⟩).toNat + 32 * columns < UInt256.size)
    (hresultFit : (sBase + ⟨32⟩).toNat + 32 * columns < UInt256.size)
    (hseparate : (nBefore + ⟨64⟩).toNat + 32 * columns ≤ (sBase + ⟨32⟩).toNat)
    (hloadsModulus : ∀ j, j < columns →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat)
    (hloadsPrior : ∀ j, j < columns →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < columns →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    nextValue = Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0 value 0 := by
  let factor := sosPeeledFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  have hmodulusCollector := sosReductionModulusWords_eq_initialMemory
    factor columns initial hoperandFit hresultFit hseparate hloadsModulus hwrites
  have hpriorCollector := sosReductionPriorWords_eq_initialMemory
    factor columns initial hresultFit hloadsPrior hwrites
  have houtputCollector := sosReductionOutputWords_eq_finalMemory
    factor columns initial hresultFit hwrites
  have hmodulusCollector' :
      sosReductionModulusWords factor columns initial =
        memoryWordsFrom mem (nP + ⟨32⟩).toNat columns := by
    simpa only [initial, sosReductionInitialState, hnPtr] using hmodulusCollector
  have hpriorCollector' :
      sosReductionPriorWords factor columns initial =
        memoryWordsFrom mem (sBase + ⟨32⟩).toNat columns := by
    simpa only [initial, sosReductionInitialState] using hpriorCollector
  have houtputCollector' :
      sosReductionOutputWords factor columns initial =
        memoryWordsFrom (sosReductionIterate factor columns initial).memory
          (sBase + ⟨32⟩).toNat columns := by
    simpa only [initial, sosReductionInitialState] using houtputCollector
  apply sosReductionPassColumns_eq_montgomeryStep mem aw sBase nP n0inv nBefore columns
    value modulus nextValue hinv
  · simpa only [factor, initial, hpriorCollector'] using hvalue
  · simpa only [factor, initial, hmodulusCollector'] using hmodulus
  · simpa only [factor, initial, houtputCollector'] using hnext

end Modexp.MultiLimbMontgomerySOSSemantic
