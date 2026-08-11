import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSSemantic

/-! # Concrete framing links for a CIOS outer iteration -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure CIOSMultiplyLinkFacts
    (columns : Nat) (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop where
  writes : ∀ j, j < columns →
    let current := multiplyPassIterate
      (ciosOuterAi state.memory state.activeWords state.aOff) j
      (ciosMultiplyInitial bP tP state)
    current.resultPtr.toNat + 32 ≤ current.memory.size
  priorLoads : ∀ j, j < columns →
    let current := multiplyPassIterate
      (ciosOuterAi state.memory state.activeWords state.aOff) j
      (ciosMultiplyInitial bP tP state)
    (schoolbookOperands current.memory current.activeWords current.operandPtr
      current.resultPtr current.carry).2.1.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat
  tailPtr :
    (multiplyPassAdvance
      (ciosOuterAi state.memory state.activeWords state.aOff)
      (ciosMultiplyInitial bP tP state)).resultPtr.toNat = tOff.toNat
  tailWrites : ∀ j, j < columns - 1 →
    let current := multiplyPassIterate
      (ciosOuterAi state.memory state.activeWords state.aOff) j
      (multiplyPassAdvance
        (ciosOuterAi state.memory state.activeWords state.aOff)
        (ciosMultiplyInitial bP tP state))
    current.resultPtr.toNat + 32 ≤ current.memory.size
  finalCovered : MemoryCovered
    (ciosMultiplyFinal columns bP tP state).memory
    (ciosMultiplyFinal columns bP tP state).activeWords
  finalFit : (ciosMultiplyFinal columns bP tP state).activeWords.toNat * 32 < UInt256.size
  finalSize : (ciosMultiplyFinal columns bP tP state).memory.size = state.memory.size
  boundary : CIOSBoundaryCoverageFacts
    (ciosMultiplyFinal columns bP tP state).memory
    (ciosMultiplyFinal columns bP tP state).activeWords tEnd
    (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP
  tEndInBounds : tEnd.toNat ≤ (ciosMultiplyFinal columns bP tP state).memory.size
  tk1InBounds : tk1Off.toNat ≤
    (ciosBoundaryMem1
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry).size
  boundaryReadSize : tP.toNat <
    (ciosBoundaryMem2
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry tk1Off).size
  boundaryReadGuard : ¬ tP ≥
    ciosBoundaryAw4 (ciosMultiplyFinal columns bP tP state).activeWords
      tEnd tk1Off * ⟨32⟩

theorem ciosMultiplyLinkFacts_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    CIOSMultiplyLinkFacts columns bP tP tEnd tk1Off nP tOff nBefore shiftedOut
      state := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  let final := ciosMultiplyFinal columns bP tP state
  have hmultiplyRange : tP.toNat + 32 * columns ≤ state.memory.size := by
    have hfrontier := layout.scratchFrontier
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hinBounds := multiplyPassIterate_inBounds ai columns initial
    (by
      simpa only [initial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * columns < UInt256.size by
          have hfit := layout.scratchFit
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosMultiplyInitial] using hmultiplyRange)
  have houter := readWords1_coverage state.memory state.activeWords state.aOff
    layout.covered layout.activeFit layout.aFit
  have hinitialCoverage :
      MemoryCovered initial.memory initial.activeWords ∧
        initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, ciosMultiplyInitial, ciosOuterAw] using houter
  have hsteps : ∀ j, j < columns →
      let current := multiplyPassIterate ai j initial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := multiplyPassIterate_operandPtr_toNat ai j initial (by
      simpa only [initial, ciosMultiplyInitial] using
        (show bP.toNat + 32 * j < UInt256.size by
          have hfit := layout.bFit
          omega))
    have hresult := multiplyPassIterate_resultPtr_toNat ai j initial (by
      simpa only [initial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * j < UInt256.size by
          have hfit := layout.scratchFit
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega))
    refine ⟨?_, ?_, hinBounds.1 j hj⟩
    · rw [hop]
      dsimp [initial, ciosMultiplyInitial]
      have hfit := layout.bFit
      omega
    · rw [hresult]
      dsimp [initial, ciosMultiplyInitial]
      have hfit := layout.scratchFit
      have hstop := layout.multiplyStop
      have htk1 := layout.tk1OffEq
      omega
  have hcoverage := multiplyPassIterate_coverage ai columns initial
    hinitialCoverage.1 hinitialCoverage.2 hsteps
  have hfinalEq : final = multiplyPassIterate ai columns initial := by
    simpa only [ai, initial, final] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have hc := layout.columnsGtOne
        omega)
  have hfinalCoverage :
      MemoryCovered final.memory final.activeWords ∧
        final.activeWords.toNat * 32 < UInt256.size := by
    rw [hfinalEq]
    exact hcoverage
  have hfinalSize : final.memory.size = state.memory.size := by
    rw [hfinalEq, hinBounds.2]
    rfl
  have htEndFit : tEnd.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have htk1 := layout.tk1OffEq
    omega
  have htPFit : tP.toNat + 32 + 31 < UInt256.size := by
    have hc := layout.columnsGtOne
    have hstop := layout.multiplyStop
    omega
  have htEndWrite : tEnd.toNat + 32 ≤ final.memory.size := by
    rw [hfinalSize]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hboundary := ciosBoundary_coverage final.memory final.activeWords tEnd final.carry
    tk1Off tP nP hfinalCoverage.1 hfinalCoverage.2 htEndFit layout.scratchFit htPFit
    layout.nPFit htEndWrite (by rw [hfinalSize]; exact layout.scratchFrontier)
  have htailPtr : (multiplyPassAdvance ai initial).resultPtr.toNat = tOff.toNat := by
    dsimp [initial, ciosMultiplyInitial, multiplyPassAdvance]
    rw [uadd_word_lit32_toNat tP (by
      have hfit := layout.scratchFit
      have hstop := layout.multiplyStop
      have htk1 := layout.tk1OffEq
      omega)]
    have hm := layout.multiplyStop
    have hr := layout.reductionStop
    have hc := layout.columnsGtOne
    omega
  have hpriorLoads : ∀ j, j < columns →
      let current := multiplyPassIterate ai j initial
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
    intro j hj
    let current := multiplyPassIterate ai j initial
    have hcurrent := multiplyPassIterate_coverage ai j initial hinitialCoverage.1
      hinitialCoverage.2 (fun i hi => hsteps i (by omega))
    have hstep := hsteps j hj
    have hoperand := readWords1_coverage current.memory current.activeWords
      current.operandPtr (by simpa only [current] using hcurrent.1)
      (by simpa only [current] using hcurrent.2)
      (by simpa only [current] using hstep.1)
    have hwrite : current.resultPtr.toNat + 32 ≤ current.memory.size := by
      simpa only [current] using hstep.2.2
    have hload := readWord_toNat_of_valid current.memory
      (readWords1 current.activeWords current.operandPtr) current.resultPtr
      (by omega)
      (wordBelowActive_of_covered current.memory
        (readWords1 current.activeWords current.operandPtr) current.resultPtr
        hoperand.1 hoperand.2 hwrite)
    simpa only [current, schoolbookOperands] using hload
  refine {
    writes := by simpa only [ai, initial] using hinBounds.1
    priorLoads := by simpa only [ai, initial] using hpriorLoads
    tailPtr := by simpa only [ai, initial] using htailPtr
    tailWrites := ?_
    finalCovered := by simpa only [final] using hfinalCoverage.1
    finalFit := by simpa only [final] using hfinalCoverage.2
    finalSize := by simpa only [final] using hfinalSize
    boundary := by simpa only [final] using hboundary
    tEndInBounds := ?_
    tk1InBounds := ?_
    boundaryReadSize := ?_
    boundaryReadGuard := ?_ }
  · intro j hj
    simpa only [ai, initial, multiplyPassIterate_advance] using
      hinBounds.1 (j + 1) (by omega)
  · simpa only [final] using
      (show tEnd.toNat ≤ final.memory.size by
        rw [hfinalSize]
        have hfrontier := layout.scratchFrontier
        have htk1 := layout.tk1OffEq
        omega)
  · simpa only [final] using
      (show tk1Off.toNat ≤
          (ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry).size by
        rw [hboundary.mem1Size, hfinalSize]
        have hfrontier := layout.scratchFrontier
        omega)
  · simpa only [final] using
      (show tP.toNat <
          (ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off).size by
        rw [hboundary.mem2Size, hfinalSize]
        have hfrontier := layout.scratchFrontier
        have hc := layout.columnsGtOne
        have hm := layout.multiplyStop
        have hk := layout.tk1OffEq
        omega)
  · simpa only [final] using
      (show ¬ tP ≥ ciosBoundaryAw4 final.activeWords tEnd tk1Off * ⟨32⟩ by
        apply wordBelowActive_of_covered
          (ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off)
          (ciosBoundaryAw4 final.activeWords tEnd tk1Off) tP
          hboundary.aw4Covered hboundary.aw4Fit
        rw [hboundary.mem2Size, hfinalSize]
        have hfrontier := layout.scratchFrontier
        have hc := layout.columnsGtOne
        have hm := layout.multiplyStop
        have hk := layout.tk1OffEq
        omega)

set_option Elab.async false in
theorem ciosBoundaryLow_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosBoundaryT0
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry tk1Off tP).toNat =
      (schoolbookStep state.memory (ciosOuterAw state.activeWords state.aOff)
        bP tP (ciosOuterAi state.memory state.activeWords state.aOff) ⟨0⟩).1.toNat := by
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  exact ciosBoundaryLow_eq_firstMultiplyOutput columns bP tP tEnd tk1Off state
    (by have h := layout.columnsGtOne; omega)
    (by
      have hc := layout.columnsGtOne
      have h := layout.multiplyStop
      omega)
    (by have h := layout.tk1OffEq; omega)
    (by
      simpa only [ciosMultiplyInitial] using
        (show tP.toNat + 32 * columns < UInt256.size by
          have hfit := layout.scratchFit
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega))
    facts.writes facts.tEndInBounds facts.tk1InBounds facts.boundaryReadSize
    facts.boundaryReadGuard

set_option Elab.async false in
/-- The multiply pass and its first boundary write are both below `tk1Off`, so the boundary's
extra-word load observes the word present at the start of the outer iteration. -/
theorem ciosBoundaryTk1_eq_initialWord
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosBoundaryTk1
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry tk1Off).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  let final := ciosMultiplyFinal columns bP tP state
  let mem1 := ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  have hfinalEq : final = multiplyPassIterate ai columns initial := by
    simpa only [ai, initial, final] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have h := layout.columnsGtOne
        omega)
  have hwrites : ∀ j, j < columns →
      let current := multiplyPassIterate ai j initial
      current.resultPtr.toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ tk1Off.toNat := by
    intro j hj
    have hresult := multiplyPassIterate_resultPtr_toNat ai j initial (by
      simpa only [initial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * j < UInt256.size by
          have hfit := layout.scratchFit
          have hstop := layout.multiplyStop
          have hk := layout.tk1OffEq
          omega))
    refine ⟨by simpa only [ai, initial] using facts.writes j hj, ?_⟩
    rw [hresult]
    dsimp [initial, ciosMultiplyInitial]
    have hstop := layout.multiplyStop
    have hk := layout.tk1OffEq
    omega
  have hfinalFrame := multiplyPassIterate_read_above ai columns initial tk1Off.toNat
    hwrites
  rw [← hfinalEq] at hfinalFrame
  have htEndWrite : tEnd.toNat + 32 ≤ final.memory.size := by
    rw [facts.finalSize]
    have h := layout.scratchFrontier
    have hk := layout.tk1OffEq
    omega
  have hboundaryFrame : mem1.readWithPadding tk1Off.toNat 32 =
      final.memory.readWithPadding tk1Off.toNat 32 := by
    dsimp [mem1, ciosBoundaryMem1]
    exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size]) htEndWrite
      (by have hk := layout.tk1OffEq; omega)
  have hword : tk1Off.toNat + 32 ≤ mem1.size := by
    dsimp [mem1]
    rw [facts.boundary.mem1Size, facts.finalSize]
    exact layout.scratchFrontier
  have hload := readWord_toNat_of_valid mem1
    (ciosBoundaryAw2 final.activeWords tEnd) tk1Off (by omega)
    (wordBelowActive_of_covered mem1 (ciosBoundaryAw2 final.activeWords tEnd) tk1Off
      (by simpa only [final, mem1] using facts.boundary.aw2Covered)
      (by simpa only [final] using facts.boundary.aw2Fit) hword)
  change (readWord mem1 (ciosBoundaryAw2 final.activeWords tEnd) tk1Off).toNat = _
  rw [hload]
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [hboundaryFrame, hfinalFrame]
  rfl

private theorem ult_toNat_le_one (a b : UInt256) : (a.lt b).toNat ≤ 1 := by
  by_cases h : a.toNat < b.toNat
  · rw [ult_one h]
    decide
  · rw [ult_zero (by omega)]
    decide

/-- Sequential multiply-pass destination loads collect the initial destination range: each write
is below every destination loaded later in the pass. -/
theorem multiplyPassPriorWords_eq_memoryWordsFrom
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hloads : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.resultPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    multiplyPassPriorWords a n state =
      memoryWordsFrom state.memory state.resultPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hptr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextFit : next.resultPtr.toNat + 32 * n < UInt256.size := by
        rw [hptr]
        omega
      have hnextLoads : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).2.1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
              current.resultPtr.toNat := by
        intro j hj
        simpa only [next, multiplyPassIterate_advance] using hloads (j + 1) (by omega)
      have hnextWrites : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.resultPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, multiplyPassIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next hnextFit hnextLoads hnextWrites
      have hheadNat :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).2.1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              state.resultPtr.toNat := by
        simpa only [multiplyPassIterate] using hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).2.1 =
            UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.resultPtr.toNat) := by
        apply u256_inj
        rw [hheadNat]
        rw [UInt256.toNat_ofNat_of_lt
          (memoryWordNat_lt_size state.memory state.resultPtr.toNat)]
      have hframe := memoryWordsFrom_write_below
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory state.resultPtr.toNat
        (state.resultPtr.toNat + 32) n (by rw [toByteArray_size])
        (by simpa only [multiplyPassIterate] using hwrites 0 (by omega)) (by omega)
      simp only [multiplyPassPriorWords, memoryWordsFrom]
      rw [hhead]
      congr 1
      rw [← hframe]
      have hadd : (state.resultPtr + ⟨32⟩).toNat = state.resultPtr.toNat + 32 := by
        simpa only [next, multiplyPassAdvance] using hptr
      simpa only [next, multiplyPassAdvance, multiplyPassMemory, hadd] using htail

theorem ciosMultiplyPriorWords_eq_memoryWordsFrom
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    multiplyPassPriorWords
        (ciosOuterAi state.memory state.activeWords state.aOff) columns
        (ciosMultiplyInitial bP tP state) =
      memoryWordsFrom state.memory tP.toNat columns := by
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  apply multiplyPassPriorWords_eq_memoryWordsFrom
  · simpa only [ciosMultiplyInitial] using
      (show tP.toNat + 32 * columns < UInt256.size by
        have hfit := layout.scratchFit
        have hstop := layout.multiplyStop
        have hk := layout.tk1OffEq
        omega)
  · exact facts.priorLoads
  · exact facts.writes

/-- The multiply pass stops immediately below `tEnd`, so its upper-word load observes the initial
scratch word at that address. -/
theorem ciosBoundaryTk_eq_initialWord
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosBoundaryTk
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tEnd.toNat := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  let final := ciosMultiplyFinal columns bP tP state
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  have hfinalEq : final = multiplyPassIterate ai columns initial := by
    simpa only [ai, initial, final] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have h := layout.columnsGtOne
        omega)
  have hwrites : ∀ j, j < columns →
      let current := multiplyPassIterate ai j initial
      current.resultPtr.toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ tEnd.toNat := by
    intro j hj
    have hresult := multiplyPassIterate_resultPtr_toNat ai j initial (by
      simpa only [initial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * j < UInt256.size by
          have hfit := layout.scratchFit
          have hstop := layout.multiplyStop
          have hk := layout.tk1OffEq
          omega))
    refine ⟨by simpa only [ai, initial] using facts.writes j hj, ?_⟩
    rw [hresult]
    dsimp [initial, ciosMultiplyInitial]
    have hstop := layout.multiplyStop
    omega
  have hframe := multiplyPassIterate_read_above ai columns initial tEnd.toNat hwrites
  rw [← hfinalEq] at hframe
  have hword : tEnd.toNat + 32 ≤ final.memory.size := by
    rw [facts.finalSize]
    have h := layout.scratchFrontier
    have hk := layout.tk1OffEq
    omega
  have hload := readWord_toNat_of_valid final.memory final.activeWords tEnd (by omega)
    (wordBelowActive_of_covered final.memory final.activeWords tEnd
      (by simpa only [final] using facts.finalCovered)
      (by simpa only [final] using facts.finalFit) hword)
  change (readWord final.memory final.activeWords tEnd).toNat = _
  rw [hload]
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [hframe]
  rfl

/-- Natural-number interpretation of the complete `columns + 2` CIOS scratch area. -/
def ciosScratchValue (columns : Nat) (tP tEnd tk1Off : UInt256)
    (state : CIOSOuterState) : Nat :=
  Modexp.wordLimbsToNat (memoryWordsFrom state.memory tP.toNat columns) +
    UInt256.size ^ columns *
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tEnd.toNat +
    UInt256.size ^ (columns + 1) *
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat

/-- The collector-based prior used by the arithmetic proof is exactly the initial scratch value. -/
theorem ciosIterationPrior_eq_scratchValue
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    ciosIterationPrior columns bP tP tEnd tk1Off state =
      ciosScratchValue columns tP tEnd tk1Off state := by
  simp only [ciosIterationPrior]
  unfold ciosScratchValue
  rw [ciosMultiplyPriorWords_eq_memoryWordsFrom columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout]
  rw [ciosBoundaryTk_eq_initialWord columns bP tP tEnd tk1Off nP tOff nBefore
    shiftedOut state layout]
  rw [ciosBoundaryTk1_eq_initialWord columns bP tP tEnd tk1Off nP tOff nBefore
    shiftedOut state layout]

/-
def CIOSReductionReads
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : Prop :=
  ∀ j, j < columns - 1 →
    let current := schoolbookIterate
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state)
    current.resultPtr.toNat < current.memory.size ∧
      ¬ current.resultPtr ≥ readWords1 current.activeWords current.operandPtr * ⟨32⟩

def CIOSReductionWritesToEnd
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : Prop :=
  ∀ j, j < columns - 1 →
    let current := schoolbookIterate
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state)
    (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat

def CIOSReductionFinalSize
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : Prop :=
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).memory.size = state.memory.size

def CIOSReductionFinalReadGuard
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : Prop :=
  ¬ tEnd ≥
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).activeWords * ⟨32⟩

def CIOSReductionShiftCoverage
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop :=
  CIOSShiftCoverageFacts
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).memory
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).activeWords
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).carry shiftedOut tk1Off tEnd

def CIOSShiftedReadGuard
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop :=
  ¬ tk1Off ≥
    ciosShiftAw2
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).activeWords shiftedOut tEnd * ⟨32⟩

structure CIOSReductionLinkFacts
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop where
  reads : CIOSReductionReads columns bP tP tEnd tk1Off nP n0inv tOff nBefore state
  writesToEnd : CIOSReductionWritesToEnd columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore state
  finalSize : CIOSReductionFinalSize columns bP tP tEnd tk1Off nP n0inv tOff nBefore
    state
  finalReadGuard : CIOSReductionFinalReadGuard columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore state
  shift : CIOSReductionShiftCoverage columns bP tP tEnd tk1Off nP n0inv tOff nBefore
    shiftedOut state
  shiftedReadGuard : CIOSShiftedReadGuard columns bP tP tEnd tk1Off nP n0inv tOff nBefore
    shiftedOut state

theorem ciosReductionLinkFacts_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    CIOSReductionLinkFacts columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state := by
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hinitialCoverage :
      MemoryCovered initial.memory initial.activeWords ∧
        initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosAfterBoundaryAw, multiplyFinal] using
      And.intro multiply.boundary.finalCovered multiply.boundary.finalFit
  have hinitialSize : initial.memory.size = state.memory.size := by
    dsimp [initial, ciosReductionInitial, ciosAfterBoundaryMemory]
    rw [show ciosMultiplyFinal columns bP tP state = multiplyFinal by rfl]
    exact multiply.boundary.mem2Size.trans multiply.finalSize
  have hrange : tOff.toNat + 32 * (columns - 1) ≤ initial.memory.size := by
    rw [hinitialSize]
    have hstop := layout.reductionStop
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hinBounds := schoolbookIterate_inBounds factor (columns - 1) initial
    (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosReductionInitial] using hrange)
  have hsteps : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := schoolbookIterate_operandPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by
          have hfit := layout.reductionOperandFit
          omega))
    have hresult := schoolbookIterate_resultPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    have hresultLo : 32 ≤ (schoolbookIterate factor j initial).resultPtr.toNat := by
      rw [hresult]
      dsimp [initial, ciosReductionInitial]
      have hlo := layout.tOffLo
      omega
    have hwritePtr := schoolbookWritePtr_toNat
      (schoolbookIterate factor j initial).resultPtr hresultLo
    refine ⟨?_, ?_, ?_, (hinBounds.1 j hj).2, (hinBounds.1 j hj).1⟩
    · rw [hop]
      dsimp [initial, ciosReductionInitial]
      have hfit := layout.reductionOperandFit
      omega
    · rw [hresult]
      dsimp [initial, ciosReductionInitial]
      have hstop := layout.reductionStop
      have hfit := layout.scratchFit
      have htk1 := layout.tk1OffEq
      omega
    · rw [hwritePtr, hresult]
      dsimp [initial, ciosReductionInitial]
      have hstop := layout.reductionStop
      have hfit := layout.scratchFit
      have htk1 := layout.tk1OffEq
      omega
  have hreads := schoolbookReadFacts_of_coverage factor (columns - 1) initial
    hinitialCoverage.1 hinitialCoverage.2 hsteps
  have hcoverage := schoolbookIterate_coverage factor (columns - 1) initial
    hinitialCoverage.1 hinitialCoverage.2 (fun j hj =>
      let h := hsteps j hj
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  have hfinalEq : final = schoolbookIterate factor (columns - 1) initial := by
    simpa only [factor, initial, final] using
      ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        state layout.columnsGtOne
  have hfinalCoverage :
      MemoryCovered final.memory final.activeWords ∧
        final.activeWords.toNat * 32 < UInt256.size := by
    rw [hfinalEq]
    exact hcoverage
  have hfinalSize : final.memory.size = state.memory.size := by
    rw [hfinalEq, hinBounds.2, hinitialSize]
  have htEndFit : tEnd.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have htk1 := layout.tk1OffEq
    omega
  have hshiftedFit : shiftedOut.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have hs := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have hshift := ciosShift_coverage final.memory final.activeWords final.carry
    shiftedOut tk1Off tEnd hfinalCoverage.1 hfinalCoverage.2 hshiftedFit
    layout.scratchFit htEndFit
    (by rw [hfinalSize]; have h := layout.scratchFrontier
        have hs := layout.shiftedOutEq; have hk := layout.tk1OffEq; omega)
    (by rw [hfinalSize]; exact layout.scratchFrontier)
    (by rw [hfinalSize]; have h := layout.scratchFrontier
        have hk := layout.tk1OffEq; omega)
  have hwritesToEnd : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat := by
    intro j hj
    dsimp only
    have hstep := hsteps j hj
    have hresult := schoolbookIterate_resultPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    have hlo : 32 ≤ (schoolbookIterate factor j initial).resultPtr.toNat := by
      rw [hresult]
      dsimp [initial, ciosReductionInitial]
      have h := layout.tOffLo
      omega
    rw [schoolbookWritePtr_toNat _ hlo, hresult]
    dsimp [initial, ciosReductionInitial]
    refine ⟨hstep.2.2.2.1, ?_⟩
    have hstop := layout.reductionStop
    omega
  refine {
    reads := by
      unfold CIOSReductionReads
      simpa only [factor, initial] using hreads
    writesToEnd := by
      unfold CIOSReductionWritesToEnd
      simpa only [factor, initial] using hwritesToEnd
    finalSize := by
      unfold CIOSReductionFinalSize
      simpa only [final] using hfinalSize
    finalReadGuard := ?_
    shift := by
      unfold CIOSReductionShiftCoverage
      simpa only [final] using hshift
    shiftedReadGuard := ?_ }
  · unfold CIOSReductionFinalReadGuard
    simpa only [final] using
      (show ¬ tEnd ≥ final.activeWords * ⟨32⟩ by
        apply wordBelowActive_of_covered final.memory final.activeWords tEnd
          hfinalCoverage.1 hfinalCoverage.2
        rw [hfinalSize]
        have h := layout.scratchFrontier
        have hk := layout.tk1OffEq
        omega)
  · unfold CIOSShiftedReadGuard
    simpa only [final] using
      (show ¬ tk1Off ≥ ciosShiftAw2 final.activeWords shiftedOut tEnd * ⟨32⟩ by
        apply wordBelowActive_of_covered
          (ciosShiftMem1 final.memory final.activeWords final.carry shiftedOut tEnd)
          (ciosShiftAw2 final.activeWords shiftedOut tEnd) tk1Off
          hshift.aw2Covered hshift.aw2Fit
        rw [hshift.mem1Size, hfinalSize]
        have h := layout.scratchFrontier
        omega)
-/

set_option Elab.async false in
theorem ciosReductionPrior_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    Modexp.wordLimbsToNat
        (schoolbookPriorResultWords
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
          (columns - 1)
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state)) =
      Modexp.wordLimbsToNat
        (multiplyPassOutputWords
          (ciosOuterAi state.memory state.activeWords state.aOff) (columns - 1)
          (multiplyPassAdvance
            (ciosOuterAi state.memory state.activeWords state.aOff)
            (ciosMultiplyInitial bP tP state))) := by
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hinitialCoverage :
      MemoryCovered initial.memory initial.activeWords ∧
        initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosAfterBoundaryAw] using
      And.intro multiply.boundary.finalCovered multiply.boundary.finalFit
  have hinitialSize : initial.memory.size = state.memory.size := by
    dsimp [initial, ciosReductionInitial, ciosAfterBoundaryMemory]
    exact multiply.boundary.mem2Size.trans multiply.finalSize
  have hrange : tOff.toNat + 32 * (columns - 1) ≤ initial.memory.size := by
    rw [hinitialSize]
    have hstop := layout.reductionStop
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hinBounds := schoolbookIterate_inBounds factor (columns - 1) initial
    (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosReductionInitial] using hrange)
  have hsteps : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := schoolbookIterate_operandPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by
          have hfit := layout.reductionOperandFit
          omega))
    have hresult := schoolbookIterate_resultPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    have hresultLo : 32 ≤ (schoolbookIterate factor j initial).resultPtr.toNat := by
      rw [hresult]
      dsimp [initial, ciosReductionInitial]
      have hlo := layout.tOffLo
      omega
    have hwritePtr := schoolbookWritePtr_toNat
      (schoolbookIterate factor j initial).resultPtr hresultLo
    refine ⟨?_, ?_, ?_, (hinBounds.1 j hj).2, (hinBounds.1 j hj).1⟩
    · rw [hop]
      dsimp [initial, ciosReductionInitial]
      have hfit := layout.reductionOperandFit
      omega
    · rw [hresult]
      dsimp [initial, ciosReductionInitial]
      have hstop := layout.reductionStop
      have hfit := layout.scratchFit
      have htk1 := layout.tk1OffEq
      omega
    · rw [hwritePtr, hresult]
      dsimp [initial, ciosReductionInitial]
      have hstop := layout.reductionStop
      have hfit := layout.scratchFit
      have htk1 := layout.tk1OffEq
      omega
  have hreads := schoolbookReadFacts_of_coverage factor (columns - 1) initial
    hinitialCoverage.1 hinitialCoverage.2 hsteps
  exact congrArg Modexp.wordLimbsToNat
    (ciosReductionPrior_eq_multiplyTail columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore state layout.columnsGtOne multiply.tailPtr
      (by have h := layout.reductionStop; omega)
      (by have h := layout.tk1OffEq; omega)
      (by rw [multiply.tailPtr]
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega)
      multiply.tailWrites
      (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
      (by
        simpa only [initial, ciosReductionInitial] using
          (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
            have hstop := layout.reductionStop
            have hfit := layout.scratchFit
            have htk1 := layout.tk1OffEq
            omega))
      (by simpa only [factor, initial] using hreads)
      (fun j hj => (hinBounds.1 j hj).2)
      multiply.tEndInBounds multiply.tk1InBounds)

structure CIOSReductionStepFacts (current : SchoolbookState) : Prop where
  operandFit : current.operandPtr.toNat + 32 + 31 < UInt256.size
  resultFit : current.resultPtr.toNat + 32 + 31 < UInt256.size
  writeFit : (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size
  writeInBounds :
    (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size

set_option Elab.async false in
theorem ciosReduction_stepFacts_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    ∀ j, j < columns - 1 →
      CIOSReductionStepFacts
        (schoolbookIterate
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)) := by
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hinitialSize : initial.memory.size = state.memory.size := by
    dsimp [initial, ciosReductionInitial, ciosAfterBoundaryMemory]
    exact multiply.boundary.mem2Size.trans multiply.finalSize
  have hrange : tOff.toNat + 32 * (columns - 1) ≤ initial.memory.size := by
    rw [hinitialSize]
    have hstop := layout.reductionStop
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hinBounds := schoolbookIterate_inBounds factor (columns - 1) initial
    (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosReductionInitial] using hrange)
  intro j hj
  have hop := schoolbookIterate_operandPtr_toNat factor j initial (by
    simpa only [initial, ciosReductionInitial] using
      (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by
        have hfit := layout.reductionOperandFit
        omega))
  have hresult := schoolbookIterate_resultPtr_toNat factor j initial (by
    simpa only [initial, ciosReductionInitial] using
      (show tOff.toNat + 32 * j < UInt256.size by
        have hstop := layout.reductionStop
        have hfit := layout.scratchFit
        have htk1 := layout.tk1OffEq
        omega))
  have hresultLo : 32 ≤ (schoolbookIterate factor j initial).resultPtr.toNat := by
    rw [hresult]
    dsimp [initial, ciosReductionInitial]
    have hlo := layout.tOffLo
    omega
  have hwritePtr := schoolbookWritePtr_toNat
    (schoolbookIterate factor j initial).resultPtr hresultLo
  change CIOSReductionStepFacts (schoolbookIterate factor j initial)
  refine
    { operandFit := ?_
      resultFit := ?_
      writeFit := ?_
      writeInBounds := (hinBounds.1 j hj).2 }
  · rw [hop]
    dsimp [initial, ciosReductionInitial]
    have hfit := layout.reductionOperandFit
    omega
  · rw [hresult]
    dsimp [initial, ciosReductionInitial]
    have hstop := layout.reductionStop
    have hfit := layout.scratchFit
    have htk1 := layout.tk1OffEq
    omega
  · rw [hwritePtr, hresult]
    dsimp [initial, ciosReductionInitial]
    have hstop := layout.reductionStop
    have hfit := layout.scratchFit
    have htk1 := layout.tk1OffEq
    omega

set_option Elab.async false in
theorem ciosReductionFinal_coverage_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore state
    MemoryCovered final.memory final.activeWords ∧
      final.activeWords.toNat * 32 < UInt256.size ∧
      final.memory.size = state.memory.size := by
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hinitialCoverage :
      MemoryCovered initial.memory initial.activeWords ∧
        initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosAfterBoundaryAw] using
      And.intro multiply.boundary.finalCovered multiply.boundary.finalFit
  have hinitialSize : initial.memory.size = state.memory.size := by
    dsimp [initial, ciosReductionInitial, ciosAfterBoundaryMemory]
    exact multiply.boundary.mem2Size.trans multiply.finalSize
  have hrange : tOff.toNat + 32 * (columns - 1) ≤ initial.memory.size := by
    rw [hinitialSize]
    have hstop := layout.reductionStop
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hinBounds := schoolbookIterate_inBounds factor (columns - 1) initial
    (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosReductionInitial] using hrange)
  have hstepFacts := ciosReduction_stepFacts_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hsteps : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
    intro j hj
    have h := hstepFacts j hj
    exact ⟨h.operandFit, h.resultFit, h.writeFit, h.writeInBounds⟩
  have hcoverage := schoolbookIterate_coverage factor (columns - 1) initial
    hinitialCoverage.1 hinitialCoverage.2 hsteps
  have hfinalEq : final = schoolbookIterate factor (columns - 1) initial := by
    simpa only [factor, initial, final] using
      ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        state layout.columnsGtOne
  rw [show ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore
    state = final by rfl, hfinalEq]
  exact ⟨hcoverage.1, hcoverage.2, hinBounds.2.trans hinitialSize⟩

structure CIOSReductionWriteFacts (current : SchoolbookState) (tEnd : UInt256) : Prop where
  inBounds : (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size
  belowEnd : (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat

set_option Elab.async false in
theorem ciosReduction_writesToEnd_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
      CIOSReductionWriteFacts current tEnd := by
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hinitialSize : initial.memory.size = state.memory.size := by
    dsimp [initial, ciosReductionInitial, ciosAfterBoundaryMemory]
    exact multiply.boundary.mem2Size.trans multiply.finalSize
  have hrange : tOff.toNat + 32 * (columns - 1) ≤ initial.memory.size := by
    rw [hinitialSize]
    have hstop := layout.reductionStop
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hinBounds := schoolbookIterate_inBounds factor (columns - 1) initial
    (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosReductionInitial] using hrange)
  intro j hj
  dsimp only
  have hresult := schoolbookIterate_resultPtr_toNat factor j initial (by
    simpa only [initial, ciosReductionInitial] using
      (show tOff.toNat + 32 * j < UInt256.size by
        have hstop := layout.reductionStop
        have hfit := layout.scratchFit
        have htk1 := layout.tk1OffEq
        omega))
  have hlo : 32 ≤ (schoolbookIterate factor j initial).resultPtr.toNat := by
    rw [hresult]
    dsimp [initial, ciosReductionInitial]
    have h := layout.tOffLo
    omega
  change CIOSReductionWriteFacts (schoolbookIterate factor j initial) tEnd
  refine
    { inBounds := (hinBounds.1 j hj).2
      belowEnd := ?_ }
  rw [schoolbookWritePtr_toNat _ hlo, hresult]
  dsimp [initial, ciosReductionInitial]
  have hstop := layout.reductionStop
  omega

set_option Elab.async false in
theorem ciosShiftLow_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosShiftTk
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
      tEnd).toNat =
      (ciosBoundaryTkNew
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).toNat := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hwritesToEnd := ciosReduction_writesToEnd_of_layout columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout
  have hwrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat := by
    intro j hj
    have h := hwritesToEnd j hj
    exact ⟨h.inBounds, h.belowEnd⟩
  exact ciosShiftLow_eq_boundaryUpper columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore state layout.columnsGtOne multiply.tEndInBounds
    (by have h := layout.tk1OffEq; omega) multiply.tk1InBounds
    hwrites
    (by
      simpa only [final] using
        (show tEnd.toNat < final.memory.size by
          rw [hfinal.2.2]
          have h := layout.scratchFrontier
          have hk := layout.tk1OffEq
          omega))
    (by
      simpa only [final] using
        (show ¬ tEnd ≥ final.activeWords * ⟨32⟩ by
          apply wordBelowActive_of_covered final.memory final.activeWords tEnd
            hfinal.1 hfinal.2.1
          rw [hfinal.2.2]
          have h := layout.scratchFrontier
          have hk := layout.tk1OffEq
          omega))

set_option Elab.async false in
theorem ciosShiftCoverage_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore state
    CIOSShiftCoverageFacts final.memory final.activeWords final.carry shiftedOut
      tk1Off tEnd := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hshiftedFit : shiftedOut.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have hs := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have htEndFit : tEnd.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have htk1 := layout.tk1OffEq
    omega
  change CIOSShiftCoverageFacts final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd
  exact ciosShift_coverage final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd hfinal.1 hfinal.2.1 hshiftedFit layout.scratchFit htEndFit
    (by
      rw [hfinal.2.2]
      have h := layout.scratchFrontier
      have hs := layout.shiftedOutEq
      have hk := layout.tk1OffEq
      omega)
    (by rw [hfinal.2.2]; exact layout.scratchFrontier)
    (by
      rw [hfinal.2.2]
      have h := layout.scratchFrontier
      have hk := layout.tk1OffEq
      omega)

set_option Elab.async false in
theorem ciosShiftExtra_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosShiftTk1
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
      shiftedOut tk1Off tEnd).toNat =
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off +
          ciosBoundaryOverflow
            (ciosMultiplyFinal columns bP tP state).memory
            (ciosMultiplyFinal columns bP tP state).activeWords tEnd
            (ciosMultiplyFinal columns bP tP state).carry).toNat := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiply := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hshift := ciosShiftCoverage_of_layout columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout
  have hwritesToEnd := ciosReduction_writesToEnd_of_layout columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout
  have hwrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tk1Off.toNat := by
    intro j hj
    have h := hwritesToEnd j hj
    refine ⟨h.inBounds, ?_⟩
    have hk := layout.tk1OffEq
    exact h.belowEnd.trans (by omega)
  exact ciosShiftExtra_eq_boundaryExtra columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout.columnsGtOne multiply.tk1InBounds hwrites
    (by
      simpa only [final] using
        (show shiftedOut.toNat + 32 ≤ final.memory.size by
          rw [hfinal.2.2]
          have h := layout.scratchFrontier
          have hs := layout.shiftedOutEq
          have hk := layout.tk1OffEq
          omega))
    (by
      have hs := layout.shiftedOutEq
      have hk := layout.tk1OffEq
      omega)
    (by
      simpa only [final] using
        (show tk1Off.toNat <
            (ciosShiftMem1 final.memory final.activeWords final.carry shiftedOut tEnd).size by
          rw [hshift.mem1Size, hfinal.2.2]
          have h := layout.scratchFrontier
          omega))
    (by
      simpa only [final] using
        (show ¬ tk1Off ≥ ciosShiftAw2 final.activeWords shiftedOut tEnd * ⟨32⟩ by
          apply wordBelowActive_of_covered
            (ciosShiftMem1 final.memory final.activeWords final.carry shiftedOut tEnd)
            (ciosShiftAw2 final.activeWords shiftedOut tEnd) tk1Off
            hshift.aw2Covered hshift.aw2Fit
          rw [hshift.mem1Size, hfinal.2.2]
          have h := layout.scratchFrontier
          omega))

set_option Elab.async false in
theorem ciosPhaseLinks_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    CIOSPhaseLinks columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
      state := by
  exact
    { reductionPrior := ciosReductionPrior_of_layout columns bP tP tEnd tk1Off nP
        n0inv tOff nBefore shiftedOut state layout
      boundaryLow := ciosBoundaryLow_of_layout columns bP tP tEnd tk1Off nP tOff
        nBefore shiftedOut state layout
      shiftLow := ciosShiftLow_of_layout columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut state layout
      shiftExtra := ciosShiftExtra_of_layout columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state layout }

/-- The last write of every concrete outer iteration clears the extra scratch word. -/
theorem ciosOuterAdvance_extraWord_zero
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
      (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state).memory tk1Off.toNat = 0 := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let mem2 := ciosShiftMem2 final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hshift := ciosShiftCoverage_of_layout columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout
  have htk1 : tk1Off.toNat ≤ mem2.size := by
    dsimp [mem2]
    rw [hshift.mem2Size, hfinal.2.2]
    have h := layout.scratchFrontier
    omega
  have hgap : tk1Off.toNat - mem2.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le htk1]
    exact lt_usize 0 (by norm_num)
  change Modexp.MultiLimbMemoryModel.memoryWordNat
    ((⟨0⟩ : UInt256).toByteArray.write 0 mem2 tk1Off.toNat 32) tk1Off.toNat = 0
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  simpa using fromByteArrayBigEndian_toByteArray (⟨0⟩ : UInt256)

/-- The extra scratch word remains zero after any finite number of outer iterations. -/
theorem ciosOuterIterate_extraWord_zero
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut iterations state).memory tk1Off.toNat = 0 := by
  cases iterations with
  | zero => exact hextra
  | succ iterations =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      have hcurrentLayout := (ciosOuterIterate_layout iterations columns bP tP tEnd
        tk1Off nP n0inv tOff nBefore shiftedOut state layout
        (fun i hi => haFit i (by omega))).1
      simpa only [ciosOuterIterate, current] using
        ciosOuterAdvance_extraWord_zero columns bP tP tEnd tk1Off nP n0inv tOff
          nBefore shiftedOut current hcurrentLayout

/-- A zero extra scratch word discharges both no-wrap premises used by the exact upper-word
recomposition. -/
theorem ciosUpperFits_of_extraWord_zero
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0) :
    ((ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off).toNat +
      (ciosBoundaryOverflow
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).toNat < UInt256.size) ∧
    ((ciosShiftTk1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        shiftedOut tk1Off tEnd).toNat +
      (ciosShiftOverflow
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        tEnd).toNat < UInt256.size) := by
  let boundaryExtra := ciosBoundaryTk1
    (ciosMultiplyFinal columns bP tP state).memory
    (ciosMultiplyFinal columns bP tP state).activeWords tEnd
    (ciosMultiplyFinal columns bP tP state).carry tk1Off
  let boundaryOverflow := ciosBoundaryOverflow
    (ciosMultiplyFinal columns bP tP state).memory
    (ciosMultiplyFinal columns bP tP state).activeWords tEnd
    (ciosMultiplyFinal columns bP tP state).carry
  have hextraNat : boundaryExtra.toNat = 0 := by
    dsimp [boundaryExtra]
    rw [ciosBoundaryTk1_eq_initialWord columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state layout, hextra]
  have hextraWord : boundaryExtra = ⟨0⟩ := by
    apply u256_inj
    simpa using hextraNat
  have hoverflowBoundary : boundaryOverflow.toNat ≤ 1 := by
    exact ult_toNat_le_one _ _
  have links := ciosPhaseLinks_of_layout columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut state layout
  have hshiftTk1 :
      (ciosShiftTk1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        shiftedOut tk1Off tEnd).toNat = boundaryOverflow.toNat := by
    rw [links.shiftExtra]
    change (boundaryExtra + boundaryOverflow).toNat = boundaryOverflow.toNat
    rw [hextraWord, u256_zero_add]
  have hoverflowShift :
      (ciosShiftOverflow
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        tEnd).toNat ≤ 1 := by
    exact ult_toNat_le_one _ _
  constructor
  · change boundaryExtra.toNat + boundaryOverflow.toNat < UInt256.size
    rw [hextraNat]
    have hsize : 1 < UInt256.size := by decide
    omega
  · rw [hshiftTk1]
    have hsize : 2 < UInt256.size := by decide
    omega

/-- The concrete layout discharges every framing premise in the exact one-iteration arithmetic
equation. -/
theorem ciosOuterAdvance_recompose_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hinv :
      (ciosBoundaryN0
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hboundaryFit :
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off).toNat +
        (ciosBoundaryOverflow
          (ciosMultiplyFinal columns bP tP state).memory
          (ciosMultiplyFinal columns bP tP state).activeWords tEnd
          (ciosMultiplyFinal columns bP tP state).carry).toNat < UInt256.size)
    (hshiftFit :
      (ciosShiftTk1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        shiftedOut tk1Off tEnd).toNat +
        (ciosShiftOverflow
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
          tEnd).toNat < UInt256.size) :
    UInt256.size *
        ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state =
      ciosIterationPrior columns bP tP tEnd tk1Off state +
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat *
          ciosIterationMultiplier columns bP tP state +
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state).toNat *
          ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore
            state := by
  exact ciosOuterAdvance_recompose columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut state layout.columnsGtOne hinv hboundaryFit hshiftFit
    (ciosPhaseLinks_of_layout columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state layout)

/-- The low word produced by the multiply pass is the complete CIOS numerator modulo the word
radix.  The two preserved upper scratch words vanish under this reduction. -/
theorem ciosBoundaryT0_eq_iterationNumerator_mod
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosBoundaryT0
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry tk1Off tP).toNat =
      (ciosIterationPrior columns bP tP tEnd tk1Off state +
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat *
          ciosIterationMultiplier columns bP tP state) % UInt256.size := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  let final := ciosMultiplyFinal columns bP tP state
  have hfinal := ciosMultiplyFinal_eq_iterate columns bP tP state (by
    have h := layout.columnsGtOne
    omega)
  have hmultiply := multiplyPassCollectors_recompose ai columns initial
  rw [← hfinal] at hmultiply
  have hhead := multiplyPassOutputWords_recompose_head ai columns initial (by
    have h := layout.columnsGtOne
    omega)
  have hboundary :
      (ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat =
        (schoolbookStep initial.memory initial.activeWords initial.operandPtr
          initial.resultPtr ai initial.carry).1.toNat := by
    simpa [ai, initial, final, ciosMultiplyInitial] using
      ciosBoundaryLow_of_layout columns bP tP tEnd tk1Off nP tOff nBefore
        shiftedOut state layout
  have hrow :
      (ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat +
          UInt256.size * Modexp.wordLimbsToNat
            (multiplyPassOutputWords ai (columns - 1)
              (multiplyPassAdvance ai initial)) +
          UInt256.size ^ columns * final.carry.toNat =
        Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
          ai.toNat * Modexp.wordLimbsToNat
            (multiplyPassOperandWords ai columns initial) := by
    rw [hboundary, ← hhead]
    simpa [initial, ciosMultiplyInitial] using hmultiply
  have hcolumns : 0 < columns := by
    have h := layout.columnsGtOne
    omega
  have hpow : UInt256.size ^ columns % UInt256.size = 0 := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : columns ≠ 0)
    simp [pow_succ]
  have hmod := congrArg (fun value : Nat => value % UInt256.size) hrow
  have hlow :
      (ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat =
        (Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
          ai.toNat * Modexp.wordLimbsToNat
            (multiplyPassOperandWords ai columns initial)) % UInt256.size := by
    have hboundaryFit :
        (ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat <
          UInt256.size :=
      (ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).val.isLt
    have hleft :
        ((ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat +
            UInt256.size * Modexp.wordLimbsToNat
              (multiplyPassOutputWords ai (columns - 1)
                (multiplyPassAdvance ai initial)) +
            UInt256.size ^ columns * final.carry.toNat) % UInt256.size =
          (ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat := by
      simp [Nat.add_mod, Nat.mul_mod, hpow, Nat.mod_eq_of_lt hboundaryFit]
    change
      ((ciosBoundaryT0 final.memory final.activeWords tEnd final.carry tk1Off tP).toNat +
          UInt256.size * Modexp.wordLimbsToNat
            (multiplyPassOutputWords ai (columns - 1)
              (multiplyPassAdvance ai initial)) +
          UInt256.size ^ columns * final.carry.toNat) % UInt256.size =
        (Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
          ai.toNat * Modexp.wordLimbsToNat
            (multiplyPassOperandWords ai columns initial)) % UInt256.size at hmod
    rw [hleft] at hmod
    exact hmod
  rw [show ciosMultiplyFinal columns bP tP state = final by rfl]
  rw [hlow]
  simp only [ciosIterationPrior, ciosIterationMultiplier]
  change _ =
    (Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
        UInt256.size ^ columns * _ + UInt256.size ^ (columns + 1) * _ +
      ai.toNat * Modexp.wordLimbsToNat (multiplyPassOperandWords ai columns initial)) %
        UInt256.size
  have hpowNext : UInt256.size ^ (columns + 1) % UInt256.size = 0 := by
    rw [pow_succ]
    simp
  rw [show
    Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
          UInt256.size ^ columns *
            (ciosBoundaryTk final.memory final.activeWords tEnd).toNat +
          UInt256.size ^ (columns + 1) *
            (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off).toNat +
        ai.toNat * Modexp.wordLimbsToNat (multiplyPassOperandWords ai columns initial) =
      (Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
        ai.toNat * Modexp.wordLimbsToNat (multiplyPassOperandWords ai columns initial)) +
      (UInt256.size ^ columns *
          (ciosBoundaryTk final.memory final.activeWords tEnd).toNat +
        UInt256.size ^ (columns + 1) *
          (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off).toNat) by ring]
  simp [Nat.add_mod, Nat.mul_mod, hpow, hpowNext]

/-- Consequently, the factor loaded onto the reduction loop is exactly the pure Montgomery
factor of the complete unbounded iteration numerator. -/
theorem ciosReductionFactor_eq_montgomeryFactor
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state).toNat =
      Modexp.montgomeryFactor UInt256.size n0inv.toNat
        (ciosIterationPrior columns bP tP tEnd tk1Off state +
          (ciosOuterAi state.memory state.activeWords state.aOff).toNat *
            ciosIterationMultiplier columns bP tP state) := by
  unfold ciosReductionFactor ciosBoundaryFactor
  rw [evmMontgomeryFactor_toNat]
  unfold Modexp.montgomeryFactor
  rw [ciosBoundaryT0_eq_iterationNumerator_mod columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout]
  simp only [Nat.mod_mod]

/-- Once the concrete low-word multiplication is identified with `montgomeryFactor`, the exact
numerator equation is precisely one pure CIOS transition. -/
theorem ciosIterationNext_eq_montgomeryCIOSStep
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hinv :
      (ciosBoundaryN0
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hboundaryFit :
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off).toNat +
        (ciosBoundaryOverflow
          (ciosMultiplyFinal columns bP tP state).memory
          (ciosMultiplyFinal columns bP tP state).activeWords tEnd
          (ciosMultiplyFinal columns bP tP state).carry).toNat < UInt256.size)
    (hshiftFit :
      (ciosShiftTk1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        shiftedOut tk1Off tEnd).toNat +
        (ciosShiftOverflow
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
          tEnd).toNat < UInt256.size)
    (hfactor :
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state).toNat =
        Modexp.montgomeryFactor UInt256.size n0inv.toNat
          (ciosIterationPrior columns bP tP tEnd tk1Off state +
            (ciosOuterAi state.memory state.activeWords state.aOff).toNat *
              ciosIterationMultiplier columns bP tP state)) :
    ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state =
      Modexp.montgomeryCIOSStep UInt256.size
        (ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
        n0inv.toNat (ciosIterationMultiplier columns bP tP state)
        (ciosIterationPrior columns bP tP tEnd tk1Off state)
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat := by
  have hrec := ciosOuterAdvance_recompose_of_layout columns bP tP tEnd tk1Off nP
    n0inv tOff nBefore shiftedOut state layout hinv hboundaryFit hshiftFit
  unfold Modexp.montgomeryCIOSStep
  rw [hfactor] at hrec
  calc
    ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state =
      (UInt256.size * ciosIterationNext columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state) / UInt256.size := by
          symm
          exact Nat.mul_div_cancel_left _ (by norm_num [UInt256.size])
    _ = _ := by rw [hrec]

/-- Fully concrete one-step CIOS semantic contract: layout, inverse, and the two no-wrap carry
bounds suffice to identify the generated result with the pure Montgomery recurrence. -/
theorem ciosIterationNext_eq_montgomeryCIOSStep_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hinv :
      (ciosBoundaryN0
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hboundaryFit :
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off).toNat +
        (ciosBoundaryOverflow
          (ciosMultiplyFinal columns bP tP state).memory
          (ciosMultiplyFinal columns bP tP state).activeWords tEnd
          (ciosMultiplyFinal columns bP tP state).carry).toNat < UInt256.size)
    (hshiftFit :
      (ciosShiftTk1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        shiftedOut tk1Off tEnd).toNat +
        (ciosShiftOverflow
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
          tEnd).toNat < UInt256.size) :
    ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state =
      Modexp.montgomeryCIOSStep UInt256.size
        (ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
        n0inv.toNat (ciosIterationMultiplier columns bP tP state)
        (ciosIterationPrior columns bP tP tEnd tk1Off state)
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat := by
  exact ciosIterationNext_eq_montgomeryCIOSStep columns bP tP tEnd tk1Off nP
    n0inv tOff nBefore shiftedOut state layout hinv hboundaryFit hshiftFit
    (ciosReductionFactor_eq_montgomeryFactor columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state layout)

/-- The maintained zero-extra-word invariant leaves only the standard low-limb inverse condition
as an arithmetic premise for one exact pure CIOS step. -/
theorem ciosIterationNext_eq_montgomeryCIOSStep_of_extraWord_zero
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0)
    (hinv :
      (ciosBoundaryN0
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1) :
    ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state =
      Modexp.montgomeryCIOSStep UInt256.size
        (ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
        n0inv.toNat (ciosIterationMultiplier columns bP tP state)
        (ciosIterationPrior columns bP tP tEnd tk1Off state)
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat := by
  have hfits := ciosUpperFits_of_extraWord_zero columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout hextra
  exact ciosIterationNext_eq_montgomeryCIOSStep_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout hinv hfits.1 hfits.2

end Modexp.MultiLimbMontgomeryCIOSSemantic
