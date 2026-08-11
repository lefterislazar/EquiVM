import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSScanLinks

/-! # CIOS immutable operand links -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A multiply-pass operand collector is the initial operand memory range when the complete
operand lies below the first result write. -/
theorem multiplyPassOperandWords_eq_initialMemory
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hoperandFit : state.operandPtr.toNat + 32 * n < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hseparate : state.operandPtr.toNat + 32 * n ≤ state.resultPtr.toNat)
    (hloads : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.operandPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    multiplyPassOperandWords a n state =
      memoryWordsFrom state.memory state.operandPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hoperandStep : next.operandPtr.toNat = state.operandPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.operandPtr (by omega)
      have hresultStep : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextLoads : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
              current.operandPtr.toNat := by
        intro j hj
        simpa only [next, multiplyPassIterate_advance] using hloads (j + 1) (by omega)
      have hnextWrites : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.resultPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, multiplyPassIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hoperandStep]; omega)
        (by rw [hresultStep]; omega)
        (by rw [hoperandStep, hresultStep]; omega) hnextLoads hnextWrites
      have hheadNat :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              state.operandPtr.toNat := by
        simpa only [multiplyPassIterate] using hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 =
            UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                state.operandPtr.toNat) := by
        apply u256_inj
        rw [hheadNat]
        rw [UInt256.toNat_ofNat_of_lt
          (memoryWordNat_lt_size state.memory state.operandPtr.toNat)]
      have hfirstWrite : state.resultPtr.toNat + 32 ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hwrites 0 (by omega)
      have hframeRaw := memoryWordsFrom_write_above
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory state.resultPtr.toNat
        next.operandPtr.toNat n (by rw [toByteArray_size]) (by omega)
        (by rw [hoperandStep]; omega)
      have hframe : memoryWordsFrom next.memory next.operandPtr.toNat n =
          memoryWordsFrom state.memory next.operandPtr.toNat n := by
        simpa only [next, multiplyPassAdvance, multiplyPassMemory] using hframeRaw
      simp only [multiplyPassOperandWords, memoryWordsFrom]
      change
        (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 :: multiplyPassOperandWords a n next =
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                state.operandPtr.toNat) ::
            memoryWordsFrom state.memory (state.operandPtr.toNat + 32) n
      rw [hhead, htail, hframe, hoperandStep]

/-- A reduction-pass operand collector is its initial operand memory range when that range lies
below the first preceding-word result store. -/
theorem schoolbookOperandWords_eq_initialMemory
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hoperandFit : state.operandPtr.toNat + 32 * n < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hresultLo : 32 ≤ state.resultPtr.toNat)
    (hseparate : state.operandPtr.toNat + 32 * n ≤
      (schoolbookWritePtr state.resultPtr).toNat)
    (hloads : ∀ j, j < n →
      let current := schoolbookIterate a j state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.operandPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := schoolbookIterate a j state
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size) :
    schoolbookOperandWords a n state =
      memoryWordsFrom state.memory state.operandPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hoperandStep : next.operandPtr.toNat = state.operandPtr.toNat + 32 := by
        dsimp only [next, schoolbookAdvance]
        exact uadd_word_lit32_toNat state.operandPtr (by omega)
      have hresultStep : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, schoolbookAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextLo : 32 ≤ next.resultPtr.toNat := by omega
      have hwriteStep : (schoolbookWritePtr next.resultPtr).toNat =
          (schoolbookWritePtr state.resultPtr).toNat + 32 := by
        rw [schoolbookWritePtr_toNat next.resultPtr hnextLo,
          schoolbookWritePtr_toNat state.resultPtr hresultLo, hresultStep]
        omega
      have hnextLoads : ∀ j, j < n →
          let current := schoolbookIterate a j next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
              current.operandPtr.toNat := by
        intro j hj
        simpa only [next, schoolbookIterate_advance] using hloads (j + 1) (by omega)
      have hnextWrites : ∀ j, j < n →
          let current := schoolbookIterate a j next
          (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, schoolbookIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hoperandStep]; omega)
        (by rw [hresultStep]; omega) hnextLo
        (by rw [hoperandStep, hwriteStep]; omega) hnextLoads hnextWrites
      have hheadNat :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              state.operandPtr.toNat := by
        simpa only [schoolbookIterate] using hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 =
            UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                state.operandPtr.toNat) := by
        apply u256_inj
        rw [hheadNat]
        rw [UInt256.toNat_ofNat_of_lt
          (memoryWordNat_lt_size state.memory state.operandPtr.toNat)]
      have hfirstWrite : (schoolbookWritePtr state.resultPtr).toNat + 32 ≤
          state.memory.size := by
        simpa only [schoolbookIterate] using hwrites 0 (by omega)
      have hframeRaw := memoryWordsFrom_write_above
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory
        (schoolbookWritePtr state.resultPtr).toNat next.operandPtr.toNat n
        (by rw [toByteArray_size]) (by omega) (by rw [hoperandStep]; omega)
      have hframe : memoryWordsFrom next.memory next.operandPtr.toNat n =
          memoryWordsFrom state.memory next.operandPtr.toNat n := by
        simpa only [next, schoolbookAdvance, schoolbookMemory] using hframeRaw
      simp only [schoolbookOperandWords, memoryWordsFrom]
      change
        (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 :: schoolbookOperandWords a n next =
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                state.operandPtr.toNat) ::
            memoryWordsFrom state.memory (state.operandPtr.toNat + 32) n
      rw [hhead, htail, hframe, hoperandStep]

/-- Under the allocation ordering `bEnd ≤ tP`, the generated multiplier collector is exactly the
initial `columns`-word multiplier array. -/
theorem ciosIterationMultiplier_eq_memoryWordsFrom
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hbEnd : bP.toNat + 32 * columns ≤ tP.toNat) :
    ciosIterationMultiplier columns bP tP state =
      Modexp.wordLimbsToNat (memoryWordsFrom state.memory bP.toNat columns) := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  have houter := readWords1_coverage state.memory state.activeWords state.aOff
    layout.covered layout.activeFit layout.aFit
  have hinitialCoverage : MemoryCovered initial.memory initial.activeWords ∧
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
          have h := layout.bFit
          omega))
    have hresult := multiplyPassIterate_resultPtr_toNat ai j initial (by
      simpa only [initial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * j < UInt256.size by
          have hfit := layout.scratchFit
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega))
    refine ⟨?_, ?_, facts.writes j hj⟩
    · rw [hop]
      dsimp only [initial, ciosMultiplyInitial]
      have h := layout.bFit
      omega
    · rw [hresult]
      dsimp only [initial, ciosMultiplyInitial]
      have hfit := layout.scratchFit
      have hstop := layout.multiplyStop
      have htk1 := layout.tk1OffEq
      omega
  have hloads : ∀ j, j < columns →
      let current := multiplyPassIterate ai j initial
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.operandPtr.toNat := by
    intro j hj
    let current := multiplyPassIterate ai j initial
    have hcurrent := multiplyPassIterate_coverage ai j initial hinitialCoverage.1
      hinitialCoverage.2 (fun i hi => hsteps i (by omega))
    have hop := multiplyPassIterate_operandPtr_toNat ai j initial (by
      simpa only [initial, ciosMultiplyInitial] using
        (show bP.toNat + 32 * j < UInt256.size by
          have h := layout.bFit
          omega))
    have hword : current.operandPtr.toNat + 32 ≤ current.memory.size := by
      have hsize := (multiplyPassIterate_inBounds ai j initial
        (by
          simpa only [initial, ciosMultiplyInitial] using
            (show tP.toNat + 32 * j < UInt256.size by
              have hfit := layout.scratchFit
              have hstop := layout.multiplyStop
              have htk1 := layout.tk1OffEq
              omega))
        (by
          simpa only [initial, ciosMultiplyInitial] using
            (show tP.toNat + 32 * j ≤ state.memory.size by
              have hfrontier := layout.scratchFrontier
              have hstop := layout.multiplyStop
              have htk1 := layout.tk1OffEq
              omega))).2
      rw [show current.memory.size = state.memory.size by
        simpa only [current, initial, ciosMultiplyInitial] using hsize]
      rw [show current.operandPtr.toNat = bP.toNat + 32 * j by
        simpa only [current, initial, ciosMultiplyInitial] using hop]
      have hjEnd : bP.toNat + 32 * j + 32 ≤ bP.toNat + 32 * columns := by
        omega
      have htPMemory : tP.toNat ≤ state.memory.size := by
        have hfrontier := layout.scratchFrontier
        have hstop := layout.multiplyStop
        have htk1 := layout.tk1OffEq
        omega
      exact hjEnd.trans (hbEnd.trans htPMemory)
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.operandPtr (by simpa only [current] using hcurrent.1)
      (by simpa only [current] using hcurrent.2) hword
    simpa only [current, schoolbookOperands] using hload
  have hcollector := multiplyPassOperandWords_eq_initialMemory ai columns initial
    (by simpa only [initial, ciosMultiplyInitial] using
      (show bP.toNat + 32 * columns < UInt256.size by
        have h := layout.bFit
        omega))
    (by simpa only [initial, ciosMultiplyInitial] using
      (show tP.toNat + 32 * columns < UInt256.size by
        have hfit := layout.scratchFit
        have hstop := layout.multiplyStop
        have htk1 := layout.tk1OffEq
        omega))
    (by simpa only [initial, ciosMultiplyInitial] using hbEnd)
    hloads facts.writes
  unfold ciosIterationMultiplier
  simpa only [ai, initial, ciosMultiplyInitial] using
    congrArg Modexp.wordLimbsToNat hcollector

/-- A complete multiply pass preserves any consecutive range below its first result write. -/
theorem multiplyPassIterate_memoryWords_below
    (a : UInt256) (n : Nat) (state : MultiplyPassState) (ptr count : Nat)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.resultPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (multiplyPassIterate a n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hresultStep : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hfirstWrite : state.resultPtr.toNat + 32 ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hwrites 0 (by omega)
      have htailWrites : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.resultPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, multiplyPassIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hresultStep]; omega)
        (by rw [hresultStep]; omega) htailWrites
      have hfirst := memoryWordsFrom_write_above
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory state.resultPtr.toNat ptr count
        (by rw [toByteArray_size]) (by omega) hbelow
      have hfirst' : memoryWordsFrom next.memory ptr count =
          memoryWordsFrom state.memory ptr count := by
        simpa only [next, multiplyPassAdvance, multiplyPassMemory] using hfirst
      calc
        memoryWordsFrom (multiplyPassIterate a (n + 1) state).memory ptr count =
            memoryWordsFrom (multiplyPassIterate a n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := hfirst'

/-- A complete schoolbook reduction pass likewise preserves ranges below its first write. -/
theorem schoolbookIterate_memoryWords_below
    (a : UInt256) (n : Nat) (state : SchoolbookState) (ptr count : Nat)
    (hresultLo : 32 ≤ state.resultPtr.toNat)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hbelow : ptr + 32 * count ≤ (schoolbookWritePtr state.resultPtr).toNat)
    (hwrites : ∀ j, j < n →
      let current := schoolbookIterate a j state
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (schoolbookIterate a n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hresultStep : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, schoolbookAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextLo : 32 ≤ next.resultPtr.toNat := by omega
      have hwriteStep : (schoolbookWritePtr next.resultPtr).toNat =
          (schoolbookWritePtr state.resultPtr).toNat + 32 := by
        rw [schoolbookWritePtr_toNat next.resultPtr hnextLo,
          schoolbookWritePtr_toNat state.resultPtr hresultLo, hresultStep]
        omega
      have hfirstWrite : (schoolbookWritePtr state.resultPtr).toNat + 32 ≤
          state.memory.size := by
        simpa only [schoolbookIterate] using hwrites 0 (by omega)
      have htailWrites : ∀ j, j < n →
          let current := schoolbookIterate a j next
          (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, schoolbookIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next hnextLo (by rw [hresultStep]; omega)
        (by rw [hwriteStep]; omega) htailWrites
      have hfirst := memoryWordsFrom_write_above
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory
        (schoolbookWritePtr state.resultPtr).toNat ptr count
        (by rw [toByteArray_size]) (by omega) hbelow
      have hfirst' : memoryWordsFrom next.memory ptr count =
          memoryWordsFrom state.memory ptr count := by
        simpa only [next, schoolbookAdvance, schoolbookMemory] using hfirst
      calc
        memoryWordsFrom (schoolbookIterate a (n + 1) state).memory ptr count =
            memoryWordsFrom (schoolbookIterate a n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := hfirst'

/-- Every write in one CIOS outer iteration is at or above `tP`; consequently any complete range
ending at `tP` is immutable across the transition. -/
theorem ciosOuterAdvance_memoryWords_below
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) (ptr count : Nat)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hbelow : ptr + 32 * count ≤ tP.toNat) :
    memoryWordsFrom
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let shiftMem1 := ciosShiftMem1 reductionFinal.memory reductionFinal.activeWords
    reductionFinal.carry shiftedOut tEnd
  let shiftMem2 := ciosShiftMem2 reductionFinal.memory reductionFinal.activeWords
    reductionFinal.carry shiftedOut tk1Off tEnd
  let finalMem := ciosShiftMemory reductionFinal.memory reductionFinal.activeWords
    reductionFinal.carry shiftedOut tk1Off tEnd
  have multiplyFacts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hmultiplyEq : multiplyFinal =
      multiplyPassIterate ai columns multiplyInitial := by
    simpa only [ai, multiplyInitial, multiplyFinal] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have h := layout.columnsGtOne
        omega)
  have hmultiplyFrame : memoryWordsFrom multiplyFinal.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
    rw [hmultiplyEq]
    have h := multiplyPassIterate_memoryWords_below ai columns multiplyInitial ptr count
      (by
        simpa only [multiplyInitial, ciosMultiplyInitial] using
          (show tP.toNat + 32 * columns < UInt256.size by
            have hfit := layout.scratchFit
            have hstop := layout.multiplyStop
            have htk1 := layout.tk1OffEq
            omega))
      (by simpa only [multiplyInitial, ciosMultiplyInitial] using hbelow)
      multiplyFacts.writes
    simpa only [multiplyInitial, ciosMultiplyInitial] using h
  have htEndWrite : tEnd.toNat + 32 ≤ multiplyFinal.memory.size := by
    rw [show multiplyFinal.memory.size = state.memory.size by
      simpa only [multiplyFinal] using multiplyFacts.finalSize]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hboundary1 :
      memoryWordsFrom
          (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry) ptr count =
        memoryWordsFrom multiplyFinal.memory ptr count := by
    simpa only [ciosBoundaryMem1] using
      memoryWordsFrom_write_above
        (ciosBoundaryTkNew multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry).toByteArray multiplyFinal.memory tEnd.toNat ptr count
        (by rw [toByteArray_size]) (by omega)
        (by exact hbelow.trans (by
          have hstop := layout.multiplyStop
          omega))
  have htk1Write : tk1Off.toNat + 32 ≤
      (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry).size := by
    rw [multiplyFacts.boundary.mem1Size, multiplyFacts.finalSize]
    exact layout.scratchFrontier
  have hboundary2 :
      memoryWordsFrom
          (ciosBoundaryMem2 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry tk1Off) ptr count =
        memoryWordsFrom
          (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry) ptr count := by
    simpa only [ciosBoundaryMem2] using
      memoryWordsFrom_write_above
        (ciosBoundaryTk1 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry tk1Off +
          ciosBoundaryOverflow multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry).toByteArray
        (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry) tk1Off.toNat ptr count
        (by rw [toByteArray_size]) (by omega)
        (by
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega)
  have hreductionEq : reductionFinal =
      schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 1) reductionInitial := by
    simpa only [reductionInitial, reductionFinal] using
      ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore state layout.columnsGtOne
  have hreductionWrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        reductionInitial
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
    intro j hj
    simpa only [reductionInitial] using
      (ciosReduction_writesToEnd_of_layout columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state layout j hj).inBounds
  have hfirstReductionWrite :
      (schoolbookWritePtr reductionInitial.resultPtr).toNat = tP.toNat := by
    rw [schoolbookWritePtr_toNat reductionInitial.resultPtr (by
      simpa only [reductionInitial, ciosReductionInitial] using layout.tOffLo)]
    change tOff.toNat - 32 = tP.toNat
    have hreduce := layout.reductionStop
    have hmultiply := layout.multiplyStop
    have hcolumns : columns - 1 + 1 = columns := by
      have h := layout.columnsGtOne
      omega
    have hmul : 32 * columns = 32 * (columns - 1) + 32 := by
      conv_lhs => rw [← hcolumns]
      simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hreductionFrame : memoryWordsFrom reductionFinal.memory ptr count =
      memoryWordsFrom reductionInitial.memory ptr count := by
    rw [hreductionEq]
    apply schoolbookIterate_memoryWords_below
    · simpa only [reductionInitial, ciosReductionInitial] using layout.tOffLo
    · simpa only [reductionInitial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega)
    · rw [hfirstReductionWrite]
      exact hbelow
    · exact hreductionWrites
  have hreductionInitialFrame : memoryWordsFrom reductionInitial.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
    change memoryWordsFrom
        (ciosBoundaryMem2 multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry tk1Off) ptr count = _
    rw [hboundary2, hboundary1, hmultiplyFrame]
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hshift := ciosShiftCoverage_of_layout columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout
  have hshiftedWrite : shiftedOut.toNat + 32 ≤ reductionFinal.memory.size := by
    rw [show reductionFinal.memory.size = state.memory.size by
      simpa only [reductionFinal] using hfinal.2.2]
    have hfrontier := layout.scratchFrontier
    have hshifted := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have hshift1 : memoryWordsFrom shiftMem1 ptr count =
      memoryWordsFrom reductionFinal.memory ptr count := by
    simpa only [shiftMem1, ciosShiftMem1] using
      memoryWordsFrom_write_above
        (ciosShiftSum reductionFinal.memory reductionFinal.activeWords reductionFinal.carry
          tEnd).toByteArray reductionFinal.memory shiftedOut.toNat ptr count
        (by rw [toByteArray_size]) (by omega)
        (by
          have hmultiply := layout.multiplyStop
          have hshifted := layout.shiftedOutEq
          have hcolumns := layout.columnsGtOne
          omega)
  have htEndShiftWrite : tEnd.toNat + 32 ≤ shiftMem1.size := by
    rw [show shiftMem1.size = reductionFinal.memory.size by
      simpa only [reductionFinal, shiftMem1] using hshift.mem1Size]
    rw [show reductionFinal.memory.size = state.memory.size by
      simpa only [reductionFinal] using hfinal.2.2]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hshift2 : memoryWordsFrom shiftMem2 ptr count =
      memoryWordsFrom shiftMem1 ptr count := by
    simpa only [shiftMem1, shiftMem2, ciosShiftMem2] using
      memoryWordsFrom_write_above
        (ciosShiftTk1 reductionFinal.memory reductionFinal.activeWords reductionFinal.carry
            shiftedOut tk1Off tEnd +
          ciosShiftOverflow reductionFinal.memory reductionFinal.activeWords
            reductionFinal.carry tEnd).toByteArray
        shiftMem1 tEnd.toNat ptr count (by rw [toByteArray_size]) (by omega)
        (by
          have hstop := layout.multiplyStop
          omega)
  have htk1ShiftWrite : tk1Off.toNat + 32 ≤ shiftMem2.size := by
    rw [show shiftMem2.size = reductionFinal.memory.size by
      simpa only [reductionFinal, shiftMem2] using hshift.mem2Size]
    rw [show reductionFinal.memory.size = state.memory.size by
      simpa only [reductionFinal] using hfinal.2.2]
    exact layout.scratchFrontier
  have hshift3 : memoryWordsFrom finalMem ptr count =
      memoryWordsFrom shiftMem2 ptr count := by
    simpa only [finalMem, shiftMem2, ciosShiftMemory] using
      memoryWordsFrom_write_above (⟨0⟩ : UInt256).toByteArray shiftMem2 tk1Off.toNat
        ptr count (by rw [toByteArray_size]) (by omega)
        (by
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega)
  change memoryWordsFrom finalMem ptr count = _
  rw [hshift3, hshift2, hshift1, hreductionFrame, hreductionInitialFrame]

/-- The multiply pass and its two boundary stores preserve all complete ranges ending at `tP`. -/
theorem ciosReductionInitial_memoryWords_below
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) (ptr count : Nat)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hbelow : ptr + 32 * count ≤ tP.toNat) :
    memoryWordsFrom
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  have hmultiplyEq : multiplyFinal =
      multiplyPassIterate ai columns multiplyInitial := by
    simpa only [ai, multiplyInitial, multiplyFinal] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have h := layout.columnsGtOne
        omega)
  have hmultiplyFrame : memoryWordsFrom multiplyFinal.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
    rw [hmultiplyEq]
    have h := multiplyPassIterate_memoryWords_below ai columns multiplyInitial ptr count
      (by
        simpa only [multiplyInitial, ciosMultiplyInitial] using
          (show tP.toNat + 32 * columns < UInt256.size by
            have hfit := layout.scratchFit
            have hstop := layout.multiplyStop
            have htk1 := layout.tk1OffEq
            omega))
      (by simpa only [multiplyInitial, ciosMultiplyInitial] using hbelow)
      facts.writes
    simpa only [multiplyInitial, ciosMultiplyInitial] using h
  have htEndWrite : tEnd.toNat + 32 ≤ multiplyFinal.memory.size := by
    rw [facts.finalSize]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hboundary1 :
      memoryWordsFrom
          (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry) ptr count =
        memoryWordsFrom multiplyFinal.memory ptr count := by
    simpa only [ciosBoundaryMem1] using
      memoryWordsFrom_write_above
        (ciosBoundaryTkNew multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry).toByteArray multiplyFinal.memory tEnd.toNat ptr count
        (by rw [toByteArray_size]) (by omega)
        (by
          have hstop := layout.multiplyStop
          omega)
  have htk1Write : tk1Off.toNat + 32 ≤
      (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry).size := by
    rw [facts.boundary.mem1Size, facts.finalSize]
    exact layout.scratchFrontier
  have hboundary2 :
      memoryWordsFrom
          (ciosBoundaryMem2 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry tk1Off) ptr count =
        memoryWordsFrom
          (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry) ptr count := by
    simpa only [ciosBoundaryMem2] using
      memoryWordsFrom_write_above
        (ciosBoundaryTk1 multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry tk1Off +
          ciosBoundaryOverflow multiplyFinal.memory multiplyFinal.activeWords tEnd
            multiplyFinal.carry).toByteArray
        (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry) tk1Off.toNat ptr count
        (by rw [toByteArray_size]) (by omega)
        (by
          have hstop := layout.multiplyStop
          have htk1 := layout.tk1OffEq
          omega)
  change memoryWordsFrom
      (ciosBoundaryMem2 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry tk1Off) ptr count = _
  rw [hboundary2, hboundary1, hmultiplyFrame]

/-- The low modulus word read by the generated boundary is the original word at `nP`. -/
theorem ciosBoundaryN0_eq_initialMemoryWord
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hn0End : nP.toNat + 32 ≤ tP.toNat) :
    (ciosBoundaryN0
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat := by
  let final := ciosMultiplyFinal columns bP tP state
  let mem2 := ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off
  let aw4 := ciosBoundaryAw4 final.activeWords tEnd tk1Off
  let aw5 := ciosBoundaryAw5 final.activeWords tEnd tk1Off tP
  have facts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout
  have htPFit : tP.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hreadT0 := readWords1_coverage mem2 aw4 tP
    (by simpa only [final, mem2, aw4] using facts.boundary.aw4Covered)
    (by simpa only [final, aw4] using facts.boundary.aw4Fit) htPFit
  have hmem2Size : mem2.size = state.memory.size := by
    rw [show mem2.size = final.memory.size by
      simpa only [final, mem2] using facts.boundary.mem2Size]
    simpa only [final] using facts.finalSize
  have hnWord : nP.toNat + 32 ≤ mem2.size := by
    rw [hmem2Size]
    have hfrontier := layout.scratchFrontier
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hload := readWord_toNat_of_covered mem2 aw5 nP
    (by simpa only [aw5, ciosBoundaryAw5, aw4] using hreadT0.1)
    (by simpa only [aw5, ciosBoundaryAw5, aw4] using hreadT0.2) hnWord
  have hframe := ciosReductionInitial_memoryWords_below columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state nP.toNat 1 layout (by simpa using hn0End)
  have hwordFrame : Modexp.MultiLimbMemoryModel.memoryWordNat mem2 nP.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat := by
    apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
    simpa only [mem2, final, ciosReductionInitial] using hframe
  change (readWord mem2 aw5 nP).toNat = _
  rw [hload, hwordFrame]

/-- The non-peeled reduction collector is the original modulus tail. -/
theorem ciosReductionOperandWords_eq_initialMemory
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hHigherPtr : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nP.toNat + 32 * columns ≤ tP.toNat) :
    schoolbookOperandWords
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 1)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state) =
      memoryWordsFrom state.memory (nP.toNat + 32) (columns - 1) := by
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have multiplyFacts := ciosMultiplyLinkFacts_of_layout columns bP tP tEnd tk1Off nP
    tOff nBefore shiftedOut state layout
  have hinitialCoverage : MemoryCovered initial.memory initial.activeWords ∧
      initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosAfterBoundaryAw] using
      And.intro multiplyFacts.boundary.finalCovered multiplyFacts.boundary.finalFit
  have hinitialSize : initial.memory.size = state.memory.size := by
    dsimp only [initial, ciosReductionInitial, ciosAfterBoundaryMemory]
    rw [multiplyFacts.boundary.mem2Size, multiplyFacts.finalSize]
  have writesToEnd := ciosReduction_writesToEnd_of_layout columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout
  have hsteps : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := schoolbookIterate_operandPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by
          have h := layout.reductionOperandFit
          omega))
    have hresult := schoolbookIterate_resultPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    have hlo : 32 ≤ (schoolbookIterate factor j initial).resultPtr.toNat := by
      rw [hresult]
      dsimp only [initial, ciosReductionInitial]
      have h := layout.tOffLo
      omega
    refine ⟨?_, ?_, ?_, (writesToEnd j hj).inBounds⟩
    · rw [hop]
      dsimp only [initial, ciosReductionInitial]
      have h := layout.reductionOperandFit
      omega
    · rw [hresult]
      dsimp only [initial, ciosReductionInitial]
      have hfit := layout.scratchFit
      have hstop := layout.reductionStop
      have htk1 := layout.tk1OffEq
      omega
    · rw [schoolbookWritePtr_toNat _ hlo, hresult]
      dsimp only [initial, ciosReductionInitial]
      have hfit := layout.scratchFit
      have hstop := layout.reductionStop
      have htk1 := layout.tk1OffEq
      omega
  have hloads : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.operandPtr.toNat := by
    intro j hj
    let current := schoolbookIterate factor j initial
    have hcurrent := schoolbookIterate_coverage factor j initial hinitialCoverage.1
      hinitialCoverage.2 (fun i hi => hsteps i (by omega))
    have hop := schoolbookIterate_operandPtr_toNat factor j initial (by
      simpa only [initial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by
          have h := layout.reductionOperandFit
          omega))
    have hiterateSize := (schoolbookIterate_inBounds factor j initial
      (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
      (by
        simpa only [initial, ciosReductionInitial] using
          (show tOff.toNat + 32 * j < UInt256.size by
            have hstop := layout.reductionStop
            have hfit := layout.scratchFit
            have htk1 := layout.tk1OffEq
            omega))
      (by
        simpa only [initial, ciosReductionInitial] using
          (show tOff.toNat + 32 * j ≤ initial.memory.size by
            rw [hinitialSize]
            have hfrontier := layout.scratchFrontier
            have hstop := layout.reductionStop
            have htk1 := layout.tk1OffEq
            omega))).2
    have hword : current.operandPtr.toNat + 32 ≤ current.memory.size := by
      rw [show current.memory.size = initial.memory.size by
        simpa only [current] using hiterateSize]
      rw [hinitialSize]
      rw [show current.operandPtr.toNat = (nBefore + ⟨64⟩).toNat + 32 * j by
        simpa only [current, initial, ciosReductionInitial] using hop]
      rw [hHigherPtr]
      have hjEnd : nP.toNat + 32 + 32 * j + 32 ≤
          nP.toNat + 32 * columns := by omega
      have htPMemory : tP.toNat ≤ state.memory.size := by
        have hfrontier := layout.scratchFrontier
        have hstop := layout.multiplyStop
        have htk1 := layout.tk1OffEq
        omega
      exact hjEnd.trans (hnEnd.trans htPMemory)
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.operandPtr (by simpa only [current] using hcurrent.1)
      (by simpa only [current] using hcurrent.2) hword
    simpa only [current, schoolbookOperands] using hload
  have hfirstWrite : (schoolbookWritePtr initial.resultPtr).toNat = tP.toNat := by
    rw [schoolbookWritePtr_toNat initial.resultPtr (by
      simpa only [initial, ciosReductionInitial] using layout.tOffLo)]
    change tOff.toNat - 32 = tP.toNat
    have hreduce := layout.reductionStop
    have hmultiply := layout.multiplyStop
    have hcolumns : columns - 1 + 1 = columns := by
      have h := layout.columnsGtOne
      omega
    have hmul : 32 * columns = 32 * (columns - 1) + 32 := by
      conv_lhs => rw [← hcolumns]
      simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hcollector := schoolbookOperandWords_eq_initialMemory factor (columns - 1)
    initial
    (by
      simpa only [initial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) < UInt256.size by
          have h := layout.reductionOperandFit
          omega))
    (by
      simpa only [initial, ciosReductionInitial] using
        (show tOff.toNat + 32 * (columns - 1) < UInt256.size by
          have hstop := layout.reductionStop
          have hfit := layout.scratchFit
          have htk1 := layout.tk1OffEq
          omega))
    (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    (by
      rw [hfirstWrite]
      rw [show initial.operandPtr.toNat = nP.toNat + 32 by
        simpa only [initial, ciosReductionInitial] using hHigherPtr]
      have hcolumns : columns - 1 + 1 = columns := by
        have h := layout.columnsGtOne
        omega
      have hmul : 32 * columns = 32 + 32 * (columns - 1) := by
        conv_lhs => rw [← hcolumns]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      omega)
    hloads (fun j hj => (writesToEnd j hj).inBounds)
  have hframe := ciosReductionInitial_memoryWords_below columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state (nP.toNat + 32) (columns - 1)
    layout (by
      have hcolumns : columns - 1 + 1 = columns := by
        have h := layout.columnsGtOne
        omega
      have hmul : 32 * columns = 32 + 32 * (columns - 1) := by
        conv_lhs => rw [← hcolumns]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      omega)
  rw [show initial.operandPtr.toNat = nP.toNat + 32 by
    simpa only [initial, ciosReductionInitial] using hHigherPtr] at hcollector
  rw [hcollector, hframe]

/-- The complete generated modulus collector is the original `columns`-word modulus array. -/
theorem ciosIterationModulus_eq_memoryWordsFrom
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hHigherPtr : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nP.toNat + 32 * columns ≤ tP.toNat) :
    ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore state =
      Modexp.wordLimbsToNat (memoryWordsFrom state.memory nP.toNat columns) := by
  have hn0 := ciosBoundaryN0_eq_initialMemoryWord columns bP tP tEnd tk1Off nP
    n0inv tOff nBefore shiftedOut state layout (by
      have hcolumns := layout.columnsGtOne
      have h : 32 ≤ 32 * columns := by omega
      omega)
  have htail := ciosReductionOperandWords_eq_initialMemory columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout hHigherPtr hnEnd
  have hcolumns : columns = (columns - 1) + 1 := by
    have h := layout.columnsGtOne
    omega
  simp only [ciosIterationModulus]
  rw [hn0, htail]
  have hmemory : memoryWordsFrom state.memory nP.toNat columns =
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat) ::
        memoryWordsFrom state.memory (nP.toNat + 32) (columns - 1) := by
    rw [hcolumns]
    rfl
  rw [hmemory]
  simp only [Modexp.wordLimbsToNat]
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size state.memory nP.toNat)]

/-- Pre-scratch memory ranges remain unchanged after any number of CIOS outer iterations. -/
theorem ciosOuterIterate_memoryWords_below
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) (ptr count : Nat)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size)
    (hbelow : ptr + 32 * count ≤ tP.toNat) :
    memoryWordsFrom
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      have hcurrentLayout :=
        (ciosOuterIterate_layout iterations columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut state layout
          (fun i hi => haFit i (by omega))).1
      have hstep := ciosOuterAdvance_memoryWords_below columns bP tP tEnd tk1Off
        nP n0inv tOff nBefore shiftedOut current ptr count hcurrentLayout hbelow
      have hprevious := ih (fun i hi => haFit i (by omega))
      simpa only [ciosOuterIterate, current] using hstep.trans hprevious

/-- The multiplier collector has one fixed value throughout the outer scan. -/
theorem ciosOuterIterate_multiplier_eq_initial
    (i iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ j, j ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut j state).aOff.toNat + 32 + 31 < UInt256.size)
    (hi : i ≤ iterations)
    (hbEnd : bP.toNat + 32 * columns ≤ tP.toNat) :
    let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut i state
    ciosIterationMultiplier columns bP tP current =
      Modexp.wordLimbsToNat (memoryWordsFrom state.memory bP.toNat columns) := by
  let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut i state
  have hcurrentLayout :=
    (ciosOuterIterate_layout i columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state layout (fun j hj => haFit j (by omega))).1
  have hcurrent := ciosIterationMultiplier_eq_memoryWordsFrom columns bP tP tEnd
    tk1Off nP tOff nBefore shiftedOut current hcurrentLayout hbEnd
  have hmemory := ciosOuterIterate_memoryWords_below i columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state bP.toNat columns layout
    (fun j hj => haFit j (by omega)) hbEnd
  change ciosIterationMultiplier columns bP tP current = _
  rw [hcurrent, hmemory]

/-- The modulus collector has one fixed value throughout the outer scan. -/
theorem ciosOuterIterate_modulus_eq_initial
    (i iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ j, j ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut j state).aOff.toNat + 32 + 31 < UInt256.size)
    (hi : i ≤ iterations)
    (hHigherPtr : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nP.toNat + 32 * columns ≤ tP.toNat) :
    let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut i state
    ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore current =
      Modexp.wordLimbsToNat (memoryWordsFrom state.memory nP.toNat columns) := by
  let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut i state
  have hcurrentLayout :=
    (ciosOuterIterate_layout i columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state layout (fun j hj => haFit j (by omega))).1
  have hcurrent := ciosIterationModulus_eq_memoryWordsFrom columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut current hcurrentLayout hHigherPtr hnEnd
  have hmemory := ciosOuterIterate_memoryWords_below i columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state nP.toNat columns layout
    (fun j hj => haFit j (by omega)) hnEnd
  change ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore
    current = _
  rw [hcurrent, hmemory]

/-- A valid initial low-limb negative inverse remains the inverse used at every iteration. -/
theorem ciosOuterIterate_inverse
    (i iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ j, j ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut j state).aOff.toNat + 32 + 31 < UInt256.size)
    (hi : i ≤ iterations)
    (hn0End : nP.toNat + 32 ≤ tP.toNat)
    (hinv : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat *
      n0inv.toNat % UInt256.size = UInt256.size - 1) :
    let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut i state
    (ciosBoundaryN0
      (ciosMultiplyFinal columns bP tP current).memory
      (ciosMultiplyFinal columns bP tP current).activeWords tEnd
      (ciosMultiplyFinal columns bP tP current).carry tk1Off tP nP).toNat *
        n0inv.toNat % UInt256.size = UInt256.size - 1 := by
  let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut i state
  have hcurrentLayout :=
    (ciosOuterIterate_layout i columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state layout (fun j hj => haFit j (by omega))).1
  have hn0 := ciosBoundaryN0_eq_initialMemoryWord columns bP tP tEnd tk1Off nP
    n0inv tOff nBefore shiftedOut current hcurrentLayout hn0End
  have hmemoryWords := ciosOuterIterate_memoryWords_below i columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state nP.toNat 1 layout
    (fun j hj => haFit j (by omega)) (by simpa using hn0End)
  have hmemory : Modexp.MultiLimbMemoryModel.memoryWordNat current.memory nP.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat := by
    apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
    simpa only [current] using hmemoryWords
  change (ciosBoundaryN0
      (ciosMultiplyFinal columns bP tP current).memory
      (ciosMultiplyFinal columns bP tP current).activeWords tEnd
      (ciosMultiplyFinal columns bP tP current).carry tk1Off tP nP).toNat *
        n0inv.toNat % UInt256.size = UInt256.size - 1
  rw [hn0, hmemory]
  exact hinv

/-- Loop-wide CIOS semantics with all static collector and inverse hypotheses discharged by
allocation ordering. -/
theorem ciosOuterIterate_eq_montgomeryCIOSScan_of_staticOperands
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0)
    (hbEnd : bP.toNat + 32 * columns ≤ tP.toNat)
    (hHigherPtr : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nP.toNat + 32 * columns ≤ tP.toNat)
    (hinv : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat *
      n0inv.toNat % UInt256.size = UInt256.size - 1) :
    ciosScratchValue columns tP tEnd tk1Off
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state) =
      Modexp.montgomeryCIOSScan UInt256.size
        (Modexp.wordLimbsToNat (memoryWordsFrom state.memory nP.toNat columns))
        n0inv.toNat
        (Modexp.wordLimbsToNat (memoryWordsFrom state.memory bP.toNat columns))
        (ciosScratchValue columns tP tEnd tk1Off state)
        (ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state) := by
  apply ciosOuterIterate_eq_montgomeryCIOSScan iterations columns
    (Modexp.wordLimbsToNat (memoryWordsFrom state.memory nP.toNat columns))
    (Modexp.wordLimbsToNat (memoryWordsFrom state.memory bP.toNat columns))
    bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut state layout haFit hextra
  · intro i hi
    exact ciosOuterIterate_modulus_eq_initial i iterations columns bP tP tEnd tk1Off
      nP n0inv tOff nBefore shiftedOut state layout haFit (by omega) hHigherPtr hnEnd
  · intro i hi
    exact ciosOuterIterate_multiplier_eq_initial i iterations columns bP tP tEnd tk1Off
      nP n0inv tOff nBefore shiftedOut state layout haFit (by omega) hbEnd
  · intro i hi
    exact ciosOuterIterate_inverse i iterations columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state layout haFit (by omega)
      (by
        have hcolumns := layout.columnsGtOne
        have h : 32 ≤ 32 * columns := by omega
        omega)
      hinv

/-- The generated source pointer advances by exactly one word per outer iteration. -/
theorem ciosOuterIterate_aOff_toNat
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (haFit : ∀ i, i < iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 < UInt256.size) :
    (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut iterations state).aOff.toNat = state.aOff.toNat + 32 * iterations := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      change (current.aOff + ⟨32⟩).toNat = state.aOff.toNat + 32 * (iterations + 1)
      rw [uadd_word_lit32_toNat current.aOff (by
        simpa only [current] using haFit iterations (by omega))]
      rw [show current.aOff.toNat = state.aOff.toNat + 32 * iterations by
        simpa only [current] using ih (fun i hi => haFit i (by omega))]
      omega

/-- Each generated outer source load is the corresponding word of the initial source array. -/
theorem ciosOuterDigit_eq_initialMemoryWord
    (i iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ j, j ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut j state).aOff.toNat + 32 + 31 < UInt256.size)
    (hi : i < iterations)
    (haEnd : state.aOff.toNat + 32 * iterations ≤ tP.toNat) :
    let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut i state
    (ciosOuterAi current.memory current.activeWords current.aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
        (state.aOff.toNat + 32 * i) := by
  let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut i state
  have hcurrentLayout :=
    (ciosOuterIterate_layout i columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state layout (fun j hj => haFit j (by omega))).1
  have haOff := ciosOuterIterate_aOff_toNat i columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state (fun j hj => by
      have h := haFit j (by omega)
      omega)
  have hcurrentEnd : current.aOff.toNat + 32 ≤ tP.toNat := by
    rw [show current.aOff.toNat = state.aOff.toNat + 32 * i by
      simpa only [current] using haOff]
    omega
  have hword : current.aOff.toNat + 32 ≤ current.memory.size := by
    have htPMemory : tP.toNat ≤ current.memory.size := by
      have htPFrontier : tP.toNat ≤ tk1Off.toNat + 32 := by
        have hstop := layout.multiplyStop
        have htk1 := layout.tk1OffEq
        omega
      exact htPFrontier.trans hcurrentLayout.scratchFrontier
    exact hcurrentEnd.trans htPMemory
  have hload := readWord_toNat_of_covered current.memory current.activeWords
    current.aOff hcurrentLayout.covered hcurrentLayout.activeFit hword
  have hmemoryWords := ciosOuterIterate_memoryWords_below i columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state current.aOff.toNat 1 layout
    (fun j hj => haFit j (by omega)) (by simpa using hcurrentEnd)
  have hmemory : Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
      current.aOff.toNat = Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
        current.aOff.toNat := by
    apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
    simpa only [current] using hmemoryWords
  change (readWord current.memory current.activeWords current.aOff).toNat = _
  rw [hload, hmemory]
  rw [show current.aOff.toNat = state.aOff.toNat + 32 * i by
    simpa only [current] using haOff]

/-- The complete generated source-digit list is the initial consecutive source memory range. -/
theorem ciosOuterDigits_eq_initialMemoryWords
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size)
    (haEnd : state.aOff.toNat + 32 * iterations ≤ tP.toNat) :
    ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
        iterations state =
      (memoryWordsFrom state.memory state.aOff.toNat iterations).map UInt256.toNat := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      have hprevious := ih (fun i hi => haFit i (by omega)) (by omega)
      have hdigit := ciosOuterDigit_eq_initialMemoryWord iterations (iterations + 1)
        columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut state layout
        haFit (by omega) haEnd
      have hsnoc := memoryWordsFrom_succ_eq_append state.memory state.aOff.toNat
        iterations
      have hlast :
          (UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              (state.aOff.toNat + 32 * iterations))).toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              (state.aOff.toNat + 32 * iterations) :=
        UInt256.toNat_ofNat_of_lt
          (memoryWordNat_lt_size state.memory (state.aOff.toNat + 32 * iterations))
      simp only [ciosOuterDigits]
      change ciosOuterDigits columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state ++
          [(ciosOuterAi current.memory current.activeWords current.aOff).toNat] = _
      rw [hprevious, hsnoc, List.map_append, List.map_singleton]
      rw [hlast]
      rw [show (ciosOuterAi current.memory current.activeWords current.aOff).toNat =
          Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
            (state.aOff.toNat + 32 * iterations) by
        simpa only [current] using hdigit]

/-- Fully memory-based CIOS scan semantics: source, multiplier, and modulus are all the original
allocated word arrays. -/
theorem ciosOuterIterate_eq_montgomeryCIOSScan_of_memoryOperands
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size)
    (hextra : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory tk1Off.toNat = 0)
    (haEnd : state.aOff.toNat + 32 * iterations ≤ tP.toNat)
    (hbEnd : bP.toNat + 32 * columns ≤ tP.toNat)
    (hHigherPtr : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nP.toNat + 32 * columns ≤ tP.toNat)
    (hinv : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat *
      n0inv.toNat % UInt256.size = UInt256.size - 1) :
    ciosScratchValue columns tP tEnd tk1Off
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state) =
      Modexp.montgomeryCIOSScan UInt256.size
        (Modexp.wordLimbsToNat (memoryWordsFrom state.memory nP.toNat columns))
        n0inv.toNat
        (Modexp.wordLimbsToNat (memoryWordsFrom state.memory bP.toNat columns))
        (ciosScratchValue columns tP tEnd tk1Off state)
        ((memoryWordsFrom state.memory state.aOff.toNat iterations).map UInt256.toNat) := by
  have hscan := ciosOuterIterate_eq_montgomeryCIOSScan_of_staticOperands iterations
    columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut state layout haFit
    hextra hbEnd hHigherPtr hnEnd hinv
  rw [ciosOuterDigits_eq_initialMemoryWords iterations columns bP tP tEnd tk1Off nP
    n0inv tOff nBefore shiftedOut state layout haFit haEnd] at hscan
  exact hscan

end Modexp.MultiLimbMontgomeryCIOSSemantic
