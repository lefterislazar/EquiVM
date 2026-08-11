import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSLayoutLinks

/-! # Sequential output-memory links for CIOS reduction -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- One generated schoolbook store preserves a complete word below its destination. -/
theorem schoolbookStore_read_below
    (mem : ByteArray) (aw operandPtr resultPtr a carry : UInt256) (read : Nat)
    (hwrite : (schoolbookWritePtr resultPtr).toNat + 32 ≤ mem.size)
    (hbelow : read + 32 ≤ (schoolbookWritePtr resultPtr).toNat) :
    ((schoolbookStep mem aw operandPtr resultPtr a carry).1.toByteArray.write 0 mem
        (schoolbookWritePtr resultPtr).toNat 32).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  apply write32_read_below
  · have hsize := toByteArray_size
      (schoolbookStep mem aw operandPtr resultPtr a carry).1
    omega
  · omega
  · exact hbelow

/-- Schoolbook writes at later destinations preserve an earlier complete output word. -/
theorem schoolbookIterate_read_below
    (a : UInt256) (n : Nat) (state : SchoolbookState) (read : Nat)
    (hwrites : ∀ j, j < n →
      (schoolbookWritePtr (schoolbookIterate a j state).resultPtr).toNat + 32 ≤
          (schoolbookIterate a j state).memory.size ∧
        read + 32 ≤
          (schoolbookWritePtr (schoolbookIterate a j state).resultPtr).toNat) :
    (schoolbookIterate a n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hfirst :
          (schoolbookWritePtr state.resultPtr).toNat + 32 ≤ state.memory.size ∧
            read + 32 ≤ (schoolbookWritePtr state.resultPtr).toNat := by
        simpa only [schoolbookIterate] using hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          (schoolbookWritePtr (schoolbookIterate a j next).resultPtr).toNat + 32 ≤
              (schoolbookIterate a j next).memory.size ∧
            read + 32 ≤
              (schoolbookWritePtr (schoolbookIterate a j next).resultPtr).toNat := by
        intro j hj
        simpa only [next, schoolbookIterate_advance] using
          hwrites (j + 1) (by omega)
      have hrest := ih next htail
      rw [schoolbookIterate, hrest]
      exact schoolbookStore_read_below state.memory state.activeWords state.operandPtr
        state.resultPtr a state.carry read hfirst.1 hfirst.2

set_option maxRecDepth 1000 in
/-- The output collector is the final memory range written by a sequential schoolbook pass. -/
theorem schoolbookOutputWords_eq_finalMemoryWords
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hresultLo : 32 ≤ state.resultPtr.toNat)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := schoolbookIterate a j state
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size) :
    schoolbookOutputWords a n state =
      memoryWordsFrom (schoolbookIterate a n state).memory
        (schoolbookWritePtr state.resultPtr).toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hresultAdd : (state.resultPtr + ⟨32⟩).toNat = state.resultPtr.toNat + 32 :=
        uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextResult : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        simpa only [next, schoolbookAdvance] using hresultAdd
      have hnextLo : 32 ≤ next.resultPtr.toNat := by omega
      have hnextFit : next.resultPtr.toNat + 32 * n < UInt256.size := by
        rw [hnextResult]
        omega
      have hnextWrites : ∀ j, j < n →
          let current := schoolbookIterate a j next
          (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, schoolbookIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next hnextLo hnextFit hnextWrites
      have hdest := schoolbookWritePtr_toNat state.resultPtr hresultLo
      have hnextDest := schoolbookWritePtr_toNat next.resultPtr hnextLo
      have hdestStep : (schoolbookWritePtr next.resultPtr).toNat =
          (schoolbookWritePtr state.resultPtr).toNat + 32 := by
        rw [hnextDest, hnextResult, hdest]
        omega
      have hfirstWrite : (schoolbookWritePtr state.resultPtr).toNat + 32 ≤
          state.memory.size := by
        simpa only [schoolbookIterate] using hwrites 0 (by omega)
      have hgap : (schoolbookWritePtr state.resultPtr).toNat - state.memory.size <
          USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        exact lt_usize 0 (by norm_num)
      have htailFrame :
          (schoolbookIterate a n next).memory.readWithPadding
              (schoolbookWritePtr state.resultPtr).toNat 32 =
            next.memory.readWithPadding (schoolbookWritePtr state.resultPtr).toNat 32 := by
        apply schoolbookIterate_read_below a n next
        intro j hj
        have hwrite := hnextWrites j hj
        have hresult := schoolbookIterate_resultPtr_toNat a j next (by
          simpa only [next] using
            (show next.resultPtr.toNat + 32 * j < UInt256.size by omega))
        have hlo : 32 ≤ (schoolbookIterate a j next).resultPtr.toNat := by
          rw [hresult]
          omega
        constructor
        · exact hwrite
        · rw [schoolbookWritePtr_toNat _ hlo, hresult, hnextResult, hdest]
          omega
      have hheadMemory :
          Modexp.MultiLimbMemoryModel.memoryWordNat
              (schoolbookIterate a n next).memory
              (schoolbookWritePtr state.resultPtr).toNat =
            (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
              a state.carry).1.toNat := by
        have hframeNat :
            Modexp.MultiLimbMemoryModel.memoryWordNat
                (schoolbookIterate a n next).memory
                (schoolbookWritePtr state.resultPtr).toNat =
              Modexp.MultiLimbMemoryModel.memoryWordNat next.memory
                (schoolbookWritePtr state.resultPtr).toNat := by
          unfold Modexp.MultiLimbMemoryModel.memoryWordNat
          rw [htailFrame]
        rw [hframeNat]
        simpa only [next, schoolbookAdvance] using
          schoolbookMemory_word state.memory state.activeWords state.operandPtr
            state.resultPtr a state.carry hgap
      simp only [schoolbookOutputWords, schoolbookIterate, memoryWordsFrom]
      have hheadWord : UInt256.ofNat
          (Modexp.MultiLimbMemoryModel.memoryWordNat
            (schoolbookIterate a n next).memory
            (schoolbookWritePtr state.resultPtr).toNat) =
          (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
            a state.carry).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hheadMemory]
      have htail' : schoolbookOutputWords a n next =
          memoryWordsFrom (schoolbookIterate a n next).memory
            ((schoolbookWritePtr state.resultPtr).toNat + 32) n := by
        rw [← hdestStep]
        simpa only [next] using htail
      rw [hheadWord, htail']

/-- The generated reduction collector is exactly the low scratch range it leaves in memory. -/
theorem ciosReductionOutputWords_eq_finalMemoryWords
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    schoolbookOutputWords
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 1)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state) =
      memoryWordsFrom
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state).memory tP.toNat (columns - 1) := by
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hfit : initial.resultPtr.toNat + 32 * (columns - 1) < UInt256.size := by
    dsimp only [initial, ciosReductionInitial]
    have hstop := layout.reductionStop
    have hscratch := layout.scratchFit
    have htk1 := layout.tk1OffEq
    omega
  have hwrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j initial
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
    intro j hj
    exact (ciosReduction_writesToEnd_of_layout columns bP tP tEnd tk1Off nP
      n0inv tOff nBefore shiftedOut state layout j hj).inBounds
  have hraw := schoolbookOutputWords_eq_finalMemoryWords factor (columns - 1)
    initial (by simpa only [initial, ciosReductionInitial] using layout.tOffLo)
    hfit hwrites
  have hfinal :
      ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state =
        schoolbookIterate factor (columns - 1) initial := by
    simpa only [factor, initial] using
      ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore state layout.columnsGtOne
  have hdest : (schoolbookWritePtr initial.resultPtr).toNat = tP.toNat := by
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
  rw [← hfinal, hdest] at hraw
  simpa only [factor, initial] using hraw

/-- Extending a consecutive memory range appends the next word at its high end. -/
theorem memoryWordsFrom_succ_eq_append
    (mem : ByteArray) (ptr n : Nat) :
    memoryWordsFrom mem ptr (n + 1) =
      memoryWordsFrom mem ptr n ++
        [UInt256.ofNat
          (Modexp.MultiLimbMemoryModel.memoryWordNat mem (ptr + 32 * n))] := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih =>
      change UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr) ::
          memoryWordsFrom mem (ptr + 32) (n + 1) =
        UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr) ::
          (memoryWordsFrom mem (ptr + 32) n ++
            [UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
              (ptr + 32 * (n + 1)))])
      rw [ih (ptr := ptr + 32)]
      congr 3
      simp only [Nat.mul_add, Nat.mul_one]
      rw [show ptr + 32 + 32 * n = ptr + (32 * n + 32) by omega]

/-- A complete word below an in-bounds 32-byte store keeps its natural-number value. -/
theorem memoryWordNat_write_above
    (src base : ByteArray) (dest ptr : Nat)
    (hsrc : 32 ≤ src.size) (hdest : dest + 32 ≤ base.size)
    (habove : ptr + 32 ≤ dest) :
    Modexp.MultiLimbMemoryModel.memoryWordNat (src.write 0 base dest 32) ptr =
      Modexp.MultiLimbMemoryModel.memoryWordNat base ptr := by
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [write32_read_below src base dest ptr hsrc (by omega) habove]

/-- Reading at an in-bounds EVM word store recovers the stored word exactly. -/
theorem memoryWordNat_store_eq
    (word : UInt256) (mem : ByteArray) (off : Nat)
    (hwrite : off + 32 ≤ mem.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (word.toByteArray.write 0 mem off 32) off = word.toNat := by
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap]
  · exact fromByteArrayBigEndian_toByteArray word
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)

/-- The three final-shift stores preserve every completed low reduction word. -/
theorem ciosOuterAdvance_lowWords_eq_reductionOutputs
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    memoryWordsFrom
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).memory tP.toNat (columns - 1) =
      schoolbookOutputWords
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 1)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state) := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let mem1 := ciosShiftMem1 final.memory final.activeWords final.carry shiftedOut tEnd
  let mem2 := ciosShiftMem2 final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd
  let finalMem := ciosShiftMemory final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hshift := ciosShiftCoverage_of_layout columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout
  have hlowEnd : tP.toNat + 32 * (columns - 1) = shiftedOut.toNat := by
    have hmultiply := layout.multiplyStop
    have hshifted := layout.shiftedOutEq
    have hcolumns : columns - 1 + 1 = columns := by
      have h := layout.columnsGtOne
      omega
    have hmul : 32 * columns = 32 * (columns - 1) + 32 := by
      conv_lhs => rw [← hcolumns]
      simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hshiftedWrite : shiftedOut.toNat + 32 ≤ final.memory.size := by
    rw [show final.memory.size = state.memory.size by
      simpa only [final] using hfinal.2.2]
    have hfrontier := layout.scratchFrontier
    have hshifted := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have htEndWrite : tEnd.toNat + 32 ≤ mem1.size := by
    rw [show mem1.size = final.memory.size by
      simpa only [final, mem1] using hshift.mem1Size]
    rw [show final.memory.size = state.memory.size by
      simpa only [final] using hfinal.2.2]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have htk1Write : tk1Off.toNat + 32 ≤ mem2.size := by
    rw [show mem2.size = final.memory.size by
      simpa only [final, mem2] using hshift.mem2Size]
    rw [show final.memory.size = state.memory.size by
      simpa only [final] using hfinal.2.2]
    exact layout.scratchFrontier
  have hframe1 : memoryWordsFrom mem1 tP.toNat (columns - 1) =
      memoryWordsFrom final.memory tP.toNat (columns - 1) := by
    simpa only [mem1, ciosShiftMem1] using
      memoryWordsFrom_write_above
        (ciosShiftSum final.memory final.activeWords final.carry tEnd).toByteArray
        final.memory shiftedOut.toNat tP.toNat (columns - 1)
        (by rw [toByteArray_size]) (by omega) (by omega)
  have hframe2 : memoryWordsFrom mem2 tP.toNat (columns - 1) =
      memoryWordsFrom mem1 tP.toNat (columns - 1) := by
    simpa only [mem1, mem2, ciosShiftMem2] using
      memoryWordsFrom_write_above
        (ciosShiftTk1 final.memory final.activeWords final.carry shiftedOut tk1Off tEnd +
          ciosShiftOverflow final.memory final.activeWords final.carry tEnd).toByteArray
        mem1 tEnd.toNat tP.toNat (columns - 1)
        (by rw [toByteArray_size]) (by omega)
        (by have h := layout.shiftedOutEq; omega)
  have hframe3 : memoryWordsFrom finalMem tP.toNat (columns - 1) =
      memoryWordsFrom mem2 tP.toNat (columns - 1) := by
    simpa only [finalMem, mem2, ciosShiftMemory] using
      memoryWordsFrom_write_above (⟨0⟩ : UInt256).toByteArray mem2 tk1Off.toNat
        tP.toNat (columns - 1) (by rw [toByteArray_size]) (by omega)
        (by
          have hshifted := layout.shiftedOutEq
          have htk1 := layout.tk1OffEq
          omega)
  have hout := ciosReductionOutputWords_eq_finalMemoryWords columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout
  change memoryWordsFrom finalMem tP.toNat (columns - 1) = _
  rw [hframe3, hframe2, hframe1, ← hout]

/-- Exact word values left by the three generated final-shift stores. -/
structure CIOSShiftStoredWords
    (mem : ByteArray) (aw reductionCarry shiftedOut tk1Off tEnd : UInt256) : Prop where
  shiftedOutWord :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd) shiftedOut.toNat =
      (ciosShiftSum mem aw reductionCarry tEnd).toNat
  endWord :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd) tEnd.toNat =
      (ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd +
        ciosShiftOverflow mem aw reductionCarry tEnd).toNat
  extraWord :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd) tk1Off.toNat = 0

/-- In-bounds, ordered final-shift stores have their expected exact memory contents. -/
theorem ciosShift_storedWords
    (mem : ByteArray) (aw reductionCarry shiftedOut tk1Off tEnd : UInt256)
    (coverage : CIOSShiftCoverageFacts mem aw reductionCarry shiftedOut tk1Off tEnd)
    (hshiftedWrite : shiftedOut.toNat + 32 ≤ mem.size)
    (htEndWrite : tEnd.toNat + 32 ≤ mem.size)
    (htk1Write : tk1Off.toNat + 32 ≤ mem.size)
    (hshiftedEnd : shiftedOut.toNat + 32 ≤ tEnd.toNat)
    (hEndTk1 : tEnd.toNat + 32 ≤ tk1Off.toNat) :
    CIOSShiftStoredWords mem aw reductionCarry shiftedOut tk1Off tEnd := by
  let sum := ciosShiftSum mem aw reductionCarry tEnd
  let upper := ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd +
    ciosShiftOverflow mem aw reductionCarry tEnd
  let mem1 := ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd
  let mem2 := ciosShiftMem2 mem aw reductionCarry shiftedOut tk1Off tEnd
  let finalMem := ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd
  have hstore1 : Modexp.MultiLimbMemoryModel.memoryWordNat mem1 shiftedOut.toNat =
      sum.toNat := by
    simpa only [sum, mem1, ciosShiftMem1] using
      memoryWordNat_store_eq sum mem shiftedOut.toNat hshiftedWrite
  have hframe2Shifted :
      Modexp.MultiLimbMemoryModel.memoryWordNat mem2 shiftedOut.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem1 shiftedOut.toNat := by
    simpa only [upper, mem1, mem2, ciosShiftMem2] using
      memoryWordNat_write_above upper.toByteArray mem1 tEnd.toNat shiftedOut.toNat
        (by rw [toByteArray_size])
        (by
          rw [show mem1.size = mem.size by simpa only [mem1] using coverage.mem1Size]
          exact htEndWrite)
        hshiftedEnd
  have hframe3Shifted :
      Modexp.MultiLimbMemoryModel.memoryWordNat finalMem shiftedOut.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem2 shiftedOut.toNat := by
    simpa only [finalMem, mem2, ciosShiftMemory] using
      memoryWordNat_write_above (⟨0⟩ : UInt256).toByteArray mem2 tk1Off.toNat
        shiftedOut.toNat (by rw [toByteArray_size])
        (by
          rw [show mem2.size = mem.size by simpa only [mem2] using coverage.mem2Size]
          exact htk1Write)
        (by omega)
  have hstore2 : Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tEnd.toNat =
      upper.toNat := by
    simpa only [upper, mem1, mem2, ciosShiftMem2] using
      memoryWordNat_store_eq upper mem1 tEnd.toNat (by
        rw [show mem1.size = mem.size by simpa only [mem1] using coverage.mem1Size]
        exact htEndWrite)
  have hframe3End : Modexp.MultiLimbMemoryModel.memoryWordNat finalMem tEnd.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tEnd.toNat := by
    simpa only [finalMem, mem2, ciosShiftMemory] using
      memoryWordNat_write_above (⟨0⟩ : UInt256).toByteArray mem2 tk1Off.toNat tEnd.toNat
        (by rw [toByteArray_size])
        (by
          rw [show mem2.size = mem.size by simpa only [mem2] using coverage.mem2Size]
          exact htk1Write)
        hEndTk1
  have hstore3 : Modexp.MultiLimbMemoryModel.memoryWordNat finalMem tk1Off.toNat = 0 := by
    have h := memoryWordNat_store_eq (⟨0⟩ : UInt256) mem2 tk1Off.toNat (by
      rw [show mem2.size = mem.size by simpa only [mem2] using coverage.mem2Size]
      exact htk1Write)
    simpa only [finalMem, mem2, ciosShiftMemory,
      show (⟨0⟩ : UInt256).toNat = 0 by decide] using h
  exact {
    shiftedOutWord := hframe3Shifted.trans (hframe2Shifted.trans hstore1)
    endWord := hframe3End.trans hstore2
    extraWord := hstore3 }

/-- The concrete CIOS layout discharges all final-shift store and ordering premises. -/
theorem ciosOuterAdvance_storedWords_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state
    CIOSShiftStoredWords final.memory final.activeWords final.carry shiftedOut
      tk1Off tEnd := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hfinal := ciosReductionFinal_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hcoverage := ciosShiftCoverage_of_layout columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout
  change CIOSShiftStoredWords final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd
  apply ciosShift_storedWords final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd hcoverage
  · rw [show final.memory.size = state.memory.size by
      simpa only [final] using hfinal.2.2]
    have hfrontier := layout.scratchFrontier
    have hshifted := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  · rw [show final.memory.size = state.memory.size by
      simpa only [final] using hfinal.2.2]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  · rw [show final.memory.size = state.memory.size by
      simpa only [final] using hfinal.2.2]
    exact layout.scratchFrontier
  · exact layout.shiftedOutEq.le
  · have h := layout.tk1OffEq
    omega

/-- All `columns` low scratch words after one iteration are the reduction outputs followed by
the generated shifted carry word. -/
theorem ciosOuterAdvance_words_eq_outputs_append
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    memoryWordsFrom
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).memory tP.toNat columns =
      schoolbookOutputWords
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
          (columns - 1)
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state) ++
        [ciosShiftSum
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state).memory
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state).activeWords
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state).carry tEnd] := by
  let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut state
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let sum := ciosShiftSum final.memory final.activeWords final.carry tEnd
  have hcolumns : columns - 1 + 1 = columns := by
    have h := layout.columnsGtOne
    omega
  have hlow := ciosOuterAdvance_lowWords_eq_reductionOutputs columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout
  have hstored := ciosOuterAdvance_storedWords_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hlowEnd : tP.toNat + 32 * (columns - 1) = shiftedOut.toNat := by
    have hmultiply := layout.multiplyStop
    have hshifted := layout.shiftedOutEq
    have hmul : 32 * columns = 32 * (columns - 1) + 32 := by
      conv_lhs => rw [← hcolumns]
      simp only [Nat.mul_add, Nat.mul_one]
    omega
  have hsumWord : UInt256.ofNat sum.toNat = sum := by
    apply u256_inj
    exact UInt256.toNat_ofNat_of_lt sum.val.isLt
  have hstored' : Modexp.MultiLimbMemoryModel.memoryWordNat next.memory
      shiftedOut.toNat = sum.toNat := by
    simpa only [next, final, sum, ciosOuterAdvance] using hstored.shiftedOutWord
  have hsnoc := memoryWordsFrom_succ_eq_append next.memory tP.toNat (columns - 1)
  rw [hcolumns] at hsnoc
  rw [hlowEnd, hstored'] at hsnoc
  rw [hsumWord] at hsnoc
  rw [hlow] at hsnoc
  simpa only [next, final, sum] using hsnoc

@[simp] theorem schoolbookOutputWords_length
    (a : UInt256) (n : Nat) (state : SchoolbookState) :
    (schoolbookOutputWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [schoolbookOutputWords, List.length_cons, ih]

/-- The arithmetic collector named `ciosIterationNext` is exactly the canonical scratch-memory
value produced by the generated outer transition. -/
theorem ciosIterationNext_eq_scratchValue_outerAdvance
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state =
      ciosScratchValue columns tP tEnd tk1Off
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state) := by
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reduction := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let outputs := schoolbookOutputWords factor (columns - 1) reduction
  let sum := ciosShiftSum final.memory final.activeWords final.carry tEnd
  let upper := ciosShiftTk1 final.memory final.activeWords final.carry shiftedOut
    tk1Off tEnd + ciosShiftOverflow final.memory final.activeWords final.carry tEnd
  have hwords := ciosOuterAdvance_words_eq_outputs_append columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hstored := ciosOuterAdvance_storedWords_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  have hend : Modexp.MultiLimbMemoryModel.memoryWordNat next.memory tEnd.toNat =
      upper.toNat := by
    simpa only [next, final, upper, ciosOuterAdvance] using hstored.endWord
  have hextra : Modexp.MultiLimbMemoryModel.memoryWordNat next.memory tk1Off.toNat = 0 := by
    simpa only [next, final, ciosOuterAdvance] using hstored.extraWord
  have hwords' : memoryWordsFrom next.memory tP.toNat columns = outputs ++ [sum] := by
    simpa only [next, final, factor, reduction, outputs, sum] using hwords
  have hvalue : Modexp.wordLimbsToNat (memoryWordsFrom next.memory tP.toNat columns) =
      Modexp.wordLimbsToNat outputs + UInt256.size ^ (columns - 1) * sum.toNat := by
    rw [hwords', Modexp.wordLimbsToNat_append]
    simp only [outputs, schoolbookOutputWords_length, Modexp.wordLimbsToNat,
      Nat.mul_zero, Nat.add_zero]
  unfold ciosIterationNext ciosScratchValue
  change Modexp.wordLimbsToNat outputs + UInt256.size ^ (columns - 1) * sum.toNat +
      UInt256.size ^ columns * upper.toNat =
    Modexp.wordLimbsToNat (memoryWordsFrom next.memory tP.toNat columns) +
      UInt256.size ^ columns *
        Modexp.MultiLimbMemoryModel.memoryWordNat next.memory tEnd.toNat +
      UInt256.size ^ (columns + 1) *
        Modexp.MultiLimbMemoryModel.memoryWordNat next.memory tk1Off.toNat
  rw [hvalue, hend, hextra, Nat.mul_zero, Nat.add_zero]

/-- One concrete outer transition updates the canonical scratch value by the pure CIOS step. -/
theorem ciosScratchValue_outerAdvance_eq_montgomeryCIOSStep
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
    ciosScratchValue columns tP tEnd tk1Off
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state) =
      Modexp.montgomeryCIOSStep UInt256.size
        (ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore state)
        n0inv.toNat (ciosIterationMultiplier columns bP tP state)
        (ciosScratchValue columns tP tEnd tk1Off state)
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat := by
  rw [← ciosIterationNext_eq_scratchValue_outerAdvance columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout]
  rw [ciosIterationNext_eq_montgomeryCIOSStep_of_extraWord_zero columns bP tP tEnd
    tk1Off nP n0inv tOff nBefore shiftedOut state layout hextra hinv]
  rw [ciosIterationPrior_eq_scratchValue columns bP tP tEnd tk1Off nP tOff
    nBefore shiftedOut state layout]

end Modexp.MultiLimbMontgomeryCIOSSemantic
