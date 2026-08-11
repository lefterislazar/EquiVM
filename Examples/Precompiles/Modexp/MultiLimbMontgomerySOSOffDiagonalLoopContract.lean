import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSOffDiagonalContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSLayout

/-! # SOS off-diagonal outer-loop semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sosOffDiagonalAt (radix offset : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => radix ^ offset * a * Modexp.limbsToNatAt radix as +
      sosOffDiagonalAt radix (offset + 2) as

/-- The offset-indexed row sum is the existing pure upper-triangle model shifted by the
corresponding radix power. -/
theorem sosOffDiagonalAt_eq_shift
    (radix offset : Nat) (limbs : List Nat) (hoffset : 0 < offset) :
    sosOffDiagonalAt radix offset limbs =
      radix ^ (offset - 1) * Modexp.sosOffDiagonal radix limbs := by
  induction limbs generalizing offset with
  | nil => simp [sosOffDiagonalAt, Modexp.sosOffDiagonal]
  | cons a as ih =>
      rw [sosOffDiagonalAt, Modexp.sosOffDiagonal, ih (offset + 2) (by omega)]
      have hpow1 : radix ^ offset = radix ^ (offset - 1) * radix := by
        rw [← pow_succ]
        congr 1
        omega
      have hpow2 : radix ^ (offset + 1) = radix ^ (offset - 1) * radix ^ 2 := by
        rw [show offset + 1 = (offset - 1) + 2 by omega, pow_add]
      rw [show offset + 2 - 1 = offset + 1 by omega, hpow1, hpow2]
      ring

theorem sosOffDiagonalAt_one (radix : Nat) (limbs : List Nat) :
    sosOffDiagonalAt radix 1 limbs = Modexp.sosOffDiagonal radix limbs := by
  simpa using sosOffDiagonalAt_eq_shift radix 1 limbs (by omega)

/-- Replacing a fixed-length middle limb window by a value larger by `delta` increases the whole
radix representation by exactly the correspondingly shifted `delta`. -/
theorem wordLimbsToNat_replace_middle
    (pre oldMiddle newMiddle suffix : List UInt256) (delta : Nat)
    (hlength : newMiddle.length = oldMiddle.length)
    (hvalue : Modexp.wordLimbsToNat newMiddle =
      Modexp.wordLimbsToNat oldMiddle + delta) :
    Modexp.wordLimbsToNat (pre ++ newMiddle ++ suffix) =
      Modexp.wordLimbsToNat (pre ++ oldMiddle ++ suffix) +
        UInt256.size ^ pre.length * delta := by
  simp only [Modexp.wordLimbsToNat_append, List.length_append]
  rw [hlength, hvalue]
  ring

/-- One selected upper-triangle row changes the complete scratch natural by exactly its shifted
schoolbook contribution.  The terminal destination is required to be fresh zero, as established
by scratch initialization and preserved by the preceding-row geometry. -/
theorem selectedSOSOffDiagonalRow_whole_value
    (offset products suffixWords : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {scratchBase : Nat}
    {selected : SOSOffDiagonalRowSelection}
    (hsRow : sRow.toNat = scratchBase + 32 * offset)
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (hafit : aOff.toNat + 32 * (products + 1) < UInt256.size)
    (hsfit : sRow.toNat + 32 * (products + 1) < UInt256.size)
    (hseparate : (aOff + ⟨32⟩).toNat + 32 * products ≤ sRow.toNat)
    (hloadsOperand : ∀ j, j < products →
      let current := sosOffDiagonalIterate (readWord mem aw aOff) j
        (sosOffDiagonalInitial mem aw sRow aOff)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat)
    (hloadsPrior : ∀ j, j < products →
      let current := sosOffDiagonalIterate (readWord mem aw aOff) j
        (sosOffDiagonalInitial mem aw sRow aOff)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < products →
      let current := sosOffDiagonalIterate (readWord mem aw aOff) j
        (sosOffDiagonalInitial mem aw sRow aOff)
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hboundary :
      let final := sosOffDiagonalIterate (readWord mem aw aOff) products
        (sosOffDiagonalInitial mem aw sRow aOff)
      final.resultPtr.toNat ≤ final.memory.size)
    (hterminalZero : Modexp.MultiLimbMemoryModel.memoryWordNat mem
      (sRow.toNat + 32 * products) = 0)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory scratchBase
          (offset + (products + 1) + suffixWords)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom mem scratchBase
            (offset + (products + 1) + suffixWords)) +
        UInt256.size ^ offset * (readWord mem aw aOff).toNat *
          Modexp.wordLimbsToNat
            (memoryWordsFrom mem (aOff + ⟨32⟩).toNat products) := by
  let a := readWord mem aw aOff
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let rowFinal := sosOffDiagonalIterate a products initial
  let finalMem := sosOffDiagonalBoundaryMemory rowFinal
  have hselectedMemory := selectedSOSOffDiagonalRow_finalMemory_eq products hend hafit hselect
  change selected.finalMemory = finalMem at hselectedMemory
  have hlocal := selectedSOSOffDiagonalRow_value products hend hafit hsfit hseparate
    hloadsOperand hloadsPrior hwrites hboundary hselect
  rw [hselectedMemory] at hlocal
  change Modexp.wordLimbsToNat
      (memoryWordsFrom finalMem sRow.toNat (products + 1)) = _ at hlocal
  have holdLocal : Modexp.wordLimbsToNat
        (memoryWordsFrom mem sRow.toNat (products + 1)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sRow.toNat products) := by
    rw [memoryWordsFrom_succ_eq_append, Modexp.wordLimbsToNat_append,
      memoryWordsFrom_length, hterminalZero]
    change Modexp.wordLimbsToNat (memoryWordsFrom mem sRow.toNat products) +
        UInt256.size ^ products * (UInt256.ofNat 0).toNat = _
    rw [show (UInt256.ofNat 0).toNat = 0 by decide]
    omega
  rw [← holdLocal] at hlocal
  have hprefix := sosOffDiagonalBoundary_memoryWords_below a products initial
    scratchBase offset (by simpa [initial, sosOffDiagonalInitial] using hsfit)
    (by simpa [initial, sosOffDiagonalInitial, hsRow]) hwrites hboundary
  have hsuffix := sosOffDiagonalBoundary_memoryWords_above a products initial
    (sRow.toNat + 32 * (products + 1)) suffixWords
    (by simpa [initial, sosOffDiagonalInitial] using hsfit) (by
      simp [initial, sosOffDiagonalInitial]) hwrites hboundary
  change memoryWordsFrom finalMem scratchBase offset =
      memoryWordsFrom mem scratchBase offset at hprefix
  change memoryWordsFrom finalMem (sRow.toNat + 32 * (products + 1)) suffixWords =
      memoryWordsFrom mem (sRow.toNat + 32 * (products + 1)) suffixWords at hsuffix
  have hfinalSplit : memoryWordsFrom finalMem scratchBase
        (offset + (products + 1) + suffixWords) =
      memoryWordsFrom finalMem scratchBase offset ++
        memoryWordsFrom finalMem sRow.toNat (products + 1) ++
          memoryWordsFrom finalMem (sRow.toNat + 32 * (products + 1)) suffixWords := by
    rw [show offset + (products + 1) + suffixWords =
        offset + ((products + 1) + suffixWords) by omega,
      memoryWordsFrom_add]
    rw [show scratchBase + 32 * offset = sRow.toNat by omega,
      memoryWordsFrom_add]
    simp only [List.append_assoc]
  have hinitialSplit : memoryWordsFrom mem scratchBase
        (offset + (products + 1) + suffixWords) =
      memoryWordsFrom mem scratchBase offset ++
        memoryWordsFrom mem sRow.toNat (products + 1) ++
          memoryWordsFrom mem (sRow.toNat + 32 * (products + 1)) suffixWords := by
    rw [show offset + (products + 1) + suffixWords =
        offset + ((products + 1) + suffixWords) by omega,
      memoryWordsFrom_add]
    rw [show scratchBase + 32 * offset = sRow.toNat by omega,
      memoryWordsFrom_add]
    simp only [List.append_assoc]
  rw [hselectedMemory, hfinalSplit, hinitialSplit]
  rw [hprefix, hsuffix]
  have hreplace := wordLimbsToNat_replace_middle
    (memoryWordsFrom mem scratchBase offset)
    (memoryWordsFrom mem sRow.toNat (products + 1))
    (memoryWordsFrom finalMem sRow.toNat (products + 1))
    (memoryWordsFrom mem (sRow.toNat + 32 * (products + 1)) suffixWords)
    ((readWord mem aw aOff).toNat *
      Modexp.wordLimbsToNat
        (memoryWordsFrom mem (aOff + ⟨32⟩).toNat products))
    (by simp only [memoryWordsFrom_length]) (by simpa [a] using hlocal)
  simpa only [memoryWordsFrom_length, Nat.mul_assoc] using hreplace

/-- The layout-facing form of the whole-row contract.  Coverage and concrete operand/scratch
ranges discharge every guarded load and generated store used by the arithmetic theorem. -/
theorem selectedSOSOffDiagonalRow_whole_value_of_layout
    (offset products suffixWords : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {scratchBase : Nat}
    {selected : SOSOffDiagonalRowSelection}
    (hsRow : sRow.toNat = scratchBase + 32 * offset)
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (haFit : aOff.toNat + 32 * (products + 1) + 31 < UInt256.size)
    (hsFit : sRow.toNat + 32 * (products + 1) + 31 < UInt256.size)
    (hseparate : (aOff + ⟨32⟩).toNat + 32 * products ≤ sRow.toNat)
    (hoperandRange : (aOff + ⟨32⟩).toNat + 32 * products ≤ mem.size)
    (hscratchRange : sRow.toNat + 32 * (products + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hterminalZero : Modexp.MultiLimbMemoryModel.memoryWordNat mem
      (sRow.toNat + 32 * products) = 0)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory scratchBase
          (offset + (products + 1) + suffixWords)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom mem scratchBase
            (offset + (products + 1) + suffixWords)) +
        UInt256.size ^ offset * (readWord mem aw aOff).toNat *
          Modexp.wordLimbsToNat
            (memoryWordsFrom mem (aOff + ⟨32⟩).toNat products) := by
  let a := readWord mem aw aOff
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let multiplyInitial := sosOffDiagonalMultiplyState initial
  have haStart : (aOff + ⟨32⟩).toNat = aOff.toNat + 32 :=
    uadd_word_lit32_toNat aOff (by omega)
  have hinitialCoverage : MemoryCovered multiplyInitial.memory multiplyInitial.activeWords ∧
      multiplyInitial.activeWords.toNat * 32 < UInt256.size := by
    have hread := readWords1_coverage mem aw aOff hcovered hawFit (by omega)
    simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial, sosOffDiagonalSetupAw] using hread
  have hinBounds := multiplyPassIterate_inBounds a products multiplyInitial
    (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial] using
        (show sRow.toNat + 32 * products < UInt256.size by omega))
    (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial] using
        (show sRow.toNat + 32 * products ≤ mem.size by omega))
  have hsteps : ∀ j, j < products →
      let current := multiplyPassIterate a j multiplyInitial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := multiplyPassIterate a j multiplyInitial
    have hop := multiplyPassIterate_operandPtr_toNat a j multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show (aOff + ⟨32⟩).toNat + 32 * j < UInt256.size by
            rw [haStart]
            omega))
    have hresult := multiplyPassIterate_resultPtr_toNat a j multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show sRow.toNat + 32 * j < UInt256.size by omega))
    refine ⟨?_, ?_, hinBounds.1 j hj⟩
    · rw [show current.operandPtr.toNat = (aOff + ⟨32⟩).toNat + 32 * j by
        simpa only [current, multiplyInitial, initial, sosOffDiagonalMultiplyState,
          sosOffDiagonalInitial] using hop]
      rw [haStart]
      omega
    · rw [show current.resultPtr.toNat = sRow.toNat + 32 * j by
        simpa only [current, multiplyInitial, initial, sosOffDiagonalMultiplyState,
          sosOffDiagonalInitial] using hresult]
      omega
  have hloadsOperand : ∀ j, j < products →
      let current := sosOffDiagonalIterate a j initial
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat := by
    intro j hj
    let current := multiplyPassIterate a j multiplyInitial
    have hcurrent := multiplyPassIterate_coverage a j multiplyInitial
      hinitialCoverage.1 hinitialCoverage.2 (fun i hi => hsteps i (by omega))
    have hop := multiplyPassIterate_operandPtr_toNat a j multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show (aOff + ⟨32⟩).toNat + 32 * j < UInt256.size by
            rw [haStart]
            omega))
    have hword : current.operandPtr.toNat + 32 ≤ current.memory.size := by
      rw [show current.memory.size = mem.size by
        simpa only [current, multiplyInitial, initial, sosOffDiagonalMultiplyState,
          sosOffDiagonalInitial] using
            (multiplyPassIterate_inBounds a j multiplyInitial
              (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
                sosOffDiagonalInitial] using
                  (show sRow.toNat + 32 * j < UInt256.size by omega))
              (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
                sosOffDiagonalInitial] using
                  (show sRow.toNat + 32 * j ≤ mem.size by omega))).2]
      rw [show current.operandPtr.toNat = (aOff + ⟨32⟩).toNat + 32 * j by
        simpa only [current, multiplyInitial, initial, sosOffDiagonalMultiplyState,
          sosOffDiagonalInitial] using hop]
      omega
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.operandPtr hcurrent.1 hcurrent.2 hword
    simpa only [current, multiplyInitial, initial, schoolbookOperands,
      ← sosOffDiagonalMultiplyState_iterate] using hload
  have hloadsPrior : ∀ j, j < products →
      let current := sosOffDiagonalIterate a j initial
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
    intro j hj
    let current := multiplyPassIterate a j multiplyInitial
    have hcurrent := multiplyPassIterate_coverage a j multiplyInitial
      hinitialCoverage.1 hinitialCoverage.2 (fun i hi => hsteps i (by omega))
    have hstep := hsteps j hj
    have hoperand := readWords1_coverage current.memory current.activeWords
      current.operandPtr hcurrent.1 hcurrent.2 hstep.1
    have hload := readWord_toNat_of_covered current.memory
      (readWords1 current.activeWords current.operandPtr) current.resultPtr
      hoperand.1 hoperand.2 hstep.2.2
    simpa only [current, multiplyInitial, initial, schoolbookOperands,
      ← sosOffDiagonalMultiplyState_iterate] using hload
  have hwrites : ∀ j, j < products →
      let current := sosOffDiagonalIterate a j initial
      current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    simpa only [multiplyInitial, ← sosOffDiagonalMultiplyState_iterate] using
      hinBounds.1 j hj
  have hboundary :
      let final := sosOffDiagonalIterate a products initial
      final.resultPtr.toNat ≤ final.memory.size := by
    have hptr := multiplyPassIterate_resultPtr_toNat a products multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show sRow.toNat + 32 * products < UInt256.size by omega))
    have hsize := hinBounds.2
    have hmap := sosOffDiagonalMultiplyState_iterate a products initial
    have hmapPtr := congrArg (fun state : MultiplyPassState => state.resultPtr.toNat) hmap
    have hmapSize := congrArg (fun state : MultiplyPassState => state.memory.size) hmap
    change (sosOffDiagonalIterate a products initial).resultPtr.toNat ≤
      (sosOffDiagonalIterate a products initial).memory.size
    rw [show (sosOffDiagonalIterate a products initial).resultPtr.toNat =
        sRow.toNat + 32 * products by
      exact hmapPtr.trans hptr]
    rw [show (sosOffDiagonalIterate a products initial).memory.size = mem.size by
      exact hmapSize.trans (by
        simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
          sosOffDiagonalInitial] using hsize)]
    omega
  apply selectedSOSOffDiagonalRow_whole_value offset products suffixWords hsRow hend
    (by omega) (by omega) hseparate hloadsOperand hloadsPrior hwrites hboundary
    hterminalZero hselect

/-- A selected row whose complete scratch window is allocated preserves memory coverage, active
word representability, and concrete byte-array size. -/
theorem selectedSOSOffDiagonalRow_coverage_of_layout
    (products : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {selected : SOSOffDiagonalRowSelection}
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (haFit : aOff.toNat + 32 * (products + 1) + 31 < UInt256.size)
    (hsFit : sRow.toNat + 32 * (products + 1) + 31 < UInt256.size)
    (hscratchRange : sRow.toNat + 32 * (products + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    MemoryCovered selected.finalMemory selected.finalActiveWords ∧
      selected.finalActiveWords.toNat * 32 < UInt256.size ∧
      selected.finalMemory.size = mem.size := by
  let a := readWord mem aw aOff
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let multiplyInitial := sosOffDiagonalMultiplyState initial
  let rowFinal := sosOffDiagonalIterate a products initial
  have hinitialCoverage : MemoryCovered multiplyInitial.memory multiplyInitial.activeWords ∧
      multiplyInitial.activeWords.toNat * 32 < UInt256.size := by
    have hread := readWords1_coverage mem aw aOff hcovered hawFit (by omega)
    simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial, sosOffDiagonalSetupAw] using hread
  have hinBounds := multiplyPassIterate_inBounds a products multiplyInitial
    (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial] using
        (show sRow.toNat + 32 * products < UInt256.size by omega))
    (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial] using
        (show sRow.toNat + 32 * products ≤ mem.size by omega))
  have hsteps : ∀ j, j < products →
      let current := multiplyPassIterate a j multiplyInitial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := multiplyPassIterate_operandPtr_toNat a j multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show (aOff + ⟨32⟩).toNat + 32 * j < UInt256.size by
            rw [uadd_word_lit32_toNat aOff (by omega)]
            omega))
    have hresult := multiplyPassIterate_resultPtr_toNat a j multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show sRow.toNat + 32 * j < UInt256.size by omega))
    refine ⟨?_, ?_, hinBounds.1 j hj⟩
    · rw [hop]
      change (aOff + ⟨32⟩).toNat + 32 * j + 32 + 31 < UInt256.size
      rw [uadd_word_lit32_toNat aOff (by omega)]
      omega
    · rw [hresult]
      change sRow.toNat + 32 * j + 32 + 31 < UInt256.size
      omega
  have hiterCoverage := multiplyPassIterate_coverage a products multiplyInitial
    hinitialCoverage.1 hinitialCoverage.2 hsteps
  have hmap := sosOffDiagonalMultiplyState_iterate a products initial
  have hrowCoverage : MemoryCovered rowFinal.memory rowFinal.activeWords ∧
      rowFinal.activeWords.toNat * 32 < UInt256.size := by
    rw [← hmap] at hiterCoverage
    exact hiterCoverage
  have hrowSize : rowFinal.memory.size = mem.size := by
    have hmapSize := congrArg (fun state : MultiplyPassState => state.memory.size) hmap
    exact hmapSize.trans (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using hinBounds.2)
  have hrowPtr : rowFinal.resultPtr.toNat = sRow.toNat + 32 * products := by
    have hptr := multiplyPassIterate_resultPtr_toNat a products multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show sRow.toNat + 32 * products < UInt256.size by omega))
    have hmapPtr := congrArg (fun state : MultiplyPassState => state.resultPtr.toNat) hmap
    exact hmapPtr.trans hptr
  have hwrite : rowFinal.resultPtr.toNat + 32 ≤ rowFinal.memory.size := by
    rw [hrowPtr, hrowSize]
    omega
  have hwriteCoverage := write32_coverage rowFinal.carry rowFinal.memory
    rowFinal.activeWords rowFinal.resultPtr hrowCoverage.1 hrowCoverage.2
    (by rw [hrowPtr]; omega)
    (by rw [Nat.sub_eq_zero_of_le (by omega : rowFinal.resultPtr.toNat ≤
      rowFinal.memory.size)]; exact lt_usize 0 (by norm_num))
  have hselectedMemory := selectedSOSOffDiagonalRow_finalMemory_eq products
    (by exact hend) (by omega) hselect
  have hselectedAw := selectedSOSOffDiagonalRow_finalActiveWords_eq products
    (by exact hend) (by omega) hselect
  have hfinalSize : selected.finalMemory.size = mem.size := by
    rw [hselectedMemory]
    unfold sosOffDiagonalBoundaryMemory
    rw [write_size_of_inBounds_from rowFinal.carry.toByteArray rowFinal.memory 0
      rowFinal.resultPtr.toNat 32 (by decide) (by rw [toByteArray_size]) hwrite,
      hrowSize]
  refine ⟨?_, ?_, hfinalSize⟩
  · rw [hselectedMemory, hselectedAw]
    simpa [sosOffDiagonalBoundaryMemory, sosOffDiagonalBoundaryAw, readWords1] using
      hwriteCoverage.1
  · rw [hselectedAw]
    simpa [sosOffDiagonalBoundaryAw, readWords1] using hwriteCoverage.2

/-- Under the allocated scratch geometry, a selected row preserves arbitrary complete word ranges
both below its first destination and above its terminal carry destination. -/
theorem selectedSOSOffDiagonalRow_frames_of_layout
    (products : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {selected : SOSOffDiagonalRowSelection}
    (belowPtr belowWords abovePtr aboveWords : Nat)
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (hafit : aOff.toNat + 32 * (products + 1) < UInt256.size)
    (hsfit : sRow.toNat + 32 * (products + 1) < UInt256.size)
    (hscratchRange : sRow.toNat + 32 * (products + 1) ≤ mem.size)
    (hbelow : belowPtr + 32 * belowWords ≤ sRow.toNat)
    (habove : sRow.toNat + 32 * (products + 1) ≤ abovePtr)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    memoryWordsFrom selected.finalMemory belowPtr belowWords =
        memoryWordsFrom mem belowPtr belowWords ∧
      memoryWordsFrom selected.finalMemory abovePtr aboveWords =
        memoryWordsFrom mem abovePtr aboveWords := by
  let a := readWord mem aw aOff
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let multiplyInitial := sosOffDiagonalMultiplyState initial
  have hinBounds := multiplyPassIterate_inBounds a products multiplyInitial
    (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial] using
        (show sRow.toNat + 32 * products < UInt256.size by omega))
    (by simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
      sosOffDiagonalInitial] using
        (show sRow.toNat + 32 * products ≤ mem.size by omega))
  have hwrites : ∀ j, j < products →
      let current := sosOffDiagonalIterate a j initial
      current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    simpa only [multiplyInitial, ← sosOffDiagonalMultiplyState_iterate] using
      hinBounds.1 j hj
  have hboundary :
      let final := sosOffDiagonalIterate a products initial
      final.resultPtr.toNat ≤ final.memory.size := by
    have hmap := sosOffDiagonalMultiplyState_iterate a products initial
    have hptr := multiplyPassIterate_resultPtr_toNat a products multiplyInitial (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using
          (show sRow.toNat + 32 * products < UInt256.size by omega))
    have hmapPtr := congrArg (fun state : MultiplyPassState => state.resultPtr.toNat) hmap
    have hmapSize := congrArg (fun state : MultiplyPassState => state.memory.size) hmap
    have hsosPtr : (sosOffDiagonalIterate a products initial).resultPtr.toNat =
        sRow.toNat + 32 * products := hmapPtr.trans (by
      simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
        sosOffDiagonalInitial] using hptr)
    have hsosSize : (sosOffDiagonalIterate a products initial).memory.size = mem.size :=
      hmapSize.trans (by
        simpa [multiplyInitial, initial, sosOffDiagonalMultiplyState,
          sosOffDiagonalInitial] using hinBounds.2)
    change (sosOffDiagonalIterate a products initial).resultPtr.toNat ≤
      (sosOffDiagonalIterate a products initial).memory.size
    rw [hsosPtr, hsosSize]
    omega
  have hselectedMemory := selectedSOSOffDiagonalRow_finalMemory_eq products hend hafit hselect
  rw [hselectedMemory]
  constructor
  · apply sosOffDiagonalBoundary_memoryWords_below a products initial belowPtr belowWords
      (by simpa [initial, sosOffDiagonalInitial] using hsfit)
      (by simpa [initial, sosOffDiagonalInitial] using hbelow) hwrites hboundary
  · apply sosOffDiagonalBoundary_memoryWords_above a products initial abovePtr aboveWords
      (by simpa [initial, sosOffDiagonalInitial] using hsfit)
      (by simpa [initial, sosOffDiagonalInitial] using habove) hwrites hboundary

/-- Every selected upper-triangle row preserves the allocated-memory invariants needed by the
following row.  This packages the row coverage theorem across the complete outer loop. -/
theorem selectedSOSOffDiagonalLoop_coverage
    (rows offset : Nat) {rowFuel productFuel : Nat}
    {aEnd fixedDrop drop : UInt256} {scratchBase : Nat}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hstop : aEnd.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsRow : state.sRow.toNat = scratchBase + 32 * offset)
    (hsFit : scratchBase + 32 * (offset + 2 * rows) + 31 < UInt256.size)
    (hseparate : aEnd.toNat ≤ state.sRow.toNat)
    (hscratchRange : scratchBase + 32 * (offset + 2 * rows) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop drop state =
      some selected) :
    MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
  induction rowFuel generalizing rows offset state selected drop with
  | zero => simp [selectSOSOffDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSOffDiagonalLoop] at hselect
      by_cases hzero : rows = 0
      · subst rows
        have hexit : state.aOff.lt aEnd = ⟨0⟩ := by apply ult_zero; omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        exact ⟨hcovered, hawFit, rfl⟩
      · have hcontinue : state.aOff.lt aEnd ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrow : selectSOSOffDiagonalRow productFuel state.memory state.activeWords
            state.sRow state.aOff aEnd with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            let next := sosOffDiagonalLoopAdvance state row
            cases hrest : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop
                fixedDrop next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hsStep : next.sRow.toNat = state.sRow.toNat + 64 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                    Nat.mod_eq_of_lt (by omega)]
                have hrowEnd : aEnd.toNat = state.aOff.toNat + 32 * ((rows - 1) + 1) := by
                  omega
                have hrowCoverage := selectedSOSOffDiagonalRow_coverage_of_layout
                  (rows - 1) hrowEnd (by omega)
                  (by rw [hsRow]; omega)
                  (by rw [hsRow]; omega) hcovered hawFit hrow
                have hrestCoverage := ih (rows - 1) (offset + 2)
                  (state := next) (selected := rest) (drop := fixedDrop)
                  (by rw [haStep]; omega)
                  (by rw [haStep]; omega)
                  (by rw [hsStep, hsRow]; omega)
                  (by omega)
                  (by rw [hsStep]; omega)
                  (by
                    dsimp only [next, sosOffDiagonalLoopAdvance]
                    rw [hrowCoverage.2.2]
                    omega)
                  hrowCoverage.1 hrowCoverage.2.1 hrest
                exact ⟨hrestCoverage.1, hrestCoverage.2.1,
                  hrestCoverage.2.2.trans hrowCoverage.2.2⟩

/-- The complete upper-triangle loop writes only in its scratch allocation. -/
theorem selectedSOSOffDiagonalLoop_frame_below
    (rows offset ptr count : Nat) {rowFuel productFuel : Nat}
    {aEnd fixedDrop drop : UInt256} {scratchBase : Nat}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hstop : aEnd.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsRow : state.sRow.toNat = scratchBase + 32 * offset)
    (hsFit : scratchBase + 32 * (offset + 2 * rows) + 31 < UInt256.size)
    (hseparate : aEnd.toNat ≤ state.sRow.toNat)
    (hscratchRange : scratchBase + 32 * (offset + 2 * rows) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbelow : ptr + 32 * count ≤ scratchBase)
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop drop state =
      some selected) :
    memoryWordsFrom selected.final.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction rowFuel generalizing rows offset state selected drop with
  | zero => simp [selectSOSOffDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSOffDiagonalLoop] at hselect
      by_cases hzero : rows = 0
      · subst rows
        have hexit : state.aOff.lt aEnd = ⟨0⟩ := by apply ult_zero; omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hcontinue : state.aOff.lt aEnd ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrow : selectSOSOffDiagonalRow productFuel state.memory state.activeWords
            state.sRow state.aOff aEnd with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            let next := sosOffDiagonalLoopAdvance state row
            cases hrest : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop
                fixedDrop next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hsStep : next.sRow.toNat = state.sRow.toNat + 64 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                    Nat.mod_eq_of_lt (by omega)]
                have hrowEnd : aEnd.toNat = state.aOff.toNat + 32 * ((rows - 1) + 1) := by
                  omega
                have hrowScratchRange : state.sRow.toNat + 32 * ((rows - 1) + 1) ≤
                    state.memory.size := by rw [hsRow]; omega
                have hrowCoverage := selectedSOSOffDiagonalRow_coverage_of_layout
                  (rows - 1) hrowEnd (by omega) (by rw [hsRow]; omega)
                  hrowScratchRange hcovered hawFit hrow
                have hrowFrame := selectedSOSOffDiagonalRow_frames_of_layout
                  (rows - 1) ptr count
                  (state.sRow.toNat + 32 * ((rows - 1) + 1)) 0
                  hrowEnd (by omega) (by rw [hsRow]; omega) hrowScratchRange
                  (by rw [hsRow]; omega) (by omega) hrow
                have hrestFrame := ih (rows - 1) (offset + 2)
                  (state := next) (selected := rest) (drop := fixedDrop)
                  (by rw [haStep]; omega)
                  (by rw [haStep]; omega)
                  (by rw [hsStep, hsRow]; omega)
                  (by omega)
                  (by rw [hsStep]; omega)
                  (by
                    dsimp only [next, sosOffDiagonalLoopAdvance]
                    rw [hrowCoverage.2.2]
                    omega)
                  hrowCoverage.1 hrowCoverage.2.1 hrest
                exact hrestFrame.trans hrowFrame.1

/-- The complete selected outer loop sums every upper-triangle row into the full scratch natural.
The zero-frontier invariant records the still-unwritten carry destinations. -/
theorem selectedSOSOffDiagonalLoop_value
    (rows offset : Nat) {rowFuel productFuel : Nat}
    {aEnd fixedDrop drop : UInt256} {scratchBase : Nat}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hstop : aEnd.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsRow : state.sRow.toNat = scratchBase + 32 * offset)
    (hsFit : scratchBase + 32 * (offset + 2 * rows) + 31 < UInt256.size)
    (hseparate : aEnd.toNat ≤ state.sRow.toNat)
    (hscratchRange : scratchBase + 32 * (offset + 2 * rows) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hzeros : memoryWordsFrom state.memory
      (scratchBase + 32 * (offset + rows - 1)) (rows + 1) =
        List.replicate (rows + 1) (⟨0⟩ : UInt256))
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop drop state =
      some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory scratchBase (offset + 2 * rows)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory scratchBase (offset + 2 * rows)) +
        sosOffDiagonalAt UInt256.size offset
          ((memoryWordsFrom state.memory state.aOff.toNat rows).map UInt256.toNat) := by
  induction rowFuel generalizing rows offset state selected drop with
  | zero => simp [selectSOSOffDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSOffDiagonalLoop] at hselect
      by_cases hzero : rows = 0
      · subst rows
        have hexit : state.aOff.lt aEnd = ⟨0⟩ := by apply ult_zero; omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hrows : 0 < rows := by omega
        have hcontinue : state.aOff.lt aEnd ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrow : selectSOSOffDiagonalRow productFuel state.memory state.activeWords
            state.sRow state.aOff aEnd with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            let next := sosOffDiagonalLoopAdvance state row
            cases hrest : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop
                fixedDrop next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hsStep : next.sRow.toNat = state.sRow.toNat + 64 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                    Nat.mod_eq_of_lt (by omega)]
                have hrowEnd : aEnd.toNat = state.aOff.toNat + 32 * ((rows - 1) + 1) := by
                  omega
                have hrowAFit : state.aOff.toNat + 32 * ((rows - 1) + 1) + 31 <
                    UInt256.size := by omega
                have hrowSFit : state.sRow.toNat + 32 * ((rows - 1) + 1) + 31 <
                    UInt256.size := by rw [hsRow]; omega
                have haStart : (state.aOff + ⟨32⟩).toNat = state.aOff.toNat + 32 :=
                  uadd_word_lit32_toNat state.aOff (by omega)
                have hrowSeparate : (state.aOff + ⟨32⟩).toNat +
                    32 * (rows - 1) ≤ state.sRow.toNat := by
                  rw [haStart]
                  omega
                have hrowOperandRange : (state.aOff + ⟨32⟩).toNat +
                    32 * (rows - 1) ≤ state.memory.size := by
                  calc
                    (state.aOff + ⟨32⟩).toNat + 32 * (rows - 1) = aEnd.toNat := by
                      rw [haStart, hstop]
                      omega
                    _ ≤ state.sRow.toNat := hseparate
                    _ ≤ state.memory.size := by rw [hsRow]; omega
                have hrowScratchRange : state.sRow.toNat + 32 * ((rows - 1) + 1) ≤
                    state.memory.size := by rw [hsRow]; omega
                have hzeroHead : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                    (state.sRow.toNat + 32 * (rows - 1)) = 0 := by
                  have hhead := congrArg List.head? hzeros
                  have hword : UInt256.ofNat
                        (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                          (scratchBase + 32 * (offset + rows - 1))) =
                      (⟨0⟩ : UInt256) := by
                    apply Option.some.inj
                    simpa only [memoryWordsFrom, List.replicate_succ, List.head?_cons] using hhead
                  have hnats := congrArg UInt256.toNat hword
                  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] at hnats
                  rw [show state.sRow.toNat + 32 * (rows - 1) =
                      scratchBase + 32 * (offset + rows - 1) by rw [hsRow]; omega]
                  exact hnats
                have hrowValue := selectedSOSOffDiagonalRow_whole_value_of_layout
                  offset (rows - 1) rows hsRow hrowEnd hrowAFit hrowSFit hrowSeparate
                  hrowOperandRange hrowScratchRange hcovered hawFit hzeroHead hrow
                have hrowCoverage := selectedSOSOffDiagonalRow_coverage_of_layout
                  (rows - 1) hrowEnd hrowAFit hrowSFit hrowScratchRange hcovered hawFit hrow
                have hframes := selectedSOSOffDiagonalRow_frames_of_layout
                  (rows - 1) state.aOff.toNat rows
                  (scratchBase + 32 * (offset + rows)) rows
                  hrowEnd (by omega) (by omega) hrowScratchRange
                  (by omega) (by rw [hsRow]; omega) hrow
                have hnextStop : aEnd.toNat = next.aOff.toNat + 32 * (rows - 1) := by
                  rw [haStep]
                  omega
                have hnextAFit : next.aOff.toNat + 32 * (rows - 1) + 31 <
                    UInt256.size := by rw [haStep]; omega
                have hnextSRow : next.sRow.toNat =
                    scratchBase + 32 * (offset + 2) := by rw [hsStep, hsRow]; omega
                have hnextSFit : scratchBase +
                    32 * ((offset + 2) + 2 * (rows - 1)) + 31 < UInt256.size := by
                  omega
                have hnextSeparate : aEnd.toNat ≤ next.sRow.toNat := by
                  rw [hsStep]
                  omega
                have hnextScratchRange : scratchBase +
                    32 * ((offset + 2) + 2 * (rows - 1)) ≤ next.memory.size := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  rw [hrowCoverage.2.2]
                  omega
                have hzeroTail : memoryWordsFrom state.memory
                    (scratchBase + 32 * (offset + rows)) rows =
                    List.replicate rows (⟨0⟩ : UInt256) := by
                  have htail := congrArg List.tail hzeros
                  simp only [memoryWordsFrom, List.replicate_succ, List.tail_cons] at htail
                  simpa [show scratchBase + 32 * (offset + rows - 1) + 32 =
                      scratchBase + 32 * (offset + rows) by omega] using htail
                have hnextZeros : memoryWordsFrom next.memory
                    (scratchBase + 32 * ((offset + 2) + (rows - 1) - 1))
                    ((rows - 1) + 1) =
                    List.replicate ((rows - 1) + 1) (⟨0⟩ : UInt256) := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  rw [show scratchBase + 32 * ((offset + 2) + (rows - 1) - 1) =
                      scratchBase + 32 * (offset + rows) by omega,
                    show rows - 1 + 1 = rows by omega, hframes.2, hzeroTail]
                have hrecursive := ih (rows - 1) (offset + 2)
                  (state := next) (selected := rest)
                  (drop := fixedDrop) hnextStop hnextAFit hnextSRow hnextSFit
                  hnextSeparate hnextScratchRange hrowCoverage.1 hrowCoverage.2.1
                  hnextZeros hrest
                have hoperandFrame : memoryWordsFrom next.memory state.aOff.toNat rows =
                    memoryWordsFrom state.memory state.aOff.toNat rows := by
                  simpa only [next, sosOffDiagonalLoopAdvance] using hframes.1
                cases rows with
                | zero => contradiction
                | succ remaining =>
                    have htailFrame := congrArg List.tail hoperandFrame
                    simp only [memoryWordsFrom, List.tail_cons] at htailFrame
                    have htailFrame' : memoryWordsFrom row.finalMemory
                          (state.aOff.toNat + 32) remaining =
                        memoryWordsFrom state.memory (state.aOff.toNat + 32) remaining := by
                      simpa only [next, sosOffDiagonalLoopAdvance] using htailFrame
                    simp only [Nat.succ_sub_one] at hrecursive hrowValue
                    dsimp only [next, sosOffDiagonalLoopAdvance] at hrecursive
                    rw [haStart] at hrecursive
                    rw [htailFrame'] at hrecursive
                    rw [show offset + 2 + 2 * remaining =
                        offset + 2 * (remaining + 1) by omega] at hrecursive
                    have hrecursive' : Modexp.wordLimbsToNat
                          (memoryWordsFrom rest.final.memory scratchBase
                            (offset + 2 * (remaining + 1))) =
                        Modexp.wordLimbsToNat
                            (memoryWordsFrom row.finalMemory scratchBase
                              (offset + 2 * (remaining + 1))) +
                          sosOffDiagonalAt UInt256.size (offset + 2)
                            ((memoryWordsFrom state.memory
                              (state.aOff.toNat + 32) remaining).map UInt256.toNat) := by
                      exact hrecursive
                    rw [haStart] at hrowValue
                    rw [show offset + (remaining + 1) + (remaining + 1) =
                        offset + 2 * (remaining + 1) by omega] at hrowValue
                    have hrowValue' : Modexp.wordLimbsToNat
                          (memoryWordsFrom row.finalMemory scratchBase
                            (offset + 2 * (remaining + 1))) =
                        Modexp.wordLimbsToNat
                            (memoryWordsFrom state.memory scratchBase
                              (offset + 2 * (remaining + 1))) +
                          UInt256.size ^ offset *
                            (readWord state.memory state.activeWords state.aOff).toNat *
                              Modexp.wordLimbsToNat
                                (memoryWordsFrom state.memory
                                  (state.aOff.toNat + 32) remaining) := by
                      exact hrowValue
                    have hwordIn : state.aOff.toNat + 32 ≤ state.memory.size := by omega
                    have hread := readWord_toNat_of_covered state.memory state.activeWords
                      state.aOff hcovered hawFit hwordIn
                    change Modexp.wordLimbsToNat
                        (memoryWordsFrom rest.final.memory scratchBase
                          (offset + 2 * (remaining + 1))) = _
                    calc
                      Modexp.wordLimbsToNat
                          (memoryWordsFrom rest.final.memory scratchBase
                            (offset + 2 * (remaining + 1))) =
                          Modexp.wordLimbsToNat
                              (memoryWordsFrom row.finalMemory scratchBase
                                (offset + 2 * (remaining + 1))) +
                            sosOffDiagonalAt UInt256.size (offset + 2)
                              ((memoryWordsFrom state.memory
                                (state.aOff.toNat + 32) remaining).map UInt256.toNat) :=
                        hrecursive'
                      _ = (Modexp.wordLimbsToNat
                              (memoryWordsFrom state.memory scratchBase
                                (offset + 2 * (remaining + 1))) +
                            UInt256.size ^ offset *
                              (readWord state.memory state.activeWords state.aOff).toNat *
                                Modexp.wordLimbsToNat
                                  (memoryWordsFrom state.memory
                                    (state.aOff.toNat + 32) remaining)) +
                            sosOffDiagonalAt UInt256.size (offset + 2)
                              ((memoryWordsFrom state.memory
                                (state.aOff.toNat + 32) remaining).map UInt256.toNat) := by
                        rw [hrowValue']
                      _ = Modexp.wordLimbsToNat
                              (memoryWordsFrom state.memory scratchBase
                                (offset + 2 * (remaining + 1))) +
                            sosOffDiagonalAt UInt256.size offset
                              ((memoryWordsFrom state.memory state.aOff.toNat
                                (remaining + 1)).map UInt256.toNat) := by
                        simp only [memoryWordsFrom, List.map_cons, sosOffDiagonalAt]
                        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hread]
                        rw [← Modexp.wordLimbsToNat_eq_limbsToNatAt]
                        ring

/-- With the deployed initial offset and zeroed `2 * words + 1` scratch allocation, the selected
outer loop computes exactly the pure upper-triangle model. -/
theorem selectedSOSOffDiagonalLoop_value_from_zero
    (words : Nat) {rowFuel productFuel : Nat}
    {aEnd fixedDrop drop : UInt256} {scratchBase : Nat}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hstop : aEnd.toNat = state.aOff.toNat + 32 * words)
    (haFit : state.aOff.toNat + 32 * words + 31 < UInt256.size)
    (hsRow : state.sRow.toNat = scratchBase + 32)
    (hsFit : scratchBase + 32 * (2 * words + 1) + 31 < UInt256.size)
    (hseparate : aEnd.toNat ≤ state.sRow.toNat)
    (hscratchRange : scratchBase + 32 * (2 * words + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hzeroAll : memoryWordsFrom state.memory scratchBase (2 * words + 1) =
      List.replicate (2 * words + 1) (⟨0⟩ : UInt256))
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop drop state =
      some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory scratchBase (2 * words + 1)) =
      Modexp.sosOffDiagonal UInt256.size
        ((memoryWordsFrom state.memory state.aOff.toNat words).map UInt256.toNat) := by
  have hfrontier : memoryWordsFrom state.memory (scratchBase + 32 * words) (words + 1) =
      List.replicate (words + 1) (⟨0⟩ : UInt256) := by
    have hall := hzeroAll
    rw [show 2 * words + 1 = words + (words + 1) by omega,
      memoryWordsFrom_add] at hall
    have hdrop := congrArg (List.drop words) hall
    simpa [memoryWordsFrom_length, List.replicate_add] using hdrop
  have hvalue := selectedSOSOffDiagonalLoop_value words 1 hstop haFit
    (by simpa using hsRow)
    (by simpa only [Nat.one_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsFit)
    hseparate
    (by simpa only [Nat.one_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hscratchRange)
    hcovered hawFit (by
      simpa only [Nat.one_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hfrontier)
    hselect
  rw [show 1 + 2 * words = 2 * words + 1 by omega] at hvalue
  rw [hzeroAll, Modexp.wordLimbsToNat_replicate_zero, Nat.zero_add,
    sosOffDiagonalAt_one] at hvalue
  exact hvalue

end Modexp.MultiLimbMontgomerySOSSemantic
