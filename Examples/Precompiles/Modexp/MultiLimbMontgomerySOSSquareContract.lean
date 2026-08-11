import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSDiagonalLoopContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSDoubleContract

/-! # Complete SOS square-phase semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem sosDoubleAdvance_coverage
    (state : SOSDoubleState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : state.ptr.toNat + 32 + 31 < UInt256.size)
    (hwrite : state.ptr.toNat + 32 ≤ state.memory.size) :
    MemoryCovered (sosDoubleAdvance state).memory (sosDoubleAdvance state).activeWords ∧
      (sosDoubleAdvance state).activeWords.toNat * 32 < UInt256.size ∧
      (sosDoubleAdvance state).memory.size = state.memory.size := by
  let aw1 := sosDoubleAw1 state.activeWords state.ptr
  have hread := readWords1_coverage state.memory state.activeWords state.ptr
    hcovered hawFit hptrFit
  have hwriteCoverage := write32_coverage
    (sosDoubleOutput state.memory state.activeWords state.ptr state.carry)
    state.memory aw1 state.ptr
    (by simpa only [aw1, sosDoubleAw1] using hread.1)
    (by simpa only [aw1, sosDoubleAw1] using hread.2)
    hptrFit
    (by rw [Nat.sub_eq_zero_of_le (by omega : state.ptr.toNat ≤ state.memory.size)]
        exact lt_usize 0 (by norm_num))
  have hsize : (sosDoubleAdvance state).memory.size = state.memory.size := by
    dsimp only [sosDoubleAdvance, sosDoubleMemory]
    rw [write_size_of_inBounds_from _ _ 0 state.ptr.toNat 32 (by decide)
      (by rw [toByteArray_size]) hwrite]
  refine ⟨?_, ?_, hsize⟩
  · simpa only [sosDoubleAdvance, sosDoubleMemory, sosDoubleAw,
      aw1, sosDoubleAw1, readWords1] using hwriteCoverage.1
  · simpa only [sosDoubleAdvance, sosDoubleAw, aw1, sosDoubleAw1,
      readWords1] using hwriteCoverage.2

theorem sosDoubleIterate_coverage
    (n : Nat) (state : SOSDoubleState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : state.ptr.toNat + 32 * n + 31 < UInt256.size)
    (hrange : state.ptr.toNat + 32 * n ≤ state.memory.size) :
    MemoryCovered (sosDoubleIterate n state).memory
        (sosDoubleIterate n state).activeWords ∧
      (sosDoubleIterate n state).activeWords.toNat * 32 < UInt256.size ∧
      (sosDoubleIterate n state).memory.size = state.memory.size := by
  induction n generalizing state with
  | zero => exact ⟨hcovered, hawFit, rfl⟩
  | succ n ih =>
      let next := sosDoubleAdvance state
      have hfirst := sosDoubleAdvance_coverage state hcovered hawFit (by omega) (by omega)
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosDoubleAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hrest := ih next hfirst.1 hfirst.2.1
        (by rw [hstep]; omega)
        (by rw [hstep, hfirst.2.2]; omega)
      simpa only [sosDoubleIterate, next] using
        ⟨hrest.1, hrest.2.1, hrest.2.2.trans hfirst.2.2⟩

theorem sosDoubleIterate_memoryWords_below
    (n : Nat) (state : SOSDoubleState) (ptr count : Nat)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (sosDoubleIterate n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosDoubleAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosDoubleAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosDoubleIterate] using hwrites 0 (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosDoubleIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosDoubleIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) (by rw [hstep]; omega) htailWrites
      have hfirst := memoryWordsFrom_write_above
        (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toByteArray
        state.memory state.ptr.toNat ptr count (by rw [toByteArray_size])
        (by omega) hbelow
      calc
        memoryWordsFrom (sosDoubleIterate (n + 1) state).memory ptr count =
            memoryWordsFrom (sosDoubleIterate n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := by
          simpa only [next, sosDoubleAdvance, sosDoubleMemory] using hfirst

theorem selectedSOSDoublePhase_memoryWords_below
    (words : Nat) {fuel : Nat} {stop : UInt256}
    {state : SOSDoubleState} {selected : SOSDoublePhaseSelection}
    (ptr count : Nat)
    (hstop : stop.toNat = state.ptr.toNat + 32 * words)
    (hfit : state.ptr.toNat + 32 * words < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat)
    (hwrites : ∀ j, j < words →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hselect : selectSOSDoublePhase fuel stop state = some selected) :
    memoryWordsFrom selected.final.memory ptr count = memoryWordsFrom state.memory ptr count := by
  have hwords := selectedSOSDoublePhase_words_eq_geometry words hstop hfit hselect
  have hfinal := selectedSOSDoublePhase_final_eq_iterate hselect
  rw [hwords] at hfinal
  rw [hfinal]
  exact sosDoubleIterate_memoryWords_below words state ptr count hfit hbelow hwrites

/-- A selected full doubling scan is exact and preserves the allocated covered memory image. -/
theorem selectedSOSDoublePhase_value_of_coverage
    (words : Nat) {fuel : Nat} {stop : UInt256}
    {state : SOSDoubleState} {selected : SOSDoublePhaseSelection}
    (hstop : stop.toNat = state.ptr.toNat + 32 * words)
    (hfit : state.ptr.toNat + 32 * words + 31 < UInt256.size)
    (hrange : state.ptr.toNat + 32 * words ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hcarry : state.carry.toNat < 2)
    (hselect : selectSOSDoublePhase fuel stop state = some selected) :
    (Modexp.wordLimbsToNat
          (memoryWordsFrom selected.final.memory state.ptr.toNat words) +
        UInt256.size ^ words * selected.final.carry.toNat =
          2 * Modexp.wordLimbsToNat
            (memoryWordsFrom state.memory state.ptr.toNat words) + state.carry.toNat) ∧
      MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
  have hwords := selectedSOSDoublePhase_words_eq_geometry words hstop (by omega) hselect
  have hfinal := selectedSOSDoublePhase_final_eq_iterate hselect
  have hiter := sosDoubleIterate_coverage words state hcovered hawFit hfit hrange
  have hloads : ∀ j, j < words →
      let current := sosDoubleIterate j state
      (sosDoubleWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
    intro j hj
    let current := sosDoubleIterate j state
    have hcurrent := sosDoubleIterate_coverage j state hcovered hawFit
      (by omega) (by omega)
    have hptr := sosDoubleIterate_ptr_toNat j state (by omega)
    have hword : current.ptr.toNat + 32 ≤ current.memory.size := by
      change (sosDoubleIterate j state).ptr.toNat + 32 ≤
        (sosDoubleIterate j state).memory.size
      rw [hptr, hcurrent.2.2]
      omega
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.ptr hcurrent.1 hcurrent.2.1 hword
    simpa only [current, sosDoubleWord] using hload
  have hwrites : ∀ j, j < words →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := sosDoubleIterate j state
    have hcurrent := sosDoubleIterate_coverage j state hcovered hawFit
      (by omega) (by omega)
    have hptr := sosDoubleIterate_ptr_toNat j state (by omega)
    change (sosDoubleIterate j state).ptr.toNat + 32 ≤
      (sosDoubleIterate j state).memory.size
    rw [hptr, hcurrent.2.2]
    omega
  have hvalue := selectedSOSDoublePhase_value words hstop (by omega) hcarry
    hloads hwrites hselect
  rw [hwords] at hfinal
  have hselectedCoverage : MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
    rw [hfinal]
    exact ⟨hiter.1, hiter.2.1, hiter.2.2⟩
  exact ⟨hvalue, hselectedCoverage⟩

theorem square_lt_radix_pow_two_mul_add_one
    {value radix words : Nat}
    (hvalue : value < radix ^ words)
    (hradix : 1 < radix) :
    value ^ 2 < radix ^ (2 * words + 1) := by
  have hsquare : value ^ 2 < (radix ^ words) ^ 2 :=
    Nat.pow_lt_pow_left hvalue (by decide)
  have hsquare' : value ^ 2 < radix ^ (2 * words) := by
    rw [show (radix ^ words) ^ 2 = radix ^ (2 * words) by
      rw [← pow_mul]
      congr 1
      omega] at hsquare
    exact hsquare
  have hpowPos : 0 < radix ^ (2 * words) := pow_pos (by omega) _
  have hnext : radix ^ (2 * words) < radix ^ (2 * words + 1) := by
    rw [pow_succ]
    have hmul := Nat.mul_lt_mul_of_pos_left hradix hpowPos
    simpa only [Nat.mul_one] using hmul
  exact hsquare'.trans hnext

theorem carry_eq_zero_of_accumulator_lt
    {output radix carry twice : Nat}
    (hvalue : output + radix * carry = twice)
    (hbound : twice < radix) :
    carry = 0 := by
  by_contra hnonzero
  have hcarry : 1 ≤ carry := by omega
  have hlower : radix ≤ radix * carry := by
    have hmul := Nat.mul_le_mul_left radix hcarry
    simpa only [Nat.mul_one] using hmul
  omega

theorem selectedSOSDoublePhase_exact_of_bound
    (words : Nat) {fuel : Nat} {stop : UInt256}
    {state : SOSDoubleState} {selected : SOSDoublePhaseSelection} {value : Nat}
    (hstop : stop.toNat = state.ptr.toNat + 32 * words)
    (hfit : state.ptr.toNat + 32 * words + 31 < UInt256.size)
    (hrange : state.ptr.toNat + 32 * words ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hcarry : state.carry = ⟨0⟩)
    (hinput : Modexp.wordLimbsToNat
        (memoryWordsFrom state.memory state.ptr.toNat words) = value)
    (hbound : 2 * value < UInt256.size ^ words)
    (hselect : selectSOSDoublePhase fuel stop state = some selected) :
    (Modexp.wordLimbsToNat
          (memoryWordsFrom selected.final.memory state.ptr.toNat words) = 2 * value) ∧
      MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
  have hcontract := selectedSOSDoublePhase_value_of_coverage words hstop hfit hrange
    hcovered hawFit (by rw [hcarry]; decide) hselect
  have hvalue := hcontract.1
  rw [hinput, hcarry] at hvalue
  have hcarryNat : selected.final.carry.toNat = 0 :=
    carry_eq_zero_of_accumulator_lt hvalue (by simpa only [UInt256.toNat] using hbound)
  have hcarryZero : selected.final.carry = ⟨0⟩ := by
    apply u256_inj
    exact hcarryNat
  rw [hcarryZero] at hvalue
  simp only [UInt256.toNat, Nat.mul_zero, Nat.add_zero] at hvalue
  exact ⟨hvalue, hcontract.2.1, hcontract.2.2.1, hcontract.2.2.2⟩

/-- Starting from the completed upper-triangle accumulator, the selected doubling and diagonal
phases produce the exact square of the source operand. -/
theorem selectedSOSSquarePhases_value
    (words : Nat) {doubleFuel diagonalFuel carryFuel : Nat}
    {mem : ByteArray} {aw sP sEnd aP aEnd fixedDrop drop : UInt256}
    {double : SOSDoublePhaseSelection} {diagonal : SOSDiagonalLoopSelection}
    (hdoubleStop : sEnd.toNat = sP.toNat + 32 * (2 * words + 1))
    (haStop : aEnd.toNat = aP.toNat + 32 * words)
    (haFit : aP.toNat + 32 * words + 31 < UInt256.size)
    (hsFit : sP.toNat + 32 * (2 * words + 1) + 31 < UInt256.size)
    (hseparate : aEnd.toNat ≤ sP.toNat)
    (hsRange : sP.toNat + 32 * (2 * words + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hoffDiagonal : Modexp.wordLimbsToNat
          (memoryWordsFrom mem sP.toNat (2 * words + 1)) =
        Modexp.sosOffDiagonal UInt256.size
          ((memoryWordsFrom mem aP.toNat words).map UInt256.toNat))
    (hdouble : selectSOSDoublePhase doubleFuel sEnd {
        carry := ⟨0⟩
        ptr := sP
        memory := mem
        activeWords := aw } = some double)
    (hdiagonal : selectSOSDiagonalLoop diagonalFuel carryFuel aEnd fixedDrop drop {
        sOff := sP
        aOff := aP
        memory := double.final.memory
        activeWords := double.final.activeWords } = some diagonal) :
    (Modexp.wordLimbsToNat
          (memoryWordsFrom diagonal.final.memory sP.toNat (2 * words + 1)) =
        Modexp.wordLimbsToNat (memoryWordsFrom mem aP.toNat words) ^ 2) ∧
      MemoryCovered diagonal.final.memory diagonal.final.activeWords ∧
      diagonal.final.activeWords.toNat * 32 < UInt256.size ∧
      diagonal.final.memory.size = mem.size ∧
      (∀ ptr count, ptr + 32 * count ≤ sP.toNat →
        memoryWordsFrom diagonal.final.memory ptr count =
          memoryWordsFrom mem ptr count) := by
  let totalWords := 2 * words + 1
  let doubleState : SOSDoubleState := {
    carry := ⟨0⟩
    ptr := sP
    memory := mem
    activeWords := aw }
  let operands := memoryWordsFrom mem aP.toNat words
  let digits := operands.map UInt256.toNat
  have hdoubleStop' : sEnd.toNat = doubleState.ptr.toNat + 32 * totalWords := by
    simpa only [doubleState, totalWords] using hdoubleStop
  have hdoubleFit : doubleState.ptr.toNat + 32 * totalWords + 31 < UInt256.size := by
    simpa only [doubleState, totalWords] using hsFit
  have hdoubleRange : doubleState.ptr.toNat + 32 * totalWords ≤
      doubleState.memory.size := by
    simpa only [doubleState, totalWords] using hsRange
  have hdoubleSelect : selectSOSDoublePhase doubleFuel sEnd doubleState = some double := by
    simpa only [doubleState] using hdouble
  have hwrites : ∀ j, j < totalWords →
      let current := sosDoubleIterate j doubleState
      current.ptr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := sosDoubleIterate j doubleState
    have hcurrent := sosDoubleIterate_coverage j doubleState hcovered hawFit
      (by dsimp only [doubleState, totalWords]; omega)
      (by dsimp only [doubleState, totalWords]; omega)
    have hptr := sosDoubleIterate_ptr_toNat j doubleState (by
      dsimp only [doubleState, totalWords]
      omega)
    change (sosDoubleIterate j doubleState).ptr.toNat + 32 ≤
      (sosDoubleIterate j doubleState).memory.size
    rw [hptr, hcurrent.2.2]
    dsimp only [doubleState, totalWords]
    omega
  have hoperandFrame := selectedSOSDoublePhase_memoryWords_below totalWords
    aP.toNat words hdoubleStop (by omega) (by omega) hwrites hdouble
  have hoperandFrame' : memoryWordsFrom double.final.memory aP.toNat words = operands := by
    simpa only [operands] using hoperandFrame
  have hdoubleFrame : ∀ ptr count, ptr + 32 * count ≤ sP.toNat →
      memoryWordsFrom double.final.memory ptr count = memoryWordsFrom mem ptr count := by
    intro ptr count hbelow
    exact selectedSOSDoublePhase_memoryWords_below totalWords ptr count hdoubleStop'
      (by omega) hbelow hwrites hdoubleSelect
  have hoperandBound := Modexp.wordLimbsToNat_lt_pow operands
  have hoperandLength : operands.length = words := memoryWordsFrom_length _ _ _
  rw [hoperandLength] at hoperandBound
  have hoperandSquareBound : Modexp.wordLimbsToNat operands ^ 2 <
      UInt256.size ^ totalWords := by
    simpa only [totalWords] using
      square_lt_radix_pow_two_mul_add_one hoperandBound (by decide)
  have hsquareModel := Modexp.sos_square_decompose UInt256.size digits
  have hoperandModel : Modexp.limbsToNatAt UInt256.size digits =
      Modexp.wordLimbsToNat operands := by
    simpa only [digits] using (Modexp.wordLimbsToNat_eq_limbsToNatAt operands).symm
  rw [hoperandModel] at hsquareModel
  have hpureBound : 2 * Modexp.sosOffDiagonal UInt256.size digits +
        Modexp.sosDiagonal UInt256.size digits < UInt256.size ^ totalWords := by
    rw [hsquareModel]
    exact hoperandSquareBound
  have hoffDiagonal' : Modexp.wordLimbsToNat
        (memoryWordsFrom mem sP.toNat totalWords) =
      Modexp.sosOffDiagonal UInt256.size digits := by
    simpa only [totalWords, digits, operands] using hoffDiagonal
  have htwiceBound : 2 * Modexp.sosOffDiagonal UInt256.size digits <
      UInt256.size ^ totalWords := by
    omega
  have hdoubleResult := selectedSOSDoublePhase_exact_of_bound
    (fuel := doubleFuel) (stop := sEnd) (state := doubleState) (selected := double)
    totalWords hdoubleStop' hdoubleFit hdoubleRange
    (by simpa only [doubleState] using hcovered)
    (by simpa only [doubleState] using hawFit)
    (by rfl) (by simpa only [doubleState] using hoffDiagonal') htwiceBound hdoubleSelect
  have hdoubleExact : Modexp.wordLimbsToNat
        (memoryWordsFrom double.final.memory sP.toNat totalWords) =
      2 * Modexp.sosOffDiagonal UInt256.size digits := by
    simpa only [doubleState] using hdoubleResult.1
  have hdiagonalBound : Modexp.wordLimbsToNat
          (memoryWordsFrom double.final.memory sP.toNat totalWords) +
        Modexp.sosDiagonal UInt256.size
          ((memoryWordsFrom double.final.memory aP.toNat words).map UInt256.toNat) <
      UInt256.size ^ totalWords := by
    rw [hoperandFrame', hdoubleExact]
    simpa only [digits, operands] using hpureBound
  let diagonalState : SOSDiagonalLoopState := {
    sOff := sP
    aOff := aP
    memory := double.final.memory
    activeWords := double.final.activeWords }
  have hdiagonalStop : aEnd.toNat = diagonalState.aOff.toNat + 32 * words := by
    simpa only [diagonalState] using haStop
  have hdiagonalAFit : diagonalState.aOff.toNat + 32 * words + 31 < UInt256.size := by
    simpa only [diagonalState] using haFit
  have hdiagonalSFit : diagonalState.sOff.toNat + 32 * (2 * words + 1) + 31 <
      UInt256.size := by
    simpa only [diagonalState] using hsFit
  have hdiagonalSeparate : aEnd.toNat ≤ diagonalState.sOff.toNat := by
    simpa only [diagonalState] using hseparate
  have hdiagonalRange : diagonalState.sOff.toNat + 32 * (2 * words + 1) ≤
      diagonalState.memory.size := by
    simpa only [diagonalState, doubleState] using
      (show sP.toNat + 32 * (2 * words + 1) ≤ double.final.memory.size by
        rw [hdoubleResult.2.2.2]
        exact hsRange)
  have hdiagonalCovered : MemoryCovered diagonalState.memory
      diagonalState.activeWords := by
    simpa only [diagonalState] using hdoubleResult.2.1
  have hdiagonalAwFit : diagonalState.activeWords.toNat * 32 < UInt256.size := by
    simpa only [diagonalState] using hdoubleResult.2.2.1
  have hdiagonalBound' : Modexp.wordLimbsToNat
          (memoryWordsFrom diagonalState.memory diagonalState.sOff.toNat
            (2 * words + 1)) +
        Modexp.sosDiagonal UInt256.size
          ((memoryWordsFrom diagonalState.memory diagonalState.aOff.toNat words).map
            UInt256.toNat) <
      UInt256.size ^ (2 * words + 1) := by
    simpa only [diagonalState, totalWords] using hdiagonalBound
  have hdiagonalSelect : selectSOSDiagonalLoop diagonalFuel carryFuel aEnd fixedDrop drop
      diagonalState = some diagonal := by
    simpa only [diagonalState] using hdiagonal
  have hdiagonalValue := selectedSOSDiagonalLoop_value
    (rowFuel := diagonalFuel) (carryFuel := carryFuel) (stop := aEnd)
    (fixedDrop := fixedDrop) (drop := drop) (state := diagonalState)
    (selected := diagonal) words hdiagonalStop hdiagonalAFit hdiagonalSFit
    hdiagonalSeparate hdiagonalRange hdiagonalCovered hdiagonalAwFit hdiagonalBound'
    hdiagonalSelect
  have hdiagonalCoverage := selectedSOSDiagonalLoop_coverage
    (rowFuel := diagonalFuel) (carryFuel := carryFuel) (stop := aEnd)
    (fixedDrop := fixedDrop) (drop := drop) (state := diagonalState)
    (selected := diagonal) words hdiagonalStop hdiagonalAFit hdiagonalSFit
    hdiagonalSeparate hdiagonalRange hdiagonalCovered hdiagonalAwFit hdiagonalBound'
    hdiagonalSelect
  have hvalue : Modexp.wordLimbsToNat
        (memoryWordsFrom diagonal.final.memory sP.toNat totalWords) =
      Modexp.wordLimbsToNat operands ^ 2 := by
    rw [hdiagonalValue.1, hdoubleExact, hoperandFrame']
    change 2 * Modexp.sosOffDiagonal UInt256.size digits +
        Modexp.sosDiagonal UInt256.size digits = Modexp.wordLimbsToNat operands ^ 2
    exact hsquareModel
  exact ⟨by simpa only [totalWords, operands] using hvalue,
    hdiagonalCoverage.1, hdiagonalCoverage.2.1,
    hdiagonalCoverage.2.2.trans hdoubleResult.2.2.2,
    by
      intro ptr count hbelow
      exact (hdiagonalValue.2 ptr count hbelow).trans (hdoubleFrame ptr count hbelow)⟩

end Modexp.MultiLimbMontgomerySOSSemantic
