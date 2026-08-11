import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSDiagonalContract

/-! # SOS diagonal outer-loop semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Coverage, exact guarded loads, and byte-array size after the generated fixed diagonal body. -/
theorem sosDiagonal_fixed_coverage
    (mem : ByteArray) (aw sOff aOff : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haFit : aOff.toNat + 32 + 31 < UInt256.size)
    (hsFit : sOff.toNat + 64 + 31 < UInt256.size)
    (haRange : aOff.toNat + 32 ≤ mem.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size) :
    MemoryCovered (sosDiagonalMemory mem aw sOff aOff) (sosDiagonalAw aw sOff aOff) ∧
      (sosDiagonalAw aw sOff aOff).toNat * 32 < UInt256.size ∧
      (sosDiagonalMemory mem aw sOff aOff).size = mem.size ∧
      (sosDiagonalAi mem aw aOff).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ∧
      (sosDiagonalLowPrior mem aw sOff aOff).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem sOff.toNat ∧
      (sosDiagonalHighPrior mem aw sOff aOff).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem (sOff.toNat + 32) := by
  let aw1 := sosDiagonalAw1 aw aOff
  let aw2 := sosDiagonalAw2 aw sOff aOff
  let mem1 := sosDiagonalMemory1 mem aw sOff aOff
  let aw3 := sosDiagonalAw3 aw sOff aOff
  let highPtr := sOff + ⟨32⟩
  let aw4 := sosDiagonalAw4 aw sOff aOff
  have hsStep : highPtr.toNat = sOff.toNat + 32 := by
    dsimp only [highPtr]
    exact uadd_word_lit32_toNat sOff (by omega)
  have hcov1 := readWords1_coverage mem aw aOff hcovered hawFit haFit
  have hcov2 := readWords1_coverage mem aw1 sOff
    (by simpa only [aw1, sosDiagonalAw1] using hcov1.1)
    (by simpa only [aw1, sosDiagonalAw1] using hcov1.2) (by omega)
  have hwrite1 := write32_coverage (sosDiagonalLow mem aw sOff aOff) mem aw2 sOff
    (by simpa only [aw2, sosDiagonalAw2, aw1, sosDiagonalAw1] using hcov2.1)
    (by simpa only [aw2, sosDiagonalAw2, aw1, sosDiagonalAw1] using hcov2.2)
    (by omega)
    (by rw [Nat.sub_eq_zero_of_le (by omega : sOff.toNat ≤ mem.size)]
        exact lt_usize 0 (by norm_num))
  have hmem1Size : mem1.size = mem.size := by
    dsimp only [mem1, sosDiagonalMemory1]
    exact write_size_of_inBounds_from _ _ 0 sOff.toNat 32 (by decide)
      (by rw [toByteArray_size]) (by omega)
  have hcov3 : MemoryCovered mem1 aw3 ∧ aw3.toNat * 32 < UInt256.size := by
    simpa only [mem1, aw3, aw2, sosDiagonalMemory1, sosDiagonalAw3, readWords1] using
      hwrite1
  have hcov4 := readWords1_coverage mem1 aw3 highPtr hcov3.1 hcov3.2 (by
    rw [hsStep]
    omega)
  have hwrite2 := write32_coverage (sosDiagonalHigh mem aw sOff aOff) mem1 aw4 highPtr
    (by simpa only [aw4, sosDiagonalAw4, highPtr] using hcov4.1)
    (by simpa only [aw4, sosDiagonalAw4, highPtr] using hcov4.2)
    (by rw [hsStep]; omega)
    (by rw [hmem1Size, hsStep, Nat.sub_eq_zero_of_le
          (by omega : sOff.toNat + 32 ≤ mem.size)]
        exact lt_usize 0 (by norm_num))
  have hfinalCoverage :
      MemoryCovered (sosDiagonalMemory mem aw sOff aOff)
          (sosDiagonalAw aw sOff aOff) ∧
        (sosDiagonalAw aw sOff aOff).toNat * 32 < UInt256.size := by
    simpa only [sosDiagonalMemory, sosDiagonalAw, mem1, aw4, highPtr, readWords1] using
      hwrite2
  have hfinalSize : (sosDiagonalMemory mem aw sOff aOff).size = mem.size := by
    unfold sosDiagonalMemory
    rw [show (sOff + ⟨32⟩).toNat = sOff.toNat + 32 by exact hsStep]
    rw [write_size_of_inBounds_from _ _ 0 (sOff.toNat + 32) 32 (by decide)
      (by rw [toByteArray_size]) (by rw [hmem1Size]; omega), hmem1Size]
  have hai := readWord_toNat_of_covered mem aw aOff hcovered hawFit haRange
  have hlow := readWord_toNat_of_covered mem aw1 sOff
    (by simpa only [aw1, sosDiagonalAw1] using hcov1.1)
    (by simpa only [aw1, sosDiagonalAw1] using hcov1.2) (by omega)
  have hhigh := readWord_toNat_of_covered mem1 aw3 highPtr hcov3.1 hcov3.2 (by
    rw [hmem1Size, hsStep]
    omega)
  refine ⟨hfinalCoverage.1, hfinalCoverage.2, hfinalSize, ?_, ?_, ?_⟩
  · simpa only [sosDiagonalAi] using hai
  · simpa only [sosDiagonalLowPrior, aw1, sosDiagonalAw1] using hlow
  · rw [show Modexp.MultiLimbMemoryModel.memoryWordNat mem1 highPtr.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem (sOff.toNat + 32) by
      rw [hsStep]
      apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
      have hframe := memoryWordsFrom_write_below
        (sosDiagonalLow mem aw sOff aOff).toByteArray mem sOff.toNat
        (sOff.toNat + 32) 1 (by rw [toByteArray_size]) (by omega) (by omega)
      simpa only [mem1, sosDiagonalMemory1] using hframe] at hhigh
    simpa only [sosDiagonalHighPrior, mem1, aw3, highPtr] using hhigh

theorem sosPropagateAdvance_coverage
    (state : SOSPropagateState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : state.ptr.toNat + 32 + 31 < UInt256.size)
    (hwrite : state.ptr.toNat + 32 ≤ state.memory.size) :
    MemoryCovered (sosPropagateAdvance state).memory
        (sosPropagateAdvance state).activeWords ∧
      (sosPropagateAdvance state).activeWords.toNat * 32 < UInt256.size ∧
      (sosPropagateAdvance state).memory.size = state.memory.size := by
  let aw1 := sosPropagateAw1 state.activeWords state.ptr
  have hread := readWords1_coverage state.memory state.activeWords state.ptr
    hcovered hawFit hptrFit
  have hwriteCoverage := write32_coverage
    (sosPropagateValue state.memory state.activeWords state.ptr state.carry)
    state.memory aw1 state.ptr
    (by simpa only [aw1, sosPropagateAw1] using hread.1)
    (by simpa only [aw1, sosPropagateAw1] using hread.2)
    hptrFit
    (by rw [Nat.sub_eq_zero_of_le (by omega : state.ptr.toNat ≤ state.memory.size)]
        exact lt_usize 0 (by norm_num))
  have hsize : (sosPropagateAdvance state).memory.size = state.memory.size := by
    dsimp only [sosPropagateAdvance, sosPropagateMemory]
    rw [write_size_of_inBounds_from _ _ 0 state.ptr.toNat 32 (by decide)
      (by rw [toByteArray_size]) hwrite]
  refine ⟨?_, ?_, hsize⟩
  · simpa only [sosPropagateAdvance, sosPropagateMemory, sosPropagateAw,
      aw1, sosPropagateAw1, readWords1] using hwriteCoverage.1
  · simpa only [sosPropagateAdvance, sosPropagateAw, aw1, sosPropagateAw1,
      readWords1] using hwriteCoverage.2

theorem sosPropagateIterate_coverage
    (n : Nat) (state : SOSPropagateState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : state.ptr.toNat + 32 * n + 31 < UInt256.size)
    (hrange : state.ptr.toNat + 32 * n ≤ state.memory.size) :
    MemoryCovered (sosPropagateIterate n state).memory
        (sosPropagateIterate n state).activeWords ∧
      (sosPropagateIterate n state).activeWords.toNat * 32 < UInt256.size ∧
      (sosPropagateIterate n state).memory.size = state.memory.size := by
  induction n generalizing state with
  | zero => exact ⟨hcovered, hawFit, rfl⟩
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hfirst := sosPropagateAdvance_coverage state hcovered hawFit (by omega) (by omega)
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosPropagateAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hrest := ih next hfirst.1 hfirst.2.1
        (by rw [hstep]; omega)
        (by rw [hstep, hfirst.2.2]; omega)
      simpa only [sosPropagateIterate, next] using
        ⟨hrest.1, hrest.2.1, hrest.2.2.trans hfirst.2.2⟩

/-- A successful propagation selector stops no later than any positive iterate whose carry is
already zero. -/
theorem selectedSOSPropagation_words_le_of_iterate_zero
    {fuel n : Nat} {state : SOSPropagateState} {selected : SOSPropagateSelection}
    (hstate : state.carry ≠ ⟨0⟩)
    (hselect : selectSOSPropagation fuel state = some selected)
    (hzero : (sosPropagateIterate n state).carry = ⟨0⟩) :
    selected.words ≤ n := by
  induction fuel generalizing n state selected with
  | zero => simp [selectSOSPropagation] at hselect
  | succ fuel ih =>
      simp only [selectSOSPropagation] at hselect
      let next := sosPropagateAdvance state
      by_cases hnext : next.carry = ⟨0⟩
      · rw [if_pos hnext] at hselect
        injection hselect with heq
        subst selected
        have hn : 0 < n := by
          by_contra hnzero
          have : n = 0 := by omega
          subst n
          exact hstate (by simpa only [sosPropagateIterate] using hzero)
        change (1 : Nat) ≤ n
        exact hn
      · rw [if_neg hnext] at hselect
        cases hrest : selectSOSPropagation fuel next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            cases n with
            | zero => exact (hstate hzero).elim
            | succ n =>
                have hrestZero : (sosPropagateIterate n next).carry = ⟨0⟩ := by
                  simpa only [next, sosPropagateIterate] using hzero
                have hle := ih hnext hrest hrestZero
                change rest.words + 1 ≤ n + 1
                omega

theorem sosPropagateIterate_carry_zero_of_bound
    (n : Nat) (state : SOSPropagateState)
    (hbound : Modexp.wordLimbsToNat (sosPropagateInputWords n state) +
      state.carry.toNat < UInt256.size ^ n) :
    (sosPropagateIterate n state).carry = ⟨0⟩ := by
  have hrecompose := sosPropagateCollectors_recompose n state
  apply u256_inj
  change (sosPropagateIterate n state).carry.toNat = 0
  by_contra hnonzero
  have hcarry : 0 < (sosPropagateIterate n state).carry.toNat := by omega
  have hpow : 0 < UInt256.size ^ n := pow_pos (by decide) _
  have hlower : UInt256.size ^ n ≤
      UInt256.size ^ n * (sosPropagateIterate n state).carry.toNat := by
    nlinarith
  omega

/-- Concrete memory obligations for one selected diagonal row.  These are exactly the guarded
loads and bounded stores used by `selectedSOSDiagonal_suffix_value`. -/
structure SOSDiagonalRowLayout
    (totalWords : Nat) (mem : ByteArray) (aw sOff aOff : UInt256)
    (selected : SOSDiagonalSelection) : Prop where
  scratchFit : sOff.toNat + 64 < UInt256.size
  scratchRange : sOff.toNat + 64 ≤ mem.size
  sourceLoad : (sosDiagonalAi mem aw aOff).toNat =
    Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat
  lowLoad : (sosDiagonalLowPrior mem aw sOff aOff).toNat =
    Modexp.MultiLimbMemoryModel.memoryWordNat mem sOff.toNat
  highLoad : (sosDiagonalHighPrior mem aw sOff aOff).toNat =
    Modexp.MultiLimbMemoryModel.memoryWordNat mem (sOff.toNat + 32)
  propagationFit :
    let carry := sosDiagonalCarry mem aw sOff aOff
    let propState : SOSPropagateState := {
      carry := carry
      ptr := sOff + ⟨64⟩
      memory := sosDiagonalMemory mem aw sOff aOff
      activeWords := sosDiagonalAw aw sOff aOff }
    propState.ptr.toNat + 32 * selected.propagatedWords < UInt256.size
  propagationLoads : ∀ j, j < selected.propagatedWords →
    let carry := sosDiagonalCarry mem aw sOff aOff
    let propState : SOSPropagateState := {
      carry := carry
      ptr := sOff + ⟨64⟩
      memory := sosDiagonalMemory mem aw sOff aOff
      activeWords := sosDiagonalAw aw sOff aOff }
    let current := sosPropagateIterate j propState
    (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat
  propagationWrites : ∀ j, j < selected.propagatedWords →
    let carry := sosDiagonalCarry mem aw sOff aOff
    let propState : SOSPropagateState := {
      carry := carry
      ptr := sOff + ⟨64⟩
      memory := sosDiagonalMemory mem aw sOff aOff
      activeWords := sosDiagonalAw aw sOff aOff }
    let current := sosPropagateIterate j propState
    current.ptr.toNat + 32 ≤ current.memory.size
  propagationWindow : 2 + selected.propagatedWords ≤ totalWords

/-- Covered allocated memory discharges every row obligation once carry propagation is known to
remain inside the row's remaining scratch suffix. -/
theorem selectedSOSDiagonal_rowLayout_of_coverage
    (totalWords : Nat) {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haFit : aOff.toNat + 32 + 31 < UInt256.size)
    (hsFit : sOff.toNat + 32 * totalWords + 31 < UInt256.size)
    (haRange : aOff.toNat + 32 ≤ mem.size)
    (hsRange : sOff.toNat + 32 * totalWords ≤ mem.size)
    (hwindow : 2 + selected.propagatedWords ≤ totalWords)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    SOSDiagonalRowLayout totalWords mem aw sOff aOff selected := by
  have htwo : 2 ≤ totalWords := by omega
  have hfixed := sosDiagonal_fixed_coverage mem aw sOff aOff hcovered hawFit haFit
    (by omega) haRange (by omega)
  let propState : SOSPropagateState := {
    carry := sosDiagonalCarry mem aw sOff aOff
    ptr := sOff + ⟨64⟩
    memory := sosDiagonalMemory mem aw sOff aOff
    activeWords := sosDiagonalAw aw sOff aOff }
  have hs64 : propState.ptr.toNat = sOff.toNat + 64 := by
    dsimp only [propState]
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hpropFit : propState.ptr.toNat + 32 * selected.propagatedWords <
      UInt256.size := by
    rw [hs64]
    omega
  have hpropRange : propState.ptr.toNat + 32 * selected.propagatedWords ≤
      propState.memory.size := by
    rw [hs64]
    change sOff.toNat + 64 + 32 * selected.propagatedWords ≤
      (sosDiagonalMemory mem aw sOff aOff).size
    rw [hfixed.2.2.1]
    omega
  have hpropLoads : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j propState
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
    intro j hj
    let current := sosPropagateIterate j propState
    have hiter := sosPropagateIterate_coverage j propState hfixed.1 hfixed.2.1
      (by omega) (by omega)
    have hptr := sosPropagateIterate_ptr_toNat j propState (by omega)
    have hword : current.ptr.toNat + 32 ≤ current.memory.size := by
      change (sosPropagateIterate j propState).ptr.toNat + 32 ≤
        (sosPropagateIterate j propState).memory.size
      rw [hptr, hiter.2.2]
      omega
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.ptr hiter.1 hiter.2.1 hword
    simpa only [current, sosPropagateWord] using hload
  have hpropWrites : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j propState
      current.ptr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := sosPropagateIterate j propState
    have hiter := sosPropagateIterate_coverage j propState hfixed.1 hfixed.2.1
      (by omega) (by omega)
    have hptr := sosPropagateIterate_ptr_toNat j propState (by omega)
    change (sosPropagateIterate j propState).ptr.toNat + 32 ≤
      (sosPropagateIterate j propState).memory.size
    rw [hptr, hiter.2.2]
    omega
  refine {
    scratchFit := by omega
    scratchRange := by omega
    sourceLoad := hfixed.2.2.2.1
    lowLoad := hfixed.2.2.2.2.1
    highLoad := hfixed.2.2.2.2.2
    propagationFit := ?_
    propagationLoads := ?_
    propagationWrites := ?_
    propagationWindow := hwindow }
  · simpa only [propState] using hpropFit
  · intro j hj
    simpa only [propState] using hpropLoads j hj
  · intro j hj
    simpa only [propState] using hpropWrites j hj

theorem selectedSOSDiagonal_coverage_of_layout
    (totalWords : Nat) {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haFit : aOff.toNat + 32 + 31 < UInt256.size)
    (hsFit : sOff.toNat + 32 * totalWords + 31 < UInt256.size)
    (haRange : aOff.toNat + 32 ≤ mem.size)
    (hsRange : sOff.toNat + 32 * totalWords ≤ mem.size)
    (hwindow : 2 + selected.propagatedWords ≤ totalWords)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    MemoryCovered selected.finalMemory selected.finalActiveWords ∧
      selected.finalActiveWords.toNat * 32 < UInt256.size ∧
      selected.finalMemory.size = mem.size := by
  have hfixed := sosDiagonal_fixed_coverage mem aw sOff aOff hcovered hawFit haFit
    (by omega) haRange (by omega)
  let carry := sosDiagonalCarry mem aw sOff aOff
  let propState : SOSPropagateState := {
    carry := carry
    ptr := sOff + ⟨64⟩
    memory := sosDiagonalMemory mem aw sOff aOff
    activeWords := sosDiagonalAw aw sOff aOff }
  have hs64 : propState.ptr.toNat = sOff.toNat + 64 := by
    dsimp only [propState]
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt (by omega)]
  unfold selectSOSDiagonal at hselect
  dsimp only at hselect
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    exact ⟨hfixed.1, hfixed.2.1, hfixed.2.2.1⟩
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation carryFuel propState with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        change 2 + propagation.words ≤ totalWords at hwindow
        have hiter := sosPropagateIterate_coverage propagation.words propState
          hfixed.1 hfixed.2.1
          (by rw [hs64]; omega)
          (by rw [hs64]; change _ ≤ (sosDiagonalMemory mem aw sOff aOff).size
              rw [hfixed.2.2.1]
              omega)
        have hfinal := selectedSOSPropagation_final_eq_iterate hprop
        rw [hfinal]
        exact ⟨hiter.1, hiter.2.1, hiter.2.2.trans hfixed.2.2.1⟩

/-- A diagonal carry run fits in the remaining scratch suffix whenever adding the current square
stays below that suffix's full radix capacity. -/
theorem selectedSOSDiagonal_propagation_window
    (totalWords : Nat) {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (htwo : 2 ≤ totalWords)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haFit : aOff.toNat + 32 + 31 < UInt256.size)
    (hsFit : sOff.toNat + 32 * totalWords + 31 < UInt256.size)
    (haRange : aOff.toNat + 32 ≤ mem.size)
    (hsRange : sOff.toNat + 32 * totalWords ≤ mem.size)
    (hbound : Modexp.wordLimbsToNat
          (memoryWordsFrom mem sOff.toNat totalWords) +
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 <
          UInt256.size ^ totalWords)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    2 + selected.propagatedWords ≤ totalWords := by
  let carry := sosDiagonalCarry mem aw sOff aOff
  let diagonalMemory := sosDiagonalMemory mem aw sOff aOff
  let diagonalAw := sosDiagonalAw aw sOff aOff
  let propState : SOSPropagateState := {
    carry := carry
    ptr := sOff + ⟨64⟩
    memory := diagonalMemory
    activeWords := diagonalAw }
  let suffixWords := totalWords - 2
  have htotal : totalWords = 2 + suffixWords := by
    dsimp only [suffixWords]
    omega
  have hfixed := sosDiagonal_fixed_coverage mem aw sOff aOff hcovered hawFit haFit
    (by omega) haRange (by omega)
  have hs64 : propState.ptr.toNat = sOff.toNat + 64 := by
    dsimp only [propState]
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt (by omega)]
  unfold selectSOSDiagonal at hselect
  dsimp only at hselect
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    omega
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation carryFuel propState with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        have hpropFit : propState.ptr.toNat + 32 * suffixWords + 31 <
            UInt256.size := by
          rw [hs64]
          omega
        have hpropRange : propState.ptr.toNat + 32 * suffixWords ≤
            propState.memory.size := by
          rw [hs64]
          change sOff.toNat + 64 + 32 * suffixWords ≤ diagonalMemory.size
          rw [show diagonalMemory.size = mem.size by
            simpa only [diagonalMemory] using hfixed.2.2.1]
          omega
        have hloads : ∀ j, j < suffixWords →
            let current := sosPropagateIterate j propState
            (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
              Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
          intro j hj
          let current := sosPropagateIterate j propState
          have hiter := sosPropagateIterate_coverage j propState hfixed.1 hfixed.2.1
            (by omega) (by omega)
          have hptr := sosPropagateIterate_ptr_toNat j propState (by omega)
          have hword : current.ptr.toNat + 32 ≤ current.memory.size := by
            change (sosPropagateIterate j propState).ptr.toNat + 32 ≤
              (sosPropagateIterate j propState).memory.size
            rw [hptr, hiter.2.2]
            omega
          have hload := readWord_toNat_of_covered current.memory current.activeWords
            current.ptr hiter.1 hiter.2.1 hword
          simpa only [current, sosPropagateWord] using hload
        have hwrites : ∀ j, j < suffixWords →
            let current := sosPropagateIterate j propState
            current.ptr.toNat + 32 ≤ current.memory.size := by
          intro j hj
          let current := sosPropagateIterate j propState
          have hiter := sosPropagateIterate_coverage j propState hfixed.1 hfixed.2.1
            (by omega) (by omega)
          have hptr := sosPropagateIterate_ptr_toNat j propState (by omega)
          change (sosPropagateIterate j propState).ptr.toNat + 32 ≤
            (sosPropagateIterate j propState).memory.size
          rw [hptr, hiter.2.2]
          omega
        have hinput := sosPropagateInputWords_eq_initialMemory suffixWords propState
          (by omega) hloads hwrites
        have hfixedValue := sosDiagonalMemory_twoWords_value mem aw sOff aOff
          (by omega) (by omega) hfixed.2.2.2.1 hfixed.2.2.2.2.1
          hfixed.2.2.2.2.2
        have hframe := sosDiagonalMemory_memoryWords_above mem aw sOff aOff
          propState.ptr.toNat suffixWords (by omega) (by omega) (by rw [hs64])
        have hsplit := memoryWordsFrom_add mem sOff.toNat 2 suffixWords
        have hsplitPoint : sOff.toNat + 32 * 2 = propState.ptr.toNat := by
          calc
            sOff.toNat + 32 * 2 = sOff.toNat + 64 := by omega
            _ = propState.ptr.toNat := hs64.symm
        rw [hsplitPoint] at hsplit
        rw [htotal, hsplit, Modexp.wordLimbsToNat_append,
          memoryWordsFrom_length] at hbound
        have hsuffixBound :
            Modexp.wordLimbsToNat (sosPropagateInputWords suffixWords propState) +
              propState.carry.toNat < UInt256.size ^ suffixWords := by
          rw [hinput, hframe]
          change _ + carry.toNat < _
          change Modexp.wordLimbsToNat (memoryWordsFrom diagonalMemory sOff.toNat 2) +
              UInt256.size ^ 2 * carry.toNat = _ at hfixedValue
          rw [pow_add] at hbound
          have hscaled : UInt256.size ^ 2 *
                (Modexp.wordLimbsToNat
                    (memoryWordsFrom mem propState.ptr.toNat suffixWords) + carry.toNat) <
              UInt256.size ^ 2 * UInt256.size ^ suffixWords := by
            rw [Nat.mul_add]
            omega
          exact (Nat.mul_lt_mul_left (pow_pos (by decide) 2)).mp hscaled
        have hcarryZero := sosPropagateIterate_carry_zero_of_bound suffixWords propState
          hsuffixBound
        have hwords := selectedSOSPropagation_words_le_of_iterate_zero hzero hprop hcarryZero
        change 2 + propagation.words ≤ totalWords
        omega

theorem SOSDiagonalRowLayout.value
    {totalWords carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (layout : SOSDiagonalRowLayout totalWords mem aw sOff aOff selected)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory sOff.toNat totalWords) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sOff.toNat totalWords) +
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 :=
  selectedSOSDiagonal_suffix_value totalWords layout.scratchFit layout.scratchRange
    layout.sourceLoad layout.lowLoad layout.highLoad layout.propagationFit
    layout.propagationLoads layout.propagationWrites layout.propagationWindow hselect

theorem SOSDiagonalRowLayout.frameBelow
    {totalWords carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (layout : SOSDiagonalRowLayout totalWords mem aw sOff aOff selected)
    (ptr count : Nat) (hbelow : ptr + 32 * count ≤ sOff.toNat)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    memoryWordsFrom selected.finalMemory ptr count = memoryWordsFrom mem ptr count :=
  selectedSOSDiagonal_memoryWords_below ptr count layout.scratchFit layout.scratchRange
    layout.propagationFit layout.propagationWrites hbelow hselect

/-- Row-by-row validity for the exact selector recursion.  The remaining-row argument fixes the
scratch suffix width used by the arithmetic induction. -/
def SOSDiagonalLoopLayout : Nat → Nat → Nat → UInt256 → UInt256 →
    SOSDiagonalLoopState → Prop
  | _, 0, _, _, _, _ => False
  | rows, rowFuel + 1, carryFuel, stop, fixedDrop, state =>
      if state.aOff.lt stop = ⟨0⟩ then
        rows = 0
      else
        match hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => False
        | some row =>
            0 < rows ∧
              SOSDiagonalRowLayout (2 * rows + 1) state.memory state.activeWords
                state.sOff state.aOff row ∧
              SOSDiagonalLoopLayout (rows - 1) rowFuel carryFuel stop fixedDrop
                (sosDiagonalLoopAdvance state row)

/-- The only data-dependent allocation fact needed by diagonal execution: every selected carry
run terminates before leaving the remaining scratch suffix. -/
def SOSDiagonalLoopWindows : Nat → Nat → Nat → UInt256 → UInt256 →
    SOSDiagonalLoopState → Prop
  | _, 0, _, _, _, _ => False
  | rows, rowFuel + 1, carryFuel, stop, fixedDrop, state =>
      if state.aOff.lt stop = ⟨0⟩ then
        rows = 0
      else
        match selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => False
        | some row =>
            0 < rows ∧ 2 + row.propagatedWords ≤ 2 * rows + 1 ∧
              SOSDiagonalLoopWindows (rows - 1) rowFuel carryFuel stop fixedDrop
                (sosDiagonalLoopAdvance state row)

theorem SOSDiagonalLoopWindows.of_bound
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop drop : UInt256}
    (state : SOSDiagonalLoopState) (selected : SOSDiagonalLoopSelection)
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsFit : state.sOff.toNat + 32 * (2 * rows + 1) + 31 < UInt256.size)
    (hseparate : stop.toNat ≤ state.sOff.toNat)
    (hsRange : state.sOff.toNat + 32 * (2 * rows + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbound : Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.sOff.toNat (2 * rows + 1)) +
        Modexp.sosDiagonal UInt256.size
          ((memoryWordsFrom state.memory state.aOff.toNat rows).map UInt256.toNat) <
        UInt256.size ^ (2 * rows + 1))
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop drop state =
      some selected) :
    SOSDiagonalLoopWindows rows rowFuel carryFuel stop fixedDrop state := by
  induction rowFuel generalizing rows state selected drop with
  | zero => simp [selectSOSDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSDiagonalLoop] at hselect
      simp only [SOSDiagonalLoopWindows]
      by_cases hexit : state.aOff.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect ⊢
        injection hselect with heq
        subst selected
        by_contra hrows
        have hpos : 0 < rows := by omega
        have hcontinue : state.aOff.lt stop ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        exact hcontinue hexit
      · rw [if_neg hexit] at hselect ⊢
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            let next := sosDiagonalLoopAdvance state row
            cases hrest : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop fixedDrop
                next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have hrows : 0 < rows := by
                  by_contra hnot
                  have : rows = 0 := by omega
                  subst rows
                  have hexit' : state.aOff.lt stop = ⟨0⟩ := by
                    apply ult_zero
                    omega
                  exact hexit hexit'
                have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hsStep : next.sOff.toNat = state.sOff.toNat + 64 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                    Nat.mod_eq_of_lt (by omega)]
                have haRange : state.aOff.toNat + 32 ≤ state.memory.size := by omega
                have hopSplit : memoryWordsFrom state.memory state.aOff.toNat rows =
                    UInt256.ofNat
                        (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                          state.aOff.toNat) ::
                      memoryWordsFrom state.memory next.aOff.toNat (rows - 1) := by
                  rw [show rows = (rows - 1) + 1 by omega]
                  simp only [memoryWordsFrom]
                  rw [haStep]
                  congr 1
                rw [hopSplit] at hbound
                simp only [List.map_cons, Modexp.sosDiagonal,
                  UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] at hbound
                have hrowBound :
                    Modexp.wordLimbsToNat
                        (memoryWordsFrom state.memory state.sOff.toNat (2 * rows + 1)) +
                      Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                          state.aOff.toNat ^ 2 <
                        UInt256.size ^ (2 * rows + 1) := by
                  omega
                have hwindow := selectedSOSDiagonal_propagation_window
                  (2 * rows + 1) (by omega) hcovered hawFit (by omega) hsFit
                  haRange hsRange hrowBound hrow
                have hrowLayout := selectedSOSDiagonal_rowLayout_of_coverage
                  (2 * rows + 1) hcovered hawFit (by omega) hsFit haRange hsRange
                  hwindow hrow
                have hrowCoverage := selectedSOSDiagonal_coverage_of_layout
                  (2 * rows + 1) hcovered hawFit (by omega) hsFit haRange hsRange
                  hwindow hrow
                have hrowValue := hrowLayout.value hrow
                have hrowOperands := hrowLayout.frameBelow next.aOff.toNat (rows - 1)
                  (by rw [haStep]; omega) hrow
                let tailWords := 2 * (rows - 1) + 1
                have htotal : 2 * rows + 1 = 2 + tailWords := by
                  dsimp only [tailWords]
                  omega
                have hsplit := memoryWordsFrom_add row.finalMemory state.sOff.toNat
                  2 tailWords
                have hsplitPoint : state.sOff.toNat + 32 * 2 = next.sOff.toNat := by
                  calc
                    state.sOff.toNat + 32 * 2 = state.sOff.toNat + 64 := by omega
                    _ = next.sOff.toNat := hsStep.symm
                rw [hsplitPoint] at hsplit
                have hrestBound :
                    Modexp.wordLimbsToNat
                          (memoryWordsFrom row.finalMemory next.sOff.toNat tailWords) +
                        Modexp.sosDiagonal UInt256.size
                          ((memoryWordsFrom row.finalMemory next.aOff.toNat
                            (rows - 1)).map UInt256.toNat) <
                      UInt256.size ^ tailWords := by
                  rw [hrowOperands]
                  rw [htotal, hsplit, Modexp.wordLimbsToNat_append,
                    memoryWordsFrom_length] at hrowValue
                  rw [htotal, pow_add] at hbound
                  have hscaled : UInt256.size ^ 2 *
                        (Modexp.wordLimbsToNat
                            (memoryWordsFrom row.finalMemory next.sOff.toNat tailWords) +
                          Modexp.sosDiagonal UInt256.size
                            ((memoryWordsFrom state.memory next.aOff.toNat
                              (rows - 1)).map UInt256.toNat)) <
                      UInt256.size ^ 2 * UInt256.size ^ tailWords := by
                    rw [Nat.mul_add]
                    omega
                  exact (Nat.mul_lt_mul_left (pow_pos (by decide) 2)).mp hscaled
                have hrestStop : stop.toNat = next.aOff.toNat + 32 * (rows - 1) := by
                  rw [haStep]
                  omega
                have hrestAFit : next.aOff.toNat + 32 * (rows - 1) + 31 <
                    UInt256.size := by
                  rw [haStep]
                  omega
                have hrestSFit : next.sOff.toNat + 32 * tailWords + 31 <
                    UInt256.size := by
                  rw [hsStep]
                  dsimp only [tailWords]
                  omega
                have hrestSeparate : stop.toNat ≤ next.sOff.toNat := by
                  rw [hsStep]
                  omega
                have hrestRange : next.sOff.toNat + 32 * tailWords ≤ next.memory.size := by
                  change next.sOff.toNat + 32 * tailWords ≤ row.finalMemory.size
                  rw [hsStep, hrowCoverage.2.2]
                  dsimp only [tailWords]
                  omega
                refine ⟨hrows, hwindow, ?_⟩
                exact ih (rows - 1) next rest hrestStop hrestAFit
                  (by simpa only [tailWords] using hrestSFit) hrestSeparate
                  (by simpa only [tailWords] using hrestRange)
                  hrowCoverage.1 hrowCoverage.2.1
                  (by simpa only [tailWords] using hrestBound) hrest

theorem SOSDiagonalLoopLayout.of_coverage
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop : UInt256}
    (state : SOSDiagonalLoopState)
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsFit : state.sOff.toNat + 32 * (2 * rows + 1) + 31 < UInt256.size)
    (hseparate : stop.toNat ≤ state.sOff.toNat)
    (hsRange : state.sOff.toNat + 32 * (2 * rows + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (windows : SOSDiagonalLoopWindows rows rowFuel carryFuel stop fixedDrop state) :
    SOSDiagonalLoopLayout rows rowFuel carryFuel stop fixedDrop state := by
  induction rowFuel generalizing rows state with
  | zero => simp [SOSDiagonalLoopWindows] at windows
  | succ rowFuel ih =>
      simp only [SOSDiagonalLoopWindows] at windows
      simp only [SOSDiagonalLoopLayout]
      by_cases hexit : state.aOff.lt stop = ⟨0⟩
      · rw [if_pos hexit] at windows ⊢
        exact windows
      · rw [if_neg hexit] at windows ⊢
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none =>
            simp only [hrow] at windows ⊢
        | some row =>
            simp only [hrow] at windows ⊢
            change 0 < rows ∧ 2 + row.propagatedWords ≤ 2 * rows + 1 ∧
                SOSDiagonalLoopWindows (rows - 1) rowFuel carryFuel stop fixedDrop
                  (sosDiagonalLoopAdvance state row) at windows
            rcases windows with ⟨hrows, hwindow, hrestWindows⟩
            let next := sosDiagonalLoopAdvance state row
            have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
              dsimp only [next, sosDiagonalLoopAdvance]
              exact uadd_word_lit32_toNat state.aOff (by omega)
            have hsStep : next.sOff.toNat = state.sOff.toNat + 64 := by
              dsimp only [next, sosDiagonalLoopAdvance]
              rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                Nat.mod_eq_of_lt (by omega)]
            have haRange : state.aOff.toNat + 32 ≤ state.memory.size := by omega
            have hrowLayout := selectedSOSDiagonal_rowLayout_of_coverage
              (2 * rows + 1) hcovered hawFit (by omega) hsFit haRange hsRange
              hwindow hrow
            have hrowCoverage := selectedSOSDiagonal_coverage_of_layout
              (2 * rows + 1) hcovered hawFit (by omega) hsFit haRange hsRange
              hwindow hrow
            have hrestStop : stop.toNat = next.aOff.toNat + 32 * (rows - 1) := by
              rw [haStep]
              omega
            have hrestAFit : next.aOff.toNat + 32 * (rows - 1) + 31 <
                UInt256.size := by
              rw [haStep]
              omega
            have hrestSFit : next.sOff.toNat + 32 * (2 * (rows - 1) + 1) + 31 <
                UInt256.size := by
              rw [hsStep]
              omega
            have hrestSeparate : stop.toNat ≤ next.sOff.toNat := by
              rw [hsStep]
              omega
            have hrestRange : next.sOff.toNat + 32 * (2 * (rows - 1) + 1) ≤
                next.memory.size := by
              change next.sOff.toNat + 32 * (2 * (rows - 1) + 1) ≤
                row.finalMemory.size
              rw [hsStep, hrowCoverage.2.2]
              omega
            refine ⟨hrows, hrowLayout, ?_⟩
            exact ih (rows - 1) next hrestStop hrestAFit hrestSFit hrestSeparate
              hrestRange hrowCoverage.1 hrowCoverage.2.1 hrestWindows

/-- Every selected diagonal row preserves covered memory and byte-array size.  The window
predicate is produced from the same partial-square bound used by the value theorem. -/
theorem selectedSOSDiagonalLoop_coverage_of_windows
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop drop : UInt256}
    {state : SOSDiagonalLoopState} {selected : SOSDiagonalLoopSelection}
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsFit : state.sOff.toNat + 32 * (2 * rows + 1) + 31 < UInt256.size)
    (hseparate : stop.toNat ≤ state.sOff.toNat)
    (hsRange : state.sOff.toNat + 32 * (2 * rows + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (windows : SOSDiagonalLoopWindows rows rowFuel carryFuel stop fixedDrop state)
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop drop state =
      some selected) :
    MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
  induction rowFuel generalizing rows state selected drop with
  | zero => simp [selectSOSDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSDiagonalLoop] at hselect
      simp only [SOSDiagonalLoopWindows] at windows
      by_cases hexit : state.aOff.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect windows
        injection hselect with heq
        subst selected
        exact ⟨hcovered, hawFit, rfl⟩
      · rw [if_neg hexit] at hselect windows
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => rw [hrow] at hselect windows; contradiction
        | some row =>
            rw [hrow] at hselect windows
            dsimp only at hselect
            rcases windows with ⟨hrows, hwindow, hrestWindows⟩
            let next := sosDiagonalLoopAdvance state row
            cases hrest : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop fixedDrop
                next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hsStep : next.sOff.toNat = state.sOff.toNat + 64 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                    Nat.mod_eq_of_lt (by omega)]
                have haRange : state.aOff.toNat + 32 ≤ state.memory.size := by omega
                have hrowCoverage := selectedSOSDiagonal_coverage_of_layout
                  (2 * rows + 1) hcovered hawFit (by omega) hsFit haRange hsRange
                  hwindow hrow
                have hrestCoverage := ih (rows - 1) (state := next) (selected := rest)
                  (by rw [haStep]; omega)
                  (by rw [haStep]; omega)
                  (by rw [hsStep]; omega)
                  (by rw [hsStep]; omega)
                  (by
                    change next.sOff.toNat + 32 * (2 * (rows - 1) + 1) ≤
                      row.finalMemory.size
                    rw [hsStep, hrowCoverage.2.2]
                    omega)
                  hrowCoverage.1 hrowCoverage.2.1 hrestWindows hrest
                exact ⟨hrestCoverage.1, hrestCoverage.2.1,
                  hrestCoverage.2.2.trans hrowCoverage.2.2⟩

theorem selectedSOSDiagonalLoop_coverage
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop drop : UInt256}
    {state : SOSDiagonalLoopState} {selected : SOSDiagonalLoopSelection}
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsFit : state.sOff.toNat + 32 * (2 * rows + 1) + 31 < UInt256.size)
    (hseparate : stop.toNat ≤ state.sOff.toNat)
    (hsRange : state.sOff.toNat + 32 * (2 * rows + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbound : Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.sOff.toNat (2 * rows + 1)) +
        Modexp.sosDiagonal UInt256.size
          ((memoryWordsFrom state.memory state.aOff.toNat rows).map UInt256.toNat) <
        UInt256.size ^ (2 * rows + 1))
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop drop state =
      some selected) :
    MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
  have windows := SOSDiagonalLoopWindows.of_bound rows state selected hstop haFit hsFit
    hseparate hsRange hcovered hawFit hbound hselect
  exact selectedSOSDiagonalLoop_coverage_of_windows rows hstop haFit hsFit hseparate
    hsRange hcovered hawFit windows hselect

/-- Every selected diagonal row is composed into the pure diagonal polynomial.  The accompanying
frame result is part of the induction because later rows start two scratch limbs higher. -/
theorem selectedSOSDiagonalLoop_value_and_frame
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop drop : UInt256}
    {state : SOSDiagonalLoopState} {selected : SOSDiagonalLoopSelection}
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsFit : state.sOff.toNat + 32 * (2 * rows + 1) < UInt256.size)
    (hseparate : stop.toNat ≤ state.sOff.toNat)
    (layout : SOSDiagonalLoopLayout rows rowFuel carryFuel stop fixedDrop state)
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop drop state =
      some selected) :
    (Modexp.wordLimbsToNat
          (memoryWordsFrom selected.final.memory state.sOff.toNat (2 * rows + 1)) =
        Modexp.wordLimbsToNat
            (memoryWordsFrom state.memory state.sOff.toNat (2 * rows + 1)) +
          Modexp.sosDiagonal UInt256.size
            ((memoryWordsFrom state.memory state.aOff.toNat rows).map UInt256.toNat)) ∧
      (∀ ptr count, ptr + 32 * count ≤ state.sOff.toNat →
        memoryWordsFrom selected.final.memory ptr count =
          memoryWordsFrom state.memory ptr count) := by
  induction rowFuel generalizing rows state selected drop with
  | zero => simp [selectSOSDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSDiagonalLoop] at hselect
      simp only [SOSDiagonalLoopLayout] at layout
      by_cases hexit : state.aOff.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect layout
        subst rows
        injection hselect with heq
        subst selected
        constructor
        · simp only [memoryWordsFrom, List.map, Modexp.sosDiagonal, Nat.add_zero]
        · intro ptr count hbelow
          rfl
      · rw [if_neg hexit] at hselect layout
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => rw [hrow] at hselect layout; contradiction
        | some row =>
            rw [hrow] at hselect layout
            dsimp only at hselect
            rcases layout with ⟨hrows, hrowLayout, hrestLayout⟩
            let next := sosDiagonalLoopAdvance state row
            cases hrest : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop fixedDrop
                next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have haStep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hsStep : next.sOff.toNat = state.sOff.toNat + 64 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
                    Nat.mod_eq_of_lt (by omega)]
                have hrestStop : stop.toNat = next.aOff.toNat + 32 * (rows - 1) := by
                  rw [haStep]
                  omega
                have hrestAFit : next.aOff.toNat + 32 * (rows - 1) + 31 <
                    UInt256.size := by
                  rw [haStep]
                  omega
                have hrestSFit : next.sOff.toNat + 32 * (2 * (rows - 1) + 1) <
                    UInt256.size := by
                  rw [hsStep]
                  omega
                have hrestSeparate : stop.toNat ≤ next.sOff.toNat := by
                  rw [hsStep]
                  omega
                have hrecursive := ih (rows - 1) hrestStop hrestAFit hrestSFit
                  hrestSeparate hrestLayout hrest
                change Modexp.wordLimbsToNat
                      (memoryWordsFrom rest.final.memory next.sOff.toNat
                        (2 * (rows - 1) + 1)) =
                    Modexp.wordLimbsToNat
                        (memoryWordsFrom row.finalMemory next.sOff.toNat
                          (2 * (rows - 1) + 1)) +
                      Modexp.sosDiagonal UInt256.size
                        ((memoryWordsFrom row.finalMemory next.aOff.toNat
                          (rows - 1)).map UInt256.toNat) ∧ _ at hrecursive
                have hrowValue := hrowLayout.value hrow
                have hrowOperands := hrowLayout.frameBelow next.aOff.toNat (rows - 1)
                  (by rw [haStep]; omega) hrow
                have hfirstBelow : state.sOff.toNat + 32 * 2 ≤ next.sOff.toNat := by
                  rw [hsStep]
                have hfirstTwo := hrecursive.2 state.sOff.toNat 2 hfirstBelow
                change memoryWordsFrom rest.final.memory state.sOff.toNat 2 =
                    memoryWordsFrom row.finalMemory state.sOff.toNat 2 at hfirstTwo
                have hfinalSplit := memoryWordsFrom_add rest.final.memory state.sOff.toNat
                  2 (2 * (rows - 1) + 1)
                have hrowSplit := memoryWordsFrom_add row.finalMemory state.sOff.toNat
                  2 (2 * (rows - 1) + 1)
                have hsplitPoint : state.sOff.toNat + 32 * 2 = next.sOff.toNat := by
                  calc
                    state.sOff.toNat + 32 * 2 = state.sOff.toNat + 64 := by omega
                    _ = next.sOff.toNat := hsStep.symm
                rw [hsplitPoint] at hfinalSplit hrowSplit
                have htotal : 2 * rows + 1 = 2 + (2 * (rows - 1) + 1) := by omega
                rw [htotal, hrowSplit, Modexp.wordLimbsToNat_append,
                  memoryWordsFrom_length] at hrowValue
                constructor
                · change Modexp.wordLimbsToNat
                      (memoryWordsFrom rest.final.memory state.sOff.toNat (2 * rows + 1)) = _
                  rw [htotal, hfinalSplit, Modexp.wordLimbsToNat_append,
                    memoryWordsFrom_length, hfirstTwo, hrecursive.1]
                  rw [hrowOperands]
                  rw [show memoryWordsFrom state.memory state.aOff.toNat rows =
                      UInt256.ofNat
                          (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
                            state.aOff.toNat) ::
                        memoryWordsFrom state.memory next.aOff.toNat (rows - 1) by
                    rw [show rows = (rows - 1) + 1 by omega]
                    simp only [memoryWordsFrom]
                    rw [haStep]
                    rfl]
                  simp only [List.map_cons, Modexp.sosDiagonal,
                    UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
                  rw [Nat.mul_add]
                  omega
                · intro ptr count hbelow
                  have hrestFrame := hrecursive.2 ptr count (by rw [hsStep]; omega)
                  have hrowFrame := hrowLayout.frameBelow ptr count hbelow hrow
                  exact hrestFrame.trans hrowFrame

/-- Complete diagonal-loop contract from the allocated-memory and partial-square bound.  All
data-dependent carry lengths and guarded memory accesses are discharged internally. -/
theorem selectedSOSDiagonalLoop_value
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop drop : UInt256}
    {state : SOSDiagonalLoopState} {selected : SOSDiagonalLoopSelection}
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (haFit : state.aOff.toNat + 32 * rows + 31 < UInt256.size)
    (hsFit : state.sOff.toNat + 32 * (2 * rows + 1) + 31 < UInt256.size)
    (hseparate : stop.toNat ≤ state.sOff.toNat)
    (hsRange : state.sOff.toNat + 32 * (2 * rows + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbound : Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.sOff.toNat (2 * rows + 1)) +
        Modexp.sosDiagonal UInt256.size
          ((memoryWordsFrom state.memory state.aOff.toNat rows).map UInt256.toNat) <
        UInt256.size ^ (2 * rows + 1))
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop drop state =
      some selected) :
    (Modexp.wordLimbsToNat
          (memoryWordsFrom selected.final.memory state.sOff.toNat (2 * rows + 1)) =
        Modexp.wordLimbsToNat
            (memoryWordsFrom state.memory state.sOff.toNat (2 * rows + 1)) +
          Modexp.sosDiagonal UInt256.size
            ((memoryWordsFrom state.memory state.aOff.toNat rows).map UInt256.toNat)) ∧
      (∀ ptr count, ptr + 32 * count ≤ state.sOff.toNat →
        memoryWordsFrom selected.final.memory ptr count =
          memoryWordsFrom state.memory ptr count) := by
  have windows := SOSDiagonalLoopWindows.of_bound rows state selected hstop haFit hsFit
    hseparate hsRange hcovered hawFit hbound hselect
  have layout := SOSDiagonalLoopLayout.of_coverage rows state hstop haFit hsFit
    hseparate hsRange hcovered hawFit windows
  exact selectedSOSDiagonalLoop_value_and_frame rows hstop haFit (by omega) hseparate
    layout hselect

end Modexp.MultiLimbMontgomerySOSSemantic
