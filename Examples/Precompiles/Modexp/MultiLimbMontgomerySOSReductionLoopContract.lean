import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSSquareContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSReductionContract

/-! # Complete SOS Montgomery reduction semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem montgomeryCIOSStep_add_high
    {radix modulus nInv low high k : Nat}
    (hradix : 1 < radix)
    (hinv : modulus * nInv % radix = radix - 1)
    (hk : 0 < k) :
    Modexp.montgomeryCIOSStep radix modulus nInv 0
        (low + radix ^ k * high) 0 =
      Modexp.montgomeryCIOSStep radix modulus nInv 0 low 0 +
        radix ^ (k - 1) * high := by
  have hfactor : Modexp.montgomeryFactor radix nInv (low + radix ^ k * high) =
      Modexp.montgomeryFactor radix nInv low := by
    unfold Modexp.montgomeryFactor
    have hpowMod : radix ^ k % radix = 0 := by
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      exact Nat.mul_mod_left _ _
    simp only [Nat.add_mod, Nat.mul_mod, hpowMod, zero_mul, Nat.zero_mod, add_zero,
      Nat.mod_mod]
  have hfull := Modexp.montgomeryCIOSStep_scale
    (radix := radix) (modulus := modulus) (nInv := nInv)
    (b := 0) (t := low + radix ^ k * high) (ai := 0) hradix hinv
  have hlow := Modexp.montgomeryCIOSStep_scale
    (radix := radix) (modulus := modulus) (nInv := nInv)
    (b := 0) (t := low) (ai := 0) hradix hinv
  simp only [Nat.zero_mul, add_zero, hfactor] at hfull
  simp only [Nat.zero_mul, add_zero] at hlow
  have hpow : radix ^ k = radix * radix ^ (k - 1) := by
    rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact Nat.mul_comm _ _
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < radix)
  calc
    radix * Modexp.montgomeryCIOSStep radix modulus nInv 0
          (low + radix ^ k * high) 0 =
        low + radix ^ k * high + Modexp.montgomeryFactor radix nInv low * modulus :=
      hfull
    _ = (low + Modexp.montgomeryFactor radix nInv low * modulus) +
          radix * (radix ^ (k - 1) * high) := by rw [hpow]; ring
    _ = radix * Modexp.montgomeryCIOSStep radix modulus nInv 0 low 0 +
          radix * (radix ^ (k - 1) * high) := by rw [hlow]
    _ = radix * (Modexp.montgomeryCIOSStep radix modulus nInv 0 low 0 +
          radix ^ (k - 1) * high) := by rw [Nat.mul_add]

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

theorem sosReductionIterate_memoryWords_above
    (factor : UInt256) (n : Nat) (state : SOSReductionState) (ptr count : Nat)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (habove : state.resultPtr.toNat + 32 * n ≤ ptr)
    (hwrites : ∀ j, j < n →
      let current := sosReductionIterate factor j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (sosReductionIterate factor n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      have hread := multiplyPassIterate_read_above factor n
        (sosReductionMultiplyState state) ptr (by
          intro j hj
          have hptr := multiplyPassIterate_resultPtr_toNat factor j
            (sosReductionMultiplyState state) (by
              simpa [sosReductionMultiplyState] using
                (show state.resultPtr.toNat + 32 * j < UInt256.size by omega))
          refine ⟨?_, ?_⟩
          · simpa only [← sosReductionMultiplyState_iterate] using hwrites j hj
          · rw [hptr]
            change state.resultPtr.toNat + 32 * j + 32 ≤ ptr
            omega)
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (sosReductionIterate factor n state).memory ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat state.memory ptr := by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        exact congrArg fromByteArrayBigEndian (by
          simpa only [← sosReductionMultiplyState_iterate] using hread)
      simp only [memoryWordsFrom]
      rw [hword, ih (ptr := ptr + 32) (by omega)]

theorem selectedSOSReductionBoundary_window_of_bound
    (totalWords : Nat) {fuel : Nat} {state : SOSPropagateState}
    {selected : SOSReductionBoundarySelection}
    (hbound : Modexp.wordLimbsToNat (sosPropagateInputWords totalWords state) +
      state.carry.toNat < UInt256.size ^ totalWords)
    (hselect : selectSOSReductionBoundary fuel state = some selected) :
    selected.propagatedWords ≤ totalWords := by
  unfold selectSOSReductionBoundary at hselect
  by_cases hzero : state.carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    simp
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation fuel state with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        have hcarryZero := sosPropagateIterate_carry_zero_of_bound totalWords state hbound
        exact selectedSOSPropagation_words_le_of_iterate_zero hzero hprop hcarryZero

structure SOSReductionBoundaryFacts
    (totalWords : Nat) (state : SOSPropagateState)
    (selected : SOSReductionBoundarySelection) : Prop where
  window : selected.propagatedWords ≤ totalWords
  loads : ∀ j, j < selected.propagatedWords →
    let current := sosPropagateIterate j state
    (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat
  writes : ∀ j, j < selected.propagatedWords →
    let current := sosPropagateIterate j state
    current.ptr.toNat + 32 ≤ current.memory.size
  finalCovered : MemoryCovered selected.final.memory selected.final.activeWords
  finalAwFit : selected.final.activeWords.toNat * 32 < UInt256.size
  finalSize : selected.final.memory.size = state.memory.size

theorem selectedSOSReductionBoundary_facts_of_coverage
    (totalWords : Nat) {fuel : Nat} {state : SOSPropagateState}
    {selected : SOSReductionBoundarySelection}
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hfit : state.ptr.toNat + 32 * totalWords + 31 < UInt256.size)
    (hrange : state.ptr.toNat + 32 * totalWords ≤ state.memory.size)
    (hbound : Modexp.wordLimbsToNat (sosPropagateInputWords totalWords state) +
      state.carry.toNat < UInt256.size ^ totalWords)
    (hselect : selectSOSReductionBoundary fuel state = some selected) :
    SOSReductionBoundaryFacts totalWords state selected := by
  have hwindow := selectedSOSReductionBoundary_window_of_bound totalWords hbound hselect
  have hloads : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j state
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
    intro j hj
    let current := sosPropagateIterate j state
    have hiter := sosPropagateIterate_coverage j state hcovered hawFit
      (by omega) (by omega)
    have hptr := sosPropagateIterate_ptr_toNat j state (by omega)
    have hword : current.ptr.toNat + 32 ≤ current.memory.size := by
      change (sosPropagateIterate j state).ptr.toNat + 32 ≤
        (sosPropagateIterate j state).memory.size
      rw [hptr, hiter.2.2]
      omega
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.ptr hiter.1 hiter.2.1 hword
    simpa only [current, sosPropagateWord] using hload
  have hwrites : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := sosPropagateIterate j state
    have hiter := sosPropagateIterate_coverage j state hcovered hawFit
      (by omega) (by omega)
    have hptr := sosPropagateIterate_ptr_toNat j state (by omega)
    change (sosPropagateIterate j state).ptr.toNat + 32 ≤
      (sosPropagateIterate j state).memory.size
    rw [hptr, hiter.2.2]
    omega
  have hfinal : MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size ∧
      selected.final.memory.size = state.memory.size := by
    unfold selectSOSReductionBoundary at hselect
    by_cases hzero : state.carry = ⟨0⟩
    · rw [if_pos hzero] at hselect
      injection hselect with heq
      subst selected
      exact ⟨hcovered, hawFit, rfl⟩
    · rw [if_neg hzero] at hselect
      cases hprop : selectSOSPropagation fuel state with
      | none => rw [hprop] at hselect; contradiction
      | some propagation =>
          rw [hprop] at hselect
          injection hselect with heq
          subst selected
          have hwords : propagation.words ≤ totalWords := by
            simpa using hwindow
          have hiter := sosPropagateIterate_coverage propagation.words state
            hcovered hawFit (by omega) (by omega)
          rw [selectedSOSPropagation_final_eq_iterate hprop]
          exact hiter
  exact {
    window := hwindow
    loads := hloads
    writes := hwrites
    finalCovered := hfinal.1
    finalAwFit := hfinal.2.1
    finalSize := hfinal.2.2 }

structure SOSReductionIterationFacts
    (factor : UInt256) (columns : Nat) (state : SOSReductionState) : Prop where
  loadsModulus : ∀ j, j < columns →
    let current := sosReductionIterate factor j state
    (schoolbookOperands current.memory current.activeWords current.modulusPtr
      current.resultPtr current.carry).1.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat
  loadsPrior : ∀ j, j < columns →
    let current := sosReductionIterate factor j state
    (schoolbookOperands current.memory current.activeWords current.modulusPtr
      current.resultPtr current.carry).2.1.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat
  writes : ∀ j, j < columns →
    let current := sosReductionIterate factor j state
    current.resultPtr.toNat + 32 ≤ current.memory.size
  finalCovered : MemoryCovered (sosReductionIterate factor columns state).memory
    (sosReductionIterate factor columns state).activeWords
  finalAwFit : (sosReductionIterate factor columns state).activeWords.toNat * 32 <
    UInt256.size
  finalSize : (sosReductionIterate factor columns state).memory.size = state.memory.size

theorem sosReductionIteration_facts_of_coverage
    (factor : UInt256) (columns : Nat) (state : SOSReductionState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hoperandFit : state.modulusPtr.toNat + 32 * columns + 31 < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * columns + 31 < UInt256.size)
    (hoperandRange : state.modulusPtr.toNat + 32 * columns ≤ state.memory.size)
    (hresultRange : state.resultPtr.toNat + 32 * columns ≤ state.memory.size) :
    SOSReductionIterationFacts factor columns state := by
  let multiplyState := sosReductionMultiplyState state
  have hinBounds := multiplyPassIterate_inBounds factor columns multiplyState
    (by simpa only [multiplyState, sosReductionMultiplyState] using
      (show state.resultPtr.toNat + 32 * columns < UInt256.size by omega))
    (by simpa only [multiplyState, sosReductionMultiplyState] using hresultRange)
  have hsteps : ∀ j, j < columns →
      let current := multiplyPassIterate factor j multiplyState
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := multiplyPassIterate factor j multiplyState
    have hop := multiplyPassIterate_operandPtr_toNat factor j multiplyState (by
      simpa only [multiplyState, sosReductionMultiplyState] using
        (show state.modulusPtr.toNat + 32 * j < UInt256.size by omega))
    have hresult := multiplyPassIterate_resultPtr_toNat factor j multiplyState (by
      simpa only [multiplyState, sosReductionMultiplyState] using
        (show state.resultPtr.toNat + 32 * j < UInt256.size by omega))
    refine ⟨?_, ?_, hinBounds.1 j hj⟩
    · change current.operandPtr.toNat + 32 + 31 < UInt256.size
      rw [show current.operandPtr.toNat = state.modulusPtr.toNat + 32 * j by
        simpa only [current, multiplyState, sosReductionMultiplyState] using hop]
      omega
    · change current.resultPtr.toNat + 32 + 31 < UInt256.size
      rw [show current.resultPtr.toNat = state.resultPtr.toNat + 32 * j by
        simpa only [current, multiplyState, sosReductionMultiplyState] using hresult]
      omega
  have hfinalCoverage := multiplyPassIterate_coverage factor columns multiplyState
    (by simpa only [multiplyState, sosReductionMultiplyState] using hcovered)
    (by simpa only [multiplyState, sosReductionMultiplyState] using hawFit) hsteps
  have hloadsModulus : ∀ j, j < columns →
      let current := sosReductionIterate factor j state
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat := by
    intro j hj
    let current := multiplyPassIterate factor j multiplyState
    have hcurrent := multiplyPassIterate_coverage factor j multiplyState
      (by simpa only [multiplyState, sosReductionMultiplyState] using hcovered)
      (by simpa only [multiplyState, sosReductionMultiplyState] using hawFit)
      (fun i hi => hsteps i (by omega))
    have hop := multiplyPassIterate_operandPtr_toNat factor j multiplyState (by
      simpa only [multiplyState, sosReductionMultiplyState] using
        (show state.modulusPtr.toNat + 32 * j < UInt256.size by omega))
    have hsize := (multiplyPassIterate_inBounds factor j multiplyState
      (by simpa only [multiplyState, sosReductionMultiplyState] using
        (show state.resultPtr.toNat + 32 * j < UInt256.size by omega))
      (by simpa only [multiplyState, sosReductionMultiplyState] using
        (show state.resultPtr.toNat + 32 * j ≤ state.memory.size by omega))).2
    have hword : current.operandPtr.toNat + 32 ≤ current.memory.size := by
      rw [hsize]
      change current.operandPtr.toNat + 32 ≤ state.memory.size
      rw [show current.operandPtr.toNat = state.modulusPtr.toNat + 32 * j by
        simpa only [current, multiplyState, sosReductionMultiplyState] using hop]
      omega
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.operandPtr hcurrent.1 hcurrent.2 hword
    simpa only [current, multiplyState, schoolbookOperands,
      ← sosReductionMultiplyState_iterate] using hload
  have hloadsPrior : ∀ j, j < columns →
      let current := sosReductionIterate factor j state
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
    intro j hj
    let current := multiplyPassIterate factor j multiplyState
    have hcurrent := multiplyPassIterate_coverage factor j multiplyState
      (by simpa only [multiplyState, sosReductionMultiplyState] using hcovered)
      (by simpa only [multiplyState, sosReductionMultiplyState] using hawFit)
      (fun i hi => hsteps i (by omega))
    have hstep := hsteps j hj
    have hoperand := readWords1_coverage current.memory current.activeWords
      current.operandPtr hcurrent.1 hcurrent.2 hstep.1
    have hload := readWord_toNat_of_covered current.memory
      (readWords1 current.activeWords current.operandPtr) current.resultPtr
      hoperand.1 hoperand.2 hstep.2.2
    simpa only [current, multiplyState, schoolbookOperands,
      ← sosReductionMultiplyState_iterate] using hload
  exact {
    loadsModulus := hloadsModulus
    loadsPrior := hloadsPrior
    writes := by
      intro j hj
      simpa only [multiplyState, ← sosReductionMultiplyState_iterate] using
        hinBounds.1 j hj
    finalCovered := by
      simpa only [multiplyState, ← sosReductionMultiplyState_iterate] using
        hfinalCoverage.1
    finalAwFit := by
      simpa only [multiplyState, ← sosReductionMultiplyState_iterate] using
        hfinalCoverage.2
    finalSize := by
      simpa only [multiplyState, ← sosReductionMultiplyState_iterate] using
        hinBounds.2 }

/-- The selected reduction boundary adds its incoming carry to any containing scratch suffix. -/
theorem selectedSOSReductionBoundary_suffix_value
    (totalWords : Nat) {fuel : Nat} {state : SOSPropagateState}
    {selected : SOSReductionBoundarySelection}
    (hfit : state.ptr.toNat + 32 * totalWords < UInt256.size)
    (hloads : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j state
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hwrites : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hwindow : selected.propagatedWords ≤ totalWords)
    (hselect : selectSOSReductionBoundary fuel state = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory state.ptr.toNat totalWords) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.ptr.toNat totalWords) + state.carry.toNat := by
  unfold selectSOSReductionBoundary at hselect
  by_cases hzero : state.carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    rw [hzero]
    rfl
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation fuel state with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        change propagation.words ≤ totalWords at hwindow
        have hpFit : state.ptr.toNat + 32 * propagation.words < UInt256.size := by omega
        have hpValue := selectedSOSPropagation_value_final state propagation hprop hpFit
          (by intro j hj; simpa using hloads j hj)
          (by intro j hj; simpa using hwrites j hj)
        let highWords := totalWords - propagation.words
        have htotal : totalWords = propagation.words + highWords := by
          dsimp only [highWords]
          omega
        have hpFrame := selectedSOSPropagation_memoryWords_above state propagation
          (state.ptr.toNat + 32 * propagation.words) highWords hprop hpFit
          (by omega) (by intro j hj; simpa using hwrites j hj)
        have hfinalSplit := memoryWordsFrom_add propagation.final.memory state.ptr.toNat
          propagation.words highWords
        have hinitialSplit := memoryWordsFrom_add state.memory state.ptr.toNat
          propagation.words highWords
        rw [htotal, hfinalSplit, hinitialSplit, Modexp.wordLimbsToNat_append,
          Modexp.wordLimbsToNat_append, memoryWordsFrom_length, hpFrame, hpValue]
        simp only [memoryWordsFrom_length]
        omega

/-- Boundary carry propagation preserves every word range below its first scratch write. -/
theorem selectedSOSReductionBoundary_memoryWords_below
    (totalWords : Nat) {fuel : Nat} {state : SOSPropagateState}
    {selected : SOSReductionBoundarySelection} (ptr count : Nat)
    (hfit : state.ptr.toNat + 32 * totalWords < UInt256.size)
    (hwrites : ∀ j, j < selected.propagatedWords →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hwindow : selected.propagatedWords ≤ totalWords)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat)
    (hselect : selectSOSReductionBoundary fuel state = some selected) :
    memoryWordsFrom selected.final.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  unfold selectSOSReductionBoundary at hselect
  by_cases hzero : state.carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    rw [← heq]
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation fuel state with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        rw [← heq] at hwrites hwindow ⊢
        change propagation.words ≤ totalWords at hwindow
        exact selectedSOSPropagation_memoryWords_below state propagation ptr count hprop
          (by omega) hbelow (by intro j hj; simpa using hwrites j hj)

/-- The pass selector's boundary state is exactly the peeled state followed by `columns - 1`
generated reduction columns. -/
theorem selectedSOSReductionPass_boundary_eq_iterationFinal
    (columns : Nat) {columnFuel carryFuel : Nat} {mem : ByteArray}
    {aw sBase nP n0inv nBefore nEnd : UInt256}
    {selected : SOSReductionPassSelection}
    (hcolumns : 0 < columns)
    (hnP : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nEnd.toNat = nP.toNat + 32 * columns)
    (hfit : nP.toNat + 32 * columns < UInt256.size)
    (hselect : selectSOSReductionPass columnFuel carryFuel mem aw sBase nP n0inv
      nBefore nEnd = some selected) :
    let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
    selectSOSReductionBoundary carryFuel {
      carry := final.carry
      ptr := final.resultPtr
      memory := final.memory
      activeWords := final.activeWords } = some selected.boundary := by
  let factor := sosReductionIterationFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
  unfold selectSOSReductionPass at hselect
  dsimp only at hselect
  by_cases hone : columns = 1
  · subst columns
    have hexit : initial.modulusPtr.lt nEnd = ⟨0⟩ := by
      apply ult_zero
      dsimp only [initial, sosReductionInitialState]
      rw [hnP, hnEnd]
    rw [if_pos hexit] at hselect
    cases hboundary : selectSOSReductionBoundary carryFuel {
        carry := initial.carry
        ptr := initial.resultPtr
        memory := initial.memory
        activeWords := initial.activeWords } with
    | none => rw [hboundary] at hselect; contradiction
    | some boundary =>
        rw [hboundary] at hselect
        injection hselect with heq
        subst selected
        simpa only [final, factor, initial, sosReductionIterationFinal,
          sosReductionIterate] using hboundary
  · have hmulti : 1 < columns := by omega
    have hcontinue : initial.modulusPtr.lt nEnd ≠ ⟨0⟩ := by
      rw [ult_one (by
        dsimp only [initial, sosReductionInitialState]
        rw [hnP, hnEnd]
        omega)]
      decide
    rw [if_neg hcontinue] at hselect
    cases hselectedColumns : selectSOSReductionColumns columnFuel factor nEnd initial with
    | none => rw [hselectedColumns] at hselect; contradiction
    | some selectedColumns =>
        rw [hselectedColumns] at hselect
        dsimp only at hselect
        cases hboundary : selectSOSReductionBoundary carryFuel {
            carry := selectedColumns.final.carry
            ptr := selectedColumns.final.resultPtr
            memory := selectedColumns.final.memory
            activeWords := selectedColumns.final.activeWords } with
        | none => rw [hboundary] at hselect; contradiction
        | some boundary =>
            rw [hboundary] at hselect
            injection hselect with heq
            subst selected
            have hwords := selectedSOSReductionColumns_words_eq_geometry
              (columns - 1) (state := initial) (selected := selectedColumns)
              (by omega)
              (by dsimp only [initial, sosReductionInitialState]; rw [hnP, hnEnd]; omega)
              (by dsimp only [initial, sosReductionInitialState]; rw [hnP]; omega)
              hselectedColumns
            have hfinal := selectedSOSReductionColumns_final_eq_iterate hselectedColumns
            rw [hwords] at hfinal
            rw [hfinal] at hboundary
            simpa only [final, factor, initial, sosReductionIterationFinal] using hboundary

/-- One selected outer reduction pass is one pure Montgomery step, including an arbitrary
untouched high scratch suffix consumed by the boundary carry propagation. -/
theorem selectedSOSReductionPass_value
    (columns highWords : Nat) {columnFuel carryFuel : Nat} {mem : ByteArray}
    {aw sBase nP n0inv nBefore nEnd : UInt256}
    {selected : SOSReductionPassSelection}
    (hcolumns : 0 < columns)
    (hsNext : (sBase + ⟨32⟩).toNat = sBase.toNat + 32)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : nEnd.toNat = nP.toNat + 32 * columns)
    (hselectorFit : nP.toNat + 32 * columns < UInt256.size)
    (hresultFit : (sBase + ⟨32⟩).toNat + 32 * (columns - 1) < UInt256.size)
    (hboundaryFit : (sBase + ⟨32⟩).toNat + 32 * (columns - 1 + highWords) <
      UInt256.size)
    (hoperandFit : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) <
      UInt256.size)
    (hseparate : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤
      (sBase + ⟨32⟩).toNat)
    (hinv : (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat % UInt256.size =
      UInt256.size - 1)
    (hpeeledValue : (sosPeeledValue mem aw sBase).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem sBase.toNat)
    (hpeeledN0 : (sosPeeledN0 mem aw sBase nP).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem nP.toNat)
    (hloadsModulus : ∀ j, j < columns - 1 →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat)
    (hloadsPrior : ∀ j, j < columns - 1 →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < columns - 1 →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hboundaryLoads :
      let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
      let state : SOSPropagateState := {
        carry := final.carry
        ptr := final.resultPtr
        memory := final.memory
        activeWords := final.activeWords }
      ∀ j, j < selected.boundary.propagatedWords →
        let current := sosPropagateIterate j state
        (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
          Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hboundaryWrites :
      let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
      let state : SOSPropagateState := {
        carry := final.carry
        ptr := final.resultPtr
        memory := final.memory
        activeWords := final.activeWords }
      ∀ j, j < selected.boundary.propagatedWords →
        let current := sosPropagateIterate j state
        current.ptr.toNat + 32 ≤ current.memory.size)
    (hboundaryWindow : selected.boundary.propagatedWords ≤ highWords)
    (hselect : selectSOSReductionPass columnFuel carryFuel mem aw sBase nP n0inv
      nBefore nEnd = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.boundary.final.memory (sBase + ⟨32⟩).toNat
          (columns - 1 + highWords)) =
      Modexp.montgomeryCIOSStep UInt256.size
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) n0inv.toNat 0
        (Modexp.wordLimbsToNat
          (memoryWordsFrom mem sBase.toNat (columns + highWords))) 0 := by
  let factor := sosPeeledFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
  let boundaryState : SOSPropagateState := {
    carry := final.carry
    ptr := final.resultPtr
    memory := final.memory
    activeWords := final.activeWords }
  let lowValue := Modexp.wordLimbsToNat (memoryWordsFrom mem sBase.toNat columns)
  let modulus := Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)
  let highValue := Modexp.wordLimbsToNat
    (memoryWordsFrom mem (sBase.toNat + 32 * columns) highWords)
  let coreValue := Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory (sBase + ⟨32⟩).toNat (columns - 1)) +
    UInt256.size ^ (columns - 1) * final.carry.toNat
  have hvalueSplit : lowValue = (sosPeeledValue mem aw sBase).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (memoryWordsFrom mem (sBase + ⟨32⟩).toNat (columns - 1)) := by
    dsimp only [lowValue]
    rw [show columns = (columns - 1) + 1 by omega]
    simp only [memoryWordsFrom, Modexp.wordLimbsToNat]
    rw [hsNext, hpeeledValue]
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
    congr 2
  have hmodulusSplit : modulus = (sosPeeledN0 mem aw sBase nP).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (memoryWordsFrom mem (nP + ⟨32⟩).toNat (columns - 1)) := by
    dsimp only [modulus]
    rw [show columns = (columns - 1) + 1 by omega]
    simp only [memoryWordsFrom, Modexp.wordLimbsToNat]
    rw [hnNext, hpeeledN0]
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
    congr 2
  have hcore : coreValue = Modexp.montgomeryCIOSStep UInt256.size modulus
      n0inv.toNat 0 lowValue 0 := by
    apply sosReductionPassMemory_eq_montgomeryStep mem aw sBase nP n0inv nBefore
      (columns - 1) lowValue modulus coreValue hinv hvalueSplit hmodulusSplit
    · rfl
    · exact hnBefore
    · exact hoperandFit
    · exact hresultFit
    · exact hseparate
    · exact hloadsModulus
    · exact hloadsPrior
    · exact hwrites
  have hboundarySelect : selectSOSReductionBoundary carryFuel boundaryState =
      some selected.boundary := by
    have hnBefore' : (nBefore + ⟨64⟩).toNat = nP.toNat + 32 :=
      hnBefore.trans hnNext
    simpa only [boundaryState, final] using
      selectedSOSReductionPass_boundary_eq_iterationFinal columns hcolumns hnBefore'
        hnEnd hselectorFit hselect
  have hfinalPtr : final.resultPtr.toNat = sBase.toNat + 32 * columns := by
    have hptr := multiplyPassIterate_resultPtr_toNat factor (columns - 1)
      (sosReductionMultiplyState initial) (by
        simpa only [initial, sosReductionInitialState] using hresultFit)
    have hptr' : final.resultPtr.toNat =
        (sBase + ⟨32⟩).toNat + 32 * (columns - 1) := by
      simpa only [final, sosReductionIterationFinal, factor, initial,
        sosReductionIterationFactor, sosReductionMultiplyState_iterate,
        sosReductionInitialState] using (show
        (sosReductionIterate factor (columns - 1) initial).resultPtr.toNat =
          (sBase + ⟨32⟩).toNat + 32 * (columns - 1) by
        simpa only [← sosReductionMultiplyState_iterate] using hptr)
    rw [hptr', hsNext]
    omega
  have hboundaryFit' : boundaryState.ptr.toNat + 32 * highWords < UInt256.size := by
    change final.resultPtr.toNat + 32 * highWords < UInt256.size
    rw [hsNext] at hboundaryFit
    rw [hfinalPtr]
    omega
  have hboundaryValue := selectedSOSReductionBoundary_suffix_value highWords
    hboundaryFit' hboundaryLoads hboundaryWrites hboundaryWindow hboundarySelect
  have hhighFrame : memoryWordsFrom final.memory final.resultPtr.toNat highWords =
      memoryWordsFrom mem final.resultPtr.toNat highWords := by
    have habove : initial.resultPtr.toNat + 32 * (columns - 1) ≤
        final.resultPtr.toNat := by
      dsimp only [initial, sosReductionInitialState]
      rw [hfinalPtr, hsNext]
      omega
    have hframe := sosReductionIterate_memoryWords_above factor (columns - 1) initial
      final.resultPtr.toNat highWords
      (by simpa only [initial, sosReductionInitialState] using hresultFit)
      habove hwrites
    simpa only [final, factor, initial, sosReductionIterationFinal,
      sosReductionInitialState] using hframe
  rw [hhighFrame] at hboundaryValue
  have hhighInitial : Modexp.wordLimbsToNat
        (memoryWordsFrom mem final.resultPtr.toNat highWords) = highValue := by
    rw [hfinalPtr]
  rw [hhighInitial] at hboundaryValue
  have hinputSplit : Modexp.wordLimbsToNat
        (memoryWordsFrom mem sBase.toNat (columns + highWords)) =
      lowValue + UInt256.size ^ columns * highValue := by
    rw [memoryWordsFrom_add, Modexp.wordLimbsToNat_append,
      memoryWordsFrom_length]
  have houtputSplit : Modexp.wordLimbsToNat
        (memoryWordsFrom selected.boundary.final.memory (sBase + ⟨32⟩).toNat
          (columns - 1 + highWords)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom selected.boundary.final.memory (sBase + ⟨32⟩).toNat
            (columns - 1)) +
        UInt256.size ^ (columns - 1) *
          Modexp.wordLimbsToNat
            (memoryWordsFrom selected.boundary.final.memory final.resultPtr.toNat highWords) := by
    rw [memoryWordsFrom_add, Modexp.wordLimbsToNat_append,
      memoryWordsFrom_length]
    rw [show (sBase + ⟨32⟩).toNat + 32 * (columns - 1) =
        final.resultPtr.toNat by rw [hfinalPtr, hsNext]; omega]
  have hcoreFrame : memoryWordsFrom selected.boundary.final.memory
        (sBase + ⟨32⟩).toNat (columns - 1) =
      memoryWordsFrom final.memory (sBase + ⟨32⟩).toNat (columns - 1) := by
    unfold selectSOSReductionBoundary at hboundarySelect
    by_cases hzero : boundaryState.carry = ⟨0⟩
    · rw [if_pos hzero] at hboundarySelect
      injection hboundarySelect with heq
      rw [← heq]
    · rw [if_neg hzero] at hboundarySelect
      cases hprop : selectSOSPropagation carryFuel boundaryState with
      | none => rw [hprop] at hboundarySelect; contradiction
      | some propagation =>
          rw [hprop] at hboundarySelect
          injection hboundarySelect with heq
          rw [← heq] at hboundaryWindow hboundaryWrites ⊢
          change propagation.words ≤ highWords at hboundaryWindow
          have hpFit : boundaryState.ptr.toNat + 32 * propagation.words <
              UInt256.size := by omega
          exact selectedSOSPropagation_memoryWords_below boundaryState propagation
            (sBase + ⟨32⟩).toNat (columns - 1) hprop hpFit
            (by
              change (sBase + ⟨32⟩).toNat + 32 * (columns - 1) ≤
                final.resultPtr.toNat
              rw [hfinalPtr, hsNext]
              omega)
            (by intro j hj; simpa using hboundaryWrites j hj)
  rw [houtputSplit, hcoreFrame, hboundaryValue, hinputSplit]
  have hinvFull : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1 := by
    have hhighMod :
        (UInt256.size * Modexp.wordLimbsToNat
            (memoryWordsFrom mem (nP + ⟨32⟩).toNat (columns - 1)) * n0inv.toNat) %
          UInt256.size = 0 := by
      rw [Nat.mul_assoc]
      exact Nat.mul_mod_right _ _
    rw [hmodulusSplit, Nat.add_mul, Nat.add_mod, hhighMod]
    simp only [Nat.add_zero, Nat.mod_mod]
    exact hinv
  have hstepHigh := montgomeryCIOSStep_add_high
    (radix := UInt256.size) (modulus := modulus) (nInv := n0inv.toNat)
    (low := lowValue) (high := highValue) (k := columns) (by decide) hinvFull hcolumns
  rw [hstepHigh, ← hcore]
  dsimp only [coreValue]
  ring

/-- If the pure value of a reduction pass fits in its output words, the concrete suffix and
incoming boundary carry fit in the suffix words.  This is the numeric fact that bounds the
selector's carry propagation without constraining the untouched suffix. -/
theorem sosReductionIteration_boundary_bound_of_step_bound
    (columns highWords : Nat) {mem : ByteArray}
    {aw sBase nP n0inv nBefore : UInt256}
    (hcolumns : 0 < columns)
    (hsNext : (sBase + ⟨32⟩).toNat = sBase.toNat + 32)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hresultFit : (sBase + ⟨32⟩).toNat + 32 * (columns - 1) < UInt256.size)
    (hoperandFit : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) <
      UInt256.size)
    (hseparate : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤
      (sBase + ⟨32⟩).toNat)
    (hinv : (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat % UInt256.size =
      UInt256.size - 1)
    (hpeeledValue : (sosPeeledValue mem aw sBase).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem sBase.toNat)
    (hpeeledN0 : (sosPeeledN0 mem aw sBase nP).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem nP.toNat)
    (hloadsModulus : ∀ j, j < columns - 1 →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat)
    (hloadsPrior : ∀ j, j < columns - 1 →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < columns - 1 →
      let current := sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) j
        (sosReductionInitialState mem aw sBase nP n0inv nBefore)
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hboundaryFit :
      let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
      final.resultPtr.toNat + 32 * highWords < UInt256.size)
    (hboundaryLoads :
      let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
      let state : SOSPropagateState := {
        carry := final.carry
        ptr := final.resultPtr
        memory := final.memory
        activeWords := final.activeWords }
      ∀ j, j < highWords →
        let current := sosPropagateIterate j state
        (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
          Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hboundaryWrites :
      let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
      let state : SOSPropagateState := {
        carry := final.carry
        ptr := final.resultPtr
        memory := final.memory
        activeWords := final.activeWords }
      ∀ j, j < highWords →
        let current := sosPropagateIterate j state
        current.ptr.toNat + 32 ≤ current.memory.size)
    (hstepBound : Modexp.montgomeryCIOSStep UInt256.size
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) n0inv.toNat 0
        (Modexp.wordLimbsToNat
          (memoryWordsFrom mem sBase.toNat (columns + highWords))) 0 <
      UInt256.size ^ (columns - 1 + highWords)) :
    let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
    let boundaryState : SOSPropagateState := {
      carry := final.carry
      ptr := final.resultPtr
      memory := final.memory
      activeWords := final.activeWords }
    Modexp.wordLimbsToNat (sosPropagateInputWords highWords boundaryState) +
      boundaryState.carry.toNat < UInt256.size ^ highWords := by
  let factor := sosPeeledFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
  let boundaryState : SOSPropagateState := {
    carry := final.carry
    ptr := final.resultPtr
    memory := final.memory
    activeWords := final.activeWords }
  let lowValue := Modexp.wordLimbsToNat (memoryWordsFrom mem sBase.toNat columns)
  let modulus := Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)
  let highValue := Modexp.wordLimbsToNat
    (memoryWordsFrom mem (sBase.toNat + 32 * columns) highWords)
  let coreValue := Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory (sBase + ⟨32⟩).toNat (columns - 1)) +
    UInt256.size ^ (columns - 1) * final.carry.toNat
  have hvalueSplit : lowValue = (sosPeeledValue mem aw sBase).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (memoryWordsFrom mem (sBase + ⟨32⟩).toNat (columns - 1)) := by
    dsimp only [lowValue]
    rw [show columns = (columns - 1) + 1 by omega]
    simp only [memoryWordsFrom, Modexp.wordLimbsToNat]
    rw [hsNext, hpeeledValue]
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
    congr 2
  have hmodulusSplit : modulus = (sosPeeledN0 mem aw sBase nP).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (memoryWordsFrom mem (nP + ⟨32⟩).toNat (columns - 1)) := by
    dsimp only [modulus]
    rw [show columns = (columns - 1) + 1 by omega]
    simp only [memoryWordsFrom, Modexp.wordLimbsToNat]
    rw [hnNext, hpeeledN0]
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
    congr 2
  have hcore : coreValue = Modexp.montgomeryCIOSStep UInt256.size modulus
      n0inv.toNat 0 lowValue 0 := by
    apply sosReductionPassMemory_eq_montgomeryStep mem aw sBase nP n0inv nBefore
      (columns - 1) lowValue modulus coreValue hinv hvalueSplit hmodulusSplit
    · rfl
    · exact hnBefore
    · exact hoperandFit
    · exact hresultFit
    · exact hseparate
    · exact hloadsModulus
    · exact hloadsPrior
    · exact hwrites
  have hfinalPtr : final.resultPtr.toNat = sBase.toNat + 32 * columns := by
    have hptr := multiplyPassIterate_resultPtr_toNat factor (columns - 1)
      (sosReductionMultiplyState initial) (by
        simpa only [initial, sosReductionInitialState] using hresultFit)
    have hptr' : final.resultPtr.toNat =
        (sBase + ⟨32⟩).toNat + 32 * (columns - 1) := by
      simpa only [final, sosReductionIterationFinal, factor, initial,
        sosReductionIterationFactor, sosReductionMultiplyState_iterate,
        sosReductionInitialState] using (show
        (sosReductionIterate factor (columns - 1) initial).resultPtr.toNat =
          (sBase + ⟨32⟩).toNat + 32 * (columns - 1) by
        simpa only [← sosReductionMultiplyState_iterate] using hptr)
    rw [hptr', hsNext]
    omega
  have hhighFrame : memoryWordsFrom final.memory final.resultPtr.toNat highWords =
      memoryWordsFrom mem final.resultPtr.toNat highWords := by
    have habove : initial.resultPtr.toNat + 32 * (columns - 1) ≤
        final.resultPtr.toNat := by
      dsimp only [initial, sosReductionInitialState]
      rw [hfinalPtr, hsNext]
      omega
    have hframe := sosReductionIterate_memoryWords_above factor (columns - 1) initial
      final.resultPtr.toNat highWords
      (by simpa only [initial, sosReductionInitialState] using hresultFit)
      habove hwrites
    simpa only [final, factor, initial, sosReductionIterationFinal,
      sosReductionInitialState] using hframe
  have hinput := sosPropagateInputWords_eq_initialMemory highWords boundaryState
    (by simpa only [boundaryState] using hboundaryFit) hboundaryLoads hboundaryWrites
  have hboundaryValue :
      Modexp.wordLimbsToNat (sosPropagateInputWords highWords boundaryState) =
        highValue := by
    rw [hinput]
    change Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory final.resultPtr.toNat highWords) = highValue
    rw [hhighFrame]
    dsimp only [highValue]
    rw [hfinalPtr]
  have hinputSplit : Modexp.wordLimbsToNat
        (memoryWordsFrom mem sBase.toNat (columns + highWords)) =
      lowValue + UInt256.size ^ columns * highValue := by
    rw [memoryWordsFrom_add, Modexp.wordLimbsToNat_append,
      memoryWordsFrom_length]
  have hinvFull : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1 := by
    have hhighMod :
        (UInt256.size * Modexp.wordLimbsToNat
            (memoryWordsFrom mem (nP + ⟨32⟩).toNat (columns - 1)) * n0inv.toNat) %
          UInt256.size = 0 := by
      rw [Nat.mul_assoc]
      exact Nat.mul_mod_right _ _
    rw [hmodulusSplit, Nat.add_mul, Nat.add_mod, hhighMod]
    simp only [Nat.add_zero, Nat.mod_mod]
    exact hinv
  have hstepHigh := montgomeryCIOSStep_add_high
    (radix := UInt256.size) (modulus := modulus) (nInv := n0inv.toNat)
    (low := lowValue) (high := highValue) (k := columns) (by decide) hinvFull hcolumns
  rw [hinputSplit, hstepHigh, ← hcore] at hstepBound
  change Modexp.wordLimbsToNat (sosPropagateInputWords highWords boundaryState) +
    boundaryState.carry.toNat < UInt256.size ^ highWords
  rw [hboundaryValue]
  dsimp only [coreValue] at hstepBound
  rw [pow_add] at hstepBound
  have hscaled : UInt256.size ^ (columns - 1) *
        (highValue + final.carry.toNat) <
      UInt256.size ^ (columns - 1) * UInt256.size ^ highWords := by
    rw [Nat.mul_add]
    omega
  exact (Nat.mul_lt_mul_left (pow_pos (by decide) (columns - 1))).mp hscaled

structure SOSReductionPassFacts
    (columns highWords : Nat) (mem : ByteArray) (sBase nP n0inv : UInt256)
    (selected : SOSReductionPassSelection) : Prop where
  value : Modexp.wordLimbsToNat
        (memoryWordsFrom selected.boundary.final.memory (sBase + ⟨32⟩).toNat
          (columns - 1 + highWords)) =
      Modexp.montgomeryCIOSStep UInt256.size
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) n0inv.toNat 0
        (Modexp.wordLimbsToNat
          (memoryWordsFrom mem sBase.toNat (columns + highWords))) 0
  finalCovered : MemoryCovered selected.boundary.final.memory
    selected.boundary.final.activeWords
  finalAwFit : selected.boundary.final.activeWords.toNat * 32 < UInt256.size
  finalSize : selected.boundary.final.memory.size = mem.size
  modulusFrame : memoryWordsFrom selected.boundary.final.memory nP.toNat columns =
    memoryWordsFrom mem nP.toNat columns

theorem selectedSOSReductionPass_facts_of_coverage
    (columns highWords : Nat) {columnFuel carryFuel : Nat} {mem : ByteArray}
    {aw sBase nP n0inv nBefore nEnd : UInt256}
    {selected : SOSReductionPassSelection}
    (hcolumns : 0 < columns)
    (hsNext : (sBase + ⟨32⟩).toNat = sBase.toNat + 32)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : nEnd.toNat = nP.toNat + 32 * columns)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hsFit : (sBase + ⟨32⟩).toNat + 32 * (columns - 1 + highWords) + 31 <
      UInt256.size)
    (hsRange : (sBase + ⟨32⟩).toNat + 32 * (columns - 1 + highWords) ≤
      mem.size)
    (hnFit : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) + 31 <
      UInt256.size)
    (hnRange : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤ mem.size)
    (hseparate : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤
      (sBase + ⟨32⟩).toNat)
    (hinv : Modexp.MultiLimbMemoryModel.memoryWordNat mem nP.toNat * n0inv.toNat %
      UInt256.size = UInt256.size - 1)
    (hstepBound : Modexp.montgomeryCIOSStep UInt256.size
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) n0inv.toNat 0
        (Modexp.wordLimbsToNat
          (memoryWordsFrom mem sBase.toNat (columns + highWords))) 0 <
      UInt256.size ^ (columns - 1 + highWords))
    (hselect : selectSOSReductionPass columnFuel carryFuel mem aw sBase nP n0inv
      nBefore nEnd = some selected) :
    SOSReductionPassFacts columns highWords mem sBase nP n0inv selected := by
  let factor := sosPeeledFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
  let boundaryState : SOSPropagateState := {
    carry := final.carry
    ptr := final.resultPtr
    memory := final.memory
    activeWords := final.activeWords }
  have hsReadFit : sBase.toNat + 32 + 31 < UInt256.size := by
    rw [hsNext] at hsFit
    omega
  have hsReadRange : sBase.toNat + 32 ≤ mem.size := by
    rw [hsNext] at hsRange
    omega
  have hnReadFit : nP.toNat + 32 + 31 < UInt256.size := by
    rw [hnBefore, hnNext] at hnFit
    omega
  have hnReadRange : nP.toNat + 32 ≤ mem.size := by
    rw [hnBefore, hnNext] at hnRange
    omega
  have hsRead := readWords1_coverage mem aw sBase hcovered hawFit hsReadFit
  have hnRead := readWords1_coverage mem (sosPeeledAw1 aw sBase) nP
    (by simpa only [sosPeeledAw1] using hsRead.1)
    (by simpa only [sosPeeledAw1] using hsRead.2) hnReadFit
  have hpeeledValue := readWord_toNat_of_covered mem aw sBase hcovered hawFit hsReadRange
  have hpeeledN0 := readWord_toNat_of_covered mem (sosPeeledAw1 aw sBase) nP
    (by simpa only [sosPeeledAw1] using hsRead.1)
    (by simpa only [sosPeeledAw1] using hsRead.2) hnReadRange
  have hinvRead : (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat %
      UInt256.size = UInt256.size - 1 := by
    rw [show (sosPeeledN0 mem aw sBase nP).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem nP.toNat by
        simpa only [sosPeeledN0, sosPeeledAw1] using hpeeledN0]
    exact hinv
  have hinitialCovered : MemoryCovered initial.memory initial.activeWords := by
    simpa only [initial, sosReductionInitialState, sosPeeledAw] using hnRead.1
  have hinitialAwFit : initial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [initial, sosReductionInitialState, sosPeeledAw] using hnRead.2
  have hiteration := sosReductionIteration_facts_of_coverage factor (columns - 1) initial
    hinitialCovered hinitialAwFit
    (by simpa only [initial, sosReductionInitialState] using hnFit)
    (by simpa only [initial, sosReductionInitialState] using
      (show (sBase + ⟨32⟩).toNat + 32 * (columns - 1) + 31 < UInt256.size by
        omega))
    (by simpa only [initial, sosReductionInitialState] using hnRange)
    (by simpa only [initial, sosReductionInitialState] using
      (show (sBase + ⟨32⟩).toNat + 32 * (columns - 1) ≤ mem.size by omega))
  have hboundarySelect : selectSOSReductionBoundary carryFuel boundaryState =
      some selected.boundary := by
    have hnBefore' : (nBefore + ⟨64⟩).toNat = nP.toNat + 32 :=
      hnBefore.trans hnNext
    simpa only [boundaryState, final] using
      selectedSOSReductionPass_boundary_eq_iterationFinal columns hcolumns hnBefore'
        hnEnd (by
          rw [hnBefore, hnNext] at hnFit
          omega) hselect
  have hfinalPtr : final.resultPtr.toNat =
      (sBase + ⟨32⟩).toNat + 32 * (columns - 1) := by
    have hptr := multiplyPassIterate_resultPtr_toNat factor (columns - 1)
      (sosReductionMultiplyState initial) (by
        simpa only [initial, sosReductionInitialState] using
          (show (sBase + ⟨32⟩).toNat + 32 * (columns - 1) < UInt256.size by
            omega))
    simpa only [final, sosReductionIterationFinal, factor, initial,
      sosReductionIterationFactor, ← sosReductionMultiplyState_iterate] using hptr
  have hboundaryCovered : MemoryCovered boundaryState.memory boundaryState.activeWords := by
    simpa only [boundaryState, final, sosReductionIterationFinal, factor, initial,
      sosReductionIterationFactor] using hiteration.finalCovered
  have hboundaryAwFit : boundaryState.activeWords.toNat * 32 < UInt256.size := by
    simpa only [boundaryState, final, sosReductionIterationFinal, factor, initial,
      sosReductionIterationFactor] using hiteration.finalAwFit
  have hboundaryFit : boundaryState.ptr.toNat + 32 * highWords + 31 <
      UInt256.size := by
    change final.resultPtr.toNat + 32 * highWords + 31 < UInt256.size
    rw [hfinalPtr]
    omega
  have hboundaryRange : boundaryState.ptr.toNat + 32 * highWords ≤
      boundaryState.memory.size := by
    change final.resultPtr.toNat + 32 * highWords ≤ final.memory.size
    rw [hfinalPtr]
    have hsize : final.memory.size = mem.size := by
      simpa only [final, sosReductionIterationFinal, factor, initial,
        sosReductionIterationFactor, sosReductionInitialState] using hiteration.finalSize
    rw [hsize]
    omega
  have hboundaryLoads : ∀ j, j < highWords →
      let current := sosPropagateIterate j boundaryState
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
    intro j hj
    let current := sosPropagateIterate j boundaryState
    have hiter := sosPropagateIterate_coverage j boundaryState hboundaryCovered
      hboundaryAwFit (by omega) (by omega)
    have hptr := sosPropagateIterate_ptr_toNat j boundaryState (by omega)
    have hword : current.ptr.toNat + 32 ≤ current.memory.size := by
      change (sosPropagateIterate j boundaryState).ptr.toNat + 32 ≤
        (sosPropagateIterate j boundaryState).memory.size
      rw [hptr, hiter.2.2]
      omega
    have hload := readWord_toNat_of_covered current.memory current.activeWords
      current.ptr hiter.1 hiter.2.1 hword
    simpa only [current, sosPropagateWord] using hload
  have hboundaryWrites : ∀ j, j < highWords →
      let current := sosPropagateIterate j boundaryState
      current.ptr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hiter := sosPropagateIterate_coverage j boundaryState hboundaryCovered
      hboundaryAwFit (by omega) (by omega)
    have hptr := sosPropagateIterate_ptr_toNat j boundaryState (by omega)
    change (sosPropagateIterate j boundaryState).ptr.toNat + 32 ≤
      (sosPropagateIterate j boundaryState).memory.size
    rw [hptr, hiter.2.2]
    omega
  have hboundaryBound := sosReductionIteration_boundary_bound_of_step_bound
    columns highWords hcolumns hsNext hnNext hnBefore
    (by omega) (by omega) hseparate hinvRead
    (by simpa only [sosPeeledValue] using hpeeledValue)
    (by simpa only [sosPeeledN0, sosPeeledAw1] using hpeeledN0)
    (by simpa only [factor, initial] using hiteration.loadsModulus)
    (by simpa only [factor, initial] using hiteration.loadsPrior)
    (by simpa only [factor, initial] using hiteration.writes)
    (by simpa only [boundaryState, final] using
      (show final.resultPtr.toNat + 32 * highWords < UInt256.size by omega))
    (by simpa only [boundaryState, final] using hboundaryLoads)
    (by simpa only [boundaryState, final] using hboundaryWrites)
    hstepBound
  have hboundaryFacts := selectedSOSReductionBoundary_facts_of_coverage highWords
    hboundaryCovered hboundaryAwFit hboundaryFit hboundaryRange hboundaryBound
    hboundarySelect
  have hselectorFit : nP.toNat + 32 * columns < UInt256.size := by
    rw [hnBefore, hnNext] at hnFit
    omega
  have hresultFit : (sBase + ⟨32⟩).toNat + 32 * (columns - 1) <
      UInt256.size := by omega
  have hfullBoundaryFit :
      (sBase + ⟨32⟩).toNat + 32 * (columns - 1 + highWords) <
        UInt256.size := by omega
  have hoperandFit : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) <
      UInt256.size := by omega
  have hvalue := selectedSOSReductionPass_value
    (columnFuel := columnFuel) (carryFuel := carryFuel) (mem := mem) (aw := aw)
    (sBase := sBase) (nP := nP) (n0inv := n0inv) (nBefore := nBefore)
    (nEnd := nEnd) (selected := selected) columns highWords hcolumns hsNext hnNext
    hnBefore hnEnd hselectorFit hresultFit hfullBoundaryFit hoperandFit hseparate hinvRead
    (by simpa only [sosPeeledValue] using hpeeledValue)
    (by simpa only [sosPeeledN0, sosPeeledAw1] using hpeeledN0)
    (by simpa only [factor, initial] using hiteration.loadsModulus)
    (by simpa only [factor, initial] using hiteration.loadsPrior)
    (by simpa only [factor, initial] using hiteration.writes)
    (by simpa only [boundaryState, final] using hboundaryFacts.loads)
    (by simpa only [boundaryState, final] using hboundaryFacts.writes)
    hboundaryFacts.window hselect
  have hmodulusBeforeBoundary :
      memoryWordsFrom final.memory nP.toNat columns =
        memoryWordsFrom mem nP.toNat columns := by
    have hframe := multiplyPassIterate_memoryWords_below factor (columns - 1)
      (sosReductionMultiplyState initial) nP.toNat columns
      (by simpa only [initial, sosReductionInitialState] using hresultFit)
      (by
        dsimp only [initial, sosReductionInitialState, sosReductionMultiplyState]
        rw [hnBefore, hnNext] at hseparate
        omega)
      (by
        intro j hj
        simpa only [← sosReductionMultiplyState_iterate] using
          hiteration.writes j hj)
    have hmemory : final.memory =
        (multiplyPassIterate factor (columns - 1)
          (sosReductionMultiplyState initial)).memory := by
      have hstate := congrArg (fun state : MultiplyPassState => state.memory)
        (sosReductionMultiplyState_iterate factor (columns - 1) initial)
      simpa only [sosReductionMultiplyState] using hstate
    rw [hmemory]
    simpa only [initial, sosReductionInitialState, sosReductionMultiplyState] using hframe
  have hmodulusFrame := selectedSOSReductionBoundary_memoryWords_below highWords
    nP.toNat columns
    (by simpa only [boundaryState, final] using
      (show final.resultPtr.toNat + 32 * highWords < UInt256.size by omega))
    (by simpa only [boundaryState, final] using hboundaryFacts.writes)
    hboundaryFacts.window
    (by
      change nP.toNat + 32 * columns ≤ final.resultPtr.toNat
      rw [hfinalPtr]
      rw [hnBefore, hnNext] at hseparate
      omega)
    hboundarySelect
  rw [hmodulusBeforeBoundary] at hmodulusFrame
  exact {
    value := hvalue
    finalCovered := hboundaryFacts.finalCovered
    finalAwFit := hboundaryFacts.finalAwFit
    finalSize := hboundaryFacts.finalSize.trans hiteration.finalSize
    modulusFrame := hmodulusFrame }

theorem montgomerySOSScan_succ
    (radix modulus nInv value steps : Nat) :
    Modexp.montgomerySOSScan radix modulus nInv value (steps + 1) =
      Modexp.montgomerySOSScan radix modulus nInv
        (Modexp.montgomeryCIOSStep radix modulus nInv 0 value 0) steps := by
  rfl

theorem mul_pow_sub_one_add_one_lt_pow_add
    {radix modulus columns remaining : Nat}
    (hradix : 1 < radix) (hremaining : 0 < remaining)
    (hmodulus : modulus < radix ^ columns) :
    modulus * (radix ^ (remaining - 1) + 1) < radix ^ (columns + remaining) := by
  let scale := radix ^ (remaining - 1) + 1
  have hscalePos : 0 < scale := by simp [scale]
  have hfirst : modulus * scale < radix ^ columns * scale :=
    Nat.mul_lt_mul_of_pos_right hmodulus hscalePos
  have hpowPos : 0 < radix ^ (remaining - 1) := pow_pos (by omega) _
  have hscale : scale ≤ radix ^ remaining := by
    have htwo : 2 ≤ radix := by omega
    have hdouble : radix ^ (remaining - 1) + 1 ≤
        radix ^ (remaining - 1) * 2 := by omega
    have hmul := Nat.mul_le_mul_left (radix ^ (remaining - 1)) htwo
    have hpow : radix ^ remaining = radix ^ (remaining - 1) * radix := by
      calc
        radix ^ remaining = radix ^ ((remaining - 1) + 1) := by congr 1 <;> omega
        _ = radix ^ (remaining - 1) * radix := by rw [pow_succ]
    dsimp only [scale]
    rw [hpow]
    exact hdouble.trans (by simpa [Nat.mul_comm] using hmul)
  calc
    modulus * scale < radix ^ columns * scale := hfirst
    _ ≤ radix ^ columns * radix ^ remaining := Nat.mul_le_mul_left _ hscale
    _ = radix ^ (columns + remaining) := by rw [pow_add]

structure SOSReductionLoopFacts
    (columns passes : Nat) (mem : ByteArray) (state : SOSReductionLoopState)
    (nP n0inv : UInt256) (modulus : Nat) (selected : SOSReductionLoopSelection) : Prop where
  value : Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory selected.final.sBase.toNat (columns + 1)) =
      Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
        (Modexp.wordLimbsToNat
          (memoryWordsFrom mem state.sBase.toNat (columns + passes + 1))) passes
  bound : Modexp.wordLimbsToNat
      (memoryWordsFrom selected.final.memory selected.final.sBase.toNat (columns + 1)) <
    2 * modulus
  finalCovered : MemoryCovered selected.final.memory selected.final.activeWords
  finalAwFit : selected.final.activeWords.toNat * 32 < UInt256.size
  finalSize : selected.final.memory.size = mem.size
  modulusFrame : memoryWordsFrom selected.final.memory nP.toNat columns =
    memoryWordsFrom mem nP.toNat columns

/-- Coverage, geometry, and the REDC value invariant discharge every selected SOS reduction
pass.  The result is the exact pure scan together with the bound needed by finalization. -/
theorem selectedSOSReductionLoop_facts_of_coverage
    (columns passes : Nat) {outerFuel columnFuel carryFuel : Nat}
    {nP n0inv nBefore nEnd sKEnd : UInt256}
    {state : SOSReductionLoopState} {selected : SOSReductionLoopSelection}
    (modulus : Nat)
    (hcolumns : 0 < columns)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : nEnd.toNat = nP.toNat + 32 * columns)
    (hstop : sKEnd.toNat = state.sBase.toNat + 32 * passes)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsFit : state.sBase.toNat + 32 * (columns + passes + 1) + 31 < UInt256.size)
    (hsRange : state.sBase.toNat + 32 * (columns + passes + 1) ≤ state.memory.size)
    (hnFit : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) + 31 < UInt256.size)
    (hnRange : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤ state.memory.size)
    (hseparate : (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤
      state.sBase.toNat + 32)
    (hmodulus : Modexp.wordLimbsToNat
      (memoryWordsFrom state.memory nP.toNat columns) = modulus)
    (hinv : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hvalueBound : Modexp.wordLimbsToNat
        (memoryWordsFrom state.memory state.sBase.toNat (columns + passes + 1)) <
      modulus * (UInt256.size ^ passes + 1))
    (hselect : selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv nBefore
      nEnd sKEnd state = some selected) :
    SOSReductionLoopFacts columns passes state.memory state nP n0inv modulus selected := by
  induction outerFuel generalizing passes state selected with
  | zero => simp [selectSOSReductionLoop] at hselect
  | succ outerFuel ih =>
      simp only [selectSOSReductionLoop] at hselect
      by_cases hzero : passes = 0
      · subst passes
        have hexit : state.sBase.lt sKEnd = ⟨0⟩ := by
          apply ult_zero
          omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        exact {
          value := rfl
          bound := by simpa [Nat.mul_comm] using hvalueBound
          finalCovered := hcovered
          finalAwFit := hawFit
          finalSize := rfl
          modulusFrame := rfl }
      · have hpasses : 0 < passes := by omega
        have hcontinue : state.sBase.lt sKEnd ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hpass : selectSOSReductionPass columnFuel carryFuel state.memory
            state.activeWords state.sBase nP n0inv nBefore nEnd with
        | none => rw [hpass] at hselect; contradiction
        | some pass =>
            rw [hpass] at hselect
            dsimp only at hselect
            let next := sosReductionLoopAdvance state pass
            cases hrest : selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv
                nBefore nEnd sKEnd next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have hsNext : (state.sBase + ⟨32⟩).toNat = state.sBase.toNat + 32 :=
                  uadd_word_lit32_toNat state.sBase (by omega)
                have hmodulusLt : modulus < UInt256.size ^ columns := by
                  rw [← hmodulus]
                  have hbound := Modexp.wordLimbsToNat_lt_pow
                    (memoryWordsFrom state.memory nP.toNat columns)
                  simpa only [memoryWordsFrom_length] using hbound
                have hnextBound := Modexp.montgomeryCIOSStep_zero_lt_mul_pow_add_one
                  (radix := UInt256.size) (modulus := modulus) (nInv := n0inv.toNat)
                  (t := Modexp.wordLimbsToNat
                    (memoryWordsFrom state.memory state.sBase.toNat
                      (columns + passes + 1)))
                  (remaining := passes) (by decide) hpasses hvalueBound
                have hstepBound : Modexp.montgomeryCIOSStep UInt256.size modulus
                      n0inv.toNat 0
                      (Modexp.wordLimbsToNat
                        (memoryWordsFrom state.memory state.sBase.toNat
                          (columns + (passes + 1)))) 0 <
                    UInt256.size ^ (columns - 1 + (passes + 1)) := by
                  have hcapacity := mul_pow_sub_one_add_one_lt_pow_add
                    (radix := UInt256.size) (modulus := modulus) (columns := columns)
                    (remaining := passes) (by decide) hpasses hmodulusLt
                  rw [show columns + (passes + 1) = columns + passes + 1 by omega]
                  rw [show columns - 1 + (passes + 1) = columns + passes by omega]
                  exact hnextBound.trans hcapacity
                have hlowMod :
                    Modexp.MultiLimbMemoryModel.memoryWordNat state.memory nP.toNat *
                        n0inv.toNat % UInt256.size = UInt256.size - 1 := by
                  have hlow := wordLimbsToNat_memoryWordsFrom_mod_size state.memory
                    nP.toNat columns hcolumns
                  rw [hmodulus] at hlow
                  rw [← hlow]
                  simpa [Nat.mul_mod] using hinv
                have hpassFacts := selectedSOSReductionPass_facts_of_coverage
                  columns (passes + 1) hcolumns hsNext hnNext hnBefore hnEnd hcovered hawFit
                  (by rw [hsNext]; omega) (by rw [hsNext]; omega) hnFit hnRange
                  (by rw [hsNext]; exact hseparate) hlowMod
                  (by simpa only [hmodulus] using hstepBound) hpass
                have hstep : next.sBase.toNat = state.sBase.toNat + 32 := by
                  simpa only [next, sosReductionLoopAdvance] using hsNext
                have hrestStop : sKEnd.toNat = next.sBase.toNat + 32 * (passes - 1) := by
                  rw [hstep]
                  omega
                have hrestModulus : Modexp.wordLimbsToNat
                    (memoryWordsFrom next.memory nP.toNat columns) = modulus := by
                  change Modexp.wordLimbsToNat
                    (memoryWordsFrom pass.boundary.final.memory nP.toNat columns) = modulus
                  rw [hpassFacts.modulusFrame, hmodulus]
                have hrestValueBound : Modexp.wordLimbsToNat
                      (memoryWordsFrom next.memory next.sBase.toNat
                        (columns + (passes - 1) + 1)) <
                    modulus * (UInt256.size ^ (passes - 1) + 1) := by
                  change Modexp.wordLimbsToNat
                      (memoryWordsFrom pass.boundary.final.memory
                        (state.sBase + ⟨32⟩).toNat (columns + (passes - 1) + 1)) < _
                  rw [show columns + (passes - 1) + 1 = columns - 1 + (passes + 1) by
                    omega]
                  rw [hpassFacts.value, hmodulus]
                  exact hnextBound
                have hrestFacts := ih (passes - 1) (state := next) (selected := rest)
                  hrestStop hpassFacts.finalCovered hpassFacts.finalAwFit
                  (by rw [hstep]; omega)
                  (by
                    change next.sBase.toNat + 32 * (columns + (passes - 1) + 1) ≤
                      pass.boundary.final.memory.size
                    rw [hstep, hpassFacts.finalSize]
                    omega)
                  (by
                    change (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) ≤
                      pass.boundary.final.memory.size
                    rw [hpassFacts.finalSize]
                    exact hnRange)
                  (by rw [hstep]; omega) hrestModulus hrestValueBound hrest
                have hscan : Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
                      (Modexp.wordLimbsToNat
                        (memoryWordsFrom state.memory state.sBase.toNat
                          (columns + passes + 1))) passes =
                    Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
                      (Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0
                        (Modexp.wordLimbsToNat
                          (memoryWordsFrom state.memory state.sBase.toNat
                            (columns + passes + 1))) 0) (passes - 1) := by
                  rw [show passes = (passes - 1) + 1 by omega]
                  exact montgomerySOSScan_succ _ _ _ _ _
                have hnextValue : Modexp.wordLimbsToNat
                      (memoryWordsFrom next.memory next.sBase.toNat
                        (columns + (passes - 1) + 1)) =
                    Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0
                      (Modexp.wordLimbsToNat
                        (memoryWordsFrom state.memory state.sBase.toNat
                          (columns + passes + 1))) 0 := by
                  change Modexp.wordLimbsToNat
                      (memoryWordsFrom pass.boundary.final.memory
                        (state.sBase + ⟨32⟩).toNat (columns + (passes - 1) + 1)) = _
                  rw [show columns + (passes - 1) + 1 = columns - 1 + (passes + 1) by
                    omega]
                  simpa only [hmodulus,
                    show columns + (passes + 1) = columns + passes + 1 by omega] using
                    hpassFacts.value
                exact {
                  value := by
                    rw [hrestFacts.value, hscan, hnextValue]
                  bound := hrestFacts.bound
                  finalCovered := hrestFacts.finalCovered
                  finalAwFit := hrestFacts.finalAwFit
                  finalSize := hrestFacts.finalSize.trans hpassFacts.finalSize
                  modulusFrame := by
                    rw [hrestFacts.modulusFrame]
                    change memoryWordsFrom pass.boundary.final.memory nP.toNat columns = _
                    exact hpassFacts.modulusFrame }

/-- Composing selected outer passes yields the pure SOS scan.  The per-pass premise is discharged
by `selectedSOSReductionPass_value` once coverage supplies its concrete load and write facts. -/
theorem selectedSOSReductionLoop_value
    (modulusWords passes : Nat) {outerFuel columnFuel carryFuel : Nat}
    {nP n0inv nBefore nEnd sKEnd : UInt256}
    {state : SOSReductionLoopState} {selected : SOSReductionLoopSelection}
    (modulus : Nat)
    (hstop : sKEnd.toNat = state.sBase.toNat + 32 * passes)
    (hfit : state.sBase.toNat + 32 * passes < UInt256.size)
    (hselect : selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv nBefore
      nEnd sKEnd state = some selected)
    (hpassValue : ∀ (remaining : Nat) (current : SOSReductionLoopState)
        (pass : SOSReductionPassSelection),
      0 < remaining →
      sKEnd.toNat = current.sBase.toNat + 32 * remaining →
      selectSOSReductionPass columnFuel carryFuel current.memory current.activeWords
        current.sBase nP n0inv nBefore nEnd = some pass →
      Modexp.wordLimbsToNat
          (memoryWordsFrom pass.boundary.final.memory
            (current.sBase + ⟨32⟩).toNat (modulusWords + remaining)) =
        Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0
          (Modexp.wordLimbsToNat
            (memoryWordsFrom current.memory current.sBase.toNat
              (modulusWords + remaining + 1))) 0) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory selected.final.sBase.toNat
          (modulusWords + 1)) =
      Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
        (Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.sBase.toNat
            (modulusWords + passes + 1))) passes := by
  induction outerFuel generalizing passes state selected with
  | zero => simp [selectSOSReductionLoop] at hselect
  | succ outerFuel ih =>
      simp only [selectSOSReductionLoop] at hselect
      by_cases hzero : passes = 0
      · subst passes
        have hexit : state.sBase.lt sKEnd = ⟨0⟩ := by
          apply ult_zero
          omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hpasses : 0 < passes := by omega
        have hcontinue : state.sBase.lt sKEnd ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hpass : selectSOSReductionPass columnFuel carryFuel state.memory
            state.activeWords state.sBase nP n0inv nBefore nEnd with
        | none => rw [hpass] at hselect; contradiction
        | some pass =>
            rw [hpass] at hselect
            dsimp only at hselect
            let next := sosReductionLoopAdvance state pass
            cases hrest : selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv
                nBefore nEnd sKEnd next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have hstep : next.sBase.toNat = state.sBase.toNat + 32 := by
                  dsimp only [next, sosReductionLoopAdvance]
                  exact uadd_word_lit32_toNat state.sBase (by omega)
                have hrestStop : sKEnd.toNat =
                    next.sBase.toNat + 32 * (passes - 1) := by
                  rw [hstep]
                  omega
                have hrestFit : next.sBase.toNat + 32 * (passes - 1) <
                    UInt256.size := by
                  rw [hstep]
                  omega
                have hrestValue := ih (passes - 1) (state := next) (selected := rest)
                  hrestStop hrestFit hrest
                have hfirst := hpassValue passes state pass hpasses hstop hpass
                change Modexp.wordLimbsToNat
                    (memoryWordsFrom rest.final.memory rest.final.sBase.toNat
                      (modulusWords + 1)) = _
                rw [hrestValue]
                have hscan : Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
                      (Modexp.wordLimbsToNat
                        (memoryWordsFrom state.memory state.sBase.toNat
                          (modulusWords + passes + 1))) passes =
                    Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
                      (Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0
                        (Modexp.wordLimbsToNat
                          (memoryWordsFrom state.memory state.sBase.toNat
                            (modulusWords + passes + 1))) 0) (passes - 1) := by
                  rw [show passes = (passes - 1) + 1 by omega]
                  exact montgomerySOSScan_succ _ _ _ _ _
                rw [hscan]
                have hnextValue : Modexp.wordLimbsToNat
                      (memoryWordsFrom next.memory next.sBase.toNat
                        (modulusWords + (passes - 1) + 1)) =
                    Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0
                      (Modexp.wordLimbsToNat
                        (memoryWordsFrom state.memory state.sBase.toNat
                          (modulusWords + passes + 1))) 0 := by
                  change Modexp.wordLimbsToNat
                      (memoryWordsFrom pass.boundary.final.memory
                        (state.sBase + ⟨32⟩).toNat
                        (modulusWords + (passes - 1) + 1)) = _
                  rw [show modulusWords + (passes - 1) + 1 =
                    modulusWords + passes by omega]
                  exact hfirst
                rw [hnextValue]

end Modexp.MultiLimbMontgomerySOSSemantic
