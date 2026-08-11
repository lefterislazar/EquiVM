import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSSquareGeometry
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSMemoryLinks

/-! # Complete SOS off-diagonal row contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem selectedSOSOffDiagonal_final_eq_iterate
    {fuel : Nat} {a stop : UInt256} {state : SOSOffDiagonalState}
    {selected : SOSOffDiagonalSelection}
    (hselect : selectSOSOffDiagonal fuel a stop state = some selected) :
    selected.final = sosOffDiagonalIterate a selected.words state := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSOffDiagonal] at hselect
  | succ fuel ih =>
      simp only [selectSOSOffDiagonal] at hselect
      let next := sosOffDiagonalAdvance a state
      by_cases hexit : next.operandPtr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSOffDiagonal fuel a stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            simpa only [sosOffDiagonalIterate, next] using ih hrest

/-- The row wrapper performs exactly its selected product iterations followed by the terminal
carry store. -/
theorem selectedSOSOffDiagonalRow_finalMemory_eq
    (products : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {selected : SOSOffDiagonalRowSelection}
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (hafit : aOff.toNat + 32 * (products + 1) < UInt256.size)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    selected.finalMemory =
      sosOffDiagonalBoundaryMemory
        (sosOffDiagonalIterate (readWord mem aw aOff) products
          (sosOffDiagonalInitial mem aw sRow aOff)) := by
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let a := readWord mem aw aOff
  have hstep : initial.operandPtr.toNat = aOff.toNat + 32 := by
    dsimp only [initial, sosOffDiagonalInitial]
    exact uadd_word_lit32_toNat aOff (by omega)
  unfold selectSOSOffDiagonalRow at hselect
  dsimp only at hselect
  by_cases hzero : products = 0
  · subst products
    have hempty : initial.operandPtr.lt aEnd = ⟨0⟩ := by
      apply ult_zero
      rw [hstep]
      omega
    rw [if_pos hempty] at hselect
    injection hselect with heq
    subst selected
    rfl
  · have hpositive : 0 < products := by omega
    have hnonempty : initial.operandPtr.lt aEnd ≠ ⟨0⟩ := by
      rw [ult_one (by rw [hstep]; omega)]
      decide
    rw [if_neg hnonempty] at hselect
    cases hproducts : selectSOSOffDiagonal productFuel a aEnd initial with
    | none => rw [hproducts] at hselect; contradiction
    | some selectedProducts =>
        rw [hproducts] at hselect
        injection hselect with heq
        subst selected
        have hcount := selectedSOSOffDiagonal_words_eq_geometry products hpositive
          (by rw [hstep]; omega) (by rw [hstep]; omega) hproducts
        have hfinal := selectedSOSOffDiagonal_final_eq_iterate hproducts
        rw [hcount] at hfinal
        rw [hfinal]

/-- The row wrapper's active-word result is the exact terminal carry-store expansion. -/
theorem selectedSOSOffDiagonalRow_finalActiveWords_eq
    (products : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {selected : SOSOffDiagonalRowSelection}
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (hafit : aOff.toNat + 32 * (products + 1) < UInt256.size)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    selected.finalActiveWords =
      sosOffDiagonalBoundaryAw
        (sosOffDiagonalIterate (readWord mem aw aOff) products
          (sosOffDiagonalInitial mem aw sRow aOff)) := by
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let a := readWord mem aw aOff
  have hstep : initial.operandPtr.toNat = aOff.toNat + 32 := by
    dsimp only [initial, sosOffDiagonalInitial]
    exact uadd_word_lit32_toNat aOff (by omega)
  unfold selectSOSOffDiagonalRow at hselect
  dsimp only at hselect
  by_cases hzero : products = 0
  · subst products
    have hempty : initial.operandPtr.lt aEnd = ⟨0⟩ := by
      apply ult_zero
      rw [hstep]
      omega
    rw [if_pos hempty] at hselect
    injection hselect with heq
    subst selected
    rfl
  · have hpositive : 0 < products := by omega
    have hnonempty : initial.operandPtr.lt aEnd ≠ ⟨0⟩ := by
      rw [ult_one (by rw [hstep]; omega)]
      decide
    rw [if_neg hnonempty] at hselect
    cases hproducts : selectSOSOffDiagonal productFuel a aEnd initial with
    | none => rw [hproducts] at hselect; contradiction
    | some selectedProducts =>
        rw [hproducts] at hselect
        injection hselect with heq
        subst selected
        have hcount := selectedSOSOffDiagonal_words_eq_geometry products hpositive
          (by rw [hstep]; omega) (by rw [hstep]; omega) hproducts
        have hfinal := selectedSOSOffDiagonal_final_eq_iterate hproducts
        rw [hcount] at hfinal
        rw [hfinal]

/-- A completed row, including its carry store, preserves every complete word range below the
row's first scratch destination. -/
theorem sosOffDiagonalBoundary_memoryWords_below
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) (ptr count : Nat)
    (hresultFit : state.resultPtr.toNat + 32 * (n + 1) < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.resultPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hboundary : (sosOffDiagonalIterate a n state).resultPtr.toNat ≤
      (sosOffDiagonalIterate a n state).memory.size) :
    memoryWordsFrom
        (sosOffDiagonalBoundaryMemory (sosOffDiagonalIterate a n state)) ptr count =
      memoryWordsFrom state.memory ptr count := by
  let final := sosOffDiagonalIterate a n state
  have hptr : final.resultPtr.toNat = state.resultPtr.toNat + 32 * n :=
    sosOffDiagonalIterate_resultPtr_toNat a n state (by omega)
  have hpass := sosOffDiagonalIterate_memoryWords_below a n state ptr count
    (by omega) hbelow hwrites
  have hstore := memoryWordsFrom_write_above final.carry.toByteArray final.memory
    final.resultPtr.toNat ptr count (by rw [toByteArray_size]) hboundary (by
      rw [hptr]
      omega)
  simpa only [sosOffDiagonalBoundaryMemory, final] using hstore.trans hpass

/-- A completed row also preserves every complete word range above its terminal carry word. -/
theorem sosOffDiagonalBoundary_memoryWords_above
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) (ptr count : Nat)
    (hresultFit : state.resultPtr.toNat + 32 * (n + 1) < UInt256.size)
    (habove : state.resultPtr.toNat + 32 * (n + 1) ≤ ptr)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hboundary : (sosOffDiagonalIterate a n state).resultPtr.toNat ≤
      (sosOffDiagonalIterate a n state).memory.size) :
    memoryWordsFrom
        (sosOffDiagonalBoundaryMemory (sosOffDiagonalIterate a n state)) ptr count =
      memoryWordsFrom state.memory ptr count := by
  let final := sosOffDiagonalIterate a n state
  have hptr : final.resultPtr.toNat = state.resultPtr.toNat + 32 * n :=
    sosOffDiagonalIterate_resultPtr_toNat a n state (by omega)
  have hpass := sosOffDiagonalIterate_memoryWords_above a n state ptr count
    (by omega) (by omega) hwrites
  have hstore := memoryWordsFrom_wordWrite_below_extending final.carry final.memory
    final.resultPtr.toNat ptr count hboundary (by
      rw [hptr]
      omega)
  simpa only [sosOffDiagonalBoundaryMemory, final] using hstore.trans hpass

/-- Writing a completed row carry appends that carry to the final inner-loop scratch window. -/
theorem sosOffDiagonalBoundaryWords
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState)
    (hfit : state.resultPtr.toNat + 32 * (n + 1) < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hboundary : (sosOffDiagonalIterate a n state).resultPtr.toNat ≤
      (sosOffDiagonalIterate a n state).memory.size) :
    memoryWordsFrom
        (sosOffDiagonalBoundaryMemory (sosOffDiagonalIterate a n state))
        state.resultPtr.toNat (n + 1) =
      sosOffDiagonalOutputWords a n state ++
        [(sosOffDiagonalIterate a n state).carry] := by
  let final := sosOffDiagonalIterate a n state
  have hptr : final.resultPtr.toNat = state.resultPtr.toNat + 32 * n := by
    exact sosOffDiagonalIterate_resultPtr_toNat a n state (by omega)
  have houtput := sosOffDiagonalOutputWords_eq_finalMemory a n state (by omega) hwrites
  have hframeRaw := memoryWordsFrom_write_above final.carry.toByteArray final.memory
    final.resultPtr.toNat state.resultPtr.toNat n (by rw [toByteArray_size]) hboundary
    (by rw [hptr])
  have hframe : memoryWordsFrom (sosOffDiagonalBoundaryMemory final)
      state.resultPtr.toNat n = memoryWordsFrom final.memory state.resultPtr.toNat n := by
    simpa only [sosOffDiagonalBoundaryMemory] using hframeRaw
  have hgap : final.resultPtr.toNat - final.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hboundary]
    exact lt_usize 0 (by norm_num)
  have hlast : UInt256.ofNat
        (Modexp.MultiLimbMemoryModel.memoryWordNat
          (sosOffDiagonalBoundaryMemory final) final.resultPtr.toNat) = final.carry := by
    apply u256_inj
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
    unfold sosOffDiagonalBoundaryMemory Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
    exact fromByteArrayBigEndian_toByteArray _
  have hlast' : UInt256.ofNat
        (Modexp.MultiLimbMemoryModel.memoryWordNat
          (sosOffDiagonalBoundaryMemory final) (state.resultPtr.toNat + 32 * n)) =
      final.carry := by
    rw [← hptr]
    exact hlast
  rw [memoryWordsFrom_succ_eq_append, hframe, ← houtput, hlast']

/-- One selected upper-triangle row adds exactly `a[i]` times the remaining operand suffix to
the corresponding scratch window, including the terminal carry word. -/
theorem selectedSOSOffDiagonalRow_value
    (products : Nat) {productFuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {selected : SOSOffDiagonalRowSelection}
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
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory sRow.toNat (products + 1)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sRow.toNat products) +
        (readWord mem aw aOff).toNat *
          Modexp.wordLimbsToNat
            (memoryWordsFrom mem (aOff + ⟨32⟩).toNat products) := by
  let a := readWord mem aw aOff
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  have hinitialOperand : initial.operandPtr = aOff + ⟨32⟩ := rfl
  have hinitialResult : initial.resultPtr = sRow := rfl
  have hcount := selectedSOSOffDiagonalRow_products_eq_geometry products hend hafit hselect
  unfold selectSOSOffDiagonalRow at hselect
  dsimp only at hselect
  by_cases hzero : products = 0
  · subst products
    have hempty : initial.operandPtr.lt aEnd = ⟨0⟩ := by
      apply ult_zero
      dsimp only [initial, sosOffDiagonalInitial]
      have hstep := uadd_word_lit32_toNat aOff (by omega)
      rw [hstep]
      omega
    rw [if_pos hempty] at hselect
    injection hselect with heq
    subst selected
    simp only [Modexp.wordLimbsToNat, Nat.zero_mul, add_zero]
    have hb := sosOffDiagonalBoundaryWords a 0 initial hsfit (by omega) hboundary
    simpa [initial, a, Modexp.wordLimbsToNat] using
      congrArg Modexp.wordLimbsToNat hb
  · have hpositive : 0 < products := by omega
    have hstep : initial.operandPtr.toNat = aOff.toNat + 32 := by
      dsimp only [initial, sosOffDiagonalInitial]
      exact uadd_word_lit32_toNat aOff (by omega)
    have hnonempty : initial.operandPtr.lt aEnd ≠ ⟨0⟩ := by
      rw [ult_one (by rw [hstep, hend]; omega)]
      decide
    rw [if_neg hnonempty] at hselect
    cases hproducts : selectSOSOffDiagonal productFuel a aEnd initial with
    | none => rw [hproducts] at hselect; contradiction
    | some selectedProducts =>
        rw [hproducts] at hselect
        injection hselect with heq
        subst selected
        have hselectedCount : selectedProducts.words = products := by
          simpa only using hcount
        have hfinal := selectedSOSOffDiagonal_final_eq_iterate hproducts
        rw [hselectedCount] at hfinal
        have hoperand := sosOffDiagonalOperandWords_eq_initialMemory a products initial
          (by
            rw [hinitialOperand]
            have hadd := uadd_word_lit32_toNat aOff (by omega)
            rw [hadd]
            omega)
          (by rw [hinitialResult]; omega)
          (by rw [hinitialOperand, hinitialResult]; exact hseparate)
          hloadsOperand hwrites
        have hprior := sosOffDiagonalPriorWords_eq_initialMemory a products initial
          (by rw [hinitialResult]; omega) hloadsPrior hwrites
        have hrecompose := sosOffDiagonalCollectors_recompose a products initial
        rw [hoperand, hprior] at hrecompose
        have hboundaryWords := sosOffDiagonalBoundaryWords a products initial hsfit
          hwrites hboundary
        have hboundaryValue := congrArg Modexp.wordLimbsToNat hboundaryWords
        rw [Modexp.wordLimbsToNat_append, sosOffDiagonalOutputWords_length] at hboundaryValue
        simp only [Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero] at hboundaryValue
        change Modexp.wordLimbsToNat
            (memoryWordsFrom (sosOffDiagonalBoundaryMemory selectedProducts.final)
              sRow.toNat (products + 1)) = _
        rw [hfinal]
        change Modexp.wordLimbsToNat
            (memoryWordsFrom
              (sosOffDiagonalBoundaryMemory (sosOffDiagonalIterate a products initial))
              initial.resultPtr.toNat (products + 1)) = _
        rw [hboundaryValue]
        simpa [initial, a, sosOffDiagonalInitial] using hrecompose

end Modexp.MultiLimbMontgomerySOSSemantic
