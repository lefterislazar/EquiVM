import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSReductionLinks

/-! # SOS square selector geometry -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem selectedSOSOffDiagonal_words_eq_geometry
    (words : Nat) {fuel : Nat} {a stop : UInt256}
    {state : SOSOffDiagonalState} {selected : SOSOffDiagonalSelection}
    (hwords : 0 < words)
    (hstop : stop.toNat = state.operandPtr.toNat + 32 * words)
    (hfit : state.operandPtr.toNat + 32 * words < UInt256.size)
    (hselect : selectSOSOffDiagonal fuel a stop state = some selected) :
    selected.words = words := by
  induction fuel generalizing words state selected with
  | zero => simp [selectSOSOffDiagonal] at hselect
  | succ fuel ih =>
      simp only [selectSOSOffDiagonal] at hselect
      let next := sosOffDiagonalAdvance a state
      have hstep : next.operandPtr.toNat = state.operandPtr.toNat + 32 := by
        dsimp only [next, sosOffDiagonalAdvance]
        exact uadd_word_lit32_toNat state.operandPtr (by omega)
      by_cases hone : words = 1
      · subst words
        have hexit : next.operandPtr.lt stop = ⟨0⟩ := by
          apply ult_zero
          rw [hstep]
          omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hwords' : 0 < words - 1 := by omega
        have hlt : next.operandPtr.toNat < stop.toNat := by rw [hstep]; omega
        have hcontinue : next.operandPtr.lt stop ≠ ⟨0⟩ := by
          rw [ult_one hlt]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrest : selectSOSOffDiagonal fuel a stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have hrestCount := ih (words - 1) (state := next) (selected := rest)
              hwords' (by rw [hstep]; omega) (by rw [hstep]; omega) hrest
            change rest.words + 1 = words
            omega

theorem selectedSOSOffDiagonalRow_products_eq_geometry
    (products : Nat) {fuel : Nat} {mem : ByteArray}
    {aw sRow aOff aEnd : UInt256} {selected : SOSOffDiagonalRowSelection}
    (hend : aEnd.toNat = aOff.toNat + 32 * (products + 1))
    (hfit : aOff.toNat + 32 * (products + 1) < UInt256.size)
    (hselect : selectSOSOffDiagonalRow fuel mem aw sRow aOff aEnd = some selected) :
    selected.products = products := by
  let initial := sosOffDiagonalInitial mem aw sRow aOff
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
  · have hproducts : 0 < products := by omega
    have hlt : initial.operandPtr.toNat < aEnd.toNat := by rw [hstep]; omega
    have hnonempty : initial.operandPtr.lt aEnd ≠ ⟨0⟩ := by
      rw [ult_one hlt]
      decide
    rw [if_neg hnonempty] at hselect
    cases hselectedProducts : selectSOSOffDiagonal fuel (readWord mem aw aOff) aEnd
        initial with
    | none => rw [hselectedProducts] at hselect; contradiction
    | some selectedProducts =>
        rw [hselectedProducts] at hselect
        injection hselect with heq
        subst selected
        exact selectedSOSOffDiagonal_words_eq_geometry products hproducts
          (by rw [hstep]; omega) (by rw [hstep]; omega) hselectedProducts

theorem selectedSOSOffDiagonalLoop_rows_eq_geometry
    (rows : Nat) {rowFuel productFuel : Nat} {aEnd fixedDrop drop : UInt256}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hstop : aEnd.toNat = state.aOff.toNat + 32 * rows)
    (hfit : state.aOff.toNat + 32 * rows < UInt256.size)
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop drop state =
      some selected) :
    selected.rows = rows := by
  induction rowFuel generalizing rows state selected drop with
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
                have hstep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosOffDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hrestCount := ih (rows - 1) (state := next) (selected := rest)
                  (drop := fixedDrop) (by rw [hstep]; omega) (by rw [hstep]; omega) hrest
                change rest.rows + 1 = rows
                omega

def sosOffDiagonalProductCounts : Nat → List Nat
  | 0 => []
  | rows + 1 => rows :: sosOffDiagonalProductCounts rows

/-- The outer upper-triangle selector cannot skip computations: row `i` contains exactly the
remaining `rows - i - 1` products, and both source and scratch cursors reach their geometric
ends. -/
theorem selectedSOSOffDiagonalLoop_full_geometry
    (rows : Nat) {rowFuel productFuel : Nat} {aEnd fixedDrop drop : UInt256}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hstop : aEnd.toNat = state.aOff.toNat + 32 * rows)
    (hafit : state.aOff.toNat + 32 * rows < UInt256.size)
    (hsfit : state.sRow.toNat + 64 * rows < UInt256.size)
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop drop state =
      some selected) :
    selected.rows = rows ∧
      selected.products = sosOffDiagonalProductCounts rows ∧
      selected.final.aOff.toNat = state.aOff.toNat + 32 * rows ∧
      selected.final.sRow.toNat = state.sRow.toNat + 64 * rows := by
  induction rowFuel generalizing rows state selected drop with
  | zero => simp [selectSOSOffDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSOffDiagonalLoop] at hselect
      by_cases hzero : rows = 0
      · subst rows
        have hexit : state.aOff.lt aEnd = ⟨0⟩ := by apply ult_zero; omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        simp [sosOffDiagonalProductCounts]
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
                have hrowCount : row.products = rows - 1 :=
                  selectedSOSOffDiagonalRow_products_eq_geometry (rows - 1)
                    (by omega) (by omega) hrow
                have hrestGeometry := ih (rows - 1) (state := next) (selected := rest)
                  (drop := fixedDrop)
                  (by rw [haStep]; omega)
                  (by rw [haStep]; omega)
                  (by rw [hsStep]; omega)
                  hrest
                refine ⟨?_, ?_, ?_, ?_⟩
                · change rest.rows + 1 = rows
                  omega
                · change row.products :: rest.products = sosOffDiagonalProductCounts rows
                  rw [hrowCount, hrestGeometry.2.1]
                  cases rows <;> simp_all [sosOffDiagonalProductCounts]
                · change rest.final.aOff.toNat = state.aOff.toNat + 32 * rows
                  rw [hrestGeometry.2.2.1, haStep]
                  omega
                · change rest.final.sRow.toNat = state.sRow.toNat + 64 * rows
                  rw [hrestGeometry.2.2.2, hsStep]
                  omega

theorem selectedSOSDouble_words_eq_geometry
    (words : Nat) {fuel : Nat} {stop : UInt256}
    {state : SOSDoubleState} {selected : SOSDoubleSelection}
    (hwords : 0 < words)
    (hstop : stop.toNat = state.ptr.toNat + 32 * words)
    (hfit : state.ptr.toNat + 32 * words < UInt256.size)
    (hselect : selectSOSDouble fuel stop state = some selected) :
    selected.words = words := by
  induction fuel generalizing words state selected with
  | zero => simp [selectSOSDouble] at hselect
  | succ fuel ih =>
      simp only [selectSOSDouble] at hselect
      let next := sosDoubleAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosDoubleAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      by_cases hone : words = 1
      · subst words
        have hexit : next.ptr.lt stop = ⟨0⟩ := by apply ult_zero; rw [hstep]; omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hwords' : 0 < words - 1 := by omega
        have hcontinue : next.ptr.lt stop ≠ ⟨0⟩ := by
          rw [ult_one (by rw [hstep]; omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrest : selectSOSDouble fuel stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have hrestCount := ih (words - 1) (state := next) (selected := rest)
              hwords' (by rw [hstep]; omega) (by rw [hstep]; omega) hrest
            change rest.words + 1 = words
            omega

theorem selectedSOSDoublePhase_words_eq_geometry
    (words : Nat) {fuel : Nat} {stop : UInt256}
    {state : SOSDoubleState} {selected : SOSDoublePhaseSelection}
    (hstop : stop.toNat = state.ptr.toNat + 32 * words)
    (hfit : state.ptr.toNat + 32 * words < UInt256.size)
    (hselect : selectSOSDoublePhase fuel stop state = some selected) :
    selected.words = words := by
  unfold selectSOSDoublePhase at hselect
  by_cases hzero : words = 0
  · subst words
    have hexit : state.ptr.lt stop = ⟨0⟩ := by apply ult_zero; omega
    rw [if_pos hexit] at hselect
    injection hselect with heq
    subst selected
    rfl
  · have hwords : 0 < words := by omega
    have hcontinue : state.ptr.lt stop ≠ ⟨0⟩ := by
      rw [ult_one (by omega)]
      decide
    rw [if_neg hcontinue] at hselect
    cases hselected : selectSOSDouble fuel stop state with
    | none => rw [hselected] at hselect; contradiction
    | some selectedWords =>
        rw [hselected] at hselect
        injection hselect with heq
        subst selected
        exact selectedSOSDouble_words_eq_geometry words hwords hstop hfit hselected

theorem selectedSOSDiagonalLoop_rows_eq_geometry
    (rows : Nat) {rowFuel carryFuel : Nat} {stop fixedDrop drop : UInt256}
    {state : SOSDiagonalLoopState} {selected : SOSDiagonalLoopSelection}
    (hstop : stop.toNat = state.aOff.toNat + 32 * rows)
    (hfit : state.aOff.toNat + 32 * rows < UInt256.size)
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop drop state =
      some selected) :
    selected.rows = rows := by
  induction rowFuel generalizing rows state selected drop with
  | zero => simp [selectSOSDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSDiagonalLoop] at hselect
      by_cases hzero : rows = 0
      · subst rows
        have hexit : state.aOff.lt stop = ⟨0⟩ := by apply ult_zero; omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hrows : 0 < rows := by omega
        have hcontinue : state.aOff.lt stop ≠ ⟨0⟩ := by
          rw [ult_one (by omega)]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords state.sOff
            state.aOff with
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
                have hstep : next.aOff.toNat = state.aOff.toNat + 32 := by
                  dsimp only [next, sosDiagonalLoopAdvance]
                  exact uadd_word_lit32_toNat state.aOff (by omega)
                have hrestCount := ih (rows - 1) (state := next) (selected := rest)
                  (drop := fixedDrop) (by rw [hstep]; omega) (by rw [hstep]; omega) hrest
                change rest.rows + 1 = rows
                omega

end Modexp.MultiLimbMontgomerySOSSemantic
