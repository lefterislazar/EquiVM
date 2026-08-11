import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSZeroLinks

/-! # CIOS outer selector links -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- Starting an iterate after one transition is the same as taking one more transition from
the original state. -/
theorem ciosOuterIterate_from_advance
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) :
    ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
        iterations
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state) =
      ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
        (iterations + 1) state := by
  induction iterations with
  | zero => rfl
  | succ iterations ih =>
      simp only [ciosOuterIterate]
      rw [ih]
      rfl

/-- For the multi-limb branch, a successful selector returns exactly its recorded number of
pure outer transitions. -/
theorem selectedCIOSOuter_final_eq_iterate
    (fuel columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut aEnd : UInt256)
    (state : CIOSOuterState) (selected : CIOSOuterSelection)
    (hcolumns : 1 < columns)
    (hselect : selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut aEnd state = some selected) :
    selected.final =
      ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut selected.iterations state := by
  induction fuel generalizing state selected with
  | zero => simp [selectCIOSOuter] at hselect
  | succ fuel ih =>
      simp only [selectCIOSOuter] at hselect
      rw [if_neg (Nat.ne_of_gt hcolumns), if_pos hcolumns] at hselect
      let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut state
      by_cases hexit : (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hexit] at hselect
        cases hrest : selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut aEnd next with
        | none =>
            rw [hrest] at hselect
            contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            rw [ih next rest hrest]
            exact ciosOuterIterate_from_advance rest.iterations columns bP tP tEnd
              tk1Off nP n0inv tOff nBefore shiftedOut state

/-- Under exact source-array geometry, selector success records one iteration per source word. -/
theorem selectedCIOSOuter_iterations_eq_geometry
    (fuel columns words : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut aEnd : UInt256)
    (state : CIOSOuterState) (selected : CIOSOuterSelection)
    (hcolumns : 1 < columns)
    (hwords : 0 < words)
    (hend : state.aOff.toNat + 32 * words = aEnd.toNat)
    (hfit : state.aOff.toNat + 32 * words < UInt256.size)
    (hselect : selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut aEnd state = some selected) :
    selected.iterations = words := by
  induction fuel generalizing words state selected with
  | zero => simp [selectCIOSOuter] at hselect
  | succ fuel ih =>
      simp only [selectCIOSOuter] at hselect
      rw [if_neg (Nat.ne_of_gt hcolumns), if_pos hcolumns] at hselect
      let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut state
      have hstep : (state.aOff + ⟨32⟩).toNat = state.aOff.toNat + 32 :=
        uadd_word_lit32_toNat state.aOff (by omega)
      by_cases hone : words = 1
      · subst words
        have hexit : (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩ := by
          rw [ult_zero]
          omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hwords' : 0 < words - 1 := by omega
        have hlt : (state.aOff + ⟨32⟩).toNat < aEnd.toNat := by
          rw [hstep]
          omega
        have hcontinue : (state.aOff + ⟨32⟩).lt aEnd ≠ ⟨0⟩ := by
          rw [ult_one hlt]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrest : selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut aEnd next with
        | none =>
            rw [hrest] at hselect
            contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have hnextOff : next.aOff.toNat = state.aOff.toNat + 32 := by
              simpa only [next, ciosOuterAdvance] using hstep
            have hrestCount := ih (words - 1) next rest hwords'
              (by rw [hnextOff]; omega) (by rw [hnextOff]; omega) hrest
            change rest.iterations + 1 = words
            omega

end Modexp.MultiLimbMontgomeryCIOSSemantic
