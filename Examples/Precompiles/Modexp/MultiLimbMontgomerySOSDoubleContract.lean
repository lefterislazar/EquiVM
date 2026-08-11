import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSSquareGeometry
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSMemoryLinks

/-! # Complete SOS doubling contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem selectedSOSDouble_final_eq_iterate
    {fuel : Nat} {stop : UInt256} {state : SOSDoubleState}
    {selected : SOSDoubleSelection}
    (hselect : selectSOSDouble fuel stop state = some selected) :
    selected.final = sosDoubleIterate selected.words state := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSDouble] at hselect
  | succ fuel ih =>
      simp only [selectSOSDouble] at hselect
      let next := sosDoubleAdvance state
      by_cases hexit : next.ptr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSDouble fuel stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            simpa only [sosDoubleIterate, next] using ih hrest

theorem selectedSOSDoublePhase_final_eq_iterate
    {fuel : Nat} {stop : UInt256} {state : SOSDoubleState}
    {selected : SOSDoublePhaseSelection}
    (hselect : selectSOSDoublePhase fuel stop state = some selected) :
    selected.final = sosDoubleIterate selected.words state := by
  unfold selectSOSDoublePhase at hselect
  by_cases hempty : state.ptr.lt stop = ⟨0⟩
  · rw [if_pos hempty] at hselect
    injection hselect with heq
    subst selected
    rfl
  · rw [if_neg hempty] at hselect
    cases hwords : selectSOSDouble fuel stop state with
    | none => rw [hwords] at hselect; contradiction
    | some words =>
        rw [hwords] at hselect
        injection hselect with heq
        subst selected
        exact selectedSOSDouble_final_eq_iterate hwords

/-- A selected full doubling phase changes the represented scratch value by exact multiplication
by two.  The high carry is retained as the word immediately above the selected range. -/
theorem selectedSOSDoublePhase_value
    (words : Nat) {fuel : Nat} {stop : UInt256}
    {state : SOSDoubleState} {selected : SOSDoublePhaseSelection}
    (hstop : stop.toNat = state.ptr.toNat + 32 * words)
    (hfit : state.ptr.toNat + 32 * words < UInt256.size)
    (hcarry : state.carry.toNat < 2)
    (hloads : ∀ j, j < words →
      let current := sosDoubleIterate j state
      (sosDoubleWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hwrites : ∀ j, j < words →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hselect : selectSOSDoublePhase fuel stop state = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory state.ptr.toNat words) +
        UInt256.size ^ words * selected.final.carry.toNat =
      2 * Modexp.wordLimbsToNat
        (memoryWordsFrom state.memory state.ptr.toNat words) + state.carry.toNat := by
  have hwords := selectedSOSDoublePhase_words_eq_geometry words hstop hfit hselect
  have hfinal := selectedSOSDoublePhase_final_eq_iterate hselect
  have hrecompose := sosDoubleCollectors_recompose words state hcarry
  have hinput := sosDoubleInputWords_eq_initialMemory words state hfit hloads hwrites
  have houtput := sosDoubleOutputWords_eq_finalMemory words state hfit hwrites
  rw [hinput, houtput] at hrecompose
  rw [hwords] at hfinal
  rw [hfinal]
  exact hrecompose

end Modexp.MultiLimbMontgomerySOSSemantic
