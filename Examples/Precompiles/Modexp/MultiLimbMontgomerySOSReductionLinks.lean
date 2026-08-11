import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFinalizeContract

/-! # SOS reduction selector geometry -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- A successful remaining-column selector returns the corresponding pure iteration. -/
theorem selectedSOSReductionColumns_final_eq_iterate
    {fuel : Nat} {factor stop : UInt256} {state : SOSReductionState}
    {selected : SOSReductionColumnsSelection}
    (hselect : selectSOSReductionColumns fuel factor stop state = some selected) :
    selected.final = sosReductionIterate factor selected.words state := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSReductionColumns] at hselect
  | succ fuel ih =>
      simp only [selectSOSReductionColumns] at hselect
      let next := sosReductionAdvance factor state
      by_cases hexit : next.modulusPtr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSReductionColumns fuel factor stop next with
        | none =>
            rw [hrest] at hselect
            contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            simpa only [sosReductionIterate, next] using ih hrest

/-- Exact nonwrapping pointer geometry forces one selected column per remaining modulus word. -/
theorem selectedSOSReductionColumns_words_eq_geometry
    (columns : Nat) {fuel : Nat} {factor stop : UInt256}
    {state : SOSReductionState} {selected : SOSReductionColumnsSelection}
    (hcolumns : 0 < columns)
    (hstop : stop.toNat = state.modulusPtr.toNat + 32 * columns)
    (hfit : state.modulusPtr.toNat + 32 * columns < UInt256.size)
    (hselect : selectSOSReductionColumns fuel factor stop state = some selected) :
    selected.words = columns := by
  induction fuel generalizing columns state selected with
  | zero => simp [selectSOSReductionColumns] at hselect
  | succ fuel ih =>
      simp only [selectSOSReductionColumns] at hselect
      let next := sosReductionAdvance factor state
      have hstep : next.modulusPtr.toNat = state.modulusPtr.toNat + 32 := by
        dsimp only [next, sosReductionAdvance]
        exact uadd_word_lit32_toNat state.modulusPtr (by omega)
      by_cases hone : columns = 1
      · subst columns
        have hexit : next.modulusPtr.lt stop = ⟨0⟩ := by
          apply ult_zero
          rw [hstep]
          omega
        rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · have hcolumns' : 0 < columns - 1 := by omega
        have hlt : next.modulusPtr.toNat < stop.toNat := by
          rw [hstep]
          omega
        have hcontinue : next.modulusPtr.lt stop ≠ ⟨0⟩ := by
          rw [ult_one hlt]
          decide
        rw [if_neg hcontinue] at hselect
        cases hrest : selectSOSReductionColumns fuel factor stop next with
        | none =>
            rw [hrest] at hselect
            contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have hrestCount := ih (columns - 1) (state := next) (selected := rest)
              hcolumns'
              (by rw [hstep]; omega) (by rw [hstep]; omega) hrest
            change rest.words + 1 = columns
            omega

/-- A successful reduction pass records exactly the full modulus width, including the peeled
low column. -/
theorem selectedSOSReductionPass_columns_eq_geometry
    (columns : Nat) {columnFuel carryFuel : Nat} {mem : ByteArray}
    {aw sBase nP n0inv nBefore nEnd : UInt256}
    {selected : SOSReductionPassSelection}
    (hcolumns : 0 < columns)
    (hnP : (nBefore + ⟨64⟩).toNat = nP.toNat + 32)
    (hnEnd : nEnd.toNat = nP.toNat + 32 * columns)
    (hfit : nP.toNat + 32 * columns < UInt256.size)
    (hselect : selectSOSReductionPass columnFuel carryFuel mem aw sBase nP n0inv
      nBefore nEnd = some selected) :
    selected.columns = columns := by
  let factor := sosReductionIterationFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  unfold selectSOSReductionPass at hselect
  dsimp only at hselect
  by_cases hone : columns = 1
  · subst columns
    have hfirst : initial.modulusPtr.lt nEnd = ⟨0⟩ := by
      apply ult_zero
      simp only [initial, sosReductionInitialState]
      rw [hnP, hnEnd]
    rw [if_pos hfirst] at hselect
    cases hboundary : selectSOSReductionBoundary carryFuel {
        carry := initial.carry
        ptr := initial.resultPtr
        memory := initial.memory
        activeWords := initial.activeWords } with
    | none =>
        rw [hboundary] at hselect
        contradiction
    | some boundary =>
        rw [hboundary] at hselect
        injection hselect with heq
        subst selected
        rfl
  · have hmulti : 1 < columns := by omega
    have hfirstNat : initial.modulusPtr.toNat < nEnd.toNat := by
      simp only [initial, sosReductionInitialState]
      rw [hnP, hnEnd]
      omega
    have hfirst : initial.modulusPtr.lt nEnd ≠ ⟨0⟩ := by
      rw [ult_one hfirstNat]
      decide
    rw [if_neg hfirst] at hselect
    cases hselectedColumns : selectSOSReductionColumns columnFuel factor nEnd initial with
    | none =>
        rw [hselectedColumns] at hselect
        contradiction
    | some selectedColumns =>
        rw [hselectedColumns] at hselect
        dsimp only at hselect
        cases hboundary : selectSOSReductionBoundary carryFuel {
            carry := selectedColumns.final.carry
            ptr := selectedColumns.final.resultPtr
            memory := selectedColumns.final.memory
            activeWords := selectedColumns.final.activeWords } with
        | none =>
            rw [hboundary] at hselect
            contradiction
        | some boundary =>
            rw [hboundary] at hselect
            injection hselect with heq
            subst selected
            have hremaining := selectedSOSReductionColumns_words_eq_geometry
              (columns - 1) (state := initial) (selected := selectedColumns)
              (by omega)
              (by simp only [initial, sosReductionInitialState]; rw [hnP, hnEnd]; omega)
              (by simp only [initial, sosReductionInitialState]; rw [hnP]; omega)
              hselectedColumns
            change selectedColumns.words + 1 = columns
            omega

/-- Exact scratch-base geometry forces one outer reduction pass per result word. -/
theorem selectedSOSReductionLoop_passes_eq_geometry
    (passes : Nat) {outerFuel columnFuel carryFuel : Nat}
    {nP n0inv nBefore nEnd sKEnd : UInt256}
    {state : SOSReductionLoopState} {selected : SOSReductionLoopSelection}
    (hstop : sKEnd.toNat = state.sBase.toNat + 32 * passes)
    (hfit : state.sBase.toNat + 32 * passes < UInt256.size)
    (hselect : selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv nBefore
      nEnd sKEnd state = some selected) :
    selected.passes = passes := by
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
        have hlt : state.sBase.toNat < sKEnd.toNat := by omega
        have hcontinue : state.sBase.lt sKEnd ≠ ⟨0⟩ := by
          rw [ult_one hlt]
          decide
        rw [if_neg hcontinue] at hselect
        cases hpass : selectSOSReductionPass columnFuel carryFuel state.memory
            state.activeWords state.sBase nP n0inv nBefore nEnd with
        | none =>
            rw [hpass] at hselect
            contradiction
        | some pass =>
            rw [hpass] at hselect
            dsimp only at hselect
            let next := sosReductionLoopAdvance state pass
            cases hrest : selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv
                nBefore nEnd sKEnd next with
            | none =>
                rw [hrest] at hselect
                contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have hstep : next.sBase.toNat = state.sBase.toNat + 32 := by
                  dsimp only [next, sosReductionLoopAdvance]
                  exact uadd_word_lit32_toNat state.sBase (by omega)
                have hrestCount := ih (passes - 1) (state := next) (selected := rest)
                  (by rw [hstep]; omega) (by rw [hstep]; omega) hrest
                change rest.passes + 1 = passes
                omega

/-- Once the generated collectors are identified with the complete scratch and modulus values,
the peeled column and every remaining selected column are exactly one pure Montgomery step. -/
theorem sosReductionPassColumns_eq_montgomeryStep
    (mem : ByteArray) (aw sBase nP n0inv nBefore : UInt256) (n : Nat)
    (value modulus nextValue : Nat)
    (hinv : (sosPeeledN0 mem aw sBase nP).toNat * n0inv.toNat % UInt256.size =
      UInt256.size - 1)
    (hvalue : value = (sosPeeledValue mem aw sBase).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (sosReductionPriorWords (sosPeeledFactor mem aw sBase n0inv) n
          (sosReductionInitialState mem aw sBase nP n0inv nBefore)))
    (hmodulus : modulus = (sosPeeledN0 mem aw sBase nP).toNat +
      UInt256.size * Modexp.wordLimbsToNat
        (sosReductionModulusWords (sosPeeledFactor mem aw sBase n0inv) n
          (sosReductionInitialState mem aw sBase nP n0inv nBefore)))
    (hnext : nextValue =
      Modexp.wordLimbsToNat
          (sosReductionOutputWords (sosPeeledFactor mem aw sBase n0inv) n
            (sosReductionInitialState mem aw sBase nP n0inv nBefore)) +
        UInt256.size ^ n *
          (sosReductionIterate (sosPeeledFactor mem aw sBase n0inv) n
            (sosReductionInitialState mem aw sBase nP n0inv nBefore)).carry.toNat) :
    nextValue = Modexp.montgomeryCIOSStep UInt256.size modulus n0inv.toNat 0
      value 0 := by
  let low := (sosPeeledValue mem aw sBase).toNat
  let factor := sosPeeledFactor mem aw sBase n0inv
  have hlow : low < UInt256.size :=
    (sosPeeledValue mem aw sBase).val.isLt
  have hvalueMod : value % UInt256.size = low := by
    rw [hvalue]
    simp only [low]
    rw [Nat.add_mod, Nat.mul_mod]
    simp only [Nat.mod_self, zero_mul, Nat.zero_mod, add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hlow
  have hfactor : factor.toNat =
      Modexp.montgomeryFactor UInt256.size n0inv.toNat value := by
    unfold factor sosPeeledFactor Modexp.montgomeryFactor
    rw [u256_mul_toNat, hvalueMod]
  have hrecompose := sosReductionPassColumns_recompose mem aw sBase nP n0inv
    nBefore n hinv
  dsimp only at hrecompose
  rw [← hnext, ← hvalue, ← hmodulus] at hrecompose
  unfold Modexp.montgomeryCIOSStep
  simp only [Nat.zero_mul, add_zero]
  rw [← hfactor]
  rw [← hrecompose]
  norm_num [UInt256.size]

end Modexp.MultiLimbMontgomerySOSSemantic
