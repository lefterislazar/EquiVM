import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSTrace

/-!
# Executable SOS carry selectors

Carry propagation has data-dependent length.  This file executes the same recurrence as the
bytecode over the named trace state and returns both the final state and exact gas.  The selector
is total by returning `none` when its explicit bound is exhausted.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSLoop

open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure SOSPropagateSelection where
  words : Nat
  final : SOSPropagateState
  gas : Nat

def selectSOSPropagation : Nat → SOSPropagateState → Option SOSPropagateSelection
  | 0, _ => none
  | fuel + 1, state =>
      let next := sosPropagateAdvance state
      let localGas := sosPropagateGas state.activeWords state.ptr + 10
      if next.carry = ⟨0⟩ then
        some { words := 1, final := next, gas := localGas }
      else
        match selectSOSPropagation fuel next with
        | none => none
        | some rest => some {
            words := rest.words + 1
            final := rest.final
            gas := localGas + rest.gas }

theorem selectSOSPropagation_words_pos
    {fuel : Nat} {state : SOSPropagateState} {selected : SOSPropagateSelection}
    (hselect : selectSOSPropagation fuel state = some selected) :
    0 < selected.words := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSPropagation] at hselect
  | succ fuel ih =>
      simp only [selectSOSPropagation] at hselect
      by_cases hzero : (sosPropagateAdvance state).carry = ⟨0⟩
      · rw [if_pos hzero] at hselect
        injection hselect with heq
        subst selected
        change 0 < (1 : Nat)
        omega
      · rw [if_neg hzero] at hselect
        cases hrest : selectSOSPropagation fuel (sosPropagateAdvance state) with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            exact Nat.zero_lt_succ _

theorem selectSOSPropagation_final_zero
    {fuel : Nat} {state : SOSPropagateState} {selected : SOSPropagateSelection}
    (hselect : selectSOSPropagation fuel state = some selected) :
    selected.final.carry = ⟨0⟩ := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSPropagation] at hselect
  | succ fuel ih =>
      simp only [selectSOSPropagation] at hselect
      by_cases hzero : (sosPropagateAdvance state).carry = ⟨0⟩
      · rw [if_pos hzero] at hselect
        injection hselect with heq
        subst selected
        exact hzero
      · rw [if_neg hzero] at hselect
        cases hrest : selectSOSPropagation fuel (sosPropagateAdvance state) with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            exact ih (state := sosPropagateAdvance state) (selected := rest) hrest

/-- A successful selector result is an exact execution of the diagonal carry loop. -/
theorem selectedSOSPropagationExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    (state : SOSPropagateState) (selected : SOSPropagateSelection)
    (hdepth : tail.length + 2 ≤ 1020)
    (hselect : selectSOSPropagation fuel state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7725⟩
      (state.carry :: state.ptr :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7707⟩
      (selected.final.carry :: selected.final.ptr :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + 22 * selected.words) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectSOSPropagation] at hselect
  | succ fuel ih =>
      simp only [selectSOSPropagation] at hselect
      let next := sosPropagateAdvance state
      let localGas := sosPropagateGas state.activeWords state.ptr + 10
      by_cases hzero : next.carry = ⟨0⟩
      · rw [if_pos hzero] at hselect
        cases hselect
        have rd7713 := sosPropagateBody hdepth h
        have rd7714 := rd7713.jumpiNT (by native_decide) hzero
          (by simp only [List.length_cons]; omega)
        have normalized := rd7714.withIndices (k' := k + 22 * 1) (by omega) rfl
        simpa [next, localGas, sosPropagateAdvance,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
      · rw [if_neg hzero] at hselect
        cases hrest : selectSOSPropagation fuel next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            cases hselect
            have rd7713 := sosPropagateBody hdepth h
            have rdNext := rd7713.jumpiT (by native_decide) hzero
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdRest := ih next rest hrest (k := k + 22) (C := C + localGas) (by
              simpa [next, localGas, sosPropagateAdvance,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
            have normalized := rdRest.withIndices
              (k' := k + 22 * (rest.words + 1)) (by omega) rfl
            simpa [next, localGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              Nat.mul_add] using normalized

/-- The same executable selector proves the reduction carry loop at its second pair of PCs. -/
theorem selectedSOSReductionPropagationExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    (state : SOSPropagateState) (selected : SOSPropagateSelection)
    (hdepth : tail.length + 2 ≤ 1020)
    (hselect : selectSOSPropagation fuel state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7559⟩
      (state.carry :: state.ptr :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7546⟩
      (selected.final.carry :: selected.final.ptr :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + 22 * selected.words) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectSOSPropagation] at hselect
  | succ fuel ih =>
      simp only [selectSOSPropagation] at hselect
      let next := sosPropagateAdvance state
      let localGas := sosPropagateGas state.activeWords state.ptr + 10
      by_cases hzero : next.carry = ⟨0⟩
      · rw [if_pos hzero] at hselect
        cases hselect
        have rd7552 := sosReductionPropagateBody hdepth h
        have rd7553 := rd7552.jumpiNT (by native_decide) hzero
          (by simp only [List.length_cons]; omega)
        have normalized := rd7553.withIndices (k' := k + 22 * 1) (by omega) rfl
        simpa [next, localGas, sosPropagateAdvance,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
      · rw [if_neg hzero] at hselect
        cases hrest : selectSOSPropagation fuel next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            cases hselect
            have rd7552 := sosReductionPropagateBody hdepth h
            have rdNext := rd7552.jumpiT (by native_decide) hzero
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdRest := ih next rest hrest (k := k + 22) (C := C + localGas) (by
              simpa [next, localGas, sosPropagateAdvance,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
            have normalized := rdRest.withIndices
              (k' := k + 22 * (rest.words + 1)) (by omega) rfl
            simpa [next, localGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              Nat.mul_add] using normalized

structure SOSReductionBoundarySelection where
  propagatedWords : Nat
  final : SOSPropagateState
  gas : Nat

def selectSOSReductionBoundary
    (fuel : Nat) (state : SOSPropagateState) : Option SOSReductionBoundarySelection :=
  if state.carry = ⟨0⟩ then
    some { propagatedWords := 0, final := state, gas := 67 }
  else
    match selectSOSPropagation fuel state with
    | none => none
    | some propagation => some {
        propagatedWords := propagation.words
        final := propagation.final
        gas := 67 + propagation.gas }

/-- The boundary selector gives exact gas and state from the inner reduction exit to the next
outer-loop guard, including either zero or arbitrarily many propagated words. -/
theorem selectedSOSReductionBoundaryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {modulusPtr factor carry resultPtr sBase x3 x4 sKEnd nEnd x7 nP x9 : UInt256}
    (selected : SOSReductionBoundarySelection)
    (hdepth : tail.length + 12 ≤ 1021)
    (hselect : selectSOSReductionBoundary fuel
      { carry := carry, ptr := resultPtr, memory := mem, activeWords := aw } = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7538⟩
      (modulusPtr :: factor :: carry :: resultPtr :: sBase :: x3 :: x4 :: sKEnd ::
        nEnd :: x7 :: nP :: x9 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7328⟩
      (⟨7486⟩ :: (⟨32⟩ + sBase).lt sKEnd :: x3 :: x4 :: sKEnd ::
        (⟨32⟩ + sBase) :: x9 :: nEnd :: x7 :: nP :: x9 :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + 21 + 22 * selected.propagatedWords) (C + selected.gas) := by
  let state : SOSPropagateState :=
    { carry := carry, ptr := resultPtr, memory := mem, activeWords := aw }
  unfold selectSOSReductionBoundary at hselect
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    subst carry
    have rd := sosReductionBoundaryNoCarry (by omega) h
    have normalized := rd.withIndices (k' := k + 21 + 22 * 0) (by omega) rfl
    simpa [state, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation fuel state with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        have rd7552 := GeneratedTraces.trace_7538_body
          (tail := resultPtr :: sBase :: x3 :: x4 :: sKEnd :: nEnd :: x7 :: nP :: x9 :: tail)
          (by simp only [List.length_cons]; omega) h
        have rd7566 := rd7552.jumpiT (by native_decide) hzero
          (by native_decide) (by simp only [List.length_cons]; omega)
        have rd7553 := selectedSOSReductionPropagationExact state propagation
          (tail := sBase :: x3 :: x4 :: sKEnd :: nEnd :: x7 :: nP :: x9 :: tail)
          (by simp only [List.length_cons]; omega) hprop (by
            simpa [state, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7566)
        have rd7335 := GeneratedTraces.trace_7546_body
          (tail := tail) (by omega) rd7553
        have normalized := rd7335.withIndices
          (k' := k + 21 + 22 * propagation.words) (by omega) rfl
        have hgas : 46 + (C + 21 + propagation.gas) =
            C + (67 + propagation.gas) := by omega
        rw [hgas] at normalized
        simpa using normalized

def sosReductionInitialState
    (mem : ByteArray) (aw sBase nP n0inv nBefore : UInt256) : SOSReductionState where
  modulusPtr := nBefore + ⟨64⟩
  resultPtr := sBase + ⟨32⟩
  carry := sosPeeledCarry mem aw sBase nP n0inv
  memory := mem
  activeWords := sosPeeledAw aw sBase nP

def sosReductionIterationFactor
    (mem : ByteArray) (aw sBase n0inv : UInt256) : UInt256 :=
  sosPeeledFactor mem aw sBase n0inv

def sosReductionIterationFinal
    (columns : Nat) (mem : ByteArray) (aw sBase nP n0inv nBefore : UInt256) :
    SOSReductionState :=
  sosReductionIterate (sosReductionIterationFactor mem aw sBase n0inv)
    (columns - 1) (sosReductionInitialState mem aw sBase nP n0inv nBefore)

theorem sosReductionAdvance_iterate (factor : UInt256) (n : Nat)
    (state : SOSReductionState) :
    sosReductionAdvance factor (sosReductionIterate factor n state) =
      sosReductionIterate factor (n + 1) state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change sosReductionAdvance factor
        (sosReductionIterate factor n (sosReductionAdvance factor state)) =
          sosReductionIterate factor (n + 1) (sosReductionAdvance factor state)
      exact ih (sosReductionAdvance factor state)

def sosReductionColumnsGas
    (columns : Nat) (mem : ByteArray) (aw sBase nP n0inv nBefore : UInt256) : Nat :=
  if columns = 1 then 0
  else
    sosReductionThroughExitGas (sosReductionIterationFactor mem aw sBase n0inv)
      (columns - 2) (sosReductionInitialState mem aw sBase nP n0inv nBefore)

structure SOSReductionIterationSelection where
  boundary : SOSReductionBoundarySelection
  gas : Nat

/-- Execute the named arithmetic state to select exact gas for one full SOS reduction pass. -/
def selectSOSReductionIteration
    (fuel columns : Nat) (mem : ByteArray)
    (aw sBase nP n0inv nBefore : UInt256) : Option SOSReductionIterationSelection :=
  if columns = 0 then none
  else
    let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
    match selectSOSReductionBoundary fuel {
        carry := final.carry
        ptr := final.resultPtr
        memory := final.memory
        activeWords := final.activeWords } with
    | none => none
    | some boundary => some {
        boundary := boundary
        gas := sosPeeledGas aw sBase nP + 10 +
          sosReductionColumnsGas columns mem aw sBase nP n0inv nBefore + boundary.gas }

/-- A successful iteration selection executes the peeled column, all remaining modulus columns,
data-dependent carry propagation, and the outer-loop boundary with exact gas. -/
theorem selectedSOSReductionIterationExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel columns : Nat} {tail : List UInt256}
    {n0inv nBefore sKEnd sBase drop nEnd x7 nP x9 : UInt256}
    (selected : SOSReductionIterationSelection)
    (hdepth : tail.length + 12 ≤ 1015)
    (hcolumns : 0 < columns)
    (hfirst : (nBefore + ⟨64⟩).lt nEnd ≠ ⟨0⟩ ↔ 1 < columns)
    (hcontinue : ∀ j, j < columns - 2 →
      (sosReductionAdvance (sosReductionIterationFactor mem aw sBase n0inv)
        (sosReductionIterate (sosReductionIterationFactor mem aw sBase n0inv) j
          (sosReductionInitialState mem aw sBase nP n0inv nBefore))).modulusPtr.lt nEnd ≠ ⟨0⟩)
    (hexit : 1 < columns →
      (sosReductionAdvance (sosReductionIterationFactor mem aw sBase n0inv)
        (sosReductionIterate (sosReductionIterationFactor mem aw sBase n0inv)
          (columns - 2) (sosReductionInitialState mem aw sBase nP n0inv nBefore))).modulusPtr.lt
        nEnd = ⟨0⟩)
    (hselect : selectSOSReductionIteration fuel columns mem aw sBase nP n0inv nBefore =
      some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7486⟩
      (n0inv :: nBefore :: sKEnd :: sBase :: drop :: nEnd :: x7 :: nP :: x9 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7328⟩
      (⟨7486⟩ :: (⟨32⟩ + sBase).lt sKEnd :: n0inv :: nBefore :: sKEnd ::
        (⟨32⟩ + sBase) :: x9 :: nEnd :: x7 :: nP :: x9 :: tail)
      selected.boundary.final.memory selected.boundary.final.activeWords rdata acc
      (k + 48 + 58 * (columns - 1) + 21 +
        22 * selected.boundary.propagatedWords)
      (C + selected.gas) := by
  let factor := sosReductionIterationFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  let final := sosReductionIterationFinal columns mem aw sBase nP n0inv nBefore
  unfold selectSOSReductionIteration at hselect
  rw [if_neg (by omega : columns ≠ 0)] at hselect
  dsimp only at hselect
  cases hboundary : selectSOSReductionBoundary fuel {
      carry := final.carry
      ptr := final.resultPtr
      memory := final.memory
      activeWords := final.activeWords } with
  | none => rw [hboundary] at hselect; contradiction
  | some boundary =>
      rw [hboundary] at hselect
      injection hselect with heq
      subst selected
      have rd7544 := sosPeeledBody
        (tail := x9 :: tail) (by simp only [List.length_cons]; omega) h
      by_cases hm : columns = 1
      · subst columns
        have hfirstExit : (nBefore + ⟨64⟩).lt nEnd = ⟨0⟩ := by
          by_contra hne
          have := hfirst.mp hne
          omega
        have rd7545 := rd7544.jumpiNT (by native_decide)
          hfirstExit
          (by simp only [List.length_cons]; omega)
        have rdBoundary := selectedSOSReductionBoundaryExact (tail := tail) boundary
          (by omega) hboundary (by
          simpa [final, factor, initial, sosReductionIterationFinal,
            sosReductionInitialState, sosReductionIterationFactor,
            sosReductionIterate] using rd7545)
        have normalized := rdBoundary.withIndices
          (k' := k + 48 + 58 * (1 - 1) + 21 +
            22 * boundary.propagatedWords) (by omega) rfl
        simpa [sosReductionColumnsGas, final, factor, initial,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
      · have hmulti : 1 < columns := by omega
        have rd7588 := rd7544.jumpiT (by native_decide) (hfirst.mpr hmulti)
          (by native_decide) (by simp only [List.length_cons]; omega)
        have rd7545 := sosReductionThroughExit
          (factor := factor) (n := columns - 2)
          (tail := x7 :: nP :: x9 :: tail) initial
          (by simp only [List.length_cons]; omega) hcontinue (hexit hmulti) (by
            simpa [factor, initial, sosReductionInitialState,
              sosReductionIterationFactor] using rd7588)
        have hfinal :
            sosReductionAdvance factor (sosReductionIterate factor (columns - 2) initial) =
              sosReductionIterate factor (columns - 1) initial := by
          rw [sosReductionAdvance_iterate]
          congr 2
          omega
        rw [hfinal] at rd7545
        have rdBoundary := selectedSOSReductionBoundaryExact (tail := tail) boundary
          (by omega) hboundary (by
          simpa [final, factor, initial, sosReductionIterationFinal,
            sosReductionIterate_advance] using rd7545)
        have normalized := rdBoundary.withIndices
          (k' := k + 48 + 58 * (columns - 1) + 21 +
            22 * boundary.propagatedWords) (by omega) rfl
        simpa [sosReductionColumnsGas, hm, final, factor, initial,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

structure SOSReductionColumnsSelection where
  words : Nat
  final : SOSReductionState
  gas : Nat

/-- Execute the non-peeled reduction columns until their pointer guard becomes false. -/
def selectSOSReductionColumns : Nat → UInt256 → UInt256 → SOSReductionState →
    Option SOSReductionColumnsSelection
  | 0, _, _, _ => none
  | fuel + 1, factor, stop, state =>
      let next := sosReductionAdvance factor state
      let localGas := sosReductionGas state.activeWords state.modulusPtr state.resultPtr + 10
      if next.modulusPtr.lt stop = ⟨0⟩ then
        some { words := 1, final := next, gas := localGas }
      else
        match selectSOSReductionColumns fuel factor stop next with
        | none => none
        | some rest => some {
            words := rest.words + 1
            final := rest.final
            gas := localGas + rest.gas }

theorem selectSOSReductionColumns_words_pos
    {fuel : Nat} {factor stop : UInt256} {state : SOSReductionState}
    {selected : SOSReductionColumnsSelection}
    (hselect : selectSOSReductionColumns fuel factor stop state = some selected) :
    0 < selected.words := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSReductionColumns] at hselect
  | succ fuel ih =>
      simp only [selectSOSReductionColumns] at hselect
      let next := sosReductionAdvance factor state
      by_cases hexit : next.modulusPtr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        change 0 < (1 : Nat)
        omega
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSReductionColumns fuel factor stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            change 0 < rest.words + 1
            omega

/-- A successful column selector is the exact generated path through the final false guard. -/
theorem selectedSOSReductionColumnsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {factor s4 s5 s6 s7 stop : UInt256}
    (state : SOSReductionState) (selected : SOSReductionColumnsSelection)
    (hdepth : tail.length + 9 ≤ 1015)
    (hselect : selectSOSReductionColumns fuel factor stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7581⟩
      (sosReductionStack state factor (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7538⟩
      (sosReductionStack selected.final factor (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      selected.final.memory selected.final.activeWords rdata acc
      (k + 58 * selected.words) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectSOSReductionColumns] at hselect
  | succ fuel ih =>
      simp only [selectSOSReductionColumns] at hselect
      let next := sosReductionAdvance factor state
      let localGas := sosReductionGas state.activeWords state.modulusPtr state.resultPtr + 10
      by_cases hexit : next.modulusPtr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        have rd7544 := sosReductionBody hdepth h
        have rd7545 := rd7544.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        have normalized := rd7545.withIndices (k' := k + 58 * 1) (by omega) rfl
        simpa [next, localGas, sosReductionStack, sosReductionAdvance,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSReductionColumns fuel factor stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            cases hselect
            have rd7544 := sosReductionBody hdepth h
            have rdNext := rd7544.jumpiT (by native_decide) hexit
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdRest := ih next rest hrest (k := k + 58) (C := C + localGas) (by
              simpa [next, localGas, sosReductionStack, sosReductionAdvance,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
            have normalized := rdRest.withIndices
              (k' := k + 58 * (rest.words + 1)) (by omega) rfl
            simpa [next, localGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              Nat.mul_add] using normalized

structure SOSReductionPassSelection where
  columns : Nat
  boundary : SOSReductionBoundarySelection
  gas : Nat

/-- Select one complete outer SOS reduction pass from its actual pointer guards. -/
def selectSOSReductionPass
    (columnFuel carryFuel : Nat) (mem : ByteArray)
    (aw sBase nP n0inv nBefore nEnd : UInt256) : Option SOSReductionPassSelection :=
  let factor := sosReductionIterationFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  if initial.modulusPtr.lt nEnd = ⟨0⟩ then
    match selectSOSReductionBoundary carryFuel {
        carry := initial.carry
        ptr := initial.resultPtr
        memory := initial.memory
        activeWords := initial.activeWords } with
    | none => none
    | some boundary => some {
        columns := 1
        boundary := boundary
        gas := sosPeeledGas aw sBase nP + 10 + boundary.gas }
  else
    match selectSOSReductionColumns columnFuel factor nEnd initial with
    | none => none
    | some columns =>
        match selectSOSReductionBoundary carryFuel {
            carry := columns.final.carry
            ptr := columns.final.resultPtr
            memory := columns.final.memory
            activeWords := columns.final.activeWords } with
        | none => none
        | some boundary => some {
            columns := columns.words + 1
            boundary := boundary
            gas := sosPeeledGas aw sBase nP + 10 + columns.gas + boundary.gas }

theorem selectSOSReductionPass_columns_pos
    {columnFuel carryFuel : Nat} {mem : ByteArray}
    {aw sBase nP n0inv nBefore nEnd : UInt256}
    {selected : SOSReductionPassSelection}
    (hselect : selectSOSReductionPass columnFuel carryFuel mem
      aw sBase nP n0inv nBefore nEnd = some selected) :
    0 < selected.columns := by
  unfold selectSOSReductionPass at hselect
  dsimp only at hselect
  by_cases hfirst :
      (sosReductionInitialState mem aw sBase nP n0inv nBefore).modulusPtr.lt nEnd = ⟨0⟩
  · rw [if_pos hfirst] at hselect
    cases hboundary : selectSOSReductionBoundary carryFuel {
        carry := (sosReductionInitialState mem aw sBase nP n0inv nBefore).carry
        ptr := (sosReductionInitialState mem aw sBase nP n0inv nBefore).resultPtr
        memory := (sosReductionInitialState mem aw sBase nP n0inv nBefore).memory
        activeWords := (sosReductionInitialState mem aw sBase nP n0inv nBefore).activeWords } with
    | none => rw [hboundary] at hselect; contradiction
    | some boundary =>
        rw [hboundary] at hselect
        cases hselect
        change 0 < (1 : Nat)
        omega
  · rw [if_neg hfirst] at hselect
    cases hcolumns : selectSOSReductionColumns columnFuel
        (sosReductionIterationFactor mem aw sBase n0inv) nEnd
        (sosReductionInitialState mem aw sBase nP n0inv nBefore) with
    | none => rw [hcolumns] at hselect; contradiction
    | some columns =>
        rw [hcolumns] at hselect
        dsimp only at hselect
        cases hboundary : selectSOSReductionBoundary carryFuel {
            carry := columns.final.carry
            ptr := columns.final.resultPtr
            memory := columns.final.memory
            activeWords := columns.final.activeWords } with
        | none => rw [hboundary] at hselect; contradiction
        | some boundary =>
            rw [hboundary] at hselect
            cases hselect
            change 0 < columns.words + 1
            omega

/-- The automatic pass selector proves all pointer branches and exact gas for `PC 7486 -> 7328`. -/
theorem selectedSOSReductionPassExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C columnFuel carryFuel : Nat} {tail : List UInt256}
    {n0inv nBefore sKEnd sBase drop nEnd x7 nP x9 : UInt256}
    (selected : SOSReductionPassSelection)
    (hdepth : tail.length + 12 ≤ 1015)
    (hselect : selectSOSReductionPass columnFuel carryFuel mem
      aw sBase nP n0inv nBefore nEnd = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7486⟩
      (n0inv :: nBefore :: sKEnd :: sBase :: drop :: nEnd :: x7 :: nP :: x9 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7328⟩
      (⟨7486⟩ :: (⟨32⟩ + sBase).lt sKEnd :: n0inv :: nBefore :: sKEnd ::
        (⟨32⟩ + sBase) :: x9 :: nEnd :: x7 :: nP :: x9 :: tail)
      selected.boundary.final.memory selected.boundary.final.activeWords rdata acc
      (k + 48 + 58 * (selected.columns - 1) + 21 +
        22 * selected.boundary.propagatedWords)
      (C + selected.gas) := by
  let factor := sosReductionIterationFactor mem aw sBase n0inv
  let initial := sosReductionInitialState mem aw sBase nP n0inv nBefore
  unfold selectSOSReductionPass at hselect
  dsimp only at hselect
  have rd7544 := sosPeeledBody
    (tail := x9 :: tail) (by simp only [List.length_cons]; omega) h
  by_cases hfirst : initial.modulusPtr.lt nEnd = ⟨0⟩
  · rw [if_pos hfirst] at hselect
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
        have rd7545 := rd7544.jumpiNT (by native_decide) (by
          simpa [initial, sosReductionInitialState] using hfirst)
          (by simp only [List.length_cons]; omega)
        have rdBoundary := selectedSOSReductionBoundaryExact (tail := tail) boundary
          (by omega) hboundary (by
            simpa [factor, initial, sosReductionInitialState,
              sosReductionIterationFactor] using rd7545)
        have normalized := rdBoundary.withIndices
          (k' := k + 48 + 58 * (1 - 1) + 21 +
            22 * boundary.propagatedWords) (by omega) rfl
        simpa [factor, initial, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
  · rw [if_neg hfirst] at hselect
    cases hcolumns : selectSOSReductionColumns columnFuel factor nEnd initial with
    | none => rw [hcolumns] at hselect; contradiction
    | some columns =>
        rw [hcolumns] at hselect
        dsimp only at hselect
        cases hboundary : selectSOSReductionBoundary carryFuel {
            carry := columns.final.carry
            ptr := columns.final.resultPtr
            memory := columns.final.memory
            activeWords := columns.final.activeWords } with
        | none => rw [hboundary] at hselect; contradiction
        | some boundary =>
            rw [hboundary] at hselect
            injection hselect with heq
            subst selected
            have rd7588 := rd7544.jumpiT (by native_decide) (by
              simpa [initial, sosReductionInitialState] using hfirst)
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rd7545 := selectedSOSReductionColumnsExact initial columns
              (tail := x7 :: nP :: x9 :: tail) (by simp only [List.length_cons]; omega)
              hcolumns (by
                simpa [factor, initial, sosReductionInitialState,
                  sosReductionIterationFactor] using rd7588)
            have rdBoundary := selectedSOSReductionBoundaryExact (tail := tail) boundary
              (by omega) hboundary rd7545
            have normalized := rdBoundary.withIndices
              (k' := k + 48 + 58 * ((columns.words + 1) - 1) + 21 +
                22 * boundary.propagatedWords) (by
                  have := selectSOSReductionColumns_words_pos hcolumns
                  omega) rfl
            have hwords := selectSOSReductionColumns_words_pos hcolumns
            simpa [factor, initial, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              Nat.mul_add] using normalized

structure SOSReductionLoopState where
  sBase : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosReductionLoopAdvance
    (state : SOSReductionLoopState) (pass : SOSReductionPassSelection) :
    SOSReductionLoopState where
  sBase := state.sBase + ⟨32⟩
  memory := pass.boundary.final.memory
  activeWords := pass.boundary.final.activeWords

structure SOSReductionLoopSelection where
  passes : Nat
  columns : List Nat
  final : SOSReductionLoopState
  steps : Nat
  gas : Nat

/-- Select all SOS reduction passes and the final false outer guard. -/
def selectSOSReductionLoop : Nat → Nat → Nat → UInt256 → UInt256 → UInt256 → UInt256 →
    UInt256 → SOSReductionLoopState → Option SOSReductionLoopSelection
  | 0, _, _, _, _, _, _, _, _ => none
  | outerFuel + 1, columnFuel, carryFuel, nP, n0inv, nBefore, nEnd, sKEnd, state =>
      if state.sBase.lt sKEnd = ⟨0⟩ then
        some {
          passes := 0
          columns := []
          final := state
          steps := 1
          gas := 10 }
      else
        match selectSOSReductionPass columnFuel carryFuel state.memory state.activeWords
            state.sBase nP n0inv nBefore nEnd with
        | none => none
        | some pass =>
            let next := sosReductionLoopAdvance state pass
            match selectSOSReductionLoop outerFuel columnFuel carryFuel nP n0inv nBefore
                nEnd sKEnd next with
            | none => none
            | some rest => some {
                passes := rest.passes + 1
                columns := pass.columns :: rest.columns
                final := rest.final
                steps := 1 + 48 + 58 * (pass.columns - 1) + 21 +
                  22 * pass.boundary.propagatedWords + rest.steps
                gas := 10 + pass.gas + rest.gas }

/-- A successful outer selector is the exact reduction loop, including its final false guard. -/
theorem selectedSOSReductionLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C outerFuel columnFuel carryFuel : Nat} {tail : List UInt256}
    {nP n0inv nBefore nEnd sKEnd x7 x9 : UInt256}
    (state : SOSReductionLoopState) (selected : SOSReductionLoopSelection)
    (hdepth : tail.length + 12 ≤ 1015)
    (hselect : selectSOSReductionLoop outerFuel columnFuel carryFuel
      nP n0inv nBefore nEnd sKEnd state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7328⟩
      (⟨7486⟩ :: state.sBase.lt sKEnd :: n0inv :: nBefore :: sKEnd ::
        state.sBase :: x9 :: nEnd :: x7 :: nP :: x9 :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7329⟩
      (n0inv :: nBefore :: sKEnd :: selected.final.sBase :: x9 :: nEnd :: x7 ::
        nP :: x9 :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction outerFuel generalizing state selected k C with
  | zero => simp [selectSOSReductionLoop] at hselect
  | succ outerFuel ih =>
      simp only [selectSOSReductionLoop] at hselect
      by_cases hexit : state.sBase.lt sKEnd = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        have rd7336 := h.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7336
      · rw [if_neg hexit] at hselect
        cases hpass : selectSOSReductionPass columnFuel carryFuel state.memory
            state.activeWords state.sBase nP n0inv nBefore nEnd with
        | none => rw [hpass] at hselect; contradiction
        | some pass =>
            rw [hpass] at hselect
            dsimp only at hselect
            let next := sosReductionLoopAdvance state pass
            cases hrest : selectSOSReductionLoop outerFuel columnFuel carryFuel
                nP n0inv nBefore nEnd sKEnd next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                cases hselect
                have rd7493 := h.jumpiT (by native_decide) hexit
                  (by native_decide) (by simp only [List.length_cons]; omega)
                have rdPass := selectedSOSReductionPassExact (tail := tail) pass hdepth hpass
                  (by simpa using rd7493)
                have hbase : (⟨32⟩ : UInt256) + state.sBase = state.sBase + ⟨32⟩ :=
                  by
                    apply u256_inj
                    rw [uadd_toNat, uadd_toNat, Nat.add_comm]
                rw [hbase] at rdPass
                have rdRest := ih next rest hrest
                  (k := k + 1 + 48 + 58 * (pass.columns - 1) + 21 +
                    22 * pass.boundary.propagatedWords)
                  (C := C + 10 + pass.gas) (by
                    simpa [next, sosReductionLoopAdvance, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using rdPass)
                have normalized := rdRest.withIndices
                  (k' := k + (1 + 48 + 58 * (pass.columns - 1) + 21 +
                    22 * pass.boundary.propagatedWords + rest.steps)) (by omega) rfl
                simpa [next, sosReductionLoopAdvance, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using normalized

structure SOSOffDiagonalSelection where
  words : Nat
  final : SOSOffDiagonalState
  gas : Nat

def selectSOSOffDiagonal : Nat → UInt256 → UInt256 → SOSOffDiagonalState →
    Option SOSOffDiagonalSelection
  | 0, _, _, _ => none
  | fuel + 1, a, stop, state =>
      let next := sosOffDiagonalAdvance a state
      let localGas := sosOffDiagonalGas state.activeWords state.operandPtr state.resultPtr + 10
      if next.operandPtr.lt stop = ⟨0⟩ then
        some { words := 1, final := next, gas := localGas }
      else
        match selectSOSOffDiagonal fuel a stop next with
        | none => none
        | some rest => some {
            words := rest.words + 1
            final := rest.final
            gas := localGas + rest.gas }

theorem selectedSOSOffDiagonalExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {a s4 s5 s6 s7 stop : UInt256}
    (state : SOSOffDiagonalState) (selected : SOSOffDiagonalSelection)
    (hdepth : tail.length + 9 ≤ 1015)
    (hselect : selectSOSOffDiagonal fuel a stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7831⟩
      (sosOffDiagonalStack state a (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7806⟩
      (sosOffDiagonalStack selected.final a (s4 :: s5 :: s6 :: s7 :: stop :: tail))
      selected.final.memory selected.final.activeWords rdata acc
      (k + 56 * selected.words) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectSOSOffDiagonal] at hselect
  | succ fuel ih =>
      simp only [selectSOSOffDiagonal] at hselect
      let next := sosOffDiagonalAdvance a state
      let localGas := sosOffDiagonalGas state.activeWords state.operandPtr state.resultPtr + 10
      by_cases hexit : next.operandPtr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        have rd7812 := sosOffDiagonalBody hdepth h
        have rd7813 := rd7812.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        have normalized := rd7813.withIndices (k' := k + 56 * 1) (by omega) rfl
        simpa [next, localGas, sosOffDiagonalStack, sosOffDiagonalAdvance,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSOffDiagonal fuel a stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            cases hselect
            have rd7812 := sosOffDiagonalBody hdepth h
            have rdNext := rd7812.jumpiT (by native_decide) hexit
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdRest := ih next rest hrest (k := k + 56) (C := C + localGas) (by
              simpa [next, localGas, sosOffDiagonalStack, sosOffDiagonalAdvance,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
            have normalized := rdRest.withIndices
              (k' := k + 56 * (rest.words + 1)) (by omega) rfl
            simpa [next, localGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
              Nat.mul_add] using normalized

structure SOSDoubleSelection where
  words : Nat
  final : SOSDoubleState
  gas : Nat

def selectSOSDouble : Nat → UInt256 → SOSDoubleState → Option SOSDoubleSelection
  | 0, _, _ => none
  | fuel + 1, stop, state =>
      let next := sosDoubleAdvance state
      let localGas := sosDoubleGas state.activeWords state.ptr + 10
      if next.ptr.lt stop = ⟨0⟩ then
        some { words := 1, final := next, gas := localGas }
      else
        match selectSOSDouble fuel stop next with
        | none => none
        | some rest => some {
            words := rest.words + 1
            final := rest.final
            gas := localGas + rest.gas }

theorem selectedSOSDoubleExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {stop s3 s4 s5 s6 s7 s8 s9 s10 s11 : UInt256}
    (state : SOSDoubleState) (selected : SOSDoubleSelection)
    (hdepth : tail.length + 12 ≤ 1021) (hfixed : s7 = s11)
    (hselect : selectSOSDouble fuel stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7747⟩
      (sosDoubleStack state stop
        (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7294⟩
      (sosDoubleStack selected.final stop
        (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      selected.final.memory selected.final.activeWords rdata acc
      (k + 30 * selected.words) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectSOSDouble] at hselect
  | succ fuel ih =>
      simp only [selectSOSDouble] at hselect
      let next := sosDoubleAdvance state
      let localGas := sosDoubleGas state.activeWords state.ptr + 10
      by_cases hexit : next.ptr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        have rd7300 := sosDoubleBody hdepth h
        have rd7301 := rd7300.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        have normalized := rd7301.withIndices (k' := k + 30 * 1) (by omega) rfl
        simpa [next, localGas, sosDoubleStack, sosDoubleAdvance, hfixed,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSDouble fuel stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            cases hselect
            have rd7300 := sosDoubleBody hdepth h
            have rdNext := rd7300.jumpiT (by native_decide) hexit
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdRest := ih next rest hrest (k := k + 30) (C := C + localGas) (by
              simpa [next, localGas, sosDoubleStack, sosDoubleAdvance, hfixed,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
            have normalized := rdRest.withIndices
              (k' := k + 30 * (rest.words + 1)) (by omega) rfl
            simpa [next, localGas, hfixed, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm, Nat.mul_add] using normalized

structure SOSDiagonalSelection where
  propagatedWords : Nat
  finalMemory : ByteArray
  finalActiveWords : UInt256
  gas : Nat

def selectSOSDiagonal
    (carryFuel : Nat) (mem : ByteArray) (aw sOff aOff : UInt256) :
    Option SOSDiagonalSelection :=
  let carry := sosDiagonalCarry mem aw sOff aOff
  let memory := sosDiagonalMemory mem aw sOff aOff
  let activeWords := sosDiagonalAw aw sOff aOff
  if carry = ⟨0⟩ then
    some {
      propagatedWords := 0
      finalMemory := memory
      finalActiveWords := activeWords
      gas := sosDiagonalGas aw sOff aOff + 10 + 61 }
  else
    match selectSOSPropagation carryFuel {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := memory
        activeWords := activeWords } with
    | none => none
    | some propagation => some {
        propagatedWords := propagation.words
        finalMemory := propagation.final.memory
        finalActiveWords := propagation.final.activeWords
        gas := sosDiagonalGas aw sOff aOff + 10 + propagation.gas + 61 }

/-- Select one diagonal square, optional carry propagation, and the generated row boundary. -/
theorem selectedSOSDiagonalExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C carryFuel : Nat} {tail : List UInt256}
    {sOff aOff stop s3 s4 drop s6 x8 x9 x10 : UInt256}
    (selected : SOSDiagonalSelection)
    (hdepth : tail.length + 10 ≤ 1016)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7636⟩
      (sOff :: aOff :: stop :: s3 :: s4 :: drop :: s6 :: x8 :: x9 :: x10 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7305⟩
      (⟨7636⟩ :: (aOff + ⟨32⟩).lt stop :: (sOff + ⟨64⟩) ::
        (aOff + ⟨32⟩) :: stop :: s3 :: s4 :: x10 :: s6 :: x8 :: x9 :: x10 :: tail)
      selected.finalMemory selected.finalActiveWords rdata acc
      (k + 87 + 22 * selected.propagatedWords) (C + selected.gas) := by
  let carry := sosDiagonalCarry mem aw sOff aOff
  let memory := sosDiagonalMemory mem aw sOff aOff
  let activeWords := sosDiagonalAw aw sOff aOff
  unfold selectSOSDiagonal at hselect
  dsimp only at hselect
  have rd7713 := sosDiagonalBody (tail := x8 :: x9 :: x10 :: tail)
    (by simp only [List.length_cons]; omega) h
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    cases hselect
    have rd7714 := rd7713.jumpiNT (by native_decide) hzero
      (by simp only [List.length_cons]; omega)
    have rd7312 := GeneratedTraces.trace_7707_body
      (tail := tail) (by omega) (by
        simpa [carry, memory, activeWords] using rd7714)
    have normalized := rd7312.withIndices (k' := k + 87 + 22 * 0) (by omega) rfl
    simpa [carry, memory, activeWords, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using normalized
  · rw [if_neg hzero] at hselect
    let propagationState : SOSPropagateState := {
      carry := carry
      ptr := sOff + ⟨64⟩
      memory := memory
      activeWords := activeWords }
    cases hprop : selectSOSPropagation carryFuel propagationState with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        cases hselect
        have rd7732 := rd7713.jumpiT (by native_decide) hzero
          (by native_decide) (by simp only [List.length_cons]; omega)
        have rd7714 := selectedSOSPropagationExact propagationState propagation
          (tail := (sOff + ⟨64⟩) :: aOff :: stop :: s6 :: s3 :: s4 ::
            x8 :: x9 :: x10 :: tail)
          (by simp only [List.length_cons]; omega) hprop (by
            simpa [propagationState, carry, memory, activeWords] using rd7732)
        have rd7312 := GeneratedTraces.trace_7707_body
          (tail := tail) (by omega) rd7714
        have normalized := rd7312.withIndices
          (k' := k + 87 + 22 * propagation.words) (by omega) rfl
        simpa [propagationState, carry, memory, activeWords, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using normalized

structure SOSDiagonalLoopState where
  sOff : UInt256
  aOff : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosDiagonalLoopAdvance
    (state : SOSDiagonalLoopState) (row : SOSDiagonalSelection) : SOSDiagonalLoopState where
  sOff := state.sOff + ⟨64⟩
  aOff := state.aOff + ⟨32⟩
  memory := row.finalMemory
  activeWords := row.finalActiveWords

structure SOSDiagonalLoopSelection where
  rows : Nat
  propagatedWords : List Nat
  final : SOSDiagonalLoopState
  finalDrop : UInt256
  steps : Nat
  gas : Nat

def selectSOSDiagonalLoop : Nat → Nat → UInt256 → UInt256 → UInt256 → SOSDiagonalLoopState →
    Option SOSDiagonalLoopSelection
  | 0, _, _, _, _, _ => none
  | rowFuel + 1, carryFuel, stop, fixedDrop, drop, state =>
      if state.aOff.lt stop = ⟨0⟩ then
        some {
          rows := 0
          propagatedWords := []
          final := state
          finalDrop := drop
          steps := 1
          gas := 10 }
      else
        match selectSOSDiagonal carryFuel state.memory state.activeWords state.sOff state.aOff with
        | none => none
        | some row =>
            let next := sosDiagonalLoopAdvance state row
            match selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop fixedDrop next with
            | none => none
            | some rest => some {
                rows := rest.rows + 1
                propagatedWords := row.propagatedWords :: rest.propagatedWords
                final := rest.final
                finalDrop := rest.finalDrop
                steps := 1 + 87 + 22 * row.propagatedWords + rest.steps
                gas := 10 + row.gas + rest.gas }

theorem selectedSOSDiagonalLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C rowFuel carryFuel : Nat} {tail : List UInt256}
    {stop s3 s4 drop s6 x8 x9 x10 : UInt256}
    (state : SOSDiagonalLoopState) (selected : SOSDiagonalLoopSelection)
    (hdepth : tail.length + 10 ≤ 1016)
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop x10 drop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7305⟩
      (⟨7636⟩ :: state.aOff.lt stop :: state.sOff :: state.aOff :: stop ::
        s3 :: s4 :: drop :: s6 :: x8 :: x9 :: x10 :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7306⟩
      (selected.final.sOff :: selected.final.aOff :: stop :: s3 :: s4 :: selected.finalDrop ::
        s6 :: x8 :: x9 :: x10 :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction rowFuel generalizing state selected k C drop with
  | zero => simp [selectSOSDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSDiagonalLoop] at hselect
      by_cases hexit : state.aOff.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        have rd7313 := h.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7313
      · rw [if_neg hexit] at hselect
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            let next := sosDiagonalLoopAdvance state row
            cases hrest : selectSOSDiagonalLoop rowFuel carryFuel stop x10 x10 next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                cases hselect
                have rd7643 := h.jumpiT (by native_decide) hexit
                  (by native_decide) (by simp only [List.length_cons]; omega)
                have rdRow := selectedSOSDiagonalExact (tail := tail) row hdepth hrow rd7643
                have rdRest := ih next rest hrest (drop := x10)
                  (k := k + 1 + 87 + 22 * row.propagatedWords)
                  (C := C + 10 + row.gas) (by
                    simpa [next, sosDiagonalLoopAdvance, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using rdRow)
                have normalized := rdRest.withIndices
                  (k' := k + (1 + 87 + 22 * row.propagatedWords + rest.steps))
                  (by omega) rfl
                simpa [next, sosDiagonalLoopAdvance, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using normalized

def sosOffDiagonalSetupAw (aw aOff : UInt256) : UInt256 := readWords1 aw aOff

def sosOffDiagonalSetupGas (aw aOff : UInt256) : Nat :=
  72 + (Cₘ (sosOffDiagonalSetupAw aw aOff) - Cₘ aw)

def sosOffDiagonalInitial
    (mem : ByteArray) (aw sRow aOff : UInt256) : SOSOffDiagonalState where
  operandPtr := aOff + ⟨32⟩
  resultPtr := sRow
  carry := ⟨0⟩
  memory := mem
  activeWords := sosOffDiagonalSetupAw aw aOff

def sosOffDiagonalBoundaryMemory (state : SOSOffDiagonalState) : ByteArray :=
  state.carry.toByteArray.write 0 state.memory state.resultPtr.toNat 32

def sosOffDiagonalBoundaryAw (state : SOSOffDiagonalState) : UInt256 :=
  UInt256.ofNat (MachineState.M state.activeWords.toNat state.resultPtr.toNat 32)

def sosOffDiagonalBoundaryGas (state : SOSOffDiagonalState) : Nat :=
  79 + (Cₘ (sosOffDiagonalBoundaryAw state) - Cₘ state.activeWords)

structure SOSOffDiagonalRowSelection where
  products : Nat
  finalMemory : ByteArray
  finalActiveWords : UInt256
  gas : Nat

def selectSOSOffDiagonalRow
    (productFuel : Nat) (mem : ByteArray) (aw sRow aOff aEnd : UInt256) :
    Option SOSOffDiagonalRowSelection :=
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  if initial.operandPtr.lt aEnd = ⟨0⟩ then
    some {
      products := 0
      finalMemory := sosOffDiagonalBoundaryMemory initial
      finalActiveWords := sosOffDiagonalBoundaryAw initial
      gas := sosOffDiagonalSetupGas aw aOff + 10 + sosOffDiagonalBoundaryGas initial }
  else
    let a := readWord mem aw aOff
    match selectSOSOffDiagonal productFuel a aEnd initial with
    | none => none
    | some products => some {
        products := products.words
        finalMemory := sosOffDiagonalBoundaryMemory products.final
        finalActiveWords := sosOffDiagonalBoundaryAw products.final
        gas := sosOffDiagonalSetupGas aw aOff + 10 + products.gas +
          sosOffDiagonalBoundaryGas products.final }

theorem selectedSOSOffDiagonalRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C productFuel : Nat} {tail : List UInt256}
    {sRow aOff x2 x3 aEnd x5 x6 x8 x9 x10 x11 x12 : UInt256}
    (selected : SOSOffDiagonalRowSelection)
    (hdepth : tail.length + 12 ≤ 1012)
    (hselect : selectSOSOffDiagonalRow productFuel mem aw sRow aOff aEnd = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7776⟩
      (sRow :: aOff :: x2 :: x3 :: aEnd :: x5 :: x6 :: x8 :: x9 ::
        x10 :: x11 :: x12 :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7280⟩
      (⟨7776⟩ :: (⟨32⟩ + aOff).lt aEnd :: (⟨64⟩ + sRow) ::
        (⟨32⟩ + aOff) :: x2 :: x3 :: aEnd :: x5 :: x6 :: x12 ::
        x9 :: x10 :: x11 :: x12 :: tail)
      selected.finalMemory selected.finalActiveWords rdata acc
      (k + 53 + 56 * selected.products) (C + selected.gas) := by
  let initial := sosOffDiagonalInitial mem aw sRow aOff
  let a := readWord mem aw aOff
  unfold selectSOSOffDiagonalRow at hselect
  dsimp only at hselect
  have rd7812 := GeneratedTraces.trace_7776_body
    (tail := x10 :: x11 :: x12 :: tail)
    (by simp only [List.length_cons]; omega) h
  by_cases hempty : initial.operandPtr.lt aEnd = ⟨0⟩
  · rw [if_pos hempty] at hselect
    cases hselect
    have rd7813 := rd7812.jumpiNT (by native_decide) (by
      simpa [initial, sosOffDiagonalInitial] using hempty)
      (by simp only [List.length_cons]; omega)
    have rd7287 := GeneratedTraces.trace_7806_body (tail := tail) (by omega) (by
      simpa [initial, a, sosOffDiagonalInitial, sosOffDiagonalSetupAw,
        sosOffDiagonalBoundaryMemory, sosOffDiagonalBoundaryAw, readWord, readWords1]
        using rd7813)
    have normalized := rd7287.withIndices (k' := k + 53 + 56 * 0) (by omega) rfl
    simpa [initial, a, sosOffDiagonalSetupGas, sosOffDiagonalBoundaryGas,
      sosOffDiagonalInitial, sosOffDiagonalSetupAw, sosOffDiagonalBoundaryMemory,
      sosOffDiagonalBoundaryAw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using normalized
  · rw [if_neg hempty] at hselect
    cases hproducts : selectSOSOffDiagonal productFuel a aEnd initial with
    | none => rw [hproducts] at hselect; contradiction
    | some products =>
        rw [hproducts] at hselect
        cases hselect
        have rd7838 := rd7812.jumpiT (by native_decide) (by
          simpa [initial, sosOffDiagonalInitial] using hempty)
          (by native_decide) (by simp only [List.length_cons]; omega)
        have rd7813 := selectedSOSOffDiagonalExact initial products
          (tail := x9 :: x5 :: x6 :: x10 :: x11 :: x12 :: tail)
          (by simp only [List.length_cons]; omega) hproducts (by
            simpa [initial, a, sosOffDiagonalInitial, sosOffDiagonalSetupAw,
              readWord, readWords1] using rd7838)
        have rd7287 := GeneratedTraces.trace_7806_body (tail := tail) (by omega) (by
          simpa [sosOffDiagonalBoundaryMemory, sosOffDiagonalBoundaryAw] using rd7813)
        have normalized := rd7287.withIndices
          (k' := k + 53 + 56 * products.words) (by omega) rfl
        simpa [initial, a, sosOffDiagonalSetupGas, sosOffDiagonalBoundaryGas,
          sosOffDiagonalInitial, sosOffDiagonalSetupAw, sosOffDiagonalBoundaryMemory,
          sosOffDiagonalBoundaryAw, readWords1, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
          using normalized

structure SOSOffDiagonalLoopState where
  sRow : UInt256
  aOff : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosOffDiagonalLoopAdvance
    (state : SOSOffDiagonalLoopState) (row : SOSOffDiagonalRowSelection) :
    SOSOffDiagonalLoopState where
  sRow := state.sRow + ⟨64⟩
  aOff := state.aOff + ⟨32⟩
  memory := row.finalMemory
  activeWords := row.finalActiveWords

structure SOSOffDiagonalLoopSelection where
  rows : Nat
  products : List Nat
  final : SOSOffDiagonalLoopState
  finalDrop : UInt256
  steps : Nat
  gas : Nat

def selectSOSOffDiagonalLoop : Nat → Nat → UInt256 → UInt256 → UInt256 →
    SOSOffDiagonalLoopState → Option SOSOffDiagonalLoopSelection
  | 0, _, _, _, _, _ => none
  | rowFuel + 1, productFuel, aEnd, fixedDrop, drop, state =>
      if state.aOff.lt aEnd = ⟨0⟩ then
        some {
          rows := 0
          products := []
          final := state
          finalDrop := drop
          steps := 1
          gas := 10 }
      else
        match selectSOSOffDiagonalRow productFuel state.memory state.activeWords
            state.sRow state.aOff aEnd with
        | none => none
        | some row =>
            let next := sosOffDiagonalLoopAdvance state row
            match selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop fixedDrop next with
            | none => none
            | some rest => some {
                rows := rest.rows + 1
                products := row.products :: rest.products
                final := rest.final
                finalDrop := rest.finalDrop
                steps := 1 + 53 + 56 * row.products + rest.steps
                gas := 10 + row.gas + rest.gas }

theorem selectedSOSOffDiagonalLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C rowFuel productFuel : Nat} {tail : List UInt256}
    {x2 x3 aEnd x5 x6 drop x9 x10 x11 x12 : UInt256}
    (state : SOSOffDiagonalLoopState) (selected : SOSOffDiagonalLoopSelection)
    (hdepth : tail.length + 12 ≤ 1012)
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd x12 drop state =
      some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7280⟩
      (⟨7776⟩ :: state.aOff.lt aEnd :: state.sRow :: state.aOff :: x2 :: x3 ::
        aEnd :: x5 :: x6 :: drop :: x9 :: x10 :: x11 :: x12 :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7281⟩
      (selected.final.sRow :: selected.final.aOff :: x2 :: x3 :: aEnd :: x5 :: x6 ::
        selected.finalDrop :: x9 :: x10 :: x11 :: x12 :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction rowFuel generalizing state selected k C drop with
  | zero => simp [selectSOSOffDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSOffDiagonalLoop] at hselect
      by_cases hexit : state.aOff.lt aEnd = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        have rd7288 := h.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7288
      · rw [if_neg hexit] at hselect
        cases hrow : selectSOSOffDiagonalRow productFuel state.memory state.activeWords
            state.sRow state.aOff aEnd with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            let next := sosOffDiagonalLoopAdvance state row
            cases hrest : selectSOSOffDiagonalLoop rowFuel productFuel aEnd x12 x12 next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                cases hselect
                have rd7783 := h.jumpiT (by native_decide) hexit
                  (by native_decide) (by simp only [List.length_cons]; omega)
                have rdRow := selectedSOSOffDiagonalRowExact (tail := tail) row
                  hdepth hrow rd7783
                have haOff : (⟨32⟩ : UInt256) + state.aOff = state.aOff + ⟨32⟩ := by
                  apply u256_inj
                  rw [uadd_toNat, uadd_toNat, Nat.add_comm]
                have hsRow : (⟨64⟩ : UInt256) + state.sRow = state.sRow + ⟨64⟩ := by
                  apply u256_inj
                  rw [uadd_toNat, uadd_toNat, Nat.add_comm]
                rw [haOff, hsRow] at rdRow
                have rdRest := ih next rest hrest (drop := x12)
                  (k := k + 1 + 53 + 56 * row.products)
                  (C := C + 10 + row.gas) (by
                    simpa [next, sosOffDiagonalLoopAdvance, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using rdRow)
                have normalized := rdRest.withIndices
                  (k' := k + (1 + 53 + 56 * row.products + rest.steps))
                  (by omega) rfl
                simpa [next, sosOffDiagonalLoopAdvance, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using normalized

structure SOSDoublePhaseSelection where
  words : Nat
  final : SOSDoubleState
  steps : Nat
  gas : Nat

def selectSOSDoublePhase
    (fuel : Nat) (stop : UInt256) (state : SOSDoubleState) :
    Option SOSDoublePhaseSelection :=
  if state.ptr.lt stop = ⟨0⟩ then
    some { words := 0, final := state, steps := 1, gas := 10 }
  else
    match selectSOSDouble fuel stop state with
    | none => none
    | some words => some {
        words := words.words
        final := words.final
        steps := 1 + 30 * words.words
        gas := 10 + words.gas }

theorem selectedSOSDoublePhaseExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {stop s3 s4 s5 s6 s7 s8 s9 s10 s11 : UInt256}
    (state : SOSDoubleState) (selected : SOSDoublePhaseSelection)
    (hdepth : tail.length + 12 ≤ 1021) (hfixed : s7 = s11)
    (hselect : selectSOSDoublePhase fuel stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7293⟩
      (⟨7747⟩ :: state.ptr.lt stop ::
        sosDoubleStack state stop (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7294⟩
      (sosDoubleStack selected.final stop
        (s3 :: s4 :: s5 :: s6 :: s7 :: s8 :: s9 :: s10 :: s11 :: tail))
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  unfold selectSOSDoublePhase at hselect
  by_cases hempty : state.ptr.lt stop = ⟨0⟩
  · rw [if_pos hempty] at hselect
    cases hselect
    have rd7301 := h.jumpiNT (by native_decide) hempty
      (by simp only [sosDoubleStack, List.length_cons]; omega)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7301
  · rw [if_neg hempty] at hselect
    cases hwords : selectSOSDouble fuel stop state with
    | none => rw [hwords] at hselect; contradiction
    | some words =>
        rw [hwords] at hselect
        cases hselect
        have rd7754 := h.jumpiT (by native_decide) hempty
          (by native_decide) (by simp only [sosDoubleStack, List.length_cons]; omega)
        have rd7301 := selectedSOSDoubleExact state words hdepth hfixed hwords rd7754
        have normalized := rd7301.withIndices
          (k' := k + (1 + 30 * words.words)) (by omega) rfl
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized


end Modexp.MultiLimbMontgomerySOSLoop
