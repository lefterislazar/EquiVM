import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSLoop

/-! # Complete selected SOS square construction and reduction -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSLoop

open Modexp.MultiLimbMontgomerySOSTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure SOSSquareSelection where
  double : SOSDoublePhaseSelection
  diagonal : SOSDiagonalLoopSelection
  reduction : SOSReductionLoopSelection
  steps : Nat
  gas : Nat

theorem selectSOSDiagonalLoop_finalDrop
    {rowFuel carryFuel : Nat} {stop fixedDrop : UInt256}
    {state : SOSDiagonalLoopState} {selected : SOSDiagonalLoopSelection}
    (hselect : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop fixedDrop state =
      some selected) :
    selected.finalDrop = fixedDrop := by
  induction rowFuel generalizing state selected with
  | zero => simp [selectSOSDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSDiagonalLoop] at hselect
      by_cases hexit : state.aOff.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        rfl
      · rw [if_neg hexit] at hselect
        cases hrow : selectSOSDiagonal carryFuel state.memory state.activeWords
            state.sOff state.aOff with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            cases hrest : selectSOSDiagonalLoop rowFuel carryFuel stop fixedDrop fixedDrop
                (sosDiagonalLoopAdvance state row) with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                change rest.finalDrop = fixedDrop
                exact ih (state := sosDiagonalLoopAdvance state row)
                  (selected := rest) hrest

/-- Execute the same guards and arithmetic states as the deployed doubling, diagonal, and
reduction phases.  Every fuel argument is explicit, so this exact-gas selector is total. -/
def selectSOSSquare
    (doubleFuel diagonalFuel reductionFuel columnFuel carryFuel : Nat)
    (mem : ByteArray) (aw sEnd aP aEnd sP n0inv kWords nBefore nP : UInt256) :
    Option SOSSquareSelection :=
  let doubleState : SOSDoubleState := {
    carry := ⟨0⟩
    ptr := sP
    memory := mem
    activeWords := aw }
  match selectSOSDoublePhase doubleFuel sEnd doubleState with
  | none => none
  | some double =>
      let diagonalState : SOSDiagonalLoopState := {
        sOff := sP
        aOff := aP
        memory := double.final.memory
        activeWords := double.final.activeWords }
      match selectSOSDiagonalLoop diagonalFuel carryFuel aEnd kWords kWords diagonalState with
      | none => none
      | some diagonal =>
          let reductionState : SOSReductionLoopState := {
            sBase := sP
            memory := diagonal.final.memory
            activeWords := diagonal.final.activeWords }
          match selectSOSReductionLoop reductionFuel columnFuel carryFuel nP n0inv nBefore
              (nBefore + kWords + ⟨32⟩) (sP + kWords) reductionState with
          | none => none
          | some reduction => some {
              double := double
              diagonal := diagonal
              reduction := reduction
              steps := 10 + double.steps + 9 + diagonal.steps + 19 + reduction.steps
              gas := 25 + double.gas + 22 + diagonal.gas + 52 + reduction.gas }

/-- Successful square selection is the exact deployed SOS computation through reduction. -/
theorem selectedSOSSquareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C doubleFuel diagonalFuel reductionFuel columnFuel carryFuel : Nat}
    {tail : List UInt256}
    {junk0 junk1 sEnd aP aEnd sP n0inv kWords nBefore x7 nP : UInt256}
    (selected : SOSSquareSelection)
    (hdepth : tail.length + 12 ≤ 1012)
    (hselect : selectSOSSquare doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      mem aw sEnd aP aEnd sP n0inv kWords nBefore nP = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7281⟩
      (junk0 :: junk1 :: sEnd :: aP :: aEnd :: sP :: n0inv :: kWords ::
        nBefore :: x7 :: nP :: kWords :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7329⟩
      (n0inv :: nBefore :: (sP + kWords) :: selected.reduction.final.sBase ::
        kWords :: (nBefore + kWords + ⟨32⟩) :: x7 :: nP :: kWords :: tail)
      selected.reduction.final.memory selected.reduction.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  let doubleState : SOSDoubleState := {
    carry := ⟨0⟩
    ptr := sP
    memory := mem
    activeWords := aw }
  unfold selectSOSSquare at hselect
  dsimp only at hselect
  cases hdouble : selectSOSDoublePhase doubleFuel sEnd doubleState with
  | none => rw [hdouble] at hselect; contradiction
  | some double =>
      rw [hdouble] at hselect
      dsimp only at hselect
      let diagonalState : SOSDiagonalLoopState := {
        sOff := sP
        aOff := aP
        memory := double.final.memory
        activeWords := double.final.activeWords }
      cases hdiagonal : selectSOSDiagonalLoop diagonalFuel carryFuel
          aEnd kWords kWords diagonalState with
      | none => rw [hdiagonal] at hselect; contradiction
      | some diagonal =>
          rw [hdiagonal] at hselect
          dsimp only at hselect
          let reductionState : SOSReductionLoopState := {
            sBase := sP
            memory := diagonal.final.memory
            activeWords := diagonal.final.activeWords }
          cases hreduction : selectSOSReductionLoop reductionFuel columnFuel carryFuel
              nP n0inv nBefore (nBefore + kWords + ⟨32⟩) (sP + kWords)
              reductionState with
          | none => rw [hreduction] at hselect; contradiction
          | some reduction =>
              rw [hreduction] at hselect
              cases hselect
              have rd7300 := GeneratedTraces.trace_7281_body
                (tail := n0inv :: kWords :: nBefore :: x7 :: nP :: kWords :: tail)
                (by simp only [List.length_cons]; omega) h
              have rd7301 := selectedSOSDoublePhaseExact doubleState double
                (tail := tail) (by omega) rfl hdouble (by
                  simpa [doubleState, sosDoubleStack] using rd7300)
              have rd7312 := GeneratedTraces.trace_7294_body
                (tail := n0inv :: kWords :: nBefore :: x7 :: nP :: kWords :: tail)
                (by simp only [List.length_cons]; omega) rd7301
              have rd7313 := selectedSOSDiagonalLoopExact diagonalState diagonal
                (tail := tail) (drop := kWords) (by omega) hdiagonal (by
                  simpa [diagonalState] using rd7312)
              have rd7335 := GeneratedTraces.trace_7306_body
                (tail := x7 :: nP :: kWords :: tail)
                (by simp only [List.length_cons]; omega) rd7313
              have hdrop := selectSOSDiagonalLoop_finalDrop hdiagonal
              rw [hdrop] at rd7335
              have rd7336 := selectedSOSReductionLoopExact reductionState reduction
                (tail := tail) (by omega) hreduction (by
                  simpa [reductionState, Nat.add_assoc] using rd7335)
              have normalized := rd7336.withIndices
                (k' := k + (10 + double.steps + 9 + diagonal.steps + 19 +
                  reduction.steps)) (by omega) rfl
              simpa [doubleState, diagonalState, reductionState, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using normalized

end Modexp.MultiLimbMontgomerySOSLoop
