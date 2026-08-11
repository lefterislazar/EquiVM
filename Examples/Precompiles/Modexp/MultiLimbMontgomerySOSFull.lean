import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSExecutable

/-! # Complete executable SOS arithmetic body -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSFull

open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomerySOSExecutable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure SOSFullSelection where
  offDiagonal : SOSOffDiagonalLoopSelection
  suffix : SOSExecutableSelection
  steps : Nat
  gas : Nat

theorem selectSOSOffDiagonalLoop_finalDrop
    {rowFuel productFuel : Nat} {aEnd fixedDrop : UInt256}
    {state : SOSOffDiagonalLoopState} {selected : SOSOffDiagonalLoopSelection}
    (hselect : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop fixedDrop state =
      some selected) :
    selected.finalDrop = fixedDrop := by
  induction rowFuel generalizing state selected with
  | zero => simp [selectSOSOffDiagonalLoop] at hselect
  | succ rowFuel ih =>
      simp only [selectSOSOffDiagonalLoop] at hselect
      by_cases hexit : state.aOff.lt aEnd = ⟨0⟩
      · rw [if_pos hexit] at hselect
        cases hselect
        rfl
      · rw [if_neg hexit] at hselect
        cases hrow : selectSOSOffDiagonalRow productFuel state.memory state.activeWords
            state.sRow state.aOff aEnd with
        | none => rw [hrow] at hselect; contradiction
        | some row =>
            rw [hrow] at hselect
            dsimp only at hselect
            cases hrest : selectSOSOffDiagonalLoop rowFuel productFuel aEnd fixedDrop
                fixedDrop (sosOffDiagonalLoopAdvance state row) with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                change rest.finalDrop = fixedDrop
                exact ih (state := sosOffDiagonalLoopAdvance state row)
                  (selected := rest) hrest

/-- Execute the off-diagonal rows and every subsequent data-dependent SOS phase. -/
def selectSOSFull
    (rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      compareFuel subFuel : Nat)
    (state : SOSOffDiagonalLoopState)
    (sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase : UInt256) :
    Option SOSFullSelection :=
  match selectSOSOffDiagonalLoop rowFuel productFuel aEnd kWords kWords state with
  | none => none
  | some offDiagonal =>
      match selectSOSExecutable doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
          compareFuel subFuel offDiagonal.final.memory offDiagonal.final.activeWords sEnd aP
          aEnd sP n0inv kWords nBefore nP resultPtr resultBase with
      | none => none
      | some suffix => some {
          offDiagonal := offDiagonal
          suffix := suffix
          steps := offDiagonal.steps + suffix.steps
          gas := offDiagonal.gas + suffix.gas }

/-- A successful full selector is the exact deployed SOS arithmetic body through caller return. -/
theorem selectedSOSFullExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      compareFuel subFuel : Nat}
    {tail : List UInt256}
    {sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase returnPc : UInt256}
    (state : SOSOffDiagonalLoopState) (selected : SOSFullSelection)
    (hdepth : tail.length + 16 ≤ 1012)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectSOSFull rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel state sEnd aP aEnd sP n0inv kWords
      nBefore resultPtr nP resultBase = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7280⟩
      (⟨7776⟩ :: state.aOff.lt aEnd :: state.sRow :: state.aOff :: sEnd :: aP ::
        aEnd :: sP :: n0inv :: kWords :: nBefore :: resultPtr :: nP :: kWords ::
        returnPc :: resultBase :: tail)
      state.memory state.activeWords rdata acc k C) :
    SOSCopyReturnPost ee g s0 returnPc resultBase tail selected.suffix.copy.memory
      selected.suffix.copy.activeWords rdata acc (k + selected.steps) (C + selected.gas) := by
  unfold selectSOSFull at hselect
  cases hoff : selectSOSOffDiagonalLoop rowFuel productFuel aEnd kWords kWords state with
  | none => rw [hoff] at hselect; contradiction
  | some offDiagonal =>
      rw [hoff] at hselect
      cases hsuffix : selectSOSExecutable doubleFuel diagonalFuel reductionFuel columnFuel
          carryFuel compareFuel subFuel offDiagonal.final.memory
          offDiagonal.final.activeWords sEnd aP aEnd sP n0inv kWords nBefore nP resultPtr
          resultBase with
      | none => simp [hsuffix] at hselect
      | some suffix =>
          have hselected : selected = {
              offDiagonal := offDiagonal
              suffix := suffix
              steps := offDiagonal.steps + suffix.steps
              gas := offDiagonal.gas + suffix.gas } := by
            simpa [hsuffix] using hselect.symm
          subst selected
          have hdrop : offDiagonal.finalDrop = kWords :=
            selectSOSOffDiagonalLoop_finalDrop hoff
          have rd7288 := selectedSOSOffDiagonalLoopExact state offDiagonal
            (tail := returnPc :: resultBase :: tail) (by
              simp only [List.length_cons]
              omega) hoff h
          have rdReturn := selectedSOSExecutableExact suffix
            (tail := tail) (by omega) hreturn hsuffix (by
              simpa only [hdrop] using rd7288)
          simpa only [Nat.add_assoc] using rdReturn

end Modexp.MultiLimbMontgomerySOSFull
