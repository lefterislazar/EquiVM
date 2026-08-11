import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSComplete
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFinalizeCopy

/-! # Complete executable exact SOS square body -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSExecutable

open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomerySOSFinalize

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure SOSExecutableSelection where
  square : SOSSquareSelection
  finalCompare : SOSFinalCompareSelection
  copy : SOSCopySelection
  steps : Nat
  gas : Nat

/-- Execute every data-dependent SOS phase with explicit fuel and exact gas accounting. -/
def selectSOSExecutable
    (doubleFuel diagonalFuel reductionFuel columnFuel carryFuel compareFuel subFuel : Nat)
    (mem : ByteArray)
    (aw sEnd aP aEnd sP n0inv kWords nBefore nP resultPtr resultBase : UInt256) :
    Option SOSExecutableSelection :=
  match selectSOSSquare doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      mem aw sEnd aP aEnd sP n0inv kWords nBefore nP with
  | none => none
  | some square =>
      let squareMem := square.reduction.final.memory
      let squareAw := square.reduction.final.activeWords
      let sBase := square.reduction.final.sBase
      let nEnd := nBefore + kWords + ⟨32⟩
      match selectSOSFinalCompare compareFuel squareMem squareAw sBase kWords nEnd with
      | none => none
      | some finalCompare =>
          match selectSOSCopy subFuel squareMem finalCompare.activeWords sBase kWords
              finalCompare.doSub resultPtr nP resultBase with
          | none => none
          | some copy => some {
              square := square
              finalCompare := finalCompare
              copy := copy
              steps := square.steps + finalCompare.steps + copy.steps
              gas := square.gas + finalCompare.gas + copy.gas }

/-- A successful SOS selection is the exact deployed square body through caller return. -/
theorem selectedSOSExecutableExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C doubleFuel diagonalFuel reductionFuel columnFuel carryFuel compareFuel subFuel : Nat}
    {tail : List UInt256}
    {junk0 junk1 sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP
      resultBase returnPc : UInt256}
    (selected : SOSExecutableSelection)
    (hdepth : tail.length + 14 ≤ 1012)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectSOSExecutable doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel mem aw sEnd aP aEnd sP n0inv kWords nBefore
      nP resultPtr resultBase = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7281⟩
      (junk0 :: junk1 :: sEnd :: aP :: aEnd :: sP :: n0inv :: kWords ::
        nBefore :: resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      mem aw rdata acc k C) :
    SOSCopyReturnPost ee g s0 returnPc resultBase tail selected.copy.memory
      selected.copy.activeWords rdata acc (k + selected.steps) (C + selected.gas) := by
  unfold selectSOSExecutable at hselect
  cases hsquare : selectSOSSquare doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel mem aw sEnd aP aEnd sP n0inv kWords nBefore nP with
  | none => rw [hsquare] at hselect; contradiction
  | some square =>
      rw [hsquare] at hselect
      dsimp only at hselect
      let squareMem := square.reduction.final.memory
      let squareAw := square.reduction.final.activeWords
      let sBase := square.reduction.final.sBase
      let nEnd := nBefore + kWords + ⟨32⟩
      cases hcompare : selectSOSFinalCompare compareFuel squareMem squareAw sBase
          kWords nEnd with
      | none => rw [hcompare] at hselect; contradiction
      | some finalCompare =>
          rw [hcompare] at hselect
          cases hcopy : selectSOSCopy subFuel squareMem finalCompare.activeWords sBase
              kWords finalCompare.doSub resultPtr nP resultBase with
          | none =>
              simp [squareMem, squareAw, sBase, nEnd, hcopy] at hselect
          | some copy =>
              have hselected : selected = {
                  square := square
                  finalCompare := finalCompare
                  copy := copy
                  steps := square.steps + finalCompare.steps + copy.steps
                  gas := square.gas + finalCompare.gas + copy.gas } := by
                simpa [squareMem, squareAw, sBase, nEnd, hcopy] using hselect.symm
              subst selected
              have rd7336 := selectedSOSSquareExact square
                (tail := returnPc :: resultBase :: tail) (by
                  simpa only [List.length_cons] using hdepth) hsquare h
              have rd7354 := selectedSOSFinalCompareExact finalCompare
                (fuel := compareFuel) (drop0 := n0inv) (drop1 := nBefore)
                (drop2 := sP + kWords) (sBase := sBase) (bytes := kWords)
                (nEnd := nEnd) (resultPtr := resultPtr) (nP := nP)
                (tail := returnPc :: resultBase :: tail) (by
                  simp only [List.length_cons]
                  omega) hcompare (by
                  simpa [sBase, nEnd, squareMem, squareAw] using rd7336)
              have rdReturn := selectedSOSCopyExact copy
                (fuel := subFuel) (tOff := finalCompare.tOff)
                (nOff := finalCompare.nOff) (source := sBase) (bytes := kWords)
                (doSub := finalCompare.doSub) (resultPtr := resultPtr) (nP := nP)
                (returnPc := returnPc) (resultBase := resultBase) (tail := tail)
                (by omega) hreturn hcopy (by
                  simpa [SOSComparePost, squareMem] using rd7354)
              simpa [squareMem, squareAw, sBase, nEnd,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

end Modexp.MultiLimbMontgomerySOSExecutable
