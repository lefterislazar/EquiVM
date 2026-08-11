import Examples.Precompiles.Modexp.MultiLimbMontgomeryCompareLoop

/-! # Complete generated CIOS outer iterations -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomeryTrace

open Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure CIOSOuterState where
  aOff : UInt256
  memory : ByteArray
  activeWords : UInt256

def ciosMultiplyInitial (bP tP : UInt256) (state : CIOSOuterState) : MultiplyPassState where
  operandPtr := bP
  resultPtr := tP
  carry := ⟨0⟩
  memory := state.memory
  activeWords := ciosOuterAw state.activeWords state.aOff

def ciosMultiplyFinal (columns : Nat) (bP tP : UInt256)
    (state : CIOSOuterState) : MultiplyPassState :=
  let initial := ciosMultiplyInitial bP tP state
  multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
    (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff)
      (columns - 1) initial)

def ciosAfterBoundaryMemory (columns : Nat) (bP tP tEnd tk1Off : UInt256)
    (state : CIOSOuterState) : ByteArray :=
  let final := ciosMultiplyFinal columns bP tP state
  ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off

def ciosAfterBoundaryAw (columns : Nat) (bP tP tEnd tk1Off nP : UInt256)
    (state : CIOSOuterState) : UInt256 :=
  let final := ciosMultiplyFinal columns bP tP state
  ciosBoundaryAw final.activeWords tEnd tk1Off tP nP

def ciosReductionFactor (columns : Nat)
    (bP tP tEnd tk1Off n0inv : UInt256) (state : CIOSOuterState) : UInt256 :=
  let final := ciosMultiplyFinal columns bP tP state
  ciosBoundaryFactor final.memory final.activeWords tEnd final.carry tk1Off tP n0inv

def ciosReductionCarry (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv : UInt256) (state : CIOSOuterState) : UInt256 :=
  let final := ciosMultiplyFinal columns bP tP state
  ciosBoundaryCarry final.memory final.activeWords tEnd final.carry tk1Off tP nP n0inv

def ciosReductionInitial (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : SchoolbookState where
  operandPtr := nBefore + ⟨64⟩
  resultPtr := tOff
  carry := ciosReductionCarry columns bP tP tEnd tk1Off nP n0inv state
  memory := ciosAfterBoundaryMemory columns bP tP tEnd tk1Off state
  activeWords := ciosAfterBoundaryAw columns bP tP tEnd tk1Off nP state

def ciosReductionFinal (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : SchoolbookState :=
  let initial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  schoolbookAdvance factor (schoolbookIterate factor (columns - 2) initial)

def ciosOuterAdvance (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : CIOSOuterState :=
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  { aOff := state.aOff + ⟨32⟩
    memory := ciosShiftMemory final.memory final.activeWords final.carry
      shiftedOut tk1Off tEnd
    activeWords := ciosShiftAw final.activeWords shiftedOut tk1Off tEnd }

def ciosOuterIterationGasAfter (C columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Nat :=
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  ciosShiftGasAfter
    (ciosBoundaryGasAfter
      (ciosOuterGasAfter C state.activeWords state.aOff + 10 +
        multiplyPassThroughExitGas ai (columns - 1) multiplyInitial)
      multiplyFinal.activeWords tEnd tk1Off tP nP + 10 +
      schoolbookThroughExitGas factor (columns - 2) reductionInitial)
    reductionFinal.activeWords shiftedOut tk1Off tEnd + 10

def ciosOuterIterationGas (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Nat :=
  ciosOuterIterationGasAfter 0 columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state

/-- One complete generated CIOS outer iteration, from its loop head through both arithmetic
passes, upper-word shift, and the taken outer back-edge. -/
theorem ciosOuterIteration
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C columns : Nat} {tail : List UInt256}
    {bP n0inv shiftedOut tk1Off aEnd tOff nBefore tP tEnd nP
      tail0 tail1 : UInt256}
    (state : CIOSOuterState)
    (hdepth : tail.length + 17 ≤ 1014)
    (hcolumns : 1 < columns)
    (houter : tP.lt tEnd ≠ ⟨0⟩)
    (hmultiplyContinue : ∀ j, j < columns - 1 →
      (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
        (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff) j
          (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hmultiplyExit :
      (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
        (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff)
          (columns - 1) (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd = ⟨0⟩)
    (hreductionStart : tOff.lt tEnd ≠ ⟨0⟩)
    (hreductionContinue : ∀ j, j < columns - 2 →
      (schoolbookAdvance
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (schoolbookIterate
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state))).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hreductionExit :
      (schoolbookAdvance
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (schoolbookIterate
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
          (columns - 2)
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state))).resultPtr.lt tEnd = ⟨0⟩)
    (hnext : (state.aOff + ⟨32⟩).lt aEnd ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (state.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      state.memory state.activeWords rdata acc k C) :
    let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state
    RDx runtimeBytecode ee g s0 ⟨4312⟩
      (next.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      next.memory next.activeWords rdata acc
      (k + 126 + 56 * columns + 61 * (columns - 1))
      (ciosOuterIterationGasAfter C columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state) := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let boundaryMemory := ciosAfterBoundaryMemory columns bP tP tEnd tk1Off state
  let boundaryAw := ciosAfterBoundaryAw columns bP tP tEnd tk1Off nP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have rdBoundary := ciosOuterThroughPeeledReduction
    (n := columns - 1) (tail := tail) (hdepth := by omega) houter
    (by simpa only [ai, multiplyInitial, ciosMultiplyInitial] using hmultiplyContinue)
    (by simpa only [ai, multiplyInitial, ciosMultiplyInitial] using hmultiplyExit) h
  have rdOuterGuard := ciosReductionThroughOuterGuard
    (n := columns - 2) (tail := tail) (hdepth := hdepth)
    (operandPtr := nBefore + ⟨64⟩) (resultPtr := tOff)
    (factor := factor)
    (carry := ciosReductionCarry columns bP tP tEnd tk1Off nP n0inv state)
    hreductionStart
    (by simpa only [factor, reductionInitial, ciosReductionInitial] using
      hreductionContinue)
    (by simpa only [factor, reductionInitial, ciosReductionInitial] using
      hreductionExit)
    (by
      simpa only [ai, multiplyInitial, multiplyFinal, boundaryMemory, boundaryAw,
        factor, ciosMultiplyFinal, ciosAfterBoundaryMemory, ciosAfterBoundaryAw,
        ciosReductionFactor, ciosReductionCarry] using rdBoundary)
  have rdNext := rdOuterGuard.jumpiT (by native_decide) hnext (by native_decide)
    (by simp only [List.length_cons]; omega)
  have normalized := rdNext.withIndices
    (k' := k + 126 + 56 * columns + 61 * (columns - 1))
    (C' := ciosOuterIterationGasAfter C columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state)
    (by omega) (by
      simp only [ciosOuterIterationGasAfter, ciosMultiplyInitial,
        ciosMultiplyFinal, ciosReductionInitial, ciosReductionFinal,
        ciosReductionFactor, factor])
  simpa only [ciosOuterAdvance, reductionFinal, Nat.add_assoc] using normalized

def ciosOuterIterate (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256) :
    Nat → CIOSOuterState → CIOSOuterState
  | 0, state => state
  | n + 1, state =>
      ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut n state)

def ciosOuterIterationsGasAfter (C columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256) :
    Nat → CIOSOuterState → Nat
  | 0, _ => C
  | n + 1, state =>
      ciosOuterIterationGasAfter
        (ciosOuterIterationsGasAfter C columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut n state)
        columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut n state)

structure CIOSOuterIterationFacts (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore aEnd : UInt256)
    (state : CIOSOuterState) : Prop where
  multiplyContinue : ∀ j, j < columns - 1 →
    (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
      (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff) j
        (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd ≠ ⟨0⟩
  multiplyExit :
    (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
      (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff)
        (columns - 1) (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd = ⟨0⟩
  reductionContinue : ∀ j, j < columns - 2 →
    (schoolbookAdvance
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
      (schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state))).resultPtr.lt tEnd ≠ ⟨0⟩
  reductionExit :
    (schoolbookAdvance
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
      (schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 2)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state))).resultPtr.lt tEnd = ⟨0⟩
  next : (state.aOff + ⟨32⟩).lt aEnd ≠ ⟨0⟩

/-- The Solidity memory layout determines all nested CIOS guards.  These are the only pointer
premises needed for a normal `k >= 2` iteration. -/
theorem ciosOuterIterationFacts_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore aEnd : UInt256)
    (state : CIOSOuterState)
    (hcolumns : 1 < columns)
    (hmultiplyBound : tP.toNat + 32 * columns < UInt256.size)
    (hmultiplyStop : tEnd.toNat = tP.toNat + 32 * columns)
    (hreductionBound : tOff.toNat + 32 * (columns - 1) < UInt256.size)
    (hreductionStop : tEnd.toNat = tOff.toNat + 32 * (columns - 1))
    (hnext : (state.aOff + ⟨32⟩).lt aEnd ≠ ⟨0⟩) :
    tP.lt tEnd ≠ ⟨0⟩ ∧ tOff.lt tEnd ≠ ⟨0⟩ ∧
      CIOSOuterIterationFacts columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore aEnd state := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hmultiply := multiplyPassGuardFacts ai tEnd columns multiplyInitial
    (by omega) (by simpa [multiplyInitial, ciosMultiplyInitial] using hmultiplyBound)
    (by simpa [multiplyInitial, ciosMultiplyInitial] using hmultiplyStop)
  have hreduction := schoolbookGuardFacts factor tEnd (columns - 1) reductionInitial
    (by omega)
    (by simpa [reductionInitial, ciosReductionInitial] using hreductionBound)
    (by simpa [reductionInitial, ciosReductionInitial] using hreductionStop)
  have houterNat : tP.toNat < tEnd.toNat := by
    rw [hmultiplyStop]
    omega
  have hreductionNat : tOff.toNat < tEnd.toNat := by
    rw [hreductionStop]
    omega
  have houter : tP.lt tEnd ≠ ⟨0⟩ := by
    rw [ult_one houterNat]
    decide
  have hredStart : tOff.lt tEnd ≠ ⟨0⟩ := by
    rw [ult_one hreductionNat]
    decide
  refine ⟨houter, hredStart, ?_⟩
  refine
    { multiplyContinue := ?_
      multiplyExit := ?_
      reductionContinue := ?_
      reductionExit := ?_
      next := hnext }
  · simpa only [ai, multiplyInitial] using hmultiply.1
  · simpa only [ai, multiplyInitial] using hmultiply.2
  · simpa only [factor, reductionInitial, Nat.sub_sub] using hreduction.1
  · simpa only [factor, reductionInitial, Nat.sub_sub] using hreduction.2

/-- Execute any number of complete generated CIOS outer iterations.  This contract traverses
both nested arithmetic loops on every iteration and retains their exact memory evolution. -/
theorem ciosOuterIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C columns iterations : Nat} {tail : List UInt256}
    {bP n0inv shiftedOut tk1Off aEnd tOff nBefore tP tEnd nP
      tail0 tail1 : UInt256}
    (state : CIOSOuterState)
    (hdepth : tail.length + 17 ≤ 1014)
    (hcolumns : 1 < columns)
    (houter : tP.lt tEnd ≠ ⟨0⟩)
    (hreductionStart : tOff.lt tEnd ≠ ⟨0⟩)
    (hfacts : ∀ j, j < iterations →
      CIOSOuterIterationFacts columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore aEnd
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut j state))
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (state.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      state.memory state.activeWords rdata acc k C) :
    let final := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut iterations state
    RDx runtimeBytecode ee g s0 ⟨4312⟩
      (final.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      final.memory final.activeWords rdata acc
      (k + iterations * (126 + 56 * columns + 61 * (columns - 1)))
      (ciosOuterIterationsGasAfter C columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut iterations state) := by
  induction iterations with
  | zero =>
      simpa [ciosOuterIterate, ciosOuterIterationsGasAfter] using h
  | succ iterations ih =>
      have hprefix : ∀ j, j < iterations →
          CIOSOuterIterationFacts columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore aEnd
            (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
              tOff nBefore shiftedOut j state) := by
        intro j hj
        exact hfacts j (by omega)
      have rdPrefix := ih hprefix
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut iterations state
      have facts := hfacts iterations (by omega)
      have rdNext := ciosOuterIteration current hdepth hcolumns houter
        facts.multiplyContinue facts.multiplyExit hreductionStart
        facts.reductionContinue facts.reductionExit facts.next rdPrefix
      have normalized := rdNext.withIndices
        (k' := k + (iterations + 1) *
          (126 + 56 * columns + 61 * (columns - 1)))
        (by ring) rfl
      simpa only [ciosOuterIterate, ciosOuterIterationsGasAfter, current]
        using normalized

/-- The last complete CIOS iteration, whose outer guard exits to finalization. -/
theorem ciosOuterFinalIteration
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C columns : Nat} {tail : List UInt256}
    {bP n0inv shiftedOut tk1Off aEnd tOff nBefore tP tEnd nP
      tail0 tail1 : UInt256}
    (state : CIOSOuterState)
    (hdepth : tail.length + 17 ≤ 1014)
    (hcolumns : 1 < columns)
    (houter : tP.lt tEnd ≠ ⟨0⟩)
    (hmultiplyContinue : ∀ j, j < columns - 1 →
      (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
        (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff) j
          (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hmultiplyExit :
      (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
        (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff)
          (columns - 1) (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd = ⟨0⟩)
    (hreductionStart : tOff.lt tEnd ≠ ⟨0⟩)
    (hreductionContinue : ∀ j, j < columns - 2 →
      (schoolbookAdvance
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (schoolbookIterate
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state))).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hreductionExit :
      (schoolbookAdvance
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (schoolbookIterate
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
          (columns - 2)
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state))).resultPtr.lt tEnd = ⟨0⟩)
    (hexit : (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (state.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      state.memory state.activeWords rdata acc k C) :
    let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state
    RDx runtimeBytecode ee g s0 ⟨4147⟩
      (next.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      next.memory next.activeWords rdata acc
      (k + 126 + 56 * columns + 61 * (columns - 1))
      (ciosOuterIterationGasAfter C columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state) := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let boundaryMemory := ciosAfterBoundaryMemory columns bP tP tEnd tk1Off state
  let boundaryAw := ciosAfterBoundaryAw columns bP tP tEnd tk1Off nP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have rdBoundary := ciosOuterThroughPeeledReduction
    (n := columns - 1) (tail := tail) (hdepth := by omega) houter
    (by simpa only [ai, multiplyInitial, ciosMultiplyInitial] using hmultiplyContinue)
    (by simpa only [ai, multiplyInitial, ciosMultiplyInitial] using hmultiplyExit) h
  have rdOuterGuard := ciosReductionThroughOuterGuard
    (n := columns - 2) (tail := tail) (hdepth := hdepth)
    (operandPtr := nBefore + ⟨64⟩) (resultPtr := tOff)
    (factor := factor)
    (carry := ciosReductionCarry columns bP tP tEnd tk1Off nP n0inv state)
    hreductionStart
    (by simpa only [factor, reductionInitial, ciosReductionInitial] using
      hreductionContinue)
    (by simpa only [factor, reductionInitial, ciosReductionInitial] using
      hreductionExit)
    (by
      simpa only [ai, multiplyInitial, multiplyFinal, boundaryMemory, boundaryAw,
        factor, ciosMultiplyFinal, ciosAfterBoundaryMemory, ciosAfterBoundaryAw,
        ciosReductionFactor, ciosReductionCarry] using rdBoundary)
  have rdExit := rdOuterGuard.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices
    (k' := k + 126 + 56 * columns + 61 * (columns - 1))
    (C' := ciosOuterIterationGasAfter C columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state)
    (by omega) (by
      simp only [ciosOuterIterationGasAfter, ciosMultiplyInitial,
        ciosMultiplyFinal, ciosReductionInitial, ciosReductionFinal,
        ciosReductionFactor, factor])
  simpa only [ciosOuterAdvance, reductionFinal, Nat.add_assoc] using normalized

/-- Complete the entire generated CIOS outer loop: `iterations` taken back-edges followed by
one final full arithmetic iteration and the exit to PC 4147. -/
theorem ciosOuterIterationsThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C columns iterations : Nat} {tail : List UInt256}
    {bP n0inv shiftedOut tk1Off aEnd tOff nBefore tP tEnd nP
      tail0 tail1 : UInt256}
    (state : CIOSOuterState)
    (hdepth : tail.length + 17 ≤ 1014)
    (hcolumns : 1 < columns)
    (houter : tP.lt tEnd ≠ ⟨0⟩)
    (hreductionStart : tOff.lt tEnd ≠ ⟨0⟩)
    (hfacts : ∀ j, j < iterations →
      CIOSOuterIterationFacts columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore aEnd
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut j state))
    (hmultiplyContinue : ∀ j, j < columns - 1 →
      (multiplyPassAdvance
        (ciosOuterAi
          (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut iterations state).memory
          (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut iterations state).activeWords
          (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut iterations state).aOff)
        (multiplyPassIterate
          (ciosOuterAi
            (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
              tOff nBefore shiftedOut iterations state).memory
            (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
              tOff nBefore shiftedOut iterations state).activeWords
            (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
              tOff nBefore shiftedOut iterations state).aOff)
          j (ciosMultiplyInitial bP tP
            (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
              tOff nBefore shiftedOut iterations state)))).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hfinalMultiplyExit :
      let final := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut iterations state
      (multiplyPassAdvance (ciosOuterAi final.memory final.activeWords final.aOff)
        (multiplyPassIterate (ciosOuterAi final.memory final.activeWords final.aOff)
          (columns - 1) (ciosMultiplyInitial bP tP final))).resultPtr.lt tEnd = ⟨0⟩)
    (hfinalReductionContinue :
      let final := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut iterations state
      ∀ j, j < columns - 2 →
        (schoolbookAdvance
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv final)
          (schoolbookIterate
            (ciosReductionFactor columns bP tP tEnd tk1Off n0inv final) j
            (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
              tOff nBefore final))).resultPtr.lt tEnd ≠ ⟨0⟩)
    (hfinalReductionExit :
      let final := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut iterations state
      (schoolbookAdvance
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv final)
        (schoolbookIterate
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv final)
          (columns - 2)
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore final))).resultPtr.lt tEnd = ⟨0⟩)
    (hfinalExit :
      let final := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut iterations state
      (final.aOff + ⟨32⟩).lt aEnd = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (state.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      state.memory state.activeWords rdata acc k C) :
    let final := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut (iterations + 1) state
    RDx runtimeBytecode ee g s0 ⟨4147⟩
      (final.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      final.memory final.activeWords rdata acc
      (k + (iterations + 1) *
        (126 + 56 * columns + 61 * (columns - 1)))
      (ciosOuterIterationsGasAfter C columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut (iterations + 1) state) := by
  have rdPrefix := ciosOuterIterations state hdepth hcolumns houter
    hreductionStart hfacts h
  let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut iterations state
  have rdFinal := ciosOuterFinalIteration current hdepth hcolumns houter
    (by simpa only [current] using hmultiplyContinue)
    (by simpa only [current] using hfinalMultiplyExit)
    hreductionStart
    (by simpa only [current] using hfinalReductionContinue)
    (by simpa only [current] using hfinalReductionExit)
    (by simpa only [current] using hfinalExit) rdPrefix
  have normalized := rdFinal.withIndices
    (k' := k + (iterations + 1) *
      (126 + 56 * columns + 61 * (columns - 1)))
    (by ring) rfl
  simpa only [ciosOuterIterate, ciosOuterIterationsGasAfter, current]
    using normalized

def ciosOuterAdvanceOne
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : CIOSOuterState :=
  let reduction := ciosReductionInitial 1 bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  { aOff := state.aOff + ⟨32⟩
    memory := ciosShiftMemory reduction.memory reduction.activeWords reduction.carry
      shiftedOut tk1Off tEnd
    activeWords := ciosShiftAw reduction.activeWords shiftedOut tk1Off tEnd }

def ciosOuterOneLimbGasAfter (C : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Nat :=
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal 1 bP tP state
  let reduction := ciosReductionInitial 1 bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  ciosShiftGasAfter
    (ciosBoundaryGasAfter
      (ciosOuterGasAfter C state.activeWords state.aOff + 10 +
        multiplyPassThroughExitGas ai 0 multiplyInitial)
      multiplyFinal.activeWords tEnd tk1Off tP nP + 10)
    reduction.activeWords shiftedOut tk1Off tEnd + 10

/-- Complete the deployed one-limb CIOS loop.  The post-peel reduction loop is empty, so its
guard is not taken; all multiply, boundary, shift, and finalization-entry computation remains. -/
theorem ciosOuterOneLimbThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {bP n0inv shiftedOut tk1Off aEnd tOff nBefore tP tEnd nP
      tail0 tail1 : UInt256}
    (state : CIOSOuterState)
    (hdepth : tail.length + 17 ≤ 1014)
    (houter : tP.lt tEnd ≠ ⟨0⟩)
    (hmultiplyExit :
      (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
        (ciosMultiplyInitial bP tP state)).resultPtr.lt tEnd = ⟨0⟩)
    (hreductionEmpty : tOff.lt tEnd = ⟨0⟩)
    (houterExit : (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (state.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      state.memory state.activeWords rdata acc k C) :
    let next := ciosOuterAdvanceOne bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state
    RDx runtimeBytecode ee g s0 ⟨4147⟩
      (next.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      next.memory next.activeWords rdata acc (k + 182)
      (ciosOuterOneLimbGasAfter C bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state) := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal 1 bP tP state
  let boundaryMemory := ciosAfterBoundaryMemory 1 bP tP tEnd tk1Off state
  let boundaryAw := ciosAfterBoundaryAw 1 bP tP tEnd tk1Off nP state
  let carry := ciosReductionCarry 1 bP tP tEnd tk1Off nP n0inv state
  let reduction := ciosReductionInitial 1 bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have rdBoundary := ciosOuterThroughPeeledReduction
    (n := 0) (tail := tail) (hdepth := by omega) houter
    (by simp) (by simpa only [ai, multiplyInitial, ciosMultiplyInitial] using
      hmultiplyExit) h
  have rd4401 := rdBoundary.jumpiNT (by native_decide) hreductionEmpty
    (by simp only [List.length_cons]; omega)
  have rdOuterGuard := ciosReductionToOuterBody
    (tail := tail) (hdepth := by omega) rd4401
  have rdExit := rdOuterGuard.jumpiNT (by native_decide) houterExit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices
    (k' := k + 182)
    (C' := ciosOuterOneLimbGasAfter C bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state)
    (by omega) (by
      simp [ciosOuterOneLimbGasAfter, ciosMultiplyInitial,
        ciosMultiplyFinal, ciosReductionInitial, ciosAfterBoundaryAw])
  simpa only [ciosOuterAdvanceOne, reduction, boundaryMemory, boundaryAw, carry,
    Nat.add_assoc] using normalized

end Modexp.MultiLimbMontgomeryTrace
