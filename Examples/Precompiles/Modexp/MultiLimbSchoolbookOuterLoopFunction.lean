import Examples.Precompiles.Modexp.MultiLimbSchoolbookIterationFunction

/-!
# Arbitrary schoolbook quotient loop

This module threads the concrete mutated `u` and quotient memory through every remaining quotient
digit.  The initial PC 5450 entry and later PC 5457 continuation have their distinct exact costs.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookOuterLoopFunction

open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookIterationFunction

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

structure OperandLayout
    (mem : ByteArray) (aw u uHi uLo : UInt256)
    (cursor kEff uCount : Nat) : Prop where
  hcursorPos : 0 < cursor
  hcursorWord : cursor < UInt256.size
  hkEffPos : 0 < kEff
  hsumWord : cursor - 1 + kEff < UInt256.size
  huCountWord : uCount < UInt256.size
  hhiIndex : cursor - 1 + kEff < uCount
  hloIndex : cursor - 1 + kEff - 1 < uCount
  huHeader : arrayHeader mem aw u = UInt256.ofNat uCount
  huHeaderAw : arrayAfterHeader aw u = aw
  huHiAw : arrayAfterWord aw u (cursor - 1 + kEff) = aw
  huLoAw : arrayAfterWord aw u (cursor - 1 + kEff - 1) = aw
  huHi : arrayWord mem aw u (cursor - 1 + kEff) = uHi
  huLo : arrayWord mem aw u (cursor - 1 + kEff - 1) = uLo

structure OuterResult where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

/-- Certificate for all iterations remaining after a stored digit has exposed `cursor` at
PC 5457. -/
inductive ValidContinuations
    (kEff uCount quotientCount : Nat)
    (shift ret rem v quotient u vTop normalizationMarker : UInt256) :
    Nat → ByteArray → UInt256 → OuterResult → Prop
  | done (mem : ByteArray) (aw : UInt256) :
      ValidContinuations kEff uCount quotientCount shift ret rem v quotient u vTop
        normalizationMarker 0 mem aw ⟨mem, aw, 0, 0⟩
  | step
      (cursor : Nat) (mem : ByteArray) (aw uHi uLo : UInt256)
      (iteration : IterationResult) (rest : OuterResult)
      (layout : OperandLayout mem aw u uHi uLo cursor kEff uCount)
      (hiteration : ValidIteration mem aw (cursor - 1) cursor kEff uCount quotientCount
        uHi vTop uLo u shift ret rem v quotient normalizationMarker iteration)
      (hrest : ValidContinuations kEff uCount quotientCount shift ret rem v quotient u vTop
        normalizationMarker (cursor - 1) iteration.memory iteration.activeWords rest) :
      ValidContinuations kEff uCount quotientCount shift ret rem v quotient u vTop
        normalizationMarker cursor mem aw
        ⟨rest.memory, rest.activeWords,
          109 + iteration.steps + rest.steps,
          397 + iteration.gas + rest.gas⟩

/-- Execute every continuation digit and stop at the terminal PC 5457 guard. -/
theorem continuationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C cursor kEff uCount quotientCount : Nat} {tail : List UInt256}
    {shift ret rem v quotient u vTop normalizationMarker : UInt256}
    {mem : ByteArray} {aw : UInt256} {result : OuterResult}
    (hkEffWord : kEff < UInt256.size)
    (hvalid : ValidContinuations kEff uCount quotientCount shift ret rem v quotient u vTop
      normalizationMarker cursor mem aw result)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat cursor).isZero :: UInt256.ofNat cursor :: shift :: ret ::
        rem :: UInt256.ofNat cursor :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: shift :: ret :: rem :: ⟨0⟩ ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + result.steps) (C + result.gas) := by
  induction hvalid generalizing k C with
  | done currentMem currentAw =>
      simpa only [OuterResult.memory, OuterResult.activeWords, OuterResult.steps,
        OuterResult.gas, Nat.add_zero] using h
  | step current currentMem currentAw uHi uLo iteration rest layout hiteration hrest ih =>
      have rd5516 := outerOperandsContinueExact layout.hcursorPos layout.hcursorWord
        layout.hkEffPos layout.hsumWord layout.huCountWord layout.hhiIndex layout.hloIndex
        layout.huHeader layout.huHeaderAw layout.huHiAw layout.huLoAw layout.huHi layout.huLo
        (by omega) h
      have rd5457 := iterationExact hkEffWord hiteration hdepth rd5516
      have rdEnd := ih (k := k + 109 + iteration.steps)
        (C := C + 397 + iteration.gas) rd5457
      have normalized := rdEnd.withIndices
        (k' := k + (109 + iteration.steps + rest.steps))
        (C' := C + (397 + iteration.gas + rest.gas)) (by omega) (by omega)
      simpa only [OuterResult.memory, OuterResult.activeWords, OuterResult.steps,
        OuterResult.gas] using normalized

/-- Execute the first quotient digit through PC 5450 and all certified continuations. -/
theorem divisionLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C numQ kEff uCount quotientCount : Nat} {tail : List UInt256}
    {shift ret rem v quotient u vTop normalizationMarker uHi uLo : UInt256}
    {mem : ByteArray} {aw : UInt256}
    {first : IterationResult} {rest : OuterResult}
    (hkEffWord : kEff < UInt256.size)
    (layout : OperandLayout mem aw u uHi uLo numQ kEff uCount)
    (hfirst : ValidIteration mem aw (numQ - 1) numQ kEff uCount quotientCount
      uHi vTop uLo u shift ret rem v quotient normalizationMarker first)
    (hrest : ValidContinuations kEff uCount quotientCount shift ret rem v quotient u vTop
      normalizationMarker (numQ - 1) first.memory first.activeWords rest)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (shift :: ret :: rem :: UInt256.ofNat numQ :: UInt256.ofNat kEff :: v :: quotient ::
        u :: vTop :: normalizationMarker :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: shift :: ret :: rem :: ⟨0⟩ ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      rest.memory rest.activeWords rdata acc
      (k + 114 + first.steps + rest.steps)
      (C + 410 + first.gas + rest.gas) := by
  have rd5516 := outerOperandsExact layout.hcursorPos layout.hcursorWord layout.hkEffPos
    layout.hsumWord layout.huCountWord layout.hhiIndex layout.hloIndex layout.huHeader
    layout.huHeaderAw layout.huHiAw layout.huLoAw layout.huHi layout.huLo (by omega) h
  have rd5457 := iterationExact hkEffWord hfirst hdepth rd5516
  have rdEnd := continuationsExact hkEffWord hrest hdepth rd5457
  exact rdEnd.withIndices (by omega) (by omega)

end Modexp.MultiLimbSchoolbookOuterLoopFunction
