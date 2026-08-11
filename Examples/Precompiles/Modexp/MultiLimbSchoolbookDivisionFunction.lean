import Examples.Precompiles.Modexp.MultiLimbSchoolbookOuterLoopFunction
import Examples.Precompiles.Modexp.MultiLimbSchoolbookZeroShiftRemainderContract

/-!
# Complete normalized schoolbook division

These theorems compose the arbitrary quotient loop with the deployed positive-shift
denormalization loop or zero-shift direct-copy loop through the internal return.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookDivisionFunction

open MultiLimbSchoolbookDenormalization
open MultiLimbSchoolbookIterationFunction
open MultiLimbSchoolbookOuterLoopFunction
open MultiLimbSchoolbookZeroShiftRemainder

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Complete normalized division when the divisor and dividend were shifted left. -/
theorem positiveShiftExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C numQ kEff uCount quotientCount shift retPc : Nat} {tail : List UInt256}
    {rem v quotient u vTop uHi uLo : UInt256}
    {mem : ByteArray} {aw : UInt256}
    {first : IterationResult} {rest : OuterResult}
    (hkEffWord : kEff < UInt256.size)
    (hshift : 0 < shift)
    (hshiftBound : shift < 256)
    (layout : OperandLayout mem aw u uHi uLo numQ kEff uCount)
    (hfirst : ValidIteration mem aw (numQ - 1) numQ kEff uCount quotientCount
      uHi vTop uLo u (UInt256.ofNat shift) (UInt256.ofNat retPc) rem v quotient ⟨1⟩ first)
    (hrest : ValidContinuations kEff uCount quotientCount (UInt256.ofNat shift)
      (UInt256.ofNat retPc) rem v quotient u vTop ⟨1⟩
      (numQ - 1) first.memory first.activeWords rest)
    (hdenormalize :
      ValidDenormalize rest.activeWords u rem uCount kEff shift 0 kEff rest.memory)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (UInt256.ofNat shift :: UInt256.ofNat retPc :: rem :: UInt256.ofNat numQ ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: ⟨1⟩ :: tail)
      mem aw rdata acc k C) :
    let denormalized := denormalizeRange rest.activeWords u rem shift 0 kEff rest.memory
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) denormalized.memory rest.activeWords rdata acc
      (k + 143 + first.steps + rest.steps + denormalized.steps)
      (C + 509 + first.gas + rest.gas + denormalized.gas) := by
  have rd5457 := divisionLoopExact hkEffWord layout hfirst hrest hdepth h
  have rd5920 := normalizedLoopSetupExact (by omega) rd5457
  have rdReturn := denormalizeAllExact hshift hshiftBound hdenormalize hret
    (by omega) rd5920
  exact rdReturn.withIndices (by omega) (by omega)

/-- Complete normalized division when normalization shift is zero. -/
theorem zeroShiftExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C numQ kEff uCount quotientCount retPc : Nat} {tail : List UInt256}
    {rem v quotient u vTop uHi uLo : UInt256}
    {mem : ByteArray} {aw : UInt256}
    {first : IterationResult} {rest : OuterResult}
    (hkEffWord : kEff < UInt256.size)
    (layout : OperandLayout mem aw u uHi uLo numQ kEff uCount)
    (hfirst : ValidIteration mem aw (numQ - 1) numQ kEff uCount quotientCount
      uHi vTop uLo u ⟨0⟩ (UInt256.ofNat retPc) rem v quotient ⟨0⟩ first)
    (hrest : ValidContinuations kEff uCount quotientCount ⟨0⟩
      (UInt256.ofNat retPc) rem v quotient u vTop ⟨0⟩
      (numQ - 1) first.memory first.activeWords rest)
    (hcopy : ValidCopy rest.activeWords u rem uCount kEff 0 kEff rest.memory)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (⟨0⟩ :: UInt256.ofNat retPc :: rem :: UInt256.ofNat numQ ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: ⟨0⟩ :: tail)
      mem aw rdata acc k C) :
    let copied := copyRange rest.activeWords u rem 0 kEff rest.memory
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) copied.memory rest.activeWords rdata acc
      (k + 144 + first.steps + rest.steps + 58 * kEff)
      (C + 510 + first.gas + rest.gas + 208 * kEff) := by
  have rd5457 := divisionLoopExact hkEffWord layout hfirst hrest hdepth h
  have rdReturn := zeroShiftRemainderExact hkEffWord hcopy hret (by omega) rd5457
  exact rdReturn.withIndices (by omega) (by omega)

end Modexp.MultiLimbSchoolbookDivisionFunction
