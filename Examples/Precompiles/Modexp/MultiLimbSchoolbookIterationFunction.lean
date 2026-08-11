import Examples.Precompiles.Modexp.MultiLimbSchoolbookEstimateSelector
import Examples.Precompiles.Modexp.MultiLimbSchoolbookDigitFunction

/-!
# Complete schoolbook quotient iteration

The certificates in this module compose one closed q-hat estimate route with the concrete
multiply-subtract/direct-or-corrected quotient write.  The resulting memory is the input to the
next outer iteration.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookIterationFunction

open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookEstimateSelector
open MultiLimbSchoolbookDigitFunction

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

structure DigitResult where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

inductive ValidDigit
    (mem : ByteArray) (aw : UInt256) (kEff jj quotientCount : Nat)
    (v u current qHat shift ret rem quotient vTop normalizationMarker : UInt256) :
    DigitResult → Prop
  | direct
      (hnonnegative :
        (topResult mem aw v u current qHat kEff).negative = ⟨0⟩)
      (hjj : jj < quotientCount)
      (hjjWord : jj < UInt256.size)
      (hquotientCountWord : quotientCount < UInt256.size)
      (hquotHeader : arrayHeader (topResult mem aw v u current qHat kEff).memory
        (topResult mem aw v u current qHat kEff).activeWords quotient =
          UInt256.ofNat quotientCount)
      (hquotHeaderAw : arrayAfterHeader
        (topResult mem aw v u current qHat kEff).activeWords quotient =
          (topResult mem aw v u current qHat kEff).activeWords)
      (hquotElementAw : arrayAfterWord
        (topResult mem aw v u current qHat kEff).activeWords quotient jj =
          (topResult mem aw v u current qHat kEff).activeWords) :
      ValidDigit mem aw kEff jj quotientCount v u current qHat shift ret rem quotient vTop
        normalizationMarker
        ⟨directMemory mem aw v u current qHat quotient kEff jj,
          (topResult mem aw v u current qHat kEff).activeWords,
          78 * kEff + 67, directGas mem aw v u current qHat kEff⟩
  | corrected
      (hnegative :
        (topResult mem aw v u current qHat kEff).negative ≠ ⟨0⟩)
      (hqHat : qHat ≠ ⟨0⟩)
      (hjj : jj < quotientCount)
      (hjjWord : jj < UInt256.size)
      (hquotientCountWord : quotientCount < UInt256.size)
      (hquotHeader : arrayHeader (correctionTop mem aw v u current qHat kEff).memory
        (correctionTop mem aw v u current qHat kEff).activeWords quotient =
          UInt256.ofNat quotientCount)
      (hquotHeaderAw : arrayAfterHeader
        (correctionTop mem aw v u current qHat kEff).activeWords quotient =
          (correctionTop mem aw v u current qHat kEff).activeWords)
      (hquotElementAw : arrayAfterWord
        (correctionTop mem aw v u current qHat kEff).activeWords quotient jj =
          (correctionTop mem aw v u current qHat kEff).activeWords) :
      ValidDigit mem aw kEff jj quotientCount v u current qHat shift ret rem quotient vTop
        normalizationMarker
        ⟨correctedMemory mem aw v u current qHat quotient kEff jj,
          (correctionTop mem aw v u current qHat kEff).activeWords,
          134 * kEff + 109, correctedGas mem aw v u current qHat kEff⟩

/-- Execute either concrete accepted-digit outcome. -/
theorem digitExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff jj quotientCount : Nat} {tail : List UInt256}
    {v u current qHat shift ret rem quotient vTop normalizationMarker : UInt256}
    {result : DigitResult}
    (hkEffWord : kEff < UInt256.size)
    (hvalid : ValidDigit mem aw kEff jj quotientCount v u current qHat shift ret rem
      quotient vTop normalizationMarker result)
    (hdepth : tail.length ≤ 1001)
    (h : RDx runtimeBytecode ee g s0 ⟨5563⟩
      (⟨5715⟩ :: (⟨0⟩ : UInt256).lt (UInt256.ofNat kEff) :: v :: ⟨0⟩ ::
        u :: ⟨0⟩ :: ⟨0⟩ :: current :: qHat :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat jj).isZero :: UInt256.ofNat jj :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + result.steps) (C + result.gas) := by
  cases hvalid with
  | direct hnonnegative hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      have rd5457 := directExact hkEffWord hnonnegative hjj hjjWord
        hquotientCountWord hquotHeader hquotHeaderAw hquotElementAw hdepth h
      simpa only [DigitResult.memory, DigitResult.activeWords, DigitResult.steps,
        DigitResult.gas] using rd5457
  | corrected hnegative hqHat hjj hjjWord hquotientCountWord hquotHeader hquotHeaderAw
      hquotElementAw =>
      have rd5457 := correctedExact hkEffWord hnegative hqHat hjj hjjWord
        hquotientCountWord hquotHeader hquotHeaderAw hquotElementAw hdepth h
      simpa only [DigitResult.memory, DigitResult.activeWords, DigitResult.steps,
        DigitResult.gas] using rd5457

structure IterationResult where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

inductive ValidIteration
    (mem : ByteArray) (aw : UInt256)
    (jj cursor kEff uCount quotientCount : Nat)
    (uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256) :
    IterationResult → Prop
  | intro
      (estimate : EstimateResult)
      (digit : DigitResult)
      (hestimate : ValidEstimate mem aw jj cursor kEff uCount vTop uLo u shift ret rem v
        quotient normalizationMarker uHi estimate)
      (hdigit : ValidDigit mem aw kEff jj quotientCount v u (UInt256.ofNat cursor)
        estimate.qHat shift ret rem quotient vTop normalizationMarker digit) :
      ValidIteration mem aw jj cursor kEff uCount quotientCount uHi vTop uLo u shift ret rem v
        quotient normalizationMarker
        ⟨digit.memory, digit.activeWords, estimate.steps + digit.steps,
          estimate.gas + digit.gas⟩

/-- Execute a complete certified estimate and accepted quotient digit. -/
theorem iterationExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C jj cursor kEff uCount quotientCount : Nat} {tail : List UInt256}
    {uHi vTop uLo u shift ret rem v quotient normalizationMarker : UInt256}
    {result : IterationResult}
    (hkEffWord : kEff < UInt256.size)
    (hvalid : ValidIteration mem aw jj cursor kEff uCount quotientCount uHi vTop uLo u
      shift ret rem v quotient normalizationMarker result)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5516⟩
      (⟨5869⟩ :: uHi.lt vTop :: uHi :: UInt256.ofNat jj :: vTop ::
        UInt256.ofNat cursor :: uLo :: u :: shift :: ret :: rem :: UInt256.ofNat jj ::
        UInt256.ofNat kEff :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5457⟩
      (⟨5894⟩ :: (UInt256.ofNat jj).isZero :: UInt256.ofNat jj :: shift :: ret :: rem ::
        UInt256.ofNat jj :: UInt256.ofNat kEff :: v :: quotient :: u :: vTop ::
        normalizationMarker :: tail)
      result.memory result.activeWords rdata acc (k + result.steps) (C + result.gas) := by
  cases hvalid with
  | intro estimate digit hestimate hdigit =>
      have rd5563 := estimateExact hestimate hdepth h
      have rd5457 := digitExact hkEffWord hdigit (by omega) rd5563
      have normalized := rd5457.withIndices
        (k' := k + (estimate.steps + digit.steps))
        (C' := C + (estimate.gas + digit.gas)) (by omega) (by omega)
      simpa only [IterationResult.memory, IterationResult.activeWords,
        IterationResult.steps, IterationResult.gas] using normalized

end Modexp.MultiLimbSchoolbookIterationFunction
