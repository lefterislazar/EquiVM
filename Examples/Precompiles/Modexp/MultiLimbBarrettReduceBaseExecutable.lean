import Examples.Precompiles.Modexp.MultiLimbBarrettConstantContract
import Examples.Precompiles.Modexp.MultiLimbBarrettContinuationExecutable
import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortFunction
import Examples.Precompiles.Modexp.MultiLimbSchoolbookZeroFunction
import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationFunction

/-!
# Executable Barrett base-reduction returns

This module connects the complete selected `schoolbookDiv` branches used by `reduceBase` to the
real PC 3010 continuation.  The effective dividend length and number of trimmed high zero limbs
remain exposed, so both execution and gas retain the deployed branch choice.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReduceBaseExecutable

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def shortReturnSteps (m zeroLimbs : Nat) : Nat :=
  MultiLimbSchoolbookShortFunction.totalSteps m zeroLimbs + 5

def shortReturnGas (aw : UInt256) (fp m zeroLimbs : Nat) : Nat :=
  MultiLimbSchoolbookShortFunction.totalGas aw fp m zeroLimbs + 17

/-- Execute the complete positive short-dividend branch and Barrett's PC 3010 return. -/
theorem shortDivisionReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp m zeroLimbs divisorCount : Nat} {tail : List UInt256}
    {rem dividend divisor modulus : UInt256}
    {dividendTop divisorTop : UInt256}
    (hmPos : 0 < m) (hdividendCount : m + zeroLimbs ≤ 32)
    (hdivisorTwo : 2 ≤ divisorCount) (hdivisorBound : divisorCount ≤ 32)
    (hshort : m < divisorCount)
    (hdividendHeader : MultiLimbSchoolbookTrim.dividendHeader mem aw dividend =
      UInt256.ofNat (m + zeroLimbs))
    (hdividendHeaderAw : MultiLimbSchoolbookTrim.dividendAfterHeader aw dividend = aw)
    (htrimAw : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendAfterWord aw dividend i = aw)
    (htrimZero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw dividend i = ⟨0⟩)
    (hdividendTopAw :
      MultiLimbSchoolbookTrim.dividendAfterWord aw dividend (m - 1) = aw)
    (hdividendTop :
      MultiLimbSchoolbookTrim.dividendWord mem aw dividend (m - 1) = dividendTop)
    (hdividendTopNonzero : dividendTop ≠ ⟨0⟩)
    (hdivisorHeader : MultiLimbSchoolbookDivisorTrim.divisorHeader mem aw divisor =
      UInt256.ofNat divisorCount)
    (hdivisorHeaderAw : MultiLimbSchoolbookDivisorTrim.divisorAfterHeader aw divisor = aw)
    (hdivisorTopAw : MultiLimbSchoolbookDivisorTrim.divisorAfterWord aw divisor
      (divisorCount - 1) = aw)
    (hdivisorTop : MultiLimbSchoolbookDivisorTrim.divisorWord mem aw divisor
      (divisorCount - 1) = divisorTop)
    (hdivisorTopNonzero : divisorTop ≠ ⟨0⟩)
    (hfp : 96 ≤ fp) (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdivHeader : ∀ i, i < m →
      MultiLimbSchoolbookShort.arrayHeader
          (MultiLimbSchoolbookShort.copyLoopMemory
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
            (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend rem i)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend =
            UInt256.ofNat (m + zeroLimbs))
    (hdivHeaderAw : MultiLimbSchoolbookShort.arrayAfterHeader
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (hdivElementAw : ∀ i, i < m → MultiLimbSchoolbookShort.arrayAfterWord
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend i =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (hremHeader : ∀ i, i < m →
      MultiLimbSchoolbookShort.arrayHeader
          (MultiLimbSchoolbookShort.copyLoopMemory
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
            (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend rem i)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rem =
            UInt256.ofNat divisorCount)
    (hremHeaderAw : MultiLimbSchoolbookShort.arrayAfterHeader
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rem =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (hremElementAw : ∀ i, i < m → MultiLimbSchoolbookShort.arrayAfterWord
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rem i =
        MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (htail : tail.length ≤ 1005)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (rem :: UInt256.ofNat (m + zeroLimbs) :: dividend :: ⟨3010⟩ ::
        UInt256.ofNat divisorCount :: divisor :: ⟨1707⟩ :: modulus :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (rem :: modulus :: tail)
      (MultiLimbSchoolbookShort.copyLoopMemory
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividend rem m)
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) rdata acc
      (steps + shortReturnSteps m zeroLimbs)
      (gasUsed + shortReturnGas aw fp m zeroLimbs) := by
  have rd3010 := MultiLimbSchoolbookShortFunction.exact hmPos hdividendCount
    hdivisorTwo hdivisorBound hshort hdividendHeader hdividendHeaderAw htrimAw
    htrimZero hdividendTopAw hdividendTop hdividendTopNonzero hdivisorHeader
    hdivisorHeaderAw hdivisorTopAw hdivisorTop hdivisorTopNonzero hfp hbound
    hmemSize hmemLe hgap haw3 haw64 hread hcalldata hdivHeader hdivHeaderAw
    hdivElementAw hremHeader hremHeaderAw hremElementAw
    (by simp only [List.length_cons]; omega)
    (by native_decide) h
  have rd1707 := MultiLimbBarrettConstant.divisionReturnExact
    (tail := tail) (by omega) rd3010
  exact rd1707.withIndices
    (by simp [shortReturnSteps, MultiLimbSchoolbookShortFunction.totalSteps]; omega)
    (by simp [shortReturnGas, MultiLimbSchoolbookShortFunction.totalGas]; omega)

def zeroReturnSteps (dividendCount : Nat) : Nat :=
  MultiLimbSchoolbookZeroFunction.totalSteps dividendCount + 5

def zeroReturnGas (aw : UInt256) (fp dividendCount : Nat) : Nat :=
  MultiLimbSchoolbookZeroFunction.totalGas aw fp dividendCount + 17

/-- Execute an all-zero converted dividend and Barrett's PC 3010 return. -/
theorem zeroDivisionReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp dividendCount : Nat} {tail : List UInt256}
    {rem dividend count divisor modulus : UInt256}
    (hcountBound : dividendCount ≤ 32)
    (hheader : MultiLimbSchoolbookTrim.dividendHeader mem aw dividend =
      UInt256.ofNat dividendCount)
    (hheaderAw : MultiLimbSchoolbookTrim.dividendAfterHeader aw dividend = aw)
    (helementAw : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendAfterWord aw dividend i = aw)
    (hzero : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendWord mem aw dividend i = ⟨0⟩)
    (hfp : 96 ≤ fp) (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1005)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (rem :: UInt256.ofNat dividendCount :: dividend :: ⟨3010⟩ :: count ::
        divisor :: ⟨1707⟩ :: modulus :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (rem :: modulus :: tail)
      (MultiLimbSchoolbookZero.allocatedMemory mem fp)
      (MultiLimbSchoolbookZero.allocatedWords aw fp)
      rdata acc (steps + zeroReturnSteps dividendCount)
      (gasUsed + zeroReturnGas aw fp dividendCount) := by
  have rd3010 := MultiLimbSchoolbookZeroFunction.exact hcountBound hheader hheaderAw
    helementAw hzero hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
    (by simp only [List.length_cons]; omega) (by native_decide) h
  have rd1707 := MultiLimbBarrettConstant.divisionReturnExact
    (tail := tail) (by omega) rd3010
  exact rd1707.withIndices
    (by simp [zeroReturnSteps, MultiLimbSchoolbookZeroFunction.totalSteps]; omega)
    (by simp [zeroReturnGas, MultiLimbSchoolbookZeroFunction.totalGas]; omega)

open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookNormalizationSemantic
open MultiLimbSchoolbookOuterSemantic

/-- The complete quotient-digit selector constructed from one normalized Knuth memory. -/
structure KnuthSelection
    (count uCount quotientCount : Nat)
    (u shift ret rem v quotient normalizationMarker : UInt256)
    (mem : ByteArray) (aw : UInt256) where
  vRest : List UInt256
  vSecond : UInt256
  vTop : UInt256
  inputs : List Nat
  finalMem : ByteArray
  finalAw : UInt256
  steps : Nat
  gas : Nat
  inputsLength : inputs.length = quotientCount
  topValue : vTop = arrayWord mem aw v (count - 1)
  semantic : MultiLimbSchoolbookOuterComplete.SemanticContinuations
    count uCount quotientCount u shift ret rem v quotient vTop normalizationMarker
    vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas

theorem KnuthSelection.inputs_ne_nil
    {count uCount quotientCount : Nat}
    {u shift ret rem v quotient normalizationMarker : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (selected : KnuthSelection count uCount quotientCount u shift ret rem v quotient
      normalizationMarker mem aw)
    (hquotientPos : 0 < quotientCount) : selected.inputs ≠ [] := by
  intro hempty
  have hlength := selected.inputsLength
  rw [hempty, List.length_nil] at hlength
  omega

/-- Pure modulo result of the same selector used by zero-shift execution. -/
theorem KnuthSelection.zeroResult_eq_mod
    {count uCount quotientCount dividend divisor : Nat}
    {u ret rem v quotient : UInt256} {mem : ByteArray} {aw : UInt256}
    (selected : KnuthSelection count uCount quotientCount u ⟨0⟩ ret rem v quotient
      ⟨0⟩ mem aw)
    (hquotientPos : 0 < quotientCount)
    (hnormalized : UInt256.size ≤ 2 * selected.vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount → sourceIndex < quotientIndex →
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat)
    (hdividend : Modexp.wordLimbsToNat
      (arrayReadWords mem aw u 0 (selected.inputs.length + count)) = dividend)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 count) = divisor)
    (hrange : count ≤ 32)
    (huFit : u.toNat + 32 * (count + 1) < UInt256.size)
    (hawFit : selected.finalAw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count →
      (arrayAddress rem j).toNat + 32 ≤ selected.finalMem.size)
    (hactive : ∀ j, j < count →
      (arrayAddress rem j).toNat + 32 ≤ 32 * selected.finalAw.toNat)
    (hremBelowU : ∀ i j, i < count → j < count →
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress u j).toNat)
    (hordered : ∀ i j, i < j → j < count →
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords
          (MultiLimbSchoolbookZeroShiftRemainder.copyRange selected.finalAw u rem 0 count
            selected.finalMem).memory selected.finalAw rem 0 count) =
      dividend % divisor := by
  exact MultiLimbSchoolbookCompleteSemantic.zeroShift_remainder_eq_original_mod
    selected.semantic (selected.inputs_ne_nil hquotientPos) hnormalized hquotBelowU
    hdividend hdivisor hrange huFit hawFit hwrite hactive hremBelowU hordered

/-- Pure modulo result of the same selector used by positive-shift execution. -/
theorem KnuthSelection.positiveResult_eq_mod
    {count uCount quotientCount shift dividend divisor : Nat}
    {u ret rem v quotient : UInt256} {mem : ByteArray} {aw : UInt256}
    (selected : KnuthSelection count uCount quotientCount u (UInt256.ofNat shift) ret rem v
      quotient ⟨1⟩ mem aw)
    (hquotientPos : 0 < quotientCount)
    (hnormalized : UInt256.size ≤ 2 * selected.vTop.toNat)
    (hshiftPos : 0 < shift) (hshiftBound : shift < 256)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount → sourceIndex < quotientIndex →
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat)
    (hdividend : Modexp.wordLimbsToNat
      (arrayReadWords mem aw u 0 (selected.inputs.length + count)) =
        dividend * 2 ^ shift)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 count) =
      divisor * 2 ^ shift)
    (hrange : count ≤ 32)
    (huFit : u.toNat + 32 * (count + 1) < UInt256.size)
    (hawFit : selected.finalAw.toNat * 32 < UInt256.size)
    (hwrite : ∀ j, j < count →
      (arrayAddress rem j).toNat + 32 ≤ selected.finalMem.size)
    (hactive : ∀ j, j < count →
      (arrayAddress rem j).toNat + 32 ≤ 32 * selected.finalAw.toNat)
    (hremBelowU : ∀ i j, i < count → j < count →
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress u j).toNat)
    (hordered : ∀ i j, i < j → j < count →
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords
          (MultiLimbSchoolbookDenormalization.denormalizeRange selected.finalAw u rem shift 0
            count selected.finalMem).memory selected.finalAw rem 0 count) =
      dividend % divisor := by
  exact MultiLimbSchoolbookCompleteSemantic.positiveShift_remainder_eq_original_mod
    selected.semantic (selected.inputs_ne_nil hquotientPos) hnormalized hshiftPos
    hshiftBound hquotBelowU hdividend hdivisor hrange huFit hawFit hwrite hactive
    hremBelowU hordered

/-- Construct the exposed quotient selector from concrete normalized arrays and their first-window
bound.  Every q-hat and correction branch remains represented by `selected.semantic`. -/
theorem knuthSelection_exists_of_memory
    {mem : ByteArray} {aw u shift ret rem v quotient normalizationMarker : UInt256}
    {count uCount quotientCount : Nat}
    (geometry : MultiLimbSchoolbookContinuationExecutable.ContinuationGeometry
      aw u v quotient count uCount quotientCount)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat count)
    (hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hnormalized : UInt256.size ≤ 2 * (arrayWord mem aw v (count - 1)).toNat)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (hbound :
      MultiLimbSchoolbookDivisionSemantic.windowNat
          (MultiLimbSchoolbookIterationSemantic.windowReadSlice
            mem aw u quotientCount 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat quotientCount) (UInt256.ofNat count))) <
        UInt256.size * Modexp.wordLimbsToNat
          (MultiLimbSchoolbookIterationSemantic.divisorReadSlice mem aw v 0 count)) :
    Nonempty (KnuthSelection count uCount quotientCount u shift ret rem v quotient
      normalizationMarker mem aw) := by
  obtain ⟨vRest, vSecond, vTop, inputs, finalMem, finalAw, steps, gas,
      hlength, htop, hsemantic⟩ :=
    MultiLimbBarrettContinuationExecutable.semanticContinuations_exists_of_memory
      geometry huHeader hvHeader hquotientHeader hnormalized hvMem hbound
  exact ⟨{
    vRest := vRest
    vSecond := vSecond
    vTop := vTop
    inputs := inputs
    finalMem := finalMem
    finalAw := finalAw
    steps := steps
    gas := gas
    inputsLength := hlength
    topValue := htop
    semantic := hsemantic
  }⟩

/-- Execute an exposed zero-normalization quotient selector and the complete direct remainder
copy.  Gas is the selected digit gas plus the deployed fixed return costs. -/
theorem knuthZeroReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas count uCount quotientCount retPc : Nat}
    {tail : List UInt256} {u rem v quotient : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (selected : KnuthSelection count uCount quotientCount u ⟨0⟩
      (UInt256.ofNat retPc) rem v quotient ⟨0⟩ mem aw)
    (hquotientPos : 0 < quotientCount)
    (hcountWord : count < UInt256.size)
    (hvalid : MultiLimbSchoolbookZeroShiftRemainder.ValidCopy
      selected.finalAw u rem uCount count 0 count selected.finalMem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (⟨0⟩ :: UInt256.ofNat retPc :: rem :: UInt256.ofNat quotientCount ::
        UInt256.ofNat count :: v :: quotient :: u :: arrayWord mem aw v (count - 1) ::
        ⟨0⟩ :: tail)
      mem aw rdata acc initialSteps initialGas) :
    let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange
      selected.finalAw u rem 0 count selected.finalMem
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) copied.memory selected.finalAw rdata acc
      (initialSteps + selected.steps + 5 + 58 * count + 30)
      (initialGas + selected.gas + 13 + 208 * count + 100) := by
  have hnonempty : selected.inputs ≠ [] := by
    exact selected.inputs_ne_nil hquotientPos
  have rd5457 := MultiLimbSchoolbookOuterComplete.semanticDivisionLoopExact
    selected.semantic hnonempty hcountWord hdepth (by
      simpa only [selected.inputsLength, selected.topValue] using h)
  have rdret := MultiLimbSchoolbookZeroShiftRemainder.zeroShiftRemainderExact
    hcountWord hvalid hret (by omega) rd5457
  exact rdret.withIndices (by omega) (by omega)

/-- Execute an exposed positive-normalization quotient selector and complete denormalization. -/
theorem knuthPositiveReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas count uCount quotientCount shift retPc : Nat}
    {tail : List UInt256} {u rem v quotient : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (selected : KnuthSelection count uCount quotientCount u (UInt256.ofNat shift)
      (UInt256.ofNat retPc) rem v quotient ⟨1⟩ mem aw)
    (hquotientPos : 0 < quotientCount)
    (hshift : 0 < shift) (hshiftBound : shift < 256)
    (hcountWord : count < UInt256.size)
    (hvalid : MultiLimbSchoolbookDenormalization.ValidDenormalize
      selected.finalAw u rem uCount count shift 0 count selected.finalMem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (UInt256.ofNat shift :: UInt256.ofNat retPc :: rem ::
        UInt256.ofNat quotientCount :: UInt256.ofNat count :: v :: quotient :: u ::
        arrayWord mem aw v (count - 1) :: ⟨1⟩ :: tail)
      mem aw rdata acc initialSteps initialGas) :
    let denormalized := MultiLimbSchoolbookDenormalization.denormalizeRange
      selected.finalAw u rem shift 0 count selected.finalMem
    RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
      (rem :: quotient :: tail) denormalized.memory selected.finalAw rdata acc
      (((initialSteps + selected.steps + 5) + 23) + denormalized.steps + 6)
      (((initialGas + selected.gas + 13) + 73) + denormalized.gas + 26) := by
  have hnonempty : selected.inputs ≠ [] := by
    exact selected.inputs_ne_nil hquotientPos
  have rd5457 := MultiLimbSchoolbookOuterComplete.semanticDivisionLoopExact
    selected.semantic hnonempty hcountWord hdepth (by
      simpa only [selected.inputsLength, selected.topValue] using h)
  have rd5920 := MultiLimbSchoolbookDenormalization.normalizedLoopSetupExact
    (by omega) rd5457
  have rdret := MultiLimbSchoolbookDenormalization.denormalizeAllExact
    hshift hshiftBound hvalid hret (by omega) rd5920
  exact rdret.withIndices (by omega) (by omega)

/-- Compose positive normalization from the real CLZ return with an exposed quotient selector and
the complete denormalizing return. -/
theorem positiveFromClzExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kEff m numQ ret shift : Nat} {tail : List UInt256}
    {rem quotient u divisor vTop : UInt256}
    (hshiftPos : 0 < shift) (hshiftBound : shift < 256)
    (hkEffPos : 0 < kEff) (hkEffLe : kEff ≤ 32)
    (hkEffWord : kEff < UInt256.size)
    (hmWord : m < UInt256.size) (hmSuccWord : m + 1 < UInt256.size)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kEff < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdivisorValid : MultiLimbSchoolbookNormalization.ValidDivisorShift
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) divisor
      (UInt256.ofNat fp) kEff shift 0 kEff
      (MultiLimbSchoolbookNormalization.vMemory mem fp kEff) ⟨0⟩)
    (hdividendValid : MultiLimbSchoolbookNormalization.ValidDivisorShift
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) u u (m + 1) shift 0 m
      (MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult
        (MultiLimbSchoolbookNormalization.vMemory mem fp kEff)
        (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
        divisor (UInt256.ofNat fp) kEff shift).memory ⟨0⟩)
    (huHeader : arrayHeader
      (MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
        (MultiLimbSchoolbookNormalization.vMemory mem fp kEff)
        (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift).memory
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) u = UInt256.ofNat (m + 1))
    (huHeaderAw : arrayAfterHeader
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) u =
        MultiLimbSchoolbookNormalization.vWords aw fp kEff)
    (huTopAw : arrayAfterWord (MultiLimbSchoolbookNormalization.vWords aw fp kEff) u m =
      MultiLimbSchoolbookNormalization.vWords aw fp kEff)
    (hvHeader : arrayHeader
      (MultiLimbSchoolbookNormalizationFunction.positiveMemory
        (MultiLimbSchoolbookNormalization.vMemory mem fp kEff)
        (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) (UInt256.ofNat fp) =
        UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) (UInt256.ofNat fp) =
        MultiLimbSchoolbookNormalization.vWords aw fp kEff)
    (hvTopAw : arrayAfterWord (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
      (UInt256.ofNat fp) (kEff - 1) =
        MultiLimbSchoolbookNormalization.vWords aw fp kEff)
    (hvTop : arrayWord
      (MultiLimbSchoolbookNormalizationFunction.positiveMemory
        (MultiLimbSchoolbookNormalization.vMemory mem fp kEff)
        (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff) (UInt256.ofNat fp)
      (kEff - 1) = vTop)
    (selected : KnuthSelection kEff (m + 1) numQ u (UInt256.ofNat shift)
      (UInt256.ofNat ret) rem (UInt256.ofNat fp) quotient ⟨1⟩
      (MultiLimbSchoolbookNormalizationFunction.positiveMemory
        (MultiLimbSchoolbookNormalization.vMemory mem fp kEff)
        (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift)
      (MultiLimbSchoolbookNormalization.vWords aw fp kEff))
    (hnumQPos : 0 < numQ)
    (hdenormalize : MultiLimbSchoolbookDenormalization.ValidDenormalize
      selected.finalAw u rem (m + 1) kEff shift 0 kEff selected.finalMem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat shift :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff ::
        UInt256.ofNat m :: quotient :: u :: UInt256.ofNat numQ :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    let denormalized := MultiLimbSchoolbookDenormalization.denormalizeRange
      selected.finalAw u rem shift 0 kEff selected.finalMem
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (rem :: quotient :: tail) denormalized.memory selected.finalAw rdata acc
      ((((steps + MultiLimbSchoolbookNormalizationFunction.positiveSteps
        (MultiLimbSchoolbookNormalization.vMemory mem fp kEff)
        (MultiLimbSchoolbookNormalization.vWords aw fp kEff)
        divisor (UInt256.ofNat fp) u kEff m shift) + selected.steps + 5) + 23) +
          denormalized.steps + 6)
      ((((gasUsed + MultiLimbSchoolbookNormalizationFunction.positiveGas
        mem aw divisor (UInt256.ofNat fp) u fp kEff m shift) + selected.gas + 13) + 73) +
          denormalized.gas + 26) := by
  have rd5450 := MultiLimbSchoolbookNormalizationFunction.positiveExact hshiftPos
    hshiftBound hkEffPos hkEffLe hkEffWord hmWord hmSuccWord hfp hbound hmemSize hmemLe
    hgap haw3 haw64 hread hcalldata hdivisorValid hdividendValid huHeader huHeaderAw
    huTopAw hvHeader hvHeaderAw hvTopAw hvTop htail h
  have rdret := knuthPositiveReturnExact (tail := tail) selected hnumQPos hshiftPos hshiftBound
    hkEffWord hdenormalize hret (by omega) (by
      simpa only [hvTop] using rd5450)
  exact rdret

/-- Compose zero normalization from the real CLZ return with an exposed quotient selector and the
complete direct-copy return. -/
theorem zeroFromClzExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp divisorPtr kEff m numQ ret : Nat} {tail : List UInt256}
    {rem quotient u vTop : UInt256}
    (hkEffPos : 0 < kEff) (hkEffLe : kEff ≤ 32)
    (hkEffWord : kEff < UInt256.size)
    (hkBytes : 32 * kEff < UInt256.size)
    (hdivisor32 : divisorPtr + 32 < UInt256.size) (hfp32 : fp + 32 < UInt256.size)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kEff < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvHeader : arrayHeader
      (MultiLimbSchoolbookNormalizationFunction.zeroMemory mem divisorPtr fp kEff)
      (MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff)
      (UInt256.ofNat fp) = UInt256.ofNat kEff)
    (hvHeaderAw : arrayAfterHeader
      (MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff)
      (UInt256.ofNat fp) =
        MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff)
    (hvTopAw : arrayAfterWord
      (MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff)
      (UInt256.ofNat fp) (kEff - 1) =
        MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff)
    (hvTop : arrayWord
      (MultiLimbSchoolbookNormalizationFunction.zeroMemory mem divisorPtr fp kEff)
      (MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff)
      (UInt256.ofNat fp) (kEff - 1) = vTop)
    (selected : KnuthSelection kEff (m + 1) numQ u ⟨0⟩ (UInt256.ofNat ret) rem
      (UInt256.ofNat fp) quotient ⟨0⟩
      (MultiLimbSchoolbookNormalizationFunction.zeroMemory mem divisorPtr fp kEff)
      (MultiLimbSchoolbookNormalizationFunction.zeroWords aw divisorPtr fp kEff))
    (hnumQPos : 0 < numQ)
    (hcopy : MultiLimbSchoolbookZeroShiftRemainder.ValidCopy
      selected.finalAw u rem (m + 1) kEff 0 kEff selected.finalMem)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length ≤ 996)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (⟨0⟩ :: rem :: UInt256.ofNat ret :: UInt256.ofNat kEff :: UInt256.ofNat m ::
        quotient :: u :: UInt256.ofNat numQ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange
      selected.finalAw u rem 0 kEff selected.finalMem
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat ret)
      (rem :: quotient :: tail) copied.memory selected.finalAw rdata acc
      (steps + 152 + selected.steps + 5 + 58 * kEff + 30)
      (gasUsed + MultiLimbSchoolbookNormalizationFunction.zeroGas
        aw divisorPtr fp kEff + selected.gas + 13 + 208 * kEff + 100) := by
  have rd5450 := MultiLimbSchoolbookNormalizationFunction.zeroExact hkEffPos hkEffLe
    hkEffWord hkBytes hdivisor32 hfp32 hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata hvHeader hvHeaderAw hvTopAw hvTop (by omega) h
  have rdret := knuthZeroReturnExact (tail := tail) selected hnumQPos hkEffWord
    hcopy hret htail (by simpa only [hvTop] using rd5450)
  exact rdret.withIndices (by omega) (by omega)

end Modexp.MultiLimbBarrettReduceBaseExecutable
