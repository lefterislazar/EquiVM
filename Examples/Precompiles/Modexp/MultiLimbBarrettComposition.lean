import Examples.Precompiles.Modexp.MultiLimbBarrettConstantComplete
import Examples.Precompiles.Modexp.MultiLimbBarrettExponentContract
import Examples.Precompiles.Modexp.MultiLimbBarrettReduceBaseComplete
import Examples.Precompiles.Modexp.MultiLimbBarrettResultSemantic

/-!
# Complete multi-limb Barrett composition

This module connects the exact Barrett-constant selector to the accumulator and exponent caller.
The first bridge consumes the allocator geometry proved by the constant selector and executes the
real accumulator allocation and initialization through PC 3154.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettComposition

open Modexp.MultiLimbBarrettConstant
open Modexp.MultiLimbBarrettConstantSemantic
open Modexp.MultiLimbBarrettConstantComplete
open Modexp.MultiLimbBarrettAccumulator

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The allocator pointer returned by the complete Barrett-constant computation. -/
def accumulatorFp (fp k : Nat) : Nat :=
  normalizedDivisorPtr fp k + wordArrayAllocationSize k

/-- The fixed backend reserve used by the multi-limb caller covers the accumulator and every
temporary array materialized by one reused-scratch Barrett multiplication. -/
theorem scratchEnd_afterAccumulator_le_reserve (fp k : Nat) (hk : k ≤ 32) :
    Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp fp k + wordArrayAllocationSize k) k ≤ fp + 32 * 539 := by
  unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
    Modexp.MultiLimbBarrettReusedCall.callResultFp accumulatorFp normalizedDivisorPtr
    normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
    wordArrayPayloadSize
  simp only [quotientCount_eq, dividendLength]
  omega

/-- The constant selector's word frame lifts to every persistent limb range ending before the
constant workspace. -/
theorem Selection.finalMemoryWordsBelow
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fp k modulusNat initialSteps initialGas : Nat} {callerTail : List UInt256}
    (selected : Selection (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas callerTail)
    (ptr words : Nat) (hptr : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom selected.finalMemory ptr words =
      Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom sourceMemory ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      simp only [Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom]
      rw [show Modexp.MultiLimbMemoryModel.memoryWordNat selected.finalMemory ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat sourceMemory ptr by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [selected.finalReadBelow ptr hptr (by omega)]]
      congr 1
      exact ih (ptr + 32) (by omega) (by omega)

/-- Accumulator allocation preserves the same source-memory limb range transitively. -/
theorem Selection.initializedMemoryWordsBelow
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fp k modulusNat initialSteps initialGas : Nat} {callerTail : List UInt256}
    (selected : Selection (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas callerTail)
    (ptr words : Nat) (hptr : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom
        (initializedMemory selected.finalMemory (accumulatorFp fp k) k) ptr words =
      Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom sourceMemory ptr words := by
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ selected.finalMemory.size := by
    rw [selected.finalMemorySize]
    exact haccFp
  have hmemLe : selected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [selected.finalMemorySize]
    rfl
  have hgap : accumulatorFp fp k - selected.finalMemory.size < USize.size := by
    rw [selected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have hfpAcc : fp ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  rw [initializedMemory_words_below selected.finalMemory (accumulatorFp fp k) k ptr words
    hmemSize hmemLe hgap hptr (by omega)]
  exact Modexp.MultiLimbBarrettComposition.Selection.finalMemoryWordsBelow
    selected ptr words hptr hbelow

/-- A completed constant selector plus the preserved source base/modulus arrays establishes the
full persistent invariant required by the first scratch-materializing Barrett square. -/
theorem Selection.initializedInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat baseValue : Nat} {tail : List UInt256}
    {a n exponent returnPc : UInt256}
    (selected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: n :: a :: UInt256.ofNat k :: returnPc :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp fp k + wordArrayAllocationSize k) k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (haBase : 96 ≤ a.toNat) (hnBase : 96 ≤ n.toNat)
    (haEnd : a.toNat + 32 * (k + 1) ≤ fp)
    (hnEnd : n.toNat + 32 * (k + 2) ≤ fp)
    (haHeader : sourceMemory.readWithPadding a.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hnHeader : sourceMemory.readWithPadding n.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hbaseValue : Modexp.wordLimbsToNat
      (Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom sourceMemory
        (a.toNat + 32) k) = baseValue)
    (hnValue : Modexp.wordLimbsToNat
      (Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom sourceMemory
        (n.toNat + 32) k) = modulusNat)
    (hnPos : 0 < modulusNat)
    (hnNormalized : UInt256.size ^ (k - 1) ≤ modulusNat)
    (hnFits : modulusNat < UInt256.size ^ k) :
    Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory selected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords selected.finalWords (accumulatorFp fp k) k) k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) a n
      (UInt256.ofNat (quotientPtr fp k)) 1 baseValue modulusNat := by
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ selected.finalMemory.size := by
    rw [selected.finalMemorySize]
    exact haccFp
  have hmemLe : selected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [selected.finalMemorySize]
    rfl
  have hgap : accumulatorFp fp k - selected.finalMemory.size < USize.size := by
    rw [selected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have hfpAcc : fp ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqFit : quotientPtr fp k < UInt256.size := by
    have haccBound : accumulatorFp fp k < 2 ^ 64 := by
      unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
        Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
      omega
    have hqBelow : quotientPtr fp k < accumulatorFp fp k := by
      unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact lt_trans hqBelow (lt_trans haccBound (by norm_num [UInt256.size]))
  have hqNat : (UInt256.ofNat (quotientPtr fp k)).toNat = quotientPtr fp k :=
    UInt256.toNat_ofNat_of_lt hqFit
  apply Modexp.MultiLimbBarrettExponentContract.initializedInvariant hkTwo hk haccFp
    hscratch hcalldata hmemSize hmemLe hgap selected.finalWordsFit haBase hnBase
  · rw [hqNat]
    unfold quotientPtr remainderPtr
    omega
  · omega
  · omega
  · rw [hqNat]
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact (selected.finalReadBelow a.toNat haBase (by omega)).trans haHeader
  · exact (selected.finalReadBelow n.toNat hnBase (by omega)).trans hnHeader
  · simpa only [hqNat, quotientCount_eq] using selected.quotientHeader
  · rw [Modexp.MultiLimbBarrettComposition.Selection.finalMemoryWordsBelow selected
      (a.toNat + 32) k (by omega) (by omega)]
    exact hbaseValue
  · rw [Modexp.MultiLimbBarrettComposition.Selection.finalMemoryWordsBelow selected
      (n.toNat + 32) k (by omega) (by omega)]
    exact hnValue
  · rw [hqNat]
    simpa only [quotientCount_eq] using
      MultiLimbBarrettConstantComplete.Selection.quotientMemoryValue selected
  · exact hnPos
  · exact hnNormalized
  · exact hnFits

/-- The concrete base-reduction result and concrete Barrett-constant computation jointly establish
the first exponent-loop invariant. No reduced base or Barrett constant is supplied as an
independent arithmetic premise. -/
theorem reducedInitializedInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata reduceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {reduceAw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount k reduceFp constantFp : Nat}
    {baseInput modulusNat initialSteps initialGas : Nat} {tail : List UInt256}
    {exponent returnPc : UInt256}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hreduceWorkspace : reduceFp +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64)
    (reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (constant : Modexp.MultiLimbBarrettConstantComplete.Selection
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) reduced.finalMemory constantFp k modulusNat
      initialSteps initialGas
      (exponent :: UInt256.ofNat divisorPtr :: UInt256.ofNat remPtr :: UInt256.ofNat k ::
        returnPc :: tail))
    (hconstantAfterArrays : remPtr + 32 * (k + 1) ≤ constantFp)
    (hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp constantFp k + wordArrayAllocationSize k) k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseInput : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat dividendPtr) 0 dividendCount) = baseInput)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat) :
    Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) 1
      (baseInput % modulusNat) modulusNat := by
  have hconstantBound : constantFp < 2 ^ 64 := by
    have haccBound : accumulatorFp constantFp k < 2 ^ 64 := by
      unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
        Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
      omega
    exact lt_of_le_of_lt (by
      unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr
        remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega) haccBound
  have hremFit : remPtr < UInt256.size := lt_trans (by
    omega : remPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hdivisorFit : divisorPtr < UInt256.size := lt_trans (by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hremNat := UInt256.toNat_ofNat_of_lt hremFit
  have hdivisorNat := UInt256.toNat_ofNat_of_lt hdivisorFit
  have hbaseReduced :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.resultMemoryValue_eq_entry_mod
      facts hreduceWorkspace reduced
  rw [hbaseInput, hmodulus] at hbaseReduced
  have hmodulusFinal :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalDivisorMemoryValue
      facts hreduceWorkspace reduced
  rw [hmodulus] at hmodulusFinal
  have hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat :=
    Modexp.MultiLimbBarrettConstantComplete.modulusLower_of_top_nonzero reduceMemory
      reduceAw (UInt256.ofNat divisorPtr)
      (Modexp.MultiLimbSchoolbookNormalization.arrayWord reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) (k - 1)) k modulusNat (by
          have := facts.divisorTwo
          omega) rfl facts.divisorTopNonzero hmodulus
  have hmodulusFits : modulusNat < UInt256.size ^ k := by
    rw [← hmodulus]
    have hlt := Modexp.wordLimbsToNat_lt_pow
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k)
    rw [Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length] at hlt
    exact hlt
  apply Modexp.MultiLimbBarrettComposition.Selection.initializedInvariant constant
    facts.divisorTwo facts.divisorBound hscratch hcalldata
  · rw [hremNat]
    have := facts.divisorPtr96
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    omega
  · rw [hdivisorNat]
    exact facts.divisorPtr96
  · rw [hremNat]
    exact hconstantAfterArrays
  · rw [hdivisorNat]
    exact le_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega : divisorPtr + 32 * (k + 2) ≤ remPtr + 32 * (k + 1))
      hconstantAfterArrays
  · rw [hremNat]
    exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalRemainderHeader
      facts hreduceWorkspace reduced
  · rw [hdivisorNat]
    exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalDivisorHeader
      facts hreduceWorkspace reduced
  · rw [hremNat]
    exact hbaseReduced
  · rw [hdivisorNat]
    exact hmodulusFinal
  · exact lt_of_lt_of_le (by norm_num [UInt256.size]) hmodulusLower
  · exact hmodulusLower
  · exact hmodulusFits

/-- The exposed fresh selector computes the trusted pure modular power from the original base.
The reduced base and Barrett constant are both obtained from their concrete preceding selectors. -/
theorem reducedFreshAccumulator_eq_modelPow
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata reduceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {reduceAw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount k reduceFp constantFp : Nat}
    {baseInput modulusNat initialSteps initialGas : Nat} {tail : List UInt256}
    {exponent returnPc : UInt256}
    {baseSize exponentSize byteFuel bitFuel callFuel : Nat}
    {selected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hreduceWorkspace : reduceFp +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64)
    (reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (constant : Modexp.MultiLimbBarrettConstantComplete.Selection
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) reduced.finalMemory constantFp k modulusNat
      initialSteps initialGas
      (exponent :: UInt256.ofNat divisorPtr :: UInt256.ofNat remPtr :: UInt256.ofNat k ::
        returnPc :: tail))
    (hconstantAfterArrays : remPtr + 32 * (k + 1) ≤ constantFp)
    (hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp constantFp k + wordArrayAllocationSize k) k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseInput : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat dividendPtr) 0 dividendCount) = baseInput)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) selected)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) selected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt
        (Modexp.MultiLimbExponentTrace.exponentArrayLength
          (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
          (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent) ≠ ⟨0⟩ →
      (idx.lt (Modexp.MultiLimbExponentTrace.exponentArrayLength mem' aw' exponent)).isZero =
          ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent idx).toNat + 32 + 31 <
        UInt256.size) :
    Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
        (UInt256.ofNat (accumulatorFp constantFp k)) selected.memory =
      baseInput ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
        modulusNat := by
  have invariant := reducedInitializedInvariant facts hreduceWorkspace reduced constant
    hconstantAfterArrays hscratch hcalldata hbaseInput hmodulus
  have hmodTwo : 1 < modulusNat := by
    have hkTwo := facts.divisorTwo
    have hlower := invariant.nNormalized
    have hbase : 1 < UInt256.size ^ (k - 1) := by
      exact one_lt_pow₀ (by norm_num [UInt256.size]) (by omega)
    omega
  have hinitial : 1 = (baseInput % modulusNat) ^ 0 % modulusNat := by
    simp [Nat.mod_eq_of_lt hmodTwo]
  have hvalue :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.value_eq_full_model_powInvariant
      valid invariant alignment hexponentFit haccess hinitial
  rw [hvalue]
  exact (Nat.mod_modEq baseInput modulusNat).pow
    (Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize)

/-- Framed form of `reducedFreshAccumulator_eq_modelPow`. -/
theorem reducedFreshAccumulator_eq_modelPowFramed
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata reduceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {reduceAw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount k reduceFp constantFp : Nat}
    {baseInput modulusNat initialSteps initialGas : Nat} {tail : List UInt256}
    {exponent returnPc : UInt256}
    {baseSize exponentSize byteFuel bitFuel callFuel : Nat}
    {selected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hreduceWorkspace : reduceFp +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64)
    (reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (constant : Modexp.MultiLimbBarrettConstantComplete.Selection
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) reduced.finalMemory constantFp k modulusNat
      initialSteps initialGas
      (exponent :: UInt256.ofNat divisorPtr :: UInt256.ofNat remPtr :: UInt256.ofNat k ::
        returnPc :: tail))
    (hconstantAfterArrays : remPtr + 32 * (k + 1) ≤ constantFp)
    (hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp constantFp k + wordArrayAllocationSize k) k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseInput : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat dividendPtr) 0 dividendCount) = baseInput)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) selected)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) selected)
    (access : Modexp.MultiLimbBarrettExponentLoop.BarrettExponentAccessFrame
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (UInt256.ofNat (accumulatorFp constantFp k))) :
    Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
        (UInt256.ofNat (accumulatorFp constantFp k)) selected.memory =
      baseInput ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
        modulusNat := by
  have invariant := reducedInitializedInvariant facts hreduceWorkspace reduced constant
    hconstantAfterArrays hscratch hcalldata hbaseInput hmodulus
  have hmodTwo : 1 < modulusNat := by
    have hkTwo := facts.divisorTwo
    have hlower := invariant.nNormalized
    have hbase : 1 < UInt256.size ^ (k - 1) := by
      exact one_lt_pow₀ (by norm_num [UInt256.size]) (by omega)
    omega
  have hinitial : 1 = (baseInput % modulusNat) ^ 0 % modulusNat := by
    simp [Nat.mod_eq_of_lt hmodTwo]
  have hvalue :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.value_eq_full_model_powInvariantFramed
      valid invariant alignment access hinitial
  rw [hvalue]
  exact (Nat.mod_modEq baseInput modulusNat).pow
    (Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize)

/-- Construct the complete Barrett-constant selector directly from a selected base-reduction
return. All guarded divisor observations are rebuilt from the reduction's concrete final memory. -/
theorem reducedConstantSelection_exists
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata reduceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {reduceAw : UInt256}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount k reduceFp modulusNat : Nat}
    {tail : List UInt256} {exponent : UInt256}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hreduceWorkspace : reduceFp +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64)
    (reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hfirstBound : reduced.finalFreePtr + wordArrayAllocationSize
      (dividendLength k) < 2 ^ 64)
    (hsecondBound : remainderPtr reduced.finalFreePtr k + wordArrayAllocationSize k <
      2 ^ 64)
    (hquotientBound : quotientPtr reduced.finalFreePtr k +
      wordArrayAllocationSize (quotientCount k) < 2 ^ 64)
    (huBound : normalizedDividendPtr reduced.finalFreePtr k +
      wordArrayAllocationSize (dividendLength k + 1) < 2 ^ 64)
    (hvBound : normalizedDivisorPtr reduced.finalFreePtr k +
      wordArrayAllocationSize k < 2 ^ 64)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 990)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat divisorPtr :: exponent :: UInt256.ofNat k :: tail)
      reduced.finalMemory reduced.finalWords rdata acc steps gasUsed) :
    Nonempty (Modexp.MultiLimbBarrettConstantComplete.Selection
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) reduced.finalMemory reduced.finalFreePtr k modulusNat
      (steps + Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
        reduced.finalMemory reduced.finalWords reduced.finalFreePtr k divisorPtr)
      (gasUsed + Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
        reduced.finalMemory reduced.finalWords reduced.finalFreePtr k divisorPtr)
      (exponent :: UInt256.ofNat divisorPtr :: UInt256.ofNat remPtr :: UInt256.ofNat k ::
        tail)) := by
  have hallocator :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalAllocatorGeometry
      facts hreduceWorkspace reduced
  have hcoverage :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalCoverageAndFit
      facts hreduceWorkspace reduced
  have hfp96 : 96 ≤ reduced.finalFreePtr := le_trans hallocator.1 hallocator.2.1
  have hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ reduced.finalFreePtr := by
    exact le_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      omega : divisorPtr + 32 * (k + 1) ≤ reduceFp)
      (Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr reduced)
  have hfirstFit : reduced.finalFreePtr + wordArrayAllocationSize (dividendLength k) + 31 <
      UInt256.size := lt_trans (by omega : reduced.finalFreePtr +
        wordArrayAllocationSize (dividendLength k) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hsecondFit : remainderPtr reduced.finalFreePtr k + wordArrayAllocationSize k + 31 <
      UInt256.size := lt_trans (by omega : remainderPtr reduced.finalFreePtr k +
        wordArrayAllocationSize k + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hdivisionRange := Modexp.MultiLimbBarrettConstantSemantic.barrettDivisionWords_range
    reduced.finalWords reduced.finalFreePtr k (by
      have := facts.divisorTwo
      omega) hcoverage.2 hfirstFit hsecondFit
  have hdivisionSize := Modexp.MultiLimbBarrettConstantSemantic.barrettDivisionMemory_size
    reduced.finalMemory reduced.finalFreePtr k facts.divisorBound hfp96 hallocator.1
    hallocator.2.1 hallocator.2.2.1 hfirstFit
  have hdivisionCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k)
      (barrettDivisionWords reduced.finalWords reduced.finalFreePtr k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hdivisionSize]
    exact le_trans (by omega) hdivisionRange.1
  have haw3 : 3 ≤ reduced.finalWords.toNat := by
    have hcovered := hcoverage.1
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
    omega
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ reduced.finalWords * ⟨32⟩ := by
    have hmul : (reduced.finalWords * (⟨32⟩ : UInt256)).toNat =
        reduced.finalWords.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := reduced.finalWords) (b := (⟨32⟩ : UInt256)) hcoverage.2
    intro hle
    have hnat : (reduced.finalWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    have hcovered := hcoverage.1
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
    omega
  have hdivisionHeader :
      (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k).readWithPadding
          divisorPtr 32 = UInt256.toByteArray (UInt256.ofNat k) := by
    exact (Modexp.MultiLimbBarrettConstantSemantic.barrettDivisionMemory_read_below_fp
      reduced.finalMemory reduced.finalFreePtr k divisorPtr facts.divisorBound hfp96
      hallocator.1 hallocator.2.1 hallocator.2.2.1 hfirstFit facts.divisorPtr96
      (by omega)).trans
        (Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalDivisorHeader
          facts hreduceWorkspace reduced)
  have hdivisorFit : divisorPtr + 32 * (k + 1) < UInt256.size := lt_trans (by
    exact lt_of_le_of_lt hdivisorEnd (by
      have := hfirstBound
      omega : reduced.finalFreePtr < 2 ^ 64)) (by norm_num [UInt256.size])
  have hdivisionLayout : MultiLimbArrayReadSemantic.Layout
      (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k)
      (barrettDivisionWords reduced.finalWords reduced.finalFreePtr k) divisorPtr k := by
    apply MultiLimbArrayReadSemantic.layout_of_geometry
    · exact hdivisorFit
    · rw [hdivisionSize]
      unfold remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact le_trans (by
        unfold remainderPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
        omega : divisorPtr + 32 + 32 * k ≤
          remainderPtr reduced.finalFreePtr k + 32 + 32 * k) hdivisionRange.1
    · exact hdivisionRange.2
    · exact hdivisionHeader
  have hdivisionWords :
      MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom
          (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k)
          (divisorPtr + 32) k =
        MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom reduced.finalMemory
          (divisorPtr + 32) k := by
    have hframe : ∀ words ptr, 96 ≤ ptr → ptr + 32 * words ≤ reduced.finalFreePtr →
        MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom
            (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k) ptr words =
          MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom reduced.finalMemory ptr words := by
      intro words
      induction words with
      | zero => intro ptr hptr hbelow; rfl
      | succ words ih =>
          intro ptr hptr hbelow
          simp only [MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom]
          rw [show MultiLimbMemoryModel.memoryWordNat
                (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k) ptr =
              MultiLimbMemoryModel.memoryWordNat reduced.finalMemory ptr by
            unfold MultiLimbMemoryModel.memoryWordNat
            rw [Modexp.MultiLimbBarrettConstantSemantic.barrettDivisionMemory_read_below_fp
              reduced.finalMemory reduced.finalFreePtr k ptr facts.divisorBound hfp96
              hallocator.1 hallocator.2.1 hallocator.2.2.1 hfirstFit hptr (by omega)]]
          congr 1
          exact ih (ptr + 32) (by omega) (by omega)
    exact hframe k (divisorPtr + 32) (by
      have := facts.divisorPtr96
      omega) (by
      exact le_trans (by omega : divisorPtr + 32 + 32 * k ≤
        divisorPtr + 32 * (k + 1)) hdivisorEnd)
  have hdivisionModulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k)
        (barrettDivisionWords reduced.finalWords reduced.finalFreePtr k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat := by
    calc
      _ = Modexp.wordLimbsToNat
          (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom
            (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k)
            (divisorPtr + 32) k) :=
        MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryWordsFrom _ _ _ _
          hdivisorFit hdivisionCovered hdivisionRange.2
      _ = Modexp.wordLimbsToNat
          (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom reduced.finalMemory
            (divisorPtr + 32) k) := congrArg Modexp.wordLimbsToNat hdivisionWords
      _ = Modexp.wordLimbsToNat
          (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory
            reduceAw (UInt256.ofNat divisorPtr) 0 k) :=
        Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalDivisorMemoryValue
          facts hreduceWorkspace reduced
      _ = modulusNat := hmodulus
  have hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat :=
    Modexp.MultiLimbBarrettConstantComplete.modulusLower_of_top_nonzero reduceMemory
      reduceAw (UInt256.ofNat divisorPtr)
      (Modexp.MultiLimbSchoolbookNormalization.arrayWord reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) (k - 1)) k modulusNat (by
        have := facts.divisorTwo
        omega) rfl
      facts.divisorTopNonzero hmodulus
  have hdivisionTopNonzero :=
    Modexp.MultiLimbSchoolbookTrimSelection.top_nonzero_of_value_lower
      (barrettDivisionMemory reduced.finalMemory reduced.finalFreePtr k)
      (barrettDivisionWords reduced.finalWords reduced.finalFreePtr k)
      (UInt256.ofNat divisorPtr) k (by
        have := facts.divisorTwo
        omega) (by rw [hdivisionModulus]; exact hmodulusLower)
  exact Modexp.MultiLimbBarrettConstantComplete.Selection.exists_of_call
    facts.divisorTwo facts.divisorBound hfp96 hfirstBound hsecondBound hquotientBound
    huBound hvBound hallocator.1 hallocator.2.1 hallocator.2.2.1 haw3 haw64 hcoverage.2
    hallocator.2.2.2 facts.divisorPtr96 hdivisorEnd hdivisionHeader hdivisionLayout
    hdivisionModulus hdivisionTopNonzero hcalldata hdepth h

/-- Execute the selected base reduction and construct the exact constant selector at its concrete
return state. The resulting indices are the path-sensitive sum of both computations. -/
theorem reduceAndConstantSelection_exists
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata reduceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {reduceAw : UInt256}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount k reduceFp modulusNat : Nat}
    {tail : List UInt256} {exponent : UInt256}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hreduceWorkspace : reduceFp +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64)
    (reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hfirstBound : reduced.finalFreePtr + wordArrayAllocationSize
      (dividendLength k) < 2 ^ 64)
    (hsecondBound : remainderPtr reduced.finalFreePtr k + wordArrayAllocationSize k <
      2 ^ 64)
    (hquotientBound : quotientPtr reduced.finalFreePtr k +
      wordArrayAllocationSize (quotientCount k) < 2 ^ 64)
    (huBound : normalizedDividendPtr reduced.finalFreePtr k +
      wordArrayAllocationSize (dividendLength k + 1) < 2 ^ 64)
    (hvBound : normalizedDivisorPtr reduced.finalFreePtr k +
      wordArrayAllocationSize k < 2 ^ 64)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 990)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount :: UInt256.ofNat dividendPtr ::
        ⟨3010⟩ :: UInt256.ofNat k :: UInt256.ofNat divisorPtr :: ⟨1707⟩ ::
        UInt256.ofNat divisorPtr :: exponent :: UInt256.ofNat k :: tail)
      reduceMemory reduceAw rdata acc steps gasUsed) :
    Nonempty (Modexp.MultiLimbBarrettConstantComplete.Selection
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) reduced.finalMemory reduced.finalFreePtr k modulusNat
      (steps + reduced.stepDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
          reduced.finalMemory reduced.finalWords reduced.finalFreePtr k divisorPtr)
      (gasUsed + reduced.gasDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
          reduced.finalMemory reduced.finalWords reduced.finalFreePtr k divisorPtr)
      (exponent :: UInt256.ofNat divisorPtr :: UInt256.ofNat remPtr :: UInt256.ofNat k ::
        tail)) := by
  have rd1707 := Modexp.MultiLimbBarrettReduceBaseComplete.Selection.exact facts
    hreduceWorkspace reduced hcalldata (by
      simp only [List.length_cons]
      omega) h
  simpa only [Nat.add_assoc] using reducedConstantSelection_exists facts hreduceWorkspace
    reduced hfirstBound hsecondBound hquotientBound huBound hvBound hmodulus hcalldata
    hdepth rd1707

/-- Free pointer after the direct modulus conversion. -/
def directBaseFp (modulusFp modulusSize : Nat) : Nat :=
  modulusFp + wordArrayAllocationSize
    (Modexp.MultiLimbBarrettConversion.words modulusSize)

/-- Free pointer after the selected-width base conversion. -/
def directRemFp (modulusFp modulusSize baseSize : Nat) : Nat :=
  directBaseFp modulusFp modulusSize + wordArrayAllocationSize
    (MultiLimbReduceBase.baseWords baseSize
      (Modexp.MultiLimbBarrettConversion.words modulusSize))

/-- The concrete direct modulus/base/remainder allocation chain establishes every PC 5199 entry
fact.  The branch selector therefore consumes facts derived from actual copied input bytes rather
than a separately assumed division state. -/
theorem directEntryFacts
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmodulusFp : 96 ≤ modulusFp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSource96 : 96 ≤ dataPtr + 32)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hsource256 : dataPtr + 32 < UInt256.size)
    (hsource64 : dataPtr + 32 < 2 ^ 64)
    (hsourceActive : dataPtr + 64 ≤ 32 * aw.toNat)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (dataPtr + 32))) ≠ ⟨0⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (Modexp.MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤
      directBaseFp modulusFp modulusSize)
    (hbackendWorkspace : directRemFp modulusFp modulusSize baseSize +
      wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize) +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 234 < 2 ^ 64) :
    Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw basePtr modulusFp dataPtr
        modulusSize (directBaseFp modulusFp modulusSize)
        (directRemFp modulusFp modulusSize baseSize) baseSize)
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
        modulusSize (directBaseFp modulusFp modulusSize)
        (directRemFp modulusFp modulusSize baseSize) baseSize)
      (directBaseFp modulusFp modulusSize) modulusFp
      (directRemFp modulusFp modulusSize baseSize)
      (MultiLimbReduceBase.baseWords baseSize
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (directRemFp modulusFp modulusSize baseSize +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize)) := by
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let baseFp := directBaseFp modulusFp modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  have hremFpEq : remFp = baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize k) := rfl
  have hmodGeometry := Modexp.MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hbaseBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize k) < 2 ^ 64 := by
    dsimp only [baseFp, remFp, directRemFp, k] at hbackendWorkspace ⊢
    omega
  have hkBound : k ≤ 32 := by
    dsimp only [k]
    unfold Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hbaseWordsBound : MultiLimbReduceBase.baseWords baseSize k ≤ 32 := by
    unfold MultiLimbReduceBase.baseWords MultiLimbReduceBase.naturalWords
    omega
  have hmodulusMemoryLe :
      (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
        mem aw modulusFp dataPtr modulusSize).size ≤ baseFp := by
    dsimp only [baseFp, directBaseFp, k]
    unfold Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
    rw [hmodGeometry.1]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hbaseGap : baseFp -
      (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
        mem aw modulusFp dataPtr modulusSize).size < USize.size := by
    have heq :
        (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize).size = baseFp := by
      apply Nat.le_antisymm hmodulusMemoryLe
      dsimp only [baseFp, directBaseFp, k]
      unfold Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
      rw [hmodGeometry.1]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    rw [heq, Nat.sub_self]
    native_decide
  have hbaseGeometry := Modexp.MultiLimbReduceBaseSemantic.convertedGeometry
    (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
      mem aw modulusFp dataPtr modulusSize)
    (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusWords
      mem aw modulusFp dataPtr modulusSize)
    basePtr baseFp baseSize k hbasePos hbaseSize (by
      unfold Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
      rw [hmodGeometry.1]
      omega) hmodulusMemoryLe hbaseGap hbaseSourceBefore hmodGeometry.2.2.2 hbaseBound
  have hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize)
        (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusWords
          mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize k basePtr).size ≤ remFp := by
    rw [hbaseGeometry.1]
    dsimp only [remFp, directRemFp, baseFp, k]
    unfold wordArrayAllocationSize wordArrayPayloadSize MultiLimbReduceBase.baseWords
    omega
  have hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize)
        (Modexp.MultiLimbBarrettReduceBaseSemantic.modulusWords
          mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize k basePtr).size < USize.size := by
    rw [hbaseGeometry.1, hremFpEq]
    have hnaturalLe : MultiLimbReduceBase.naturalWords baseSize ≤
        MultiLimbReduceBase.baseWords baseSize k := Nat.le_max_left _ _
    unfold wordArrayAllocationSize wordArrayPayloadSize
    have : 32 * 33 < USize.size := by native_decide
    omega
  apply Modexp.MultiLimbBarrettReduceBaseSelection.finalEntryFacts
    mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize
    hmodulusLarge hmodulusBound hmodulusFp hmemSize hmemLe hmodulusGap
    hmodulusSource96 hmodulusSourceBefore hsource256 hsource64 hsourceActive hfirst
    hawFit hmodulusAllocationBound
  · dsimp only [baseFp, directBaseFp, k]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact hmodulusMemoryLe
  · exact hbaseGap
  · exact hbasePos
  · exact hbaseSize
  · exact hbaseSourceBefore
  · exact hbaseBound
  · change baseFp + 32 + 32 * MultiLimbReduceBase.baseWords baseSize k ≤ remFp
    rw [hremFpEq]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact hbaseConvertedLe
  · exact hremGap
  · have hw : remFp + wordArrayAllocationSize k +
        Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 234 < 2 ^ 64 :=
      hbackendWorkspace
    change remFp + wordArrayAllocationSize k < 2 ^ 64
    omega
  · have hw : remFp + wordArrayAllocationSize k +
        Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 234 < 2 ^ 64 :=
      hbackendWorkspace
    change remFp + wordArrayAllocationSize k + wordArrayAllocationSize 1 < 2 ^ 64
    simp only [Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes,
      wordArrayAllocationSize, wordArrayPayloadSize] at hw ⊢
    omega

/-- Exposed selector for the direct (already normalized) multi-limb Barrett branch.  Its constant
selector indices include the exact scan, conversion, base conversion, selected division, and
Barrett-constant gas. -/
structure DirectSelection
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (mem : ByteArray) (aw : UInt256)
    (steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat)
    (exponent result retBar ret : UInt256) (tail : List UInt256) where
  scanSteps : Nat
  dataLenLarge : 32 < modulusSize
  dataLenBound : modulusSize ≤ 1024
  calldataBound : ee.calldata.size < 2 ^ 64
  backendWorkspace : directRemFp modulusFp modulusSize baseSize +
    wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize) +
    Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 < 2 ^ 64
  entryFacts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts
    (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw (UInt256.ofNat basePtr)
      modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
      (directRemFp modulusFp modulusSize baseSize) baseSize)
    (Modexp.MultiLimbBarrettReduceBaseSemantic.finalWords mem aw (UInt256.ofNat basePtr)
      modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
      (directRemFp modulusFp modulusSize baseSize) baseSize)
    (directBaseFp modulusFp modulusSize) modulusFp
    (directRemFp modulusFp modulusSize baseSize)
    (MultiLimbReduceBase.baseWords baseSize
      (Modexp.MultiLimbBarrettConversion.words modulusSize))
    (Modexp.MultiLimbBarrettConversion.words modulusSize)
    (directRemFp modulusFp modulusSize baseSize +
      wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
  baseInput_eq : Modexp.wordLimbsToNat
    (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw (UInt256.ofNat basePtr)
        modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
        (directRemFp modulusFp modulusSize baseSize) baseSize)
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalWords mem aw (UInt256.ofNat basePtr)
        modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
        (directRemFp modulusFp modulusSize baseSize) baseSize)
      (UInt256.ofNat (directBaseFp modulusFp modulusSize)) 0
      (MultiLimbReduceBase.baseWords baseSize
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) =
      Model.bytesToNatPadded mem (basePtr + 32) baseSize
  modulus_eq : Modexp.wordLimbsToNat
    (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw (UInt256.ofNat basePtr)
        modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
        (directRemFp modulusFp modulusSize baseSize) baseSize)
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalWords mem aw (UInt256.ofNat basePtr)
        modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
        (directRemFp modulusFp modulusSize baseSize) baseSize)
      (UInt256.ofNat modulusFp) 0
      (Modexp.MultiLimbBarrettConversion.words modulusSize)) =
      Model.bytesToNatPadded mem (p + 32) modulusSize
  reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection
    (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw (UInt256.ofNat basePtr)
      modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
      (directRemFp modulusFp modulusSize baseSize) baseSize)
    (Modexp.MultiLimbBarrettReduceBaseSemantic.finalWords mem aw (UInt256.ofNat basePtr)
      modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
      (directRemFp modulusFp modulusSize baseSize) baseSize)
    (directBaseFp modulusFp modulusSize) modulusFp
    (directRemFp modulusFp modulusSize baseSize)
    (MultiLimbReduceBase.baseWords baseSize
      (Modexp.MultiLimbBarrettConversion.words modulusSize))
    (Modexp.MultiLimbBarrettConversion.words modulusSize)
    (directRemFp modulusFp modulusSize baseSize +
      wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
  constant : Modexp.MultiLimbBarrettConstantComplete.Selection
    (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
    reduced.finalMemory reduced.finalFreePtr
    (Modexp.MultiLimbBarrettConversion.words modulusSize)
    (Model.bytesToNatPadded mem (p + 32) modulusSize)
    (scanSteps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize
      (Modexp.MultiLimbBarrettConversion.words modulusSize) + reduced.stepDelta +
      Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
        reduced.finalMemory reduced.finalWords reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) modulusFp)
    (gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
      modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
        (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
        (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
        (directBaseFp modulusFp modulusSize) (directRemFp modulusFp modulusSize baseSize)
        baseSize (Modexp.MultiLimbBarrettConversion.words modulusSize)
        (UInt256.ofNat basePtr) + reduced.gasDelta +
      Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
        reduced.finalMemory reduced.finalWords reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) modulusFp)
    (exponent :: UInt256.ofNat modulusFp ::
      UInt256.ofNat (directRemFp modulusFp modulusSize baseSize) ::
      UInt256.ofNat (Modexp.MultiLimbBarrettConversion.words modulusSize) :: ⟨1745⟩ ::
      result :: UInt256.ofNat modulusSize :: ⟨805⟩ :: retBar :: result :: ret :: tail)
  sourceReadBelow : ∀ read, 96 ≤ read → read + 32 ≤ modulusFp →
    (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw (UInt256.ofNat basePtr)
      modulusFp p modulusSize (directBaseFp modulusFp modulusSize)
      (directRemFp modulusFp modulusSize baseSize) baseSize).readWithPadding read 32 =
        mem.readWithPadding read 32

/-- Compose the deployed `reduceBase` call at PC 1700 with a constructive selection of every
PC 5199 reduction branch and the complete Barrett-constant computation.  Both selectors remain
exposed, and the constant selector's initial indices contain the exact selected reduction gas. -/
theorem baseToConstantSelection_exists
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata mem : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256}
    {steps gasUsed basePtr modulusPtr baseFp remFp baseSize k modulusNat dataLen : Nat}
    {tail : List UInt256} {exponent result retBar ret : UInt256}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts
      (MultiLimbReduceBase.remainderMemory mem aw baseFp remFp baseSize k
        (UInt256.ofNat basePtr))
      (MultiLimbReduceBase.remainderWords mem aw baseFp remFp baseSize k
        (UInt256.ofNat basePtr))
      baseFp modulusPtr remFp (MultiLimbReduceBase.baseWords baseSize k) k
      (remFp + wordArrayAllocationSize k))
    (hbackendWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 234 < 2 ^ 64)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (MultiLimbReduceBase.remainderMemory mem aw baseFp remFp baseSize k
          (UInt256.ofNat basePtr))
        (MultiLimbReduceBase.remainderWords mem aw baseFp remFp baseSize k
          (UInt256.ofNat basePtr))
        (UInt256.ofNat modulusPtr) 0 k) = modulusNat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize <= 1024) (hk : k <= 32)
    (hbasePtrFit : basePtr < UInt256.size)
    (hbaseAccess : basePtr + 32 <= 32 * aw.toNat)
    (hbaseLoad : wideLoadWord mem aw (UInt256.ofNat basePtr) = UInt256.ofNat baseSize)
    (hbaseFp : 96 <= baseFp)
    (hbaseBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize k) < 2 ^ 64)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (haw3 : 3 <= aw.toNat) (haw64 : ¬ (UInt256.ofNat 64 >= aw * UInt256.ofNat 32))
    (hbaseFree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat baseFp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseAccessAllocated : basePtr + 32 <=
      32 * (MultiLimbReduceBase.baseAllocatedWords aw baseFp baseSize k).toNat)
    (hbaseLoadAllocated : wideLoadWord
      (MultiLimbReduceBase.baseAllocatedMemory mem baseFp baseSize k)
      (MultiLimbReduceBase.baseAllocatedWords aw baseFp baseSize k)
      (UInt256.ofNat basePtr) = UInt256.ofNat baseSize)
    (hremFp : 96 <= remFp)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64)
    (hconvertedSize : 96 <=
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k
        (UInt256.ofNat basePtr)).size)
    (hconvertedLe :
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k
        (UInt256.ofNat basePtr)).size <= remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k
        (UInt256.ofNat basePtr)).size < USize.size)
    (hconvertedAw3 : 3 <=
      (MultiLimbReduceBase.convertedWords mem aw baseFp baseSize k
        (UInt256.ofNat basePtr)).toNat)
    (hconvertedAw64 : ¬ (UInt256.ofNat 64 >=
      MultiLimbReduceBase.convertedWords mem aw baseFp baseSize k
        (UInt256.ofNat basePtr) * UInt256.ofNat 32))
    (hremFree :
      (MultiLimbReduceBase.convertedMemory mem aw baseFp baseSize k
        (UInt256.ofNat basePtr)).readWithPadding 64 32 =
          UInt256.toByteArray (UInt256.ofNat remFp))
    (hdepth : tail.length <= 983)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 1700)
      (UInt256.ofNat modulusPtr :: UInt256.ofNat k :: UInt256.ofNat 1707 ::
        UInt256.ofNat basePtr :: exponent :: UInt256.ofNat k :: UInt256.ofNat 1745 ::
        result :: UInt256.ofNat dataLen :: UInt256.ofNat 805 :: retBar :: result :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    exists reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection
        (MultiLimbReduceBase.remainderMemory mem aw baseFp remFp baseSize k
          (UInt256.ofNat basePtr))
        (MultiLimbReduceBase.remainderWords mem aw baseFp remFp baseSize k
          (UInt256.ofNat basePtr))
        baseFp modulusPtr remFp (MultiLimbReduceBase.baseWords baseSize k) k
        (remFp + wordArrayAllocationSize k),
      Nonempty (Modexp.MultiLimbBarrettConstantComplete.Selection
        (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
        (rdata := rdata) (acc := acc) reduced.finalMemory reduced.finalFreePtr k modulusNat
        (steps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize k + reduced.stepDelta +
          Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
            reduced.finalMemory reduced.finalWords reduced.finalFreePtr k modulusPtr)
        (gasUsed + 18 + MultiLimbReduceBase.nonzeroGas mem aw baseFp remFp baseSize k
            (UInt256.ofNat basePtr) + reduced.gasDelta +
          Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
            reduced.finalMemory reduced.finalWords reduced.finalFreePtr k modulusPtr)
        (exponent :: UInt256.ofNat modulusPtr :: UInt256.ofNat remFp :: UInt256.ofNat k ::
          UInt256.ofNat 1745 :: result :: UInt256.ofNat dataLen :: UInt256.ofNat 805 ::
          retBar :: result :: ret :: tail)) := by
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by omega
  obtain ⟨reduced⟩ :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.exists_of_entry facts hreduceWorkspace
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace facts reduced
  have hconstantReserve : reduced.finalFreePtr + 32 * 234 < 2 ^ 64 := by
    omega
  have hfirstBound : reduced.finalFreePtr + wordArrayAllocationSize
      (dividendLength k) < 2 ^ 64 := by
    apply lt_of_le_of_lt (b := reduced.finalFreePtr + 32 * 234) _ hconstantReserve
    simp only [dividendLength, wordArrayAllocationSize, wordArrayPayloadSize]
    omega
  have hsecondBound : remainderPtr reduced.finalFreePtr k + wordArrayAllocationSize k <
      2 ^ 64 := by
    apply lt_of_le_of_lt (b := reduced.finalFreePtr + 32 * 234) _ hconstantReserve
    simp only [remainderPtr, dividendLength, wordArrayAllocationSize, wordArrayPayloadSize]
    omega
  have hquotientBound : quotientPtr reduced.finalFreePtr k +
      wordArrayAllocationSize (quotientCount k) < 2 ^ 64 := by
    apply lt_of_le_of_lt (b := reduced.finalFreePtr + 32 * 234) _ hconstantReserve
    simp only [quotientPtr, remainderPtr, quotientCount, dividendLength,
      MultiLimbSchoolbookKnuthPrefix.numQ, wordArrayAllocationSize,
      wordArrayPayloadSize]
    omega
  have huBound : normalizedDividendPtr reduced.finalFreePtr k +
      wordArrayAllocationSize (dividendLength k + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt (b := reduced.finalFreePtr + 32 * 234) _ hconstantReserve
    simp only [normalizedDividendPtr, quotientPtr, remainderPtr, quotientCount,
      dividendLength, MultiLimbSchoolbookKnuthPrefix.numQ, wordArrayAllocationSize,
      wordArrayPayloadSize]
    omega
  have hvBound : normalizedDivisorPtr reduced.finalFreePtr k + wordArrayAllocationSize k <
      2 ^ 64 := by
    apply lt_of_le_of_lt (b := reduced.finalFreePtr + 32 * 234) _ hconstantReserve
    simp only [normalizedDivisorPtr, normalizedDividendPtr, quotientPtr, remainderPtr,
      quotientCount, dividendLength, MultiLimbSchoolbookKnuthPrefix.numQ,
      wordArrayAllocationSize, wordArrayPayloadSize]
    omega
  have rd5199 := Modexp.MultiLimbBarrettReduceBase.nonzeroToDivisionEntry
    (tail := exponent :: UInt256.ofNat k :: UInt256.ofNat 1745 :: result ::
      UInt256.ofNat dataLen :: UInt256.ofNat 805 :: retBar :: result :: ret :: tail)
    (basePtr := UInt256.ofNat basePtr) (modulusPtr := UInt256.ofNat modulusPtr)
    (by simp only [List.length_cons]; omega) hbasePos hbaseSize hk
    (by simpa [UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbaseAccess) hbaseLoad
    hbaseFp hbaseBound hmemSize hmemLe hbaseGap haw3 haw64 hbaseFree hcalldata
    (by simpa [UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbaseAccessAllocated)
    hbaseLoadAllocated hremFp hremBound hconvertedSize hconvertedLe
    hremGap hconvertedAw3 hconvertedAw64 hremFree h
  refine ⟨reduced, ?_⟩
  simpa only [Nat.add_assoc] using reduceAndConstantSelection_exists
    (tail := UInt256.ofNat 1745 :: result :: UInt256.ofNat dataLen :: UInt256.ofNat 805 ::
      retBar :: result :: ret :: tail) (exponent := exponent) facts hreduceWorkspace
    reduced hfirstBound hsecondBound hquotientBound huBound hvBound hmodulus hcalldata
    (by simp only [List.length_cons]; omega) rd5199

/-- Construct the complete exposed selector for a direct multi-limb modulus from the real PC 1592
entry.  All post-conversion allocator facts and both division input values are derived from the
original source objects; the only load premises are the Solidity headers immediately before the
first deployed allocator call. -/
theorem directSelection_exists
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat}
    {exponentPtr resultPtr retBar ret : Nat} {tail : List UInt256}
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hp32 : p + 32 < UInt256.size) (hp64 : p + 32 < 2 ^ 64)
    (hpend : p + modulusSize + 31 < UInt256.size)
    (hmodulusSource96 : 96 ≤ p + 32)
    (hmodulusSourceBefore : p + 32 + modulusSize ≤ modulusFp)
    (hactive : p + 64 ≤ 32 * aw.toNat)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (p + 32))) ≠ ⟨0⟩)
    (hmodulusFp : 96 ≤ modulusFp)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (Modexp.MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat modulusFp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hmodulusAccessAllocated : (UInt256.ofNat p).toNat + 32 ≤
      32 * (Modexp.MultiLimbBarrettConversion.allocatedWords aw modulusFp modulusSize).toNat)
    (hmodulusLoadAllocated : wideLoadWord
      (Modexp.MultiLimbBarrettConversion.allocatedMemory mem modulusFp modulusSize)
      (Modexp.MultiLimbBarrettConversion.allocatedWords aw modulusFp modulusSize)
      (UInt256.ofNat p) = UInt256.ofNat modulusSize)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbasePtr96 : 96 ≤ basePtr)
    (hbaseSourceBefore : basePtr + 32 + baseSize ≤ modulusFp)
    (hbaseHeader : mem.readWithPadding basePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize))
    (hbackendWorkspace : directRemFp modulusFp modulusSize baseSize +
      wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize) +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 < 2 ^ 64)
    (hdepth : tail.length ≤ 983)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat modulusSize :: UInt256.ofNat retBar ::
        UInt256.ofNat resultPtr :: UInt256.ofNat exponentPtr :: UInt256.ofNat basePtr ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    Nonempty (DirectSelection I g (initState cA gh bl σ σ₀ g A I) rdata acc mem aw
      steps gasUsed p modulusFp modulusSize basePtr baseSize (UInt256.ofNat exponentPtr)
      (UInt256.ofNat resultPtr) (UInt256.ofNat retBar) (UInt256.ofNat ret) tail) := by
  let kWords := Modexp.MultiLimbBarrettConversion.words modulusSize
  let baseFp := directBaseFp modulusFp modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  let modulusMemory := Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p
    modulusSize
  let modulusWords := Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p
    modulusSize
  have hmodGeometry := Modexp.MultiLimbBarrettConversion.convertedGeometry mem aw modulusFp p
    modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap
    hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hkTwo : 2 ≤ kWords := by
    dsimp only [kWords]
    unfold Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hk : kWords ≤ 32 := by
    dsimp only [kWords]
    unfold Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hbaseFpEq : baseFp = modulusFp + 32 + 32 * kWords := by
    dsimp only [baseFp, directBaseFp, kWords]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmodulusMemorySize : modulusMemory.size = baseFp := by
    dsimp only [modulusMemory]
    rw [hmodGeometry.1, hbaseFpEq]
  have hbaseFp96 : 96 ≤ baseFp := by omega
  have hbaseBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize kWords) < 2 ^ 64 := by
    dsimp only [remFp, directRemFp, baseFp, kWords] at hbackendWorkspace ⊢
    omega
  have hbasePtrFit : basePtr < UInt256.size := by
    have hmodulusFp64 : modulusFp < 2 ^ 64 := by omega
    exact lt_trans (by omega : basePtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hbaseRead : modulusMemory.readWithPadding basePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize) := by
    dsimp only [modulusMemory]
    exact (Modexp.MultiLimbBarrettConversion.convertedMemory_read_below_len mem aw modulusFp p
      modulusSize basePtr 32 hmodulusBound hmemSize hmemLe hmodulusGap hbasePtr96
      (by omega) (by omega) (by omega) hmodulusAllocationBound).trans hbaseHeader
  have hbaseAccess : basePtr + 32 ≤ 32 * modulusWords.toNat := by
    have hcovered := hmodGeometry.2.2.1
    unfold Modexp.MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
    change modulusMemory.size ≤ 32 * modulusWords.toNat at hcovered
    rw [hmodulusMemorySize] at hcovered
    omega
  have hbaseLoad : wideLoadWord modulusMemory modulusWords (UInt256.ofNat basePtr) =
      UInt256.ofNat baseSize := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt hbasePtrFit, hmodulusMemorySize]
      omega
    · apply Modexp.MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
        modulusMemory modulusWords (UInt256.ofNat basePtr)
      · simpa only [modulusMemory, modulusWords] using hmodGeometry.2.2.1
      · simpa only [modulusWords] using hmodGeometry.2.2.2
      · rw [UInt256.toNat_ofNat_of_lt hbasePtrFit, hmodulusMemorySize]
        omega
    · simpa only [UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbaseRead
  have hbaseLoadAllocated : wideLoadWord
      (MultiLimbReduceBase.baseAllocatedMemory modulusMemory baseFp baseSize kWords)
      (MultiLimbReduceBase.baseAllocatedWords modulusWords baseFp baseSize kWords)
      (UInt256.ofNat basePtr) = UInt256.ofNat baseSize := by
    apply Modexp.MultiLimbReduceBaseSemantic.baseAllocatedWideLoad_preserved
      modulusMemory modulusWords (UInt256.ofNat basePtr) baseFp baseSize kWords hbasePos
    · rw [hmodulusMemorySize]
      exact hbaseFp96
    · rw [hmodulusMemorySize]
    · rw [hmodulusMemorySize, Nat.sub_self]
      native_decide
    · simpa only [UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbasePtr96
    · rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]
      omega
    · simpa only [modulusWords] using hmodGeometry.2.2.2
    · exact hbaseBound
    · simpa only [UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbaseRead
  have hbaseGeometry := Modexp.MultiLimbReduceBaseSemantic.convertedGeometry
    modulusMemory modulusWords (UInt256.ofNat basePtr) baseFp baseSize kWords hbasePos
    hbaseSize (by rw [hmodulusMemorySize]; exact hbaseFp96)
    (by rw [hmodulusMemorySize]) (by rw [hmodulusMemorySize, Nat.sub_self]; native_decide)
    (by rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]; omega) hmodGeometry.2.2.2 hbaseBound
  have hremFpEq : remFp = baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize kWords) := by
    rfl
  have hconvertedSize : 96 ≤
      (MultiLimbReduceBase.convertedMemory modulusMemory modulusWords baseFp baseSize kWords
        (UInt256.ofNat basePtr)).size := by
    rw [hbaseGeometry.1]
    omega
  have hconvertedLe :
      (MultiLimbReduceBase.convertedMemory modulusMemory modulusWords baseFp baseSize kWords
        (UInt256.ofNat basePtr)).size ≤ remFp := by
    rw [hbaseGeometry.1, hremFpEq]
    unfold wordArrayAllocationSize wordArrayPayloadSize MultiLimbReduceBase.baseWords
    omega
  have hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory modulusMemory modulusWords baseFp baseSize kWords
        (UInt256.ofNat basePtr)).size < USize.size := by
    rw [hbaseGeometry.1, hremFpEq]
    have hnaturalLe : MultiLimbReduceBase.naturalWords baseSize ≤
        MultiLimbReduceBase.baseWords baseSize kWords := Nat.le_max_left _ _
    have hbaseWordsBound : MultiLimbReduceBase.baseWords baseSize kWords ≤ 32 := by
      unfold MultiLimbReduceBase.baseWords MultiLimbReduceBase.naturalWords
      omega
    unfold wordArrayAllocationSize wordArrayPayloadSize
    apply lt_of_le_of_lt (b := 32 * 32)
    · omega
    · native_decide
  have hremFp96 : 96 ≤ remFp := by omega
  have hremBound : remFp + wordArrayAllocationSize kWords < 2 ^ 64 := by
    dsimp only [remFp, kWords] at hbackendWorkspace ⊢
    omega
  have hconvertedAw3 : 3 ≤
      (MultiLimbReduceBase.convertedWords modulusMemory modulusWords baseFp baseSize kWords
        (UInt256.ofNat basePtr)).toNat := by
    have hcovered := hbaseGeometry.2.2.1
    unfold Modexp.MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
    rw [hbaseGeometry.1] at hcovered
    omega
  have hconvertedAw64 : ¬ (⟨64⟩ : UInt256) ≥
      MultiLimbReduceBase.convertedWords modulusMemory modulusWords baseFp baseSize kWords
        (UInt256.ofNat basePtr) * ⟨32⟩ := by
    intro hle
    have hmul := umul_toNat (a := MultiLimbReduceBase.convertedWords modulusMemory modulusWords
      baseFp baseSize kWords (UInt256.ofNat basePtr)) (b := (⟨32⟩ : UInt256))
      hbaseGeometry.2.2.2
    have hnat : (MultiLimbReduceBase.convertedWords modulusMemory modulusWords baseFp baseSize
      kWords (UInt256.ofNat basePtr) * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul, show (⟨32⟩ : UInt256).toNat = 32 by decide] at hnat
    omega
  have hconvertedFree := Modexp.MultiLimbReduceBaseSemantic.convertedMemory_free_read
    modulusMemory modulusWords (UInt256.ofNat basePtr) baseFp baseSize kWords hbaseSize
    hbaseFp96 (by rw [hmodulusMemorySize]; exact hbaseFp96)
    (by rw [hmodulusMemorySize]) (by rw [hmodulusMemorySize, Nat.sub_self]; native_decide)
    hbaseBound
  have hbaseFree : modulusMemory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat baseFp) := by
    dsimp only [modulusMemory, baseFp, directBaseFp, kWords]
    exact Modexp.MultiLimbBarrettConversion.convertedMemory_free_read mem aw modulusFp p
      modulusSize hmodulusBound hmodulusFp hmemSize hmemLe hmodulusGap
      hmodulusAllocationBound
  have facts := directEntryFacts mem aw (UInt256.ofNat basePtr) modulusFp p modulusSize
    baseSize hmodulusLarge hmodulusBound hmodulusFp hmemSize hmemLe hmodulusGap
    hmodulusSource96 hmodulusSourceBefore hp32 hp64 hactive hfirst
    hawFit hmodulusAllocationBound hbasePos hbaseSize (by
      rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]
      omega) (by omega)
  have hmodulusValue := Modexp.MultiLimbBarrettReduceBaseSemantic.finalModulusArrayValue_eq_model
    mem aw (UInt256.ofNat basePtr) modulusFp p modulusSize baseFp remFp baseSize
    hmodulusLarge hmodulusBound hmodulusFp hmemSize hmemLe hmodulusGap hmodulusSource96
    hmodulusSourceBefore hawFit hmodulusAllocationBound (by rw [hbaseFpEq])
    (by change modulusMemory.size ≤ baseFp; rw [hmodulusMemorySize])
    (by change baseFp - modulusMemory.size < USize.size
        rw [hmodulusMemorySize, Nat.sub_self]
        native_decide)
    hbasePos hbaseSize (by rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]; omega)
    hbaseBound hconvertedLe hremGap hremBound
  have hbaseValue := Modexp.MultiLimbBarrettReduceBaseSemantic.finalBaseArrayValue_eq_model
    mem aw (UInt256.ofNat basePtr) modulusFp p modulusSize baseFp remFp baseSize
    hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap hmodulusSourceBefore
    (by rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]; exact hbaseSourceBefore)
    hawFit hmodulusAllocationBound
    (by change modulusMemory.size ≤ baseFp; rw [hmodulusMemorySize])
    (by change baseFp - modulusMemory.size < USize.size
        rw [hmodulusMemorySize, Nat.sub_self]
        native_decide)
    hbasePos hbaseSize
    (by rw [UInt256.toNat_ofNat_of_lt hbasePtrFit]; omega)
    hbaseBound (by
      rw [hremFpEq]
      change baseFp + 32 + 32 * MultiLimbReduceBase.baseWords baseSize kWords ≤
        baseFp + wordArrayAllocationSize (MultiLimbReduceBase.baseWords baseSize kWords)
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega) hconvertedLe hremGap hremBound
  obtain ⟨scanSteps, rd1700⟩ := Modexp.MultiLimbBarrettConversion.scanDirectExact
    (tail := tail)
    hmodulusLarge hmodulusBound hp32 hpend hactive hfirst hmodulusFp
    hmodulusAllocationBound hmemSize hmemLe hmodulusGap haw3 haw64 hfree hcalldata
    hmodulusAccessAllocated hmodulusLoadAllocated (by omega) h
  obtain ⟨reduced, ⟨constant⟩⟩ := baseToConstantSelection_exists
    (tail := tail)
    (mem := modulusMemory) (aw := modulusWords) (basePtr := basePtr)
    (modulusPtr := modulusFp) (baseFp := baseFp) (remFp := remFp)
    (baseSize := baseSize) (k := kWords)
    (modulusNat := Model.bytesToNatPadded mem (p + 32) modulusSize)
    (dataLen := modulusSize) facts (by
      dsimp only [remFp, kWords] at hbackendWorkspace ⊢
      omega)
    (by simpa only [modulusMemory, modulusWords, baseFp, remFp, kWords] using hmodulusValue)
    hbasePos hbaseSize hk hbasePtrFit
    (by simpa only [UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbaseAccess)
    (by simpa only [modulusMemory, modulusWords] using hbaseLoad) hbaseFp96 hbaseBound
    (by rw [hmodulusMemorySize]; exact hbaseFp96) (by rw [hmodulusMemorySize])
    (by rw [hmodulusMemorySize, Nat.sub_self]; native_decide)
    (by
      have hcovered := hmodGeometry.2.2.1
      unfold Modexp.MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
      change modulusMemory.size ≤ 32 * modulusWords.toNat at hcovered
      rw [hmodulusMemorySize] at hcovered
      omega)
    (by
      intro hle
      have hmul := umul_toNat (a := modulusWords) (b := (⟨32⟩ : UInt256))
        (by simpa only [modulusWords] using hmodGeometry.2.2.2)
      have hnat : (modulusWords * ⟨32⟩).toNat ≤ 64 := hle
      rw [hmul, show (⟨32⟩ : UInt256).toNat = 32 by decide] at hnat
      omega)
    hbaseFree hcalldata
    (by
      unfold MultiLimbReduceBase.baseAllocatedWords
      have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range modulusWords
        baseFp (MultiLimbReduceBase.baseWords baseSize kWords) (by
          unfold MultiLimbReduceBase.baseWords MultiLimbReduceBase.naturalWords
          omega) hmodGeometry.2.2.2 (by
            exact lt_trans (by omega : baseFp + wordArrayAllocationSize
              (MultiLimbReduceBase.baseWords baseSize kWords) + 31 < 2 ^ 64 + 31)
              (by norm_num [UInt256.size]))
      exact le_trans (by omega) hrange.1)
    (by simpa only [modulusMemory, modulusWords] using hbaseLoadAllocated)
    hremFp96 hremBound hconvertedSize hconvertedLe hremGap hconvertedAw3 hconvertedAw64
    (by simpa only [modulusMemory, modulusWords, hremFpEq] using hconvertedFree) hdepth
    (by simpa only [modulusMemory, modulusWords, baseFp, kWords] using rd1700)
  have hsourceReadBelow : ∀ read, 96 ≤ read → read + 32 ≤ modulusFp →
      (Modexp.MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw
        (UInt256.ofNat basePtr) modulusFp p modulusSize baseFp remFp baseSize
      ).readWithPadding read 32 = mem.readWithPadding read 32 := by
    intro read hread96 hreadBelow
    have hrem := Modexp.MultiLimbReduceBaseSemantic.remainderMemory_read_below
      modulusMemory modulusWords (UInt256.ofNat basePtr) baseFp remFp baseSize kWords read
      hconvertedSize hread96 (by omega) hremGap
    have hbase := Modexp.MultiLimbReduceBaseSemantic.convertedMemory_read_below
      modulusMemory modulusWords (UInt256.ofNat basePtr) baseFp baseSize kWords read
      hbaseSize (by rw [hmodulusMemorySize]; exact hbaseFp96)
      (by rw [hmodulusMemorySize])
      (by rw [hmodulusMemorySize, Nat.sub_self]; native_decide)
      hread96 (by omega) hbaseBound
    have hmodulus := Modexp.MultiLimbBarrettConversion.convertedMemory_read_below_len
      mem aw modulusFp p modulusSize read 32 hmodulusBound hmemSize hmemLe
      hmodulusGap hread96 hreadBelow (by omega) (by omega) hmodulusAllocationBound
    exact hrem.trans (hbase.trans hmodulus)
  refine ⟨{
    scanSteps := scanSteps
    dataLenLarge := hmodulusLarge
    dataLenBound := hmodulusBound
    calldataBound := hcalldata
    backendWorkspace := hbackendWorkspace
    entryFacts := by simpa only [modulusMemory, modulusWords, baseFp, remFp, kWords] using facts
    baseInput_eq := by
      simpa only [modulusMemory, modulusWords, baseFp, remFp, kWords,
        UInt256.toNat_ofNat_of_lt hbasePtrFit] using hbaseValue
    modulus_eq := by
      simpa only [modulusMemory, modulusWords, baseFp, remFp, kWords] using hmodulusValue
    reduced := by simpa only [modulusMemory, modulusWords, baseFp, remFp, kWords] using reduced
    constant := by
      simpa only [modulusMemory, modulusWords, baseFp, remFp, kWords, Nat.add_assoc] using
        constant
    sourceReadBelow := by
      exact hsourceReadBelow }⟩

/-- The complete direct selector preserves every source word below the newly allocated modulus
array through base conversion, selected division, and Barrett-constant construction. -/
theorem DirectSelection.constantReadBelow
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata mem : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw : UInt256}
    {steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat}
    {exponent result retBar ret : UInt256} {tail : List UInt256}
    (selected : DirectSelection I g s0 rdata acc mem aw steps gasUsed p modulusFp
      modulusSize basePtr baseSize exponent result retBar ret tail)
    (read : Nat) (hread96 : 96 ≤ read) (hbelow : read + 32 ≤ modulusFp) :
    selected.constant.finalMemory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  have hworkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    have h := selected.backendWorkspace
    dsimp only [remFp, k] at h ⊢
    omega
  have hconstant := selected.constant.finalReadBelow read hread96 (by
    apply le_trans hbelow
    apply le_trans (show modulusFp ≤ remFp + wordArrayAllocationSize k by
      dsimp only [remFp, k]
      unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
      omega)
    exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
      selected.reduced)
  have hreduced :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalReadBelowRemainderHeader
      selected.entryFacts hworkspace selected.reduced hread96 (by
        unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
        omega)
  exact hconstant.trans (hreduced.trans (selected.sourceReadBelow read hread96 hbelow))

/-- Accumulator allocation and `r[0] = 1` preserve the same source words. -/
theorem DirectSelection.initializedReadBelow
    {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata mem : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {aw : UInt256}
    {steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat}
    {exponent result retBar ret : UInt256} {tail : List UInt256}
    (selected : DirectSelection I g s0 rdata acc mem aw steps gasUsed p modulusFp
      modulusSize basePtr baseSize exponent result retBar ret tail)
    (read : Nat) (hread96 : 96 ≤ read) (hbelow : read + 32 ≤ modulusFp) :
    (initializedMemory selected.constant.finalMemory
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (Modexp.MultiLimbBarrettConversion.words modulusSize)).readWithPadding read 32 =
        mem.readWithPadding read 32 := by
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  have hrFp : 96 ≤ rFp := by
    dsimp only [rFp]
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ selected.constant.finalMemory.size := by
    rw [selected.constant.finalMemorySize]
    exact hrFp
  have hmemLe : selected.constant.finalMemory.size ≤ rFp := by
    rw [selected.constant.finalMemorySize]
    rfl
  have hgap : rFp - selected.constant.finalMemory.size < USize.size := by
    rw [selected.constant.finalMemorySize]
    dsimp only [rFp, k]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have hinitialized := initializedMemory_read_below selected.constant.finalMemory rFp k read
    hmemSize hmemLe hgap hread96 (by
      apply le_trans hbelow
      apply le_trans (b := selected.reduced.finalFreePtr)
      · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
            wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
        · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.reduced
      · dsimp only [rFp, k]
        unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega)
  exact hinitialized.trans (selected.constantReadBelow read hread96 hbelow)

/-- Consume a completed Barrett-constant selector and execute the deployed accumulator allocation,
checked `r[0]` access, initialization store, and jump to the exponent-loop entry. -/
theorem Selection.accumulatorSetupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat : Nat} {tail : List UInt256}
    {exponent modulus baseReduced : UInt256}
    (selected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 1008) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3154⟩
      (UInt256.ofNat (accumulatorFp fp k) :: baseReduced :: exponent :: modulus ::
        UInt256.ofNat (quotientPtr fp k) :: UInt256.ofNat k :: tail)
      (initializedMemory selected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords selected.finalWords (accumulatorFp fp k) k)
      rdata acc
      (initialSteps + selected.stepDelta + 104)
      (initialGas + selected.gasDelta +
        setupGas selected.finalWords (accumulatorFp fp k) k) := by
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ selected.finalMemory.size := by
    rw [selected.finalMemorySize]
    exact haccFp
  have hmemLe : selected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [selected.finalMemorySize]
    rfl
  have hgap : accumulatorFp fp k - selected.finalMemory.size < USize.size := by
    rw [selected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have haw3 : 3 ≤ selected.finalWords.toNat := by
    have hcovered := selected.workspaceCovered
    change accumulatorFp fp k ≤ 32 * selected.finalWords.toNat at hcovered
    omega
  have hmul : (selected.finalWords * (⟨32⟩ : UInt256)).toNat =
      selected.finalWords.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := selected.finalWords) (b := (⟨32⟩ : UInt256))
        selected.finalWordsFit
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ selected.finalWords * ⟨32⟩ := by
    intro hle
    have hnat : (selected.finalWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have rd3154 := MultiLimbBarrettAccumulator.setupExact hkTwo hk haccFp hbound hmemSize
    hmemLe hgap haw3 haw64 selected.finalWordsFit hfit selected.finalFreePointer hcalldata
    hdepth selected.exactExecution
  simpa only [Nat.add_assoc] using rd3154

/-- Compose a constant selector with any concrete valid exponent-loop selection. The resulting
gas is the exact sum of the selected constant path, accumulator setup, and selected exponent path. -/
theorem Selection.exponentExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel : Nat} {tail : List UInt256}
    {exponent modulus baseReduced returnPc : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.BarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: returnPc :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.BarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (hdepth : tail.length + 37 ≤ 1016)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat (accumulatorFp fp k) :: tail)
      exponentSelected.memory exponentSelected.activeWords rdata acc
      (initialSteps + constantSelected.stepDelta + 104 + exponentSelected.steps)
      (initialGas + constantSelected.gasDelta +
        setupGas constantSelected.finalWords (accumulatorFp fp k) k +
        exponentSelected.gas
          (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent) := by
  have rd3154 :=
    Modexp.MultiLimbBarrettComposition.Selection.accumulatorSetupExact
      constantSelected hkTwo hk hfp hbound hcalldata
      (by simp only [List.length_cons]; omega)
  have rdReturn := valid.exact rfl (by omega) hreturn rd3154
  simpa only [Nat.add_assoc] using rdReturn

/-- Compose a constant selector with the canonical fresh exponent selection. The selected first
square materializes scratch, and the exact gas remains the sum of all concrete selected paths. -/
theorem Selection.freshExponentExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel : Nat} {tail : List UInt256}
    {exponent modulus baseReduced returnPc : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: returnPc :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (hdepth : tail.length + 37 ≤ 1016)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat (accumulatorFp fp k) :: tail)
      exponentSelected.memory exponentSelected.activeWords rdata acc
      (initialSteps + constantSelected.stepDelta + 104 + exponentSelected.steps)
      (initialGas + constantSelected.gasDelta +
        setupGas constantSelected.finalWords (accumulatorFp fp k) k +
        exponentSelected.gas
          (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent) := by
  have rd3154 :=
    Modexp.MultiLimbBarrettComposition.Selection.accumulatorSetupExact
      constantSelected hkTwo hk hfp hbound hcalldata
      (by simp only [List.length_cons]; omega)
  have rdReturn := valid.exact rfl (by omega) hreturn rd3154
  simpa only [Nat.add_assoc] using rdReturn

/-- Execute a completed constant selector through the exposed fresh exponent selector, concrete
serializer, and external wrapper return. The gas index is the exact sum of every selected path. -/
theorem Selection.freshExactReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel dataLen value : Nat}
    {tail : List UInt256}
    {exponent modulus baseReduced result ret : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨173⟩ :: result :: ret :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * exponentSelected.activeWords.toNat)
    (hpartialOutIn : result.toNat + 64 ≤ exponentSelected.memory.size)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ accumulatorFp fp k)
    (hselectedCovered : Modexp.MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      exponentSelected.memory exponentSelected.activeWords)
    (hselectedAwFit : exponentSelected.activeWords.toNat * 32 < UInt256.size)
    (hselectedHeader : Modexp.MultiLimbLimbsToBytes.headerValue
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) = UInt256.ofNat k)
    (haccumulator : Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
      (UInt256.ofNat (accumulatorFp fp k)) exponentSelected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : exponentSelected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen)
      (initialGas + constantSelected.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas constantSelected.finalWords
          (accumulatorFp fp k) k exponent exponentSelected dataLen + 16) := by
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ constantSelected.finalMemory.size := by
    rw [constantSelected.finalMemorySize]
    exact haccFp
  have hmemLe : constantSelected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [constantSelected.finalMemorySize]
    unfold accumulatorFp
    rfl
  have hgap : accumulatorFp fp k - constantSelected.finalMemory.size < USize.size := by
    rw [constantSelected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have haw3 : 3 ≤ constantSelected.finalWords.toNat := by
    have hcovered := constantSelected.workspaceCovered
    change accumulatorFp fp k ≤ 32 * constantSelected.finalWords.toNat at hcovered
    omega
  have hmul : (constantSelected.finalWords * (⟨32⟩ : UInt256)).toNat =
      constantSelected.finalWords.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := constantSelected.finalWords) (b := (⟨32⟩ : UInt256))
        constantSelected.finalWordsFit
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ constantSelected.finalWords * ⟨32⟩ := by
    intro hle
    have hnat : (constantSelected.finalWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hdepth' : tail.length + 43 ≤ 1015 := hdepth
  have rd := Modexp.MultiLimbBarrettResultSemantic.freshExactReturn_of_serializerGeometry
    hkTwo hk haccFp hbound hmemSize hmemLe hgap haw3 haw64
    constantSelected.finalWordsFit hfit constantSelected.finalFreePointer hcalldata valid
    hlen hkData hresultAddr hresultAddr64 hresultMem hsourceActive hpartialOutIn
    houtBeforeHeader hselectedCovered hselectedAwFit hselectedHeader haccumulator hvalueFit
    hresultHeader hdepth' constantSelected.exactExecution
  simpa only [Nat.add_assoc] using rd

/-- Invariant-driven form of `freshExactReturn`. All final selector memory geometry is derived
from the concrete initialized exponent invariant; only the preallocated result header's frame is
kept explicit until the top-level allocator/backend frame theorem is connected. -/
theorem Selection.freshExactReturn_of_invariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel dataLen baseValue value : Nat}
    {baseSize exponentSize byteFuel bitFuel : Nat}
    {tail : List UInt256}
    {exponent modulus baseReduced result ret : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨173⟩ :: result :: ret :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (invariant : Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) 1 baseValue modulusNat)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt
        (Modexp.MultiLimbExponentTrace.exponentArrayLength
          (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
          (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent) ≠ ⟨0⟩ →
      (idx.lt (Modexp.MultiLimbExponentTrace.exponentArrayLength mem' aw' exponent)).isZero =
          ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent idx).toNat + 32 + 31 <
        UInt256.size)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ accumulatorFp fp k)
    (haccumulator : Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
      (UInt256.ofNat (accumulatorFp fp k)) exponentSelected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : exponentSelected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen)
      (initialGas + constantSelected.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas constantSelected.finalWords
          (accumulatorFp fp k) k exponent exponentSelected dataLen + 16) := by
  have hgeometry :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.finalGeometry
      valid invariant alignment hexponentFit haccess
  have hselectedCovered := hgeometry.1
  have hselectedAwFit := hgeometry.2.1
  have hselectedRawHeader := hgeometry.2.2
  have hpartialOutIn : result.toNat + 64 ≤ exponentSelected.memory.size := by
    apply le_trans (b := result.toNat + 32 + dataLen)
    · have hkDataTwo : 2 ≤ (dataLen + 31) / 32 := by simpa [← hkData] using hkTwo
      omega
    · exact hresultMem
  have haccBound : accumulatorFp fp k < 2 ^ 64 := by omega
  have haccNat : (UInt256.ofNat (accumulatorFp fp k)).toNat = accumulatorFp fp k :=
    UInt256.toNat_ofNat_of_lt (lt_trans haccBound (by norm_num [UInt256.size]))
  have hselectedHeader : Modexp.MultiLimbLimbsToBytes.headerValue
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) = UInt256.ofNat k := by
    apply Modexp.MultiLimbBarrettResultSemantic.headerValue_eq_of_rawHeader
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) k hselectedCovered hselectedAwFit
    · simpa only [haccNat] using hselectedRawHeader
  exact Modexp.MultiLimbBarrettComposition.Selection.freshExactReturn constantSelected
    hkTwo hk hbound hcalldata valid hlen hkData hresultAddr hresultAddr64 hresultMem
    hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered hselectedAwFit hselectedHeader
    haccumulator hvalueFit hresultHeader hdepth

/-- Invariant-driven fresh result path returning to an arbitrary deployed caller continuation.
This is the form needed by normalized Barrett recursion: the selected computation serializes into
the temporary result object and returns to PC 1808 without prematurely invoking the external
wrapper.  Both the selector and its exact path-sensitive gas remain visible in the conclusion. -/
theorem Selection.freshReturn_of_invariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel dataLen baseValue : Nat}
    {baseSize exponentSize byteFuel bitFuel : Nat}
    {tail : List UInt256}
    {exponent modulus baseReduced retBar result ret : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (invariant : Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) 1 baseValue modulusNat)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt
        (Modexp.MultiLimbExponentTrace.exponentArrayLength
          (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
          (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent) ≠ ⟨0⟩ →
      (idx.lt (Modexp.MultiLimbExponentTrace.exponentArrayLength mem' aw' exponent)).isZero =
          ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent idx).toNat + 32 + 31 <
        UInt256.size)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultMem : result.toNat + 32 + dataLen ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ accumulatorFp fp k)
    (hdepth : tail.length + 43 ≤ 1015)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) retBar
      (result :: ret :: tail)
      (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords (UInt256.ofNat (accumulatorFp fp k)) result dataLen)
      exponentSelected.activeWords rdata acc
      (initialSteps + constantSelected.stepDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionSteps exponentSelected dataLen)
      (initialGas + constantSelected.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas constantSelected.finalWords
          (accumulatorFp fp k) k exponent exponentSelected dataLen) := by
  have hgeometry :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.finalGeometry
      valid invariant alignment hexponentFit haccess
  have hselectedCovered := hgeometry.1
  have hselectedAwFit := hgeometry.2.1
  have hselectedRawHeader := hgeometry.2.2
  have hpartialOutIn : result.toNat + 64 ≤ exponentSelected.memory.size := by
    apply le_trans (b := result.toNat + 32 + dataLen)
    · have hkDataTwo : 2 ≤ (dataLen + 31) / 32 := by simpa [← hkData] using hkTwo
      omega
    · exact hresultMem
  have haccBound : accumulatorFp fp k < 2 ^ 64 := by omega
  have haccNat : (UInt256.ofNat (accumulatorFp fp k)).toNat = accumulatorFp fp k :=
    UInt256.toNat_ofNat_of_lt (lt_trans haccBound (by norm_num [UInt256.size]))
  have hselectedHeader : Modexp.MultiLimbLimbsToBytes.headerValue
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) = UInt256.ofNat k := by
    apply Modexp.MultiLimbBarrettResultSemantic.headerValue_eq_of_rawHeader
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) k hselectedCovered hselectedAwFit
    simpa only [haccNat] using hselectedRawHeader
  have hsourceFit : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) <
      UInt256.size := by
    have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
      lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
        2 ^ 64 + 31) (by norm_num [UInt256.size])
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    rw [← hkData]
    omega
  have hserializer :=
    Modexp.MultiLimbBarrettResultSemantic.serializerValidity_of_geometry hlen hkData
      hresultAddr hresultMem hsourceFit hsourceActive hpartialOutIn houtBeforeHeader
      hselectedCovered hselectedHeader
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ constantSelected.finalMemory.size := by
    rw [constantSelected.finalMemorySize]
    exact haccFp
  have hmemLe : constantSelected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [constantSelected.finalMemorySize]
    rfl
  have hgap : accumulatorFp fp k - constantSelected.finalMemory.size < USize.size := by
    rw [constantSelected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have haw3 : 3 ≤ constantSelected.finalWords.toNat := by
    have hcovered := constantSelected.workspaceCovered
    change accumulatorFp fp k ≤ 32 * constantSelected.finalWords.toNat at hcovered
    omega
  have hmul : (constantSelected.finalWords * (⟨32⟩ : UInt256)).toNat =
      constantSelected.finalWords.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := constantSelected.finalWords) (b := (⟨32⟩ : UInt256))
        constantSelected.finalWordsFit
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ constantSelected.finalWords * ⟨32⟩ := by
    intro hle
    have hnat : (constantSelected.finalWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have rd := Modexp.MultiLimbBarrettResult.freshExact hkTwo hk haccFp hbound hmemSize
    hmemLe hgap haw3 haw64 constantSelected.finalWordsFit hfit
    constantSelected.finalFreePointer hcalldata valid hlen hserializer.1 hserializer.2.1
    hdepth hretBar constantSelected.exactExecution
  simpa only [Nat.add_assoc] using rd

/-- Concrete-frame form of `freshReturn_of_invariant`. The exponent header and byte-address
bounds are tied to the initialized selector memory and preserved across selected Barrett calls. -/
theorem Selection.freshReturn_of_invariantFramed
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel dataLen baseValue : Nat}
    {baseSize exponentSize byteFuel bitFuel : Nat}
    {tail : List UInt256}
    {exponent modulus baseReduced retBar result ret : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: retBar :: result :: ret :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (invariant : Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) 1 baseValue modulusNat)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (access : Modexp.MultiLimbBarrettExponentLoop.BarrettExponentAccessFrame
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (UInt256.ofNat (accumulatorFp fp k)))
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultMem : result.toNat + 32 + dataLen ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ accumulatorFp fp k)
    (hdepth : tail.length + 43 ≤ 1015)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) retBar
      (result :: ret :: tail)
      (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords (UInt256.ofNat (accumulatorFp fp k)) result dataLen)
      exponentSelected.activeWords rdata acc
      (initialSteps + constantSelected.stepDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionSteps exponentSelected dataLen)
      (initialGas + constantSelected.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas constantSelected.finalWords
          (accumulatorFp fp k) k exponent exponentSelected dataLen) := by
  have hgeometry :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.finalGeometryFramed
      valid invariant alignment access
  have hselectedCovered := hgeometry.1
  have hselectedAwFit := hgeometry.2.1
  have hselectedRawHeader := hgeometry.2.2
  have hpartialOutIn : result.toNat + 64 ≤ exponentSelected.memory.size := by
    apply le_trans (b := result.toNat + 32 + dataLen)
    · have hkDataTwo : 2 ≤ (dataLen + 31) / 32 := by simpa [← hkData] using hkTwo
      omega
    · exact hresultMem
  have haccBound : accumulatorFp fp k < 2 ^ 64 := by omega
  have haccNat : (UInt256.ofNat (accumulatorFp fp k)).toNat = accumulatorFp fp k :=
    UInt256.toNat_ofNat_of_lt (lt_trans haccBound (by norm_num [UInt256.size]))
  have hselectedHeader : Modexp.MultiLimbLimbsToBytes.headerValue
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) = UInt256.ofNat k := by
    apply Modexp.MultiLimbBarrettResultSemantic.headerValue_eq_of_rawHeader
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) k hselectedCovered hselectedAwFit
    simpa only [haccNat] using hselectedRawHeader
  have hsourceFit : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) <
      UInt256.size := by
    have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
      lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
        2 ^ 64 + 31) (by norm_num [UInt256.size])
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    rw [← hkData]
    omega
  have hserializer :=
    Modexp.MultiLimbBarrettResultSemantic.serializerValidity_of_geometry hlen hkData
      hresultAddr hresultMem hsourceFit hsourceActive hpartialOutIn houtBeforeHeader
      hselectedCovered hselectedHeader
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ constantSelected.finalMemory.size := by
    rw [constantSelected.finalMemorySize]
    exact haccFp
  have hmemLe : constantSelected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [constantSelected.finalMemorySize]
    rfl
  have hgap : accumulatorFp fp k - constantSelected.finalMemory.size < USize.size := by
    rw [constantSelected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have haw3 : 3 ≤ constantSelected.finalWords.toNat := by
    have hcovered := constantSelected.workspaceCovered
    change accumulatorFp fp k ≤ 32 * constantSelected.finalWords.toNat at hcovered
    omega
  have hmul : (constantSelected.finalWords * (⟨32⟩ : UInt256)).toNat =
      constantSelected.finalWords.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := constantSelected.finalWords) (b := (⟨32⟩ : UInt256))
        constantSelected.finalWordsFit
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ constantSelected.finalWords * ⟨32⟩ := by
    intro hle
    have hnat : (constantSelected.finalWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have rd := Modexp.MultiLimbBarrettResult.freshExact hkTwo hk haccFp hbound hmemSize
    hmemLe hgap haw3 haw64 constantSelected.finalWordsFit hfit
    constantSelected.finalFreePointer hcalldata valid hlen hserializer.1 hserializer.2.1
    hdepth hretBar constantSelected.exactExecution
  simpa only [Nat.add_assoc] using rd

/-- Invariant-driven fresh result path for the deployed multi-limb caller, whose serializer
returns through PC 1271 before entering the external wrapper at PC 173. -/
theorem Selection.freshExactReturnVia1271_of_invariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas fp k modulusNat callFuel dataLen baseValue value : Nat}
    {baseSize exponentSize byteFuel bitFuel : Nat}
    {tail : List UInt256}
    {exponent modulus baseReduced result : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (constantSelected : Selection (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas
      (exponent :: modulus :: baseReduced :: UInt256.ofNat k :: ⟨1745⟩ ::
        result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨1271⟩ :: result :: ⟨173⟩ :: tail))
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hbound : accumulatorFp fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (invariant : Modexp.MultiLimbBarrettExponentLoop.InitialBarrettExponentInvariant I
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) 1 baseValue modulusNat)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp fp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp fp k)) baseReduced modulus
      (UInt256.ofNat (quotientPtr fp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
        (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent)
      (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
      (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k)
      exponentSelected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt
        (Modexp.MultiLimbExponentTrace.exponentArrayLength
          (initializedMemory constantSelected.finalMemory (accumulatorFp fp k) k)
          (allocatedWords constantSelected.finalWords (accumulatorFp fp k) k) exponent) ≠ ⟨0⟩ →
      (idx.lt (Modexp.MultiLimbExponentTrace.exponentArrayLength mem' aw' exponent)).isZero =
          ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent idx).toNat + 32 + 31 <
        UInt256.size)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp fp k + 32 + 32 * ((dataLen + 31) / 32) ≤
      32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ accumulatorFp fp k)
    (haccumulator : Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
      (UInt256.ofNat (accumulatorFp fp k)) exponentSelected.memory = value)
    (hvalueFit : value < 256 ^ dataLen)
    (hresultHeader : exponentSelected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes value dataLen)
      (initialGas + constantSelected.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas constantSelected.finalWords
          (accumulatorFp fp k) k exponent exponentSelected dataLen + 28) := by
  have hgeometry :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.finalGeometry
      valid invariant alignment hexponentFit haccess
  have hselectedCovered := hgeometry.1
  have hselectedAwFit := hgeometry.2.1
  have hselectedRawHeader := hgeometry.2.2
  have hpartialOutIn : result.toNat + 64 ≤ exponentSelected.memory.size := by
    apply le_trans (b := result.toNat + 32 + dataLen)
    · have hkDataTwo : 2 ≤ (dataLen + 31) / 32 := by simpa [← hkData] using hkTwo
      omega
    · exact hresultMem
  have haccBound : accumulatorFp fp k < 2 ^ 64 := by omega
  have haccNat : (UInt256.ofNat (accumulatorFp fp k)).toNat = accumulatorFp fp k :=
    UInt256.toNat_ofNat_of_lt (lt_trans haccBound (by norm_num [UInt256.size]))
  have hselectedHeader : Modexp.MultiLimbLimbsToBytes.headerValue
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) = UInt256.ofNat k := by
    apply Modexp.MultiLimbBarrettResultSemantic.headerValue_eq_of_rawHeader
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp fp k)) k hselectedCovered hselectedAwFit
    · simpa only [haccNat] using hselectedRawHeader
  have haccFp : 96 ≤ accumulatorFp fp k := by
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemSize : 96 ≤ constantSelected.finalMemory.size := by
    rw [constantSelected.finalMemorySize]
    exact haccFp
  have hmemLe : constantSelected.finalMemory.size ≤ accumulatorFp fp k := by
    rw [constantSelected.finalMemorySize]
    rfl
  have hgap : accumulatorFp fp k - constantSelected.finalMemory.size < USize.size := by
    rw [constantSelected.finalMemorySize]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have haw3 : 3 ≤ constantSelected.finalWords.toNat := by
    have hcovered := constantSelected.workspaceCovered
    change accumulatorFp fp k ≤ 32 * constantSelected.finalWords.toNat at hcovered
    omega
  have hmul : (constantSelected.finalWords * (⟨32⟩ : UInt256)).toNat =
      constantSelected.finalWords.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := constantSelected.finalWords) (b := (⟨32⟩ : UInt256))
        constantSelected.finalWordsFit
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ constantSelected.finalWords * ⟨32⟩ := by
    intro hle
    have hnat : (constantSelected.finalWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hfit : accumulatorFp fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : accumulatorFp fp k + wordArrayAllocationSize k + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have rd := Modexp.MultiLimbBarrettResultSemantic.freshExactReturnVia1271_of_serializerGeometry
    hkTwo hk haccFp hbound hmemSize hmemLe hgap haw3 haw64 constantSelected.finalWordsFit
    hfit constantSelected.finalFreePointer hcalldata valid hlen hkData hresultAddr
    hresultAddr64 hresultMem hsourceActive hpartialOutIn houtBeforeHeader hselectedCovered
    hselectedAwFit hselectedHeader haccumulator hvalueFit hresultHeader hdepth
    constantSelected.exactExecution
  simpa only [Nat.add_assoc] using rd

/-- End-to-end arithmetic/serialization bridge for a concretely selected base reduction and
Barrett constant.  The returned bytes are identified with the trusted pure modular-power model;
neither the reduced base nor the final accumulator value is an independent premise. -/
theorem reducedFreshExactReturnVia1271
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {rdata reduceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {reduceAw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount k reduceFp constantFp : Nat}
    {baseInput modulusNat initialSteps initialGas dataLen : Nat}
    {baseSize exponentSize byteFuel bitFuel callFuel : Nat}
    {tail : List UInt256} {exponent result : UInt256}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (facts : Modexp.MultiLimbBarrettReduceBaseComplete.EntryFacts reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (hreduceWorkspace : reduceFp +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64)
    (reduced : Modexp.MultiLimbBarrettReduceBaseComplete.Selection reduceMemory reduceAw
      dividendPtr divisorPtr remPtr dividendCount k reduceFp)
    (constant : Modexp.MultiLimbBarrettConstantComplete.Selection
      (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) reduced.finalMemory constantFp k modulusNat
      initialSteps initialGas
      (exponent :: UInt256.ofNat divisorPtr :: UInt256.ofNat remPtr :: UInt256.ofNat k ::
        ⟨1745⟩ :: result :: UInt256.ofNat dataLen :: ⟨805⟩ :: ⟨1271⟩ :: result ::
        ⟨173⟩ :: tail))
    (hconstantAfterArrays : remPtr + 32 * (k + 1) ≤ constantFp)
    (hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp constantFp k + wordArrayAllocationSize k) k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseInput : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat dividendPtr) 0 dividendCount) = baseInput)
    (hmodulus : Modexp.wordLimbsToNat
      (Modexp.MultiLimbSchoolbookNormalizationSemantic.arrayReadWords reduceMemory reduceAw
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k)
      exponentSelected)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel k
      (accumulatorFp constantFp k + wordArrayAllocationSize k)
      (UInt256.ofNat (accumulatorFp constantFp k)) (UInt256.ofNat remPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (quotientPtr constantFp k)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
        (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent)
      (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
      (allocatedWords constant.finalWords (accumulatorFp constantFp k) k)
      exponentSelected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt
        (Modexp.MultiLimbExponentTrace.exponentArrayLength
          (initializedMemory constant.finalMemory (accumulatorFp constantFp k) k)
          (allocatedWords constant.finalWords (accumulatorFp constantFp k) k) exponent) ≠ ⟨0⟩ →
      (idx.lt (Modexp.MultiLimbExponentTrace.exponentArrayLength mem' aw' exponent)).isZero =
          ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent idx).toNat + 32 + 31 <
        UInt256.size)
    (hlen : dataLen ≤ 1024)
    (hkData : k = (dataLen + 31) / 32)
    (hresultAddr : result.toNat + 32 + dataLen < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + dataLen < 2 ^ 64)
    (hresultMem : result.toNat + 32 + dataLen ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp constantFp k + 32 +
      32 * ((dataLen + 31) / 32) ≤ 32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + dataLen ≤ accumulatorFp constantFp k)
    (hmodulusFitsData : modulusNat ≤ 256 ^ dataLen)
    (hresultHeader : exponentSelected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat dataLen))
    (hdepth : tail.length + 43 ≤ 1015) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (baseInput ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
          modulusNat) dataLen)
      (initialGas + constant.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas constant.finalWords
          (accumulatorFp constantFp k) k exponent exponentSelected dataLen + 28) := by
  have invariant := reducedInitializedInvariant facts hreduceWorkspace reduced constant
    hconstantAfterArrays hscratch hcalldata hbaseInput hmodulus
  have haccumulator := reducedFreshAccumulator_eq_modelPow facts hreduceWorkspace reduced
    constant hconstantAfterArrays hscratch hcalldata hbaseInput hmodulus valid alignment
    hexponentFit haccess
  have hvalueFit :
      baseInput ^ Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
          modulusNat < 256 ^ dataLen := by
    have hmodPos := invariant.nPos
    exact lt_of_lt_of_le (Nat.mod_lt _ hmodPos) hmodulusFitsData
  exact Selection.freshExactReturnVia1271_of_invariant constant facts.divisorTwo
    facts.divisorBound (by
      unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
        Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
      omega) hcalldata valid invariant alignment hexponentFit haccess hlen hkData
    hresultAddr hresultAddr64 hresultMem hsourceActive houtBeforeHeader haccumulator
    hvalueFit hresultHeader hdepth

/-- Complete direct multi-limb Barrett execution from the exposed PC 1592 selector through the
real PC 1271 return.  The source base and modulus are the copied input bytes carried by the
selector, while the selected exponent trace remains explicit and determines the exact gas. -/
theorem DirectSelection.freshExactReturnVia1271
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat}
    {tail : List UInt256} {exponent result : UInt256}
    {exponentSize byteFuel bitFuel callFuel : Nat}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (selected : DirectSelection I g (initState cA gh bl σ σ₀ g A I) rdata acc mem aw
      steps gasUsed p modulusFp modulusSize basePtr baseSize exponent result ⟨1271⟩ ⟨173⟩ tail)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (allocatedWords selected.constant.finalWords
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponentSelected)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (allocatedWords selected.constant.finalWords
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponentSelected)
    (hexponentFit : exponent.toNat + 32 + 31 < UInt256.size)
    (haccess : ∀ (mem' : ByteArray) (aw' idx : UInt256), idx.lt
        (Modexp.MultiLimbExponentTrace.exponentArrayLength
          (initializedMemory selected.constant.finalMemory
            (accumulatorFp selected.reduced.finalFreePtr
              (Modexp.MultiLimbBarrettConversion.words modulusSize))
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (allocatedWords selected.constant.finalWords
            (accumulatorFp selected.reduced.finalFreePtr
              (Modexp.MultiLimbBarrettConversion.words modulusSize))
            (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent) ≠ ⟨0⟩ →
      (idx.lt (Modexp.MultiLimbExponentTrace.exponentArrayLength mem' aw' exponent)).isZero =
          ⟨0⟩ ∧
      exponent.toNat + 32 + 31 < UInt256.size ∧
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent idx).toNat + 32 + 31 <
        UInt256.size)
    (hresultAddr : result.toNat + 32 + modulusSize < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + modulusSize < 2 ^ 64)
    (hresultMem : result.toNat + 32 + modulusSize ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) + 32 +
      32 * ((modulusSize + 31) / 32) ≤ 32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + modulusSize ≤
      accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
    (hresultHeader : exponentSelected.memory.readWithPadding result.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize))
    (hdepth : tail.length + 43 ≤ 1015) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) acc
      (Model.natToBytes
        (Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
          Model.bytesToNatPadded mem (p + 32) modulusSize) modulusSize)
      (gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
          modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
          (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
          (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
          (directBaseFp modulusFp modulusSize)
          (directRemFp modulusFp modulusSize baseSize) baseSize
          (Modexp.MultiLimbBarrettConversion.words modulusSize) (UInt256.ofNat basePtr) +
        selected.reduced.gasDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
          selected.reduced.finalMemory selected.reduced.finalWords
          selected.reduced.finalFreePtr (Modexp.MultiLimbBarrettConversion.words modulusSize)
          modulusFp + selected.constant.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize) exponent exponentSelected
          modulusSize + 28) := by
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  have hbackend := selected.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, k] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤ selected.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.entryFacts selected.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp selected.reduced.finalFreePtr k + wordArrayAllocationSize k) k <
        2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.reduced.finalFreePtr k
        selected.entryFacts.divisorBound)
    dsimp only [remFp, k] at hbackend hfinalFree ⊢
    omega
  have hkData : k = (modulusSize + 31) / 32 := by
    rfl
  have hmodulusFits : Model.bytesToNatPadded mem (p + 32) modulusSize ≤
      256 ^ modulusSize :=
    Nat.le_of_lt (model_bytesToNatPadded_lt_pow mem (p + 32) modulusSize)
  have rd := reducedFreshExactReturnVia1271 selected.entryFacts hreduceWorkspace
    selected.reduced selected.constant hconstantAfter hscratch selected.calldataBound
    selected.baseInput_eq selected.modulus_eq valid alignment hexponentFit haccess
    selected.dataLenBound hkData hresultAddr hresultAddr64 hresultMem hsourceActive
    houtBeforeHeader hmodulusFits hresultHeader hdepth
  simpa only [k, remFp, Nat.add_assoc] using rd

/-- Complete a direct selected multi-limb computation to an arbitrary deployed caller
continuation. This is the recursive form used by normalized Barrett, where `retBar` is PC 1808;
the selected steps and gas remain explicit in the resulting `RDx` state. -/
theorem DirectSelection.freshReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat}
    {tail : List UInt256} {exponent result retBar ret : UInt256}
    {exponentSize byteFuel bitFuel callFuel : Nat}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (selected : DirectSelection I g (initState cA gh bl σ σ₀ g A I) rdata acc mem aw
      steps gasUsed p modulusFp modulusSize basePtr baseSize exponent result retBar ret tail)
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (allocatedWords selected.constant.finalWords
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponentSelected)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (allocatedWords selected.constant.finalWords
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponentSelected)
    (access : Modexp.MultiLimbBarrettExponentLoop.BarrettExponentAccessFrame
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))))
    (hresultAddr : result.toNat + 32 + modulusSize < UInt256.size)
    (hresultAddr64 : result.toNat + 32 + modulusSize < 2 ^ 64)
    (hresultMem : result.toNat + 32 + modulusSize ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) + 32 +
      32 * ((modulusSize + 31) / 32) ≤ 32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : result.toNat + 32 + modulusSize ≤
      accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
    (hdepth : tail.length + 43 ≤ 1015)
    (hretBar : (D_J runtimeBytecode 0).contains retBar = true) :
    (RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) retBar
      (result :: ret :: tail)
      (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords
        (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))) result modulusSize)
      exponentSelected.activeWords rdata acc
      (selected.scanSteps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize
          (Modexp.MultiLimbBarrettConversion.words modulusSize) + selected.reduced.stepDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
          selected.reduced.finalMemory selected.reduced.finalWords
          selected.reduced.finalFreePtr (Modexp.MultiLimbBarrettConversion.words modulusSize)
          modulusFp + selected.constant.stepDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionSteps exponentSelected modulusSize)
      (gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
          modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
          (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
          (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
          (directBaseFp modulusFp modulusSize)
          (directRemFp modulusFp modulusSize baseSize) baseSize
          (Modexp.MultiLimbBarrettConversion.words modulusSize) (UInt256.ofNat basePtr) +
        selected.reduced.gasDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
          selected.reduced.finalMemory selected.reduced.finalWords
          selected.reduced.finalFreePtr (Modexp.MultiLimbBarrettConversion.words modulusSize)
          modulusFp + selected.constant.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize) exponent exponentSelected
          modulusSize)) ∧
    Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue
        (Modexp.MultiLimbBarrettConversion.words modulusSize)
        (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponentSelected.memory =
      Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
        Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
          Model.bytesToNatPadded mem (p + 32) modulusSize ∧
    (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords
        (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))) result modulusSize
      ).readWithPadding (result.toNat + 32) modulusSize =
      Model.natToBytes
        (Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded mem (p + 32) modulusSize) modulusSize ∧
    Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
        Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
          Model.bytesToNatPadded mem (p + 32) modulusSize < 256 ^ modulusSize := by
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  have hbackend := selected.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, k] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤ selected.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.entryFacts selected.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp selected.reduced.finalFreePtr k + wordArrayAllocationSize k) k <
        2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.reduced.finalFreePtr k
        selected.entryFacts.divisorBound)
    dsimp only [remFp, k] at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.entryFacts hreduceWorkspace
    selected.reduced selected.constant hconstantAfter hscratch selected.calldataBound
    selected.baseInput_eq selected.modulus_eq
  have hkData : k = (modulusSize + 31) / 32 := rfl
  have haccBound : accumulatorFp selected.reduced.finalFreePtr k +
      wordArrayAllocationSize k < 2 ^ 64 := by
    apply lt_of_le_of_lt (b := Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp selected.reduced.finalFreePtr k + wordArrayAllocationSize k) k)
    · unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
        Modexp.MultiLimbBarrettReusedCall.callResultFp
      omega
    · exact hscratch
  have rd := Selection.freshReturn_of_invariantFramed selected.constant
    selected.entryFacts.divisorTwo selected.entryFacts.divisorBound haccBound
    selected.calldataBound valid invariant alignment access
    selected.dataLenBound hkData hresultAddr hresultMem hsourceActive houtBeforeHeader
    hdepth hretBar
  have haccumulator := reducedFreshAccumulator_eq_modelPowFramed selected.entryFacts
    hreduceWorkspace selected.reduced selected.constant hconstantAfter hscratch
    selected.calldataBound selected.baseInput_eq selected.modulus_eq valid alignment
    access
  have hgeometry :=
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettLoopSetupValid.finalGeometryFramed
      valid invariant alignment access
  have hselectedCovered := hgeometry.1
  have hselectedAwFit := hgeometry.2.1
  have hselectedRawHeader := hgeometry.2.2
  have hpartialOutIn : result.toNat + 64 ≤ exponentSelected.memory.size := by
    have hlarge := selected.dataLenLarge
    exact le_trans (by omega) hresultMem
  have haccFit : accumulatorFp selected.reduced.finalFreePtr k +
      wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : accumulatorFp selected.reduced.finalFreePtr k +
      wordArrayAllocationSize k + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hsourceFit : accumulatorFp selected.reduced.finalFreePtr k + 32 +
      32 * ((modulusSize + 31) / 32) < UInt256.size := by
    have haccFit' := haccFit
    unfold wordArrayAllocationSize wordArrayPayloadSize at haccFit'
    have haccFit'' : accumulatorFp selected.reduced.finalFreePtr k + 32 + 32 * k + 31 <
        UInt256.size := by
      simpa only [Nat.add_assoc] using haccFit'
    have hkEq : k = (modulusSize + 31) / 32 := hkData
    rw [← hkEq]
    exact lt_of_le_of_lt (Nat.le_add_right _ 31) haccFit''
  have haccFpBound : accumulatorFp selected.reduced.finalFreePtr k < 2 ^ 64 := by omega
  have haccNat : (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr k)).toNat =
      accumulatorFp selected.reduced.finalFreePtr k :=
    UInt256.toNat_ofNat_of_lt (lt_trans haccFpBound (by norm_num [UInt256.size]))
  have hselectedHeader : Modexp.MultiLimbLimbsToBytes.headerValue
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr k)) = UInt256.ofNat k := by
    apply Modexp.MultiLimbBarrettResultSemantic.headerValue_eq_of_rawHeader
      exponentSelected.memory exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr k)) k
      hselectedCovered hselectedAwFit
    simpa only [k, haccNat] using hselectedRawHeader
  have hserializer :=
    Modexp.MultiLimbBarrettResultSemantic.serializerValidity_of_geometry
      selected.dataLenBound hkData hresultAddr hresultMem hsourceFit hsourceActive
      hpartialOutIn houtBeforeHeader hselectedCovered hselectedHeader
  have hvalueFit :
      Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded mem (p + 32) modulusSize < 256 ^ modulusSize := by
    exact lt_trans (Nat.mod_lt _ invariant.nPos)
      (model_bytesToNatPadded_lt_pow mem (p + 32) modulusSize)
  have houtForValue : result.toNat + 32 + modulusSize ≤
      accumulatorFp selected.reduced.finalFreePtr k + 32 :=
    le_trans houtBeforeHeader (Nat.le_add_right _ 32)
  have hnumeric := Modexp.MultiLimbBarrettResultSemantic.resultMemory_value_eq
    selected.dataLenBound hkData hresultAddr64 hresultMem hsourceFit
    houtForValue
    hselectedCovered hselectedAwFit hserializer.1 hserializer.2.1 hserializer.2.2
    (by simpa only [k, remFp] using haccumulator) hvalueFit
  have hbytes := Modexp.MultiLimbBarrettResultSemantic.resultMemory_bytes_eq_natToBytes
    hresultAddr64 hnumeric hvalueFit
  constructor
  · simpa only [k, remFp, Nat.add_assoc] using rd
  · constructor
    · simpa only [k, remFp] using haccumulator
    · constructor
      · simpa only [k, remFp] using hbytes
      · exact hvalueFit

end Modexp.MultiLimbBarrettComposition
