import Examples.Precompiles.Modexp.MultiLimbBarrettCorrectionSemantic
import Examples.Precompiles.Modexp.MultiLimbBarrettTruncatedMulSemantic
import Examples.Precompiles.Modexp.MultiLimbBarrettMulSemantic

/-!
# Complete Barrett reduction tail

This module composes the deployed product-minus-r2 loop with the exposed zero/one/two-pass
correction selector.  The selector contains the complete final memory and exact path gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReduction

open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbBarrettCorrection
open Modexp.MultiLimbBarrettCorrectionSemantic
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbBarrettTruncatedMul
open Modexp.MultiLimbBarrettTruncatedMulSemantic
open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbBarrettMulSemantic
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

def subtractionFinal
    (mem : ByteArray) (aw product r2 : UInt256) (kWords : Nat) :
    BarrettSubtractionState :=
  subtractionIterate product r2 (kWords + 1) (subtractionInitialState mem aw)

/-- The executable selector for the complete reduction tail beginning after result allocation. -/
def selectBarrettReductionTail
    (fuel : Nat) (mem : ByteArray) (aw product n r2 result : UInt256)
    (kWords : Nat) : Option BarrettCorrectionSelection :=
  let final := subtractionFinal mem aw product r2 kWords
  selectBarrettCorrection fuel final.memory final.activeWords n r2 result kWords

/-- The subtraction prefix introduces no failure: correction fuel bounded by the limb count makes
the complete reduction-tail selector total. -/
theorem selectBarrettReductionTail_exists
    {fuel kWords : Nat} {mem : ByteArray} {aw product n r2 result : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected,
      selectBarrettReductionTail fuel mem aw product n r2 result kWords = some selected := by
  unfold selectBarrettReductionTail
  exact selectBarrettCorrection_exists hkPos hfuel

/-- Execute every `product-r2` column and the selected correction path through the final dynamic
return jump.  Gas is exact and remains a computation of the selected memory path. -/
theorem selectedBarrettReductionTailExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel kWords : Nat} {tail : List UInt256}
    {product n r2 returnPc result : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (hselect : selectBarrettReductionTail fuel mem aw product n r2 result kWords =
      some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨6696⟩
      (result :: UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords ::
        r2 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial := subtractionInitialState mem aw
    RDx runtimeBytecode ee g s0 ⟨6737⟩
      (returnPc :: result :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 10 + 44 * (kWords + 1) + selected.steps)
      (gasUsed + 31 + subtractionThroughExitGas product r2 kWords initial +
        selected.gas) := by
  let initial := subtractionInitialState mem aw
  let final := subtractionIterate product r2 (kWords + 1) initial
  have rd6940 := subtractionEntryExact hkWord (by omega) h
  have rd6708 := subtractionFromZeroExact hkWord hdepth rd6940
  have hselect' :
      selectBarrettCorrection fuel final.memory final.activeWords n r2 result kWords =
        some selected := by
    simpa only [selectBarrettReductionTail, subtractionFinal, final, initial] using hselect
  have rd6737 := selectedBarrettCorrectionExact selected hkPos hkWord hdepth hselect'
    (by simpa only [final, initial] using rd6708)
  have normalized := rd6737.withIndices
    (k' := steps + 10 + 44 * (kWords + 1) + selected.steps) (by omega)
    (C' := gasUsed + 31 + subtractionThroughExitGas product r2 kWords initial +
      selected.gas) (by simp only [initial])
  simpa only [initial] using normalized

/-- The complete selected reduction tail computes the ordinary remainder from the concrete
product, truncated-product, and modulus windows present after result allocation. -/
theorem selectedBarrettReductionTail_resultValue_eq_mod
    {fuel : Nat} {mem : ByteArray} {aw product n r2 result : UInt256}
    {kWords nValue x : Nat} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hproductFit : product.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hproductMem : product.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hresultMem : result.toNat + 32 ≤ mem.size)
    (hproductBeforeR2 : product.toNat + 32 * (kWords + 2) ≤ r2.toNat)
    (hnBeforeR2 : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hmodulusValue : correctionModulusValue mem n kWords = nValue)
    (hproductValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (product.toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1))
    (hr2Value : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (r2.toNat + 32) (kWords + 1)) =
        (Modexp.barrettQ3 kWords nValue x * nValue) %
          UInt256.size ^ (kWords + 1))
    (hselect : selectBarrettReductionTail fuel mem aw product n r2 result kWords =
      some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory (result.toNat + 32) kWords) =
      x % nValue := by
  let initial := subtractionInitialState mem aw
  let final := subtractionIterate product r2 (kWords + 1) initial
  have hfinalGeometry := subtractionIterate_coverage_size (kWords + 1) product r2 initial
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simpa [initial, subtractionInitialState] using hcovered)
    (by simpa [initial, subtractionInitialState] using hawFit)
  have hcandidate := subtractionFromZero_finalMemory_deployedCandidate
    kWords mem aw product r2 nValue x hkPos hnPos hnNormalized hnFits hx
    hproductFit hr2Fit hproductMem hr2Mem hproductBeforeR2 hcovered hawFit
    hproductValue hr2Value
  have hmodulusFrame := subtractionIterate_memoryWords_below (kWords + 1) product r2
    initial (n.toNat + 32) kWords
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simpa [initial, subtractionInitialState] using hcovered)
    (by simpa [initial, subtractionInitialState] using hawFit)
    (by simp [initial, subtractionInitialState]; omega)
  have hfinalModulus : correctionModulusValue final.memory n kWords = nValue := by
    unfold correctionModulusValue
    rw [show memoryWordsFrom final.memory (n.toNat + 32) kWords =
      memoryWordsFrom mem (n.toNat + 32) kWords by
        simpa only [final] using hmodulusFrame]
    exact hmodulusValue
  have hfinalCandidate : correctionCandidateValue final.memory r2 kWords =
      Modexp.deployedBarrettCandidate kWords nValue x := by
    unfold correctionCandidateValue
    simpa only [final, initial] using hcandidate
  have hselect' : selectBarrettCorrection fuel final.memory final.activeWords n r2 result
      kWords = some selected := by
    simpa only [selectBarrettReductionTail, subtractionFinal, final, initial] using hselect
  apply selectedBarrettCorrection_resultValue_eq_mod hkPos hkShift hr2Fit hnFit
    hresultFit
  · rw [show final.memory.size = mem.size by
      simpa [final, initial, subtractionInitialState] using hfinalGeometry.2.2]
    exact hr2Mem
  · rw [show final.memory.size = mem.size by
      simpa [final, initial, subtractionInitialState] using hfinalGeometry.2.2]
    exact hnMem
  · rw [show final.memory.size = mem.size by
      simpa [final, initial, subtractionInitialState] using hfinalGeometry.2.2]
    exact hresultMem
  · exact hnBeforeR2
  · simpa only [final] using hfinalGeometry.1
  · simpa only [final] using hfinalGeometry.2.1
  · exact hnPos
  · exact hnNormalized
  · exact hx
  · exact hfinalModulus
  · exact hfinalCandidate
  · exact hselect'

/-! ## Truncated-product entry through return -/

def truncatedFinal
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat) : TruncatedOuterState :=
  truncatedRowsIterate q3 n r2 kWords (kWords + 1)
    { i := 0, memory := mem, activeWords := aw }

def selectedResultMemory
    (mem : ByteArray) (aw q3 n r2 : UInt256) (fp kWords : Nat) : ByteArray :=
  resultAllocatedMemory (truncatedFinal mem aw q3 n r2 kWords).memory fp kWords

def selectedResultWords
    (mem : ByteArray) (aw q3 n r2 : UInt256) (fp kWords : Nat) : UInt256 :=
  resultAllocatedWords (truncatedFinal mem aw q3 n r2 kWords).activeWords fp kWords

/-- Executable correction selection for every path from the concrete truncated-product entry. -/
def selectBarrettFromTruncated
    (fuel : Nat) (mem : ByteArray) (aw q3 n r2 product : UInt256)
    (fp kWords : Nat) : Option BarrettCorrectionSelection :=
  selectBarrettReductionTail fuel
    (selectedResultMemory mem aw q3 n r2 fp kWords)
    (selectedResultWords mem aw q3 n r2 fp kWords)
    product n r2 (UInt256.ofNat fp) kWords

/-- Truncated multiplication and result allocation are total computations, so the same correction
fuel bound makes their composed selector total. -/
theorem selectBarrettFromTruncated_exists
    {fuel fp kWords : Nat} {mem : ByteArray} {aw q3 n r2 product : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected,
      selectBarrettFromTruncated fuel mem aw q3 n r2 product fp kWords = some selected := by
  unfold selectBarrettFromTruncated
  exact selectBarrettReductionTail_exists hkPos hfuel

structure TruncatedResultGeometry
    (memory : ByteArray) (activeWords : UInt256) (resultFp : Nat) : Prop where
  covered : MemoryCovered memory activeWords
  activeWordsFit : activeWords.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ memory.size
  memoryLeResult : memory.size ≤ resultFp
  resultGap : resultFp - memory.size < USize.size
  activeWords3 : 3 ≤ activeWords.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ activeWords * ⟨32⟩
  freePointerRead : memory.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat resultFp)

/-- The exact header-only `r2` allocation and every truncated row leave concrete memory inside
the next Solidity allocation boundary. -/
theorem r2Allocated_truncatedResultGeometry
    (mem : ByteArray) (aw q3 n : UInt256) (fp kWords : Nat)
    (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size) :
    let allocatedMemory := r2AllocatedMemory mem fp kWords
    let allocatedWords := r2AllocatedWords aw fp kWords
    let r2 := UInt256.ofNat fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    TruncatedResultGeometry final.memory final.activeWords
      (fp + wordArrayAllocationSize (kWords + 1)) := by
  let allocatedMemory := r2AllocatedMemory mem fp kWords
  let allocatedWords := r2AllocatedWords aw fp kWords
  let r2 := UInt256.ofNat fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  have hfpNat : r2.toNat = fp := by
    simpa only [r2] using r2AllocatedPtr_toNat fp kWords hbound
  have hallocatedCoverage := r2AllocatedMemory_coverage mem aw fp kWords hcovered hawFit
    hmemSize hmemLe hgap hbound
  have hallocatedSize : allocatedMemory.size = fp + 32 := by
    simpa only [allocatedMemory] using
      r2AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hfp : 96 ≤ fp := hmemSize.trans hmemLe
  have hallocatedRead : allocatedMemory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat
        (fp + wordArrayAllocationSize (kWords + 1))) := by
    unfold allocatedMemory r2AllocatedMemory
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 hmemSize
    · rw [setFreePtr_size hmemSize]
      exact hmemSize
    · exact hfp
    · rw [setFreePtr_size hmemSize]
      exact hgap
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hfpNat]
    have h64 : fp + 32 * (kWords + 2) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    exact lt_trans (by omega : fp + 32 * (kWords + 3) < 2 ^ 64 + 32)
      (by decide : 2 ^ 64 + 32 < UInt256.size)
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q initial).i = q := by
    simpa only [initial, Nat.zero_add] using
      truncatedRowsIterate_i q3 n r2 kWords q initial
  have hindices : ∀ q, q < kWords + 1 →
      (truncatedRowsIterate q3 n r2 kWords q initial).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hfinalCoverage := truncatedRows_coverage q3 n r2 kWords (kWords + 1) initial
    hk hindices (by simpa only [initial, allocatedMemory, allocatedWords] using
      hallocatedCoverage.1)
    (by simpa only [initial, allocatedMemory, allocatedWords] using hallocatedCoverage.2)
    hq3Fit hnFit hr2Fit (by simpa only [r2, hfpNat] using hbound)
  have hfinalLe : final.memory.size ≤ fp + wordArrayAllocationSize (kWords + 1) := by
    have hupper := truncatedRows_memory_size_le q3 n r2 kWords (kWords + 1) initial
      hindices (by simpa only [r2, hfpNat] using hbound) (by
        rw [show initial.memory.size = fp + 32 by
          simpa only [initial] using hallocatedSize, hfpNat]
        unfold wordArrayAllocationSize wordArrayPayloadSize
        omega)
    simpa only [final, hfpNat] using hupper
  have hfinalSize : 96 ≤ final.memory.size := by
    have hmono : initial.memory.size ≤ final.memory.size := by
      simpa only [final] using hfinalCoverage.2.2
    rw [show initial.memory.size = fp + 32 by simpa only [initial] using hallocatedSize] at hmono
    omega
  have hfinalCovered : MemoryCovered final.memory final.activeWords := by
    simpa only [final] using hfinalCoverage.1
  have hfinalFit : final.activeWords.toNat * 32 < UInt256.size := by
    simpa only [final] using hfinalCoverage.2.1
  have haw3 : 3 ≤ final.activeWords.toNat := by
    unfold MemoryCovered at hfinalCovered
    omega
  have hmul : (final.activeWords * (⟨32⟩ : UInt256)).toNat =
      final.activeWords.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := final.activeWords) (b := (⟨32⟩ : UInt256)) hfinalFit
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩ := by
    intro hle
    have hnat : (final.activeWords * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hfinalRead : final.memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat
        (fp + wordArrayAllocationSize (kWords + 1))) := by
    have hframe := truncatedRows_read32_below q3 n r2 kWords (kWords + 1) 64 initial
      hk hindices (by
        rw [show initial.memory.size = fp + 32 by simpa only [initial] using hallocatedSize]
        omega)
      (by simpa only [initial, allocatedMemory, allocatedWords] using hallocatedCoverage.1)
      (by simpa only [initial, allocatedMemory, allocatedWords] using hallocatedCoverage.2)
      hq3Fit hnFit hr2Fit (by simpa only [r2, hfpNat] using hbound) (by
        rw [hfpNat]
        omega)
    rw [show final.memory.readWithPadding 64 32 = initial.memory.readWithPadding 64 32 by
      simpa only [final] using hframe]
    simpa only [initial] using hallocatedRead
  refine ⟨hfinalCovered, hfinalFit, hfinalSize, hfinalLe, ?_, haw3, haw64, hfinalRead⟩
  · rw [show USize.size = 2 ^ 64 by native_decide]
    apply lt_of_le_of_lt (Nat.sub_le _ _)
    exact hbound

/-- Execute the defensive q3 cap, every selected truncated row, result allocation, all candidate
subtraction columns, and the selected correction path through the return jump. -/
theorem selectedBarrettFromTruncatedExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q3 n r2 returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kWords < 2 ^ 64)
    (hmemSize : 96 ≤ (truncatedFinal mem aw q3 n r2 kWords).memory.size)
    (hmemLe : (truncatedFinal mem aw q3 n r2 kWords).memory.size ≤ fp)
    (hgap : fp - (truncatedFinal mem aw q3 n r2 kWords).memory.size < USize.size)
    (haw3 : 3 ≤ (truncatedFinal mem aw q3 n r2 kWords).activeWords.toNat)
    (haw64 : ¬(⟨64⟩ : UInt256) ≥
      (truncatedFinal mem aw q3 n r2 kWords).activeWords * ⟨32⟩)
    (hread : (truncatedFinal mem aw q3 n r2 kWords).memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 13 ≤ 1016)
    (hselect : selectBarrettFromTruncated fuel mem aw q3 n r2 product fp kWords =
      some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6666⟩
      (r2 :: UInt256.ofNat (kWords + 3) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory fp kWords
    let resultAw := resultAllocatedWords final.activeWords fp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat fp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 116 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 126 + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords fp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  have hkWord : kWords + 1 < UInt256.size :=
    (show kWords + 1 < 2 ^ 64 by omega).trans (by decide)
  have hkCap : kWords + 3 < UInt256.size :=
    (show kWords + 3 < 2 ^ 64 by omega).trans (by decide)
  let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory fp kWords
  let resultAw := resultAllocatedWords final.activeWords fp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have rd6677 := truncatedEntryExact hkCap hdepth h
  have rd6685 := truncatedRowsFromZeroExitExact hkPos hkWord hdepth
    (by simpa only [initial, truncatedOuterStack] using rd6677)
  dsimp only at rd6685
  have rd6696 := resultAllocationExact (fp := fp) (kWords := kWords) (tail := tail)
    (i := UInt256.ofNat final.i) (q3 := q3)
    (q3Cap := UInt256.ofNat (kWords + 1)) (rLen := UInt256.ofNat (kWords + 1))
    (n := n) (r2 := r2) (returnPc := returnPc) (product := product)
    (by omega) hfp hbound
    (by simpa only [final, initial, truncatedFinal] using hmemSize)
    (by simpa only [final, initial, truncatedFinal] using hmemLe)
    (by simpa only [final, initial, truncatedFinal] using hgap)
    (by simpa only [final, initial, truncatedFinal] using haw3)
    (by simpa only [final, initial, truncatedFinal] using haw64)
    (by simpa only [final, initial, truncatedFinal] using hread)
    hcalldata (by omega) (by simpa only [final, initial, truncatedOuterStack] using rd6685)
  have hselect' : selectBarrettReductionTail fuel resultMem resultAw product n r2
      (UInt256.ofNat fp) kWords = some selected := by
    simpa only [selectBarrettFromTruncated, selectedResultMemory, selectedResultWords,
      truncatedFinal, final, initial, resultMem, resultAw] using hselect
  have rd6737 := selectedBarrettReductionTailExact (tail := tail) (product := product)
    (n := n) (r2 := r2) (returnPc := returnPc) (result := UInt256.ofNat fp)
    selected hkPos hkWord (by omega)
    hselect' (by simpa only [resultMem, resultAw] using rd6696)
  have normalized := rd6737.withIndices
    (k' := steps + 116 +
      truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by
        simp only [initial]
        omega)
    (C' := gasUsed + 126 +
      truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords fp kWords +
      subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) (by
        simp only [subtractionInitial, resultMem, resultAw, final, initial]
        omega)
  simpa only [initial, final, resultMem, resultAw, subtractionInitial] using normalized

/-- Specialize the PC 6666 execution theorem to the literal state returned by `r2AllocationExact`.
All following result-allocation premises are discharged by the concrete truncated-row geometry. -/
theorem selectedBarrettFromAllocatedR2Exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q3 n returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hr2Bound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 13 ≤ 1016)
    (hselect : selectBarrettFromTruncated fuel
      (r2AllocatedMemory mem fp kWords) (r2AllocatedWords aw fp kWords)
      q3 n (UInt256.ofNat fp) product
      (fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6666⟩
      (UInt256.ofNat fp :: UInt256.ofNat (kWords + 3) :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      (r2AllocatedMemory mem fp kWords) (r2AllocatedWords aw fp kWords)
      rdata acc steps gasUsed) :
    let allocatedMemory := r2AllocatedMemory mem fp kWords
    let allocatedWords := r2AllocatedWords aw fp kWords
    let r2 := UInt256.ofNat fp
    let resultFp := fp + wordArrayAllocationSize (kWords + 1)
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory resultFp kWords
    let resultAw := resultAllocatedWords final.activeWords resultFp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat resultFp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 116 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 126 + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords resultFp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  let allocatedMemory := r2AllocatedMemory mem fp kWords
  let allocatedWords := r2AllocatedWords aw fp kWords
  let r2 := UInt256.ofNat fp
  let resultFp := fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have hgeometry := r2Allocated_truncatedResultGeometry mem aw q3 n fp kWords hk
    hcovered hawFit hmemSize hmemLe hgap hr2Bound hq3Fit hnFit
  have hresultFp : 96 ≤ resultFp := by
    dsimp only [resultFp]
    omega
  have rd := selectedBarrettFromTruncatedExact (tail := tail) (q3 := q3) (n := n)
    (r2 := r2) (returnPc := returnPc) (product := product) selected hkPos hk hresultFp
    (by simpa only [resultFp] using hresultBound)
    (by simpa only [allocatedMemory, allocatedWords, r2, initial, final, resultFp] using
      hgeometry.memorySize96)
    (by simpa only [allocatedMemory, allocatedWords, r2, initial, final, resultFp] using
      hgeometry.memoryLeResult)
    (by simpa only [allocatedMemory, allocatedWords, r2, initial, final, resultFp] using
      hgeometry.resultGap)
    (by simpa only [allocatedMemory, allocatedWords, r2, initial, final, resultFp] using
      hgeometry.activeWords3)
    (by simpa only [allocatedMemory, allocatedWords, r2, initial, final, resultFp] using
      hgeometry.activeWords64)
    (by simpa only [allocatedMemory, allocatedWords, r2, initial, final, resultFp] using
      hgeometry.freePointerRead)
    hcalldata hdepth (by simpa only [allocatedMemory, allocatedWords, r2, resultFp] using hselect)
    (by simpa only [allocatedMemory, allocatedWords, r2] using h)
  simpa only [allocatedMemory, allocatedWords, r2, resultFp, initial, final, resultMem,
    resultAw, subtractionInitial] using rd

/-- Execute the real `r2` allocation and the complete selected Barrett reduction through return. -/
theorem selectedBarrettFromR2AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q3 n returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hfp : 96 ≤ fp)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hr2Bound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 13 ≤ 1016)
    (hselect : selectBarrettFromTruncated fuel
      (r2AllocatedMemory mem fp kWords) (r2AllocatedWords aw fp kWords)
      q3 n (UInt256.ofNat fp) product
      (fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6656⟩
      (UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let allocatedMemory := r2AllocatedMemory mem fp kWords
    let allocatedWords := r2AllocatedWords aw fp kWords
    let r2 := UInt256.ofNat fp
    let resultFp := fp + wordArrayAllocationSize (kWords + 1)
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory resultFp kWords
    let resultAw := resultAllocatedWords final.activeWords resultFp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat resultFp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 200 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 147 + newWordArrayGas aw fp (kWords + 1) +
        truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords resultFp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  let allocatedMemory := r2AllocatedMemory mem fp kWords
  let allocatedWords := r2AllocatedWords aw fp kWords
  let r2 := UInt256.ofNat fp
  let resultFp := fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have rd6666 := r2AllocationExact (tail := tail) (q3 := q3) (n := n)
    (returnPc := returnPc) (product := product) (by omega) hfp hr2Bound hmemSize hmemLe
    hgap haw3 haw64 hread hcalldata (by omega) h
  have rd6737 := selectedBarrettFromAllocatedR2Exact (tail := tail) selected hkPos hk
    hcovered hawFit hmemSize hmemLe hgap hr2Bound hresultBound hq3Fit hnFit hcalldata
    hdepth hselect (by simpa only [allocatedMemory, allocatedWords] using rd6666)
  have normalized := rd6737.withIndices
    (k' := steps + 200 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by
        simp only [r2, initial, allocatedMemory, allocatedWords])
    (C' := gasUsed + 147 + newWordArrayGas aw fp (kWords + 1) +
      truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords resultFp kWords +
      subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) (by
        simp only [r2, resultFp, initial, final, allocatedMemory, allocatedWords,
          resultMem, resultAw, subtractionInitial]
        omega)
  simpa only [allocatedMemory, allocatedWords, r2, resultFp, initial, final, resultMem,
    resultAw, subtractionInitial] using normalized

/-- Execute the concrete q3 `MCOPY`, `r2` allocation, truncated product, subtraction, and selected
correction path through return. -/
theorem selectedBarrettFromQ3CopyExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q3 q2 n returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hfp : 96 ≤ fp)
    (hcovered : MemoryCovered (q3CopiedMemory mem q3 q2 kWords)
      (q3CopiedWords aw q3 q2 kWords))
    (hawFit : (q3CopiedWords aw q3 q2 kWords).toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ (q3CopiedMemory mem q3 q2 kWords).size)
    (hmemLe : (q3CopiedMemory mem q3 q2 kWords).size ≤ fp)
    (hgap : fp - (q3CopiedMemory mem q3 q2 kWords).size < USize.size)
    (haw3 : 3 ≤ (q3CopiedWords aw q3 q2 kWords).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ q3CopiedWords aw q3 q2 kWords * ⟨32⟩)
    (hread : (q3CopiedMemory mem q3 q2 kWords).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hr2Bound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 13 ≤ 1016)
    (hselect : selectBarrettFromTruncated fuel
      (r2AllocatedMemory (q3CopiedMemory mem q3 q2 kWords) fp kWords)
      (r2AllocatedWords (q3CopiedWords aw q3 q2 kWords) fp kWords)
      q3 n (UInt256.ofNat fp) product
      (fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6626⟩
      (UInt256.ofNat (kWords + 3) :: q2 :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let copiedMem := q3CopiedMemory mem q3 q2 kWords
    let copiedAw := q3CopiedWords aw q3 q2 kWords
    let allocatedMemory := r2AllocatedMemory copiedMem fp kWords
    let allocatedWords := r2AllocatedWords copiedAw fp kWords
    let r2 := UInt256.ofNat fp
    let resultFp := fp + wordArrayAllocationSize (kWords + 1)
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory resultFp kWords
    let resultAw := resultAllocatedWords final.activeWords resultFp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat resultFp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 232 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + q3CopyGas aw q3 q2 kWords + 147 +
        newWordArrayGas copiedAw fp (kWords + 1) +
        truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords resultFp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  let copiedMem := q3CopiedMemory mem q3 q2 kWords
  let copiedAw := q3CopiedWords aw q3 q2 kWords
  let allocatedMemory := r2AllocatedMemory copiedMem fp kWords
  let allocatedWords := r2AllocatedWords copiedAw fp kWords
  let r2 := UInt256.ofNat fp
  let resultFp := fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have hkWord : kWords + 1 < UInt256.size :=
    (show kWords + 1 < 2 ^ 64 by omega).trans (by decide)
  have rd6656 := q3CopyAndRLenExact (tail := tail) hkWord (by omega) h
  have rd6737 := selectedBarrettFromR2AllocationExact (tail := tail) selected hkPos hk hfp
    hcovered hawFit hmemSize hmemLe hgap haw3 haw64 hread hr2Bound hresultBound
    hq3Fit hnFit hcalldata hdepth hselect
    (by simpa only [copiedMem, copiedAw] using rd6656)
  have normalized := rd6737.withIndices
    (k' := steps + 232 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by
        simp only [copiedMem, copiedAw, allocatedMemory, allocatedWords, r2, initial])
    (C' := gasUsed + q3CopyGas aw q3 q2 kWords + 147 +
      newWordArrayGas copiedAw fp (kWords + 1) +
      truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords resultFp kWords +
      subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) (by
        simp only [copiedMem, copiedAw, allocatedMemory, allocatedWords, r2, resultFp,
          initial, final, resultMem, resultAw, subtractionInitial])
  simpa only [copiedMem, copiedAw, allocatedMemory, allocatedWords, r2, resultFp,
    initial, final, resultMem, resultAw, subtractionInitial] using normalized

/-- Execute q3's allocation, slice copy, and the complete selected Barrett reduction through
return.  All memory geometry required by the r2 allocator is derived from the concrete q3
allocator and `MCOPY`. -/
theorem selectedBarrettFromQ3AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hfp : 96 ≤ fp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hq3Bound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hr2Bound : fp + wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) + wordArrayAllocationSize kWords < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hq2Source : q2.toNat + 32 * (2 * kWords + 5) ≤ fp + 32)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 13 ≤ 1016)
    (hselect : selectBarrettFromTruncated fuel
      (r2AllocatedMemory
        (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords)
        (fp + wordArrayAllocationSize (kWords + 3)) kWords)
      (r2AllocatedWords
        (q3CopiedWords (q3AllocatedWords aw fp kWords) (UInt256.ofNat fp) q2 kWords)
        (fp + wordArrayAllocationSize (kWords + 3)) kWords)
      (UInt256.ofNat fp) n
      (UInt256.ofNat (fp + wordArrayAllocationSize (kWords + 3))) product
      (fp + wordArrayAllocationSize (kWords + 3) +
        wordArrayAllocationSize (kWords + 1)) kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6530⟩
      (q2 :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let q3Mem := q3AllocatedMemory mem fp kWords
    let q3Aw := q3AllocatedWords aw fp kWords
    let q3 := UInt256.ofNat fp
    let r2Fp := fp + wordArrayAllocationSize (kWords + 3)
    let copiedMem := q3CopiedMemory q3Mem q3 q2 kWords
    let copiedAw := q3CopiedWords q3Aw q3 q2 kWords
    let allocatedMemory := r2AllocatedMemory copiedMem r2Fp kWords
    let allocatedWords := r2AllocatedWords copiedAw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory resultFp kWords
    let resultAw := resultAllocatedWords final.activeWords resultFp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat resultFp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 447 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 669 + newWordArrayGas aw fp (kWords + 3) +
        q3CopyGas q3Aw q3 q2 kWords + newWordArrayGas copiedAw r2Fp (kWords + 1) +
        truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords resultFp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  let q3Mem := q3AllocatedMemory mem fp kWords
  let q3Aw := q3AllocatedWords aw fp kWords
  let q3 := UInt256.ofNat fp
  let r2Fp := fp + wordArrayAllocationSize (kWords + 3)
  let copiedMem := q3CopiedMemory q3Mem q3 q2 kWords
  let copiedAw := q3CopiedWords q3Aw q3 q2 kWords
  let allocatedMemory := r2AllocatedMemory copiedMem r2Fp kWords
  let allocatedWords := r2AllocatedWords copiedAw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have hcopiedCoverage := q3CopiedMemory_coverage mem aw q2 fp kWords hawFit hmemSize
    hmemLe hgap hq3Bound hq2Fit hq2Source
  have hcopiedSize := q3CopiedMemory_size mem q2 fp kWords hmemSize hmemLe hgap
    hq3Bound hq2Fit hq2Source
  have hcopiedRead : copiedMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat r2Fp) := by
    have hframe := q3CopiedMemory_read64 mem q2 fp kWords hmemSize hmemLe hgap
      hq3Bound hq2Fit hq2Source
    rw [hframe]
    exact q3AllocatedMemory_read64 mem fp kWords hmemSize hmemLe hgap
  have hcopied3 : 3 ≤ copiedAw.toNat := by
    have hrange := q3CopiedWords_range aw q2 fp kWords hawFit hq3Bound hq2Fit hq2Source
    have : 96 ≤ fp + wordArrayAllocationSize (kWords + 3) := by omega
    dsimp only [copiedAw, q3Aw, q3, r2Fp]
    omega
  have hcopied64 : ¬ (⟨64⟩ : UInt256) ≥ copiedAw * ⟨32⟩ := by
    have hmul : (copiedAw * (⟨32⟩ : UInt256)).toNat = copiedAw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := copiedAw) (b := (⟨32⟩ : UInt256))
          (by simpa only [copiedAw, q3Aw, q3] using hcopiedCoverage.2)
    intro hge
    have hgeNat : (copiedAw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa using hge
    rw [hmul] at hgeNat
    omega
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [show q3.toNat = fp by simpa only [q3] using q3AllocatedPtr_toNat fp kWords hq3Bound]
    have hbound := hq3Bound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    exact lt_trans (by omega : fp + 32 * (kWords + 3) < 2 ^ 64) (by decide)
  have rd6582 := q3AllocationExact (tail := tail) hkPos (by omega) hfp hq3Bound hmemSize
    hmemLe hgap haw3 haw64 hread hcalldata (by omega) h
  have rd6626 := q3CopySetupExact (tail := tail) hkPos (by omega) (by omega)
    (by simpa only [q3Mem, q3Aw, q3] using rd6582)
  have rd6737 := selectedBarrettFromQ3CopyExact (tail := tail) selected hkPos hk
    (fp := r2Fp) (q3 := q3) (q2 := q2) (n := n) (returnPc := returnPc)
    (product := product)
    (by omega)
    (by simpa only [copiedMem, copiedAw, q3Mem, q3Aw, q3] using hcopiedCoverage.1)
    (by simpa only [copiedAw, q3Aw, q3] using hcopiedCoverage.2)
    (by rw [show copiedMem.size = r2Fp by
      simpa only [copiedMem, q3Mem, q3, r2Fp] using hcopiedSize]; omega)
    (by simpa only [copiedMem, q3Mem, q3, r2Fp] using hcopiedSize.le)
    (by rw [show copiedMem.size = r2Fp by
      simpa only [copiedMem, q3Mem, q3, r2Fp] using hcopiedSize]; omega)
    hcopied3 hcopied64 hcopiedRead
    (by simpa only [r2Fp, Nat.add_assoc] using hr2Bound)
    (by simpa only [r2Fp, Nat.add_assoc] using hresultBound)
    hq3Fit hnFit hcalldata hdepth
    (by simpa only [copiedMem, copiedAw, allocatedMemory, allocatedWords, q3Mem, q3Aw,
      q3, r2Fp, r2, resultFp] using hselect)
    (by simpa only [q3Mem, q3Aw, q3] using rd6626)
  have normalized := rd6737.withIndices
    (k' := steps + 447 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by
        simp only [q3Mem, q3Aw, q3, r2Fp, copiedMem, copiedAw, allocatedMemory,
          allocatedWords, r2, initial])
    (C' := gasUsed + 669 + newWordArrayGas aw fp (kWords + 3) +
      q3CopyGas q3Aw q3 q2 kWords + newWordArrayGas copiedAw r2Fp (kWords + 1) +
      truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords resultFp kWords +
      subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) (by
        simp only [q3Mem, q3Aw, q3, r2Fp, copiedMem, copiedAw, allocatedMemory,
          allocatedWords, r2, resultFp, initial, final, resultMem, resultAw,
          subtractionInitial]
        omega)
  simpa only [q3Mem, q3Aw, q3, r2Fp, copiedMem, copiedAw, allocatedMemory,
    allocatedWords, r2, resultFp, initial, final, resultMem, resultAw,
    subtractionInitial] using normalized

/-- Execute the actual q1 slice and complete `q1*mu` product before the q3 allocation and full
selected Barrett reduction.  The second product's allocator geometry is derived from its row
execution rather than assumed at PC 6530. -/
theorem selectedBarrettFromQ1ProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hmuInMemory : mu.toNat < (q1CopiedMemory mem q1 product kWords).size)
    (hmuActive : ¬ mu ≥ q1CopiedWords aw q1 product kWords * ⟨32⟩)
    (hmuHeader : (q1CopiedMemory mem q1 product kWords).readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2)))
    (hfp : 96 ≤ fp)
    (hsecondCovered : MemoryCovered (q1CopiedMemory mem q1 product kWords)
      (q1LoadedWords aw q1 product mu kWords))
    (hsecondAwFit : (q1LoadedWords aw q1 product mu kWords).toNat * 32 < UInt256.size)
    (hsecondMemSize : 96 ≤ (q1CopiedMemory mem q1 product kWords).size)
    (hsecondMemLe : (q1CopiedMemory mem q1 product kWords).size ≤ fp)
    (hsecondGap : fp - (q1CopiedMemory mem q1 product kWords).size < USize.size)
    (hsecondAw3 : 3 ≤ (q1LoadedWords aw q1 product mu kWords).toNat)
    (hsecondAw64 : ¬ (⟨64⟩ : UInt256) ≥
      q1LoadedWords aw q1 product mu kWords * ⟨32⟩)
    (hsecondRead : (q1CopiedMemory mem q1 product kWords).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hq1End : q1.toNat + 32 * (kWords + 3) ≤ fp)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp)
    (hsecondBound : fp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq3Bound : fp + wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hr2Bound : fp + wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) + wordArrayAllocationSize (kWords + 1) <
        2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) + wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 17 ≤ 1016)
    (hselect :
      let copiedMem := q1CopiedMemory mem q1 product kWords
      let copiedAw := q1LoadedWords aw q1 product mu kWords
      let q2Final := secondProductFinal copiedMem copiedAw q1 mu fp kWords
      let q3Fp := fp + wordArrayAllocationSize (2 * kWords + 4)
      let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
      let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
      let q3 := UInt256.ofNat q3Fp
      let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
      selectBarrettFromTruncated fuel
        (r2AllocatedMemory (q3CopiedMemory q3Mem q3 (UInt256.ofNat fp) kWords)
          r2Fp kWords)
        (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat fp) kWords)
          r2Fp kWords)
        q3 n (UInt256.ofNat r2Fp) product
        (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6490⟩
      (q1 :: mu :: ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let copiedMem := q1CopiedMemory mem q1 product kWords
    let copiedAw := q1LoadedWords aw q1 product mu kWords
    let q2Initial := secondProductInitial copiedMem copiedAw fp kWords
    let q2Final := secondProductFinal copiedMem copiedAw q1 mu fp kWords
    let q3Fp := fp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat fp) kWords
    let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat fp) kWords
    let allocatedMemory := r2AllocatedMemory q3CopiedMem r2Fp kWords
    let allocatedWords := r2AllocatedWords q3CopiedAw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory resultFp kWords
    let resultAw := resultAllocatedWords final.activeWords resultFp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat resultFp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 604 + rowsSteps q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2)
          q2Initial + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 865 + q1SliceGas aw q1 product mu kWords +
        newWordArrayGas copiedAw fp (2 * kWords + 4) +
        rowsGas q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) q2Initial +
        newWordArrayGas q2Final.activeWords q3Fp (kWords + 3) +
        q3CopyGas q3Aw q3 (UInt256.ofNat fp) kWords +
        newWordArrayGas q3CopiedAw r2Fp (kWords + 1) +
        truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords resultFp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  let copiedMem := q1CopiedMemory mem q1 product kWords
  let copiedAw := q1LoadedWords aw q1 product mu kWords
  let q2Initial := secondProductInitial copiedMem copiedAw fp kWords
  let q2Final := secondProductFinal copiedMem copiedAw q1 mu fp kWords
  let q3Fp := fp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat fp) kWords
  let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat fp) kWords
  let allocatedMemory := r2AllocatedMemory q3CopiedMem r2Fp kWords
  let allocatedWords := r2AllocatedWords q3CopiedAw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have hgeometry := secondProductFinal_geometry copiedMem copiedAw q1 mu fp kWords
    (by omega) (by simpa only [copiedMem, copiedAw] using hsecondCovered)
    (by simpa only [copiedAw] using hsecondAwFit) hsecondMemSize hsecondMemLe hsecondGap
    hsecondBound hq1End hmuEnd
  have hq2Nat : (UInt256.ofNat fp).toNat = fp := by
    exact functionResultPtr_toNat fp (2 * kWords + 4) hsecondBound
  have hq2Fit : (UInt256.ofNat fp).toNat + 32 * (kWords + 2) < UInt256.size := by
    rw [hq2Nat]
    have hbound := hsecondBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    exact lt_trans (by omega : fp + 32 * (kWords + 2) < 2 ^ 64) (by decide)
  have hq2Source : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 5) ≤ q3Fp + 32 := by
    rw [hq2Nat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have rd6530 := q1ProductExact (tail := tail) (by omega) (by omega) hmuInMemory
    hmuActive hmuHeader hfp hsecondBound hsecondMemSize hsecondMemLe hsecondGap
    hsecondAw3 hsecondAw64 hsecondRead hcalldata hdepth h
  have rd6737 := selectedBarrettFromQ3AllocationExact (tail := tail) selected hkPos hk
    (fp := q3Fp) (q2 := UInt256.ofNat fp) (n := n) (returnPc := returnPc)
    (product := product)
    (by omega)
    (by simpa only [q2Final] using hgeometry.activeWordsFit)
    (by simpa only [q2Final] using hgeometry.memorySize96)
    (by simpa only [q2Final, q3Fp] using hgeometry.memoryLeNext)
    (by simpa only [q2Final, q3Fp] using hgeometry.nextGap)
    (by simpa only [q2Final] using hgeometry.activeWords3)
    (by simpa only [q2Final] using hgeometry.activeWords64)
    (by simpa only [q2Final, q3Fp] using hgeometry.freePointerRead)
    (by simpa only [q3Fp, Nat.add_assoc] using hq3Bound)
    (by simpa only [q3Fp, Nat.add_assoc] using hr2Bound)
    (by simpa only [q3Fp, Nat.add_assoc] using hresultBound)
    hq2Fit hq2Source hnFit hcalldata (by omega)
    (by simpa only [copiedMem, copiedAw, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp]
      using hselect)
    (by simpa only [copiedMem, copiedAw, q2Final] using rd6530)
  have normalized := rd6737.withIndices
    (k' := steps + 604 + rowsSteps q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2)
      q2Initial + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by
        simp only [copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3,
          r2Fp, q3CopiedMem, q3CopiedAw, allocatedMemory, allocatedWords, r2, initial]
        omega)
    (C' := gasUsed + 865 + q1SliceGas aw q1 product mu kWords +
      newWordArrayGas copiedAw fp (2 * kWords + 4) +
      rowsGas q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) q2Initial +
      newWordArrayGas q2Final.activeWords q3Fp (kWords + 3) +
      q3CopyGas q3Aw q3 (UInt256.ofNat fp) kWords +
      newWordArrayGas q3CopiedAw r2Fp (kWords + 1) +
      truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords resultFp kWords +
      subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) (by
        simp only [copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3,
          r2Fp, q3CopiedMem, q3CopiedAw, allocatedMemory, allocatedWords, r2, resultFp,
          initial, final, resultMem, resultAw, subtractionInitial]
        omega)
  simpa only [copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3,
    r2Fp, q3CopiedMem, q3CopiedAw, allocatedMemory, allocatedWords, r2, resultFp,
    initial, final, resultMem, resultAw, subtractionInitial] using normalized

/-- Exact Barrett execution from the first `a*b` call through the exposed correction selector.
All allocator, copy, and second-product premises are derived from the initial memory geometry. -/
theorem selectedBarrettFromFirstProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {a b n mu returnPc : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp)
    (hmuBase : 96 ≤ mu.toNat)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp)
    (hmuHeader : mem.readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2)))
    (hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) + wordArrayAllocationSize kWords < 2 ^ 64)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 17 ≤ 1016)
    (hselect :
      let firstFinal := firstProductFinal mem aw a b fp kWords
      let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
      let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
      let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
      let q1 := UInt256.ofNat q1Fp
      let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
      let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
      let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
      let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
      let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
      let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
      let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
      let q3 := UInt256.ofNat q3Fp
      let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
      selectBarrettFromTruncated fuel
        (r2AllocatedMemory (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        q3 n (UInt256.ofNat r2Fp) (UInt256.ofNat fp)
        (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    let firstInitial := firstProductInitial mem aw fp kWords
    let firstFinal := firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
    let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let q2Initial := secondProductInitial copiedMem copiedAw secondFp kWords
    let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let allocatedMemory := r2AllocatedMemory q3CopiedMem r2Fp kWords
    let allocatedWords := r2AllocatedWords q3CopiedAw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory resultFp kWords
    let resultAw := resultAllocatedWords final.activeWords resultFp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat resultFp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 837 + rowsSteps a b (UInt256.ofNat fp) kWords kWords firstInitial +
        rowsSteps q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
        truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 1133 + newWordArrayGas aw fp (2 * kWords) +
        rowsGas a b (UInt256.ofNat fp) kWords kWords firstInitial +
        newWordArrayGas firstFinal.activeWords q1Fp (kWords + 2) +
        q1SliceGas q1Aw q1 (UInt256.ofNat fp) mu kWords +
        newWordArrayGas copiedAw secondFp (2 * kWords + 4) +
        rowsGas q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
        newWordArrayGas q2Final.activeWords q3Fp (kWords + 3) +
        q3CopyGas q3Aw q3 (UInt256.ofNat secondFp) kWords +
        newWordArrayGas q3CopiedAw r2Fp (kWords + 1) +
        truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords resultFp kWords +
        subtractionThroughExitGas (UInt256.ofNat fp) r2 kWords subtractionInitial +
        selected.gas) := by
  let firstInitial := firstProductInitial mem aw fp kWords
  let firstFinal := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Initial := secondProductInitial copiedMem copiedAw secondFp kWords
  let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let allocatedMemory := r2AllocatedMemory q3CopiedMem r2Fp kWords
  let allocatedWords := r2AllocatedWords q3CopiedAw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have hfirstGeometry := firstProductFinal_geometry mem aw a b fp kWords (by omega)
    hcovered hawFit hmemSize hmemLe hgap hfirstBound haEnd hbEnd
  have hproductNat : (UInt256.ofNat fp).toNat = fp :=
    functionResultPtr_toNat fp (2 * kWords) hfirstBound
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hproductNat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstBound
      omega : fp + 32 * kWords < 2 ^ 64) (by decide)
  have hsource : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp + 32 := by
    rw [hproductNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Geometry := q1Slice_geometry firstFinal.memory firstFinal.activeWords
    (UInt256.ofNat fp) mu q1Fp kWords hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.activeWordsFit)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hsource (by omega)
  have hfirstMu := firstProductFinal_read32_below mem aw a b fp kWords mu.toNat
    (by omega) hcovered hawFit hmemSize hmemLe hgap hfirstBound haEnd hbEnd hmuBase
    (by omega)
  have hcopiedMu := q1CopiedMemory_read_below firstFinal.memory (UInt256.ofNat fp)
    q1Fp kWords mu.toNat hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hsource hmuBase (by omega)
  have hcopiedMuHeader : copiedMem.readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2)) := by
    have hcopiedFrame : copiedMem.readWithPadding mu.toNat 32 =
        firstFinal.memory.readWithPadding mu.toNat 32 := by
      simpa only [copiedMem, q1Mem, q1, firstFinal] using hcopiedMu
    exact hcopiedFrame.trans (hfirstMu.trans hmuHeader)
  have rd6468 := firstProductExact (tail := tail) hkPos (by omega) (by omega)
    hfirstBound hmemSize hmemLe hgap haw3 haw64 hread hcalldata (by omega) h
  have rd6490 := q1AllocationExact (tail := tail) (fp := q1Fp)
    (mem := firstFinal.memory) (aw := firstFinal.activeWords)
    (product := UInt256.ofNat fp) (kWords := kWords) (by omega)
    (by
      have hle := hfirstGeometry.memoryLeNext
      have hbase := hfirstGeometry.memorySize96
      dsimp only [firstFinal, q1Fp] at hle hbase ⊢
      omega)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [firstFinal] using hfirstGeometry.activeWords3)
    (by simpa only [firstFinal] using hfirstGeometry.activeWords64)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.freePointerRead)
    hcalldata (by omega) (by simpa only [firstFinal] using rd6468)
  have rd6737 := selectedBarrettFromQ1ProductExact (tail := tail) (mem := q1Mem)
    (aw := q1Aw) (fp := secondFp) (kWords := kWords) (fuel := fuel)
    (q1 := q1) (mu := mu) (n := n) (returnPc := returnPc)
    (product := UInt256.ofNat fp) selected hkPos hk
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.muInMemory)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.muActive)
    hcopiedMuHeader
    (by
      have hbase := hq1Geometry.memorySize96
      have hle := hq1Geometry.memoryLeNext
      simp only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] at hbase hle ⊢
      omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWords3)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWords64)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.freePointerRead)
    (by
      dsimp only [q1, secondFp, q1Fp]
      rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
          (by decide))]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by
      dsimp only [secondFp, q1Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hr2Bound)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hresultBound)
    hnFit hcalldata (by omega)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp, copiedMem, copiedAw,
      q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp] using hselect)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1] using rd6490)
  have normalized := rd6737.withIndices
    (k' := steps + 837 + rowsSteps a b (UInt256.ofNat fp) kWords kWords firstInitial +
      rowsSteps q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
      truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by
        simp only [firstInitial, firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp,
          copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp,
          q3CopiedMem, q3CopiedAw, allocatedMemory, allocatedWords, r2, initial]
        omega)
    (C' := gasUsed + 1133 + newWordArrayGas aw fp (2 * kWords) +
      rowsGas a b (UInt256.ofNat fp) kWords kWords firstInitial +
      newWordArrayGas firstFinal.activeWords q1Fp (kWords + 2) +
      q1SliceGas q1Aw q1 (UInt256.ofNat fp) mu kWords +
      newWordArrayGas copiedAw secondFp (2 * kWords + 4) +
      rowsGas q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
      newWordArrayGas q2Final.activeWords q3Fp (kWords + 3) +
      q3CopyGas q3Aw q3 (UInt256.ofNat secondFp) kWords +
      newWordArrayGas q3CopiedAw r2Fp (kWords + 1) +
      truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords resultFp kWords +
      subtractionThroughExitGas (UInt256.ofNat fp) r2 kWords subtractionInitial +
      selected.gas) (by
        simp only [firstInitial, firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp,
          copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp,
          q3CopiedMem, q3CopiedAw, allocatedMemory, allocatedWords, r2, resultFp,
          initial, final, resultMem, resultAw, subtractionInitial]
        omega)
  simpa only [firstInitial, firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp,
    copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp,
    q3CopiedMem, q3CopiedAw, allocatedMemory, allocatedWords, r2, resultFp,
    initial, final, resultMem, resultAw, subtractionInitial] using normalized

/-- The selected execution from the truncated-product entry returns the pure Barrett remainder.
The `r2` premise consumed by the reduction tail is derived from the concrete outer multiplication
over the copied q3 and modulus arrays. -/
theorem selectedBarrettFromTruncated_resultValue_eq_mod
    {fuel fp kWords nValue x : Nat} {mem : ByteArray}
    {aw q3 n r2 product : UInt256} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hk : kWords ≤ 32) (hkShift : kWords < 2 ^ 251)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbase : 96 ≤ mem.size)
    (hfresh : mem.size ≤ r2.toNat + 32)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hproductFit : product.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize kWords < 2 ^ 64)
    (hproductBase : 96 ≤ product.toNat + 32)
    (hnBase : 96 ≤ n.toNat + 32)
    (hr2Base : 96 ≤ r2.toNat + 32)
    (hq3Before : q3.toNat + 32 * (kWords + 2) ≤ r2.toNat + 32)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hproductBefore : product.toNat + 32 * (kWords + 2) ≤ r2.toNat)
    (hr2BeforeResult : r2.toNat + wordArrayAllocationSize (kWords + 1) ≤ fp)
    (hfinalSize : 96 ≤ (truncatedFinal mem aw q3 n r2 kWords).memory.size)
    (hfinalLe : (truncatedFinal mem aw q3 n r2 kWords).memory.size ≤ fp)
    (hfinalGap : fp - (truncatedFinal mem aw q3 n r2 kWords).memory.size < USize.size)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hq3Value : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (q3.toNat + 32) (kWords + 1)) =
        Modexp.barrettQ3 kWords nValue x)
    (hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue)
    (hproductValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (product.toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1))
    (hselect : selectBarrettFromTruncated fuel mem aw q3 n r2 product fp kWords =
      some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory (fp + 32) kWords) = x % nValue := by
  let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory fp kWords
  let resultAw := resultAllocatedWords final.activeWords fp kWords
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q initial).i = q := by
    simpa only [initial, Nat.zero_add] using
      truncatedRowsIterate_i q3 n r2 kWords q initial
  have hindices (limit : Nat) (hlimit : limit ≤ kWords + 1) :
      ∀ q, q < limit →
        (truncatedRowsIterate q3 n r2 kWords q initial).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hcoverage (q : Nat) (hq : q ≤ kWords + 1) :=
    truncatedRows_coverage q3 n r2 kWords q initial hk (hindices q hq)
      (by simpa only [initial] using hcovered)
      (by simpa only [initial] using hawFit) hq3Fit hnFit hr2Fit hr2Bound
  have hbases : ∀ q, q < kWords + 1 →
      32 ≤ (truncatedRowsIterate q3 n r2 kWords q initial).memory.size := by
    intro q hq
    exact (by omega : 32 ≤ mem.size).trans (hcoverage q (by omega)).2.2
  have hframe (ptr words : Nat) (hbelow : ptr + 32 * words ≤ r2.toNat + 32) :
      memoryWordsFrom final.memory ptr words = memoryWordsFrom mem ptr words := by
    have h := truncatedRows_memoryWords_below q3 n r2 kWords (kWords + 1)
      ptr words initial (hindices (kWords + 1) (by rfl)) hbases hr2Bound hbelow
    simpa only [final, initial] using h
  have hfinalCoverage := hcoverage (kWords + 1) (by rfl)
  have hresultCoverage := resultAllocatedMemory_coverage final.memory final.activeWords
    fp kWords (by simpa only [final] using hfinalCoverage.1)
    (by simpa only [final] using hfinalCoverage.2.1) (by simpa only [final] using hfinalSize)
    (by simpa only [final] using hfinalLe) (by simpa only [final] using hfinalGap)
    hresultBound
  have hresultSize : resultMem.size = fp + 32 := by
    simpa only [resultMem] using resultAllocatedMemory_size final.memory fp kWords
      (by simpa only [final] using hfinalSize) (by simpa only [final] using hfinalLe)
      (by simpa only [final] using hfinalGap)
  have hresultPtr : (UInt256.ofNat fp).toNat = fp :=
    resultAllocatedPtr_toNat fp kWords hresultBound
  have hr2PayloadBefore : r2.toNat + 32 + 32 * (kWords + 1) ≤ fp := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hr2BeforeResult
    omega
  have hr2LeFp : r2.toNat ≤ fp := by omega
  have hfpFit : fp + 32 < UInt256.size := by
    apply (show fp + 32 < 2 ^ 64 by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound
      omega).trans
    decide
  have hresultFrame (ptr words : Nat) (hptr : 96 ≤ ptr)
      (hbelow : ptr + 32 * words ≤ fp) :
      memoryWordsFrom resultMem ptr words = memoryWordsFrom final.memory ptr words := by
    simpa only [resultMem] using resultAllocatedMemory_words_below final.memory fp kWords
      ptr words (by simpa only [final] using hfinalSize)
      (by simpa only [final] using hfinalGap) hptr hbelow
  have hr2Value := Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_value_of_fresh_payload
    q3 n r2 kWords initial (by rfl) hkPos hk
    (by simpa only [initial] using hcovered) (by simpa only [initial] using hawFit)
    (by simpa only [initial] using (show 32 ≤ mem.size by omega))
    (by simpa only [initial] using hfresh)
    hq3Fit hnFit hr2Fit hr2Bound hq3Before hnBefore
  have hr2Value' : Modexp.wordLimbsToNat
      (memoryWordsFrom resultMem (r2.toNat + 32) (kWords + 1)) =
        (Modexp.barrettQ3 kWords nValue x * nValue) %
          UInt256.size ^ (kWords + 1) := by
    rw [hresultFrame (r2.toNat + 32) (kWords + 1) hr2Base hr2PayloadBefore]
    rw [show Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
      (Modexp.wordLimbsToNat
          (memoryWordsFrom mem (q3.toNat + 32) (kWords + 1)) *
        Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords)) %
          UInt256.size ^ (kWords + 1) by
      simpa only [final, initial] using hr2Value]
    rw [hq3Value, hnValue]
  have hnValue' : correctionModulusValue resultMem n kWords = nValue := by
    unfold correctionModulusValue
    rw [hresultFrame (n.toNat + 32) kWords hnBase (by omega),
      hframe (n.toNat + 32) kWords (by omega), hnValue]
  have hproductValue' : Modexp.wordLimbsToNat
      (memoryWordsFrom resultMem (product.toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1) := by
    rw [hresultFrame (product.toNat + 32) (kWords + 1) hproductBase (by omega),
      hframe (product.toNat + 32) (kWords + 1) (by omega), hproductValue]
  have hselect' : selectBarrettReductionTail fuel resultMem resultAw product n r2
      (UInt256.ofNat fp) kWords = some selected := by
    simpa only [selectBarrettFromTruncated, selectedResultMemory, selectedResultWords,
      truncatedFinal, final, initial, resultMem, resultAw] using hselect
  have htail := selectedBarrettReductionTail_resultValue_eq_mod
    (fuel := fuel) (mem := resultMem) (aw := resultAw) (product := product) (n := n)
    (r2 := r2) (result := UInt256.ofNat fp) (kWords := kWords) (nValue := nValue)
    (x := x) (selected := selected) hkPos hkShift hproductFit (by omega) (by omega)
    (by rw [hresultPtr]; exact hfpFit)
    (by rw [hresultSize]; omega) (by rw [hresultSize]; omega)
    (by rw [hresultSize]; omega) (by rw [hresultSize, hresultPtr])
    hproductBefore hnBefore
    (by simpa only [resultMem, resultAw] using hresultCoverage.1)
    (by simpa only [resultMem, resultAw] using hresultCoverage.2)
    hnPos hnNormalized hnFits hx hnValue' hproductValue' hr2Value' hselect'
  simpa only [hresultPtr] using htail

/-- Specialize the complete reduction semantics to the literal state returned by the `r2`
allocator, framing all earlier product, q3, and modulus words across that allocation. -/
theorem selectedBarrettFromAllocatedR2_resultValue_eq_mod
    {fuel fp kWords nValue x : Nat} {mem : ByteArray}
    {aw q3 n product : UInt256} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hk : kWords ≤ 32) (hkShift : kWords < 2 ^ 251)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hr2Bound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (kWords + 1) +
      wordArrayAllocationSize kWords < 2 ^ 64)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hproductFit : product.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hq3Base : 96 ≤ q3.toNat + 32)
    (hnBase : 96 ≤ n.toNat + 32)
    (hproductBase : 96 ≤ product.toNat + 32)
    (hq3Before : q3.toNat + 32 * (kWords + 2) ≤ fp)
    (hnBefore : n.toNat + 32 * (kWords + 1) ≤ fp)
    (hproductBefore : product.toNat + 32 * (kWords + 2) ≤ fp)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hq3Value : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (q3.toNat + 32) (kWords + 1)) =
        Modexp.barrettQ3 kWords nValue x)
    (hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue)
    (hproductValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (product.toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1))
    (hselect : selectBarrettFromTruncated fuel
      (r2AllocatedMemory mem fp kWords) (r2AllocatedWords aw fp kWords)
      q3 n (UInt256.ofNat fp) product
      (fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory
          (fp + wordArrayAllocationSize (kWords + 1) + 32) kWords) = x % nValue := by
  let allocatedMemory := r2AllocatedMemory mem fp kWords
  let allocatedWords := r2AllocatedWords aw fp kWords
  let r2 := UInt256.ofNat fp
  let resultFp := fp + wordArrayAllocationSize (kWords + 1)
  have hfpNat : r2.toNat = fp := by
    simpa only [r2] using r2AllocatedPtr_toNat fp kWords hr2Bound
  have hallocatedCoverage := r2AllocatedMemory_coverage mem aw fp kWords hcovered hawFit
    hmemSize hmemLe hgap hr2Bound
  have hallocatedSize : allocatedMemory.size = fp + 32 := by
    simpa only [allocatedMemory] using
      r2AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hgeometry := r2Allocated_truncatedResultGeometry mem aw q3 n fp kWords hk
    hcovered hawFit hmemSize hmemLe hgap hr2Bound hq3Fit hnFit
  have hframe (ptr words : Nat) (hptr : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
      memoryWordsFrom allocatedMemory ptr words = memoryWordsFrom mem ptr words := by
    simpa only [allocatedMemory] using r2AllocatedMemory_words_below mem fp kWords ptr words
      hmemSize hgap hptr hbelow
  have hq3Value' : Modexp.wordLimbsToNat
      (memoryWordsFrom allocatedMemory (q3.toNat + 32) (kWords + 1)) =
        Modexp.barrettQ3 kWords nValue x := by
    rw [hframe (q3.toNat + 32) (kWords + 1) hq3Base (by omega), hq3Value]
  have hnValue' : Modexp.wordLimbsToNat
      (memoryWordsFrom allocatedMemory (n.toNat + 32) kWords) = nValue := by
    rw [hframe (n.toNat + 32) kWords hnBase (by omega), hnValue]
  have hproductValue' : Modexp.wordLimbsToNat
      (memoryWordsFrom allocatedMemory (product.toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1) := by
    rw [hframe (product.toNat + 32) (kWords + 1) hproductBase (by omega), hproductValue]
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hfpNat]
    have h64 : fp + 32 * (kWords + 2) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
      omega
    exact lt_trans (by omega : fp + 32 * (kWords + 3) < 2 ^ 64 + 32)
      (by decide : 2 ^ 64 + 32 < UInt256.size)
  have hsemantic := selectedBarrettFromTruncated_resultValue_eq_mod
    (fuel := fuel) (fp := resultFp) (kWords := kWords) (nValue := nValue) (x := x)
    (mem := allocatedMemory) (aw := allocatedWords) (q3 := q3) (n := n) (r2 := r2)
    (product := product) (selected := selected) hkPos hk hkShift
    (by simpa only [allocatedMemory, allocatedWords] using hallocatedCoverage.1)
    (by simpa only [allocatedMemory, allocatedWords] using hallocatedCoverage.2)
    (by rw [hallocatedSize]; omega) (by rw [hallocatedSize, hfpNat])
    hq3Fit hnFit hr2Fit hproductFit
    (by simpa only [r2, hfpNat] using hr2Bound)
    (by simpa only [resultFp] using hresultBound)
    hproductBase hnBase (by rw [hfpNat]; omega)
    (by rw [hfpNat]; omega) (by rw [hfpNat]; exact hnBefore)
    (by rw [hfpNat]; exact hproductBefore)
    (show r2.toNat + wordArrayAllocationSize (kWords + 1) ≤ resultFp by
      dsimp only [resultFp]
      rw [hfpNat])
    (by simpa only [allocatedMemory, allocatedWords, r2, resultFp, truncatedFinal] using
      hgeometry.memorySize96)
    (by simpa only [allocatedMemory, allocatedWords, r2, resultFp, truncatedFinal] using
      hgeometry.memoryLeResult)
    (by simpa only [allocatedMemory, allocatedWords, r2, resultFp, truncatedFinal] using
      hgeometry.resultGap)
    hnPos hnNormalized hnFits hx hq3Value' hnValue' hproductValue'
    (by simpa only [allocatedMemory, allocatedWords, r2, resultFp] using hselect)
  simpa only [resultFp] using hsemantic

/-- Compose the two concrete full products and q1/q3 slices with the complete selected Barrett
reduction.  This is the numeric companion to `selectedBarrettFromFirstProductExact`: the exposed
selector's actual result payload is the pure remainder of the original product. -/
theorem selectedBarrettFromFirstProduct_resultValue_eq_mod
    {fuel fp kWords aValue bValue nValue x : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) + wordArrayAllocationSize kWords < 2 ^ 64)
    (haBase : 96 ≤ a.toNat + 32) (hbBase : 96 ≤ b.toNat + 32)
    (hnBase : 96 ≤ n.toNat + 32) (hmuBase : 96 ≤ mu.toNat + 32)
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp)
    (hnEnd : n.toNat + 32 * (kWords + 1) ≤ fp)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (haValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (a.toNat + 32) kWords) = aValue)
    (hbValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (b.toNat + 32) kWords) = bValue)
    (hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue)
    (hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue)
    (hxValue : aValue * bValue = x)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hselect :
      let firstFinal := firstProductFinal mem aw a b fp kWords
      let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
      let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
      let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
      let q1 := UInt256.ofNat q1Fp
      let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
      let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
      let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
      let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
      let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
      let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
      let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
      let q3 := UInt256.ofNat q3Fp
      let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
      selectBarrettFromTruncated fuel
        (r2AllocatedMemory (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        q3 n (UInt256.ofNat r2Fp) (UInt256.ofNat fp)
        (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected) :
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory
          (r2Fp + wordArrayAllocationSize (kWords + 1) + 32) kWords) = x % nValue := by
  let firstFinal := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  have hfirstGeometry := firstProductFinal_geometry mem aw a b fp kWords (by omega)
    hcovered hawFit hmemSize hmemLe hgap hfirstBound haEnd hbEnd
  have hproductNat : (UInt256.ofNat fp).toNat = fp :=
    functionResultPtr_toNat fp (2 * kWords) hfirstBound
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hproductNat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstBound
      omega : fp + 32 * kWords < 2 ^ 64) (by decide)
  have hq1Source : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp + 32 := by
    rw [hproductNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Geometry := q1Slice_geometry firstFinal.memory firstFinal.activeWords
    (UInt256.ofNat fp) mu q1Fp kWords hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.activeWordsFit)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source (by omega)
  have hq1Nat : q1.toNat = q1Fp := q1AllocatedPtr_toNat q1Fp kWords
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
  have hsecondGeometry := secondProductFinal_geometry copiedMem copiedAw q1 mu
    secondFp kWords (by omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by omega)
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp :=
    functionResultPtr_toNat secondFp (2 * kWords + 4)
      (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
  have hsecondPayload64 : secondFp + 32 * (2 * kWords + 5) < 2 ^ 64 := by
    have hb := hsecondBound
    dsimp only [secondFp, q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb ⊢
    omega
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) < UInt256.size := by
    rw [hsecondNat]
    exact lt_trans (by omega : secondFp + 32 * (kWords + 2) < 2 ^ 64) (by decide)
  have hq2Source : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤
      q3Fp + 32 := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq3CopiedCoverage := q3CopiedMemory_coverage q2Final.memory q2Final.activeWords
    (UInt256.ofNat secondFp) q3Fp kWords
    (by simpa only [q2Final] using hsecondGeometry.activeWordsFit)
    (by simpa only [q2Final] using hsecondGeometry.memorySize96)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.memoryLeNext)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
    hq2Fit hq2Source
  have hq3CopiedSize : q3CopiedMem.size = r2Fp := by
    simpa only [q3CopiedMem, q3Mem, q3, r2Fp] using
      q3CopiedMemory_size q2Final.memory (UInt256.ofNat secondFp) q3Fp kWords
        (by simpa only [q2Final] using hsecondGeometry.memorySize96)
        (by simpa only [q2Final, q3Fp] using hsecondGeometry.memoryLeNext)
        (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
        (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
        hq2Fit hq2Source
  have hq3Nat : q3.toNat = q3Fp := q3AllocatedPtr_toNat q3Fp kWords
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
  have hvalues := firstThroughQ3_values mem aw a b n mu fp kWords aValue bValue nValue x
    hkPos hk hcovered hawFit hmemSize hmemLe hgap hfirstBound hq1Bound hsecondBound
    hq3Bound haBase hbBase hnBase hmuBase haEnd hbEnd hnEnd hmuEnd haValue hbValue
    hnValue hmuValue hxValue hnNormalized hx
  have hnPos : 0 < nValue :=
    lt_of_lt_of_le (pow_pos (by decide : 0 < UInt256.size) _) hnNormalized
  have hnFits : nValue < UInt256.size ^ kWords := by
    have hb := Modexp.wordLimbsToNat_lt_pow
      (memoryWordsFrom mem (n.toNat + 32) kWords)
    rw [memoryWordsFrom_length, hnValue] at hb
    exact hb
  have hq3Fit' : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hq3Nat]
    have hb := hq3Bound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb ⊢
    exact lt_trans (by omega) (by decide : 2 ^ 64 < UInt256.size)
  have hproductReductionFit :
      (UInt256.ofNat fp).toNat + 32 * (kWords + 2) + 31 < UInt256.size := by
    rw [hproductNat]
    have hb := hq3Bound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    exact lt_trans (by omega : fp + 32 * (kWords + 2) + 31 < 2 ^ 64)
      (by decide)
  have hq3Before : q3.toNat + 32 * (kWords + 2) ≤ r2Fp := by
    rw [hq3Nat]
    dsimp only [r2Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hnBefore : n.toNat + 32 * (kWords + 1) ≤ r2Fp := by
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    omega
  have hproductBefore : (UInt256.ofNat fp).toNat + 32 * (kWords + 2) ≤ r2Fp := by
    rw [hproductNat]
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsemantic := selectedBarrettFromAllocatedR2_resultValue_eq_mod
    (fuel := fuel) (fp := r2Fp) (kWords := kWords) (nValue := nValue) (x := x)
    (mem := q3CopiedMem) (aw := q3CopiedAw) (q3 := q3) (n := n)
    (product := UInt256.ofNat fp) (selected := selected) hkPos hk (by omega)
    (by simpa only [q3CopiedMem, q3CopiedAw, q3Mem, q3Aw, q3] using
      hq3CopiedCoverage.1)
    (by simpa only [q3CopiedAw, q3Aw, q3] using hq3CopiedCoverage.2)
    (by rw [hq3CopiedSize]; omega) (by rw [hq3CopiedSize])
    (by rw [hq3CopiedSize]; omega)
    (by simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using hr2Bound)
    (by simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using hresultBound)
    hq3Fit' hnFit hproductReductionFit
    (by rw [hq3Nat]; omega) hnBase (by rw [hproductNat]; omega)
    hq3Before hnBefore hproductBefore
    hnPos hnNormalized hnFits hx
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp, copiedMem, copiedAw,
      q2Final, q3Fp, q3Mem, q3Aw, q3, q3CopiedMem] using hvalues.1)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp, copiedMem, copiedAw,
      q2Final, q3Fp, q3Mem, q3Aw, q3, q3CopiedMem] using hvalues.2.1)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp, copiedMem, copiedAw,
      q2Final, q3Fp, q3Mem, q3Aw, q3, q3CopiedMem] using hvalues.2.2)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp, copiedMem, copiedAw,
      q2Final, q3Fp, q3Mem, q3Aw, q3, q3CopiedMem, q3CopiedAw, r2Fp] using hselect)
  simpa only [q1Fp, secondFp, q3Fp, r2Fp] using hsemantic

/-- A complete first Barrett call materializes the scratch range and preserves every persistent
word range below its initial free pointer.  This is the state bridge from fresh allocation to the
reused-scratch exponent invariant. -/
theorem selectedBarrettFromFirstProduct_stateGeometry
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) + wordArrayAllocationSize kWords < 2 ^ 64)
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp)
    (hnEnd : n.toNat + 32 * (kWords + 2) ≤ fp)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hselect :
      let firstFinal := firstProductFinal mem aw a b fp kWords
      let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
      let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
      let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
      let q1 := UInt256.ofNat q1Fp
      let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
      let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
      let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
      let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
      let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
      let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
      let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
      let q3 := UInt256.ofNat q3Fp
      let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
      selectBarrettFromTruncated fuel
        (r2AllocatedMemory (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        q3 n (UInt256.ofNat r2Fp) (UInt256.ofNat fp)
        (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected) :
    MemoryCovered selected.memory selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size ∧
      selected.memory.size = fp + wordArrayAllocationSize (2 * kWords) +
        wordArrayAllocationSize (kWords + 2) +
        wordArrayAllocationSize (2 * kWords + 4) +
        wordArrayAllocationSize (kWords + 3) +
        wordArrayAllocationSize (kWords + 1) + wordArrayAllocationSize kWords ∧
      ∀ ptr words, 96 ≤ ptr → ptr + 32 * words ≤ fp →
        memoryWordsFrom selected.memory ptr words = memoryWordsFrom mem ptr words := by
  let first := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState := { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  let subtractionFinal := subtractionIterate (UInt256.ofNat fp) r2 (kWords + 1)
    subtractionInitial
  have hfirstGeometry := firstProductFinal_geometry mem aw a b fp kWords (by omega)
    hcovered hawFit hmemSize hmemLe hgap hfirstBound haEnd hbEnd
  have hproductNat : (UInt256.ofNat fp).toNat = fp :=
    functionResultPtr_toNat fp (2 * kWords) hfirstBound
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hproductNat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstBound
      omega : fp + 32 * kWords < 2 ^ 64) (by decide)
  have hq1Source : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp + 32 := by
    rw [hproductNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Geometry := q1Slice_geometry first.memory first.activeWords
    (UInt256.ofNat fp) mu q1Fp kWords hkPos (by omega)
    (by simpa only [first] using hfirstGeometry.activeWordsFit)
    (by simpa only [first] using hfirstGeometry.memorySize96)
    (by simpa only [first, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [first, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source (by omega)
  have hq1Nat : q1.toNat = q1Fp := q1AllocatedPtr_toNat q1Fp kWords
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
  have hsecondGeometry := secondProductFinal_geometry copiedMem copiedAw q1 mu
    secondFp kWords (by omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by have hmu := hmuEnd; dsimp only [secondFp, q1Fp]; omega)
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp :=
    functionResultPtr_toNat secondFp (2 * kWords + 4)
      (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) < UInt256.size := by
    rw [hsecondNat]
    exact lt_trans (by
      have hb : secondFp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
        simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega : secondFp + 32 * (kWords + 2) < 2 ^ 64) (by decide)
  have hq2Source : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤
      q3Fp + 32 := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq3Coverage := q3CopiedMemory_coverage q2.memory q2.activeWords
    (UInt256.ofNat secondFp) q3Fp kWords
    (by simpa only [q2] using hsecondGeometry.activeWordsFit)
    (by simpa only [q2] using hsecondGeometry.memorySize96)
    (by simpa only [q2, q3Fp] using hsecondGeometry.memoryLeNext)
    (by simpa only [q2, q3Fp] using hsecondGeometry.nextGap)
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
    hq2Fit hq2Source
  have hq3Size : copiedQ3Mem.size = r2Fp := by
    simpa only [copiedQ3Mem, q3Mem, q3, r2Fp] using
      q3CopiedMemory_size q2.memory (UInt256.ofNat secondFp) q3Fp kWords
        (by simpa only [q2] using hsecondGeometry.memorySize96)
        (by simpa only [q2, q3Fp] using hsecondGeometry.memoryLeNext)
        (by simpa only [q2, q3Fp] using hsecondGeometry.nextGap)
        (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
        hq2Fit hq2Source
  have hq3Nat : q3.toNat = q3Fp := q3AllocatedPtr_toNat q3Fp kWords
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hq3Nat]
    have hb : q3Fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
      simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    exact lt_trans (by omega : q3Fp + 32 * (kWords + 3) < 2 ^ 64)
      (by decide : 2 ^ 64 < UInt256.size)
  have hallocatedCoverage := r2AllocatedMemory_coverage copiedQ3Mem copiedQ3Aw r2Fp kWords
    (by simpa only [copiedQ3Mem, copiedQ3Aw, q3Mem, q3Aw, q3] using hq3Coverage.1)
    (by simpa only [copiedQ3Aw, q3Aw, q3] using hq3Coverage.2)
    (by rw [hq3Size]; omega) (by rw [hq3Size]) (by rw [hq3Size]; omega)
    (by simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using hr2Bound)
  have htruncatedGeometry := r2Allocated_truncatedResultGeometry copiedQ3Mem copiedQ3Aw q3 n
    r2Fp kWords hk
    (by simpa only [copiedQ3Mem, copiedQ3Aw, q3Mem, q3Aw, q3] using hq3Coverage.1)
    (by simpa only [copiedQ3Aw, q3Aw, q3] using hq3Coverage.2)
    (by rw [hq3Size]; omega) (by rw [hq3Size]) (by rw [hq3Size]; omega)
    (by simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using hr2Bound)
    hq3Fit hnFit
  have hresultCoverage := resultAllocatedMemory_coverage final.memory final.activeWords
    resultFp kWords
    (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
      htruncatedGeometry.covered)
    (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
      htruncatedGeometry.activeWordsFit)
    (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
      htruncatedGeometry.memorySize96)
    (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
      htruncatedGeometry.memoryLeResult)
    (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
      htruncatedGeometry.resultGap)
    (by simpa only [resultFp, r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
      hresultBound)
  have hresultSize : resultMem.size = resultFp + 32 := by
    simpa only [resultMem] using resultAllocatedMemory_size final.memory resultFp kWords
      (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
        htruncatedGeometry.memorySize96)
      (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
        htruncatedGeometry.memoryLeResult)
      (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
        htruncatedGeometry.resultGap)
  have hr2Nat : r2.toNat = r2Fp := by
    dsimp only [r2]
    exact r2AllocatedPtr_toNat r2Fp kWords
      (by simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using hr2Bound)
  have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp :=
    resultAllocatedPtr_toNat resultFp kWords
      (by simpa only [resultFp, r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
        hresultBound)
  have hproductReductionFit : (UInt256.ofNat fp).toNat + 32 * (kWords + 2) + 31 <
      UInt256.size := by
    rw [hproductNat]
    exact lt_trans (by
      have hb := hresultBound
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega : fp + 32 * (kWords + 2) + 31 < 2 ^ 64) (by decide)
  have hr2ReductionFit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size := by
    rw [hr2Nat]
    have hresultRelation : resultFp = r2Fp + 32 * (kWords + 2) := by
      dsimp only [resultFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact lt_trans (by
      have hb : resultFp + wordArrayAllocationSize kWords < 2 ^ 64 := by
        simpa only [resultFp, r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
          hresultBound
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega : r2Fp + 32 * (kWords + 2) + 31 < 2 ^ 64) (by decide)
  have hnReductionFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size := by
    omega
  have hproductMem : (UInt256.ofNat fp).toNat + 32 * (kWords + 2) ≤ resultMem.size := by
    rw [hproductNat, hresultSize]
    dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ resultMem.size := by
    rw [hr2Nat, hresultSize]
    dsimp only [resultFp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hnMem : n.toNat + 32 * (kWords + 1) ≤ resultMem.size := by
    rw [hresultSize]
    exact le_trans (by omega : n.toNat + 32 * (kWords + 1) ≤ fp)
      (by dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]; omega)
  have hsubtraction := subtractionIterate_coverage_size (kWords + 1)
    (UInt256.ofNat fp) r2 subtractionInitial
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using
      hproductReductionFit)
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using
      hr2ReductionFit)
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hproductMem)
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hr2Mem)
    (by simpa only [subtractionInitial, subtractionInitialState, resultMem, resultAw] using
      hresultCoverage.1)
    (by simpa only [subtractionInitial, subtractionInitialState, resultMem, resultAw] using
      hresultCoverage.2)
  have hsubtractionSize : subtractionFinal.memory.size = resultMem.size := by
    simpa only [subtractionFinal, subtractionInitial, subtractionInitialState] using
      hsubtraction.2.2
  have hcorrectionSelect : selectBarrettCorrection fuel subtractionFinal.memory
      subtractionFinal.activeWords n r2 (UInt256.ofNat resultFp) kWords = some selected := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp,
      allocatedMem, allocatedAw, r2, initial, final, resultFp, resultMem, resultAw,
      selectBarrettFromTruncated, selectedResultMemory, selectedResultWords,
      truncatedFinal, selectBarrettReductionTail, Modexp.MultiLimbBarrettReduction.subtractionFinal,
      subtractionFinal, subtractionInitial, subtractionInitialState] using hselect
  have hresultHeaderFit : resultFp + 32 < UInt256.size := by
    have hb : resultFp + wordArrayAllocationSize kWords < 2 ^ 64 := by
      simpa only [resultFp, r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
        hresultBound
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega : resultFp + 32 < 2 ^ 64) (by decide)
  have hresultAccessFit : resultFp + 32 + 32 * kWords + 31 < UInt256.size := by
    have hb : resultFp + wordArrayAllocationSize kWords < 2 ^ 64 := by
      simpa only [resultFp, r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
        hresultBound
    have hb64 : resultFp + 32 + 32 * kWords + 31 < 2 ^ 64 + 31 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega
    exact lt_trans hb64 (by norm_num [UInt256.size])
  have hcorrection := selectedBarrettCorrection_coverage_size_from_start
    (mem := subtractionFinal.memory) (aw := subtractionFinal.activeWords)
    (n := n) (r2 := r2) (result := UInt256.ofNat resultFp)
    (kWords := kWords) (selected := selected) hkPos
    (lt_of_le_of_lt hk (by native_decide : 32 < 2 ^ 251))
    hr2ReductionFit hnReductionFit
    (by rw [hresultNat]; exact hresultHeaderFit)
    (by rw [hsubtractionSize]; exact hr2Mem)
    (by rw [hsubtractionSize]; exact hnMem)
    (by rw [hresultNat, hsubtractionSize, hresultSize])
    (by rw [hresultNat]; exact hresultAccessFit)
    (by simpa only [subtractionFinal] using hsubtraction.1)
    (by simpa only [subtractionFinal] using hsubtraction.2.1) hcorrectionSelect
  refine ⟨hcorrection.1, hcorrection.2.1, ?_, ?_⟩
  · rw [hcorrection.2.2, hsubtractionSize, hresultSize, hresultNat]
    dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
    rw [max_eq_right (by omega)]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro ptr words hptrBase hbelow
    have hfirstFrame : memoryWordsFrom first.memory ptr words =
        memoryWordsFrom mem ptr words := by
      simpa only [first, firstProductFinal] using
        functionFinalState_words_below mem aw a b fp kWords kWords ptr words (by omega)
          hcovered hawFit hmemSize hmemLe hgap
          (by simpa only [show kWords + kWords = 2 * kWords by omega] using hfirstBound)
          haEnd hbEnd hptrBase hbelow
    have hq1Frame : memoryWordsFrom copiedMem ptr words =
        memoryWordsFrom first.memory ptr words := by
      simpa only [copiedMem, q1Mem, q1] using
        q1CopiedMemory_words_below first.memory (UInt256.ofNat fp) q1Fp kWords ptr words
          hkPos (by omega) (by simpa only [first] using hfirstGeometry.memorySize96)
          (by simpa only [first, q1Fp] using hfirstGeometry.memoryLeNext)
          (by simpa only [first, q1Fp] using hfirstGeometry.nextGap)
          (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound) hproductFit hq1Source
          hptrBase (by dsimp only [q1Fp]; omega)
    have hsecondFrame : memoryWordsFrom q2.memory ptr words =
        memoryWordsFrom copiedMem ptr words := by
      simpa only [q2, secondProductFinal] using
        functionFinalState_words_below copiedMem copiedAw q1 mu secondFp (kWords + 2)
          (kWords + 2) ptr words (by omega)
          (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
          (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
          (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
          (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
            hq1Geometry.memoryLeNext)
          (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
            hq1Geometry.nextGap)
          (by simpa only [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega,
            secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
          (by
            rw [hq1Nat]
            dsimp only [secondFp, q1Fp]
            unfold wordArrayAllocationSize wordArrayPayloadSize
            omega)
          (by omega)
          hptrBase (by dsimp only [secondFp, q1Fp]; omega)
    have hq3Frame : memoryWordsFrom copiedQ3Mem ptr words =
        memoryWordsFrom q2.memory ptr words := by
      simpa only [copiedQ3Mem, q3Mem, q3] using
        q3CopiedMemory_words_below q2.memory (UInt256.ofNat secondFp) q3Fp kWords ptr words
          (by simpa only [q2] using hsecondGeometry.memorySize96)
          (by simpa only [q2, q3Fp] using hsecondGeometry.memoryLeNext)
          (by simpa only [q2, q3Fp] using hsecondGeometry.nextGap)
          (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
          hq2Fit hq2Source hptrBase (by dsimp only [q3Fp, secondFp, q1Fp]; omega)
    have hallocatedFrame : memoryWordsFrom allocatedMem ptr words =
        memoryWordsFrom copiedQ3Mem ptr words := by
      simpa only [allocatedMem] using r2AllocatedMemory_words_below copiedQ3Mem r2Fp
        kWords ptr words (by rw [hq3Size]; omega) (by rw [hq3Size]; omega) hptrBase
        (by dsimp only [r2Fp, q3Fp, secondFp, q1Fp]; omega)
    have hindex (q : Nat) : (truncatedRowsIterate q3 n r2 kWords q initial).i = q := by
      simpa only [initial, Nat.zero_add] using
        truncatedRowsIterate_i q3 n r2 kWords q initial
    have hindices (limit : Nat) (hlimit : limit ≤ kWords + 1) :
        ∀ q, q < limit → (truncatedRowsIterate q3 n r2 kWords q initial).i ≤ kWords := by
      intro q hq
      rw [hindex q]
      omega
    have hcoverage (q : Nat) (hq : q ≤ kWords + 1) :=
      truncatedRows_coverage q3 n r2 kWords q initial hk (hindices q hq)
        (by simpa only [initial] using hallocatedCoverage.1)
        (by simpa only [initial] using hallocatedCoverage.2) hq3Fit hnFit
        (by rw [hr2Nat]; exact lt_trans (by
          have hb : r2Fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
            simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using hr2Bound
          unfold wordArrayAllocationSize wordArrayPayloadSize at hb
          omega : r2Fp + 32 * (kWords + 3) < 2 ^ 64 + 32) (by decide))
        (by rw [hr2Nat]; simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
          hr2Bound)
    have hbases : ∀ q, q < kWords + 1 →
        32 ≤ (truncatedRowsIterate q3 n r2 kWords q initial).memory.size := by
      intro q hq
      have hallocatedSize : allocatedMem.size = r2Fp + 32 := by
        simpa only [allocatedMem] using r2AllocatedMemory_size copiedQ3Mem r2Fp kWords
          (by rw [hq3Size]; omega) (by rw [hq3Size]) (by rw [hq3Size]; omega)
      exact (by rw [hallocatedSize]; omega : 32 ≤ allocatedMem.size).trans
        (hcoverage q (by omega)).2.2
    have htruncatedFrame : memoryWordsFrom final.memory ptr words =
        memoryWordsFrom allocatedMem ptr words := by
      have hframe := truncatedRows_memoryWords_below q3 n r2 kWords (kWords + 1)
        ptr words initial (hindices (kWords + 1) (by rfl)) hbases
        (by rw [hr2Nat]; simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using
          hr2Bound)
        (by rw [hr2Nat]; omega)
      simpa only [final] using hframe
    have hresultFrame : memoryWordsFrom resultMem ptr words =
        memoryWordsFrom final.memory ptr words := by
      simpa only [resultMem] using resultAllocatedMemory_words_below final.memory resultFp
        kWords ptr words
        (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
          htruncatedGeometry.memorySize96)
        (by simpa only [allocatedMem, allocatedAw, r2, initial, final, resultFp] using
          htruncatedGeometry.resultGap)
        hptrBase (by dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]; omega)
    have hsubFrame : memoryWordsFrom subtractionFinal.memory ptr words =
        memoryWordsFrom resultMem ptr words := by
      have hframe := subtractionIterate_memoryWords_below (kWords + 1)
        (UInt256.ofNat fp) r2 subtractionInitial ptr words
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using
          hproductReductionFit)
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using
          hr2ReductionFit)
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hproductMem)
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hr2Mem)
        (by simpa only [subtractionInitial, subtractionInitialState, resultMem, resultAw] using
          hresultCoverage.1)
        (by simpa only [subtractionInitial, subtractionInitialState, resultMem, resultAw] using
          hresultCoverage.2)
        (by rw [hr2Nat]; omega)
      simpa only [subtractionFinal, subtractionInitial] using hframe
    have hcorrectionFrame := selectedBarrettCorrection_memoryWords_below
      (mem := subtractionFinal.memory) (aw := subtractionFinal.activeWords)
      (n := n) (r2 := r2) (result := UInt256.ofNat resultFp)
      (kWords := kWords) (ptr := ptr) (words := words) (selected := selected)
      hkPos (lt_of_le_of_lt hk (by native_decide : 32 < 2 ^ 251))
      hr2ReductionFit hnReductionFit
      (by rw [hresultNat]; exact hresultHeaderFit)
      (by rw [hsubtractionSize]; exact hr2Mem)
      (by rw [hsubtractionSize]; exact hnMem)
      (by rw [hresultNat, hsubtractionSize, hresultSize])
      (by rw [hr2Nat, hresultNat]; dsimp only [resultFp]; omega)
      (by simpa only [subtractionFinal] using hsubtraction.1)
      (by simpa only [subtractionFinal] using hsubtraction.2.1)
      (by rw [hr2Nat]; omega) hcorrectionSelect
    calc
      memoryWordsFrom selected.memory ptr words =
          memoryWordsFrom subtractionFinal.memory ptr words := hcorrectionFrame
      _ = memoryWordsFrom resultMem ptr words := hsubFrame
      _ = memoryWordsFrom final.memory ptr words := hresultFrame
      _ = memoryWordsFrom allocatedMem ptr words := htruncatedFrame
      _ = memoryWordsFrom copiedQ3Mem ptr words := hallocatedFrame
      _ = memoryWordsFrom q2.memory ptr words := hq3Frame
      _ = memoryWordsFrom copiedMem ptr words := hsecondFrame
      _ = memoryWordsFrom first.memory ptr words := hq1Frame
      _ = memoryWordsFrom mem ptr words := hfirstFrame

end Modexp.MultiLimbBarrettReduction
