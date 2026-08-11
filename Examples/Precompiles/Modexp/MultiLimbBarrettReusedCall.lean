import Examples.Precompiles.Modexp.MultiLimbBarrettReusedContract

/-! # Complete Barrett call over reused scratch memory -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReusedCall

open Modexp.MultiLimbBarrettCorrection
open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbBarrettReduction
open Modexp.MultiLimbBarrettReused
open Modexp.MultiLimbBarrettCorrectionSemantic
open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbBarrettTruncatedMul
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def callResultFp (fp kWords : Nat) : Nat :=
  fp + wordArrayAllocationSize (2 * kWords) +
    wordArrayAllocationSize (kWords + 2) +
    wordArrayAllocationSize (2 * kWords + 4) +
    wordArrayAllocationSize (kWords + 3) +
    wordArrayAllocationSize (kWords + 1)

def selectCall (fuel : Nat) (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords : Nat) : Option BarrettCorrectionSelection :=
  let firstFinal := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Final := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  Modexp.MultiLimbBarrettReused.selectBarrettFromTruncated fuel
    (Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords)
    (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords)
      r2Fp kWords)
    q3 n (UInt256.ofNat r2Fp) (UInt256.ofNat fp)
    (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords

theorem selectCall_exists
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected, selectCall fuel mem aw a b n mu fp kWords = some selected := by
  unfold selectCall
  exact Modexp.MultiLimbBarrettReused.selectBarrettFromTruncated_exists hkPos hfuel

def callSteps (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords : Nat) (selected : BarrettCorrectionSelection) : Nat :=
  let firstInitial := Modexp.MultiLimbBarrettReused.firstProductInitial mem aw fp kWords
  let firstFinal := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Initial := Modexp.MultiLimbBarrettReused.secondProductInitial
    copiedMem copiedAw secondFp kWords
  let q2Final := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let initial : TruncatedOuterState := { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  837 + rowsSteps a b (UInt256.ofNat fp) kWords kWords firstInitial +
    rowsSteps q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
    truncatedRowsSteps q3 n (UInt256.ofNat r2Fp) kWords (kWords + 1) initial +
    44 * (kWords + 1) + selected.steps

def callGas (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords : Nat) (selected : BarrettCorrectionSelection) : Nat :=
  let firstInitial := Modexp.MultiLimbBarrettReused.firstProductInitial mem aw fp kWords
  let firstFinal := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Initial := Modexp.MultiLimbBarrettReused.secondProductInitial
    copiedMem copiedAw secondFp kWords
  let q2Final := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState := { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let resultMem := Modexp.MultiLimbBarrettReused.resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  1133 + newWordArrayGas aw fp (2 * kWords) +
    rowsGas a b (UInt256.ofNat fp) kWords kWords firstInitial +
    newWordArrayGas firstFinal.activeWords q1Fp (kWords + 2) +
    q1SliceGas q1Aw q1 (UInt256.ofNat fp) mu kWords +
    newWordArrayGas copiedAw secondFp (2 * kWords + 4) +
    rowsGas q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
    newWordArrayGas q2Final.activeWords q3Fp (kWords + 3) +
    q3CopyGas q3Aw q3 (UInt256.ofNat secondFp) kWords +
    newWordArrayGas copiedQ3Aw r2Fp (kWords + 1) +
    truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
    newWordArrayGas final.activeWords resultFp kWords +
    subtractionThroughExitGas (UInt256.ofNat fp) r2 kWords
      (subtractionInitialState resultMem resultAw) + selected.gas

/-- End of the complete scratch range materialized by one Barrett call. -/
def scratchEnd (fp kWords : Nat) : Nat :=
  callResultFp fp kWords + wordArrayAllocationSize kWords

/-- Compact caller-facing invariant for a Barrett call that reuses an existing scratch region.
The persistent operand arrays all precede `fp`; the entire temporary range is already concrete
and covered by the EVM active-word counter. -/
structure ScratchInvariant (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray)
    (aw a b n mu : UInt256) (fp kWords : Nat)
    (selected : BarrettCorrectionSelection) : Prop where
  wordsPos : 0 < kWords
  words : kWords ≤ 32
  scratchBound : scratchEnd fp kWords < 2 ^ 64
  calldataBound : I.calldata.size < 2 ^ 64
  freePointerBase : 96 ≤ fp
  covered : MemoryCovered mem aw
  activeWordsFit : aw.toNat * 32 < UInt256.size
  scratchConcrete : scratchEnd fp kWords ≤ mem.size
  freePointerRead : mem.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat fp)
  aBase : 96 ≤ a.toNat
  bBase : 96 ≤ b.toNat
  nBase : 96 ≤ n.toNat
  muBase : 96 ≤ mu.toNat
  aBeforeScratch : a.toNat + 32 * (kWords + 1) ≤ fp
  bBeforeScratch : b.toNat + 32 * (kWords + 1) ≤ fp
  nBeforeScratch : n.toNat + 32 * (kWords + 2) ≤ fp
  muBeforeScratch : mu.toNat + 32 * (kWords + 3) ≤ fp
  muHeader : mem.readWithPadding mu.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat (kWords + 2))
  selection : selectCall fuel mem aw a b n mu fp kWords = some selected

/-- The compact scratch invariant supplies all geometry exported by the first reused product. -/
theorem ScratchInvariant.firstProductGeometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let final := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    ReusedFunctionFinalGeometry final
      (fp + wordArrayAllocationSize (2 * kWords)) := by
  have hmemSize : 96 ≤ mem.size := by
    have hfpLe : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact valid.freePointerBase.trans (hfpLe.trans valid.scratchConcrete)
  have hcapacity : fp + wordArrayAllocationSize (2 * kWords) ≤ mem.size := by
    have hfirst : fp + wordArrayAllocationSize (2 * kWords) ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp
      omega
    exact hfirst.trans valid.scratchConcrete
  have hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    have hfirst : fp + wordArrayAllocationSize (2 * kWords) ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp
      omega
    exact hfirst.trans_lt valid.scratchBound
  simpa only [Modexp.MultiLimbBarrettReused.firstProductFinal,
    show kWords + kWords = 2 * kWords by omega] using
    reusedFunctionFinal_geometry mem aw a b fp kWords kWords
      (by have hk := valid.words; omega) (by have hk := valid.wordsPos; omega)
      valid.covered valid.activeWordsFit hmemSize (by
        simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
      (by simpa only [show kWords + kWords = 2 * kWords by omega] using hbound)
      valid.freePointerBase valid.aBeforeScratch valid.bBeforeScratch

/-- The complete pre-existing scratch extent remains concrete after the first product. -/
theorem ScratchInvariant.firstProductScratchConcrete
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    scratchEnd fp kWords ≤
      (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory.size := by
  have hmemSize : 96 ≤ mem.size := by
    have hfpLe : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact valid.freePointerBase.trans (hfpLe.trans valid.scratchConcrete)
  have hcapacity : fp + wordArrayAllocationSize (2 * kWords) ≤ mem.size := by
    have hfirst : fp + wordArrayAllocationSize (2 * kWords) ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp
      omega
    exact hfirst.trans valid.scratchConcrete
  have hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    have hfirst : fp + wordArrayAllocationSize (2 * kWords) ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp
      omega
    exact hfirst.trans_lt valid.scratchBound
  have hrows := reusedFunctionRows_coverage mem aw a b fp kWords kWords kWords (by omega)
    valid.covered valid.activeWordsFit hmemSize
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hbound)
    valid.aBeforeScratch valid.bBeforeScratch
  have hinitialSize :
      (reusedFunctionInitialState mem aw fp kWords kWords).memory.size = mem.size := by
    simpa only [reusedFunctionInitialState,
      show kWords + kWords = 2 * kWords by omega] using
      reusedFunctionAllocatedMemory_size mem fp kWords kWords hmemSize (by
        simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
  have hmono : mem.size ≤
      (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory.size := by
    rw [← hinitialSize]
    simpa only [Modexp.MultiLimbBarrettReused.firstProductFinal,
      reusedFunctionFinalState] using hrows.2.2
  exact valid.scratchConcrete.trans hmono

/-- The first reused product computes the exact full product of the caller's input limbs. -/
theorem ScratchInvariant.firstProductValue
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let final := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (2 * kWords)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (a.toNat + 32) kWords) *
        Modexp.wordLimbsToNat (memoryWordsFrom mem (b.toNat + 32) kWords) := by
  have hmemSize : 96 ≤ mem.size := by
    have hfpScratch : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact valid.freePointerBase.trans (hfpScratch.trans valid.scratchConcrete)
  have hcapacity : fp + wordArrayAllocationSize (2 * kWords) ≤ mem.size := by
    apply le_trans _ valid.scratchConcrete
    unfold scratchEnd callResultFp
    omega
  have hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp
    omega
  simpa only [Modexp.MultiLimbBarrettReused.firstProductFinal,
    show kWords + kWords = 2 * kWords by omega] using
    reusedFunctionSchoolbookMul_value_of_input mem aw a b fp kWords kWords
      (by have hk := valid.words; omega) valid.wordsPos valid.covered
      valid.activeWordsFit hmemSize
      (by simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
      (by simpa only [show kWords + kWords = 2 * kWords by omega] using hbound)
      valid.aBase valid.bBase valid.aBeforeScratch valid.bBeforeScratch

/-- The first reused product preserves every complete persistent word range below its result
header. -/
theorem ScratchInvariant.firstProductWordsBelow
    {I : ExecutionEnv} {fuel fp kWords ptr words : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory
        ptr words =
      memoryWordsFrom mem ptr words := by
  have hmemSize : 96 ≤ mem.size := by
    have hfpScratch : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact valid.freePointerBase.trans (hfpScratch.trans valid.scratchConcrete)
  have hcapacity : fp + wordArrayAllocationSize (2 * kWords) ≤ mem.size := by
    apply le_trans _ valid.scratchConcrete
    unfold scratchEnd callResultFp
    omega
  have hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp
    omega
  have hrows := reusedFunctionRows_memoryWords_below_result mem aw a b fp kWords kWords
    kWords ptr words (by omega) (by have hk := valid.words; omega) valid.covered
    valid.activeWordsFit hmemSize
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hbound)
    valid.aBeforeScratch valid.bBeforeScratch hbelow
  have hallocated := reusedFunctionAllocatedMemory_words_below mem fp kWords kWords ptr
    words hmemSize
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
    (by have hk := valid.wordsPos; omega) hptrBase hbelow
  calc
    memoryWordsFrom
        (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory
        ptr words =
        memoryWordsFrom (reusedFunctionInitialState mem aw fp kWords kWords).memory
          ptr words := by
            simpa only [Modexp.MultiLimbBarrettReused.firstProductFinal,
              reusedFunctionFinalState] using hrows
    _ = memoryWordsFrom mem ptr words := by
      simpa only [reusedFunctionInitialState] using hallocated

/-- Geometry exported by the in-place q1 allocation, product slice, and `mu.length` load. -/
structure ReusedQ1Geometry
    (copiedMem : ByteArray) (copiedAw loadedAw mu : UInt256)
    (nextFp kWords backingSize : Nat) : Prop where
  muInMemory : mu.toNat < copiedMem.size
  muActive : ¬ mu ≥ copiedAw * ⟨32⟩
  muHeader : copiedMem.readWithPadding mu.toNat 32 =
    UInt256.toByteArray (UInt256.ofNat (kWords + 2))
  covered : MemoryCovered copiedMem loadedAw
  activeWordsFit : loadedAw.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ copiedMem.size
  activeWords3 : 3 ≤ loadedAw.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ loadedAw * ⟨32⟩
  freePointerRead : copiedMem.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat nextFp)
  concreteThrough : nextFp ≤ copiedMem.size
  memorySizeEq : copiedMem.size = backingSize

set_option maxHeartbeats 500000 in
/-- A q1 slice performed inside an already-materialized scratch region has the same logical
geometry as the fresh allocation, while retaining the larger concrete memory extent. -/
theorem reusedQ1Slice_geometry
    (mem : ByteArray) (aw product mu : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 2) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hfp : 96 ≤ fp)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp)
    (hmuBase : 96 ≤ mu.toNat) (hmuEnd : mu.toNat + 32 ≤ fp)
    (hmuHeader : mem.readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2))) :
    let allocatedMem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords
    let allocatedAw := q1AllocatedWords aw fp kWords
    let q1 := UInt256.ofNat fp
    let copiedMem := q1CopiedMemory allocatedMem q1 product kWords
    let copiedAw := q1CopiedWords allocatedAw q1 product kWords
    let loadedAw := q1LoadedWords allocatedAw q1 product mu kWords
    let nextFp := fp + wordArrayAllocationSize (kWords + 2)
    ReusedQ1Geometry copiedMem copiedAw loadedAw mu nextFp kWords mem.size := by
  let allocatedMem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords
  let allocatedAw := q1AllocatedWords aw fp kWords
  let q1 := UInt256.ofNat fp
  let copiedMem := q1CopiedMemory allocatedMem q1 product kWords
  let copiedAw := q1CopiedWords allocatedAw q1 product kWords
  let loadedAw := q1LoadedWords allocatedAw q1 product mu kWords
  let nextFp := fp + wordArrayAllocationSize (kWords + 2)
  have hfpNat : q1.toNat = fp := by
    dsimp only [q1]
    exact Modexp.MultiLimbBarrettMulSemantic.q1AllocatedPtr_toNat fp kWords hbound
  have hq1Fit : q1.toNat + 32 < UInt256.size := by
    rw [hfpNat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat q1 hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  have hallocatedSize : allocatedMem.size = mem.size := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.q1AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 2) hmemSize hcapacity
  have hallocatedCoverage : MemoryCovered allocatedMem allocatedAw ∧
      allocatedAw.toNat * 32 < UInt256.size := by
    simpa only [allocatedMem, allocatedAw,
      Modexp.MultiLimbBarrettReused.q1AllocatedMemory, q1AllocatedWords,
      reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords, show kWords + 2 + 0 = kWords + 2 by omega] using
      reusedFunctionInitialState_coverage mem aw fp (kWords + 2) 0 hcovered hawFit
        hmemSize (by simpa only [show kWords + 2 + 0 = kWords + 2 by omega] using hcapacity)
        (by simpa only [show kWords + 2 + 0 = kWords + 2 by omega] using hbound)
  let access := max (fp + 32) (product.toNat + 32 * kWords)
  have haccessFit : access + 32 * (kWords + 1) + 31 < UInt256.size := by
    dsimp only [access]
    have hmargin : 2 ^ 64 + 31 < UInt256.size := by native_decide
    have hsrcLe : product.toNat + 32 * kWords ≤ fp + 32 := by omega
    rw [max_eq_left hsrcLe]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hcopySize : copiedMem.size = mem.size := by
    dsimp only [copiedMem]
    unfold q1CopiedMemory
    rw [hsrc, hdst, hlen, hfpNat]
    have hsrcIn : product.toNat + 32 * kWords + 32 * (kWords + 1) ≤
        allocatedMem.size := by rw [hallocatedSize]; omega
    have hdstIn : fp + 32 + 32 * (kWords + 1) ≤ allocatedMem.size := by
      rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    exact (write_size_of_inBounds_from allocatedMem allocatedMem
      (product.toNat + 32 * kWords) (fp + 32) (32 * (kWords + 1))
      (by omega) hsrcIn hdstIn).trans hallocatedSize
  have hcopiedExpansion := machineM_coverage allocatedMem allocatedAw access
    (32 * (kWords + 1)) hallocatedCoverage.1 hallocatedCoverage.2 haccessFit
  have hcopiedAw : copiedAw =
      UInt256.ofNat (MachineState.M allocatedAw.toNat access (32 * (kWords + 1))) := by
    dsimp only [copiedAw]
    unfold q1CopiedWords
    rw [hsrc, hdst, hlen, hfpNat]
  have hcopiedCovered : MemoryCovered copiedMem copiedAw := by
    unfold MemoryCovered at hcopiedExpansion ⊢
    rw [hcopySize, hcopiedAw, ← hallocatedSize]
    exact hcopiedExpansion.1
  have hcopiedFit : copiedAw.toNat * 32 < UInt256.size := by
    rw [hcopiedAw]
    exact hcopiedExpansion.2
  have hloadedExpansion := machineM_coverage copiedMem copiedAw mu.toNat 32
    hcopiedCovered hcopiedFit (by
      have hmargin : 2 ^ 64 + 31 < UInt256.size := by native_decide
      omega)
  have hloadedAw : loadedAw =
      UInt256.ofNat (MachineState.M copiedAw.toNat mu.toNat 32) := by
    rfl
  have hloadedCovered : MemoryCovered copiedMem loadedAw := by
    rw [hloadedAw]
    exact hloadedExpansion.1
  have hloadedFit : loadedAw.toNat * 32 < UInt256.size := by
    rw [hloadedAw]
    exact hloadedExpansion.2
  have hallocatedRead64 : allocatedMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := by
    simpa only [allocatedMem, nextFp,
      Modexp.MultiLimbBarrettReused.q1AllocatedMemory] using
      reusedWordArrayMemory_read64 mem fp (kWords + 2) hmemSize hfp (by omega) hcapacity
  have hcopyRead64 : copiedMem.readWithPadding 64 32 =
      allocatedMem.readWithPadding 64 32 := by
    dsimp only [copiedMem]
    unfold q1CopiedMemory
    rw [hsrc, hdst, hlen, hfpNat]
    apply write_read_below_gen_from_extend allocatedMem allocatedMem
      (product.toNat + 32 * kWords) (fp + 32) (32 * (kWords + 1)) 64 32
    · omega
    · rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    · rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    · omega
    · rw [hallocatedSize]; omega
    · omega
    · norm_num
  have hallocatedMu : allocatedMem.readWithPadding mu.toNat 32 =
      mem.readWithPadding mu.toNat 32 := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.q1AllocatedMemory] using
      reusedWordArrayMemory_read_below mem fp (kWords + 2) mu.toNat hmemSize
        (by omega) hcapacity hmuBase hmuEnd
  have hcopyMu : copiedMem.readWithPadding mu.toNat 32 =
      allocatedMem.readWithPadding mu.toNat 32 := by
    dsimp only [copiedMem]
    unfold q1CopiedMemory
    rw [hsrc, hdst, hlen, hfpNat]
    apply write_read_below_gen_from_extend allocatedMem allocatedMem
      (product.toNat + 32 * kWords) (fp + 32) (32 * (kWords + 1)) mu.toNat 32
    · omega
    · rw [hallocatedSize]; omega
    · rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    · omega
    · rw [hallocatedSize]; omega
    · omega
    · norm_num
  have hmuActive : ¬ mu ≥ copiedAw * ⟨32⟩ := by
    have hmul : (copiedAw * (⟨32⟩ : UInt256)).toNat = copiedAw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := copiedAw) (b := (⟨32⟩ : UInt256)) hcopiedFit
    intro hge
    have hgeNat : (copiedAw * (⟨32⟩ : UInt256)).toNat ≤ mu.toNat := by simpa using hge
    rw [hmul] at hgeNat
    unfold MemoryCovered at hcopiedCovered
    rw [hcopySize] at hcopiedCovered
    omega
  have hloaded3 : 3 ≤ loadedAw.toNat := by
    unfold MemoryCovered at hloadedCovered
    rw [hcopySize] at hloadedCovered
    omega
  have hloaded64 : ¬ (⟨64⟩ : UInt256) ≥ loadedAw * ⟨32⟩ := by
    have hmul : (loadedAw * (⟨32⟩ : UInt256)).toNat = loadedAw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := loadedAw) (b := (⟨32⟩ : UInt256)) hloadedFit
    intro hge
    have hgeNat : (loadedAw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by simpa using hge
    rw [hmul] at hgeNat
    omega
  exact {
    muInMemory := by rw [hcopySize]; omega
    muActive := hmuActive
    muHeader := by
      rw [hcopyMu, hallocatedMu, hmuHeader]
    covered := hloadedCovered
    activeWordsFit := hloadedFit
    memorySize96 := by rw [hcopySize]; exact hmemSize
    activeWords3 := hloaded3
    activeWords64 := hloaded64
    freePointerRead := hcopyRead64.trans hallocatedRead64
    concreteThrough := by rw [hcopySize]; exact hcapacity
    memorySizeEq := hcopySize
  }

/-- The first product does not touch the persistent Barrett reciprocal header. -/
theorem ScratchInvariant.firstProductMuHeader
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory.readWithPadding
        mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2)) := by
  have hmemSize : 96 ≤ mem.size := by
    have hfpLe : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact valid.freePointerBase.trans (hfpLe.trans valid.scratchConcrete)
  have hcapacity : fp + wordArrayAllocationSize (2 * kWords) ≤ mem.size := by
    have hfirst : fp + wordArrayAllocationSize (2 * kWords) ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp
      omega
    exact hfirst.trans valid.scratchConcrete
  have hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64 := by
    have hfirst : fp + wordArrayAllocationSize (2 * kWords) ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp
      omega
    exact hfirst.trans_lt valid.scratchBound
  have hinitial :
      (reusedFunctionInitialState mem aw fp kWords kWords).memory.readWithPadding
          mu.toNat 32 = mem.readWithPadding mu.toNat 32 := by
    simpa only [reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      show kWords + kWords = 2 * kWords by omega] using
      reusedWordArrayMemory_read_below mem fp (2 * kWords) mu.toNat hmemSize
        (Nat.mul_pos (by decide) valid.wordsPos) hcapacity valid.muBase (by
          have hk := valid.wordsPos
          have hmu := valid.muBeforeScratch
          omega)
  have hframe := reusedFunctionRows_read32_below_result mem aw a b fp kWords kWords
    kWords mu.toNat (by omega) (by have hk := valid.words; omega) valid.covered
    valid.activeWordsFit hmemSize
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hcapacity)
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hbound)
    valid.aBeforeScratch valid.bBeforeScratch
    (by
      have hmuFp : mu.toNat + 32 ≤ fp := by
        have hk := valid.wordsPos
        have hmu := valid.muBeforeScratch
        omega
      have hfpScratch : fp ≤ scratchEnd fp kWords := by
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      exact hmuFp.trans (hfpScratch.trans valid.scratchConcrete))
    (by
      have hk := valid.wordsPos
      have hmu := valid.muBeforeScratch
      omega)
  calc
    (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory.readWithPadding
        mu.toNat 32 =
        (reusedFunctionInitialState mem aw fp kWords kWords).memory.readWithPadding
          mu.toNat 32 := by
          simpa only [Modexp.MultiLimbBarrettReused.firstProductFinal,
            reusedFunctionFinalState] using hframe
    _ = mem.readWithPadding mu.toNat 32 := hinitial
    _ = UInt256.toByteArray (UInt256.ofNat (kWords + 2)) := valid.muHeader

/-- In a reused q1 allocation, the copied `k+1`-word slice is followed by the zero limb written
by the allocator.  Thus the full `k+2`-word operand has the expected shifted product value. -/
theorem reusedQ1Copied_full_value_of_product_value
    (mem : ByteArray) (product : UInt256) (fp kWords productValue : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 2) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp)
    (hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom
        (Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords)
        (product.toNat + 32) (2 * kWords)) = productValue) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom
          (q1CopiedMemory
            (Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords)
            (UInt256.ofNat fp) product kWords)
          (fp + 32) (kWords + 2)) =
      productValue / UInt256.size ^ (kWords - 1) := by
  let allocated := Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords
  let q1 := UInt256.ofNat fp
  let copied := q1CopiedMemory allocated q1 product kWords
  have hallocatedSize : allocated.size = mem.size := by
    simpa only [allocated, Modexp.MultiLimbBarrettReused.q1AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 2) hmemSize hcapacity
  have hq1Nat : q1.toNat = fp := by
    dsimp only [q1]
    exact Modexp.MultiLimbBarrettMulSemantic.q1AllocatedPtr_toNat fp kWords hbound
  have hq1Fit : q1.toNat + 32 < UInt256.size := by
    rw [hq1Nat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsourceIn : product.toNat + 32 * (2 * kWords + 1) ≤ allocated.size := by
    rw [hallocatedSize]
    exact hsource.trans (le_trans (Nat.le_add_right fp _) hcapacity)
  have hdestIn : q1.toNat + 32 ≤ allocated.size := by
    rw [hallocatedSize, hq1Nat]
    apply le_trans _ hcapacity
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hlow := Modexp.MultiLimbBarrettMulSemantic.q1Copied_value_of_product_value
    allocated q1 product kWords productValue hkPos hkWord (by omega) hproductFit hq1Fit
    hsourceIn hdestIn
    (by simpa only [allocated] using hproduct)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat q1 hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  have hlastRead : copied.readWithPadding (fp + 32 + 32 * (kWords + 1)) 32 =
      allocated.readWithPadding (fp + 32 + 32 * (kWords + 1)) 32 := by
    dsimp only [copied]
    unfold q1CopiedMemory
    rw [hsrc, hdst, hlen, hq1Nat]
    apply write_read_above_gen_from allocated allocated
      (product.toNat + 32 * kWords) (fp + 32) (32 * (kWords + 1))
      (fp + 32 + 32 * (kWords + 1)) 32
    · omega
    · rw [hallocatedSize]; omega
    · rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    · omega
    · rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    · omega
    · decide
  have hallocatedLast :
      allocated.readWithPadding (fp + 32 + 32 * (kWords + 1)) 32 =
        ffi.ByteArray.zeroes 32 := by
    simpa only [allocated, Modexp.MultiLimbBarrettReused.q1AllocatedMemory] using
      reusedWordArrayMemory_payload_read mem fp (kWords + 2) (kWords + 1)
        hmemSize (by omega) hcapacity
  have hlast : Modexp.MultiLimbMemoryModel.memoryWordNat copied
      (fp + 32 + 32 * (kWords + 1)) = 0 := by
    unfold Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [hlastRead, hallocatedLast, ← zero_toByteArray_eq_zeroes32,
      fromByteArrayBigEndian_toByteArray]
    rfl
  have hsnoc := Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append
    copied (fp + 32) (kWords + 1)
  rw [show kWords + 1 + 1 = kWords + 2 by omega] at hsnoc
  rw [hq1Nat] at hlow
  rw [hsnoc, Modexp.wordLimbsToNat_append, hlow, hlast]
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 :=
    UInt256.toNat_ofNat_of_lt (by decide)
  simp only [Modexp.wordLimbsToNat, hzeroNat, Nat.zero_add, Nat.mul_zero, Nat.add_zero]

/-- Consecutive limb observations are equal when every corresponding padded word read is equal. -/
theorem memoryWordsFrom_eq_of_readWithPadding
    (left right : ByteArray) (ptr count : Nat)
    (hreads : ∀ i, i < count →
      left.readWithPadding (ptr + 32 * i) 32 =
        right.readWithPadding (ptr + 32 * i) 32) :
    memoryWordsFrom left ptr count = memoryWordsFrom right ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      have hhead := hreads 0 (by omega)
      have htail := ih (ptr + 32) (by
        intro i hi
        simpa only [show ptr + 32 + 32 * i = ptr + 32 * (i + 1) by omega] using
          hreads (i + 1) (by omega))
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [show ptr + 32 * 0 = ptr by omega] at hhead
      rw [hhead, htail]

/-- A complete reused schoolbook call preserves every complete range below its result header. -/
theorem reusedFunctionFinal_words_below
    (mem : ByteArray) (aw aPtr bPtr : UInt256)
    (fp aCount bCount ptr words : Nat)
    (hsum : aCount + bCount ≤ 68)
    (htotalPos : 0 < aCount + bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount).memory ptr words =
      memoryWordsFrom mem ptr words := by
  have hrows := reusedFunctionRows_memoryWords_below_result mem aw aPtr bPtr fp
    aCount bCount aCount ptr words (by rfl) hsum hcovered hawFit hmemSize hcapacity
    hbound haEnd hbEnd hbelow
  have hallocated := reusedFunctionAllocatedMemory_words_below mem fp aCount bCount ptr
    words hmemSize hcapacity htotalPos hptrBase hbelow
  calc
    memoryWordsFrom
        (reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount).memory ptr words =
        memoryWordsFrom (reusedFunctionInitialState mem aw fp aCount bCount).memory
          ptr words := by
            simpa only [reusedFunctionFinalState] using hrows
    _ = memoryWordsFrom mem ptr words := by
      simpa only [reusedFunctionInitialState] using hallocated

/-- Reused q1 allocation and copying preserve every complete persistent word range below the q1
header. -/
theorem reusedQ1CopiedMemory_words_below
    (mem : ByteArray) (product : UInt256) (fp kWords ptr words : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 2) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (q1CopiedMemory
          (Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords)
          (UInt256.ofNat fp) product kWords) ptr words =
      memoryWordsFrom mem ptr words := by
  let allocated := Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords
  let q1 := UInt256.ofNat fp
  have hallocatedSize : allocated.size = mem.size := by
    simpa only [allocated, Modexp.MultiLimbBarrettReused.q1AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 2) hmemSize hcapacity
  have hq1Nat : q1.toNat = fp := by
    dsimp only [q1]
    exact Modexp.MultiLimbBarrettMulSemantic.q1AllocatedPtr_toNat fp kWords hbound
  have hq1Fit : q1.toNat + 32 < UInt256.size := by
    rw [hq1Nat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat q1 hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  have hcopyFrame : memoryWordsFrom
      (q1CopiedMemory allocated q1 product kWords) ptr words =
        memoryWordsFrom allocated ptr words := by
    apply memoryWordsFrom_eq_of_readWithPadding
    intro i hi
    unfold q1CopiedMemory
    rw [hsrc, hdst, hlen, hq1Nat]
    apply write_read_below_gen_from_extend allocated allocated
      (product.toNat + 32 * kWords) (fp + 32) (32 * (kWords + 1))
      (ptr + 32 * i) 32
    · omega
    · rw [hallocatedSize]; omega
    · rw [hallocatedSize]
      apply le_trans _ hcapacity
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · omega
    · rw [hallocatedSize]; omega
    · omega
    · decide
  have hallocatedFrame := reusedFunctionAllocatedMemory_words_below mem fp
    (kWords + 2) 0 ptr words hmemSize
    (by simpa only [show kWords + 2 + 0 = kWords + 2 by omega] using hcapacity)
    (by omega) hptrBase hbelow
  rw [show q1CopiedMemory
      (Modexp.MultiLimbBarrettReused.q1AllocatedMemory mem fp kWords)
      (UInt256.ofNat fp) product kWords = q1CopiedMemory allocated q1 product kWords by rfl]
  rw [hcopyFrame]
  simpa only [allocated, Modexp.MultiLimbBarrettReused.q1AllocatedMemory,
    reusedFunctionAllocatedMemory,
    show kWords + 2 + 0 = kWords + 2 by omega] using hallocatedFrame

/-- The compact scratch invariant supplies the complete in-place q1 slice geometry. -/
theorem ScratchInvariant.q1Geometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let copiedAw := q1CopiedWords q1Aw q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    ReusedQ1Geometry copiedMem copiedAw loadedAw mu secondFp kWords first.memory.size := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1CopiedWords q1Aw q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  have hfirst := valid.firstProductGeometry
  have hscratch := valid.firstProductScratchConcrete
  have hcapacity : q1Fp + wordArrayAllocationSize (kWords + 2) ≤ first.memory.size := by
    apply le_trans _ hscratch
    dsimp only [q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hbound : q1Fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hfpNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp := by
    rw [hfpNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmuEnd : mu.toNat + 32 ≤ q1Fp := by
    dsimp only [q1Fp]
    have hk := valid.wordsPos
    have hmu := valid.muBeforeScratch
    omega
  simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw, loadedAw,
    secondFp] using
    reusedQ1Slice_geometry first.memory first.activeWords (UInt256.ofNat fp) mu q1Fp
      kWords valid.wordsPos
      (lt_of_le_of_lt valid.words (by native_decide : 32 < UInt256.size)) hfirst.covered
      hfirst.activeWordsFit hfirst.memorySize96 hcapacity hbound
      (by dsimp only [q1Fp]; exact valid.freePointerBase.trans (Nat.le_add_right fp _))
      hproductFit hsource valid.muBase hmuEnd valid.firstProductMuHeader

/-- The in-place q1 allocation and copy expose the exact high slice of the first product as the
`k+2`-limb operand consumed by the second multiplication. -/
theorem ScratchInvariant.q1Value
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom copiedMem (q1.toNat + 32) (kWords + 2)) =
      (Modexp.wordLimbsToNat (memoryWordsFrom mem (a.toNat + 32) kWords) *
          Modexp.wordLimbsToNat (memoryWordsFrom mem (b.toNat + 32) kWords)) /
        UInt256.size ^ (kWords - 1) := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  have hfirstGeometry := valid.firstProductGeometry
  have hscratch := valid.firstProductScratchConcrete
  have hcapacity : q1Fp + wordArrayAllocationSize (kWords + 2) ≤ first.memory.size := by
    apply le_trans _ hscratch
    dsimp only [q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hbound : q1Fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Nat : q1.toNat = q1Fp := by
    dsimp only [q1]
    exact Modexp.MultiLimbBarrettMulSemantic.q1AllocatedPtr_toNat q1Fp kWords hbound
  have hproductFrame := reusedFunctionAllocatedMemory_words_below first.memory q1Fp
    (kWords + 2) 0 (fp + 32) (2 * kWords) hfirstGeometry.memorySize96
    (by simpa only [show kWords + 2 + 0 = kWords + 2 by omega] using hcapacity)
    (by omega) (by have hfp := valid.freePointerBase; omega) (by
      dsimp only [q1Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom q1Mem ((UInt256.ofNat fp).toNat + 32) (2 * kWords)) =
        Modexp.wordLimbsToNat (memoryWordsFrom mem (a.toNat + 32) kWords) *
          Modexp.wordLimbsToNat (memoryWordsFrom mem (b.toNat + 32) kWords) := by
    rw [hfpNat]
    rw [show memoryWordsFrom q1Mem (fp + 32) (2 * kWords) =
      memoryWordsFrom first.memory (fp + 32) (2 * kWords) by
        simpa only [q1Mem, Modexp.MultiLimbBarrettReused.q1AllocatedMemory,
          reusedFunctionAllocatedMemory,
          show kWords + 2 + 0 = kWords + 2 by omega] using hproductFrame]
    simpa only [first] using valid.firstProductValue
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hfpNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp := by
    rw [hfpNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hvalue := reusedQ1Copied_full_value_of_product_value first.memory
    (UInt256.ofNat fp) q1Fp kWords
    (Modexp.wordLimbsToNat (memoryWordsFrom mem (a.toNat + 32) kWords) *
      Modexp.wordLimbsToNat (memoryWordsFrom mem (b.toNat + 32) kWords))
    valid.wordsPos (lt_of_le_of_lt valid.words (by native_decide : 32 < UInt256.size))
    hfirstGeometry.memorySize96 hcapacity hbound hproductFit hsource
    (by simpa only [q1Mem] using hproduct)
  have hq1Raw : (UInt256.ofNat q1Fp).toNat = q1Fp := by
    simpa only [q1] using hq1Nat
  simpa only [copiedMem, q1Mem, q1, first, q1Fp, hq1Raw] using hvalue

/-- The complete reused q1 stage preserves every persistent limb range that preceded the scratch
region in the caller's memory. -/
theorem ScratchInvariant.q1WordsBelow
    {I : ExecutionEnv} {fuel fp kWords ptr words : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    memoryWordsFrom copiedMem ptr words = memoryWordsFrom mem ptr words := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  have hfirstGeometry := valid.firstProductGeometry
  have hscratch := valid.firstProductScratchConcrete
  have hcapacity : q1Fp + wordArrayAllocationSize (kWords + 2) ≤ first.memory.size := by
    apply le_trans _ hscratch
    dsimp only [q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hbound : q1Fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hfpNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp := by
    rw [hfpNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Frame := reusedQ1CopiedMemory_words_below first.memory (UInt256.ofNat fp)
    q1Fp kWords ptr words valid.wordsPos
    (lt_of_le_of_lt valid.words (by native_decide : 32 < UInt256.size))
    hfirstGeometry.memorySize96 hcapacity hbound hproductFit hsource hptrBase (by
      dsimp only [q1Fp]
      omega)
  have hfirstFrame := valid.firstProductWordsBelow hptrBase hbelow
  rw [show memoryWordsFrom mem ptr words = memoryWordsFrom first.memory ptr words by
    exact hfirstFrame.symm]
  simpa only [first, q1Fp] using hq1Frame

/-- The q1 geometry supplies every premise of the second reused schoolbook product. -/
theorem ScratchInvariant.secondProductGeometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    ReusedFunctionFinalGeometry q2 q3Fp := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1CopiedWords q1Aw q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  have hq1 := valid.q1Geometry
  have hfirstScratch := valid.firstProductScratchConcrete
  have hcapacity : secondFp + wordArrayAllocationSize (2 * kWords + 4) ≤
      copiedMem.size := by
    rw [hq1.memorySizeEq]
    apply le_trans _ hfirstScratch
    dsimp only [secondFp, q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hbound : secondFp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1Nat : q1.toNat = q1Fp := by
    dsimp only [q1]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1End : q1.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    rw [hq1Nat]
    dsimp only [secondFp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmuEnd : mu.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    dsimp only [secondFp, q1Fp]
    have hmu := valid.muBeforeScratch
    omega
  simpa only [q2, q3Fp, Modexp.MultiLimbBarrettReused.secondProductFinal,
    show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
    reusedFunctionFinal_geometry copiedMem loadedAw q1 mu secondFp (kWords + 2)
      (kWords + 2) (by have hk := valid.words; omega) (by omega) hq1.covered
      hq1.activeWordsFit hq1.memorySize96
      (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
        hcapacity)
      (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
        hbound)
      (by
        dsimp only [secondFp, q1Fp]
        have hfp := valid.freePointerBase
        omega)
      hq1End hmuEnd

/-- The second reused schoolbook multiplication computes the exact product of the copied q1
operand and the persistent Barrett reciprocal. -/
theorem ScratchInvariant.secondProductValue
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom q2.memory (secondFp + 32) (2 * kWords + 4)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom copiedMem (q1.toNat + 32) (kWords + 2)) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom copiedMem (mu.toNat + 32) (kWords + 2)) := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  have hq1 := valid.q1Geometry
  have hscratch := valid.firstProductScratchConcrete
  have hcapacity : secondFp + wordArrayAllocationSize (2 * kWords + 4) ≤
      copiedMem.size := by
    rw [hq1.memorySizeEq]
    apply le_trans _ hscratch
    dsimp only [secondFp, q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hbound : secondFp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1Nat : q1.toNat = q1Fp := by
    dsimp only [q1]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1End : q1.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    rw [hq1Nat]
    dsimp only [secondFp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmuEnd : mu.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    dsimp only [secondFp, q1Fp]
    have hmu := valid.muBeforeScratch
    omega
  simpa only [Modexp.MultiLimbBarrettReused.secondProductFinal,
    show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
    reusedFunctionSchoolbookMul_value_of_input copiedMem loadedAw q1 mu secondFp
      (kWords + 2) (kWords + 2) (by have hk := valid.words; omega) (by omega)
      hq1.covered hq1.activeWordsFit hq1.memorySize96
      (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
        hcapacity)
      (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
        hbound)
      (by
        rw [hq1Nat]
        dsimp only [q1Fp]
        exact valid.freePointerBase.trans (Nat.le_add_right fp _))
      valid.muBase hq1End hmuEnd

/-- Supplying the caller's reciprocal value turns the second executed multiplication into the
pure Barrett q1-by-mu product. -/
theorem ScratchInvariant.secondProductValueOfMu
    {I : ExecutionEnv} {fuel fp kWords muValue : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) = muValue) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom q2.memory (secondFp + 32) (2 * kWords + 4)) =
      ((Modexp.wordLimbsToNat (memoryWordsFrom mem (a.toNat + 32) kWords) *
            Modexp.wordLimbsToNat (memoryWordsFrom mem (b.toNat + 32) kWords)) /
          UInt256.size ^ (kWords - 1)) * muValue := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  have hq1Value := valid.q1Value
  have hmuFrame := valid.q1WordsBelow (ptr := mu.toNat + 32) (words := kWords + 2)
    (by have hmu := valid.muBase; omega) (by
      have hmu := valid.muBeforeScratch
      omega)
  have hmuCopied : Modexp.wordLimbsToNat
      (memoryWordsFrom copiedMem (mu.toNat + 32) (kWords + 2)) = muValue := by
    rw [show memoryWordsFrom copiedMem (mu.toNat + 32) (kWords + 2) =
      memoryWordsFrom mem (mu.toNat + 32) (kWords + 2) by
        simpa only [copiedMem, q1Mem, q1, first, q1Fp] using hmuFrame]
    exact hmuValue
  have hvalue := valid.secondProductValue
  simpa only [q2, secondFp, loadedAw, copiedMem, q1, q1Aw, q1Mem, q1Fp, first,
    hq1Value, hmuCopied] using hvalue

/-- The complete second reused product preserves every persistent range below the original
scratch base. -/
theorem ScratchInvariant.secondProductWordsBelow
    {I : ExecutionEnv} {fuel fp kWords ptr words : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    memoryWordsFrom q2.memory ptr words = memoryWordsFrom mem ptr words := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  have hq1 := valid.q1Geometry
  have hscratch := valid.firstProductScratchConcrete
  have hcapacity : secondFp + wordArrayAllocationSize (2 * kWords + 4) ≤
      copiedMem.size := by
    rw [hq1.memorySizeEq]
    apply le_trans _ hscratch
    dsimp only [secondFp, q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hbound : secondFp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1Nat : q1.toNat = q1Fp := by
    dsimp only [q1]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1End : q1.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    rw [hq1Nat]
    dsimp only [secondFp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmuEnd : mu.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    dsimp only [secondFp, q1Fp]
    have hmu := valid.muBeforeScratch
    omega
  have hrows := reusedFunctionRows_memoryWords_below_result copiedMem loadedAw q1 mu
    secondFp (kWords + 2) (kWords + 2) (kWords + 2) ptr words (by omega)
    (by have hk := valid.words; omega) hq1.covered hq1.activeWordsFit hq1.memorySize96
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hcapacity)
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hbound)
    hq1End hmuEnd (by dsimp only [secondFp, q1Fp]; omega)
  have hallocated := reusedFunctionAllocatedMemory_words_below copiedMem secondFp
    (kWords + 2) (kWords + 2) ptr words hq1.memorySize96
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hcapacity)
    (by omega) hptrBase (by dsimp only [secondFp, q1Fp]; omega)
  have hq1Frame := valid.q1WordsBelow hptrBase hbelow
  calc
    memoryWordsFrom q2.memory ptr words =
        memoryWordsFrom
          (reusedFunctionInitialState copiedMem loadedAw secondFp (kWords + 2)
            (kWords + 2)).memory ptr words := by
          simpa only [q2, Modexp.MultiLimbBarrettReused.secondProductFinal,
            reusedFunctionFinalState] using hrows
    _ = memoryWordsFrom copiedMem ptr words := by
      simpa only [reusedFunctionInitialState] using hallocated
    _ = memoryWordsFrom mem ptr words := by
      simpa only [copiedMem, q1Mem, q1, first, q1Fp] using hq1Frame

/-- A q3 copy performed inside materialized scratch divides the preserved q2 product by
`B^(k+1)`, exactly as in the fresh-allocation model. -/
theorem reusedQ3Copied_value_of_product_value
    (mem : ByteArray) (q2 : UInt256) (fp kWords productValue : Nat)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 3) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp)
    (hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom
        (Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords)
        (q2.toNat + 32) (2 * kWords + 4)) = productValue) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom
          (q3CopiedMemory
            (Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords)
            (UInt256.ofNat fp) q2 kWords)
          (fp + 32) (kWords + 3)) =
      productValue / UInt256.size ^ (kWords + 1) := by
  let allocated := Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords
  let q3 := UInt256.ofNat fp
  have hallocatedSize : allocated.size = mem.size := by
    simpa only [allocated, Modexp.MultiLimbBarrettReused.q3AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 3) hmemSize hcapacity
  have hq3Nat : q3.toNat = fp := by
    dsimp only [q3]
    exact Modexp.MultiLimbBarrettMulSemantic.q3AllocatedPtr_toNat fp kWords hbound
  have hq3Fit : q3.toNat + 32 < UInt256.size := by
    rw [hq3Nat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsourceIn : q2.toNat + 32 * (2 * kWords + 5) ≤ allocated.size := by
    rw [hallocatedSize]
    exact hsource.trans (le_trans (Nat.le_add_right fp _) hcapacity)
  have hdestIn : q3.toNat + 32 ≤ allocated.size := by
    rw [hallocatedSize, hq3Nat]
    apply le_trans _ hcapacity
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hvalue := Modexp.MultiLimbBarrettMulSemantic.q3Copied_value_of_product_value
    allocated q3 q2 kWords productValue (by omega) hq2Fit hq3Fit hsourceIn hdestIn
    (by simpa only [allocated] using hproduct)
  rw [hq3Nat] at hvalue
  simpa only [allocated, q3] using hvalue

/-- Reused q3 allocation and copying preserve every complete persistent range below the q3
header. -/
theorem reusedQ3CopiedMemory_words_below
    (mem : ByteArray) (q2 : UInt256) (fp kWords ptr words : Nat)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 3) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (q3CopiedMemory
          (Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords)
          (UInt256.ofNat fp) q2 kWords) ptr words =
      memoryWordsFrom mem ptr words := by
  let allocated := Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords
  let q3 := UInt256.ofNat fp
  have hallocatedSize : allocated.size = mem.size := by
    simpa only [allocated, Modexp.MultiLimbBarrettReused.q3AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 3) hmemSize hcapacity
  have hq3Nat : q3.toNat = fp := by
    dsimp only [q3]
    exact Modexp.MultiLimbBarrettMulSemantic.q3AllocatedPtr_toNat fp kWords hbound
  have hq3Fit : q3.toNat + 32 < UInt256.size := by
    rw [hq3Nat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q3CopySourceWord_toNat q2 kWords
    (by omega) hq2Fit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q3CopyDestinationWord_toNat q3 hq3Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q3CopyLengthWord_toNat kWords (by omega)
  have hcopyFrame : memoryWordsFrom (q3CopiedMemory allocated q3 q2 kWords) ptr words =
      memoryWordsFrom allocated ptr words := by
    apply memoryWordsFrom_eq_of_readWithPadding
    intro i hi
    unfold q3CopiedMemory
    rw [hsrc, hdst, hlen, hq3Nat]
    apply write_read_below_gen_from_extend allocated allocated
      (q2.toNat + 32 * (kWords + 2)) (fp + 32) (32 * (kWords + 3))
      (ptr + 32 * i) 32
    · omega
    · rw [hallocatedSize]; omega
    · rw [hallocatedSize]
      apply le_trans _ hcapacity
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · omega
    · rw [hallocatedSize]; omega
    · omega
    · decide
  have hallocatedFrame := reusedFunctionAllocatedMemory_words_below mem fp
    (kWords + 3) 0 ptr words hmemSize
    (by simpa only [show kWords + 3 + 0 = kWords + 3 by omega] using hcapacity)
    (by omega) hptrBase hbelow
  rw [show q3CopiedMemory
      (Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords)
      (UInt256.ofNat fp) q2 kWords = q3CopiedMemory allocated q3 q2 kWords by rfl]
  rw [hcopyFrame]
  simpa only [allocated, Modexp.MultiLimbBarrettReused.q3AllocatedMemory,
    reusedFunctionAllocatedMemory,
    show kWords + 3 + 0 = kWords + 3 by omega] using hallocatedFrame

structure ReusedQ3Geometry
    (copiedMem : ByteArray) (copiedAw : UInt256) (nextFp backingSize : Nat) : Prop where
  covered : MemoryCovered copiedMem copiedAw
  activeWordsFit : copiedAw.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ copiedMem.size
  activeWords3 : 3 ≤ copiedAw.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ copiedAw * ⟨32⟩
  freePointerRead : copiedMem.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat nextFp)
  concreteThrough : nextFp ≤ copiedMem.size
  memorySizeEq : copiedMem.size = backingSize

set_option maxHeartbeats 500000 in
/-- The q3 allocation and full payload copy can execute in place over materialized scratch. -/
theorem reusedQ3Slice_geometry
    (mem : ByteArray) (aw q2 : UInt256) (fp kWords : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 3) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hfp : 96 ≤ fp)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp) :
    let allocatedMem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords
    let allocatedAw := q3AllocatedWords aw fp kWords
    let q3 := UInt256.ofNat fp
    let copiedMem := q3CopiedMemory allocatedMem q3 q2 kWords
    let copiedAw := q3CopiedWords allocatedAw q3 q2 kWords
    let nextFp := fp + wordArrayAllocationSize (kWords + 3)
    ReusedQ3Geometry copiedMem copiedAw nextFp mem.size := by
  let allocatedMem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory mem fp kWords
  let allocatedAw := q3AllocatedWords aw fp kWords
  let q3 := UInt256.ofNat fp
  let copiedMem := q3CopiedMemory allocatedMem q3 q2 kWords
  let copiedAw := q3CopiedWords allocatedAw q3 q2 kWords
  let nextFp := fp + wordArrayAllocationSize (kWords + 3)
  have hfpNat : q3.toNat = fp := by
    dsimp only [q3]
    exact Modexp.MultiLimbBarrettMulSemantic.q3AllocatedPtr_toNat fp kWords hbound
  have hq3Fit : q3.toNat + 32 < UInt256.size := by
    rw [hfpNat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q3CopySourceWord_toNat q2 kWords
    (by omega) hq2Fit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q3CopyDestinationWord_toNat q3 hq3Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q3CopyLengthWord_toNat kWords (by omega)
  have hallocatedSize : allocatedMem.size = mem.size := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.q3AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 3) hmemSize hcapacity
  have hallocatedCoverage : MemoryCovered allocatedMem allocatedAw ∧
      allocatedAw.toNat * 32 < UInt256.size := by
    simpa only [allocatedMem, allocatedAw,
      Modexp.MultiLimbBarrettReused.q3AllocatedMemory, q3AllocatedWords,
      reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords, show kWords + 3 + 0 = kWords + 3 by omega] using
      reusedFunctionInitialState_coverage mem aw fp (kWords + 3) 0 hcovered hawFit
        hmemSize (by simpa only [show kWords + 3 + 0 = kWords + 3 by omega] using hcapacity)
        (by simpa only [show kWords + 3 + 0 = kWords + 3 by omega] using hbound)
  have hcopySize : copiedMem.size = mem.size := by
    dsimp only [copiedMem]
    unfold q3CopiedMemory
    rw [hsrc, hdst, hlen, hfpNat]
    have hsrcIn : q2.toNat + 32 * (kWords + 2) + 32 * (kWords + 3) ≤
        allocatedMem.size := by rw [hallocatedSize]; omega
    have hdstIn : fp + 32 + 32 * (kWords + 3) ≤ allocatedMem.size := by
      rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    exact (write_size_of_inBounds_from allocatedMem allocatedMem
      (q2.toNat + 32 * (kWords + 2)) (fp + 32) (32 * (kWords + 3))
      (by omega) hsrcIn hdstIn).trans hallocatedSize
  let access := max (fp + 32) (q2.toNat + 32 * (kWords + 2))
  have haccessFit : access + 32 * (kWords + 3) + 31 < UInt256.size := by
    dsimp only [access]
    have hsrcLe : q2.toNat + 32 * (kWords + 2) ≤ fp + 32 := by omega
    rw [max_eq_left hsrcLe]
    have hmargin : 2 ^ 64 + 31 < UInt256.size := by native_decide
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hexpansion := machineM_coverage allocatedMem allocatedAw access
    (32 * (kWords + 3)) hallocatedCoverage.1 hallocatedCoverage.2 haccessFit
  have hcopiedAw : copiedAw =
      UInt256.ofNat (MachineState.M allocatedAw.toNat access (32 * (kWords + 3))) := by
    dsimp only [copiedAw]
    unfold q3CopiedWords
    rw [hsrc, hdst, hlen, hfpNat]
  have hcopiedCovered : MemoryCovered copiedMem copiedAw := by
    unfold MemoryCovered at hexpansion ⊢
    rw [hcopySize, hcopiedAw, ← hallocatedSize]
    exact hexpansion.1
  have hcopiedFit : copiedAw.toNat * 32 < UInt256.size := by
    rw [hcopiedAw]
    exact hexpansion.2
  have hallocatedRead64 : allocatedMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := by
    simpa only [allocatedMem, nextFp,
      Modexp.MultiLimbBarrettReused.q3AllocatedMemory] using
      reusedWordArrayMemory_read64 mem fp (kWords + 3) hmemSize hfp (by omega) hcapacity
  have hcopyRead64 : copiedMem.readWithPadding 64 32 =
      allocatedMem.readWithPadding 64 32 := by
    dsimp only [copiedMem]
    unfold q3CopiedMemory
    rw [hsrc, hdst, hlen, hfpNat]
    apply write_read_below_gen_from_extend allocatedMem allocatedMem
      (q2.toNat + 32 * (kWords + 2)) (fp + 32) (32 * (kWords + 3)) 64 32
    · omega
    · rw [hallocatedSize]; omega
    · rw [hallocatedSize]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hcapacity
      omega
    · omega
    · rw [hallocatedSize]; omega
    · omega
    · norm_num
  have hcopied3 : 3 ≤ copiedAw.toNat := by
    unfold MemoryCovered at hcopiedCovered
    rw [hcopySize] at hcopiedCovered
    omega
  have hcopied64 : ¬ (⟨64⟩ : UInt256) ≥ copiedAw * ⟨32⟩ := by
    have hmul : (copiedAw * (⟨32⟩ : UInt256)).toNat = copiedAw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := copiedAw) (b := (⟨32⟩ : UInt256)) hcopiedFit
    intro hge
    have hgeNat : (copiedAw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by simpa using hge
    rw [hmul] at hgeNat
    omega
  exact {
    covered := hcopiedCovered
    activeWordsFit := hcopiedFit
    memorySize96 := by rw [hcopySize]; exact hmemSize
    activeWords3 := hcopied3
    activeWords64 := hcopied64
    freePointerRead := hcopyRead64.trans hallocatedRead64
    concreteThrough := by rw [hcopySize]; exact hcapacity
    memorySizeEq := hcopySize
  }

/-- The complete scratch extent remains concrete after the second product. -/
theorem ScratchInvariant.secondProductScratchConcrete
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    scratchEnd fp kWords ≤
      (Modexp.MultiLimbBarrettReused.secondProductFinal
        copiedMem loadedAw q1 mu secondFp kWords).memory.size := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  have hq1 := valid.q1Geometry
  have hfirstScratch := valid.firstProductScratchConcrete
  have hcopiedScratch : scratchEnd fp kWords ≤ copiedMem.size := by
    rw [hq1.memorySizeEq]
    exact hfirstScratch
  have hcapacity : secondFp + wordArrayAllocationSize (2 * kWords + 4) ≤
      copiedMem.size := by
    apply le_trans _ hcopiedScratch
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hbound : secondFp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1Nat : q1.toNat = q1Fp := by
    dsimp only [q1]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq1End : q1.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    rw [hq1Nat]
    dsimp only [secondFp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmuEnd : mu.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    dsimp only [secondFp, q1Fp]
    have hmu := valid.muBeforeScratch
    omega
  have hrows := reusedFunctionRows_coverage copiedMem loadedAw q1 mu secondFp
    (kWords + 2) (kWords + 2) (kWords + 2) (by omega) hq1.covered
    hq1.activeWordsFit hq1.memorySize96
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hcapacity)
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hbound)
    hq1End hmuEnd
  have hinitialSize :
      (reusedFunctionInitialState copiedMem loadedAw secondFp (kWords + 2)
        (kWords + 2)).memory.size = copiedMem.size := by
    simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      reusedFunctionAllocatedMemory_size copiedMem secondFp (kWords + 2) (kWords + 2)
        hq1.memorySize96 (by
          simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
            hcapacity)
  have hmono : copiedMem.size ≤
      (Modexp.MultiLimbBarrettReused.secondProductFinal
        copiedMem loadedAw q1 mu secondFp kWords).memory.size := by
    rw [← hinitialSize]
    simpa only [Modexp.MultiLimbBarrettReused.secondProductFinal,
      reusedFunctionFinalState] using hrows.2.2
  exact hcopiedScratch.trans hmono

/-- The second product and compact scratch invariant supply the in-place q3 slice geometry. -/
theorem ScratchInvariant.q3Geometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    ReusedQ3Geometry copiedQ3Mem copiedQ3Aw r2Fp q2.memory.size := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  have hq2 := valid.secondProductGeometry
  have hscratch := valid.secondProductScratchConcrete
  have hcapacity : q3Fp + wordArrayAllocationSize (kWords + 3) ≤ q2.memory.size := by
    apply le_trans _ hscratch
    dsimp only [q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hbound : q3Fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) <
      UInt256.size := by
    rw [hsecondNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤ q3Fp := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  simpa only [q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp] using
    reusedQ3Slice_geometry q2.memory q2.activeWords (UInt256.ofNat secondFp) q3Fp
      kWords hq2.covered hq2.activeWordsFit hq2.memorySize96 hcapacity hbound
      (by
        dsimp only [q3Fp, secondFp, q1Fp]
        have hfp := valid.freePointerBase
        omega)
      hq2Fit hsource

/-- The complete reused product-and-slice prefix exposes the pure Barrett q3 estimate in the low
`k+1` limbs consumed by truncated multiplication. -/
theorem ScratchInvariant.q3Value
    {I : ExecutionEnv} {fuel fp kWords aValue bValue nValue x : Nat}
    {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
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
    (hx : x < UInt256.size ^ (2 * kWords)) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom copiedQ3Mem (q3.toNat + 32) (kWords + 1)) =
      Modexp.barrettQ3 kWords nValue x := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  have hq2Geometry := valid.secondProductGeometry
  have hscratch := valid.secondProductScratchConcrete
  have hcapacity : q3Fp + wordArrayAllocationSize (kWords + 3) ≤ q2.memory.size := by
    apply le_trans _ hscratch
    dsimp only [q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hbound : q3Fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Nat : q3.toNat = q3Fp := by
    dsimp only [q3]
    exact Modexp.MultiLimbBarrettMulSemantic.q3AllocatedPtr_toNat q3Fp kWords hbound
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) <
      UInt256.size := by
    rw [hsecondNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤ q3Fp := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq2ValueRaw := valid.secondProductValueOfMu hmuValue
  have hq2Value : Modexp.wordLimbsToNat
      (memoryWordsFrom q2.memory (secondFp + 32) (2 * kWords + 4)) =
        (x / UInt256.size ^ (kWords - 1)) *
          (UInt256.size ^ (2 * kWords) / nValue) := by
    simpa only [q2, secondFp, loadedAw, copiedMem, q1, q1Aw, q1Mem, q1Fp, first,
      haValue, hbValue, hxValue] using hq2ValueRaw
  have hq2Frame := reusedFunctionAllocatedMemory_words_below q2.memory q3Fp
    (kWords + 3) 0 (secondFp + 32) (2 * kWords + 4) hq2Geometry.memorySize96
    (by simpa only [show kWords + 3 + 0 = kWords + 3 by omega] using hcapacity)
    (by omega) (by
      dsimp only [secondFp, q1Fp]
      have hfp := valid.freePointerBase
      omega) (by
        dsimp only [q3Fp]
        unfold wordArrayAllocationSize wordArrayPayloadSize
        omega)
  have hq2AllocatedValue : Modexp.wordLimbsToNat
      (memoryWordsFrom q3Mem ((UInt256.ofNat secondFp).toNat + 32)
        (2 * kWords + 4)) =
        (x / UInt256.size ^ (kWords - 1)) *
          (UInt256.size ^ (2 * kWords) / nValue) := by
    rw [hsecondNat]
    rw [show memoryWordsFrom q3Mem (secondFp + 32) (2 * kWords + 4) =
      memoryWordsFrom q2.memory (secondFp + 32) (2 * kWords + 4) by
        simpa only [q3Mem, Modexp.MultiLimbBarrettReused.q3AllocatedMemory,
          reusedFunctionAllocatedMemory,
          show kWords + 3 + 0 = kWords + 3 by omega] using hq2Frame]
    exact hq2Value
  have hfull := reusedQ3Copied_value_of_product_value q2.memory
    (UInt256.ofNat secondFp) q3Fp kWords
    ((x / UInt256.size ^ (kWords - 1)) *
      (UInt256.size ^ (2 * kWords) / nValue))
    hq2Geometry.memorySize96 hcapacity hbound hq2Fit hsource
    (by simpa only [q3Mem] using hq2AllocatedValue)
  have hfullBarrett : Modexp.wordLimbsToNat
      (memoryWordsFrom copiedQ3Mem (q3.toNat + 32) (kWords + 3)) =
        Modexp.barrettQ3 kWords nValue x := by
    rw [hq3Nat]
    simpa only [copiedQ3Mem, q3Mem, q3, Modexp.barrettQ3] using hfull
  exact Modexp.MultiLimbBarrettMulSemantic.q3Copied_low_value copiedQ3Mem q3 kWords
    nValue x valid.wordsPos hnNormalized hx hfullBarrett

/-- The complete reused q3 allocation and copy preserve every persistent range below the original
scratch base. -/
theorem ScratchInvariant.q3WordsBelow
    {I : ExecutionEnv} {fuel fp kWords ptr words : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    memoryWordsFrom copiedQ3Mem ptr words = memoryWordsFrom mem ptr words := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  have hq2Geometry := valid.secondProductGeometry
  have hscratch := valid.secondProductScratchConcrete
  have hcapacity : q3Fp + wordArrayAllocationSize (kWords + 3) ≤ q2.memory.size := by
    apply le_trans _ hscratch
    dsimp only [q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hbound : q3Fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) <
      UInt256.size := by
    rw [hsecondNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsource : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤ q3Fp := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq3Frame := reusedQ3CopiedMemory_words_below q2.memory
    (UInt256.ofNat secondFp) q3Fp kWords ptr words hq2Geometry.memorySize96 hcapacity
    hbound hq2Fit hsource hptrBase (by dsimp only [q3Fp, secondFp, q1Fp]; omega)
  have hq2Frame := valid.secondProductWordsBelow hptrBase hbelow
  rw [show memoryWordsFrom mem ptr words = memoryWordsFrom q2.memory ptr words by
    exact hq2Frame.symm]
  simpa only [q2, q3Fp] using hq3Frame

structure ReusedTruncatedGeometry
    (final : TruncatedOuterState) (nextFp : Nat) : Prop where
  covered : MemoryCovered final.memory final.activeWords
  activeWordsFit : final.activeWords.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ final.memory.size
  activeWords3 : 3 ≤ final.activeWords.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩
  freePointerRead : final.memory.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat nextFp)

/-- Any complete range ending at the r2 header is preserved by every truncated row, including
when the backing memory extends beyond the logical r2 allocation. -/
theorem reusedTruncatedRows_words_below
    (q3 n r2 : UInt256) (kWords ptr words : Nat) (state : TruncatedOuterState)
    (hstateIndex : state.i = 0) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ state.memory.size)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size)
    (hr2Bound : r2.toNat + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hbelow : ptr + 32 * words ≤ r2.toNat + 32) :
    memoryWordsFrom
        (truncatedRowsIterate q3 n r2 kWords (kWords + 1) state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q state).i = q := by
    rw [truncatedRowsIterate_i, hstateIndex, Nat.zero_add]
  have hindices (limit : Nat) (hlimit : limit ≤ kWords + 1) :
      ∀ q, q < limit →
        (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hcoverage (q : Nat) (hq : q ≤ kWords + 1) :=
    Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_coverage
      q3 n r2 kWords q state hk (hindices q hq) hcovered hawFit
      hq3Fit hnFit hr2Fit hr2Bound
  have hbases : ∀ q, q < kWords + 1 →
      32 ≤ (truncatedRowsIterate q3 n r2 kWords q state).memory.size := by
    intro q hq
    exact hbase.trans (hcoverage q (by omega)).2.2
  exact Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_memoryWords_below
    q3 n r2 kWords (kWords + 1) ptr words state
    (hindices (kWords + 1) (by rfl)) hbases hr2Bound hbelow

set_option maxHeartbeats 500000 in
/-- Reused r2 allocation and all truncated rows establish the correction-tail geometry. -/
theorem reusedTruncated_geometry
    (mem : ByteArray) (aw q3 n : UInt256) (fp kWords : Nat)
    (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hcapacity : fp + wordArrayAllocationSize (kWords + 1) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hfp : 96 ≤ fp)
    (hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size) :
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory mem fp kWords
    let allocatedAw := r2AllocatedWords aw fp kWords
    let r2 := UInt256.ofNat fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    ReusedTruncatedGeometry final (fp + wordArrayAllocationSize (kWords + 1)) := by
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory mem fp kWords
  let allocatedAw := r2AllocatedWords aw fp kWords
  let r2 := UInt256.ofNat fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let nextFp := fp + wordArrayAllocationSize (kWords + 1)
  have hfpNat : r2.toNat = fp := by
    dsimp only [r2]
    apply UInt256.toNat_ofNat_of_lt
    exact (show fp < 2 ^ 64 by omega).trans (by decide)
  have hallocatedSize : allocatedMem.size = mem.size := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using
      reusedWordArrayMemory_size mem fp (kWords + 1) hmemSize hcapacity
  have hallocatedCoverage : MemoryCovered allocatedMem allocatedAw ∧
      allocatedAw.toNat * 32 < UInt256.size := by
    simpa only [allocatedMem, allocatedAw,
      Modexp.MultiLimbBarrettReused.r2AllocatedMemory, r2AllocatedWords,
      reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords, show kWords + 1 + 0 = kWords + 1 by omega] using
      reusedFunctionInitialState_coverage mem aw fp (kWords + 1) 0 hcovered hawFit
        hmemSize (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hcapacity)
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hbound)
  have hallocatedRead : allocatedMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := by
    simpa only [allocatedMem, nextFp,
      Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using
      reusedWordArrayMemory_read64 mem fp (kWords + 1) hmemSize hfp (by omega) hcapacity
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hfpNat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega : fp + 32 * (kWords + 3) < 2 ^ 64 + 32) (by decide)
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q initial).i = q := by
    simpa only [initial, Nat.zero_add] using
      truncatedRowsIterate_i q3 n r2 kWords q initial
  have hindices : ∀ q, q < kWords + 1 →
      (truncatedRowsIterate q3 n r2 kWords q initial).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hfinalCoverage :=
    Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_coverage
      q3 n r2 kWords (kWords + 1) initial
    hk hindices
    (by simpa only [initial, allocatedMem, allocatedAw] using hallocatedCoverage.1)
    (by simpa only [initial, allocatedMem, allocatedAw] using hallocatedCoverage.2)
    hq3Fit hnFit hr2Fit (by simpa only [r2, hfpNat] using hbound)
  have hfinalCovered : MemoryCovered final.memory final.activeWords := by
    simpa only [final] using hfinalCoverage.1
  have hfinalFit : final.activeWords.toNat * 32 < UInt256.size := by
    simpa only [final] using hfinalCoverage.2.1
  have hfinalSize : 96 ≤ final.memory.size := by
    have hmono : initial.memory.size ≤ final.memory.size := by
      simpa only [final] using hfinalCoverage.2.2
    have hinitialSize : initial.memory.size = mem.size := by
      simpa only [initial] using hallocatedSize
    rw [hinitialSize] at hmono
    omega
  have hfinal3 : 3 ≤ final.activeWords.toNat := by
    unfold MemoryCovered at hfinalCovered
    omega
  have hfinal64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩ := by
    have hmul : (final.activeWords * (⟨32⟩ : UInt256)).toNat =
        final.activeWords.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := final.activeWords) (b := (⟨32⟩ : UInt256)) hfinalFit
    intro hge
    have hgeNat : (final.activeWords * (⟨32⟩ : UInt256)).toNat ≤ 64 := by simpa using hge
    rw [hmul] at hgeNat
    omega
  have hframe := Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_read32_below
    q3 n r2 kWords (kWords + 1) 64 initial
    hk hindices
    (by
      have hinitialSize : initial.memory.size = mem.size := by
        simpa only [initial] using hallocatedSize
      rw [hinitialSize]
      omega)
    (by simpa only [initial, allocatedMem, allocatedAw] using hallocatedCoverage.1)
    (by simpa only [initial, allocatedMem, allocatedAw] using hallocatedCoverage.2)
    hq3Fit hnFit hr2Fit (by simpa only [r2, hfpNat] using hbound)
    (by rw [hfpNat]; omega)
  exact {
    covered := hfinalCovered
    activeWordsFit := hfinalFit
    memorySize96 := hfinalSize
    activeWords3 := hfinal3
    activeWords64 := hfinal64
    freePointerRead := by
      calc
        final.memory.readWithPadding 64 32 = initial.memory.readWithPadding 64 32 := by
          simpa only [final] using hframe
        _ = allocatedMem.readWithPadding 64 32 := rfl
        _ = UInt256.toByteArray (UInt256.ofNat nextFp) := hallocatedRead
  }

/-- The compact invariant supplies the reused r2 allocation and complete truncated-product
geometry used by the correction tail. -/
theorem ScratchInvariant.truncatedGeometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      copiedQ3Mem r2Fp kWords
    let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    ReusedTruncatedGeometry final (r2Fp + wordArrayAllocationSize (kWords + 1)) := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
    copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  have hq3 := valid.q3Geometry
  have hscratch := valid.secondProductScratchConcrete
  have hcapacity : r2Fp + wordArrayAllocationSize (kWords + 1) ≤ copiedQ3Mem.size := by
    rw [hq3.memorySizeEq]
    apply le_trans _ hscratch
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hbound : r2Fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Nat : q3.toNat = q3Fp := by
    dsimp only [q3]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hq3Nat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    apply lt_of_le_of_lt valid.nBeforeScratch
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  simpa only [allocatedMem, allocatedAw, r2, initial, final] using
    reusedTruncated_geometry copiedQ3Mem copiedQ3Aw q3 n r2Fp kWords valid.words
      hq3.covered hq3.activeWordsFit hq3.memorySize96 hcapacity hbound
      (by
        dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
        have hfp := valid.freePointerBase
        omega)
      hq3Fit hnFit

/-- Truncated rows only write inside the already-materialized scratch region, so the complete
backing extent remains concrete through the result allocation range. -/
theorem ScratchInvariant.truncatedScratchConcrete
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      copiedQ3Mem r2Fp kWords
    let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    scratchEnd fp kWords ≤
      (truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial).memory.size := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
    copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  have hq3 := valid.q3Geometry
  have hsecondScratch := valid.secondProductScratchConcrete
  have hcapacity : r2Fp + wordArrayAllocationSize (kWords + 1) ≤ copiedQ3Mem.size := by
    rw [hq3.memorySizeEq]
    apply le_trans _ hsecondScratch
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hbound : r2Fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hallocatedSize : allocatedMem.size = copiedQ3Mem.size := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using
      reusedWordArrayMemory_size copiedQ3Mem r2Fp (kWords + 1) hq3.memorySize96 hcapacity
  have hallocatedCoverage : MemoryCovered allocatedMem allocatedAw ∧
      allocatedAw.toNat * 32 < UInt256.size := by
    simpa only [allocatedMem, allocatedAw,
      Modexp.MultiLimbBarrettReused.r2AllocatedMemory, r2AllocatedWords,
      reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords, show kWords + 1 + 0 = kWords + 1 by omega] using
      reusedFunctionInitialState_coverage copiedQ3Mem copiedQ3Aw r2Fp (kWords + 1) 0
        hq3.covered hq3.activeWordsFit hq3.memorySize96
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hcapacity)
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hbound)
  have hr2Nat : r2.toNat = r2Fp := by
    dsimp only [r2]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Nat : q3.toNat = q3Fp := by
    dsimp only [q3]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hq3Nat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    apply lt_of_le_of_lt valid.nBeforeScratch
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hr2Nat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega : r2Fp + 32 * (kWords + 3) < 2 ^ 64 + 32) (by decide)
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q initial).i = q := by
    simpa only [initial, Nat.zero_add] using
      truncatedRowsIterate_i q3 n r2 kWords q initial
  have hindices : ∀ q, q < kWords + 1 →
      (truncatedRowsIterate q3 n r2 kWords q initial).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hcoverage :=
    Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_coverage
      q3 n r2 kWords (kWords + 1) initial valid.words hindices
      (by simpa only [initial] using hallocatedCoverage.1)
      (by simpa only [initial] using hallocatedCoverage.2)
      hq3Fit hnFit hr2Fit (by simpa only [r2, hr2Nat] using hbound)
  have hinitialScratch : scratchEnd fp kWords ≤ initial.memory.size := by
    change scratchEnd fp kWords ≤ allocatedMem.size
    rw [hallocatedSize, hq3.memorySizeEq]
    exact hsecondScratch
  exact hinitialScratch.trans (by simpa only [initial] using hcoverage.2.2)

/-- Every complete range below the q1 header in first-product memory survives all later Barrett
scratch stages through the truncated-product result. -/
theorem ScratchInvariant.truncatedWordsFromFirstBelowQ1
    {I : ExecutionEnv} {fuel fp kWords ptr words : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hptrBase : 96 ≤ ptr)
    (hbelow : ptr + 32 * words ≤ fp + wordArrayAllocationSize (2 * kWords)) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      copiedQ3Mem r2Fp kWords
    let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    memoryWordsFrom final.memory ptr words = memoryWordsFrom first.memory ptr words := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
    copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  have hfirstGeometry := valid.firstProductGeometry
  have hq1Geometry := valid.q1Geometry
  have hq2Geometry := valid.secondProductGeometry
  have hq3Geometry := valid.q3Geometry
  have hfirstScratch := valid.firstProductScratchConcrete
  have hsecondScratch := valid.secondProductScratchConcrete
  have hq1Capacity : q1Fp + wordArrayAllocationSize (kWords + 2) ≤ first.memory.size := by
    apply le_trans _ hfirstScratch
    dsimp only [q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hq1Bound : q1Fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hsecondCapacity : secondFp + wordArrayAllocationSize (2 * kWords + 4) ≤
      copiedMem.size := by
    rw [hq1Geometry.memorySizeEq]
    apply le_trans _ hfirstScratch
    dsimp only [secondFp, q1Fp, first]
    unfold scratchEnd callResultFp
    omega
  have hsecondBound : secondFp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Capacity : q3Fp + wordArrayAllocationSize (kWords + 3) ≤ q2.memory.size := by
    apply le_trans _ hsecondScratch
    dsimp only [q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hq3Bound : q3Fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hr2Capacity : r2Fp + wordArrayAllocationSize (kWords + 1) ≤ copiedQ3Mem.size := by
    rw [hq3Geometry.memorySizeEq]
    apply le_trans _ hsecondScratch
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hr2Bound : r2Fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Nat : q1.toNat = q1Fp := by
    dsimp only [q1]
    exact Modexp.MultiLimbBarrettMulSemantic.q1AllocatedPtr_toNat q1Fp kWords hq1Bound
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Nat : q3.toNat = q3Fp := by
    dsimp only [q3]
    exact Modexp.MultiLimbBarrettMulSemantic.q3AllocatedPtr_toNat q3Fp kWords hq3Bound
  have hr2Nat : r2.toNat = r2Fp := by
    dsimp only [r2]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hfpNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Source : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp := by
    rw [hfpNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Frame := reusedQ1CopiedMemory_words_below first.memory (UInt256.ofNat fp)
    q1Fp kWords ptr words valid.wordsPos
    (lt_of_le_of_lt valid.words (by native_decide : 32 < UInt256.size))
    hfirstGeometry.memorySize96 hq1Capacity hq1Bound hproductFit hq1Source hptrBase hbelow
  have hq1End : q1.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    rw [hq1Nat]
    dsimp only [secondFp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmuEnd : mu.toNat + 32 * (kWords + 2 + 1) ≤ secondFp := by
    dsimp only [secondFp, q1Fp]
    have hmu := valid.muBeforeScratch
    omega
  have hsecondFrame := reusedFunctionFinal_words_below copiedMem loadedAw q1 mu secondFp
    (kWords + 2) (kWords + 2) ptr words (by have hk := valid.words; omega) (by omega)
    hq1Geometry.covered hq1Geometry.activeWordsFit hq1Geometry.memorySize96
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hsecondCapacity)
    (by simpa only [show kWords + 2 + (kWords + 2) = 2 * kWords + 4 by omega] using
      hsecondBound)
    hq1End hmuEnd hptrBase (by dsimp only [secondFp, q1Fp]; omega)
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) <
      UInt256.size := by
    rw [hsecondNat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq3Source : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤ q3Fp := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq3Frame := reusedQ3CopiedMemory_words_below q2.memory
    (UInt256.ofNat secondFp) q3Fp kWords ptr words hq2Geometry.memorySize96 hq3Capacity
    hq3Bound hq2Fit hq3Source hptrBase (by dsimp only [q3Fp, secondFp, q1Fp]; omega)
  have hr2Frame := reusedFunctionAllocatedMemory_words_below copiedQ3Mem r2Fp
    (kWords + 1) 0 ptr words hq3Geometry.memorySize96
    (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hr2Capacity)
    (by omega) hptrBase (by dsimp only [r2Fp, q3Fp, secondFp, q1Fp]; omega)
  have hallocatedCoverage : MemoryCovered allocatedMem allocatedAw ∧
      allocatedAw.toNat * 32 < UInt256.size := by
    simpa only [allocatedMem, allocatedAw,
      Modexp.MultiLimbBarrettReused.r2AllocatedMemory, r2AllocatedWords,
      reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords, show kWords + 1 + 0 = kWords + 1 by omega] using
      reusedFunctionInitialState_coverage copiedQ3Mem copiedQ3Aw r2Fp (kWords + 1) 0
        hq3Geometry.covered hq3Geometry.activeWordsFit hq3Geometry.memorySize96
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hr2Capacity)
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hr2Bound)
  have hallocatedSize : allocatedMem.size = copiedQ3Mem.size := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using
      reusedWordArrayMemory_size copiedQ3Mem r2Fp (kWords + 1)
        hq3Geometry.memorySize96 hr2Capacity
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hq3Nat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    apply lt_of_le_of_lt valid.nBeforeScratch
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hr2Nat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hr2Bound
      omega : r2Fp + 32 * (kWords + 3) < 2 ^ 64 + 32) (by decide)
  have htruncatedFrame := reusedTruncatedRows_words_below q3 n r2 kWords ptr words initial
    (by rfl) valid.words (by simpa only [initial] using hallocatedCoverage.1)
    (by simpa only [initial] using hallocatedCoverage.2)
    (by
      change 32 ≤ allocatedMem.size
      rw [hallocatedSize]
      have h96 := hq3Geometry.memorySize96
      omega)
    hq3Fit hnFit hr2Fit (by simpa only [r2, hr2Nat] using hr2Bound) (by
      rw [hr2Nat]
      dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
      omega)
  calc
    memoryWordsFrom final.memory ptr words = memoryWordsFrom allocatedMem ptr words := by
      simpa only [final, initial] using htruncatedFrame
    _ = memoryWordsFrom copiedQ3Mem ptr words := by
      simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory,
        reusedFunctionAllocatedMemory,
        show kWords + 1 + 0 = kWords + 1 by omega] using hr2Frame
    _ = memoryWordsFrom q2.memory ptr words := by
      simpa only [copiedQ3Mem, q3, q3Mem, q3Aw, q3Fp] using hq3Frame
    _ = memoryWordsFrom copiedMem ptr words := by
      simpa only [q2, Modexp.MultiLimbBarrettReused.secondProductFinal] using hsecondFrame
    _ = memoryWordsFrom first.memory ptr words := by
      simpa only [copiedMem, q1Mem, q1] using hq1Frame

/-- The low `k+1` limbs of the concrete first product survive every reused scratch stage and
therefore still contain the pure product reduced modulo `B^(k+1)` when correction starts. -/
theorem ScratchInvariant.truncatedProductValue
    {I : ExecutionEnv} {fuel fp kWords aValue bValue x : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (haValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (a.toNat + 32) kWords) = aValue)
    (hbValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (b.toNat + 32) kWords) = bValue)
    (hxValue : aValue * bValue = x) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      copiedQ3Mem r2Fp kWords
    let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory
          ((UInt256.ofNat fp).toNat + 32) (kWords + 1)) =
      x % UInt256.size ^ (kWords + 1) := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hfull : Modexp.wordLimbsToNat
      (memoryWordsFrom first.memory (fp + 32) (2 * kWords)) = x := by
    simpa only [first, haValue, hbValue, hxValue] using valid.firstProductValue
  have hlow := Modexp.MultiLimbBarrettMulSemantic.firstProduct_low_value
    first.memory (UInt256.ofNat fp) kWords x valid.wordsPos (by
      simpa only [hfpNat] using hfull)
  have hframe := valid.truncatedWordsFromFirstBelowQ1
    (ptr := (UInt256.ofNat fp).toNat + 32) (words := kWords + 1)
    (by
      rw [hfpNat]
      have hbase := valid.freePointerBase
      omega)
    (by
      rw [hfpNat]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      have hk := valid.wordsPos
      omega)
  change Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory ((UInt256.ofNat fp).toNat + 32) (kWords + 1)) =
    x % UInt256.size ^ (kWords + 1)
  rw [show memoryWordsFrom final.memory ((UInt256.ofNat fp).toNat + 32) (kWords + 1) =
      memoryWordsFrom first.memory ((UInt256.ofNat fp).toNat + 32) (kWords + 1) by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final] using hframe]
  exact hlow

/-- Every persistent word range below the scratch pointer survives the complete reused Barrett
arithmetic prefix, from the first product through the truncated product. -/
theorem ScratchInvariant.truncatedPersistentWords
    {I : ExecutionEnv} {fuel fp kWords ptr words : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      copiedQ3Mem r2Fp kWords
    let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    memoryWordsFrom final.memory ptr words = memoryWordsFrom mem ptr words := by
  have hprefix := valid.truncatedWordsFromFirstBelowQ1 hptrBase (by
    apply le_trans hbelow
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega)
  have hfirst := valid.firstProductWordsBelow hptrBase hbelow
  calc
    _ = memoryWordsFrom
        (Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords).memory
        ptr words := hprefix
    _ = memoryWordsFrom mem ptr words := hfirst

/-- The reused r2 allocation and concrete truncated rows compute the low `k+1` limbs of the pure
Barrett estimate times the modulus. -/
theorem ScratchInvariant.truncatedValue
    {I : ExecutionEnv} {fuel fp kWords aValue bValue nValue x : Nat}
    {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
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
    (hx : x < UInt256.size ^ (2 * kWords)) :
    let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
      copiedMem loadedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      copiedQ3Mem r2Fp kWords
    let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
    let r2 := UInt256.ofNat r2Fp
    let initial : TruncatedOuterState :=
      { i := 0, memory := allocatedMem, activeWords := allocatedAw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
      (Modexp.barrettQ3 kWords nValue x * nValue) %
        UInt256.size ^ (kWords + 1) := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
    copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  have hq3Geometry := valid.q3Geometry
  have hscratch := valid.secondProductScratchConcrete
  have hcapacity : r2Fp + wordArrayAllocationSize (kWords + 1) ≤ copiedQ3Mem.size := by
    rw [hq3Geometry.memorySizeEq]
    apply le_trans _ hscratch
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp, q2]
    unfold scratchEnd callResultFp
    omega
  have hbound : r2Fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hr2Nat : r2.toNat = r2Fp := by
    dsimp only [r2]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Nat : q3.toNat = q3Fp := by
    dsimp only [q3]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hq3Fit : q3.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hq3Nat]
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size := by
    apply lt_of_le_of_lt valid.nBeforeScratch
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hr2Fit : r2.toNat + 32 * (kWords + 3) < UInt256.size := by
    rw [hr2Nat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega : r2Fp + 32 * (kWords + 3) < 2 ^ 64 + 32) (by decide)
  have hallocatedCoverage : MemoryCovered allocatedMem allocatedAw ∧
      allocatedAw.toNat * 32 < UInt256.size := by
    simpa only [allocatedMem, allocatedAw,
      Modexp.MultiLimbBarrettReused.r2AllocatedMemory, r2AllocatedWords,
      reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords, show kWords + 1 + 0 = kWords + 1 by omega] using
      reusedFunctionInitialState_coverage copiedQ3Mem copiedQ3Aw r2Fp (kWords + 1) 0
        hq3Geometry.covered hq3Geometry.activeWordsFit hq3Geometry.memorySize96
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hcapacity)
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hbound)
  have hallocatedSize : allocatedMem.size = copiedQ3Mem.size := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using
      reusedWordArrayMemory_size copiedQ3Mem r2Fp (kWords + 1)
        hq3Geometry.memorySize96 hcapacity
  have hcopiedSize96 : 96 ≤ copiedQ3Mem.size := by
    simpa only [copiedQ3Mem, q3, q3Mem, q3Aw, q3Fp, q2, secondFp, loadedAw,
      copiedMem, q1, q1Aw, q1Mem, q1Fp, first] using hq3Geometry.memorySize96
  have hinitialZero : memoryWordsFrom allocatedMem (r2Fp + 32) (kWords + 1) =
      List.replicate (kWords + 1) (⟨0⟩ : UInt256) := by
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory,
      reusedFunctionAllocatedMemory,
      show kWords + 1 + 0 = kWords + 1 by omega] using
      reusedFunctionAllocatedMemory_payload_zero copiedQ3Mem r2Fp (kWords + 1) 0
        hq3Geometry.memorySize96
        (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hcapacity)
  have hinitialLowZero : memoryWordsFrom allocatedMem (r2Fp + 32) kWords =
      List.replicate kWords (⟨0⟩ : UInt256) := by
    apply memoryWordsFrom_eq_replicate_zero_of_reads
    intro i hi
    simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using
      reusedWordArrayMemory_payload_read copiedQ3Mem r2Fp (kWords + 1) i
        hq3Geometry.memorySize96 (by omega) hcapacity
  have htopZero : Modexp.MultiLimbMemoryModel.memoryWordNat allocatedMem
      (r2Fp + 32 * (kWords + 1)) = 0 := by
    unfold Modexp.MultiLimbMemoryModel.memoryWordNat
    have hread := reusedWordArrayMemory_payload_read copiedQ3Mem r2Fp (kWords + 1)
      kWords hq3Geometry.memorySize96 (by omega) hcapacity
    rw [show r2Fp + 32 + 32 * kWords = r2Fp + 32 * (kWords + 1) by omega] at hread
    rw [show allocatedMem.readWithPadding (r2Fp + 32 * (kWords + 1)) 32 =
      ffi.ByteArray.zeroes 32 by
        simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory] using hread]
    rw [← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
    rfl
  have hq3Frame := reusedFunctionAllocatedMemory_words_below copiedQ3Mem r2Fp
    (kWords + 1) 0 (q3.toNat + 32) (kWords + 1) hq3Geometry.memorySize96
    (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hcapacity)
    (by omega) (by rw [hq3Nat]; have hfp := valid.freePointerBase; omega) (by
      rw [hq3Nat]
      dsimp only [r2Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hnFrame := reusedFunctionAllocatedMemory_words_below copiedQ3Mem r2Fp
    (kWords + 1) 0 (n.toNat + 32) kWords hq3Geometry.memorySize96
    (by simpa only [show kWords + 1 + 0 = kWords + 1 by omega] using hcapacity)
    (by omega) (by have hn := valid.nBase; omega) (by
      dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
      have hn := valid.nBeforeScratch
      omega)
  have hq3Value := valid.q3Value haValue hbValue hnValue hmuValue hxValue
    hnNormalized hx
  have hsemantic :=
    Modexp.MultiLimbBarrettTruncatedMulSemantic.truncatedRows_value_of_zero_payload
      q3 n r2 kWords initial (by rfl) valid.wordsPos valid.words
      (by simpa only [initial] using hallocatedCoverage.1)
      (by simpa only [initial] using hallocatedCoverage.2)
      (by
        change 32 ≤ allocatedMem.size
        rw [hallocatedSize]
        exact (by omega : 32 ≤ copiedQ3Mem.size))
      (by simpa only [initial, hr2Nat] using hinitialZero)
      (by simpa only [initial, hr2Nat] using hinitialLowZero)
      (by simpa only [initial, hr2Nat] using htopZero)
      hq3Fit hnFit hr2Fit (by simpa only [r2, hr2Nat] using hbound)
      (by
        rw [hq3Nat, hr2Nat]
        dsimp only [r2Fp]
        unfold wordArrayAllocationSize wordArrayPayloadSize
        omega)
      (by
        rw [hr2Nat]
        dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
        have hn := valid.nBeforeScratch
        omega)
  change Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
    (Modexp.barrettQ3 kWords nValue x * nValue) % UInt256.size ^ (kWords + 1)
  rw [show Modexp.wordLimbsToNat
      (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
    (Modexp.wordLimbsToNat
        (memoryWordsFrom allocatedMem (q3.toNat + 32) (kWords + 1)) *
      Modexp.wordLimbsToNat (memoryWordsFrom allocatedMem (n.toNat + 32) kWords)) %
      UInt256.size ^ (kWords + 1) by
        simpa only [final, initial] using hsemantic]
  rw [show memoryWordsFrom allocatedMem (q3.toNat + 32) (kWords + 1) =
      memoryWordsFrom copiedQ3Mem (q3.toNat + 32) (kWords + 1) by
        simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory,
          reusedFunctionAllocatedMemory,
          show kWords + 1 + 0 = kWords + 1 by omega] using hq3Frame]
  rw [show memoryWordsFrom allocatedMem (n.toNat + 32) kWords =
      memoryWordsFrom copiedQ3Mem (n.toNat + 32) kWords by
        simpa only [allocatedMem, Modexp.MultiLimbBarrettReused.r2AllocatedMemory,
          reusedFunctionAllocatedMemory,
          show kWords + 1 + 0 = kWords + 1 by omega] using hnFrame]
  rw [show Modexp.wordLimbsToNat
      (memoryWordsFrom copiedQ3Mem (q3.toNat + 32) (kWords + 1)) =
        Modexp.barrettQ3 kWords nValue x by
      simpa only [copiedQ3Mem, q3, q3Mem, q3Aw, q3Fp, q2, secondFp, loadedAw,
        copiedMem, q1, q1Aw, q1Mem, q1Fp, first] using hq3Value]
  have hnCopiedFrame := valid.q3WordsBelow (ptr := n.toNat + 32) (words := kWords)
    (by have hn := valid.nBase; omega) (by
      have hn := valid.nBeforeScratch
      omega)
  have hnCopied : Modexp.wordLimbsToNat
      (memoryWordsFrom copiedQ3Mem (n.toNat + 32) kWords) = nValue := by
    rw [show memoryWordsFrom copiedQ3Mem (n.toNat + 32) kWords =
      memoryWordsFrom mem (n.toNat + 32) kWords by
        simpa only [copiedQ3Mem, q3, q3Mem, q3Aw, q3Fp, q2, secondFp, loadedAw,
          copiedMem, q1, q1Aw, q1Mem, q1Fp, first] using hnCopiedFrame]
    exact hnValue
  rw [hnCopied]

/-- One complete selected reused Barrett call computes the ordinary remainder in its concrete
result array.  All multiplication, slicing, truncated multiplication, subtraction, and selected
correction paths are connected to the pure model. -/
theorem ScratchInvariant.selectedResultValue
    {I : ExecutionEnv} {fuel fp kWords aValue bValue nValue x : Nat}
    {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
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
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory
          ((UInt256.ofNat (callResultFp fp kWords)).toNat + 32) kWords) =
      x % nValue := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let resultMem := Modexp.MultiLimbBarrettReused.resultAllocatedMemory
    final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  have hgeometry : ReusedTruncatedGeometry final resultFp := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final, resultFp] using valid.truncatedGeometry
  have hscratch : scratchEnd fp kWords ≤ final.memory.size := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final] using valid.truncatedScratchConcrete
  have hresultCapacity : resultFp + wordArrayAllocationSize kWords ≤ final.memory.size := by
    apply le_trans _ hscratch
    dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hresultBound : resultFp + wordArrayAllocationSize kWords < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hresultCoverage : MemoryCovered resultMem resultAw ∧
      resultAw.toNat * 32 < UInt256.size := by
    simpa only [resultMem, Modexp.MultiLimbBarrettReused.resultAllocatedMemory,
      resultAw, resultAllocatedWords, reusedFunctionInitialState,
      reusedFunctionAllocatedMemory, functionAllocatedWords,
      show kWords + 0 = kWords by omega] using
      reusedFunctionInitialState_coverage final.memory final.activeWords resultFp kWords 0
        hgeometry.covered hgeometry.activeWordsFit hgeometry.memorySize96
        (by simpa only [show kWords + 0 = kWords by omega] using hresultCapacity)
        (by simpa only [show kWords + 0 = kWords by omega] using hresultBound)
  have hresultSize : resultMem.size = final.memory.size := by
    simpa only [resultMem, Modexp.MultiLimbBarrettReused.resultAllocatedMemory] using
      reusedWordArrayMemory_size final.memory resultFp kWords
        hgeometry.memorySize96 hresultCapacity
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hr2Nat : r2.toNat = r2Fp := by
    dsimp only [r2]
    apply UInt256.toNat_ofNat_of_lt
    apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp := by
    apply UInt256.toNat_ofNat_of_lt
    exact (show resultFp < 2 ^ 64 by omega).trans (by decide)
  have hresultFrame (ptr words : Nat) (hbase : 96 ≤ ptr)
      (hbelow : ptr + 32 * words ≤ resultFp) :
      memoryWordsFrom resultMem ptr words = memoryWordsFrom final.memory ptr words := by
    simpa only [resultMem, Modexp.MultiLimbBarrettReused.resultAllocatedMemory,
      reusedFunctionAllocatedMemory, show kWords + 0 = kWords by omega] using
      reusedFunctionAllocatedMemory_words_below final.memory resultFp kWords 0 ptr words
        hgeometry.memorySize96
        (by simpa only [show kWords + 0 = kWords by omega] using hresultCapacity)
        (by have hk := valid.wordsPos; omega) hbase hbelow
  have hproductFinal := valid.truncatedProductValue haValue hbValue hxValue
  have hproductValue : Modexp.wordLimbsToNat
      (memoryWordsFrom resultMem ((UInt256.ofNat fp).toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1) := by
    rw [hresultFrame ((UInt256.ofNat fp).toNat + 32) (kWords + 1) (by
      rw [hfpNat]
      have hbase := valid.freePointerBase
      omega) (by
      rw [hfpNat]
      dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)]
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final] using hproductFinal
  have hr2Final := valid.truncatedValue haValue hbValue hnValue hmuValue hxValue
    hnNormalized hx
  have hr2Value : Modexp.wordLimbsToNat
      (memoryWordsFrom resultMem (r2.toNat + 32) (kWords + 1)) =
        (Modexp.barrettQ3 kWords nValue x * nValue) %
          UInt256.size ^ (kWords + 1) := by
    rw [hresultFrame (r2.toNat + 32) (kWords + 1) (by
      rw [hr2Nat]
      dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
      have hbase := valid.freePointerBase
      omega) (by
      rw [hr2Nat]
      dsimp only [resultFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)]
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final] using hr2Final
  have hnFinalWords := valid.truncatedPersistentWords
    (ptr := n.toNat + 32) (words := kWords)
    (by have hn := valid.nBase; omega) (by have hn := valid.nBeforeScratch; omega)
  have hnResultValue : Modexp.wordLimbsToNat
      (memoryWordsFrom resultMem (n.toNat + 32) kWords) = nValue := by
    rw [hresultFrame (n.toNat + 32) kWords (by have hn := valid.nBase; omega) (by
      dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
      have hn := valid.nBeforeScratch
      omega)]
    rw [show memoryWordsFrom final.memory (n.toNat + 32) kWords =
        memoryWordsFrom mem (n.toNat + 32) kWords by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
        q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
        allocatedAw, r2, initial, final] using hnFinalWords]
    exact hnValue
  have hselect : Modexp.MultiLimbBarrettReduction.selectBarrettReductionTail
      fuel resultMem resultAw (UInt256.ofNat fp) n r2 (UInt256.ofNat resultFp) kWords =
        some selected := by
    simpa only [selectCall, first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw,
      secondFp, q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp,
      allocatedMem, allocatedAw, r2, initial, final, resultFp, resultMem, resultAw,
      Modexp.MultiLimbBarrettReused.selectBarrettFromTruncated] using valid.selection
  have hsemantic :=
    Modexp.MultiLimbBarrettReduction.selectedBarrettReductionTail_resultValue_eq_mod
      valid.wordsPos (lt_of_le_of_lt valid.words (by native_decide : 32 < 2 ^ 251))
      (product := UInt256.ofNat fp) (n := n) (r2 := r2)
      (result := UInt256.ofNat resultFp) (mem := resultMem) (aw := resultAw)
      (nValue := nValue) (x := x) (selected := selected)
      (by
        rw [hfpNat]
        apply lt_of_le_of_lt _ (valid.scratchBound.trans (by decide))
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega)
      (by
        rw [hr2Nat]
        apply lt_of_le_of_lt _ (valid.scratchBound.trans (by decide))
        dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega)
      (by
        apply lt_of_le_of_lt _ (valid.scratchBound.trans (by decide))
        have hn := valid.nBeforeScratch
        unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
        omega)
      (by
        rw [hresultNat]
        apply lt_trans _ (by decide : 2 ^ 64 < UInt256.size)
        unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound
        have hk := valid.wordsPos
        omega)
      (by rw [hfpNat, hresultSize]; apply le_trans _ hscratch;
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize; omega)
      (by rw [hr2Nat, hresultSize]; apply le_trans _ hscratch;
          dsimp only [r2Fp, q3Fp, secondFp, q1Fp];
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize; omega)
      (by
        rw [hresultSize]
        apply le_trans (b := fp)
        · have hn := valid.nBeforeScratch
          omega
        · apply le_trans _ hscratch
          unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
          omega)
      (by
        rw [hresultNat, hresultSize]
        apply le_trans _ hresultCapacity
        unfold wordArrayAllocationSize wordArrayPayloadSize
        have hk := valid.wordsPos
        omega)
      (by
        rw [hfpNat, hr2Nat]
        dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
        unfold wordArrayAllocationSize wordArrayPayloadSize
        omega)
      (by rw [hr2Nat]; dsimp only [r2Fp, q3Fp, secondFp, q1Fp];
          have hn := valid.nBeforeScratch; omega)
      hresultCoverage.1 hresultCoverage.2 hnPos hnNormalized hnFits hx
      (by exact hnResultValue) hproductValue hr2Value hselect
  simpa only [resultFp, r2Fp, q3Fp, secondFp, q1Fp, callResultFp] using hsemantic

/-- A complete selected reused call preserves covered materialized scratch and every persistent
word range below the caller's scratch pointer. -/
theorem ScratchInvariant.selectedStateGeometry
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    MemoryCovered selected.memory selected.activeWords /\
      selected.activeWords.toNat * 32 < UInt256.size /\
      scratchEnd fp kWords <= selected.memory.size /\
      forall ptr words, 96 <= ptr -> ptr + 32 * words <= fp ->
        memoryWordsFrom selected.memory ptr words = memoryWordsFrom mem ptr words := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let resultMem := Modexp.MultiLimbBarrettReused.resultAllocatedMemory
    final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  let subtractionFinal := subtractionIterate (UInt256.ofNat fp) r2 (kWords + 1)
    subtractionInitial
  have hgeometry : ReusedTruncatedGeometry final resultFp := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final, resultFp] using valid.truncatedGeometry
  have hscratch : scratchEnd fp kWords <= final.memory.size := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final] using valid.truncatedScratchConcrete
  have hresultCapacity : resultFp + wordArrayAllocationSize kWords <= final.memory.size := by
    apply le_trans _ hscratch
    dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hresultBound : resultFp + wordArrayAllocationSize kWords < 2 ^ 64 := by
    apply lt_of_le_of_lt _ valid.scratchBound
    dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
    unfold scratchEnd callResultFp
    omega
  have hresultCoverage : MemoryCovered resultMem resultAw /\
      resultAw.toNat * 32 < UInt256.size := by
    simpa only [resultMem, Modexp.MultiLimbBarrettReused.resultAllocatedMemory,
      resultAw, resultAllocatedWords, reusedFunctionInitialState,
      reusedFunctionAllocatedMemory, functionAllocatedWords,
      show kWords + 0 = kWords by omega] using
      reusedFunctionInitialState_coverage final.memory final.activeWords resultFp kWords 0
        hgeometry.covered hgeometry.activeWordsFit hgeometry.memorySize96
        (by simpa only [show kWords + 0 = kWords by omega] using hresultCapacity)
        (by simpa only [show kWords + 0 = kWords by omega] using hresultBound)
  have hresultSize : resultMem.size = final.memory.size := by
    simpa only [resultMem, Modexp.MultiLimbBarrettReused.resultAllocatedMemory] using
      reusedWordArrayMemory_size final.memory resultFp kWords
        hgeometry.memorySize96 hresultCapacity
  have hfpNat : (UInt256.ofNat fp).toNat = fp := by
    apply UInt256.toNat_ofNat_of_lt
    exact (show fp < 2 ^ 64 by
      apply lt_of_le_of_lt _ valid.scratchBound
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega).trans (by decide)
  have hr2Nat : r2.toNat = r2Fp := by
    dsimp only [r2]
    apply UInt256.toNat_ofNat_of_lt
    exact (show r2Fp < 2 ^ 64 by
      apply lt_of_le_of_lt _ valid.scratchBound
      dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega).trans (by decide)
  have hresultNat : (UInt256.ofNat resultFp).toNat = resultFp := by
    apply UInt256.toNat_ofNat_of_lt
    exact (show resultFp < 2 ^ 64 by omega).trans (by decide)
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * (kWords + 2) + 31 <
      UInt256.size := by
    rw [hfpNat]
    exact lt_of_le_of_lt (by
      apply le_trans _ valid.scratchBound.le
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) (by norm_num [UInt256.size])
  have hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size := by
    rw [hr2Nat]
    exact lt_of_le_of_lt (by
      apply le_trans _ valid.scratchBound.le
      dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) (by norm_num [UInt256.size])
  have hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size := by
    exact lt_of_le_of_lt (by
      apply le_trans _ valid.scratchBound.le
      have hn := valid.nBeforeScratch
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) (by norm_num [UInt256.size])
  have hproductMem : (UInt256.ofNat fp).toNat + 32 * (kWords + 2) <= resultMem.size := by
    rw [hfpNat, hresultSize]
    exact le_trans (by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hscratch
  have hr2Mem : r2.toNat + 32 * (kWords + 2) <= resultMem.size := by
    rw [hr2Nat, hresultSize]
    exact le_trans (by
      dsimp only [r2Fp, q3Fp, secondFp, q1Fp]
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hscratch
  have hnMem : n.toNat + 32 * (kWords + 1) <= resultMem.size := by
    rw [hresultSize]
    apply le_trans (b := fp)
    · have hn := valid.nBeforeScratch
      omega
    · apply le_trans _ hscratch
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
  have hsubtraction := subtractionIterate_coverage_size (kWords + 1)
    (UInt256.ofNat fp) r2 subtractionInitial
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hproductFit)
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hr2Fit)
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hproductMem)
    (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hr2Mem)
    (by simpa only [subtractionInitial, subtractionInitialState] using hresultCoverage.1)
    (by simpa only [subtractionInitial, subtractionInitialState] using hresultCoverage.2)
  have hsubtractionSize : subtractionFinal.memory.size = resultMem.size := by
    simpa only [subtractionFinal, subtractionInitial, subtractionInitialState] using
      hsubtraction.2.2
  have htailSelect : Modexp.MultiLimbBarrettReduction.selectBarrettReductionTail
      fuel resultMem resultAw (UInt256.ofNat fp) n r2 (UInt256.ofNat resultFp) kWords =
        some selected := by
    simpa only [selectCall, first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw,
      secondFp, q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp,
      allocatedMem, allocatedAw, r2, initial, final, resultFp, resultMem, resultAw,
      Modexp.MultiLimbBarrettReused.selectBarrettFromTruncated] using valid.selection
  have hcorrectionSelect : selectBarrettCorrection fuel subtractionFinal.memory
      subtractionFinal.activeWords n r2 (UInt256.ofNat resultFp) kWords = some selected := by
    simpa only [Modexp.MultiLimbBarrettReduction.selectBarrettReductionTail,
      Modexp.MultiLimbBarrettReduction.subtractionFinal, subtractionFinal,
      subtractionInitial, subtractionInitialState] using htailSelect
  have hcorrection := selectedBarrettCorrection_coverage_size
    (mem := subtractionFinal.memory) (aw := subtractionFinal.activeWords)
    (n := n) (r2 := r2) (result := UInt256.ofNat resultFp)
    (kWords := kWords) (selected := selected)
    valid.wordsPos (lt_of_le_of_lt valid.words (by native_decide : 32 < 2 ^ 251))
    hr2Fit hnFit
    (by rw [hresultNat]; exact (show resultFp + 32 < UInt256.size by
      exact (show resultFp + 32 < 2 ^ 64 by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound
        omega).trans (by decide)))
    (by rw [hsubtractionSize]; exact hr2Mem)
    (by rw [hsubtractionSize]; exact hnMem)
    (by
      rw [hresultNat, hsubtractionSize, hresultSize]
      have hc := hresultCapacity
      unfold wordArrayAllocationSize wordArrayPayloadSize at hc
      omega)
    (by
      rw [hresultNat]
      apply lt_trans (b := 2 ^ 64 + 31)
      · unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound
        omega
      · norm_num [UInt256.size])
    (by simpa only [subtractionFinal] using hsubtraction.1)
    (by simpa only [subtractionFinal] using hsubtraction.2.1)
    hcorrectionSelect
  refine ⟨hcorrection.1, hcorrection.2.1, ?_, ?_⟩
  · rw [hcorrection.2.2, hsubtractionSize, hresultSize]
    exact hscratch
  · intro ptr words hptrBase hbelow
    have hprefix := valid.truncatedPersistentWords hptrBase hbelow
    have hresultFrame : memoryWordsFrom resultMem ptr words =
        memoryWordsFrom final.memory ptr words := by
      simpa only [resultMem, Modexp.MultiLimbBarrettReused.resultAllocatedMemory,
        reusedFunctionAllocatedMemory, show kWords + 0 = kWords by omega] using
        reusedFunctionAllocatedMemory_words_below final.memory resultFp kWords 0 ptr words
          hgeometry.memorySize96
          (by simpa only [show kWords + 0 = kWords by omega] using hresultCapacity)
          (by have hk := valid.wordsPos; omega) hptrBase (by
            dsimp only [resultFp, r2Fp, q3Fp, secondFp, q1Fp]
            omega)
    have hsubFrame : memoryWordsFrom subtractionFinal.memory ptr words =
        memoryWordsFrom resultMem ptr words := by
      have hframe := subtractionIterate_memoryWords_below (kWords + 1)
        (UInt256.ofNat fp) r2 subtractionInitial ptr words
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hproductFit)
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hr2Fit)
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hproductMem)
        (by simpa only [subtractionInitial, subtractionInitialState, Nat.zero_add] using hr2Mem)
        (by simpa only [subtractionInitial, subtractionInitialState] using hresultCoverage.1)
        (by simpa only [subtractionInitial, subtractionInitialState] using hresultCoverage.2)
        (by rw [hr2Nat]; omega)
      simpa only [subtractionFinal, subtractionInitial] using hframe
    have hcorrectionFrame := selectedBarrettCorrection_memoryWords_below
      (mem := subtractionFinal.memory) (aw := subtractionFinal.activeWords)
      (n := n) (r2 := r2) (result := UInt256.ofNat resultFp)
      (kWords := kWords) (ptr := ptr) (words := words) (selected := selected)
      valid.wordsPos (lt_of_le_of_lt valid.words (by native_decide : 32 < 2 ^ 251))
      hr2Fit hnFit
      (by rw [hresultNat]; exact (show resultFp + 32 < UInt256.size by
        exact (show resultFp + 32 < 2 ^ 64 by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hresultBound
          omega).trans (by decide)))
      (by rw [hsubtractionSize]; exact hr2Mem)
      (by rw [hsubtractionSize]; exact hnMem)
      (by
        rw [hresultNat, hsubtractionSize, hresultSize]
        have hc := hresultCapacity
        unfold wordArrayAllocationSize wordArrayPayloadSize at hc
        omega)
      (by rw [hr2Nat, hresultNat]; dsimp only [resultFp]; omega)
      (by simpa only [subtractionFinal] using hsubtraction.1)
      (by simpa only [subtractionFinal] using hsubtraction.2.1)
      (by rw [hr2Nat]; omega) hcorrectionSelect
    calc
      memoryWordsFrom selected.memory ptr words =
          memoryWordsFrom subtractionFinal.memory ptr words := hcorrectionFrame
      _ = memoryWordsFrom resultMem ptr words := hsubFrame
      _ = memoryWordsFrom final.memory ptr words := hresultFrame
      _ = memoryWordsFrom mem ptr words := by
        simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
          q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
          allocatedAw, r2, initial, final] using hprefix

structure CallValid (I : ExecutionEnv) (fuel : Nat) (mem : ByteArray)
    (aw a b n mu : UInt256) (fp kWords : Nat) (selected : BarrettCorrectionSelection) : Prop where
  wordsPos : 0 < kWords
  words : kWords ≤ 32
  firstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64
  q1Bound : fp + wordArrayAllocationSize (2 * kWords) +
    wordArrayAllocationSize (kWords + 2) < 2 ^ 64
  secondBound : fp + wordArrayAllocationSize (2 * kWords) +
    wordArrayAllocationSize (kWords + 2) +
    wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64
  q3Bound : fp + wordArrayAllocationSize (2 * kWords) +
    wordArrayAllocationSize (kWords + 2) +
    wordArrayAllocationSize (2 * kWords + 4) +
    wordArrayAllocationSize (kWords + 3) < 2 ^ 64
  r2Bound : fp + wordArrayAllocationSize (2 * kWords) +
    wordArrayAllocationSize (kWords + 2) +
    wordArrayAllocationSize (2 * kWords + 4) +
    wordArrayAllocationSize (kWords + 3) +
    wordArrayAllocationSize (kWords + 1) < 2 ^ 64
  resultBound : callResultFp fp kWords + wordArrayAllocationSize kWords < 2 ^ 64
  calldataBound : I.calldata.size < 2 ^ 64
  freePointerBase : 96 ≤ fp
  initialMemorySize : 96 ≤ mem.size
  initialWordsMin : 3 ≤ aw.toNat
  initialWords64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
  initialFreePointer : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp)
  q1MemorySize : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    96 ≤ first.memory.size
  q1WordsMin : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    3 ≤ first.activeWords.toNat
  q1Words64 : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    ¬ (⟨64⟩ : UInt256) ≥ first.activeWords * ⟨32⟩
  q1FreePointer : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    first.memory.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat q1Fp)
  muInMemory : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    mu.toNat < (q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords).size
  muActive : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    ¬ mu ≥ q1CopiedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords * ⟨32⟩
  muHeader : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    (q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords).readWithPadding
      mu.toNat 32 = UInt256.toByteArray (UInt256.ofNat (kWords + 2))
  secondMemorySize : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    96 ≤ copied.size
  secondWordsMin : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    3 ≤ (q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords).toNat
  secondWords64 : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    ¬ (⟨64⟩ : UInt256) ≥
      q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords * ⟨32⟩
  secondFreePointer : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    copied.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat secondFp)
  q3MemorySize : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    96 ≤ q2.memory.size
  q3WordsMin : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    3 ≤ q2.activeWords.toNat
  q3Words64 : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    ¬ (⟨64⟩ : UInt256) ≥ q2.activeWords * ⟨32⟩
  q3FreePointer : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    q2.memory.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat q3Fp)
  r2MemorySize : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    96 ≤ (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords).size
  r2WordsMin : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    3 ≤ (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords).toNat
  r2Words64 : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    ¬ (⟨64⟩ : UInt256) ≥ q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords * ⟨32⟩
  r2FreePointer : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let copiedQ3 := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    copiedQ3.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat r2Fp)
  finalMemorySize : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocated := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    let allocatedAw := r2AllocatedWords
      (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    96 ≤ (truncatedFinal allocated allocatedAw q3 n (UInt256.ofNat r2Fp) kWords).memory.size
  finalWordsMin : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocated := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    let allocatedAw := r2AllocatedWords
      (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    3 ≤ (truncatedFinal allocated allocatedAw q3 n (UInt256.ofNat r2Fp) kWords).activeWords.toNat
  finalWords64 : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocated := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    let allocatedAw := r2AllocatedWords
      (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    ¬ (⟨64⟩ : UInt256) ≥
      (truncatedFinal allocated allocatedAw q3 n (UInt256.ofNat r2Fp) kWords).activeWords * ⟨32⟩
  finalFreePointer : let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
    let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
    let copied := q1CopiedMemory q1Mem (UInt256.ofNat q1Fp) (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw (UInt256.ofNat q1Fp) (UInt256.ofNat fp) mu kWords
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal copied copiedAw
      (UInt256.ofNat q1Fp) mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
    let allocated := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
      (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    let allocatedAw := r2AllocatedWords
      (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords) r2Fp kWords
    let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
    (truncatedFinal allocated allocatedAw q3 n (UInt256.ofNat r2Fp) kWords).memory.readWithPadding
      64 32 = UInt256.toByteArray (UInt256.ofNat resultFp)
  selection : selectCall fuel mem aw a b n mu fp kWords = some selected

/-- The compact external scratch contract discharges every internal exact-call obligation. -/
theorem ScratchInvariant.toCallValid
    {I : ExecutionEnv} {fuel fp kWords : Nat} {mem : ByteArray}
    {aw a b n mu : UInt256} {selected : BarrettCorrectionSelection}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected) :
    CallValid I fuel mem aw a b n mu fp kWords selected := by
  let first := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory first.memory q1Fp kWords
  let q1Aw := q1AllocatedWords first.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedOnlyAw := q1CopiedWords q1Aw q1 (UInt256.ofNat fp) kWords
  let loadedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let q2 := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem loadedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory
    copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  have hfirst : ReusedFunctionFinalGeometry first q1Fp := by
    simpa only [first, q1Fp] using valid.firstProductGeometry
  have hq1 : ReusedQ1Geometry copiedMem copiedOnlyAw loadedAw mu secondFp kWords
      first.memory.size := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedOnlyAw, loadedAw,
      secondFp] using valid.q1Geometry
  have hq2 : ReusedFunctionFinalGeometry q2 q3Fp := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp] using valid.secondProductGeometry
  have hq3 : ReusedQ3Geometry copiedQ3Mem copiedQ3Aw r2Fp q2.memory.size := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp] using valid.q3Geometry
  have hfinal : ReusedTruncatedGeometry final resultFp := by
    simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp, q2,
      q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
      allocatedAw, r2, initial, final, resultFp] using valid.truncatedGeometry
  have hmem96 : 96 ≤ mem.size := by
    have hfpScratch : fp ≤ scratchEnd fp kWords := by
      unfold scratchEnd callResultFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact valid.freePointerBase.trans (hfpScratch.trans valid.scratchConcrete)
  have haw3 : 3 ≤ aw.toNat := by
    have hcovered := valid.covered
    unfold MemoryCovered at hcovered
    omega
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ := by
    have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) valid.activeWordsFit
    intro hge
    have hgeNat : (aw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by simpa using hge
    rw [hmul] at hgeNat
    omega
  exact {
    wordsPos := valid.wordsPos
    words := valid.words
    firstBound := by
      apply lt_of_le_of_lt _ valid.scratchBound
      unfold scratchEnd callResultFp
      omega
    q1Bound := by
      apply lt_of_le_of_lt _ valid.scratchBound
      unfold scratchEnd callResultFp
      omega
    secondBound := by
      apply lt_of_le_of_lt _ valid.scratchBound
      unfold scratchEnd callResultFp
      omega
    q3Bound := by
      apply lt_of_le_of_lt _ valid.scratchBound
      unfold scratchEnd callResultFp
      omega
    r2Bound := by
      apply lt_of_le_of_lt _ valid.scratchBound
      unfold scratchEnd callResultFp
      omega
    resultBound := by simpa only [scratchEnd] using valid.scratchBound
    calldataBound := valid.calldataBound
    freePointerBase := valid.freePointerBase
    initialMemorySize := hmem96
    initialWordsMin := haw3
    initialWords64 := haw64
    initialFreePointer := valid.freePointerRead
    q1MemorySize := by simpa only [first] using hfirst.memorySize96
    q1WordsMin := by simpa only [first] using hfirst.activeWords3
    q1Words64 := by simpa only [first] using hfirst.activeWords64
    q1FreePointer := by simpa only [first, q1Fp] using hfirst.freePointerRead
    muInMemory := by simpa only [first, q1Fp, q1Mem, q1, copiedMem] using hq1.muInMemory
    muActive := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedOnlyAw] using hq1.muActive
    muHeader := by simpa only [first, q1Fp, q1Mem, q1, copiedMem] using hq1.muHeader
    secondMemorySize := by
      simpa only [first, q1Fp, q1Mem, q1, copiedMem] using hq1.memorySize96
    secondWordsMin := by
      simpa only [first, q1Fp, q1Aw, q1, loadedAw] using hq1.activeWords3
    secondWords64 := by
      simpa only [first, q1Fp, q1Aw, q1, loadedAw] using hq1.activeWords64
    secondFreePointer := by
      simpa only [first, q1Fp, q1Mem, q1, copiedMem, secondFp] using hq1.freePointerRead
    q3MemorySize := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2] using hq2.memorySize96
    q3WordsMin := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2] using hq2.activeWords3
    q3Words64 := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2] using hq2.activeWords64
    q3FreePointer := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp] using hq2.freePointerRead
    r2MemorySize := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Mem, q3, copiedQ3Mem] using hq3.memorySize96
    r2WordsMin := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Aw, q3, copiedQ3Aw] using hq3.activeWords3
    r2Words64 := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Aw, q3, copiedQ3Aw] using hq3.activeWords64
    r2FreePointer := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Mem, q3, copiedQ3Mem, r2Fp] using hq3.freePointerRead
    finalMemorySize := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
        allocatedAw, r2, initial, final, truncatedFinal] using hfinal.memorySize96
    finalWordsMin := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
        allocatedAw, r2, initial, final, truncatedFinal] using hfinal.activeWords3
    finalWords64 := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
        allocatedAw, r2, initial, final, truncatedFinal] using hfinal.activeWords64
    finalFreePointer := by
      simpa only [first, q1Fp, q1Mem, q1Aw, q1, copiedMem, loadedAw, secondFp,
        q2, q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw, r2Fp, allocatedMem,
        allocatedAw, r2, initial, final, resultFp, truncatedFinal] using
        hfinal.freePointerRead
    selection := valid.selection
  }

theorem validCallExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat} {returnPc : UInt256}
    (valid : CallValid I fuel mem aw a b n mu fp kWords selected)
    (hdepth : tail.length + 17 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat (callResultFp fp kWords) :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + callSteps mem aw a b n mu fp kWords selected)
      (gasUsed + callGas mem aw a b n mu fp kWords selected) := by
  let firstInitial := Modexp.MultiLimbBarrettReused.firstProductInitial mem aw fp kWords
  let firstFinal := Modexp.MultiLimbBarrettReused.firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := Modexp.MultiLimbBarrettReused.q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Initial := Modexp.MultiLimbBarrettReused.secondProductInitial
    copiedMem copiedAw secondFp kWords
  let q2Final := Modexp.MultiLimbBarrettReused.secondProductFinal
    copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := Modexp.MultiLimbBarrettReused.q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let copiedQ3Mem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let copiedQ3Aw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let allocatedMem := Modexp.MultiLimbBarrettReused.r2AllocatedMemory copiedQ3Mem r2Fp kWords
  let allocatedAw := r2AllocatedWords copiedQ3Aw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState := { i := 0, memory := allocatedMem, activeWords := allocatedAw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := Modexp.MultiLimbBarrettReused.resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  have hkPos := valid.wordsPos
  have hk := valid.words
  have hfp := valid.freePointerBase
  have hkWord : kWords + 1 < UInt256.size :=
    (show kWords + 1 < 2 ^ 64 by omega).trans (by decide)
  have rd6468 := Modexp.MultiLimbBarrettReused.firstProductExact (tail := tail)
    hkPos (by omega) hfp valid.firstBound valid.initialMemorySize
    valid.initialWordsMin valid.initialWords64 valid.initialFreePointer valid.calldataBound
    (by omega) h
  have rd6490 := Modexp.MultiLimbBarrettReused.q1AllocationExact (tail := tail)
    (fp := q1Fp) (mem := firstFinal.memory) (aw := firstFinal.activeWords)
    (product := UInt256.ofNat fp) (kWords := kWords) (by omega) (by omega)
    (by simpa only [q1Fp, Nat.add_assoc] using valid.q1Bound)
    (by simpa only [firstFinal] using valid.q1MemorySize)
    (by simpa only [firstFinal] using valid.q1WordsMin)
    (by simpa only [firstFinal] using valid.q1Words64)
    (by simpa only [firstFinal, q1Fp] using valid.q1FreePointer)
    valid.calldataBound (by omega) (by simpa only [firstFinal] using rd6468)
  have rd5016 := Modexp.MultiLimbBarrettMul.q1ProductEntryExact (tail := tail)
    (kWords := kWords) (muWords := kWords + 2) hkWord
    (by simpa only [firstFinal, q1Fp, q1Mem, q1] using valid.muInMemory)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1] using valid.muActive)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1] using valid.muHeader)
    (by omega) (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1] using rd6490)
  have rd6530 := Modexp.MultiLimbBarrettReused.secondProductExact (tail := tail)
    (fp := secondFp) (kWords := kWords) (mem := copiedMem) (aw := copiedAw)
    (q1 := q1) (mu := mu) (by omega) (by omega)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using valid.secondBound)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1] using valid.secondMemorySize)
    (by simpa only [firstFinal, q1Fp, q1Aw, q1, copiedAw] using valid.secondWordsMin)
    (by simpa only [firstFinal, q1Fp, q1Aw, q1, copiedAw] using valid.secondWords64)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1, copiedMem, secondFp] using
      valid.secondFreePointer)
    valid.calldataBound (by omega)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw] using rd5016)
  have rd6582 := Modexp.MultiLimbBarrettReused.q3AllocationExact (tail := tail)
    (fp := q3Fp) (kWords := kWords) (mem := q2Final.memory) (aw := q2Final.activeWords)
    (q2 := UInt256.ofNat secondFp) hkPos (by omega) (by omega)
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using valid.q3Bound)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final] using valid.q3MemorySize)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final] using valid.q3WordsMin)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final] using valid.q3Words64)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp] using valid.q3FreePointer)
    valid.calldataBound (by omega) (by simpa only [q2Final] using rd6530)
  have rd6626 := Modexp.MultiLimbBarrettMul.q3CopySetupExact (tail := tail)
    hkPos (by omega) (by omega)
    (by simpa only [q2Final, q3Fp, q3Mem, q3Aw, q3] using rd6582)
  have rd6656 := Modexp.MultiLimbBarrettMul.q3CopyAndRLenExact (tail := tail)
    hkWord (by omega) rd6626
  have rd6666 := Modexp.MultiLimbBarrettReused.r2AllocationExact (tail := tail)
    (fp := r2Fp) (kWords := kWords) (mem := copiedQ3Mem) (aw := copiedQ3Aw)
    (q3 := q3) (by omega) (by omega)
    (by simpa only [r2Fp, q3Fp, secondFp, q1Fp, Nat.add_assoc] using valid.r2Bound)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Mem, q3] using valid.r2MemorySize)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Aw, q3, copiedQ3Aw] using valid.r2WordsMin)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Aw, q3, copiedQ3Aw] using valid.r2Words64)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Mem, q3, copiedQ3Mem, r2Fp] using
      valid.r2FreePointer)
    valid.calldataBound (by omega)
    (by simpa only [q3Fp, q3Mem, q3Aw, q3, copiedQ3Mem, copiedQ3Aw] using rd6656)
  have hselect : Modexp.MultiLimbBarrettReused.selectBarrettFromTruncated fuel
      allocatedMem allocatedAw q3 n r2 (UInt256.ofNat fp) resultFp kWords = some selected := by
    simpa only [selectCall, firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp, copiedMem,
      copiedAw, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp, copiedQ3Mem, copiedQ3Aw,
      allocatedMem, allocatedAw, r2, resultFp] using valid.selection
  have rd6737 := Modexp.MultiLimbBarrettReused.selectedBarrettFromTruncatedExact
    (tail := tail) (fp := resultFp) (kWords := kWords) (mem := allocatedMem)
    (aw := allocatedAw) (q3 := q3) (n := n) (r2 := r2)
    (product := UInt256.ofNat fp) selected hkPos hk (by omega)
    (by simpa only [callResultFp, q1Fp, secondFp, q3Fp, r2Fp, resultFp] using
      valid.resultBound)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp, copiedQ3Mem, copiedQ3Aw,
      allocatedMem, allocatedAw, r2, resultFp, initial, truncatedFinal] using
      valid.finalMemorySize)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp, copiedQ3Mem, copiedQ3Aw,
      allocatedMem, allocatedAw, r2, resultFp, initial, truncatedFinal] using
      valid.finalWordsMin)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp, copiedQ3Mem, copiedQ3Aw,
      allocatedMem, allocatedAw, r2, resultFp, initial, truncatedFinal] using
      valid.finalWords64)
    (by simpa only [firstFinal, q1Fp, q1Mem, q1Aw, q1, copiedMem, copiedAw,
      secondFp, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp, copiedQ3Mem, copiedQ3Aw,
      allocatedMem, allocatedAw, r2, resultFp, initial, truncatedFinal] using
      valid.finalFreePointer)
    valid.calldataBound (by omega) hselect
    (by simpa only [r2Fp, copiedQ3Mem, copiedQ3Aw, allocatedMem, allocatedAw, r2] using rd6666)
  have normalized := rd6737.withIndices
    (k' := steps + callSteps mem aw a b n mu fp kWords selected) (by
      simp only [callSteps, firstInitial, firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp,
        copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp,
        copiedQ3Mem, copiedQ3Aw, allocatedMem, allocatedAw, r2, initial]
      omega)
    (C' := gasUsed + callGas mem aw a b n mu fp kWords selected) (by
      simp only [callGas, firstInitial, firstFinal, q1Fp, q1Mem, q1Aw, q1, secondFp,
        copiedMem, copiedAw, q2Initial, q2Final, q3Fp, q3Mem, q3Aw, q3, r2Fp,
        copiedQ3Mem, copiedQ3Aw, allocatedMem, allocatedAw, r2, resultFp, initial,
        final, resultMem, resultAw]
      omega)
  simpa only [callResultFp, q1Fp, secondFp, q3Fp, r2Fp, resultFp] using normalized

/-- Exact deployed Barrett execution from the compact caller-facing scratch invariant. -/
theorem validCallExactOfScratchInvariant
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu : UInt256}
    {selected : BarrettCorrectionSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {steps gasUsed : Nat} {returnPc : UInt256}
    (valid : ScratchInvariant I fuel mem aw a b n mu fp kWords selected)
    (hdepth : tail.length + 17 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat (callResultFp fp kWords) :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + callSteps mem aw a b n mu fp kWords selected)
      (gasUsed + callGas mem aw a b n mu fp kWords selected) :=
  validCallExact valid.toCallValid hdepth h

end Modexp.MultiLimbBarrettReusedCall
