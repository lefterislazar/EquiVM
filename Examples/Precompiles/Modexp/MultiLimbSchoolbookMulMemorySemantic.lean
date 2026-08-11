import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulSemantic
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeLinks

/-!
# Standalone schoolbook multiplication memory semantics

The standalone multiplier computes operand and destination addresses from its `(i,j)` indices.
This module establishes the covered-memory and fixed-size invariants for those concrete reads and
writes, including the row carry store.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookMulTrace

open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbArithmeticTrace

theorem elementPtr_toNat_of_fit (array index : UInt256)
    (hfit : array.toNat + 32 * (index.toNat + 1) < UInt256.size) :
    (elementPtr array index).toNat = array.toNat + 32 * (index.toNat + 1) := by
  have hsize : UInt256.size = 32 * 2 ^ 251 := by native_decide
  have hshift : (index.shiftLeft ⟨5⟩).toNat = 32 * index.toNat := by
    calc
      (index.shiftLeft ⟨5⟩).toNat =
          ((UInt256.ofNat index.toNat).shiftLeft ⟨5⟩).toNat := by
            rw [u256_ofNat_toNat]
      _ = 32 * index.toNat :=
        ushl5_ofNat_toNat index.toNat (by rw [hsize] at hfit; omega)
  have hfirst : 32 * index.toNat + array.toNat < UInt256.size := by omega
  unfold elementPtr
  rw [uadd_toNat, uadd_toNat, hshift, Nat.mod_eq_of_lt hfirst,
    show (⟨32⟩ : UInt256).toNat = 32 by decide,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- A nonwrapping array element pointer advances by one word when its index advances by one. -/
theorem elementPtr_add_one (array index : UInt256)
    (hfit : array.toNat + 32 * (index.toNat + 2) < UInt256.size) :
    elementPtr array (index + ⟨1⟩) = elementPtr array index + ⟨32⟩ := by
  have hindexNext : (index + ⟨1⟩).toNat = index.toNat + 1 := by
    rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
      Nat.mod_eq_of_lt (by omega)]
  have hleft := elementPtr_toNat_of_fit array (index + ⟨1⟩) (by
    rw [hindexNext]
    omega)
  have hright := elementPtr_toNat_of_fit array index (by omega)
  have hrightAdd : (elementPtr array index + ⟨32⟩).toNat =
      array.toNat + 32 * (index.toNat + 1) + 32 := by
    rw [uadd_toNat, hright, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt (by omega)]
  apply u256_inj
  rw [hleft, hrightAdd, hindexNext]
  omega

/-- Reinterpret one standalone `(i,j)` state as the generic contiguous multiply-pass state used
by the CIOS semantic library. -/
def asMultiplyPassState (bPtr resultPtr i : UInt256) (state : InnerState) :
    MultiplyPassState where
  operandPtr := elementPtr bPtr state.j
  resultPtr := elementPtr resultPtr (i + state.j)
  carry := state.carry
  memory := state.memory
  activeWords := state.activeWords

@[simp] theorem asMultiplyPassState_memory
    (bPtr resultPtr i : UInt256) (state : InnerState) :
    (asMultiplyPassState bPtr resultPtr i state).memory = state.memory := rfl

@[simp] theorem asMultiplyPassState_activeWords
    (bPtr resultPtr i : UInt256) (state : InnerState) :
    (asMultiplyPassState bPtr resultPtr i state).activeWords = state.activeWords := rfl

/-- The standalone arithmetic, write, and active-word update are exactly the generic multiply
pass at its two concretely derived pointers. -/
theorem asMultiplyPassState_advance
    (a bPtr resultPtr i : UInt256) (state : InnerState)
    (hbNext : elementPtr bPtr (state.j + ⟨1⟩) = elementPtr bPtr state.j + ⟨32⟩)
    (hresultNext : elementPtr resultPtr (i + (state.j + ⟨1⟩)) =
      elementPtr resultPtr (i + state.j) + ⟨32⟩) :
    asMultiplyPassState bPtr resultPtr i (advance a bPtr resultPtr i state) =
      multiplyPassAdvance a (asMultiplyPassState bPtr resultPtr i state) := by
  cases state
  simp only [asMultiplyPassState, advance, multiplyPassAdvance]
  rw [hbNext, hresultNext]
  rfl

/-- Under concrete nonwrapping pointer ranges, every standalone inner iterate is the generic
contiguous multiply-pass iterate. -/
theorem asMultiplyPassState_iterate
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size) :
    asMultiplyPassState bPtr resultPtr i (iterate a bPtr resultPtr i count state) =
      multiplyPassIterate a count (asMultiplyPassState bPtr resultPtr i state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      have hbFirst := hbFits 0 (by omega)
      have hresultFirst := hresultFits 0 (by omega)
      have hbNext := elementPtr_add_one bPtr state.j (by
        simpa only [iterate] using hbFirst)
      have hresultNext : elementPtr resultPtr (i + (state.j + ⟨1⟩)) =
          elementPtr resultPtr (i + state.j) + ⟨32⟩ := by
        rw [← u256_add_assoc]
        exact elementPtr_add_one resultPtr (i + state.j) (by
          simpa only [iterate] using hresultFirst)
      have hstep := asMultiplyPassState_advance a bPtr resultPtr i state
        hbNext hresultNext
      have hbTail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size := by
        intro q hq
        simpa only [next, iterate_advance] using hbFits (q + 1) (by omega)
      have hresultTail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size := by
        intro q hq
        simpa only [next, iterate_advance] using hresultFits (q + 1) (by omega)
      have htail := ih next hbTail hresultTail
      rw [show iterate a bPtr resultPtr i (count + 1) state =
        iterate a bPtr resultPtr i count next by rfl, htail, hstep]
      rfl

/-- All three standalone inner collectors are the generic multiply-pass collectors at the
concretely derived initial pointers. -/
theorem innerCollectors_eq_multiplyPassCollectors
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size) :
    innerOperandWords a bPtr resultPtr i count state =
        multiplyPassOperandWords a count (asMultiplyPassState bPtr resultPtr i state) ∧
      innerPriorWords a bPtr resultPtr i count state =
        multiplyPassPriorWords a count (asMultiplyPassState bPtr resultPtr i state) ∧
      innerOutputWords a bPtr resultPtr i count state =
        multiplyPassOutputWords a count (asMultiplyPassState bPtr resultPtr i state) := by
  induction count generalizing state with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      have hbFirst := hbFits 0 (by omega)
      have hresultFirst := hresultFits 0 (by omega)
      have hbNext := elementPtr_add_one bPtr state.j (by
        simpa only [iterate] using hbFirst)
      have hresultNext : elementPtr resultPtr (i + (state.j + ⟨1⟩)) =
          elementPtr resultPtr (i + state.j) + ⟨32⟩ := by
        rw [← u256_add_assoc]
        exact elementPtr_add_one resultPtr (i + state.j) (by
          simpa only [iterate] using hresultFirst)
      have hstep := asMultiplyPassState_advance a bPtr resultPtr i state
        hbNext hresultNext
      have hbTail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size := by
        intro q hq
        simpa only [next, iterate_advance] using hbFits (q + 1) (by omega)
      have hresultTail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size := by
        intro q hq
        simpa only [next, iterate_advance] using hresultFits (q + 1) (by omega)
      have htail := ih next hbTail hresultTail
      simp only [innerOperandWords, innerPriorWords, innerOutputWords,
        multiplyPassOperandWords, multiplyPassPriorWords, multiplyPassOutputWords]
      have hheadOperand :
          (operands state.memory state.activeWords bPtr resultPtr i state.j
            state.carry).1 =
          (schoolbookOperands state.memory state.activeWords
            (elementPtr bPtr state.j) (elementPtr resultPtr (i + state.j))
            state.carry).1 := rfl
      have hheadPrior :
          (operands state.memory state.activeWords bPtr resultPtr i state.j
            state.carry).2.1 =
          (schoolbookOperands state.memory state.activeWords
            (elementPtr bPtr state.j) (elementPtr resultPtr (i + state.j))
            state.carry).2.1 := rfl
      have hheadOutput :
          (step state.memory state.activeWords a bPtr resultPtr i state.j
            state.carry).1 =
          (schoolbookStep state.memory state.activeWords
            (elementPtr bPtr state.j) (elementPtr resultPtr (i + state.j)) a
            state.carry).1 := rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hheadOperand, htail.1, hstep]
        rfl
      · rw [hheadPrior, htail.2.1, hstep]
        rfl
      · rw [hheadOutput, htail.2.2, hstep]
        rfl

/-- Every stored standalone inner output word is exactly the corresponding word in the final
evolving destination memory. -/
theorem innerOutputWords_eq_finalMemory
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * count <
      UInt256.size)
    (hwrites : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size) :
    innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory
        (elementPtr resultPtr (i + state.j)).toNat count := by
  have hcollectors := innerCollectors_eq_multiplyPassCollectors
    a bPtr resultPtr i count state hbFits hresultFits
  have hgenericWrites : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro q hq
    have hbPrefix : ∀ p, p < q →
        let current := iterate a bPtr resultPtr i p state
        bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size := by
      intro p hp
      exact hbFits p (by omega)
    have hresultPrefix : ∀ p, p < q →
        let current := iterate a bPtr resultPtr i p state
        resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size := by
      intro p hp
      exact hresultFits p (by omega)
    have hmap := asMultiplyPassState_iterate a bPtr resultPtr i q state
      hbPrefix hresultPrefix
    rw [← hmap]
    simpa only [asMultiplyPassState] using hwrites q hq
  have houtput := multiplyPassOutputWords_eq_finalMemory a count
    (asMultiplyPassState bPtr resultPtr i state) hresultRange hgenericWrites
  have hmapFinal := asMultiplyPassState_iterate a bPtr resultPtr i count state
    hbFits hresultFits
  rw [← hmapFinal] at houtput
  rw [hcollectors.2.2]
  simpa only [asMultiplyPassState] using houtput

/-- One standalone inner column preserves covered representable memory and the allocated byte
array size when its concrete destination word is in bounds. -/
theorem advance_coverage_size
    (a bPtr resultPtr i : UInt256) (state : InnerState)
    (hbFit : (elementPtr bPtr state.j).toNat + 32 + 31 < UInt256.size)
    (hresultFit : (elementPtr resultPtr (i + state.j)).toNat + 32 + 31 <
      UInt256.size)
    (hwrite : (elementPtr resultPtr (i + state.j)).toNat + 32 ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (advance a bPtr resultPtr i state).memory
        (advance a bPtr resultPtr i state).activeWords ∧
      (advance a bPtr resultPtr i state).activeWords.toNat * 32 < UInt256.size ∧
      (advance a bPtr resultPtr i state).memory.size = state.memory.size := by
  let bAddress := elementPtr bPtr state.j
  let resultAddress := elementPtr resultPtr (i + state.j)
  have hbCoverage := readWords1_coverage state.memory state.activeWords bAddress
    hcovered hawFit (by simpa [bAddress] using hbFit)
  have hresultCoverage := readWords1_coverage state.memory
    (afterLoad state.activeWords bAddress) resultAddress
    (by simpa [afterLoad] using hbCoverage.1)
    (by simpa [afterLoad] using hbCoverage.2)
    (by simpa [resultAddress] using hresultFit)
  have hresultLe : resultAddress.toNat ≤ state.memory.size := by
    dsimp only [resultAddress]
    omega
  have hgap : resultAddress.toNat - state.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hresultLe]
    exact lt_usize 0 (by norm_num)
  have hstoreCoverage := write32_coverage
    (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1
    state.memory (afterLoad (afterLoad state.activeWords bAddress) resultAddress)
    resultAddress
    (by simpa [afterLoad] using hresultCoverage.1)
    (by simpa [afterLoad] using hresultCoverage.2)
    (by simpa [resultAddress] using hresultFit) hgap
  have hsize : (advance a bPtr resultPtr i state).memory.size = state.memory.size := by
    unfold advance nextMemory
    exact write_size_of_inBounds_from _ _ 0 resultAddress.toNat 32
      (by decide) (by rw [toByteArray_size]) (by simpa [resultAddress] using hwrite)
  refine ⟨?_, ?_, hsize⟩
  · simpa [advance, nextMemory, nextWords, bAddress, resultAddress, afterLoad]
      using hstoreCoverage.1
  · simpa [advance, nextWords, bAddress, resultAddress, afterLoad]
      using hstoreCoverage.2

/-- A standalone inner column may start at the concrete memory frontier and extend it by one word.
Coverage and representability still follow from the actual EVM active-word updates. -/
theorem advance_coverage_extending
    (a bPtr resultPtr i : UInt256) (state : InnerState)
    (hbFit : (elementPtr bPtr state.j).toNat + 32 + 31 < UInt256.size)
    (hresultFit : (elementPtr resultPtr (i + state.j)).toNat + 32 + 31 <
      UInt256.size)
    (hwriteStart : (elementPtr resultPtr (i + state.j)).toNat ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (advance a bPtr resultPtr i state).memory
        (advance a bPtr resultPtr i state).activeWords ∧
      (advance a bPtr resultPtr i state).activeWords.toNat * 32 < UInt256.size ∧
      (advance a bPtr resultPtr i state).memory.size =
        max state.memory.size ((elementPtr resultPtr (i + state.j)).toNat + 32) := by
  let bAddress := elementPtr bPtr state.j
  let resultAddress := elementPtr resultPtr (i + state.j)
  have hbCoverage := readWords1_coverage state.memory state.activeWords bAddress
    hcovered hawFit (by simpa [bAddress] using hbFit)
  have hresultCoverage := readWords1_coverage state.memory
    (afterLoad state.activeWords bAddress) resultAddress
    (by simpa [afterLoad] using hbCoverage.1)
    (by simpa [afterLoad] using hbCoverage.2)
    (by simpa [resultAddress] using hresultFit)
  have hgap : resultAddress.toNat - state.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by simpa [resultAddress] using hwriteStart)]
    exact lt_usize 0 (by norm_num)
  have hstoreCoverage := write32_coverage
    (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1
    state.memory (afterLoad (afterLoad state.activeWords bAddress) resultAddress)
    resultAddress
    (by simpa [afterLoad] using hresultCoverage.1)
    (by simpa [afterLoad] using hresultCoverage.2)
    (by simpa [resultAddress] using hresultFit) hgap
  have hsize : (advance a bPtr resultPtr i state).memory.size =
      max state.memory.size (resultAddress.toNat + 32) := by
    unfold advance nextMemory
    exact toByteArray_write_size_eq_max _ _ _ hgap
  refine ⟨?_, ?_, ?_⟩
  · simpa [advance, nextMemory, nextWords, bAddress, resultAddress, afterLoad]
      using hstoreCoverage.1
  · simpa [advance, nextWords, bAddress, resultAddress, afterLoad]
      using hstoreCoverage.2
  · simpa only [resultAddress] using hsize

/-- A standalone inner column may also materialize a bounded implicit-zero gap before its
destination.  This is the concrete case needed after one or more skipped zero source rows. -/
theorem advance_coverage_of_gap
    (a bPtr resultPtr i : UInt256) (state : InnerState)
    (hbFit : (elementPtr bPtr state.j).toNat + 32 + 31 < UInt256.size)
    (hresultFit : (elementPtr resultPtr (i + state.j)).toNat + 32 + 31 <
      UInt256.size)
    (hgap : (elementPtr resultPtr (i + state.j)).toNat - state.memory.size < USize.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (advance a bPtr resultPtr i state).memory
        (advance a bPtr resultPtr i state).activeWords ∧
      (advance a bPtr resultPtr i state).activeWords.toNat * 32 < UInt256.size ∧
      (advance a bPtr resultPtr i state).memory.size =
        max state.memory.size ((elementPtr resultPtr (i + state.j)).toNat + 32) := by
  let bAddress := elementPtr bPtr state.j
  let resultAddress := elementPtr resultPtr (i + state.j)
  have hbCoverage := readWords1_coverage state.memory state.activeWords bAddress
    hcovered hawFit (by simpa [bAddress] using hbFit)
  have hresultCoverage := readWords1_coverage state.memory
    (afterLoad state.activeWords bAddress) resultAddress
    (by simpa [afterLoad] using hbCoverage.1)
    (by simpa [afterLoad] using hbCoverage.2)
    (by simpa [resultAddress] using hresultFit)
  have hstoreCoverage := write32_coverage
    (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1
    state.memory (afterLoad (afterLoad state.activeWords bAddress) resultAddress)
    resultAddress
    (by simpa [afterLoad] using hresultCoverage.1)
    (by simpa [afterLoad] using hresultCoverage.2)
    (by simpa [resultAddress] using hresultFit)
    (by simpa only [resultAddress] using hgap)
  have hsize : (advance a bPtr resultPtr i state).memory.size =
      max state.memory.size (resultAddress.toNat + 32) := by
    unfold advance nextMemory
    exact toByteArray_write_size_eq_max _ _ _
      (by simpa only [resultAddress] using hgap)
  refine ⟨?_, ?_, ?_⟩
  · simpa [advance, nextMemory, nextWords, bAddress, resultAddress, afterLoad]
      using hstoreCoverage.1
  · simpa [advance, nextWords, bAddress, resultAddress, afterLoad]
      using hstoreCoverage.2
  · simpa only [resultAddress] using hsize

/-- Covered in-bounds standalone operand loads are the corresponding concrete memory words. -/
theorem operands_toNat_eq_memoryWords
    (mem : ByteArray) (aw bPtr resultPtr i j carry : UInt256)
    (hbFit : (elementPtr bPtr j).toNat + 32 + 31 < UInt256.size)
    (hbMem : (elementPtr bPtr j).toNat + 32 ≤ mem.size)
    (hresultMem : (elementPtr resultPtr (i + j)).toNat + 32 ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    (operands mem aw bPtr resultPtr i j carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem (elementPtr bPtr j).toNat ∧
      (operands mem aw bPtr resultPtr i j carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem
          (elementPtr resultPtr (i + j)).toNat := by
  let bAddress := elementPtr bPtr j
  let resultAddress := elementPtr resultPtr (i + j)
  have hbRead := readWord_eq_memoryWordOf_covered mem aw bAddress
    hcovered hawFit (by simpa [bAddress] using hbMem)
  have hbCoverage := readWords1_coverage mem aw bAddress hcovered hawFit
    (by simpa [bAddress] using hbFit)
  have hresultRead := readWord_eq_memoryWordOf_covered mem
    (afterLoad aw bAddress) resultAddress
    (by simpa [afterLoad] using hbCoverage.1)
    (by simpa [afterLoad] using hbCoverage.2)
    (by simpa [resultAddress] using hresultMem)
  constructor
  · have hnat := congrArg UInt256.toNat hbRead
    simpa [operands, bAddress, resultAddress,
      UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem bAddress.toNat)] using hnat
  · have hnat := congrArg UInt256.toNat hresultRead
    simpa [operands, bAddress, resultAddress,
      UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem resultAddress.toNat)] using hnat

/-- A generated guarded load agrees with the padded memory-word model even when its address begins
at or beyond the concrete byte-array frontier. -/
theorem readWord_eq_memoryWordOf_covered_padded
    (mem : ByteArray) (aw ptr : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    Modexp.MultiLimbDivisionTrace.readWord mem aw ptr =
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat) := by
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  by_cases hpast : ptr.toNat ≥ mem.size
  · unfold Modexp.MultiLimbDivisionTrace.readWord
    rw [if_pos (Or.inl hpast)]
    have hword : Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat = 0 := by
      unfold Modexp.MultiLimbMemoryModel.memoryWordNat
      rw [readWithPadding_past_end mem ptr.toNat 32 hpast (by decide),
        ← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
      rfl
    rw [hword]
    rfl
  · have hnotActive : ¬ ptr ≥ aw * ⟨32⟩ := by
      intro hge
      have hgeNat : (aw * (⟨32⟩ : UInt256)).toNat ≤ ptr.toNat := hge
      rw [hmul] at hgeNat
      unfold MemoryCovered at hcovered
      omega
    unfold Modexp.MultiLimbDivisionTrace.readWord
    rw [if_neg (not_or.mpr ⟨by omega, hnotActive⟩)]
    rfl

/-- Both standalone operands agree with padded memory words under coverage, including a fresh
implicit-zero destination word. -/
theorem operands_toNat_eq_memoryWords_padded
    (mem : ByteArray) (aw bPtr resultPtr i j carry : UInt256)
    (hbFit : (elementPtr bPtr j).toNat + 32 + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    (operands mem aw bPtr resultPtr i j carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem (elementPtr bPtr j).toNat ∧
      (operands mem aw bPtr resultPtr i j carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat mem
          (elementPtr resultPtr (i + j)).toNat := by
  let bAddress := elementPtr bPtr j
  let resultAddress := elementPtr resultPtr (i + j)
  have hbRead := readWord_eq_memoryWordOf_covered_padded mem aw bAddress hcovered hawFit
  have hbCoverage := readWords1_coverage mem aw bAddress hcovered hawFit
    (by simpa [bAddress] using hbFit)
  have hresultRead := readWord_eq_memoryWordOf_covered_padded mem
    (afterLoad aw bAddress) resultAddress
    (by simpa [afterLoad] using hbCoverage.1)
    (by simpa [afterLoad] using hbCoverage.2)
  constructor
  · have hnat := congrArg UInt256.toNat hbRead
    simpa [operands, bAddress, resultAddress,
      UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem bAddress.toNat)] using hnat
  · have hnat := congrArg UInt256.toNat hresultRead
    simpa [operands, bAddress, resultAddress,
      UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size mem resultAddress.toNat)] using hnat

/-- Coverage, representability, and byte-array size propagate through any finite standalone
inner recurrence whose concrete accesses stay in its allocated ranges. -/
theorem iterate_coverage_size
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsteps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size) :
    MemoryCovered (iterate a bPtr resultPtr i count state).memory
        (iterate a bPtr resultPtr i count state).activeWords ∧
      (iterate a bPtr resultPtr i count state).activeWords.toNat * 32 < UInt256.size ∧
      (iterate a bPtr resultPtr i count state).memory.size = state.memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, rfl⟩
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      have hfirst := hsteps 0 (by omega)
      have hnext := advance_coverage_size a bPtr resultPtr i state
        hfirst.1 hfirst.2.1 hfirst.2.2 hcovered hawFit
      have htail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hsteps (q + 1) (by omega)
      have hrest := ih next hnext.1 hnext.2.1 htail
      simpa only [next, iterate] using
        And.intro hrest.1 (And.intro hrest.2.1 (hrest.2.2.trans hnext.2.2))

/-- Coverage propagates through frontier-extending inner stores; concrete memory size grows
monotonically instead of remaining fixed. -/
theorem iterate_coverage_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsteps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size) :
    MemoryCovered (iterate a bPtr resultPtr i count state).memory
        (iterate a bPtr resultPtr i count state).activeWords ∧
      (iterate a bPtr resultPtr i count state).activeWords.toNat * 32 < UInt256.size ∧
      state.memory.size ≤ (iterate a bPtr resultPtr i count state).memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, le_rfl⟩
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      have hfirst := hsteps 0 (by omega)
      have hnext := advance_coverage_extending a bPtr resultPtr i state
        hfirst.1 hfirst.2.1 hfirst.2.2 hcovered hawFit
      have htail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hsteps (q + 1) (by omega)
      have hrest := ih next hnext.1 hnext.2.1 htail
      have hstateLeNext : state.memory.size ≤ next.memory.size := by
        rw [hnext.2.2]
        exact Nat.le_max_left _ _
      simpa only [next, iterate] using
        And.intro hrest.1 (And.intro hrest.2.1 (hstateLeNext.trans hrest.2.2))

/-- Coverage propagates through inner stores that may cross a bounded implicit-zero gap. -/
theorem iterate_coverage_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsteps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size) :
    MemoryCovered (iterate a bPtr resultPtr i count state).memory
        (iterate a bPtr resultPtr i count state).activeWords ∧
      (iterate a bPtr resultPtr i count state).activeWords.toNat * 32 < UInt256.size ∧
      state.memory.size ≤ (iterate a bPtr resultPtr i count state).memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, le_rfl⟩
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      have hfirst := hsteps 0 (by omega)
      have hnext := advance_coverage_of_gap a bPtr resultPtr i state
        hfirst.1 hfirst.2.1 hfirst.2.2 hcovered hawFit
      have htail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
            (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hsteps (q + 1) (by omega)
      have hrest := ih next hnext.1 hnext.2.1 htail
      have hstateLeNext : state.memory.size ≤ next.memory.size := by
        rw [hnext.2.2]
        exact Nat.le_max_left _ _
      simpa only [next, iterate] using
        And.intro hrest.1 (And.intro hrest.2.1 (hstateLeNext.trans hrest.2.2))

/-- Bounded-gap inner writes grow concrete memory monotonically, independently of the load-side
coverage invariant. -/
theorem iterate_memory_size_mono_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size) :
    state.memory.size ≤ (iterate a bPtr resultPtr i count state).memory.size := by
  induction count generalizing state with
  | zero => exact le_rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstGap : dest - state.memory.size < USize.size := by
        simpa only [dest, iterate] using hgaps 0 (by omega)
      have hnextSize : next.memory.size = max state.memory.size (dest + 32) := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_size_eq_max _ _ _ hfirstGap
      have htailGaps : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hgaps (q + 1) (by omega)
      have htail := ih next htailGaps
      have hhead : state.memory.size ≤ next.memory.size := by
        rw [hnextSize]
        exact Nat.le_max_left _ _
      simpa only [next, iterate] using hhead.trans htail

/-- Bounded-gap inner writes stay below a common logical allocation end when every concrete
destination word does. -/
theorem iterate_memory_size_le_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState) (bound : Nat)
    (hstate : state.memory.size ≤ bound)
    (hsteps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ bound ∧
        (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size) :
    (iterate a bPtr resultPtr i count state).memory.size ≤ bound := by
  induction count generalizing state with
  | zero => exact hstate
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirst := hsteps 0 (by omega)
      have hnextSize : next.memory.size = max state.memory.size (dest + 32) := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_size_eq_max _ _ _ hfirst.2
      have hnextLe : next.memory.size ≤ bound := by
        rw [hnextSize]
        exact max_le hstate hfirst.1
      have htail : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ bound ∧
            (elementPtr resultPtr (i + current.j)).toNat - current.memory.size <
              USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hsteps (q + 1) (by omega)
      simpa only [next, iterate] using ih next hnextLe htail

/-- A complete 32-byte word below every selected destination is unchanged by an inner
schoolbook row, including stores that materialize an implicit-zero gap. -/
theorem iterate_read32_below_of_gap
    (a bPtr resultPtr i : UInt256) (count read : Nat) (state : InnerState)
    (hread : read + 32 ≤ state.memory.size)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (hbelow : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      read + 32 ≤ (elementPtr resultPtr (i + current.j)).toNat) :
    (iterate a bPtr resultPtr i count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstGap : dest - state.memory.size < USize.size := by
        simpa only [dest, iterate] using hgaps 0 (by omega)
      have hfirstBelow : read + 32 ≤ dest := by
        simpa only [dest, iterate] using hbelow 0 (by omega)
      have hhead : next.memory.readWithPadding read 32 =
          state.memory.readWithPadding read 32 := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_read_below_of_gap _ _ _ _ hread hfirstBelow hfirstGap
      have hnextSize : next.memory.size = max state.memory.size (dest + 32) := by
        dsimp only [next, advance, nextMemory, dest]
        exact toByteArray_write_size_eq_max _ _ _ hfirstGap
      have hnextRead : read + 32 ≤ next.memory.size := by
        rw [hnextSize]
        exact hread.trans (Nat.le_max_left _ _)
      have htailGaps : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hgaps (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          read + 32 ≤ (elementPtr resultPtr (i + current.j)).toNat := by
        intro q hq
        simpa only [next, iterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next hnextRead htailGaps htailBelow
      simpa only [next, iterate] using htail.trans hhead

/-- A word write beginning in concrete memory preserves every padded complete-word range above
the written word, including a one-word frontier extension. -/
theorem memoryWordsFrom_write_below_extending
    (word : UInt256) (base : ByteArray) (dest ptr words : Nat)
    (hdest : dest ≤ base.size) (habove : dest + 32 ≤ ptr) :
    memoryWordsFrom (word.toByteArray.write 0 base dest 32) ptr words =
      memoryWordsFrom base ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hread : (word.toByteArray.write 0 base dest 32).readWithPadding ptr 32 =
          base.readWithPadding ptr 32 := by
        by_cases hin : dest + 32 ≤ base.size
        · exact write32_read_above_padded word.toByteArray base dest ptr
            (by rw [toByteArray_size]) hin habove
        · have hgap : dest - base.size < USize.size := by
            rw [Nat.sub_eq_zero_of_le hdest]
            exact lt_usize 0 (by norm_num)
          have hsize := toByteArray_write_size_eq_max word base dest hgap
          rw [readWithPadding_past_end base ptr 32 (by omega) (by decide)]
          rw [readWithPadding_past_end (word.toByteArray.write 0 base dest 32) ptr 32
            (by rw [hsize]; omega) (by decide)]
      simp only [memoryWordsFrom]
      rw [show Modexp.MultiLimbMemoryModel.memoryWordNat
          (word.toByteArray.write 0 base dest 32) ptr =
            Modexp.MultiLimbMemoryModel.memoryWordNat base ptr by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hread]]
      rw [ih (ptr + 32) (by omega)]

/-- A bounded-gap word write preserves every padded complete-word range above the written
word. -/
theorem memoryWordsFrom_write_below_of_gap
    (word : UInt256) (base : ByteArray) (dest ptr words : Nat)
    (hgap : dest - base.size < USize.size) (habove : dest + 32 ≤ ptr) :
    memoryWordsFrom (word.toByteArray.write 0 base dest 32) ptr words =
      memoryWordsFrom base ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hread : (word.toByteArray.write 0 base dest 32).readWithPadding ptr 32 =
          base.readWithPadding ptr 32 := by
        by_cases hin : dest + 32 ≤ base.size
        · exact write32_read_above_padded word.toByteArray base dest ptr
            (by rw [toByteArray_size]) hin habove
        · have hsize := toByteArray_write_size_eq_max word base dest hgap
          rw [readWithPadding_past_end base ptr 32 (by omega) (by decide)]
          rw [readWithPadding_past_end (word.toByteArray.write 0 base dest 32) ptr 32
            (by rw [hsize]; omega) (by decide)]
      simp only [memoryWordsFrom]
      rw [show Modexp.MultiLimbMemoryModel.memoryWordNat
          (word.toByteArray.write 0 base dest 32) ptr =
            Modexp.MultiLimbMemoryModel.memoryWordNat base ptr by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hread]]
      rw [ih (ptr + 32) (by omega)]

/-- A bounded-gap word write preserves every padded complete-word range below its
destination. -/
theorem memoryWordsFrom_write_above_padded_of_gap
    (word : UInt256) (base : ByteArray) (dest ptr words : Nat)
    (hbase : 32 ≤ base.size) (hbelow : ptr + 32 * words ≤ dest)
    (hgap : dest - base.size < USize.size) :
    memoryWordsFrom (word.toByteArray.write 0 base dest 32) ptr words =
      memoryWordsFrom base ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      simp only [memoryWordsFrom]
      have hread := toByteArray_write_read_below_padded_of_gap word base dest ptr hbase
        (by omega) hgap
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (word.toByteArray.write 0 base dest 32) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat base ptr := by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        exact congrArg fromByteArrayBigEndian hread
      rw [hword]
      rw [ih (ptr + 32) (by omega)]

/-- Frontier-extending standalone inner stores preserve complete ranges below the row window. -/
theorem iterate_memoryWords_below_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (ptr words : Nat)
    (hstarts : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size)
    (hbelow : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      ptr + 32 * words ≤ (elementPtr resultPtr (i + current.j)).toNat) :
    memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstStart : dest ≤ state.memory.size := by
        simpa only [dest, iterate] using hstarts 0 (by omega)
      have hfirstBelow : ptr + 32 * words ≤ dest := by
        simpa only [dest, iterate] using hbelow 0 (by omega)
      have hfirst := memoryWordsFrom_write_above
        (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1.toByteArray
        state.memory dest ptr words (by rw [toByteArray_size]) hfirstStart hfirstBelow
      have htailStarts : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hstarts (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          ptr + 32 * words ≤ (elementPtr resultPtr (i + current.j)).toNat := by
        intro q hq
        simpa only [next, iterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next htailStarts htailBelow
      calc
        memoryWordsFrom (iterate a bPtr resultPtr i (count + 1) state).memory ptr words =
            memoryWordsFrom (iterate a bPtr resultPtr i count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, advance, nextMemory, dest] using hfirst

/-- Frontier-extending standalone inner stores also preserve complete padded ranges above the row
window. -/
theorem iterate_memoryWords_above_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (ptr words : Nat)
    (hstarts : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size)
    (habove : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ ptr) :
    memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstStart : dest ≤ state.memory.size := by
        simpa only [dest, iterate] using hstarts 0 (by omega)
      have hfirstAbove : dest + 32 ≤ ptr := by
        simpa only [dest, iterate] using habove 0 (by omega)
      have hfirst := memoryWordsFrom_write_below_extending
        (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1
        state.memory dest ptr words hfirstStart hfirstAbove
      have htailStarts : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hstarts (q + 1) (by omega)
      have htailAbove : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ ptr := by
        intro q hq
        simpa only [next, iterate_advance] using habove (q + 1) (by omega)
      have htail := ih next htailStarts htailAbove
      calc
        memoryWordsFrom (iterate a bPtr resultPtr i (count + 1) state).memory ptr words =
            memoryWordsFrom (iterate a bPtr resultPtr i count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, advance, nextMemory, dest] using hfirst

/-- Inner stores crossing bounded implicit-zero gaps preserve complete padded ranges below the
row window. -/
theorem iterate_memoryWords_below_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (ptr words : Nat) (hbase : 32 ≤ state.memory.size)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (hbelow : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      ptr + 32 * words ≤ (elementPtr resultPtr (i + current.j)).toNat) :
    memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstGap : dest - state.memory.size < USize.size := by
        simpa only [dest, iterate] using hgaps 0 (by omega)
      have hfirstBelow : ptr + 32 * words ≤ dest := by
        simpa only [dest, iterate] using hbelow 0 (by omega)
      have hfirst := memoryWordsFrom_write_above_padded_of_gap
        (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1
        state.memory dest ptr words hbase hfirstBelow hfirstGap
      have hnextBase : 32 ≤ next.memory.size := by
        have hsize : next.memory.size = max state.memory.size (dest + 32) := by
          dsimp only [next, advance, nextMemory, dest]
          exact toByteArray_write_size_eq_max _ _ _ hfirstGap
        rw [hsize]
        exact hbase.trans (Nat.le_max_left _ _)
      have htailGaps : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hgaps (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          ptr + 32 * words ≤ (elementPtr resultPtr (i + current.j)).toNat := by
        intro q hq
        simpa only [next, iterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next hnextBase htailGaps htailBelow
      calc
        memoryWordsFrom (iterate a bPtr resultPtr i (count + 1) state).memory ptr words =
            memoryWordsFrom (iterate a bPtr resultPtr i count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, advance, nextMemory, dest] using hfirst

/-- Inner stores crossing bounded implicit-zero gaps preserve complete padded ranges above the
row window. -/
theorem iterate_memoryWords_above_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (ptr words : Nat)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (habove : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ ptr) :
    memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstGap : dest - state.memory.size < USize.size := by
        simpa only [dest, iterate] using hgaps 0 (by omega)
      have hfirstAbove : dest + 32 ≤ ptr := by
        simpa only [dest, iterate] using habove 0 (by omega)
      have hfirst := memoryWordsFrom_write_below_of_gap
        (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1
        state.memory dest ptr words hfirstGap hfirstAbove
      have htailGaps : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, iterate_advance] using hgaps (q + 1) (by omega)
      have htailAbove : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ ptr := by
        intro q hq
        simpa only [next, iterate_advance] using habove (q + 1) (by omega)
      have htail := ih next htailGaps htailAbove
      calc
        memoryWordsFrom (iterate a bPtr resultPtr i (count + 1) state).memory ptr words =
            memoryWordsFrom (iterate a bPtr resultPtr i count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, advance, nextMemory, dest] using hfirst

/-- Every standalone inner store preserves a complete word range below the selected row window. -/
theorem iterate_memoryWords_below
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (ptr words : Nat)
    (hwrites : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size)
    (hbelow : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      ptr + 32 * words ≤ (elementPtr resultPtr (i + current.j)).toNat) :
    memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstWrite : dest + 32 ≤ state.memory.size := by
        simpa only [dest, iterate] using hwrites 0 (by omega)
      have hfirstBelow : ptr + 32 * words ≤ dest := by
        simpa only [dest, iterate] using hbelow 0 (by omega)
      have hfirst := memoryWordsFrom_write_above
        (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1.toByteArray
        state.memory dest ptr words (by rw [toByteArray_size]) (by omega) hfirstBelow
      have htailWrites : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hwrites (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          ptr + 32 * words ≤ (elementPtr resultPtr (i + current.j)).toNat := by
        intro q hq
        simpa only [next, iterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next htailWrites htailBelow
      calc
        memoryWordsFrom (iterate a bPtr resultPtr i (count + 1) state).memory ptr words =
            memoryWordsFrom (iterate a bPtr resultPtr i count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, advance, nextMemory, dest] using hfirst

/-- Every standalone inner store also preserves a complete word range above the selected row
window. -/
theorem iterate_memoryWords_above
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (ptr words : Nat)
    (hwrites : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size)
    (habove : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ ptr) :
    memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := advance a bPtr resultPtr i state
      let dest := (elementPtr resultPtr (i + state.j)).toNat
      have hfirstWrite : dest + 32 ≤ state.memory.size := by
        simpa only [dest, iterate] using hwrites 0 (by omega)
      have hfirstAbove : dest + 32 ≤ ptr := by
        simpa only [dest, iterate] using habove 0 (by omega)
      have hfirst := memoryWordsFrom_write_below
        (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).1.toByteArray
        state.memory dest ptr words (by rw [toByteArray_size]) hfirstWrite hfirstAbove
      have htailWrites : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size := by
        intro q hq
        simpa only [next, iterate_advance] using hwrites (q + 1) (by omega)
      have htailAbove : ∀ q, q < count →
          let current := iterate a bPtr resultPtr i q next
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ ptr := by
        intro q hq
        simpa only [next, iterate_advance] using habove (q + 1) (by omega)
      have htail := ih next htailWrites htailAbove
      calc
        memoryWordsFrom (iterate a bPtr resultPtr i (count + 1) state).memory ptr words =
            memoryWordsFrom (iterate a bPtr resultPtr i count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, advance, nextMemory, dest] using hfirst

/-- Generic multiply-pass writes beginning at the concrete frontier preserve complete ranges below
all destinations. -/
theorem multiplyPassIterate_memoryWords_below_extending
    (a : UInt256) (count : Nat) (state : MultiplyPassState) (ptr words : Nat)
    (hstarts : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat ≤ current.memory.size)
    (hbelow : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      ptr + 32 * words ≤ current.resultPtr.toNat) :
    memoryWordsFrom (multiplyPassIterate a count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hfirstStart : state.resultPtr.toNat ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hstarts 0 (by omega)
      have hfirstBelow : ptr + 32 * words ≤ state.resultPtr.toNat := by
        simpa only [multiplyPassIterate] using hbelow 0 (by omega)
      have hfirst := memoryWordsFrom_write_above
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory state.resultPtr.toNat ptr words
        (by rw [toByteArray_size]) hfirstStart hfirstBelow
      have htailStarts : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hstarts (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          ptr + 32 * words ≤ current.resultPtr.toNat := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next htailStarts htailBelow
      calc
        memoryWordsFrom (multiplyPassIterate a (count + 1) state).memory ptr words =
            memoryWordsFrom (multiplyPassIterate a count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, multiplyPassAdvance, multiplyPassMemory] using hfirst

/-- Generic multiply-pass writes crossing bounded implicit-zero gaps preserve complete padded
ranges below every destination. -/
theorem multiplyPassIterate_memoryWords_below_of_gap
    (a : UInt256) (count : Nat) (state : MultiplyPassState) (ptr words : Nat)
    (hbase : 32 ≤ state.memory.size)
    (hgaps : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat - current.memory.size < USize.size)
    (hbelow : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      ptr + 32 * words ≤ current.resultPtr.toNat) :
    memoryWordsFrom (multiplyPassIterate a count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hfirstGap : state.resultPtr.toNat - state.memory.size < USize.size := by
        simpa only [multiplyPassIterate] using hgaps 0 (by omega)
      have hfirstBelow : ptr + 32 * words ≤ state.resultPtr.toNat := by
        simpa only [multiplyPassIterate] using hbelow 0 (by omega)
      have hfirst := memoryWordsFrom_write_above_padded_of_gap
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1 state.memory state.resultPtr.toNat ptr words
        hbase hfirstBelow hfirstGap
      have hnextBase : 32 ≤ next.memory.size := by
        have hsize : next.memory.size =
            max state.memory.size (state.resultPtr.toNat + 32) := by
          dsimp only [next, multiplyPassAdvance, multiplyPassMemory]
          exact toByteArray_write_size_eq_max _ _ _ hfirstGap
        rw [hsize]
        exact hbase.trans (Nat.le_max_left _ _)
      have htailGaps : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hgaps (q + 1) (by omega)
      have htailBelow : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          ptr + 32 * words ≤ current.resultPtr.toNat := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hbelow (q + 1) (by omega)
      have htail := ih next hnextBase htailGaps htailBelow
      calc
        memoryWordsFrom (multiplyPassIterate a (count + 1) state).memory ptr words =
            memoryWordsFrom (multiplyPassIterate a count next).memory ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := by
          simpa only [next, multiplyPassAdvance, multiplyPassMemory] using hfirst

/-- A completed generic multiply pass exposes exactly its output collector even when the first
destination store extends concrete memory at the allocator frontier. -/
theorem multiplyPassOutputWords_eq_finalMemory_extending
    (a : UInt256) (count : Nat) (state : MultiplyPassState)
    (hptr : state.resultPtr.toNat + 32 * count < UInt256.size)
    (hstarts : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat ≤ current.memory.size) :
    multiplyPassOutputWords a count state =
      memoryWordsFrom (multiplyPassIterate a count state).memory state.resultPtr.toNat count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hstepPtr : next.resultPtr.toNat = state.resultPtr.toNat + 32 :=
        uadd_word_lit32_toNat _ (by omega)
      have htailStarts : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hstarts (q + 1) (by omega)
      have htail := ih next (by rw [hstepPtr]; omega) htailStarts
      have hlaterWords := multiplyPassIterate_memoryWords_below_extending a count next
        state.resultPtr.toNat 1 htailStarts (by
          intro q hq
          have hcurrentPtr := multiplyPassIterate_resultPtr_toNat a q next (by
            rw [hstepPtr]
            omega)
          change state.resultPtr.toNat + 32 * 1 ≤
            (multiplyPassIterate a q next).resultPtr.toNat
          rw [hcurrentPtr, hstepPtr]
          omega)
      have hlater : Modexp.MultiLimbMemoryModel.memoryWordNat
            (multiplyPassIterate a count next).memory state.resultPtr.toNat =
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.resultPtr.toNat := by
        exact memoryWordNat_eq_of_memoryWordsFrom_one_eq _ _ _ hlaterWords
      have hfirstStart : state.resultPtr.toNat ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hstarts 0 (by omega)
      have hstored : Modexp.MultiLimbMemoryModel.memoryWordNat next.memory
          state.resultPtr.toNat =
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toNat := by
        apply multiplyPassMemory_word
        rw [Nat.sub_eq_zero_of_le hfirstStart]
        exact lt_usize 0 (by norm_num)
      have hhead : UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat
              (multiplyPassIterate a count next).memory state.resultPtr.toNat) =
          (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
            a state.carry).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hlater, hstored]
      simp only [multiplyPassOutputWords, multiplyPassIterate, memoryWordsFrom]
      change
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
            a state.carry).1 :: multiplyPassOutputWords a count next =
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                (multiplyPassIterate a count next).memory state.resultPtr.toNat) ::
            memoryWordsFrom (multiplyPassIterate a count next).memory
              (state.resultPtr.toNat + 32) count
      rw [← hhead, htail, ← hstepPtr]

/-- A completed generic multiply pass exposes exactly its output collector when any destination
store may cross a bounded implicit-zero gap. -/
theorem multiplyPassOutputWords_eq_finalMemory_of_gap
    (a : UInt256) (count : Nat) (state : MultiplyPassState)
    (hptr : state.resultPtr.toNat + 32 * count < UInt256.size)
    (hgaps : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat - current.memory.size < USize.size) :
    multiplyPassOutputWords a count state =
      memoryWordsFrom (multiplyPassIterate a count state).memory state.resultPtr.toNat count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hstepPtr : next.resultPtr.toNat = state.resultPtr.toNat + 32 :=
        uadd_word_lit32_toNat _ (by omega)
      have hfirstGap : state.resultPtr.toNat - state.memory.size < USize.size := by
        simpa only [multiplyPassIterate] using hgaps 0 (by omega)
      have htailGaps : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hgaps (q + 1) (by omega)
      have htail := ih next (by rw [hstepPtr]; omega) htailGaps
      have hnextBase : 32 ≤ next.memory.size := by
        have hsize : next.memory.size =
            max state.memory.size (state.resultPtr.toNat + 32) := by
          dsimp only [next, multiplyPassAdvance, multiplyPassMemory]
          exact toByteArray_write_size_eq_max _ _ _ hfirstGap
        rw [hsize]
        exact le_trans (by omega : 32 ≤ state.resultPtr.toNat + 32)
          (Nat.le_max_right _ _)
      have hlaterWords := multiplyPassIterate_memoryWords_below_of_gap a count next
        state.resultPtr.toNat 1 hnextBase htailGaps (by
          intro q hq
          have hcurrentPtr := multiplyPassIterate_resultPtr_toNat a q next (by
            rw [hstepPtr]
            omega)
          change state.resultPtr.toNat + 32 * 1 ≤
            (multiplyPassIterate a q next).resultPtr.toNat
          rw [hcurrentPtr, hstepPtr]
          omega)
      have hlater : Modexp.MultiLimbMemoryModel.memoryWordNat
            (multiplyPassIterate a count next).memory state.resultPtr.toNat =
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.resultPtr.toNat := by
        exact memoryWordNat_eq_of_memoryWordsFrom_one_eq _ _ _ hlaterWords
      have hstored : Modexp.MultiLimbMemoryModel.memoryWordNat next.memory
          state.resultPtr.toNat =
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toNat := by
        apply multiplyPassMemory_word
        exact hfirstGap
      have hhead : UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat
              (multiplyPassIterate a count next).memory state.resultPtr.toNat) =
          (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
            a state.carry).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hlater, hstored]
      simp only [multiplyPassOutputWords, multiplyPassIterate, memoryWordsFrom]
      change
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
            a state.carry).1 :: multiplyPassOutputWords a count next =
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                (multiplyPassIterate a count next).memory state.resultPtr.toNat) ::
            memoryWordsFrom (multiplyPassIterate a count next).memory
              (state.resultPtr.toNat + 32) count
      rw [← hhead, htail, ← hstepPtr]

/-- Standalone output collectors likewise equal the final contiguous row memory after
frontier-extending stores. -/
theorem innerOutputWords_eq_finalMemory_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * count <
      UInt256.size)
    (hstarts : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size) :
    innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory
        (elementPtr resultPtr (i + state.j)).toNat count := by
  have hcollectors := innerCollectors_eq_multiplyPassCollectors
    a bPtr resultPtr i count state hbFits hresultFits
  have hmap (q : Nat) (hq : q ≤ count) :
      asMultiplyPassState bPtr resultPtr i (iterate a bPtr resultPtr i q state) =
        multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state) := by
    apply asMultiplyPassState_iterate
    · intro p hp
      exact hbFits p (by omega)
    · intro p hp
      exact hresultFits p (by omega)
  have hgenericStarts : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      current.resultPtr.toNat ≤ current.memory.size := by
    intro q hq
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState] using hstarts q hq
  have houtput := multiplyPassOutputWords_eq_finalMemory_extending a count
    (asMultiplyPassState bPtr resultPtr i state) hresultRange hgenericStarts
  rw [← hmap count (by omega)] at houtput
  rw [hcollectors.2.2]
  simpa only [asMultiplyPassState] using houtput

/-- Standalone output collectors equal the final contiguous row memory when stores may cross
bounded implicit-zero gaps. -/
theorem innerOutputWords_eq_finalMemory_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * count <
      UInt256.size)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size) :
    innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory
        (elementPtr resultPtr (i + state.j)).toNat count := by
  have hcollectors := innerCollectors_eq_multiplyPassCollectors
    a bPtr resultPtr i count state hbFits hresultFits
  have hmap (q : Nat) (hq : q ≤ count) :
      asMultiplyPassState bPtr resultPtr i (iterate a bPtr resultPtr i q state) =
        multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state) := by
    apply asMultiplyPassState_iterate
    · intro p hp
      exact hbFits p (by omega)
    · intro p hp
      exact hresultFits p (by omega)
  have hgenericGaps : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      current.resultPtr.toNat - current.memory.size < USize.size := by
    intro q hq
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState] using hgaps q hq
  have houtput := multiplyPassOutputWords_eq_finalMemory_of_gap a count
    (asMultiplyPassState bPtr resultPtr i state) hresultRange hgenericGaps
  rw [← hmap count (by omega)] at houtput
  rw [hcollectors.2.2]
  simpa only [asMultiplyPassState] using houtput

/-- The standalone row carry load/store preserves covered representable memory and fixed size. -/
theorem carryMemory_coverage_size
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256)
    (hptrFit : (carryPtr resultPtr i bLen).toNat + 32 + 31 < UInt256.size)
    (hwrite : (carryPtr resultPtr i bLen).toNat + 32 ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MemoryCovered (carryMemory mem aw resultPtr i bLen carry)
        (carryWords aw resultPtr i bLen) ∧
      (carryWords aw resultPtr i bLen).toNat * 32 < UInt256.size ∧
      (carryMemory mem aw resultPtr i bLen carry).size = mem.size := by
  let ptr := carryPtr resultPtr i bLen
  have hload := readWords1_coverage mem aw ptr hcovered hawFit
    (by simpa [ptr] using hptrFit)
  have hptrLe : ptr.toNat ≤ mem.size := by
    dsimp only [ptr]
    omega
  have hgap : ptr.toNat - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hptrLe]
    exact lt_usize 0 (by norm_num)
  have hstore := write32_coverage
    (Modexp.MultiLimbDivisionTrace.readWord mem aw ptr + carry)
    mem (afterLoad aw ptr) ptr
    (by simpa [afterLoad] using hload.1) (by simpa [afterLoad] using hload.2)
    (by simpa [ptr] using hptrFit) hgap
  have hsize : (carryMemory mem aw resultPtr i bLen carry).size = mem.size := by
    unfold carryMemory
    exact write_size_of_inBounds_from _ _ 0 ptr.toNat 32
      (by decide) (by rw [toByteArray_size]) (by simpa [ptr] using hwrite)
  refine ⟨?_, ?_, hsize⟩
  · simpa [carryMemory, carryWords, ptr, afterLoad] using hstore.1
  · simpa [carryWords, ptr, afterLoad] using hstore.2

/-- The row carry load/store may occur at the current concrete memory frontier and extend it by
one word while preserving active-word coverage. -/
theorem carryMemory_coverage_extending
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256)
    (hptrFit : (carryPtr resultPtr i bLen).toNat + 32 + 31 < UInt256.size)
    (hwriteStart : (carryPtr resultPtr i bLen).toNat ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MemoryCovered (carryMemory mem aw resultPtr i bLen carry)
        (carryWords aw resultPtr i bLen) ∧
      (carryWords aw resultPtr i bLen).toNat * 32 < UInt256.size ∧
      (carryMemory mem aw resultPtr i bLen carry).size =
        max mem.size ((carryPtr resultPtr i bLen).toNat + 32) := by
  let ptr := carryPtr resultPtr i bLen
  have hload := readWords1_coverage mem aw ptr hcovered hawFit
    (by simpa [ptr] using hptrFit)
  have hgap : ptr.toNat - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by simpa [ptr] using hwriteStart)]
    exact lt_usize 0 (by norm_num)
  have hstore := write32_coverage
    (Modexp.MultiLimbDivisionTrace.readWord mem aw ptr + carry)
    mem (afterLoad aw ptr) ptr
    (by simpa [afterLoad] using hload.1) (by simpa [afterLoad] using hload.2)
    (by simpa [ptr] using hptrFit) hgap
  have hsize : (carryMemory mem aw resultPtr i bLen carry).size =
      max mem.size (ptr.toNat + 32) := by
    unfold carryMemory
    exact toByteArray_write_size_eq_max _ _ _ hgap
  refine ⟨?_, ?_, ?_⟩
  · simpa [carryMemory, carryWords, ptr, afterLoad] using hstore.1
  · simpa [carryWords, ptr, afterLoad] using hstore.2
  · simpa only [ptr] using hsize

/-- The row carry load/store may materialize a bounded implicit-zero gap while preserving
active-word coverage. -/
theorem carryMemory_coverage_of_gap
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256)
    (hptrFit : (carryPtr resultPtr i bLen).toNat + 32 + 31 < UInt256.size)
    (hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MemoryCovered (carryMemory mem aw resultPtr i bLen carry)
        (carryWords aw resultPtr i bLen) ∧
      (carryWords aw resultPtr i bLen).toNat * 32 < UInt256.size ∧
      (carryMemory mem aw resultPtr i bLen carry).size =
        max mem.size ((carryPtr resultPtr i bLen).toNat + 32) := by
  let ptr := carryPtr resultPtr i bLen
  have hload := readWords1_coverage mem aw ptr hcovered hawFit
    (by simpa [ptr] using hptrFit)
  have hstore := write32_coverage
    (Modexp.MultiLimbDivisionTrace.readWord mem aw ptr + carry)
    mem (afterLoad aw ptr) ptr
    (by simpa [afterLoad] using hload.1) (by simpa [afterLoad] using hload.2)
    (by simpa [ptr] using hptrFit) (by simpa only [ptr] using hgap)
  have hsize : (carryMemory mem aw resultPtr i bLen carry).size =
      max mem.size (ptr.toNat + 32) := by
    unfold carryMemory
    exact toByteArray_write_size_eq_max _ _ _ (by simpa only [ptr] using hgap)
  refine ⟨?_, ?_, ?_⟩
  · simpa [carryMemory, carryWords, ptr, afterLoad] using hstore.1
  · simpa [carryWords, ptr, afterLoad] using hstore.2
  · simpa only [ptr] using hsize

/-- The final carry store preserves every complete range below its destination. -/
theorem carryMemory_words_below
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr words : Nat)
    (hwrite : (carryPtr resultPtr i bLen).toNat + 32 ≤ mem.size)
    (hbelow : ptr + 32 * words ≤ (carryPtr resultPtr i bLen).toNat) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr words =
      memoryWordsFrom mem ptr words := by
  exact memoryWordsFrom_write_above
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry).toByteArray
    mem (carryPtr resultPtr i bLen).toNat ptr words (by rw [toByteArray_size])
    (by omega) hbelow

/-- The final carry store preserves every complete range above its destination. -/
theorem carryMemory_words_above
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr words : Nat)
    (hwrite : (carryPtr resultPtr i bLen).toNat + 32 ≤ mem.size)
    (habove : (carryPtr resultPtr i bLen).toNat + 32 ≤ ptr) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr words =
      memoryWordsFrom mem ptr words := by
  exact memoryWordsFrom_write_below
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry).toByteArray
    mem (carryPtr resultPtr i bLen).toNat ptr words (by rw [toByteArray_size]) hwrite habove

/-- A frontier-extending carry store preserves every complete range below its destination. -/
theorem carryMemory_words_below_extending
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr words : Nat)
    (hwriteStart : (carryPtr resultPtr i bLen).toNat ≤ mem.size)
    (hbelow : ptr + 32 * words ≤ (carryPtr resultPtr i bLen).toNat) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr words =
      memoryWordsFrom mem ptr words := by
  exact memoryWordsFrom_write_above
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry).toByteArray
    mem (carryPtr resultPtr i bLen).toNat ptr words (by rw [toByteArray_size])
    hwriteStart hbelow

/-- A frontier-extending carry store preserves every complete padded range above its destination. -/
theorem carryMemory_words_above_extending
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr words : Nat)
    (hwriteStart : (carryPtr resultPtr i bLen).toNat ≤ mem.size)
    (habove : (carryPtr resultPtr i bLen).toNat + 32 ≤ ptr) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr words =
      memoryWordsFrom mem ptr words := by
  exact memoryWordsFrom_write_below_extending
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry)
    mem (carryPtr resultPtr i bLen).toNat ptr words hwriteStart habove

/-- A bounded-gap carry store preserves every complete padded range below its destination. -/
theorem carryMemory_words_below_of_gap
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr words : Nat)
    (hbase : 32 ≤ mem.size)
    (hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size)
    (hbelow : ptr + 32 * words ≤ (carryPtr resultPtr i bLen).toNat) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr words =
      memoryWordsFrom mem ptr words := by
  exact memoryWordsFrom_write_above_padded_of_gap
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry)
    mem (carryPtr resultPtr i bLen).toNat ptr words hbase hbelow hgap

/-- A bounded-gap carry store preserves every complete padded range above its destination. -/
theorem carryMemory_words_above_of_gap
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr words : Nat)
    (hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size)
    (habove : (carryPtr resultPtr i bLen).toNat + 32 ≤ ptr) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr words =
      memoryWordsFrom mem ptr words := by
  exact memoryWordsFrom_write_below_of_gap
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry)
    mem (carryPtr resultPtr i bLen).toNat ptr words hgap habove

/-- When the fresh row-top slot reads as zero, the concrete carry store writes the exact carry
word rather than a wrapped unrelated sum. -/
theorem carryMemory_word_of_read_zero
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256)
    (hzero : Modexp.MultiLimbDivisionTrace.readWord mem aw
      (carryPtr resultPtr i bLen) = ⟨0⟩)
    (hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (carryMemory mem aw resultPtr i bLen carry)
        (carryPtr resultPtr i bLen).toNat = carry.toNat := by
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  simp only [carryMemory]
  rw [hzero, u256_zero_add,
    toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray carry

/-- The zero-top carry store appends the final carry to a completed lower destination range. -/
theorem carryMemory_words_of_read_zero
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr count : Nat)
    (haddress : (carryPtr resultPtr i bLen).toNat = ptr + 32 * count)
    (hzero : Modexp.MultiLimbDivisionTrace.readWord mem aw
      (carryPtr resultPtr i bLen) = ⟨0⟩)
    (hwrite : (carryPtr resultPtr i bLen).toNat + 32 ≤ mem.size) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr (count + 1) =
      memoryWordsFrom mem ptr count ++ [carry] := by
  have hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have hframe := memoryWordsFrom_write_above
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) +
      carry).toByteArray mem (carryPtr resultPtr i bLen).toNat ptr count
    (by rw [toByteArray_size]) (by omega) (by rw [haddress])
  have hword := carryMemory_word_of_read_zero mem aw resultPtr i bLen carry
    hzero hgap
  have hmemory : carryMemory mem aw resultPtr i bLen carry =
      (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) +
        carry).toByteArray.write 0 mem (carryPtr resultPtr i bLen).toNat 32 := by
    rfl
  rw [hmemory] at hword
  rw [Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
  rw [show ptr + 32 * count = (carryPtr resultPtr i bLen).toNat by omega]
  rw [hmemory]
  rw [hframe]
  congr 2
  apply u256_inj
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hword]

/-- The exact carry store appends its carry even when it extends concrete memory at the allocator
frontier. -/
theorem carryMemory_words_of_read_zero_extending
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr count : Nat)
    (haddress : (carryPtr resultPtr i bLen).toNat = ptr + 32 * count)
    (hzero : Modexp.MultiLimbDivisionTrace.readWord mem aw
      (carryPtr resultPtr i bLen) = ⟨0⟩)
    (hwriteStart : (carryPtr resultPtr i bLen).toNat ≤ mem.size) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr (count + 1) =
      memoryWordsFrom mem ptr count ++ [carry] := by
  have hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hwriteStart]
    exact lt_usize 0 (by norm_num)
  have hframe := memoryWordsFrom_write_above
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) +
      carry).toByteArray mem (carryPtr resultPtr i bLen).toNat ptr count
    (by rw [toByteArray_size]) hwriteStart (by rw [haddress])
  have hword := carryMemory_word_of_read_zero mem aw resultPtr i bLen carry
    hzero hgap
  have hmemory : carryMemory mem aw resultPtr i bLen carry =
      (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) +
        carry).toByteArray.write 0 mem (carryPtr resultPtr i bLen).toNat 32 := by
    rfl
  rw [hmemory] at hword
  rw [Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
  rw [show ptr + 32 * count = (carryPtr resultPtr i bLen).toNat by omega]
  rw [hmemory, hframe]
  congr 2
  apply u256_inj
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hword]

/-- The exact zero-top carry store appends its carry when it crosses a bounded implicit-zero
gap. -/
theorem carryMemory_words_of_read_zero_of_gap
    (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) (ptr count : Nat)
    (haddress : (carryPtr resultPtr i bLen).toNat = ptr + 32 * count)
    (hzero : Modexp.MultiLimbDivisionTrace.readWord mem aw
      (carryPtr resultPtr i bLen) = ⟨0⟩)
    (hbase : 32 ≤ mem.size)
    (hgap : (carryPtr resultPtr i bLen).toNat - mem.size < USize.size) :
    memoryWordsFrom (carryMemory mem aw resultPtr i bLen carry) ptr (count + 1) =
      memoryWordsFrom mem ptr count ++ [carry] := by
  have hframe := memoryWordsFrom_write_above_padded_of_gap
    (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) + carry)
    mem (carryPtr resultPtr i bLen).toNat ptr count hbase (by rw [haddress]) hgap
  have hword := carryMemory_word_of_read_zero mem aw resultPtr i bLen carry hzero hgap
  have hmemory : carryMemory mem aw resultPtr i bLen carry =
      (Modexp.MultiLimbDivisionTrace.readWord mem aw (carryPtr resultPtr i bLen) +
        carry).toByteArray.write 0 mem (carryPtr resultPtr i bLen).toNat 32 := by
    rfl
  rw [hmemory] at hword
  rw [Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
  rw [show ptr + 32 * count = (carryPtr resultPtr i bLen).toNat by omega]
  rw [hmemory, hframe]
  congr 2
  apply u256_inj
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hword]

end Modexp.MultiLimbSchoolbookMulTrace
