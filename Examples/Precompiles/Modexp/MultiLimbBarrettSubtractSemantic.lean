import Examples.Precompiles.Modexp.MultiLimbBarrettSubtractContract
import Examples.Precompiles.Modexp.MultiLimbBarrettModel
import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulMemorySemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupSemantic

/-!
# Barrett subtraction semantics

This module identifies the concrete evolving-memory subtraction recurrence with the pure
`evmSubLimbs` model over the words actually loaded by the deployed loop.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbBarrettSubtract

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbSchoolbookMulTrace
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

theorem subtractionElementPtr_ofNat_toNat_of_fit (array : UInt256) (i : Nat)
    (hfit : array.toNat + 32 * (i + 1) < UInt256.size) :
    (elementPtr array (UInt256.ofNat i)).toNat = array.toNat + 32 * (i + 1) := by
  change (Modexp.MultiLimbOddCompare.elementPtr array (UInt256.ofNat i)).toNat = _
  exact Modexp.MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit array i hfit

def subtractionLeftWords (product r2 : UInt256) :
    Nat → BarrettSubtractionState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      (subtractionOperands state.memory state.activeWords product r2
        (UInt256.ofNat state.i)).1 ::
      subtractionLeftWords product r2 count (subtractionAdvance product r2 state)

def subtractionRightWords (product r2 : UInt256) :
    Nat → BarrettSubtractionState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      (subtractionOperands state.memory state.activeWords product r2
        (UInt256.ofNat state.i)).2 ::
      subtractionRightWords product r2 count (subtractionAdvance product r2 state)

def subtractionOutputWords (product r2 : UInt256) :
    Nat → BarrettSubtractionState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      (subtractionStep state.memory state.activeWords product r2
        (UInt256.ofNat state.i) state.borrow).1 ::
      subtractionOutputWords product r2 count (subtractionAdvance product r2 state)

@[simp] theorem subtractionLeftWords_length
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    (subtractionLeftWords product r2 count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [subtractionLeftWords, ih]

@[simp] theorem subtractionRightWords_length
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    (subtractionRightWords product r2 count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [subtractionRightWords, ih]

@[simp] theorem subtractionOutputWords_length
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    (subtractionOutputWords product r2 count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [subtractionOutputWords, ih]

/-- The exact bytecode recurrence is pure limb subtraction over its concrete loaded words. -/
theorem subtractionCollectors_eq_evmSubLimbs
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    Modexp.evmSubLimbs
      (subtractionLeftWords product r2 count state)
      (subtractionRightWords product r2 count state) state.borrow =
      (subtractionOutputWords product r2 count state,
        (subtractionIterate product r2 count state).borrow) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      simp only [subtractionLeftWords, subtractionRightWords, subtractionOutputWords,
        Modexp.evmSubLimbs, subtractionIterate]
      let digit := subtractionStep state.memory state.activeWords product r2
        (UInt256.ofNat state.i) state.borrow
      change
        (digit.1 ::
            (Modexp.evmSubLimbs
              (subtractionLeftWords product r2 count
                (subtractionAdvance product r2 state))
              (subtractionRightWords product r2 count
                (subtractionAdvance product r2 state)) digit.2).1,
          (Modexp.evmSubLimbs
            (subtractionLeftWords product r2 count
              (subtractionAdvance product r2 state))
            (subtractionRightWords product r2 count
              (subtractionAdvance product r2 state)) digit.2).2) =
        (digit.1 :: subtractionOutputWords product r2 count
            (subtractionAdvance product r2 state),
          (subtractionIterate product r2 count
            (subtractionAdvance product r2 state)).borrow)
      have hborrow : digit.2 = (subtractionAdvance product r2 state).borrow := by
        rfl
      rw [hborrow, ih (subtractionAdvance product r2 state)]

/-- The collectors satisfy the pure model's exact unbounded radix equation. -/
theorem subtractionCollectors_recompose
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState)
    (hborrow : state.borrow = ⟨0⟩ ∨ state.borrow = ⟨1⟩) :
    Modexp.wordLimbsToNat (subtractionOutputWords product r2 count state) +
        Modexp.wordLimbsToNat (subtractionRightWords product r2 count state) +
        state.borrow.toNat =
      Modexp.wordLimbsToNat (subtractionLeftWords product r2 count state) +
        UInt256.size ^ count *
          (subtractionIterate product r2 count state).borrow.toNat := by
  have hpure := Modexp.evmSubLimbs_recompose
    (subtractionLeftWords product r2 count state)
    (subtractionRightWords product r2 count state) state.borrow
    (by simp) hborrow
  rw [subtractionCollectors_eq_evmSubLimbs] at hpure
  simpa using hpure

/-- From the deployed zero-borrow entry, the output collectors are exactly equal-width
subtraction modulo `B^count`. -/
theorem subtractionCollectors_fromZero_value
    (mem : ByteArray) (aw product r2 : UInt256) (count : Nat) :
    let initial := subtractionInitialState mem aw
    Modexp.wordLimbsToNat (subtractionOutputWords product r2 count initial) =
      if Modexp.wordLimbsToNat (subtractionRightWords product r2 count initial) ≤
          Modexp.wordLimbsToNat (subtractionLeftWords product r2 count initial) then
        Modexp.wordLimbsToNat (subtractionLeftWords product r2 count initial) -
          Modexp.wordLimbsToNat (subtractionRightWords product r2 count initial)
      else
        Modexp.wordLimbsToNat (subtractionLeftWords product r2 count initial) +
            UInt256.size ^ count -
          Modexp.wordLimbsToNat (subtractionRightWords product r2 count initial) := by
  let initial := subtractionInitialState mem aw
  have hpure := Modexp.evmSubLimbs_value
    (subtractionLeftWords product r2 count initial)
    (subtractionRightWords product r2 count initial) (by simp)
  have hcollect := subtractionCollectors_eq_evmSubLimbs product r2 count initial
  have hborrow : initial.borrow = ⟨0⟩ := by rfl
  rw [hborrow] at hcollect
  rw [hcollect] at hpure
  simpa [initial, subtractionInitialState] using hpure

/-- One product-minus-r2 column preserves covered representable memory and the size of the
already materialized r2 allocation. -/
theorem subtractionAdvance_coverage_size
    (product r2 : UInt256) (state : BarrettSubtractionState)
    (hproductFit : (elementPtr product (UInt256.ofNat state.i)).toNat + 32 + 31 <
      UInt256.size)
    (hr2Fit : (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 + 31 < UInt256.size)
    (_hproductMem : (elementPtr product (UInt256.ofNat state.i)).toNat + 32 ≤
      state.memory.size)
    (hr2Mem : (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (subtractionAdvance product r2 state).memory
        (subtractionAdvance product r2 state).activeWords ∧
      (subtractionAdvance product r2 state).activeWords.toNat * 32 < UInt256.size ∧
      (subtractionAdvance product r2 state).memory.size = state.memory.size := by
  let productPtr := elementPtr product (UInt256.ofNat state.i)
  let r2Ptr := elementPtr r2 (UInt256.ofNat state.i)
  have hleft := readWords1_coverage state.memory state.activeWords productPtr
    hcovered hawFit (by simpa only [productPtr] using hproductFit)
  have hright := readWords1_coverage state.memory (afterLoad state.activeWords productPtr) r2Ptr
    (by simpa only [afterLoad] using hleft.1) (by simpa only [afterLoad] using hleft.2)
    (by simpa only [r2Ptr] using hr2Fit)
  have hgap : r2Ptr.toNat - state.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by
      have hword : r2Ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [r2Ptr] using hr2Mem
      omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite := write32_coverage
    (subtractionStep state.memory state.activeWords product r2
      (UInt256.ofNat state.i) state.borrow).1
    state.memory (afterLoad (afterLoad state.activeWords productPtr) r2Ptr) r2Ptr
    (by simpa only [afterLoad] using hright.1) (by simpa only [afterLoad] using hright.2)
    (by simpa only [r2Ptr] using hr2Fit) hgap
  have hsize : (subtractionAdvance product r2 state).memory.size = state.memory.size := by
    unfold subtractionAdvance subtractionMemory
    exact write_size_of_inBounds_from _ _ 0 r2Ptr.toNat 32
      (by decide) (by rw [toByteArray_size]) (by simpa only [r2Ptr] using hr2Mem)
  refine ⟨?_, ?_, hsize⟩
  · simpa [subtractionAdvance, subtractionMemory, subtractionWords, subtractionPtr,
      productPtr, r2Ptr, afterLoad] using hwrite.1
  · simpa [subtractionAdvance, subtractionWords, subtractionPtr,
      productPtr, r2Ptr, afterLoad] using hwrite.2

/-- Coverage, representability, and fixed allocated size propagate through all subtraction
columns. -/
theorem subtractionIterate_coverage_size
    (count : Nat) (product r2 : UInt256) (state : BarrettSubtractionState)
    (hproductFit : product.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hproductMem : product.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hr2Mem : r2.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (subtractionIterate product r2 count state).memory
        (subtractionIterate product r2 count state).activeWords ∧
      (subtractionIterate product r2 count state).activeWords.toNat * 32 < UInt256.size ∧
      (subtractionIterate product r2 count state).memory.size = state.memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, rfl⟩
  | succ count ih =>
      have hproductAddress : (elementPtr product (UInt256.ofNat state.i)).toNat =
          product.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit product state.i (by omega)
      have hr2Address : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hadvance := subtractionAdvance_coverage_size product r2 state
        (by rw [hproductAddress]; omega) (by rw [hr2Address]; omega)
        (by rw [hproductAddress]; omega) (by rw [hr2Address]; omega) hcovered hawFit
      let next := subtractionAdvance product r2 state
      have hnextI : next.i = state.i + 1 := by rfl
      have hrest := ih next
        (by rw [hnextI]; omega) (by rw [hnextI]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI, hadvance.2.2]; omega) hadvance.1 hadvance.2.1
      simpa only [next, subtractionIterate] using
        And.intro hrest.1 (And.intro hrest.2.1 (hrest.2.2.trans hadvance.2.2))

/-- The concrete subtraction collectors are the original product and r2 slices.  Earlier r2
writes are below later r2 reads and above the disjoint product allocation. -/
theorem subtractionCollectors_eq_memoryWordsFrom
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState)
    (hproductFit : product.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hproductMem : product.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hr2Mem : r2.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hdisjoint : product.toNat + 32 * (state.i + count + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    subtractionLeftWords product r2 count state =
        memoryWordsFrom state.memory (product.toNat + 32 * (state.i + 1)) count ∧
      subtractionRightWords product r2 count state =
        memoryWordsFrom state.memory (r2.toNat + 32 * (state.i + 1)) count := by
  induction count generalizing state with
  | zero => simp [subtractionLeftWords, subtractionRightWords, memoryWordsFrom]
  | succ count ih =>
      have hproductAddress : (elementPtr product (UInt256.ofNat state.i)).toNat =
          product.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit product state.i (by omega)
      have hr2Address : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hadvance := subtractionAdvance_coverage_size product r2 state
        (by rw [hproductAddress]; omega) (by rw [hr2Address]; omega)
        (by rw [hproductAddress]; omega) (by rw [hr2Address]; omega) hcovered hawFit
      let next := subtractionAdvance product r2 state
      have hnextI : next.i = state.i + 1 := by rfl
      have hrest := ih next
        (by rw [hnextI]; omega) (by rw [hnextI]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI]; omega) hadvance.1 hadvance.2.1
      have hleftWord :
          (subtractionOperands state.memory state.activeWords product r2
            (UInt256.ofNat state.i)).1 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              (product.toNat + 32 * (state.i + 1))) := by
        have hread := readWord_eq_memoryWordOf_covered state.memory state.activeWords
          (elementPtr product (UInt256.ofNat state.i)) hcovered hawFit
          (by rw [hproductAddress]; omega)
        simpa [subtractionOperands, subtractionPtr, hproductAddress] using hread
      have hleftCoverage := readWords1_coverage state.memory state.activeWords
        (elementPtr product (UInt256.ofNat state.i)) hcovered hawFit
        (by rw [hproductAddress]; omega)
      have hrightWord :
          (subtractionOperands state.memory state.activeWords product r2
            (UInt256.ofNat state.i)).2 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              (r2.toNat + 32 * (state.i + 1))) := by
        have hread := readWord_eq_memoryWordOf_covered state.memory
          (afterLoad state.activeWords (elementPtr product (UInt256.ofNat state.i)))
          (elementPtr r2 (UInt256.ofNat state.i))
          (by simpa only [afterLoad] using hleftCoverage.1)
          (by simpa only [afterLoad] using hleftCoverage.2)
          (by rw [hr2Address]; omega)
        simpa [subtractionOperands, subtractionPtr, hr2Address] using hread
      have hleftFrame :
          memoryWordsFrom next.memory (product.toNat + 32 * (next.i + 1)) count =
            memoryWordsFrom state.memory (product.toNat + 32 * (state.i + 2)) count := by
        have hframe := memoryWordsFrom_write_above
          (subtractionStep state.memory state.activeWords product r2
            (UInt256.ofNat state.i) state.borrow).1.toByteArray
          state.memory (elementPtr r2 (UInt256.ofNat state.i)).toNat
          (product.toNat + 32 * (state.i + 2)) count
          (by rw [toByteArray_size]) (by rw [hr2Address]; omega)
          (by rw [hr2Address]; omega)
        simpa [next, subtractionAdvance, subtractionMemory, hnextI] using hframe
      have hrightFrame :
          memoryWordsFrom next.memory (r2.toNat + 32 * (next.i + 1)) count =
            memoryWordsFrom state.memory (r2.toNat + 32 * (state.i + 2)) count := by
        have hframe := memoryWordsFrom_write_below
          (subtractionStep state.memory state.activeWords product r2
            (UInt256.ofNat state.i) state.borrow).1.toByteArray
          state.memory (elementPtr r2 (UInt256.ofNat state.i)).toNat
          (r2.toNat + 32 * (state.i + 2)) count
          (by rw [toByteArray_size]) (by rw [hr2Address]; omega)
          (by rw [hr2Address]; omega)
        simpa [next, subtractionAdvance, subtractionMemory, hnextI] using hframe
      constructor
      · simp only [subtractionLeftWords]
        rw [hrest.1, hleftFrame, hleftWord]
        simp only [memoryWordsFrom]
        rw [show product.toNat + 32 * (state.i + 2) =
          product.toNat + 32 * (state.i + 1) + 32 by omega]
      · simp only [subtractionRightWords]
        rw [hrest.2, hrightFrame, hrightWord]
        simp only [memoryWordsFrom]
        rw [show r2.toNat + 32 * (state.i + 2) =
          r2.toNat + 32 * (state.i + 1) + 32 by omega]

/-- Later subtraction writes preserve an already written lower word. -/
theorem subtractionIterate_read_below
    (count : Nat) (product r2 : UInt256) (state : BarrettSubtractionState) (read : Nat)
    (hwrites : ∀ j, j < count →
      let current := subtractionIterate product r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size ∧
        read + 32 ≤ (elementPtr r2 (UInt256.ofNat current.i)).toNat) :
    (subtractionIterate product r2 count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := subtractionAdvance product r2 state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count →
          let current := subtractionIterate product r2 j next
          (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size ∧
            read + 32 ≤ (elementPtr r2 (UInt256.ofNat current.i)).toNat := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstInBounds :
          (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size := by
        simpa only [subtractionIterate] using hfirst.1
      rw [subtractionIterate, hrest]
      unfold next subtractionAdvance subtractionMemory
      unfold subtractionPtr
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirst.2

/-- Every subtraction write is at or above the first r2 payload word, so a complete prior range
below that boundary is preserved by an arbitrary loop prefix. -/
theorem subtractionIterate_memoryWords_below
    (count : Nat) (product r2 : UInt256) (state : BarrettSubtractionState)
    (ptr words : Nat)
    (hproductFit : product.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hproductMem : product.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hr2Mem : r2.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbelow : ptr + 32 * words ≤ r2.toNat + 32 * (state.i + 1)) :
    memoryWordsFrom (subtractionIterate product r2 count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      have hproductAddress : (elementPtr product (UInt256.ofNat state.i)).toNat =
          product.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit product state.i (by omega)
      have hr2Address : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hadvance := subtractionAdvance_coverage_size product r2 state
        (by rw [hproductAddress]; omega) (by rw [hr2Address]; omega)
        (by rw [hproductAddress]; omega) (by rw [hr2Address]; omega) hcovered hawFit
      let next := subtractionAdvance product r2 state
      have hnextI : next.i = state.i + 1 := by rfl
      have hhead : memoryWordsFrom next.memory ptr words =
          memoryWordsFrom state.memory ptr words := by
        have hframe := memoryWordsFrom_write_above
          (subtractionStep state.memory state.activeWords product r2
            (UInt256.ofNat state.i) state.borrow).1.toByteArray
          state.memory (elementPtr r2 (UInt256.ofNat state.i)).toNat ptr words
          (by rw [toByteArray_size]) (by rw [hr2Address]; omega)
          (by rw [hr2Address]; exact hbelow)
        simpa only [next, subtractionAdvance, subtractionMemory] using hframe
      have htail := ih next
        (by rw [hnextI]; omega) (by rw [hnextI]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        hadvance.1 hadvance.2.1 (by rw [hnextI]; omega)
      simpa only [next, subtractionIterate] using htail.trans hhead

/-- One in-bounds subtraction store records its arithmetic output word. -/
theorem subtractionMemory_word
    (mem : ByteArray) (aw product r2 i borrow : UInt256)
    (hgap : (elementPtr r2 i).toNat - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (subtractionMemory mem aw product r2 i borrow) (elementPtr r2 i).toNat =
      (subtractionStep mem aw product r2 i borrow).1.toNat := by
  unfold subtractionMemory subtractionPtr Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- The subtraction output collector is exactly the final contiguous r2 range written by the
loop. -/
theorem subtractionOutputWords_eq_finalMemoryWords
    (count : Nat) (product r2 : UInt256) (state : BarrettSubtractionState)
    (hfit : r2.toNat + 32 * (state.i + count + 1) < UInt256.size)
    (hwrites : ∀ j, j < count →
      let current := subtractionIterate product r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size) :
    subtractionOutputWords product r2 count state =
      memoryWordsFrom (subtractionIterate product r2 count state).memory
        (r2.toNat + 32 * (state.i + 1)) count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := subtractionAdvance product r2 state
      have hfirstWrite :
          (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size := by
        simpa only [subtractionIterate] using hwrites 0 (by omega)
      have haddress : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        subtractionElementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hnextI : next.i = state.i + 1 := by rfl
      have hnextWrites : ∀ j, j < count →
          let current := subtractionIterate product r2 j next
          (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hnextI]; omega) hnextWrites
      have hgap : (elementPtr r2 (UInt256.ofNat state.i)).toNat - state.memory.size <
          USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        exact lt_usize 0 (by norm_num)
      have hstored :
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory
              (r2.toNat + 32 * (state.i + 1)) =
            (subtractionStep state.memory state.activeWords product r2
              (UInt256.ofNat state.i) state.borrow).1.toNat := by
        simpa [next, subtractionAdvance, haddress] using
          subtractionMemory_word state.memory state.activeWords product r2
            (UInt256.ofNat state.i) state.borrow hgap
      have hlater :
          (subtractionIterate product r2 count next).memory.readWithPadding
              (r2.toNat + 32 * (state.i + 1)) 32 =
            next.memory.readWithPadding (r2.toNat + 32 * (state.i + 1)) 32 := by
        apply subtractionIterate_read_below count product r2 next
        intro j hj
        let current := subtractionIterate product r2 j next
        have hwrite := hnextWrites j hj
        have hi : current.i = state.i + 1 + j := by
          change (subtractionIterate product r2 j next).i = _
          rw [subtractionIterate_i, hnextI]
        have hcurrentAddress :
            (elementPtr r2 (UInt256.ofNat current.i)).toNat =
              r2.toNat + 32 * (current.i + 1) :=
          subtractionElementPtr_ofNat_toNat_of_fit r2 current.i (by rw [hi]; omega)
        refine ⟨hwrite, ?_⟩
        rw [hcurrentAddress, hi]
        omega
      have hhead :
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              (subtractionIterate product r2 count next).memory
              (r2.toNat + 32 * (state.i + 1))) =
            (subtractionStep state.memory state.activeWords product r2
              (UInt256.ofNat state.i) state.borrow).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hlater]
        exact hstored
      simp only [subtractionOutputWords, subtractionIterate, memoryWordsFrom]
      rw [← hhead, htail]
      rw [show r2.toNat + 32 * (next.i + 1) =
        r2.toNat + 32 * (state.i + 1) + 32 by rw [hnextI]; omega]

/-- From the deployed zero-borrow entry, the final concrete r2 window is equal-width modular
subtraction of the initial product and r2 windows. -/
theorem subtractionFromZero_finalMemory_value
    (count : Nat) (mem : ByteArray) (aw product r2 : UInt256)
    (hproductFit : product.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hproductMem : product.toNat + 32 * (count + 1) ≤ mem.size)
    (hr2Mem : r2.toNat + 32 * (count + 1) ≤ mem.size)
    (hdisjoint : product.toNat + 32 * (count + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let initial := subtractionInitialState mem aw
    let final := subtractionIterate product r2 count initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) count) =
      (Modexp.wordLimbsToNat (memoryWordsFrom mem (product.toNat + 32) count) +
        UInt256.size ^ count -
        Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) count)) %
        UInt256.size ^ count := by
  let initial := subtractionInitialState mem aw
  let final := subtractionIterate product r2 count initial
  have hinputs := subtractionCollectors_eq_memoryWordsFrom product r2 count initial
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simpa [initial, subtractionInitialState] using hdisjoint)
    (by simpa [initial, subtractionInitialState] using hcovered)
    (by simpa [initial, subtractionInitialState] using hawFit)
  have hcoverage := subtractionIterate_coverage_size count product r2 initial
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simp [initial, subtractionInitialState]; omega)
    (by simpa [initial, subtractionInitialState] using hcovered)
    (by simpa [initial, subtractionInitialState] using hawFit)
  have hwrites : ∀ j, j < count →
      let current := subtractionIterate product r2 j initial
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := subtractionIterate product r2 j initial
    have hi : current.i = j := by
      simpa [current, initial, subtractionInitialState] using
        subtractionIterate_i product r2 j initial
    have haddr : (elementPtr r2 (UInt256.ofNat current.i)).toNat =
        r2.toNat + 32 * (j + 1) := by
      rw [subtractionElementPtr_ofNat_toNat_of_fit r2 current.i (by rw [hi]; omega), hi]
    have hcurrentCoverage := subtractionIterate_coverage_size j product r2 initial
      (by simp [initial, subtractionInitialState]; omega)
      (by simp [initial, subtractionInitialState]; omega)
      (by simp [initial, subtractionInitialState]; omega)
      (by simp [initial, subtractionInitialState]; omega)
      (by simpa [initial, subtractionInitialState] using hcovered)
      (by simpa [initial, subtractionInitialState] using hawFit)
    dsimp only
    rw [haddr]
    have hsize : current.memory.size = mem.size := by
      simpa [current, initial, subtractionInitialState] using hcurrentCoverage.2.2
    rw [hsize]
    omega
  have houtputs := subtractionOutputWords_eq_finalMemoryWords count product r2 initial
    (by simp [initial, subtractionInitialState]; omega) hwrites
  have hpure := subtractionCollectors_fromZero_value mem aw product r2 count
  have hinputs' : subtractionLeftWords product r2 count initial =
        memoryWordsFrom mem (product.toNat + 32) count ∧
      subtractionRightWords product r2 count initial =
        memoryWordsFrom mem (r2.toNat + 32) count := by
    simpa [initial, subtractionInitialState] using hinputs
  have houtputs' : subtractionOutputWords product r2 count initial =
      memoryWordsFrom final.memory (r2.toNat + 32) count := by
    simpa [initial, final, subtractionInitialState] using houtputs
  dsimp only at hpure ⊢
  rw [hinputs'.1, hinputs'.2, houtputs'] at hpure
  have hleftBound := Modexp.wordLimbsToNat_lt_pow
    (memoryWordsFrom mem (product.toNat + 32) count)
  have hrightBound := Modexp.wordLimbsToNat_lt_pow
    (memoryWordsFrom mem (r2.toNat + 32) count)
  rw [memoryWordsFrom_length] at hleftBound hrightBound
  split at hpure
  · rename_i hle
    rw [hpure]
    have hdiff : Modexp.wordLimbsToNat (memoryWordsFrom mem (product.toNat + 32) count) +
          UInt256.size ^ count -
          Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) count) =
        Modexp.wordLimbsToNat (memoryWordsFrom mem (product.toNat + 32) count) -
          Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) count) +
          UInt256.size ^ count := by omega
    calc
      _ = (Modexp.wordLimbsToNat (memoryWordsFrom mem (product.toNat + 32) count) -
            Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) count)) %
          UInt256.size ^ count := (Nat.mod_eq_of_lt (by omega)).symm
      _ = (Modexp.wordLimbsToNat (memoryWordsFrom mem (product.toNat + 32) count) -
              Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) count) +
            UInt256.size ^ count) % UInt256.size ^ count := by
          simp
      _ = _ := by rw [← hdiff]
  · rename_i hnotLe
    rw [hpure]
    exact (Nat.mod_eq_of_lt (by omega)).symm

/-- Once the two concrete input windows are identified with the low full product and truncated
`q3*n`, the executed in-place subtraction stores exactly the deployed pure Barrett candidate. -/
theorem subtractionFromZero_finalMemory_deployedCandidate
    (kWords : Nat) (mem : ByteArray) (aw product r2 : UInt256) (nValue x : Nat)
    (hkPos : 0 < kWords)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hnFits : nValue < UInt256.size ^ kWords)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hproductFit : product.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hproductMem : product.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hdisjoint : product.toNat + 32 * (kWords + 2) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hproductValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (product.toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1))
    (hr2Value : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (r2.toNat + 32) (kWords + 1)) =
        (Modexp.barrettQ3 kWords nValue x * nValue) %
          UInt256.size ^ (kWords + 1)) :
    let initial := subtractionInitialState mem aw
    let final := subtractionIterate product r2 (kWords + 1) initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (r2.toNat + 32) (kWords + 1)) =
      Modexp.deployedBarrettCandidate kWords nValue x := by
  have hsub := subtractionFromZero_finalMemory_value (kWords + 1) mem aw product r2
    hproductFit hr2Fit hproductMem hr2Mem hdisjoint hcovered hawFit
  dsimp only at hsub ⊢
  rw [hproductValue, hr2Value] at hsub
  rw [hsub]
  exact Modexp.deployedBarrettCandidate_eq_wrappedResidueSub
    kWords nValue x hkPos hnPos hnNormalized hnFits hx

/-! ## Result-allocation boundary -/

/-- The result allocation materializes only its header; this also materializes every earlier
padded word through the end of the preceding r2 allocation. -/
theorem resultAllocatedMemory_size
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (resultAllocatedMemory mem fp kWords).size = fp + 32 := by
  unfold resultAllocatedMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- The exact result allocator preserves covered, representable memory. -/
theorem resultAllocatedMemory_coverage
    (mem : ByteArray) (aw : UInt256) (fp kWords : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize kWords < 2 ^ 64) :
    MemoryCovered (resultAllocatedMemory mem fp kWords)
        (resultAllocatedWords aw fp kWords) ∧
      (resultAllocatedWords aw fp kWords).toNat * 32 < UInt256.size := by
  simpa only [resultAllocatedMemory, resultAllocatedWords] using
    allocatedWordArray_coverage mem aw fp kWords hcovered hawFit hmemSize hmemLe hgap hbound

/-- The result pointer returned by the allocator is the ordinary current free pointer. -/
theorem resultAllocatedPtr_toNat
    (fp kWords : Nat) (hbound : fp + wordArrayAllocationSize kWords < 2 ^ 64) :
    (UInt256.ofNat fp).toNat = fp := by
  apply UInt256.toNat_ofNat_of_lt
  exact (show fp < 2 ^ 64 by omega).trans (by decide)

/-- A complete prior word range at or above Solidity's reserved memory is unchanged by the
following result-array allocation. -/
theorem resultAllocatedMemory_words_below
    (mem : ByteArray) (fp kWords ptr count : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size)
    (hptr : 96 ≤ ptr) (hbelow : ptr + 32 * count ≤ fp) :
    memoryWordsFrom (resultAllocatedMemory mem fp kWords) ptr count =
      memoryWordsFrom mem ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      have hhead :=
        Modexp.MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
          mem fp kWords ptr hmemSize hgap hptr (by omega)
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (resultAllocatedMemory mem fp kWords) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr := by
        unfold resultAllocatedMemory Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hhead]
      simp only [memoryWordsFrom]
      rw [hword, ih (ptr := ptr + 32) (by omega) (by omega)]

/-! ## Correction-pass collectors -/

/-- Words loaded from the evolving r2 buffer by the ordinary `i < k` correction columns. -/
def correctionLeftWords (n r2 : UInt256) :
    Nat → CorrectionSubtractionState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      (correctionOperands state.memory state.activeWords n r2
        (UInt256.ofNat state.i)).1 ::
      correctionLeftWords n r2 count (correctionAdvance n r2 state)

/-- Words loaded from the modulus by the ordinary `i < k` correction columns. -/
def correctionRightWords (n r2 : UInt256) :
    Nat → CorrectionSubtractionState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      (correctionOperands state.memory state.activeWords n r2
        (UInt256.ofNat state.i)).2 ::
      correctionRightWords n r2 count (correctionAdvance n r2 state)

/-- Words stored into r2 by the ordinary `i < k` correction columns. -/
def correctionOutputWords (n r2 : UInt256) :
    Nat → CorrectionSubtractionState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      (correctionStep state.memory state.activeWords n r2
        (UInt256.ofNat state.i) state.borrow).1 ::
      correctionOutputWords n r2 count (correctionAdvance n r2 state)

@[simp] theorem correctionLeftWords_length
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionLeftWords n r2 count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [correctionLeftWords, ih]

@[simp] theorem correctionRightWords_length
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionRightWords n r2 count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [correctionRightWords, ih]

@[simp] theorem correctionOutputWords_length
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionOutputWords n r2 count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [correctionOutputWords, ih]

/-- The ordinary correction columns are pure propagated limb subtraction over exactly the words
loaded and stored by the deployed loop. -/
theorem correctionCollectors_eq_evmSubLimbs
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    Modexp.evmSubLimbs
      (correctionLeftWords n r2 count state)
      (correctionRightWords n r2 count state) state.borrow =
      (correctionOutputWords n r2 count state,
        (correctionIterate n r2 count state).borrow) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      simp only [correctionLeftWords, correctionRightWords, correctionOutputWords,
        Modexp.evmSubLimbs, correctionIterate]
      let digit := correctionStep state.memory state.activeWords n r2
        (UInt256.ofNat state.i) state.borrow
      change
        (digit.1 ::
            (Modexp.evmSubLimbs
              (correctionLeftWords n r2 count (correctionAdvance n r2 state))
              (correctionRightWords n r2 count (correctionAdvance n r2 state))
              digit.2).1,
          (Modexp.evmSubLimbs
            (correctionLeftWords n r2 count (correctionAdvance n r2 state))
            (correctionRightWords n r2 count (correctionAdvance n r2 state))
            digit.2).2) =
        (digit.1 :: correctionOutputWords n r2 count (correctionAdvance n r2 state),
          (correctionIterate n r2 count (correctionAdvance n r2 state)).borrow)
      have hborrow : digit.2 = (correctionAdvance n r2 state).borrow := by
        rfl
      rw [hborrow, ih (correctionAdvance n r2 state)]

/-- Include the source's terminal `r2[k] - 0 - borrow` column in the pure input vectors. -/
def correctionPassLeftWords (n r2 : UInt256) (count : Nat)
    (state : CorrectionSubtractionState) : List UInt256 :=
  let beforeFinal := correctionIterate n r2 count state
  correctionLeftWords n r2 count state ++
    [readWord beforeFinal.memory beforeFinal.activeWords
      (elementPtr r2 (UInt256.ofNat beforeFinal.i))]

def correctionPassRightWords (n r2 : UInt256) (count : Nat)
    (state : CorrectionSubtractionState) : List UInt256 :=
  correctionRightWords n r2 count state ++ [⟨0⟩]

def correctionPassOutputWords (n r2 : UInt256) (count : Nat)
    (state : CorrectionSubtractionState) : List UInt256 :=
  let beforeFinal := correctionIterate n r2 count state
  correctionOutputWords n r2 count state ++
    [(correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1]

private theorem evmSubLimbs_append_one
    (left right : List UInt256) (leftLast rightLast borrow : UInt256)
    (hlength : left.length = right.length) :
    let prior := Modexp.evmSubLimbs left right borrow
    let last := Modexp.evmSubBorrow leftLast rightLast prior.2
    Modexp.evmSubLimbs (left ++ [leftLast]) (right ++ [rightLast]) borrow =
      (prior.1 ++ [last.1], last.2) := by
  induction left generalizing right borrow with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      rfl
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htail : lefts.length = rights.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlength
          simp only [List.cons_append, Modexp.evmSubLimbs]
          rw [ih rights (Modexp.evmSubBorrow left right borrow).2 htail]

/-- A complete selected correction pass, including its extra top word, is exactly
`evmSubLimbs` against the modulus extended by zero. -/
theorem correctionPassCollectors_eq_evmSubLimbs
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    let beforeFinal := correctionIterate n r2 count state
    Modexp.evmSubLimbs
      (correctionPassLeftWords n r2 count state)
      (correctionPassRightWords n r2 count state) state.borrow =
      (correctionPassOutputWords n r2 count state,
        (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
          (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).2) := by
  let beforeFinal := correctionIterate n r2 count state
  have hordinary := correctionCollectors_eq_evmSubLimbs n r2 count state
  rw [show (correctionIterate n r2 count state) = beforeFinal by rfl] at hordinary
  simp only [correctionPassLeftWords, correctionPassRightWords,
    correctionPassOutputWords]
  rw [evmSubLimbs_append_one _ _ _ _ _
    (correctionLeftWords_length n r2 count state |>.trans
      (correctionRightWords_length n r2 count state).symm)]
  rw [hordinary]
  rfl

@[simp] theorem correctionPassLeftWords_length
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionPassLeftWords n r2 count state).length = count + 1 := by
  simp [correctionPassLeftWords]

@[simp] theorem correctionPassRightWords_length
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionPassRightWords n r2 count state).length = count + 1 := by
  simp [correctionPassRightWords]

@[simp] theorem correctionPassOutputWords_length
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionPassOutputWords n r2 count state).length = count + 1 := by
  simp [correctionPassOutputWords]

/-- From zero borrow, a selected correction pass is ordinary natural subtraction whenever its
extended modulus collector is no larger than its extended r2 collector. -/
theorem correctionPassCollectors_fromZero_eq_sub
    (n r2 : UInt256) (count : Nat) (mem : ByteArray) (aw : UInt256)
    (hge : Modexp.wordLimbsToNat
          (correctionPassRightWords n r2 count (correctionInitialState mem aw)) ≤
        Modexp.wordLimbsToNat
          (correctionPassLeftWords n r2 count (correctionInitialState mem aw))) :
    Modexp.wordLimbsToNat
        (correctionPassOutputWords n r2 count (correctionInitialState mem aw)) =
      Modexp.wordLimbsToNat
          (correctionPassLeftWords n r2 count (correctionInitialState mem aw)) -
        Modexp.wordLimbsToNat
          (correctionPassRightWords n r2 count (correctionInitialState mem aw)) := by
  let initial := correctionInitialState mem aw
  have hmodel := Modexp.evmSubLimbs_eq_sub
    (correctionPassLeftWords n r2 count initial)
    (correctionPassRightWords n r2 count initial)
    (by simp) (by simpa [initial] using hge)
  have hcollect := correctionPassCollectors_eq_evmSubLimbs n r2 count initial
  have hborrow : initial.borrow = ⟨0⟩ := by rfl
  rw [hborrow] at hcollect
  rw [hcollect] at hmodel
  simpa [initial] using hmodel.2

end Modexp.MultiLimbBarrettSubtract
