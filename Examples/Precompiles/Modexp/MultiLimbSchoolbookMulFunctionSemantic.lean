import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulOuterSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulFunction

/-! # Standalone schoolbook function semantics -/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookMulTrace

open Modexp.MultiLimbMontgomeryCIOSSemantic

/-- A complete EVM word starting at or beyond the concrete byte-array end is zero. -/
theorem memoryWordNat_past_end_zero (mem : ByteArray) (ptr : Nat)
    (hpast : mem.size ≤ ptr) :
    Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr = 0 := by
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [readWithPadding_past_end mem ptr 32 hpast (by decide),
    ← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
  rfl

/-- Every consecutive padded word range beginning beyond the concrete byte-array end is zero. -/
theorem memoryWordsFrom_past_end_zero (mem : ByteArray) (ptr count : Nat)
    (hpast : mem.size ≤ ptr) :
    memoryWordsFrom mem ptr count = List.replicate count (⟨0⟩ : UInt256) := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      simp only [memoryWordsFrom, List.replicate_succ]
      rw [memoryWordNat_past_end_zero mem ptr hpast]
      have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
      rw [hzero, ih (ptr + 32) (by omega)]

/-- A range whose every concrete word reads as 32 zero bytes is the all-zero limb vector. -/
theorem memoryWordsFrom_eq_replicate_zero_of_reads
    (mem : ByteArray) (ptr count : Nat)
    (hreads : ∀ i, i < count →
      mem.readWithPadding (ptr + 32 * i) 32 = ffi.ByteArray.zeroes 32) :
    memoryWordsFrom mem ptr count = List.replicate count (⟨0⟩ : UInt256) := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      simp only [memoryWordsFrom, List.replicate_succ]
      have hread := hreads 0 (by omega)
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr = 0 := by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [show ptr + 32 * 0 = ptr by omega] at hread
        rw [hread, ← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
        rfl
      rw [hword]
      have hzero : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
      rw [hzero]
      congr 1
      apply ih
      intro i hi
      simpa only [show ptr + 32 + 32 * i = ptr + 32 * (i + 1) by omega] using
        hreads (i + 1) (by omega)

/-- The concrete memory retained by the word-array allocator ends immediately after the length
header; its logical payload is represented by padded zero reads. -/
theorem functionAllocatedMemory_size
    (mem : ByteArray) (fp aCount bCount : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (functionAllocatedMemory mem fp aCount bCount).size = fp + 32 := by
  unfold functionAllocatedMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- The complete result payload of the concrete standalone allocation is initially zero. -/
theorem functionAllocatedMemory_payload_zero
    (mem : ByteArray) (fp aCount bCount : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    memoryWordsFrom (functionAllocatedMemory mem fp aCount bCount) (fp + 32)
        (aCount + bCount) =
      List.replicate (aCount + bCount) (⟨0⟩ : UInt256) := by
  apply memoryWordsFrom_past_end_zero
  rw [functionAllocatedMemory_size mem fp aCount bCount hmemSize hmemLe hgap]

/-! ## Reused allocation semantics -/

/-- A reused standalone result allocation retains the caller's fully materialized scratch size. -/
theorem reusedFunctionAllocatedMemory_size
    (mem : ByteArray) (fp aCount bCount : Nat)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size) :
    (reusedFunctionAllocatedMemory mem fp aCount bCount).size = mem.size := by
  exact reusedWordArrayMemory_size mem fp (aCount + bCount) hmemSize hin

/-- The source-exhausted allocator copy resets every reused result limb to zero. -/
theorem reusedFunctionAllocatedMemory_payload_zero
    (mem : ByteArray) (fp aCount bCount : Nat)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size) :
    memoryWordsFrom (reusedFunctionAllocatedMemory mem fp aCount bCount) (fp + 32)
        (aCount + bCount) =
      List.replicate (aCount + bCount) (⟨0⟩ : UInt256) := by
  apply memoryWordsFrom_eq_replicate_zero_of_reads
  intro i hi
  simpa only [reusedFunctionAllocatedMemory] using
    reusedWordArrayMemory_payload_read mem fp (aCount + bCount) i hmemSize hi hin

/-- A reused result allocation preserves complete operand ranges below its header. -/
theorem reusedFunctionAllocatedMemory_words_below
    (mem : ByteArray) (fp aCount bCount ptr words : Nat)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (htotalPos : 0 < aCount + bCount)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom (reusedFunctionAllocatedMemory mem fp aCount bCount) ptr words =
      memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hhead := reusedWordArrayMemory_read_below mem fp (aCount + bCount) ptr
        hmemSize htotalPos
        hin hptrBase (by omega)
      have htail := ih (ptr + 32) (by omega) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat,
        reusedFunctionAllocatedMemory]
      rw [hhead]
      congr 1

/-- Reused allocation remains covered by solc's exact active-word update. -/
theorem reusedFunctionInitialState_coverage
    (mem : ByteArray) (aw : UInt256) (fp aCount bCount : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64) :
    MemoryCovered (reusedFunctionInitialState mem aw fp aCount bCount).memory
        (reusedFunctionInitialState mem aw fp aCount bCount).activeWords ∧
      (reusedFunctionInitialState mem aw fp aCount bCount).activeWords.toNat * 32 <
        UInt256.size := by
  have hfirst := machineM_coverage mem aw fp 32 hcovered hawFit (by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hmargin : 2 ^ 64 + 31 < UInt256.size := by native_decide
    omega)
  have hsecond := machineM_coverage mem (newBytesStoreWords aw fp) (fp + 32)
    (wordArrayPayloadSize (aCount + bCount))
    (by simpa only [newBytesStoreWords] using hfirst.1)
    (by simpa only [newBytesStoreWords] using hfirst.2) (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      unfold wordArrayPayloadSize
      have hmargin : 2 ^ 64 + 31 < UInt256.size := by native_decide
      omega)
  have hsize := reusedFunctionAllocatedMemory_size mem fp aCount bCount hmemSize hin
  constructor
  · unfold MemoryCovered at hsecond ⊢
    change (reusedFunctionAllocatedMemory mem fp aCount bCount).size ≤
      32 * (newWordArrayWords aw fp (aCount + bCount)).toNat
    rw [hsize]
    simpa only [newWordArrayWords] using hsecond.1
  · simpa only [reusedFunctionInitialState, functionAllocatedWords, newWordArrayWords] using
      hsecond.2

/-- The exact allocator also gives the initial outer loop covered, representable memory. -/
theorem functionInitialState_coverage
    (mem : ByteArray) (aw : UInt256) (fp aCount bCount : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64) :
    MemoryCovered (functionInitialState mem aw fp aCount bCount).memory
        (functionInitialState mem aw fp aCount bCount).activeWords ∧
      (functionInitialState mem aw fp aCount bCount).activeWords.toNat * 32 < UInt256.size := by
  simpa only [functionInitialState, functionAllocatedMemory, functionAllocatedWords] using
    allocatedWordArray_coverage mem aw fp (aCount + bCount) hcovered hawFit hmemSize hmemLe
      hgap hbound

/-- The allocator's 64-bit bound makes the result pointer an exact UInt256 natural. -/
theorem functionResultPtr_toNat
    (fp total : Nat) (hbound : fp + wordArrayAllocationSize total < 2 ^ 64) :
    (UInt256.ofNat fp).toNat = fp := by
  have hfp64 : fp < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  rw [UInt256.toNat_ofNat_of_lt (hfp64.trans (by decide))]

/-- An input-array element address is exact when the complete allocation ends before the result
allocation. -/
theorem inputElementPtr_toNat
    (array index : UInt256) (count fp : Nat)
    (hend : array.toNat + 32 * (count + 1) ≤ fp)
    (hindex : index.toNat < count) (hfp : fp < 2 ^ 64) :
    (elementPtr array index).toNat = array.toNat + 32 * (index.toNat + 1) := by
  apply elementPtr_toNat_of_fit
  have haddress64 : array.toNat + 32 * (index.toNat + 1) < 2 ^ 64 := by omega
  exact haddress64.trans (by decide)

/-- A result-array element address is exact throughout the allocated product payload. -/
theorem functionResultElementPtr_toNat
    (fp total : Nat) (index : UInt256)
    (hbound : fp + wordArrayAllocationSize total < 2 ^ 64)
    (hindex : index.toNat < total) :
    (elementPtr (UInt256.ofNat fp) index).toNat = fp + 32 * (index.toNat + 1) := by
  have hfpWord := functionResultPtr_toNat fp total hbound
  have hfit : (UInt256.ofNat fp).toNat + 32 * (index.toNat + 1) < UInt256.size := by
    rw [hfpWord]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have haddress64 : fp + 32 * (index.toNat + 1) < 2 ^ 64 := by omega
    exact haddress64.trans (by decide)
  rw [elementPtr_toNat_of_fit _ _ hfit, hfpWord]

/-- The concrete outer index after `q` rows is exactly `q`. -/
theorem functionRows_i_toNat
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q : Nat)
    (hsum : aCount + bCount ≤ 68) (hq : q ≤ aCount) :
    (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
      (functionInitialState mem aw fp aCount bCount)).i.toNat = q := by
  have hindex := rowsIterate_i_toNat aPtr bPtr (UInt256.ofNat fp) bCount q
    (functionInitialState mem aw fp aCount bCount) (by
      simp only [functionInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
        Nat.zero_add]
      exact (show q < 2 ^ 64 by omega).trans (by decide))
  simpa only [functionInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.zero_add] using hindex

/-- The concrete inner index after `p` columns from the deployed zero initialization is exactly
`p`. -/
theorem functionInner_j_toNat
    (a bPtr resultPtr i : UInt256) (mem : ByteArray) (aw aPtr : UInt256)
    (bCount p : Nat) (hsum : bCount ≤ 68) (hp : p ≤ bCount) :
    (iterate a bPtr resultPtr i p (initialInnerState mem aw aPtr i)).j.toNat = p := by
  have hindex := iterate_j_toNat a bPtr resultPtr i p (initialInnerState mem aw aPtr i) (by
    simp only [initialInnerState, show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
    exact (show p < 2 ^ 64 by omega).trans (by decide))
  simpa only [initialInnerState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.zero_add] using hindex

/-- The standalone row-address proof depends only on a zero outer index and the array layout; it
therefore applies unchanged to fresh and reused result allocations. -/
theorem rowsFromZero_accessSafe
    (state : OuterState) (aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hstateIndex : state.i = (⟨0⟩ : UInt256))
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    ∀ q, q < aCount →
      RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q state) := by
  intro q hq
  let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q state
  have hfp64 : fp < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hi : outer.i.toNat = q := by
    have hindex := rowsIterate_i_toNat aPtr bPtr (UInt256.ofNat fp) bCount q state (by
      rw [hstateIndex, show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
      exact (show q < 2 ^ 64 by omega).trans (by decide))
    simpa only [outer, hstateIndex, show (⟨0⟩ : UInt256).toNat = 0 by decide,
      Nat.zero_add] using hindex
  have hsourceAddress : (sourcePtr aPtr outer.i).toNat =
      aPtr.toNat + 32 * (q + 1) := by
    unfold sourcePtr
    rw [inputElementPtr_toNat aPtr outer.i aCount fp haEnd (by rw [hi]; exact hq) hfp64,
      hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsourceAddress]
    have hstart64 : aPtr.toNat + 32 * (q + 1) < 2 ^ 64 := by omega
    have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
    omega
  · intro p hp
    let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
    let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
      bPtr (UInt256.ofNat fp) outer.i p initial
    have hj : current.j.toNat = p := by
      have hindex := iterate_j_toNat
        (sourceWord outer.memory outer.activeWords aPtr outer.i) bPtr (UInt256.ofNat fp)
        outer.i p initial (by
          dsimp only [initial, initialInnerState]
          rw [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
          exact (show p < 2 ^ 64 by omega).trans (by decide))
      simpa only [current, initial, initialInnerState,
        show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add] using hindex
    have hisum : (outer.i + current.j).toNat = q + p := by
      rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
      exact (show q + p < 2 ^ 64 by omega).trans (by decide)
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (p + 1) := by
      rw [inputElementPtr_toNat bPtr current.j bCount fp hbEnd (by rw [hj]; exact hp) hfp64,
        hj]
    have hresultAddress : (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
        fp + 32 * (q + p + 1) := by
      rw [functionResultElementPtr_toNat fp (aCount + bCount) (outer.i + current.j)
        hbound (by rw [hisum]; omega), hisum]
    refine ⟨?_, ?_, ?_⟩
    · rw [hbAddress]
      have hstart64 : bPtr.toNat + 32 * (p + 1) < 2 ^ 64 := by omega
      have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
      omega
    · rw [hresultAddress]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      have hstart64 : fp + 32 * (q + p + 1) < 2 ^ 64 := by omega
      have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
      omega
    · apply lt_of_le_of_lt
        (Nat.sub_le (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat
          current.memory.size)
      rw [hresultAddress, show USize.size = 2 ^ 64 by native_decide]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
  · have hbWord : bCount < UInt256.size :=
      (show bCount < 2 ^ 64 by omega).trans (by decide)
    have hisum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
      rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
      exact (show q + bCount < 2 ^ 64 by omega).trans (by decide)
    have hcarryAddress :
        (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat =
          fp + 32 * (q + bCount + 1) := by
      unfold carryPtr
      rw [functionResultElementPtr_toNat fp (aCount + bCount)
        (outer.i + UInt256.ofNat bCount) hbound (by rw [hisum]; omega), hisum]
    rw [hcarryAddress]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hstart64 : fp + 32 * (q + bCount + 1) < 2 ^ 64 := by omega
    have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
    omega
  · let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
    let final := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
      bPtr (UInt256.ofNat fp) outer.i bCount initial
    have hbWord : bCount < UInt256.size :=
      (show bCount < 2 ^ 64 by omega).trans (by decide)
    have hisum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
      rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
      exact (show q + bCount < 2 ^ 64 by omega).trans (by decide)
    have hcarryAddress :
        (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat =
          fp + 32 * (q + bCount + 1) := by
      unfold carryPtr
      rw [functionResultElementPtr_toNat fp (aCount + bCount)
        (outer.i + UInt256.ofNat bCount) hbound (by rw [hisum]; omega), hisum]
    apply lt_of_le_of_lt
      (Nat.sub_le (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat
        final.memory.size)
    rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega

/-- All source, operand, destination, and carry accesses in the allocated standalone product are
representable, and every destination write satisfies the concrete bounded-gap requirement. -/
theorem functionRows_accessSafe
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hsum : aCount + bCount ≤ 68)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    ∀ q, q < aCount →
      RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
          (functionInitialState mem aw fp aCount bCount)) := by
  intro q hq
  let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
    (functionInitialState mem aw fp aCount bCount)
  have hfp64 : fp < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hi : outer.i.toNat = q := by
    have hindex := rowsIterate_i_toNat aPtr bPtr (UInt256.ofNat fp) bCount q
      (functionInitialState mem aw fp aCount bCount) (by
        simp only [functionInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
          Nat.zero_add]
        exact (show q < 2 ^ 64 by omega).trans (by decide))
    simpa only [outer, functionInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
      Nat.zero_add] using hindex
  have hsourceAddress : (sourcePtr aPtr outer.i).toNat =
      aPtr.toNat + 32 * (q + 1) := by
    unfold sourcePtr
    rw [inputElementPtr_toNat aPtr outer.i aCount fp haEnd (by rw [hi]; exact hq) hfp64,
      hi]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsourceAddress]
    have hstart64 : aPtr.toNat + 32 * (q + 1) < 2 ^ 64 := by omega
    have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
    omega
  · intro p hp
    let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
    let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
      bPtr (UInt256.ofNat fp) outer.i p initial
    have hj : current.j.toNat = p := by
      have hindex := iterate_j_toNat
        (sourceWord outer.memory outer.activeWords aPtr outer.i) bPtr (UInt256.ofNat fp)
        outer.i p initial (by
          dsimp only [initial, initialInnerState]
          rw [show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
          exact (show p < 2 ^ 64 by omega).trans (by decide))
      simpa only [current, initial, initialInnerState,
        show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add] using hindex
    have hisum : (outer.i + current.j).toNat = q + p := by
      rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
      exact lt_trans (by omega : q + p < 2 ^ 64) (by decide)
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (p + 1) := by
      rw [inputElementPtr_toNat bPtr current.j bCount fp hbEnd (by rw [hj]; exact hp) hfp64,
        hj]
    have hresultAddress : (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
        fp + 32 * (q + p + 1) := by
      rw [functionResultElementPtr_toNat fp (aCount + bCount) (outer.i + current.j)
        hbound (by rw [hisum]; omega), hisum]
    refine ⟨?_, ?_, ?_⟩
    · rw [hbAddress]
      have hstart64 : bPtr.toNat + 32 * (p + 1) < 2 ^ 64 := by omega
      have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
      omega
    · rw [hresultAddress]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      have hstart64 : fp + 32 * (q + p + 1) < 2 ^ 64 := by omega
      have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
      omega
    · apply lt_of_le_of_lt
        (Nat.sub_le (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat
          current.memory.size)
      rw [hresultAddress, show USize.size = 2 ^ 64 by native_decide]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
  · have hbWord : bCount < UInt256.size :=
      lt_trans (by omega : bCount < 2 ^ 64) (by decide)
    have hisum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
      rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
      exact lt_trans (by omega : q + bCount < 2 ^ 64) (by decide)
    have hcarryAddress :
        (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat =
          fp + 32 * (q + bCount + 1) := by
      unfold carryPtr
      rw [functionResultElementPtr_toNat fp (aCount + bCount)
        (outer.i + UInt256.ofNat bCount) hbound (by rw [hisum]; omega), hisum]
    rw [hcarryAddress]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hstart64 : fp + 32 * (q + bCount + 1) < 2 ^ 64 := by omega
    have hmargin : 2 ^ 64 + 63 < UInt256.size := by native_decide
    omega
  · let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
    let final := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
      bPtr (UInt256.ofNat fp) outer.i bCount initial
    have hbWord : bCount < UInt256.size :=
      lt_trans (by omega : bCount < 2 ^ 64) (by decide)
    have hisum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
      rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
      exact lt_trans (by omega : q + bCount < 2 ^ 64) (by decide)
    have hcarryAddress :
        (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat =
          fp + 32 * (q + bCount + 1) := by
      unfold carryPtr
      rw [functionResultElementPtr_toNat fp (aCount + bCount)
        (outer.i + UInt256.ofNat bCount) hbound (by rw [hisum]; omega), hisum]
    apply lt_of_le_of_lt
      (Nat.sub_le (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat
        final.memory.size)
    rw [hcarryAddress, show USize.size = 2 ^ 64 by native_decide]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega

/-- Generic below-result frame safety for any zero-indexed outer state. -/
theorem rowsFromZero_rowBelowFrameSafe
    (state : OuterState) (aPtr bPtr : UInt256)
    (fp aCount bCount q ptr words : Nat)
    (hstateIndex : state.i = (⟨0⟩ : UInt256))
    (hsum : aCount + bCount ≤ 68)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hq : q < aCount)
    (houterBase : 32 ≤
      (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q state).memory.size)
    (hbelow : ptr + 32 * words ≤ fp) :
    RowBelowFrameSafeGap aPtr bPtr (UInt256.ofNat fp) bCount ptr words
      (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q state) := by
  let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q state
  have hi : outer.i.toNat = q := by
    have hindex := rowsIterate_i_toNat aPtr bPtr (UInt256.ofNat fp) bCount q state (by
      rw [hstateIndex, show (⟨0⟩ : UInt256).toNat = 0 by decide, Nat.zero_add]
      exact (show q < 2 ^ 64 by omega).trans (by decide))
    simpa only [outer, hstateIndex, show (⟨0⟩ : UInt256).toNat = 0 by decide,
      Nat.zero_add] using hindex
  have hsafe : RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount outer := by
    simpa only [outer] using rowsFromZero_accessSafe state aPtr bPtr fp aCount bCount
      hstateIndex hbound haEnd hbEnd q hq
  have hinnerGaps : ∀ p, p < bCount →
      let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
      let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
        bPtr (UInt256.ofNat fp) outer.i p initial
      (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat - current.memory.size <
        USize.size := by
    intro p hp
    exact (hsafe.2.1 p hp).2.2
  change RowBelowFrameSafeGap aPtr bPtr (UInt256.ofNat fp) bCount ptr words outer
  refine ⟨by simpa only [outer] using houterBase, hinnerGaps, ?_, ?_, hsafe.2.2.2, ?_⟩
  · intro p hp
    let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
    let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
      bPtr (UInt256.ofNat fp) outer.i p initial
    have hj : current.j.toNat = p := by
      simpa only [current, initial] using functionInner_j_toNat
        (sourceWord outer.memory outer.activeWords aPtr outer.i) bPtr (UInt256.ofNat fp)
        outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
    have hisum : (outer.i + current.j).toNat = q + p := by
      rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
      exact (show q + p < 2 ^ 64 by omega).trans (by decide)
    have haddress :
        (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
          fp + 32 * (q + p + 1) := by
      rw [functionResultElementPtr_toNat fp (aCount + bCount) (outer.i + current.j)
        hbound (by rw [hisum]; omega), hisum]
    dsimp only
    rw [haddress]
    omega
  · let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
    let final := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
      bPtr (UInt256.ofNat fp) outer.i bCount initial
    have hmono := iterate_memory_size_mono_of_gap
      (sourceWord outer.memory outer.activeWords aPtr outer.i) bPtr (UInt256.ofNat fp)
      outer.i bCount initial hinnerGaps
    have hstart : 32 ≤ initial.memory.size := by
      simpa only [initial, initialInnerState, outer] using houterBase
    exact hstart.trans (by simpa only [final] using hmono)
  · have hbWord : bCount < UInt256.size :=
      (show bCount < 2 ^ 64 by omega).trans (by decide)
    have hisum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
      rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
      exact (show q + bCount < 2 ^ 64 by omega).trans (by decide)
    have haddress :
        (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat =
          fp + 32 * (q + bCount + 1) := by
      unfold carryPtr
      rw [functionResultElementPtr_toNat fp (aCount + bCount)
        (outer.i + UInt256.ofNat bCount) hbound (by rw [hisum]; omega), hisum]
    rw [haddress]
    omega

/-- Every function row preserves any complete input range ending before `fp`; all of the bundled
frame premises follow from the concrete loop indices and allocation ordering. -/
theorem functionRowBelowFrameSafe
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q ptr words : Nat)
    (hsum : aCount + bCount ≤ 68)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hq : q < aCount)
    (houterBase : 32 ≤
      (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
        (functionInitialState mem aw fp aCount bCount)).memory.size)
    (hbelow : ptr + 32 * words ≤ fp) :
    RowBelowFrameSafeGap aPtr bPtr (UInt256.ofNat fp) bCount ptr words
      (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
        (functionInitialState mem aw fp aCount bCount)) := by
  exact rowsFromZero_rowBelowFrameSafe (functionInitialState mem aw fp aCount bCount)
    aPtr bPtr fp aCount bCount q ptr words (by simp only [functionInitialState]) hsum
    hbound haEnd hbEnd hq houterBase hbelow

/-- Every reused standalone multiplication prefix preserves coverage and concrete memory
monotonicity. -/
theorem reusedFunctionRows_coverage
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    MemoryCovered final.memory final.activeWords ∧
      final.activeWords.toNat * 32 < UInt256.size ∧
      initial.memory.size ≤ final.memory.size := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  have hinitial := reusedFunctionInitialState_coverage mem aw fp aCount bCount hcovered
    hawFit hmemSize hin hbound
  have hsafe : ∀ q, q < count →
      RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial) := by
    intro q hq
    exact rowsFromZero_accessSafe initial aPtr bPtr fp aCount bCount (by
      simp only [initial, reusedFunctionInitialState]) hbound haEnd hbEnd q (by omega)
  simpa only [initial] using rowsIterate_coverage_of_gap aPtr bPtr (UInt256.ofNat fp)
    bCount count initial hinitial.1 hinitial.2 hsafe

/-- A reused multiplication preserves any complete word below its result header. -/
theorem reusedFunctionRows_read32_below_result
    (mem : ByteArray) (aw aPtr bPtr : UInt256)
    (fp aCount bCount count read : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hread : read + 32 ≤ mem.size) (hbelow : read + 32 ≤ fp) :
    (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count
      (reusedFunctionInitialState mem aw fp aCount bCount)).memory.readWithPadding read 32 =
        (reusedFunctionInitialState mem aw fp aCount bCount).memory.readWithPadding read 32 := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  have hinitialSize : initial.memory.size = mem.size := by
    simpa only [initial, reusedFunctionInitialState] using
      reusedFunctionAllocatedMemory_size mem fp aCount bCount hmemSize hin
  have hsafe : ∀ q, q < count →
      RowBelowFrameSafeGap aPtr bPtr (UInt256.ofNat fp) bCount read 1
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial) := by
    intro q hq
    have hcoverage := reusedFunctionRows_coverage mem aw aPtr bPtr fp aCount bCount q
      (by omega) hcovered hawFit hmemSize hin hbound haEnd hbEnd
    have houterBase : 32 ≤
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial).memory.size := by
      have hmono : initial.memory.size ≤
          (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial).memory.size := by
        simpa only [initial] using hcoverage.2.2
      rw [hinitialSize] at hmono
      omega
    exact rowsFromZero_rowBelowFrameSafe initial aPtr bPtr fp aCount bCount q read 1
      (by simp only [initial, reusedFunctionInitialState]) hsum hbound haEnd hbEnd
      (by omega) houterBase (by simpa only [Nat.mul_one] using hbelow)
  apply rowsIterate_read32_below_of_gap aPtr bPtr (UInt256.ofNat fp) bCount count read
    initial
  · rw [hinitialSize]
    exact hread
  · exact hsafe

/-- The outer index theorem is independent of whether the result allocation is fresh or reused. -/
theorem reusedFunctionRows_i_toNat
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q : Nat)
    (hsum : aCount + bCount ≤ 68) (hq : q ≤ aCount) :
    (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
      (reusedFunctionInitialState mem aw fp aCount bCount)).i.toNat = q := by
  have hindex := rowsIterate_i_toNat aPtr bPtr (UInt256.ofNat fp) bCount q
    (reusedFunctionInitialState mem aw fp aCount bCount) (by
      simp only [reusedFunctionInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
        Nat.zero_add]
      exact (show q < 2 ^ 64 by omega).trans (by decide))
  simpa only [reusedFunctionInitialState, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.zero_add] using hindex

/-- Both operand payloads remain immutable throughout a reused multiplication prefix. -/
theorem reusedFunctionRows_input_payloads
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount) (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    memoryWordsFrom final.memory (aPtr.toNat + 32) aCount =
        memoryWordsFrom initial.memory (aPtr.toNat + 32) aCount ∧
      memoryWordsFrom final.memory (bPtr.toNat + 32) bCount =
        memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
  have hword (ptr words : Nat) (hbelow : ptr + 32 * words ≤ fp) :
      memoryWordsFrom final.memory ptr words = memoryWordsFrom initial.memory ptr words := by
    induction words generalizing ptr with
    | zero => rfl
    | succ words ih =>
        have hhead := reusedFunctionRows_read32_below_result mem aw aPtr bPtr fp aCount
          bCount count ptr hcount hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
          (by
            unfold wordArrayAllocationSize wordArrayPayloadSize at hin
            omega)
          (by omega)
        have htail := ih (ptr + 32) (by omega)
        simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
        rw [hhead, htail]
  exact ⟨hword (aPtr.toNat + 32) aCount (by omega),
    hword (bPtr.toNat + 32) bCount (by omega)⟩

theorem reusedFunctionRows_memoryWords_below_result
    (mem : ByteArray) (aw aPtr bPtr : UInt256)
    (fp aCount bCount count ptr words : Nat)
    (hcount : count ≤ aCount) (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count
          (reusedFunctionInitialState mem aw fp aCount bCount)).memory ptr words =
      memoryWordsFrom (reusedFunctionInitialState mem aw fp aCount bCount).memory
        ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hhead := reusedFunctionRows_read32_below_result mem aw aPtr bPtr fp aCount
        bCount count ptr hcount hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
        (by
          unfold wordArrayAllocationSize wordArrayPayloadSize at hin
          omega)
        (by omega)
      have htail := ih (ptr + 32) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [hhead, htail]

theorem reusedFunctionRows_accessSafe
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (_hsum : aCount + bCount ≤ 68)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    ∀ q, q < aCount →
      RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q
          (reusedFunctionInitialState mem aw fp aCount bCount)) := by
  exact rowsFromZero_accessSafe (reusedFunctionInitialState mem aw fp aCount bCount)
    aPtr bPtr fp aCount bCount (by simp only [reusedFunctionInitialState])
    hbound haEnd hbEnd

theorem reusedFunctionRows_memory_size_lower_bound
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount) (_hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    fp + 32 ≤
      (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count
        (reusedFunctionInitialState mem aw fp aCount bCount)).memory.size := by
  have hrows := reusedFunctionRows_coverage mem aw aPtr bPtr fp aCount bCount count
    hcount hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have hinitialSize :
      (reusedFunctionInitialState mem aw fp aCount bCount).memory.size = mem.size := by
    simpa only [reusedFunctionInitialState] using
      reusedFunctionAllocatedMemory_size mem fp aCount bCount hmemSize hin
  have hfpMem : fp + 32 ≤ mem.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hin
    omega
  exact hfpMem.trans (by rw [← hinitialSize]; exact hrows.2.2)

theorem reusedFunctionRows_coverageForSemantic
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount) (_hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    MemoryCovered final.memory final.activeWords ∧
      final.activeWords.toNat * 32 < UInt256.size ∧
      initial.memory.size ≤ final.memory.size :=
  reusedFunctionRows_coverage mem aw aPtr bPtr fp aCount bCount count hcount
    hcovered hawFit hmemSize hin hbound haEnd hbEnd

/-- Geometry exported by a complete standalone multiplication over already-materialized scratch
memory.  Unlike the fresh geometry, concrete memory may extend beyond the next free pointer. -/
structure ReusedFunctionFinalGeometry (final : OuterState) (nextFp : Nat) : Prop where
  covered : MemoryCovered final.memory final.activeWords
  activeWordsFit : final.activeWords.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ final.memory.size
  activeWords3 : 3 ≤ final.activeWords.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩
  freePointerRead : final.memory.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat nextFp)

/-- A complete reused schoolbook call establishes the exact allocator geometry required by the
next Solidity allocation. -/
theorem reusedFunctionFinal_geometry
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hsum : aCount + bCount ≤ 68) (htotalPos : 0 < aCount + bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (hfp : 96 ≤ fp)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let final := reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount
    ReusedFunctionFinalGeometry final
      (fp + wordArrayAllocationSize (aCount + bCount)) := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  let final := reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount
  let nextFp := fp + wordArrayAllocationSize (aCount + bCount)
  have hcoverage := reusedFunctionRows_coverage mem aw aPtr bPtr fp aCount bCount aCount
    (by omega) hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have hinitialSize : initial.memory.size = mem.size := by
    simpa only [initial, reusedFunctionInitialState] using
      reusedFunctionAllocatedMemory_size mem fp aCount bCount hmemSize hin
  have hfinalCoverage : MemoryCovered final.memory final.activeWords := by
    simpa only [final, reusedFunctionFinalState, initial] using hcoverage.1
  have hfinalFit : final.activeWords.toNat * 32 < UInt256.size := by
    simpa only [final, reusedFunctionFinalState, initial] using hcoverage.2.1
  have hfinalSize : 96 ≤ final.memory.size := by
    have hmono : initial.memory.size ≤ final.memory.size := by
      simpa only [final, reusedFunctionFinalState, initial] using hcoverage.2.2
    rw [hinitialSize] at hmono
    omega
  have hinitialRead : initial.memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := by
    simpa only [initial, reusedFunctionInitialState, reusedFunctionAllocatedMemory, nextFp] using
      reusedWordArrayMemory_read64 mem fp (aCount + bCount) hmemSize hfp htotalPos hin
  have hframe := reusedFunctionRows_read32_below_result mem aw aPtr bPtr fp aCount bCount
    aCount 64 (by omega) hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
    (by omega) (by omega)
  have hfinalRead : final.memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := by
    have hframe' : final.memory.readWithPadding 64 32 =
        initial.memory.readWithPadding 64 32 := by
      simpa only [final, reusedFunctionFinalState, initial] using hframe
    exact hframe'.trans hinitialRead
  have hfinal3 : 3 ≤ final.activeWords.toNat := by
    unfold MemoryCovered at hfinalCoverage
    omega
  have hfinal64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩ := by
    have hmul : (final.activeWords * (⟨32⟩ : UInt256)).toNat =
        final.activeWords.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := final.activeWords) (b := (⟨32⟩ : UInt256)) hfinalFit
    intro hge
    have hgeNat : (final.activeWords * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa using hge
    rw [hmul] at hgeNat
    omega
  exact {
    covered := hfinalCoverage
    activeWordsFit := hfinalFit
    memorySize96 := hfinalSize
    activeWords3 := hfinal3
    activeWords64 := hfinal64
    freePointerRead := hfinalRead
  }

/-- Every prefix of the standalone outer loop preserves covered, representable memory and grows
the concrete byte array monotonically. -/
theorem functionRows_coverage
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    MemoryCovered final.memory final.activeWords ∧
      final.activeWords.toNat * 32 < UInt256.size ∧
      initial.memory.size ≤ final.memory.size := by
  let initial := functionInitialState mem aw fp aCount bCount
  have hinitial := functionInitialState_coverage mem aw fp aCount bCount hcovered hawFit
    hmemSize hmemLe hgap hbound
  have hsafe : ∀ q, q < count →
      RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial) := by
    intro q hq
    simpa only [initial] using functionRows_accessSafe mem aw aPtr bPtr fp aCount bCount
      hsum hbound haEnd hbEnd q (by omega)
  simpa only [initial] using rowsIterate_coverage_of_gap aPtr bPtr (UInt256.ofNat fp)
    bCount count initial hinitial.1 hinitial.2 hsafe

/-- Every standalone multiplication prefix stays below the logical end of its result allocation,
including prefixes with skipped zero rows and bounded implicit-memory gaps. -/
theorem functionRows_memory_size_upper_bound
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count
      (functionInitialState mem aw fp aCount bCount)).memory.size ≤
        fp + wordArrayAllocationSize (aCount + bCount) := by
  let initial := functionInitialState mem aw fp aCount bCount
  let bound := fp + wordArrayAllocationSize (aCount + bCount)
  have hinitialSize : initial.memory.size = fp + 32 := by
    simpa only [initial, functionInitialState] using
      functionAllocatedMemory_size mem fp aCount bCount hmemSize hmemLe hgap
  have hsafe : ∀ q, q < count →
      RowAccessSafeGap aPtr bPtr (UInt256.ofNat fp) bCount
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial) := by
    intro q hq
    simpa only [initial] using functionRows_accessSafe mem aw aPtr bPtr fp aCount bCount
      hsum hbound haEnd hbEnd q (by omega)
  have hends : ∀ q, q < count →
      let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial
      (∀ p, p < bCount →
        let innerInitial := initialInnerState outer.memory outer.activeWords aPtr outer.i
        let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
          bPtr (UInt256.ofNat fp) outer.i p innerInitial
        (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat + 32 ≤ bound) ∧
      (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat + 32 ≤
        bound := by
    intro q hq
    let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial
    have hi : outer.i.toNat = q := by
      simpa only [outer, initial] using
        functionRows_i_toNat mem aw aPtr bPtr fp aCount bCount q hsum (by omega)
    constructor
    · intro p hp
      let innerInitial := initialInnerState outer.memory outer.activeWords aPtr outer.i
      let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
        bPtr (UInt256.ofNat fp) outer.i p innerInitial
      have hj : current.j.toNat = p := by
        simpa only [current, innerInitial] using functionInner_j_toNat
          (sourceWord outer.memory outer.activeWords aPtr outer.i) bPtr (UInt256.ofNat fp)
          outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
      have hisum : (outer.i + current.j).toNat = q + p := by
        rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
        exact (show q + p < 2 ^ 64 by omega).trans (by decide)
      change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat + 32 ≤ bound
      rw [functionResultElementPtr_toNat fp (aCount + bCount) (outer.i + current.j)
        hbound (by rw [hisum]; omega), hisum]
      dsimp only [bound]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · have hbWord : bCount < UInt256.size :=
        (show bCount < 2 ^ 64 by omega).trans (by decide)
      have hisum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
        rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
        exact (show q + bCount < 2 ^ 64 by omega).trans (by decide)
      change (carryPtr (UInt256.ofNat fp) outer.i (UInt256.ofNat bCount)).toNat + 32 ≤
        bound
      unfold carryPtr
      rw [functionResultElementPtr_toNat fp (aCount + bCount)
        (outer.i + UInt256.ofNat bCount) hbound (by rw [hisum]; omega), hisum]
      dsimp only [bound]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
  apply rowsIterate_memory_size_le_of_gap aPtr bPtr (UInt256.ofNat fp) bCount count
    initial bound
  · rw [hinitialSize]
    dsimp only [bound]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact hsafe
  · exact hends

/-- Every outer-loop prefix retains at least the allocator's concrete header word. -/
theorem functionRows_memory_size_lower_bound
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    fp + 32 ≤
      (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count
        (functionInitialState mem aw fp aCount bCount)).memory.size := by
  have hrows := functionRows_coverage mem aw aPtr bPtr fp aCount bCount count hcount hsum
    hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have hinitialSize : (functionInitialState mem aw fp aCount bCount).memory.size = fp + 32 := by
    simpa only [functionInitialState] using
      functionAllocatedMemory_size mem fp aCount bCount hmemSize hmemLe hgap
  exact (by rw [← hinitialSize]; exact hrows.2.2)

/-- Every outer-loop prefix preserves a complete padded range whose end lies before the result
allocation. -/
theorem functionRows_memoryWords_below_result
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count ptr words : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hbelow : ptr + 32 * words ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    memoryWordsFrom
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial).memory ptr words =
      memoryWordsFrom initial.memory ptr words := by
  let initial := functionInitialState mem aw fp aCount bCount
  have hsafe : ∀ q, q < count →
      RowBelowFrameSafeGap aPtr bPtr (UInt256.ofNat fp) bCount ptr words
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial) := by
    intro q hq
    have houterBase := functionRows_memory_size_lower_bound mem aw aPtr bPtr fp aCount bCount q
      (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
    simpa only [initial] using functionRowBelowFrameSafe mem aw aPtr bPtr fp aCount bCount q
      ptr words hsum hbound haEnd hbEnd (by omega) (by omega) hbelow
  simpa only [initial] using rowsIterate_memoryWords_below_of_gap aPtr bPtr
    (UInt256.ofNat fp) bCount count initial ptr words hsafe

/-- Every standalone multiplication prefix preserves a raw complete 32-byte word below the
result allocation. -/
theorem functionRows_read32_below_result
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count read : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hread : read + 32 ≤ (functionInitialState mem aw fp aCount bCount).memory.size)
    (hbelow : read + 32 ≤ fp) :
    (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count
      (functionInitialState mem aw fp aCount bCount)).memory.readWithPadding read 32 =
        (functionInitialState mem aw fp aCount bCount).memory.readWithPadding read 32 := by
  let initial := functionInitialState mem aw fp aCount bCount
  have hsafe : ∀ q, q < count →
      RowBelowFrameSafeGap aPtr bPtr (UInt256.ofNat fp) bCount read 1
        (rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial) := by
    intro q hq
    have houterBase := functionRows_memory_size_lower_bound mem aw aPtr bPtr fp aCount bCount q
      (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
    simpa only [initial] using functionRowBelowFrameSafe mem aw aPtr bPtr fp aCount bCount q
      read 1 hsum hbound haEnd hbEnd (by omega) (by omega) (by simpa only [Nat.mul_one])
  simpa only [initial] using rowsIterate_read32_below_of_gap aPtr bPtr
    (UInt256.ofNat fp) bCount count read initial (by simpa only [initial] using hread) hsafe

/-- Concrete geometry exported by a complete standalone multiplication for the allocator that
immediately follows it. -/
structure FunctionFinalGeometry (final : OuterState) (nextFp : Nat) : Prop where
  covered : MemoryCovered final.memory final.activeWords
  activeWordsFit : final.activeWords.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ final.memory.size
  memoryLeNext : final.memory.size ≤ nextFp
  nextGap : nextFp - final.memory.size < USize.size
  activeWords3 : 3 ≤ final.activeWords.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩
  freePointerRead : final.memory.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat nextFp)

/-- Allocating a standalone multiplication result preserves every earlier padded limb range
whose end is below the previous free pointer. -/
theorem functionAllocatedMemory_words_below
    (mem : ByteArray) (fp aCount bCount ptr words : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom (functionAllocatedMemory mem fp aCount bCount) ptr words =
      memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hread :
          (functionAllocatedMemory mem fp aCount bCount).readWithPadding ptr 32 =
            mem.readWithPadding ptr 32 := by
        unfold functionAllocatedMemory
        rw [storeBytesLength_read_below_padded]
        · exact setFreePtr_read_above_padded hmemSize hptrBase
        · rw [setFreePtr_size hmemSize]
          omega
        · omega
        · rw [setFreePtr_size hmemSize]
          exact hgap
      have htail := ih (ptr + 32) (by omega) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [hread, htail]

/-- The same frame stated for the concrete initial state consumed by the row semantics. -/
theorem functionInitialState_words_below
    (mem : ByteArray) (aw : UInt256) (fp aCount bCount ptr words : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom (functionInitialState mem aw fp aCount bCount).memory ptr words =
      memoryWordsFrom mem ptr words := by
  simpa only [functionInitialState] using
    functionAllocatedMemory_words_below mem fp aCount bCount ptr words
      hmemSize hgap hptrBase hbelow

/-- A complete standalone multiplication preserves every earlier padded limb range below its
result header, not just its two operand arrays. -/
theorem functionFinalState_words_below
    (mem : ByteArray) (aw aPtr bPtr : UInt256)
    (fp aCount bCount ptr words : Nat)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom (functionFinalState mem aw aPtr bPtr fp aCount bCount).memory
        ptr words = memoryWordsFrom mem ptr words := by
  have hrows := functionRows_memoryWords_below_result mem aw aPtr bPtr fp aCount bCount
    aCount ptr words (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound
    haEnd hbEnd hbelow
  rw [show memoryWordsFrom
      (functionFinalState mem aw aPtr bPtr fp aCount bCount).memory ptr words =
        memoryWordsFrom (functionInitialState mem aw fp aCount bCount).memory ptr words by
    simpa only [functionFinalState] using hrows]
  exact functionInitialState_words_below mem aw fp aCount bCount ptr words
    hmemSize hgap hptrBase hbelow

/-- A complete standalone schoolbook execution establishes every ordinary geometry premise of
the following Solidity allocator, even when zero rows leave part of the payload implicit. -/
theorem functionFinal_geometry
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount aCount
      (functionInitialState mem aw fp aCount bCount)
    FunctionFinalGeometry final (fp + wordArrayAllocationSize (aCount + bCount)) := by
  let initial := functionInitialState mem aw fp aCount bCount
  let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount aCount initial
  let nextFp := fp + wordArrayAllocationSize (aCount + bCount)
  have hcoverage := functionRows_coverage mem aw aPtr bPtr fp aCount bCount aCount
    (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have hlower := functionRows_memory_size_lower_bound mem aw aPtr bPtr fp aCount bCount
    aCount (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have hupper := functionRows_memory_size_upper_bound mem aw aPtr bPtr fp aCount bCount
    aCount (by omega) hsum hmemSize hmemLe hgap hbound haEnd hbEnd
  have hinitialSize : initial.memory.size = fp + 32 := by
    simpa only [initial, functionInitialState] using
      functionAllocatedMemory_size mem fp aCount bCount hmemSize hmemLe hgap
  have hinitialRead : initial.memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := by
    dsimp only [initial, functionInitialState, functionAllocatedMemory, nextFp]
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 hmemSize
    · rw [setFreePtr_size hmemSize]
      exact hmemSize
    · exact hmemSize.trans hmemLe
    · rw [setFreePtr_size hmemSize]
      exact hgap
  have hframe := functionRows_read32_below_result mem aw aPtr bPtr fp aCount bCount
    aCount 64 (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
    (by rw [hinitialSize]; omega) (by omega)
  have hfinalRead : final.memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat nextFp) := hframe.trans hinitialRead
  have hcoverage' : MemoryCovered final.memory final.activeWords ∧
      final.activeWords.toNat * 32 < UInt256.size := by
    simpa only [final, initial] using ⟨hcoverage.1, hcoverage.2.1⟩
  have hlower' : fp + 32 ≤ final.memory.size := by
    simpa only [final, initial] using hlower
  have hupper' : final.memory.size ≤ nextFp := by
    simpa only [final, initial, nextFp] using hupper
  have hfinal3 : 3 ≤ final.activeWords.toNat := by
    unfold MemoryCovered at hcoverage'
    omega
  have hfinal64 : ¬ (⟨64⟩ : UInt256) ≥ final.activeWords * ⟨32⟩ := by
    have hmul : (final.activeWords * (⟨32⟩ : UInt256)).toNat =
        final.activeWords.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := final.activeWords) (b := (⟨32⟩ : UInt256))
          (by simpa only [final] using hcoverage.2.1)
    intro hge
    have hgeNat : (final.activeWords * (⟨32⟩ : UInt256)).toNat ≤ 64 := by simpa using hge
    rw [hmul] at hgeNat
    omega
  have hnextGap : nextFp - final.memory.size < USize.size := by
    have hdiff : nextFp - final.memory.size ≤ 32 * (aCount + bCount) := by
      dsimp only [nextFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    have husize : 32 * (aCount + bCount) < USize.size := by
      have : 32 * 68 < USize.size := by native_decide
      omega
    exact hdiff.trans_lt husize
  exact {
    covered := hcoverage'.1
    activeWordsFit := hcoverage'.2
    memorySize96 := (by omega : 96 ≤ fp + 32).trans hlower'
    memoryLeNext := hupper'
    nextGap := hnextGap
    activeWords3 := hfinal3
    activeWords64 := hfinal64
    freePointerRead := hfinalRead
  }

/-- The complete `a` and `b` payloads are immutable throughout every standalone multiplication
prefix. -/
theorem functionRows_input_payloads
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    memoryWordsFrom final.memory (aPtr.toNat + 32) aCount =
        memoryWordsFrom initial.memory (aPtr.toNat + 32) aCount ∧
      memoryWordsFrom final.memory (bPtr.toNat + 32) bCount =
        memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount := by
  let initial := functionInitialState mem aw fp aCount bCount
  let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
  constructor
  · simpa only [initial, final] using functionRows_memoryWords_below_result mem aw aPtr bPtr
      fp aCount bCount count (aPtr.toNat + 32) aCount hcount hsum hcovered hawFit
      hmemSize hmemLe hgap hbound haEnd hbEnd (by omega)
  · simpa only [initial, final] using functionRows_memoryWords_below_result mem aw aPtr bPtr
      fp aCount bCount count (bPtr.toNat + 32) bCount hcount hsum hcovered hawFit
      hmemSize hmemLe hgap hbound haEnd hbEnd (by omega)

/-- One concrete function row satisfies the pure row relation from the carried zero-tail
invariant, with all collectors and the fresh carry load derived from the evolving EVM memory. -/
theorem functionRow_schoolbookRowUpdate
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q : Nat)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount) (hq : q < aCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (htail :
      let functionInitial := functionInitialState mem aw fp aCount bCount
      let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
      Modexp.SchoolbookZeroTail
        (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
        q (aCount - q)
        (memoryWordsFrom outer.memory (fp + 32) (aCount + bCount))) :
    let functionInitial := functionInitialState mem aw fp aCount bCount
    let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
    Modexp.SchoolbookRowUpdate
      (sourceWord outer.memory outer.activeWords aPtr outer.i)
      (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount) q
      (memoryWordsFrom outer.memory (fp + 32) (aCount + bCount))
      (memoryWordsFrom
        (rowAdvance aPtr bPtr (UInt256.ofNat fp) bCount outer).memory
        (fp + 32) (aCount + bCount)) := by
  let functionInitial := functionInitialState mem aw fp aCount bCount
  let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
  let resultPtr := UInt256.ofNat fp
  let a := sourceWord outer.memory outer.activeWords aPtr outer.i
  let innerInitial := initialInnerState outer.memory outer.activeWords aPtr outer.i
  let innerFinal := iterate a bPtr resultPtr outer.i bCount innerInitial
  let operandWords := memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount
  let base := fp + 32
  let rowPtr := base + 32 * q
  let carryAddress := rowPtr + 32 * bCount
  have hresultPtrNat : resultPtr.toNat = fp := by
    simpa only [resultPtr] using functionResultPtr_toNat fp (aCount + bCount) hbound
  have hi : outer.i.toNat = q := by
    simpa only [outer, functionInitial] using
      functionRows_i_toNat mem aw aPtr bPtr fp aCount bCount q hsum (by omega)
  have hsafe : RowAccessSafeGap aPtr bPtr resultPtr bCount outer := by
    simpa only [outer, functionInitial, resultPtr] using
      functionRows_accessSafe mem aw aPtr bPtr fp aCount bCount hsum hbound haEnd hbEnd q hq
  have houterCoverage := functionRows_coverage mem aw aPtr bPtr fp aCount bCount q
    (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have houterCovered : MemoryCovered outer.memory outer.activeWords := by
    simpa only [outer, functionInitial] using houterCoverage.1
  have houterFit : outer.activeWords.toNat * 32 < UInt256.size := by
    simpa only [outer, functionInitial] using houterCoverage.2.1
  have houterBase : 32 ≤ outer.memory.size := by
    have hsize := functionRows_memory_size_lower_bound mem aw aPtr bPtr fp aCount bCount q
      (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
    have hsize' : fp + 32 ≤ outer.memory.size := by
      simpa only [outer, functionInitial] using hsize
    omega
  have hsourceCoverage := readWords1_coverage outer.memory outer.activeWords
    (sourcePtr aPtr outer.i) houterCovered houterFit hsafe.1
  have hinnerCovered : MemoryCovered innerInitial.memory innerInitial.activeWords := by
    simpa only [innerInitial, initialInnerState, sourceWords, afterLoad] using hsourceCoverage.1
  have hinnerFit : innerInitial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [innerInitial, initialInnerState, sourceWords, afterLoad] using hsourceCoverage.2
  have hinnerGaps : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      (elementPtr resultPtr (outer.i + current.j)).toNat - current.memory.size <
        USize.size := by
    intro p hp
    simpa only [a, resultPtr, innerInitial] using (hsafe.2.1 p hp).2.2
  have hinnerSteps : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (outer.i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (outer.i + current.j)).toNat - current.memory.size <
          USize.size := by
    intro p hp
    simpa only [a, resultPtr, innerInitial] using hsafe.2.1 p hp
  have hinnerCoverage := iterate_coverage_of_gap a bPtr resultPtr outer.i bCount innerInitial
    hinnerCovered hinnerFit hinnerSteps
  have hfinalBase : 32 ≤ innerFinal.memory.size := by
    have hmono := iterate_memory_size_mono_of_gap a bPtr resultPtr outer.i bCount innerInitial
      hinnerGaps
    exact (by
      have hstart : 32 ≤ innerInitial.memory.size := by
        simpa only [innerInitial, initialInnerState] using houterBase
      exact hstart.trans (by simpa only [innerFinal] using hmono))
  have hbFits : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
    intro p hp
    let current := iterate a bPtr resultPtr outer.i p innerInitial
    have hj : current.j.toNat = p := by
      simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
        resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
    dsimp only
    rw [hj]
    have hstart64 : bPtr.toNat + 32 * (p + 3) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    exact hstart64.trans (by decide)
  have hresultFits : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      resultPtr.toNat + 32 * ((outer.i + current.j).toNat + 3) < UInt256.size := by
    intro p hp
    let current := iterate a bPtr resultPtr outer.i p innerInitial
    have hj : current.j.toNat = p := by
      simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
        resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
    have hisum : (outer.i + current.j).toNat = q + p := by
      rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
      exact (show q + p < 2 ^ 64 by omega).trans (by decide)
    have hresultNat : resultPtr.toNat = fp := by
      simpa only [resultPtr] using functionResultPtr_toNat fp (aCount + bCount) hbound
    dsimp only
    rw [hresultNat, hisum]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hstart64 : fp + 32 * (q + p + 3) < 2 ^ 64 := by omega
    exact hstart64.trans (by decide)
  have hbStart : (elementPtr bPtr innerInitial.j).toNat = bPtr.toNat + 32 := by
    have hindex : innerInitial.j.toNat = 0 := by rfl
    rw [inputElementPtr_toNat bPtr innerInitial.j bCount fp hbEnd
      (by rw [hindex]; exact hbPos) (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
        omega), hindex]
  have hrowSum : (outer.i + innerInitial.j).toNat = q := by
    rw [uadd_toNat, hi, show innerInitial.j.toNat = 0 by rfl, Nat.add_zero,
      Nat.mod_eq_of_lt]
    exact (show q < 2 ^ 64 by omega).trans (by decide)
  have hrowPtr : (elementPtr resultPtr (outer.i + innerInitial.j)).toNat = rowPtr := by
    have haddress := functionResultElementPtr_toNat fp (aCount + bCount)
      (outer.i + innerInitial.j) hbound (by rw [hrowSum]; omega)
    change (elementPtr (UInt256.ofNat fp) (outer.i + innerInitial.j)).toNat = rowPtr
    rw [haddress, hrowSum]
    dsimp only [rowPtr, base]
    omega
  have hoperandRange : (elementPtr bPtr innerInitial.j).toNat + 32 * bCount <
      UInt256.size := by
    rw [hbStart]
    have hstart64 : bPtr.toNat + 32 + 32 * bCount < 2 ^ 64 := by omega
    exact hstart64.trans (by decide)
  have hresultRange : (elementPtr resultPtr (outer.i + innerInitial.j)).toNat +
      32 * bCount < UInt256.size := by
    rw [hrowPtr]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hstart64 : rowPtr + 32 * bCount < 2 ^ 64 := by
      dsimp only [rowPtr, base]
      omega
    exact hstart64.trans (by decide)
  have hseparate : (elementPtr bPtr innerInitial.j).toNat + 32 * bCount ≤
      (elementPtr resultPtr (outer.i + innerInitial.j)).toNat := by
    rw [hbStart, hrowPtr]
    dsimp only [rowPtr, base]
    omega
  have hinput := innerInputWords_eq_initialMemory_of_gap a bPtr resultPtr outer.i bCount
    innerInitial hinnerCovered hinnerFit
    (by simpa only [innerInitial, initialInnerState] using houterBase)
    hbFits hresultFits hinnerGaps hoperandRange hresultRange hseparate
  have hinputFrames := functionRows_input_payloads mem aw aPtr bPtr fp aCount bCount q
    (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have hoperand : innerOperandWords a bPtr resultPtr outer.i bCount innerInitial =
      operandWords := by
    calc
      innerOperandWords a bPtr resultPtr outer.i bCount innerInitial =
          memoryWordsFrom innerInitial.memory
            (elementPtr bPtr innerInitial.j).toNat bCount := hinput.1
      _ = memoryWordsFrom outer.memory (bPtr.toNat + 32) bCount := by
        rw [hbStart]
        rfl
      _ = memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount := by
        simpa only [outer, functionInitial] using hinputFrames.2
      _ = operandWords := rfl
  have hprior : innerPriorWords a bPtr resultPtr outer.i bCount innerInitial =
      memoryWordsFrom outer.memory rowPtr bCount := by
    calc
      innerPriorWords a bPtr resultPtr outer.i bCount innerInitial =
          memoryWordsFrom innerInitial.memory
            (elementPtr resultPtr (outer.i + innerInitial.j)).toNat bCount := hinput.2
      _ = memoryWordsFrom outer.memory rowPtr bCount := by
        rw [hrowPtr]
        rfl
  have houtput := innerOutputWords_eq_finalMemory_of_gap a bPtr resultPtr outer.i bCount
    innerInitial (by
      intro p hp
      have h := hbFits p hp
      omega) (by
      intro p hp
      have h := hresultFits p hp
      omega) hresultRange hinnerGaps
  have houtput' : innerOutputWords a bPtr resultPtr outer.i bCount innerInitial =
      memoryWordsFrom innerFinal.memory rowPtr bCount := by
    simpa only [innerFinal, hrowPtr] using houtput
  have hbWord : bCount < UInt256.size :=
    (show bCount < 2 ^ 64 by omega).trans (by decide)
  have hcarrySum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
    rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
    exact (show q + bCount < 2 ^ 64 by omega).trans (by decide)
  have hcarryAddress : (carryPtr resultPtr outer.i (UInt256.ofNat bCount)).toNat =
      carryAddress := by
    unfold carryPtr
    have haddress := functionResultElementPtr_toNat fp (aCount + bCount)
      (outer.i + UInt256.ofNat bCount) hbound (by rw [hcarrySum]; omega)
    change (elementPtr (UInt256.ofNat fp) (outer.i + UInt256.ofNat bCount)).toNat =
      carryAddress
    rw [haddress, hcarrySum]
    dsimp only [carryAddress, rowPtr, base]
    omega
  have htopFrame := iterate_memoryWords_above_of_gap a bPtr resultPtr outer.i bCount
    innerInitial carryAddress 1 hinnerGaps (by
      intro p hp
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      have hj : current.j.toNat = p := by
        simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
          resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
      have hisum : (outer.i + current.j).toNat = q + p := by
        rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
        exact (show q + p < 2 ^ 64 by omega).trans (by decide)
      have haddress : (elementPtr resultPtr (outer.i + current.j)).toNat =
          fp + 32 * (q + p + 1) := by
        change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
          fp + 32 * (q + p + 1)
        rw [functionResultElementPtr_toNat fp (aCount + bCount)
          (outer.i + current.j) hbound (by rw [hisum]; omega), hisum]
      dsimp only
      rw [haddress]
      dsimp only [carryAddress, rowPtr, base]
      omega)
  have hfresh := Modexp.schoolbookZeroTail_fresh_decomposition
    (by simpa only [functionInitial, outer, operandWords, base] using htail)
    (by omega : 0 < aCount - q)
  rcases hfresh with ⟨pre, segment, suffix, hpre, hsegment, hbefore⟩
  have hsuffixLength : suffix.length = aCount - q - 1 := by
    have hlength := congrArg List.length hbefore
    rw [memoryWordsFrom_length] at hlength
    simp only [List.length_append, List.length_cons, hpre, hsegment,
      memoryWordsFrom_length] at hlength
    omega
  have htopZero : Modexp.MultiLimbMemoryModel.memoryWordNat outer.memory carryAddress = 0 := by
    have hraw := memoryWordNat_of_words_zero outer.memory base (q + bCount)
      (pre ++ segment) suffix
      (by simp only [List.length_append, hpre, hsegment, operandWords,
        memoryWordsFrom_length])
      (by
        rw [show q + bCount + 1 + suffix.length = aCount + bCount by omega]
        simpa only [base] using hbefore)
    rw [show carryAddress = base + 32 * (q + bCount) by
      dsimp only [carryAddress, rowPtr]
      omega]
    exact hraw
  have hfinalTopZero : Modexp.MultiLimbMemoryModel.memoryWordNat innerFinal.memory carryAddress =
      0 := by
    have hwordFrame := memoryWordNat_eq_of_memoryWordsFrom_one_eq innerFinal.memory
      outer.memory carryAddress htopFrame
    rw [hwordFrame, htopZero]
  have hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord innerFinal.memory
      innerFinal.activeWords (carryPtr resultPtr outer.i (UInt256.ofNat bCount)) = ⟨0⟩ := by
    have hread := readWord_eq_memoryWordOf_covered_padded innerFinal.memory
      innerFinal.activeWords (carryPtr resultPtr outer.i (UInt256.ofNat bCount))
      (by simpa only [innerFinal] using hinnerCoverage.1)
      (by simpa only [innerFinal] using hinnerCoverage.2.1)
    rw [hcarryAddress, hfinalTopZero] at hread
    simpa using hread
  have hcarryGap : (carryPtr resultPtr outer.i (UInt256.ofNat bCount)).toNat -
      innerFinal.memory.size < USize.size := by
    simpa only [resultPtr, a, innerInitial, innerFinal] using hsafe.2.2.2
  by_cases hzero : sourceWord outer.memory outer.activeWords aPtr outer.i = ⟨0⟩
  · have hbefore' : memoryWordsFrom outer.memory (resultPtr.toNat + 32)
        (aCount + bCount) = pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix := by
      rw [hresultPtrNat]
      simpa only [base] using hbefore
    have hupdate := rowAdvance_zero_schoolbookRowUpdate aPtr bPtr resultPtr bCount q
      (aCount + bCount) outer operandWords pre segment suffix hzero hpre hsegment hbefore'
    simpa only [functionInitial, outer, resultPtr, operandWords, base,
      functionResultPtr_toNat fp (aCount + bCount) hbound] using hupdate
  · have hupdate := rowAdvance_nonzero_schoolbookRowUpdate aPtr bPtr resultPtr bCount q
      suffix.length outer operandWords hzero houterBase (by simp [operandWords])
      (by simpa only [innerInitial, initialInnerState, u256_zero_add, rowPtr, base,
        hresultPtrNat]
        using hrowPtr)
      (by simpa only [carryAddress, rowPtr, base, Nat.add_assoc, hresultPtrNat]
        using hcarryAddress)
      (by simpa only [carryAddress, rowPtr, base, hresultPtrNat, Nat.add_assoc]
        using htopZero)
      (by simpa only [a, innerInitial, operandWords, resultPtr] using hoperand)
      (by simpa only [a, innerInitial, resultPtr, rowPtr, base, hresultPtrNat] using hprior)
      (by simpa only [a, innerInitial, innerFinal, resultPtr, rowPtr, base,
        hresultPtrNat] using houtput')
      (by simpa only [a, innerInitial, innerFinal, resultPtr] using hcarryReadZero)
      (by simpa only [a, innerInitial, innerFinal, resultPtr] using hfinalBase)
      (by simpa only [a, innerInitial, innerFinal, resultPtr] using hcarryGap)
      (by simpa only [a, innerInitial, resultPtr] using hinnerGaps)
      (by
        intro p hp
        let current := iterate a bPtr resultPtr outer.i p innerInitial
        have hj : current.j.toNat = p := by
          simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
            resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
        have hisum : (outer.i + current.j).toNat = q + p := by
          rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
          exact (show q + p < 2 ^ 64 by omega).trans (by decide)
        have haddress : (elementPtr resultPtr (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1) := by
          change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1)
          rw [functionResultElementPtr_toNat fp (aCount + bCount)
            (outer.i + current.j) hbound (by rw [hisum]; omega), hisum]
        dsimp only
        rw [hresultPtrNat, haddress]
        omega)
      (by
        intro p hp
        let current := iterate a bPtr resultPtr outer.i p innerInitial
        have hj : current.j.toNat = p := by
          simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
            resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
        have hisum : (outer.i + current.j).toNat = q + p := by
          rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
          exact (show q + p < 2 ^ 64 by omega).trans (by decide)
        have haddress : (elementPtr resultPtr (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1) := by
          change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1)
          rw [functionResultElementPtr_toNat fp (aCount + bCount)
            (outer.i + current.j) hbound (by rw [hisum]; omega), hisum]
        dsimp only
        rw [hresultPtrNat, haddress]
        omega)
    rw [hsuffixLength, show q + bCount + 1 + (aCount - q - 1) = aCount + bCount by
      omega] at hupdate
    simpa only [functionInitial, outer, resultPtr, operandWords, base,
      functionResultPtr_toNat fp (aCount + bCount) hbound] using hupdate

/-- One reused-allocation row satisfies the same pure schoolbook update relation. -/
theorem reusedFunctionRow_schoolbookRowUpdate
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q : Nat)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount) (hq : q < aCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp)
    (htail :
      let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
      let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
      Modexp.SchoolbookZeroTail
        (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
        q (aCount - q)
        (memoryWordsFrom outer.memory (fp + 32) (aCount + bCount))) :
    let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
    let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
    Modexp.SchoolbookRowUpdate
      (sourceWord outer.memory outer.activeWords aPtr outer.i)
      (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount) q
      (memoryWordsFrom outer.memory (fp + 32) (aCount + bCount))
      (memoryWordsFrom
        (rowAdvance aPtr bPtr (UInt256.ofNat fp) bCount outer).memory
        (fp + 32) (aCount + bCount)) := by
  let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
  let outer := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
  let resultPtr := UInt256.ofNat fp
  let a := sourceWord outer.memory outer.activeWords aPtr outer.i
  let innerInitial := initialInnerState outer.memory outer.activeWords aPtr outer.i
  let innerFinal := iterate a bPtr resultPtr outer.i bCount innerInitial
  let operandWords := memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount
  let base := fp + 32
  let rowPtr := base + 32 * q
  let carryAddress := rowPtr + 32 * bCount
  have hresultPtrNat : resultPtr.toNat = fp := by
    simpa only [resultPtr] using functionResultPtr_toNat fp (aCount + bCount) hbound
  have hi : outer.i.toNat = q := by
    simpa only [outer, functionInitial] using
      reusedFunctionRows_i_toNat mem aw aPtr bPtr fp aCount bCount q hsum (by omega)
  have hsafe : RowAccessSafeGap aPtr bPtr resultPtr bCount outer := by
    simpa only [outer, functionInitial, resultPtr] using
      reusedFunctionRows_accessSafe mem aw aPtr bPtr fp aCount bCount hsum hbound haEnd hbEnd q hq
  have houterCoverage := reusedFunctionRows_coverageForSemantic mem aw aPtr bPtr fp aCount bCount q
    (by omega) hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have houterCovered : MemoryCovered outer.memory outer.activeWords := by
    simpa only [outer, functionInitial] using houterCoverage.1
  have houterFit : outer.activeWords.toNat * 32 < UInt256.size := by
    simpa only [outer, functionInitial] using houterCoverage.2.1
  have houterBase : 32 ≤ outer.memory.size := by
    have hsize := reusedFunctionRows_memory_size_lower_bound mem aw aPtr bPtr fp aCount bCount q
      (by omega) hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
    have hsize' : fp + 32 ≤ outer.memory.size := by
      simpa only [outer, functionInitial] using hsize
    omega
  have hsourceCoverage := readWords1_coverage outer.memory outer.activeWords
    (sourcePtr aPtr outer.i) houterCovered houterFit hsafe.1
  have hinnerCovered : MemoryCovered innerInitial.memory innerInitial.activeWords := by
    simpa only [innerInitial, initialInnerState, sourceWords, afterLoad] using hsourceCoverage.1
  have hinnerFit : innerInitial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [innerInitial, initialInnerState, sourceWords, afterLoad] using hsourceCoverage.2
  have hinnerGaps : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      (elementPtr resultPtr (outer.i + current.j)).toNat - current.memory.size <
        USize.size := by
    intro p hp
    simpa only [a, resultPtr, innerInitial] using (hsafe.2.1 p hp).2.2
  have hinnerSteps : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (outer.i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (outer.i + current.j)).toNat - current.memory.size <
          USize.size := by
    intro p hp
    simpa only [a, resultPtr, innerInitial] using hsafe.2.1 p hp
  have hinnerCoverage := iterate_coverage_of_gap a bPtr resultPtr outer.i bCount innerInitial
    hinnerCovered hinnerFit hinnerSteps
  have hfinalBase : 32 ≤ innerFinal.memory.size := by
    have hmono := iterate_memory_size_mono_of_gap a bPtr resultPtr outer.i bCount innerInitial
      hinnerGaps
    exact (by
      have hstart : 32 ≤ innerInitial.memory.size := by
        simpa only [innerInitial, initialInnerState] using houterBase
      exact hstart.trans (by simpa only [innerFinal] using hmono))
  have hbFits : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
    intro p hp
    let current := iterate a bPtr resultPtr outer.i p innerInitial
    have hj : current.j.toNat = p := by
      simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
        resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
    dsimp only
    rw [hj]
    have hstart64 : bPtr.toNat + 32 * (p + 3) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    exact hstart64.trans (by decide)
  have hresultFits : ∀ p, p < bCount →
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      resultPtr.toNat + 32 * ((outer.i + current.j).toNat + 3) < UInt256.size := by
    intro p hp
    let current := iterate a bPtr resultPtr outer.i p innerInitial
    have hj : current.j.toNat = p := by
      simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
        resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
    have hisum : (outer.i + current.j).toNat = q + p := by
      rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
      exact (show q + p < 2 ^ 64 by omega).trans (by decide)
    have hresultNat : resultPtr.toNat = fp := by
      simpa only [resultPtr] using functionResultPtr_toNat fp (aCount + bCount) hbound
    dsimp only
    rw [hresultNat, hisum]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hstart64 : fp + 32 * (q + p + 3) < 2 ^ 64 := by omega
    exact hstart64.trans (by decide)
  have hbStart : (elementPtr bPtr innerInitial.j).toNat = bPtr.toNat + 32 := by
    have hindex : innerInitial.j.toNat = 0 := by rfl
    rw [inputElementPtr_toNat bPtr innerInitial.j bCount fp hbEnd
      (by rw [hindex]; exact hbPos) (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
        omega), hindex]
  have hrowSum : (outer.i + innerInitial.j).toNat = q := by
    rw [uadd_toNat, hi, show innerInitial.j.toNat = 0 by rfl, Nat.add_zero,
      Nat.mod_eq_of_lt]
    exact (show q < 2 ^ 64 by omega).trans (by decide)
  have hrowPtr : (elementPtr resultPtr (outer.i + innerInitial.j)).toNat = rowPtr := by
    have haddress := functionResultElementPtr_toNat fp (aCount + bCount)
      (outer.i + innerInitial.j) hbound (by rw [hrowSum]; omega)
    change (elementPtr (UInt256.ofNat fp) (outer.i + innerInitial.j)).toNat = rowPtr
    rw [haddress, hrowSum]
    dsimp only [rowPtr, base]
    omega
  have hoperandRange : (elementPtr bPtr innerInitial.j).toNat + 32 * bCount <
      UInt256.size := by
    rw [hbStart]
    have hstart64 : bPtr.toNat + 32 + 32 * bCount < 2 ^ 64 := by omega
    exact hstart64.trans (by decide)
  have hresultRange : (elementPtr resultPtr (outer.i + innerInitial.j)).toNat +
      32 * bCount < UInt256.size := by
    rw [hrowPtr]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    have hstart64 : rowPtr + 32 * bCount < 2 ^ 64 := by
      dsimp only [rowPtr, base]
      omega
    exact hstart64.trans (by decide)
  have hseparate : (elementPtr bPtr innerInitial.j).toNat + 32 * bCount ≤
      (elementPtr resultPtr (outer.i + innerInitial.j)).toNat := by
    rw [hbStart, hrowPtr]
    dsimp only [rowPtr, base]
    omega
  have hinput := innerInputWords_eq_initialMemory_of_gap a bPtr resultPtr outer.i bCount
    innerInitial hinnerCovered hinnerFit
    (by simpa only [innerInitial, initialInnerState] using houterBase)
    hbFits hresultFits hinnerGaps hoperandRange hresultRange hseparate
  have hinputFrames := reusedFunctionRows_input_payloads mem aw aPtr bPtr fp aCount bCount q
    (by omega) hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have hoperand : innerOperandWords a bPtr resultPtr outer.i bCount innerInitial =
      operandWords := by
    calc
      innerOperandWords a bPtr resultPtr outer.i bCount innerInitial =
          memoryWordsFrom innerInitial.memory
            (elementPtr bPtr innerInitial.j).toNat bCount := hinput.1
      _ = memoryWordsFrom outer.memory (bPtr.toNat + 32) bCount := by
        rw [hbStart]
        rfl
      _ = memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount := by
        simpa only [outer, functionInitial] using hinputFrames.2
      _ = operandWords := rfl
  have hprior : innerPriorWords a bPtr resultPtr outer.i bCount innerInitial =
      memoryWordsFrom outer.memory rowPtr bCount := by
    calc
      innerPriorWords a bPtr resultPtr outer.i bCount innerInitial =
          memoryWordsFrom innerInitial.memory
            (elementPtr resultPtr (outer.i + innerInitial.j)).toNat bCount := hinput.2
      _ = memoryWordsFrom outer.memory rowPtr bCount := by
        rw [hrowPtr]
        rfl
  have houtput := innerOutputWords_eq_finalMemory_of_gap a bPtr resultPtr outer.i bCount
    innerInitial (by
      intro p hp
      have h := hbFits p hp
      omega) (by
      intro p hp
      have h := hresultFits p hp
      omega) hresultRange hinnerGaps
  have houtput' : innerOutputWords a bPtr resultPtr outer.i bCount innerInitial =
      memoryWordsFrom innerFinal.memory rowPtr bCount := by
    simpa only [innerFinal, hrowPtr] using houtput
  have hbWord : bCount < UInt256.size :=
    (show bCount < 2 ^ 64 by omega).trans (by decide)
  have hcarrySum : (outer.i + UInt256.ofNat bCount).toNat = q + bCount := by
    rw [uadd_toNat, hi, UInt256.toNat_ofNat_of_lt hbWord, Nat.mod_eq_of_lt]
    exact (show q + bCount < 2 ^ 64 by omega).trans (by decide)
  have hcarryAddress : (carryPtr resultPtr outer.i (UInt256.ofNat bCount)).toNat =
      carryAddress := by
    unfold carryPtr
    have haddress := functionResultElementPtr_toNat fp (aCount + bCount)
      (outer.i + UInt256.ofNat bCount) hbound (by rw [hcarrySum]; omega)
    change (elementPtr (UInt256.ofNat fp) (outer.i + UInt256.ofNat bCount)).toNat =
      carryAddress
    rw [haddress, hcarrySum]
    dsimp only [carryAddress, rowPtr, base]
    omega
  have htopFrame := iterate_memoryWords_above_of_gap a bPtr resultPtr outer.i bCount
    innerInitial carryAddress 1 hinnerGaps (by
      intro p hp
      let current := iterate a bPtr resultPtr outer.i p innerInitial
      have hj : current.j.toNat = p := by
        simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
          resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
      have hisum : (outer.i + current.j).toNat = q + p := by
        rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
        exact (show q + p < 2 ^ 64 by omega).trans (by decide)
      have haddress : (elementPtr resultPtr (outer.i + current.j)).toNat =
          fp + 32 * (q + p + 1) := by
        change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
          fp + 32 * (q + p + 1)
        rw [functionResultElementPtr_toNat fp (aCount + bCount)
          (outer.i + current.j) hbound (by rw [hisum]; omega), hisum]
      dsimp only
      rw [haddress]
      dsimp only [carryAddress, rowPtr, base]
      omega)
  have hfresh := Modexp.schoolbookZeroTail_fresh_decomposition
    (by simpa only [functionInitial, outer, operandWords, base] using htail)
    (by omega : 0 < aCount - q)
  rcases hfresh with ⟨pre, segment, suffix, hpre, hsegment, hbefore⟩
  have hsuffixLength : suffix.length = aCount - q - 1 := by
    have hlength := congrArg List.length hbefore
    rw [memoryWordsFrom_length] at hlength
    simp only [List.length_append, List.length_cons, hpre, hsegment,
      memoryWordsFrom_length] at hlength
    omega
  have htopZero : Modexp.MultiLimbMemoryModel.memoryWordNat outer.memory carryAddress = 0 := by
    have hraw := memoryWordNat_of_words_zero outer.memory base (q + bCount)
      (pre ++ segment) suffix
      (by simp only [List.length_append, hpre, hsegment, operandWords,
        memoryWordsFrom_length])
      (by
        rw [show q + bCount + 1 + suffix.length = aCount + bCount by omega]
        simpa only [base] using hbefore)
    rw [show carryAddress = base + 32 * (q + bCount) by
      dsimp only [carryAddress, rowPtr]
      omega]
    exact hraw
  have hfinalTopZero : Modexp.MultiLimbMemoryModel.memoryWordNat innerFinal.memory carryAddress =
      0 := by
    have hwordFrame := memoryWordNat_eq_of_memoryWordsFrom_one_eq innerFinal.memory
      outer.memory carryAddress htopFrame
    rw [hwordFrame, htopZero]
  have hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord innerFinal.memory
      innerFinal.activeWords (carryPtr resultPtr outer.i (UInt256.ofNat bCount)) = ⟨0⟩ := by
    have hread := readWord_eq_memoryWordOf_covered_padded innerFinal.memory
      innerFinal.activeWords (carryPtr resultPtr outer.i (UInt256.ofNat bCount))
      (by simpa only [innerFinal] using hinnerCoverage.1)
      (by simpa only [innerFinal] using hinnerCoverage.2.1)
    rw [hcarryAddress, hfinalTopZero] at hread
    simpa using hread
  have hcarryGap : (carryPtr resultPtr outer.i (UInt256.ofNat bCount)).toNat -
      innerFinal.memory.size < USize.size := by
    simpa only [resultPtr, a, innerInitial, innerFinal] using hsafe.2.2.2
  by_cases hzero : sourceWord outer.memory outer.activeWords aPtr outer.i = ⟨0⟩
  · have hbefore' : memoryWordsFrom outer.memory (resultPtr.toNat + 32)
        (aCount + bCount) = pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix := by
      rw [hresultPtrNat]
      simpa only [base] using hbefore
    have hupdate := rowAdvance_zero_schoolbookRowUpdate aPtr bPtr resultPtr bCount q
      (aCount + bCount) outer operandWords pre segment suffix hzero hpre hsegment hbefore'
    simpa only [functionInitial, outer, resultPtr, operandWords, base,
      functionResultPtr_toNat fp (aCount + bCount) hbound] using hupdate
  · have hupdate := rowAdvance_nonzero_schoolbookRowUpdate aPtr bPtr resultPtr bCount q
      suffix.length outer operandWords hzero houterBase (by simp [operandWords])
      (by simpa only [innerInitial, initialInnerState, u256_zero_add, rowPtr, base,
        hresultPtrNat]
        using hrowPtr)
      (by simpa only [carryAddress, rowPtr, base, Nat.add_assoc, hresultPtrNat]
        using hcarryAddress)
      (by simpa only [carryAddress, rowPtr, base, hresultPtrNat, Nat.add_assoc]
        using htopZero)
      (by simpa only [a, innerInitial, operandWords, resultPtr] using hoperand)
      (by simpa only [a, innerInitial, resultPtr, rowPtr, base, hresultPtrNat] using hprior)
      (by simpa only [a, innerInitial, innerFinal, resultPtr, rowPtr, base,
        hresultPtrNat] using houtput')
      (by simpa only [a, innerInitial, innerFinal, resultPtr] using hcarryReadZero)
      (by simpa only [a, innerInitial, innerFinal, resultPtr] using hfinalBase)
      (by simpa only [a, innerInitial, innerFinal, resultPtr] using hcarryGap)
      (by simpa only [a, innerInitial, resultPtr] using hinnerGaps)
      (by
        intro p hp
        let current := iterate a bPtr resultPtr outer.i p innerInitial
        have hj : current.j.toNat = p := by
          simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
            resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
        have hisum : (outer.i + current.j).toNat = q + p := by
          rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
          exact (show q + p < 2 ^ 64 by omega).trans (by decide)
        have haddress : (elementPtr resultPtr (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1) := by
          change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1)
          rw [functionResultElementPtr_toNat fp (aCount + bCount)
            (outer.i + current.j) hbound (by rw [hisum]; omega), hisum]
        dsimp only
        rw [hresultPtrNat, haddress]
        omega)
      (by
        intro p hp
        let current := iterate a bPtr resultPtr outer.i p innerInitial
        have hj : current.j.toNat = p := by
          simpa only [current, a, resultPtr, innerInitial] using functionInner_j_toNat a bPtr
            resultPtr outer.i outer.memory outer.activeWords aPtr bCount p (by omega) (by omega)
        have hisum : (outer.i + current.j).toNat = q + p := by
          rw [uadd_toNat, hi, hj, Nat.mod_eq_of_lt]
          exact (show q + p < 2 ^ 64 by omega).trans (by decide)
        have haddress : (elementPtr resultPtr (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1) := by
          change (elementPtr (UInt256.ofNat fp) (outer.i + current.j)).toNat =
            fp + 32 * (q + p + 1)
          rw [functionResultElementPtr_toNat fp (aCount + bCount)
            (outer.i + current.j) hbound (by rw [hisum]; omega), hisum]
        dsimp only
        rw [hresultPtrNat, haddress]
        omega)
    rw [hsuffixLength, show q + bCount + 1 + (aCount - q - 1) = aCount + bCount by
      omega] at hupdate
    simpa only [functionInitial, outer, resultPtr, operandWords, base,
      functionResultPtr_toNat fp (aCount + bCount) hbound] using hupdate



/-- After any concrete outer-loop prefix, exactly the unprocessed carry slots remain zero. -/
theorem functionRows_zeroTail
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let functionInitial := functionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count functionInitial
    Modexp.SchoolbookZeroTail
      (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
      count (aCount - count)
      (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) := by
  induction count with
  | zero =>
      let functionInitial := functionInitialState mem aw fp aCount bCount
      have hpayload := functionAllocatedMemory_payload_zero mem fp aCount bCount
        hmemSize hmemLe hgap
      have hzero : memoryWordsFrom functionInitial.memory (fp + 32) (aCount + bCount) =
          List.replicate (aCount + bCount) (⟨0⟩ : UInt256) := by
        simpa only [functionInitial, functionInitialState] using hpayload
      have hinitial := Modexp.schoolbookZeroTail_initial
        (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
        aCount (aCount + bCount) (by rw [memoryWordsFrom_length]; omega)
      simpa only [functionInitial, rowsIterate, Nat.zero_sub, hzero] using hinitial
  | succ count ih =>
      let functionInitial := functionInitialState mem aw fp aCount bCount
      let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count functionInitial
      have hprev : count ≤ aCount := by omega
      have hstrict : count < aCount := by omega
      have htail := ih hprev
      have hupdate := functionRow_schoolbookRowUpdate mem aw aPtr bPtr fp aCount bCount count
        hsum hbPos hstrict hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
        (by simpa only [functionInitial, current] using htail)
      have htailForStep : Modexp.SchoolbookZeroTail
          (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
          count ((aCount - (count + 1)) + 1)
          (memoryWordsFrom current.memory (fp + 32) (aCount + bCount)) := by
        simpa only [functionInitial, current, show aCount - count =
          (aCount - (count + 1)) + 1 by omega] using htail
      have hnext := Modexp.schoolbookRowUpdate_zeroTail hupdate htailForStep
      simpa only [functionInitial, current, rowsIterate_succ_last] using hnext

/-- Every row in the concrete function execution satisfies the pure schoolbook row relation. -/
theorem functionRows_schoolbookRowUpdates
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let functionInitial := functionInitialState mem aw fp aCount bCount
    ∀ q, q < count →
      let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
      Modexp.SchoolbookRowUpdate
        (sourceWord current.memory current.activeWords aPtr current.i)
        (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount) q
        (memoryWordsFrom current.memory (fp + 32) (aCount + bCount))
        (memoryWordsFrom
          (rowAdvance aPtr bPtr (UInt256.ofNat fp) bCount current).memory
          (fp + 32) (aCount + bCount)) := by
  dsimp only
  intro q hq
  have htail := functionRows_zeroTail mem aw aPtr bPtr fp aCount bCount q (by omega)
    hsum hbPos hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  exact functionRow_schoolbookRowUpdate mem aw aPtr bPtr fp aCount bCount q hsum hbPos
    (by omega) hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd htail

/-- The source load for row `q` is exactly limb `q` of the immutable input `a` payload. -/
theorem functionRow_sourceWord
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q : Nat)
    (hq : q < aCount) (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial
    sourceWord current.memory current.activeWords aPtr current.i =
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat initial.memory
        (aPtr.toNat + 32 + 32 * q)) := by
  let initial := functionInitialState mem aw fp aCount bCount
  let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial
  have hi : current.i.toNat = q := by
    simpa only [current, initial] using
      functionRows_i_toNat mem aw aPtr bPtr fp aCount bCount q hsum (by omega)
  have hfp64 : fp < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have haddress : (sourcePtr aPtr current.i).toNat = aPtr.toNat + 32 + 32 * q := by
    unfold sourcePtr
    rw [inputElementPtr_toNat aPtr current.i aCount fp haEnd (by rw [hi]; exact hq) hfp64,
      hi]
    omega
  have hcurrentCoverage := functionRows_coverage mem aw aPtr bPtr fp aCount bCount q
    (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have hframe := functionRows_memoryWords_below_result mem aw aPtr bPtr fp aCount bCount q
    (aPtr.toNat + 32 + 32 * q) 1 (by omega) hsum hcovered hawFit hmemSize hmemLe hgap
    hbound haEnd hbEnd (by omega)
  have hword := memoryWordNat_eq_of_memoryWordsFrom_one_eq current.memory initial.memory
    (aPtr.toNat + 32 + 32 * q) (by simpa only [current, initial] using hframe)
  dsimp only
  unfold sourceWord
  rw [readWord_eq_memoryWordOf_covered_padded current.memory current.activeWords
    (sourcePtr aPtr current.i) hcurrentCoverage.1 hcurrentCoverage.2.1]
  rw [haddress, hword]

/-- The generated source collector for a concrete prefix is the corresponding initial `a` prefix. -/
theorem functionOuterSourceWords_eq_inputPrefix
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount) (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    outerSourceWords aPtr bPtr (UInt256.ofNat fp) bCount count initial =
      memoryWordsFrom initial.memory (aPtr.toNat + 32) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let initial := functionInitialState mem aw fp aCount bCount
      have hsource := functionRow_sourceWord mem aw aPtr bPtr fp aCount bCount count
        (by omega) hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
      dsimp only
      rw [outerSourceWords_succ_last,
        Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
      rw [ih (by omega)]
      simpa only [initial, show aPtr.toNat + 32 + 32 * count =
        aPtr.toNat + 32 + 32 * count by rfl] using congrArg
          (fun word => memoryWordsFrom
            (functionInitialState mem aw fp aCount bCount).memory
            (aPtr.toNat + 32) count ++ [word]) hsource

/-- Any concrete outer prefix returns the exact product of the observed `a` prefix and all of `b`. -/
theorem functionRows_value
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) =
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory (aPtr.toNat + 32) count) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount) := by
  let initial := functionInitialState mem aw fp aCount bCount
  have hresultPtr := functionResultPtr_toNat fp (aCount + bCount) hbound
  have hzero := functionAllocatedMemory_payload_zero mem fp aCount bCount
    hmemSize hmemLe hgap
  have hzero' : memoryWordsFrom initial.memory
      ((UInt256.ofNat fp).toNat + 32) (aCount + bCount) =
        List.replicate (aCount + bCount) (⟨0⟩ : UInt256) := by
    simpa only [initial, functionInitialState, hresultPtr] using hzero
  have hupdates := functionRows_schoolbookRowUpdates mem aw aPtr bPtr fp aCount bCount count
    hcount hsum hbPos hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  have hvalue := rowsIterate_from_zero_value aPtr bPtr (UInt256.ofNat fp) bCount count
    (aCount + bCount) initial
    (memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount) hzero' (by
      simpa only [initial, hresultPtr] using hupdates)
  have hsource := functionOuterSourceWords_eq_inputPrefix mem aw aPtr bPtr fp aCount bCount
    count hcount hsum hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd
  rw [hsource] at hvalue
  simpa only [initial, hresultPtr] using hvalue

/-- The complete standalone schoolbook multiplication computes the exact full-limb product. -/
theorem functionSchoolbookMul_value
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := functionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount aCount initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (aPtr.toNat + 32) aCount) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount) := by
  exact functionRows_value mem aw aPtr bPtr fp aCount bCount aCount (by omega) hsum hbPos
    hcovered hawFit hmemSize hmemLe hgap hbound haEnd hbEnd


/-- Reused allocations compose the same concrete rows into an exact full schoolbook product. -/
theorem reusedFunctionRows_zeroTail
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count functionInitial
    Modexp.SchoolbookZeroTail
      (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
      count (aCount - count)
      (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) := by
  induction count with
  | zero =>
      let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
      have hpayload := reusedFunctionAllocatedMemory_payload_zero mem fp aCount bCount
        hmemSize hin
      have hzero : memoryWordsFrom functionInitial.memory (fp + 32) (aCount + bCount) =
          List.replicate (aCount + bCount) (⟨0⟩ : UInt256) := by
        simpa only [functionInitial, reusedFunctionInitialState] using hpayload
      have hinitial := Modexp.schoolbookZeroTail_initial
        (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
        aCount (aCount + bCount) (by rw [memoryWordsFrom_length]; omega)
      simpa only [functionInitial, rowsIterate, Nat.zero_sub, hzero] using hinitial
  | succ count ih =>
      let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
      let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count functionInitial
      have hprev : count ≤ aCount := by omega
      have hstrict : count < aCount := by omega
      have htail := ih hprev
      have hupdate := reusedFunctionRow_schoolbookRowUpdate mem aw aPtr bPtr fp aCount bCount count
        hsum hbPos hstrict hcovered hawFit hmemSize hin hbound haEnd hbEnd
        (by simpa only [functionInitial, current] using htail)
      have htailForStep : Modexp.SchoolbookZeroTail
          (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount)
          count ((aCount - (count + 1)) + 1)
          (memoryWordsFrom current.memory (fp + 32) (aCount + bCount)) := by
        simpa only [functionInitial, current, show aCount - count =
          (aCount - (count + 1)) + 1 by omega] using htail
      have hnext := Modexp.schoolbookRowUpdate_zeroTail hupdate htailForStep
      simpa only [functionInitial, current, rowsIterate_succ_last] using hnext

/-- Every row in the concrete function execution satisfies the pure schoolbook row relation. -/
theorem reusedFunctionRows_schoolbookRowUpdates
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let functionInitial := reusedFunctionInitialState mem aw fp aCount bCount
    ∀ q, q < count →
      let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q functionInitial
      Modexp.SchoolbookRowUpdate
        (sourceWord current.memory current.activeWords aPtr current.i)
        (memoryWordsFrom functionInitial.memory (bPtr.toNat + 32) bCount) q
        (memoryWordsFrom current.memory (fp + 32) (aCount + bCount))
        (memoryWordsFrom
          (rowAdvance aPtr bPtr (UInt256.ofNat fp) bCount current).memory
          (fp + 32) (aCount + bCount)) := by
  dsimp only
  intro q hq
  have htail := reusedFunctionRows_zeroTail mem aw aPtr bPtr fp aCount bCount q (by omega)
    hsum hbPos hcovered hawFit hmemSize hin hbound haEnd hbEnd
  exact reusedFunctionRow_schoolbookRowUpdate mem aw aPtr bPtr fp aCount bCount q hsum hbPos
    (by omega) hcovered hawFit hmemSize hin hbound haEnd hbEnd htail

/-- The source load for row `q` is exactly limb `q` of the immutable input `a` payload. -/
theorem reusedFunctionRow_sourceWord
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount q : Nat)
    (hq : q < aCount) (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial
    sourceWord current.memory current.activeWords aPtr current.i =
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat initial.memory
        (aPtr.toNat + 32 + 32 * q)) := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  let current := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount q initial
  have hi : current.i.toNat = q := by
    simpa only [current, initial] using
      reusedFunctionRows_i_toNat mem aw aPtr bPtr fp aCount bCount q hsum (by omega)
  have hfp64 : fp < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have haddress : (sourcePtr aPtr current.i).toNat = aPtr.toNat + 32 + 32 * q := by
    unfold sourcePtr
    rw [inputElementPtr_toNat aPtr current.i aCount fp haEnd (by rw [hi]; exact hq) hfp64,
      hi]
    omega
  have hcurrentCoverage := reusedFunctionRows_coverageForSemantic mem aw aPtr bPtr fp aCount bCount q
    (by omega) hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have hframe := reusedFunctionRows_memoryWords_below_result mem aw aPtr bPtr fp aCount bCount q
    (aPtr.toNat + 32 + 32 * q) 1 (by omega) hsum hcovered hawFit hmemSize hin
    hbound haEnd hbEnd (by omega)
  have hword := memoryWordNat_eq_of_memoryWordsFrom_one_eq current.memory initial.memory
    (aPtr.toNat + 32 + 32 * q) (by simpa only [current, initial] using hframe)
  dsimp only
  unfold sourceWord
  rw [readWord_eq_memoryWordOf_covered_padded current.memory current.activeWords
    (sourcePtr aPtr current.i) hcurrentCoverage.1 hcurrentCoverage.2.1]
  rw [haddress, hword]

/-- The generated source collector for a concrete prefix is the corresponding initial `a` prefix. -/
theorem reusedFunctionOuterSourceWords_eq_inputPrefix
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount) (hsum : aCount + bCount ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    outerSourceWords aPtr bPtr (UInt256.ofNat fp) bCount count initial =
      memoryWordsFrom initial.memory (aPtr.toNat + 32) count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let initial := reusedFunctionInitialState mem aw fp aCount bCount
      have hsource := reusedFunctionRow_sourceWord mem aw aPtr bPtr fp aCount bCount count
        (by omega) hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
      dsimp only
      rw [outerSourceWords_succ_last,
        Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
      rw [ih (by omega)]
      simpa only [initial, show aPtr.toNat + 32 + 32 * count =
        aPtr.toNat + 32 + 32 * count by rfl] using congrArg
          (fun word => memoryWordsFrom
            (reusedFunctionInitialState mem aw fp aCount bCount).memory
            (aPtr.toNat + 32) count ++ [word]) hsource

/-- Any concrete outer prefix returns the exact product of the observed `a` prefix and all of `b`. -/
theorem reusedFunctionRows_value
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount count : Nat)
    (hcount : count ≤ aCount)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount count initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) =
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory (aPtr.toNat + 32) count) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount) := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  have hresultPtr := functionResultPtr_toNat fp (aCount + bCount) hbound
  have hzero := reusedFunctionAllocatedMemory_payload_zero mem fp aCount bCount
    hmemSize hin
  have hzero' : memoryWordsFrom initial.memory
      ((UInt256.ofNat fp).toNat + 32) (aCount + bCount) =
        List.replicate (aCount + bCount) (⟨0⟩ : UInt256) := by
    simpa only [initial, reusedFunctionInitialState, hresultPtr] using hzero
  have hupdates := reusedFunctionRows_schoolbookRowUpdates mem aw aPtr bPtr fp aCount bCount count
    hcount hsum hbPos hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have hvalue := rowsIterate_from_zero_value aPtr bPtr (UInt256.ofNat fp) bCount count
    (aCount + bCount) initial
    (memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount) hzero' (by
      simpa only [initial, hresultPtr] using hupdates)
  have hsource := reusedFunctionOuterSourceWords_eq_inputPrefix mem aw aPtr bPtr fp aCount bCount
    count hcount hsum hcovered hawFit hmemSize hin hbound haEnd hbEnd
  rw [hsource] at hvalue
  simpa only [initial, hresultPtr] using hvalue

/-- The complete standalone schoolbook multiplication computes the exact full-limb product. -/
theorem reusedFunctionSchoolbookMul_value
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount aCount initial
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (aPtr.toNat + 32) aCount) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (bPtr.toNat + 32) bCount) := by
  exact reusedFunctionRows_value mem aw aPtr bPtr fp aCount bCount aCount (by omega) hsum hbPos
    hcovered hawFit hmemSize hin hbound haEnd hbEnd

/-- The reused multiplication's result is the product of the caller's original operand limbs. -/
theorem reusedFunctionSchoolbookMul_value_of_input
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat)
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hin : fp + wordArrayAllocationSize (aCount + bCount) ≤ mem.size)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (haBase : 96 ≤ aPtr.toNat) (hbBase : 96 ≤ bPtr.toNat)
    (haEnd : aPtr.toNat + 32 * (aCount + 1) ≤ fp)
    (hbEnd : bPtr.toNat + 32 * (bCount + 1) ≤ fp) :
    let final := reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (aCount + bCount)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (aPtr.toNat + 32) aCount) *
        Modexp.wordLimbsToNat (memoryWordsFrom mem (bPtr.toNat + 32) bCount) := by
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  let final := reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount
  have hvalue := reusedFunctionSchoolbookMul_value mem aw aPtr bPtr fp aCount bCount
    hsum hbPos hcovered hawFit hmemSize hin hbound haEnd hbEnd
  have haFrame := reusedFunctionAllocatedMemory_words_below mem fp aCount bCount
    (aPtr.toNat + 32) aCount hmemSize hin (by omega) (by omega) (by omega)
  have hbFrame := reusedFunctionAllocatedMemory_words_below mem fp aCount bCount
    (bPtr.toNat + 32) bCount hmemSize hin (by omega) (by omega) (by omega)
  simpa only [final, reusedFunctionFinalState, initial, reusedFunctionInitialState,
    haFrame, hbFrame] using hvalue

end Modexp.MultiLimbSchoolbookMulTrace
