import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSZeroLinks
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCompareLoop

/-! # Semantic links for CIOS final comparison and subtraction -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSCall
open Modexp.MultiLimbMontgomeryCompareTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The left pointer of the generated subtraction advances by one complete word per body. -/
theorem subtractionIterate_leftPtr_toNat (n : Nat) (state : SubtractionState)
    (hfit : state.leftPtr.toNat + 32 * n < UInt256.size) :
    (subtractionIterate n state).leftPtr.toNat = state.leftPtr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      have hstepFit : state.leftPtr.toNat + 32 < UInt256.size := by omega
      have hstep : (subtractionAdvance state).leftPtr.toNat =
          state.leftPtr.toNat + 32 := by
        simp [subtractionAdvance, uadd_word_lit32_toNat state.leftPtr hstepFit]
      have hrestFit :
          (subtractionAdvance state).leftPtr.toNat + 32 * n < UInt256.size := by
        rw [hstep]
        omega
      rw [subtractionIterate]
      rw [ih (subtractionAdvance state) hrestFit, hstep]
      omega

/-- The modulus pointer advances in lockstep with the output pointer. -/
theorem subtractionIterate_rightPtr_toNat (n : Nat) (state : SubtractionState)
    (hfit : state.rightPtr.toNat + 32 * n < UInt256.size) :
    (subtractionIterate n state).rightPtr.toNat = state.rightPtr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      have hstepFit : state.rightPtr.toNat + 32 < UInt256.size := by omega
      have hstep : (subtractionAdvance state).rightPtr.toNat =
          state.rightPtr.toNat + 32 := by
        simp [subtractionAdvance, uadd_word_lit32_toNat state.rightPtr hstepFit]
      have hrestFit :
          (subtractionAdvance state).rightPtr.toNat + 32 * n < UInt256.size := by
        rw [hstep]
        omega
      rw [subtractionIterate]
      rw [ih (subtractionAdvance state) hrestFit, hstep]
      omega

/-- One generated subtraction transition preserves covered, representable EVM memory. -/
theorem subtractionAdvance_coverage (state : SubtractionState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hleftFit : state.leftPtr.toNat + 32 + 31 < UInt256.size)
    (hrightFit : state.rightPtr.toNat + 32 + 31 < UInt256.size)
    (hgap : state.leftPtr.toNat - state.memory.size < USize.size) :
    MemoryCovered (subtractionAdvance state).memory
        (subtractionAdvance state).activeWords ∧
      (subtractionAdvance state).activeWords.toNat * 32 < UInt256.size := by
  have hleft := readWords1_coverage state.memory state.activeWords state.leftPtr
    hcovered hawFit hleftFit
  have hright := readWords1_coverage state.memory
    (readWords1 state.activeWords state.leftPtr) state.rightPtr
    hleft.1 hleft.2 hrightFit
  have hwrite := write32_coverage
    (subtractionStep state.memory state.activeWords state.leftPtr state.rightPtr
      state.borrow).1
    state.memory (readWords1 (readWords1 state.activeWords state.leftPtr)
      state.rightPtr) state.leftPtr hright.1 hright.2 hleftFit hgap
  simpa [subtractionAdvance, subtractionMemory, subtractionAw] using hwrite

/-- An in-bounds generated subtraction write does not resize the allocated result buffer. -/
theorem subtractionAdvance_memory_size (state : SubtractionState)
    (hwrite : state.leftPtr.toNat + 32 ≤ state.memory.size) :
    (subtractionAdvance state).memory.size = state.memory.size := by
  unfold subtractionAdvance subtractionMemory
  exact write_size_of_inBounds_from _ _ 0 state.leftPtr.toNat 32
    (by decide) (by rw [toByteArray_size]) hwrite

/-- Coverage, representability, and allocated memory size propagate through an arbitrary number
of in-bounds subtraction columns. -/
theorem subtractionIterate_coverage_size
    (n : Nat) (state : SubtractionState)
    (hleftFit : state.leftPtr.toNat + 32 * n + 31 < UInt256.size)
    (hrightFit : state.rightPtr.toNat + 32 * n + 31 < UInt256.size)
    (hleftMem : state.leftPtr.toNat + 32 * n ≤ state.memory.size)
    (hrightMem : state.rightPtr.toNat + 32 * n ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    (subtractionIterate n state).memory.size = state.memory.size ∧
      MemoryCovered (subtractionIterate n state).memory
        (subtractionIterate n state).activeWords ∧
      (subtractionIterate n state).activeWords.toNat * 32 < UInt256.size := by
  induction n generalizing state with
  | zero => exact ⟨rfl, hcovered, hawFit⟩
  | succ n ih =>
      let next := subtractionAdvance state
      have hleftStepFit : state.leftPtr.toNat + 32 < UInt256.size := by omega
      have hrightStepFit : state.rightPtr.toNat + 32 < UInt256.size := by omega
      have hnextLeft : next.leftPtr.toNat = state.leftPtr.toNat + 32 := by
        simp [next, subtractionAdvance,
          uadd_word_lit32_toNat state.leftPtr hleftStepFit]
      have hnextRight : next.rightPtr.toNat = state.rightPtr.toNat + 32 := by
        simp [next, subtractionAdvance,
          uadd_word_lit32_toNat state.rightPtr hrightStepFit]
      have hfirstWrite : state.leftPtr.toNat + 32 ≤ state.memory.size := by omega
      have hnextSize : next.memory.size = state.memory.size :=
        subtractionAdvance_memory_size state hfirstWrite
      have hnextCoverage := subtractionAdvance_coverage state hcovered hawFit
        (by omega) (by omega) (by
          rw [Nat.sub_eq_zero_of_le (by omega)]
          exact lt_usize 0 (by norm_num))
      have hrest := ih next (by rw [hnextLeft]; omega) (by rw [hnextRight]; omega)
        (by rw [hnextLeft, hnextSize]; omega)
        (by rw [hnextRight, hnextSize]; omega)
        hnextCoverage.1 hnextCoverage.2
      rw [subtractionIterate]
      exact ⟨hrest.1.trans hnextSize, hrest.2⟩

/-- A covered generated load is the corresponding word in `memoryWordsFrom`. -/
theorem readWord_eq_memoryWordOf_covered (mem : ByteArray) (aw ptr : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hword : ptr.toNat + 32 ≤ mem.size) :
    readWord mem aw ptr = UInt256.ofNat
      (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat) := by
  unfold Modexp.MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by omega,
    wordBelowActive_of_covered mem aw ptr hcovered hawFit hword⟩)]
  rfl

/-- The evolving left collector reads the original candidate vector before overwriting it. -/
theorem subtractionLeftWords_eq_initialMemoryWords
    (n : Nat) (state : SubtractionState)
    (hleftFit : state.leftPtr.toNat + 32 * n + 31 < UInt256.size)
    (hcovered : ∀ j, j < n →
      let current := subtractionIterate j state
      MemoryCovered current.memory current.activeWords)
    (hawFit : ∀ j, j < n →
      let current := subtractionIterate j state
      current.activeWords.toNat * 32 < UInt256.size)
    (hwords : ∀ j, j < n →
      let current := subtractionIterate j state
      current.leftPtr.toNat + 32 ≤ current.memory.size) :
    subtractionLeftWords n state =
      memoryWordsFrom state.memory state.leftPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := subtractionAdvance state
      have hstepFit : state.leftPtr.toNat + 32 < UInt256.size := by omega
      have hnextPtr : next.leftPtr.toNat = state.leftPtr.toNat + 32 := by
        simp [next, subtractionAdvance,
          uadd_word_lit32_toNat state.leftPtr hstepFit]
      have hfirstCovered : MemoryCovered state.memory state.activeWords := by
        simpa only [subtractionIterate] using hcovered 0 (by omega)
      have hfirstAwFit : state.activeWords.toNat * 32 < UInt256.size := by
        simpa only [subtractionIterate] using hawFit 0 (by omega)
      have hfirstWord : state.leftPtr.toNat + 32 ≤ state.memory.size := by
        simpa only [subtractionIterate] using hwords 0 (by omega)
      have hhead := readWord_eq_memoryWordOf_covered state.memory state.activeWords
        state.leftPtr hfirstCovered hfirstAwFit hfirstWord
      have hnextCovered : ∀ j, j < n →
          let current := subtractionIterate j next
          MemoryCovered current.memory current.activeWords := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hcovered (j + 1) (by omega)
      have hnextAwFit : ∀ j, j < n →
          let current := subtractionIterate j next
          current.activeWords.toNat * 32 < UInt256.size := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hawFit (j + 1) (by omega)
      have hnextWords : ∀ j, j < n →
          let current := subtractionIterate j next
          current.leftPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hwords (j + 1) (by omega)
      have htail := ih next (by rw [hnextPtr]; omega)
        hnextCovered hnextAwFit hnextWords
      have hframe := memoryWordsFrom_write_below
        (subtractionStep state.memory state.activeWords state.leftPtr state.rightPtr
          state.borrow).1.toByteArray
        state.memory state.leftPtr.toNat (state.leftPtr.toNat + 32) n
        (by rw [toByteArray_size]) hfirstWord (by omega)
      simp only [subtractionLeftWords, memoryWordsFrom]
      rw [hhead, htail]
      congr 1
      simpa only [next, subtractionAdvance, subtractionMemory,
        uadd_word_lit32_toNat state.leftPtr hstepFit] using hframe

/-- With the modulus below the output buffer, every evolving right load reads the original
modulus vector. -/
theorem subtractionRightWords_eq_initialMemoryWords
    (n : Nat) (state : SubtractionState)
    (hleftFit : state.leftPtr.toNat + 32 * n + 31 < UInt256.size)
    (hrightFit : state.rightPtr.toNat + 32 * n + 31 < UInt256.size)
    (hdisjoint : state.rightPtr.toNat + 32 * n ≤ state.leftPtr.toNat)
    (hcovered : ∀ j, j < n →
      let current := subtractionIterate j state
      MemoryCovered current.memory current.activeWords)
    (hawFit : ∀ j, j < n →
      let current := subtractionIterate j state
      current.activeWords.toNat * 32 < UInt256.size)
    (hwords : ∀ j, j < n →
      let current := subtractionIterate j state
      current.leftPtr.toNat + 32 ≤ current.memory.size ∧
        current.rightPtr.toNat + 32 ≤ current.memory.size) :
    subtractionRightWords n state =
      memoryWordsFrom state.memory state.rightPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := subtractionAdvance state
      have hleftStepFit : state.leftPtr.toNat + 32 < UInt256.size := by omega
      have hrightStepFit : state.rightPtr.toNat + 32 < UInt256.size := by omega
      have hnextLeft : next.leftPtr.toNat = state.leftPtr.toNat + 32 := by
        simp [next, subtractionAdvance,
          uadd_word_lit32_toNat state.leftPtr hleftStepFit]
      have hnextRight : next.rightPtr.toNat = state.rightPtr.toNat + 32 := by
        simp [next, subtractionAdvance,
          uadd_word_lit32_toNat state.rightPtr hrightStepFit]
      have hfirstCovered : MemoryCovered state.memory state.activeWords := by
        simpa only [subtractionIterate] using hcovered 0 (by omega)
      have hfirstAwFit : state.activeWords.toNat * 32 < UInt256.size := by
        simpa only [subtractionIterate] using hawFit 0 (by omega)
      have hfirstWords : state.leftPtr.toNat + 32 ≤ state.memory.size ∧
          state.rightPtr.toNat + 32 ≤ state.memory.size := by
        simpa only [subtractionIterate] using hwords 0 (by omega)
      have hleftExpansion := readWords1_coverage state.memory state.activeWords
        state.leftPtr hfirstCovered hfirstAwFit (by omega)
      have hhead := readWord_eq_memoryWordOf_covered state.memory
        (readWords1 state.activeWords state.leftPtr) state.rightPtr
        hleftExpansion.1 hleftExpansion.2 hfirstWords.2
      have hnextCovered : ∀ j, j < n →
          let current := subtractionIterate j next
          MemoryCovered current.memory current.activeWords := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hcovered (j + 1) (by omega)
      have hnextAwFit : ∀ j, j < n →
          let current := subtractionIterate j next
          current.activeWords.toNat * 32 < UInt256.size := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hawFit (j + 1) (by omega)
      have hnextWords : ∀ j, j < n →
          let current := subtractionIterate j next
          current.leftPtr.toNat + 32 ≤ current.memory.size ∧
            current.rightPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hwords (j + 1) (by omega)
      have htail := ih next (by rw [hnextLeft]; omega) (by rw [hnextRight]; omega)
        (by rw [hnextLeft, hnextRight]; omega)
        hnextCovered hnextAwFit hnextWords
      have hframe := memoryWordsFrom_write_above
        (subtractionStep state.memory state.activeWords state.leftPtr state.rightPtr
          state.borrow).1.toByteArray
        state.memory state.leftPtr.toNat (state.rightPtr.toNat + 32) n
        (by rw [toByteArray_size]) (by omega) (by omega)
      simp only [subtractionRightWords, memoryWordsFrom]
      rw [hhead, htail]
      congr 1
      simpa only [next, subtractionAdvance, subtractionMemory,
        uadd_word_lit32_toNat state.rightPtr hrightStepFit] using hframe

/-- Reading a subwindow from an arbitrary source-window copy returns the source subwindow. -/
theorem write_read_copy_window (source base : ByteArray)
    (src dest total start len : Nat)
    (htotal : total ≠ 0) (hsource : src + total ≤ source.size)
    (hdest : dest ≤ base.size) (hwindow : start + len ≤ total)
    (hlen : 0 < len) (hlen64 : len < 2 ^ 64) :
    (source.write src base dest total).readWithPadding (dest + start) len =
      source.extract (src + start) (src + start + len) := by
  have hprefix : (base.extract 0 dest).size = dest := by
    rw [ByteArray.size_extract]
    omega
  have hcopied : (source.extract src (src + total)).size = total := by
    rw [ByteArray.size_extract]
    omega
  by_cases hin : dest + total ≤ base.size
  · rw [write_eq_gen_from source base src dest total htotal hsource hin]
    rw [readWithPadding_eq_extract' _ (dest + start) len hlen hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hcopied]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hprefix, hcopied]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show dest + start - dest = start by omega,
      show dest + start + len - dest = start + len by omega]
    rw [extract_extract_BA]
    congr 1 <;> omega
  · have hext : base.size < dest + total := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend_from source base src dest total htotal hsource hdest hext]
    rw [readWithPadding_eq_extract' _ (dest + start) len hlen hlen64 (by
      rw [ByteArray.size_append, hprefix, hcopied]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show dest + start - dest = start by omega,
      show dest + start + len - dest = start + len by omega]
    rw [extract_extract_BA]
    congr 1 <;> omega

/-- Every complete word window of an in-range `MCOPY` destination is its source word. -/
theorem memoryWordsFrom_write_copy_window
    (source base : ByteArray) (src dest totalWords offset words : Nat)
    (htotal : 0 < totalWords)
    (hsrc : src + 32 * totalWords ≤ source.size)
    (hdest : dest ≤ base.size)
    (hwindow : offset + words ≤ totalWords) :
    memoryWordsFrom
        (source.write src base dest (32 * totalWords))
        (dest + 32 * offset) words =
      memoryWordsFrom source (src + 32 * offset) words := by
  induction words generalizing offset with
  | zero => rfl
  | succ words ih =>
      have hoffset : offset < totalWords := by omega
      have hread := write_read_copy_window source base src dest (32 * totalWords)
        (32 * offset) 32 (by omega) hsrc hdest (by omega) (by omega) (by norm_num)
      have hsourceRead :
          source.extract (src + 32 * offset) (src + 32 * offset + 32) =
            source.readWithPadding (src + 32 * offset) 32 := by
        symm
        apply readWithPadding_eq_extract'
        · omega
        · norm_num
        · omega
      rw [hsourceRead] at hread
      have htail := ih (offset + 1) (by omega)
      simp only [memoryWordsFrom]
      rw [show dest + 32 * offset + 32 = dest + 32 * (offset + 1) by ring,
        show src + 32 * offset + 32 = src + 32 * (offset + 1) by ring,
        htail]
      congr 1
      unfold Modexp.MultiLimbMemoryModel.memoryWordNat
      exact congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes)) hread

/-- The CIOS final `MCOPY` places exactly the low candidate limbs in the result buffer. -/
theorem finalCopyMemory_words_eq_source
    (columns : Nat) (mem : ByteArray) (source result bytes : UInt256)
    (hcolumns : 0 < columns)
    (hbytes : bytes.toNat = 32 * columns)
    (hsource : source.toNat + 32 * columns ≤ mem.size)
    (hresult : result.toNat ≤ mem.size) :
    memoryWordsFrom (finalCopyMemory mem source result bytes) result.toNat columns =
      memoryWordsFrom mem source.toNat columns := by
  unfold finalCopyMemory
  rw [hbytes]
  simpa only [Nat.zero_add, Nat.mul_zero] using
    memoryWordsFrom_write_copy_window mem mem source.toNat result.toNat columns 0
      columns hcolumns hsource hresult (by omega)

/-- An in-bounds final `MCOPY` retains the allocated byte-array size. -/
theorem finalCopyMemory_size
    (mem : ByteArray) (source result bytes : UInt256)
    (hbytes : bytes.toNat ≠ 0)
    (hsource : source.toNat + bytes.toNat ≤ mem.size)
    (hresult : result.toNat + bytes.toNat ≤ mem.size) :
    (finalCopyMemory mem source result bytes).size = mem.size := by
  unfold finalCopyMemory
  exact write_size_of_inBounds_from mem mem source.toNat result.toNat bytes.toNat
    hbytes hsource hresult

/-- A copy whose destination starts in concrete memory has the expected size even when the copied
window extends that memory.  This is the first-call counterpart of `finalCopyMemory_size`. -/
theorem finalCopyMemory_size_from_start
    (mem : ByteArray) (source result bytes : UInt256)
    (hbytes : bytes.toNat ≠ 0)
    (hsource : source.toNat + bytes.toNat ≤ mem.size)
    (hresult : result.toNat ≤ mem.size) :
    (finalCopyMemory mem source result bytes).size =
      max mem.size (result.toNat + bytes.toNat) := by
  by_cases hin : result.toNat + bytes.toNat ≤ mem.size
  · rw [finalCopyMemory_size mem source result bytes hbytes hsource hin,
      max_eq_left hin]
  · have hext : mem.size < result.toNat + bytes.toNat := Nat.lt_of_not_ge hin
    unfold finalCopyMemory
    rw [write_eq_gen_extend_from mem mem source.toNat result.toNat bytes.toNat
      hbytes hsource hresult hext, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, max_eq_right hext.le]
    omega

/-- The EVM active-word update covers an extending copy as well as an in-bounds one. -/
theorem finalCopy_coverage_from_start
    (mem : ByteArray) (aw source result bytes : UInt256)
    (hbytes : bytes.toNat ≠ 0)
    (hsource : source.toNat + bytes.toNat ≤ mem.size)
    (hresult : result.toNat ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haccessFit : max result.toNat source.toNat + bytes.toNat + 31 < UInt256.size) :
    MemoryCovered (finalCopyMemory mem source result bytes)
        (finalCopyAw aw source result bytes) ∧
      (finalCopyAw aw source result bytes).toNat * 32 < UInt256.size := by
  let access := max result.toNat source.toNat
  let expanded := MachineState.M aw.toNat access bytes.toNat
  have hexpandedFit : expanded * 32 < UInt256.size :=
    machineM_mul32_lt_size hawFit (by simpa only [access] using haccessFit)
  have hexpandedNat : (UInt256.ofNat expanded).toNat = expanded := by
    apply UInt256.toNat_ofNat_of_lt
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_right expanded (by decide : 0 < 32))
      hexpandedFit
  have hsize := finalCopyMemory_size_from_start mem source result bytes hbytes hsource hresult
  have hold : mem.size ≤ 32 * expanded := by
    have hawLe : aw.toNat ≤ expanded := by
      dsimp only [expanded]
      simp [MachineState.M, hbytes]
    unfold MemoryCovered at hcovered
    nlinarith
  have hnew : result.toNat + bytes.toNat ≤ 32 * expanded := by
    have haccess : result.toNat ≤ access := Nat.le_max_left _ _
    have hspan := machineM_access_le (s := aw.toNat) (off := access)
      (len := bytes.toNat) (Nat.pos_of_ne_zero hbytes)
    dsimp only [expanded]
    omega
  constructor
  · unfold MemoryCovered finalCopyAw
    rw [hsize, hexpandedNat]
    exact max_le hold hnew
  · unfold finalCopyAw
    rw [hexpandedNat]
    exact hexpandedFit

/-- The active-word update accompanying final `MCOPY` covers its unchanged allocated memory. -/
theorem finalCopy_coverage
    (mem : ByteArray) (aw source result bytes : UInt256)
    (hbytes : bytes.toNat ≠ 0)
    (hsource : source.toNat + bytes.toNat ≤ mem.size)
    (hresult : result.toNat + bytes.toNat ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (haccessFit : max result.toNat source.toNat + bytes.toNat + 31 < UInt256.size) :
    MemoryCovered (finalCopyMemory mem source result bytes)
        (finalCopyAw aw source result bytes) ∧
      (finalCopyAw aw source result bytes).toNat * 32 < UInt256.size := by
  have hnext := machineM_coverage mem aw (max result.toNat source.toNat)
    bytes.toNat hcovered hawFit haccessFit
  have hsize := finalCopyMemory_size mem source result bytes hbytes hsource hresult
  unfold finalCopyAw
  constructor
  · unfold MemoryCovered at hnext ⊢
    rw [hsize]
    exact hnext.1
  · exact hnext.2

/-- A copy into a result buffer above a complete word range preserves that lower range. -/
theorem memoryWordsFrom_finalCopy_below
    (columns : Nat) (mem : ByteArray) (source result bytes : UInt256)
    (read : Nat)
    (hbytes : bytes.toNat ≠ 0)
    (hsource : source.toNat + bytes.toNat ≤ mem.size)
    (hresult : result.toNat ≤ mem.size)
    (hread : read + 32 * columns ≤ mem.size)
    (hbelow : read + 32 * columns ≤ result.toNat) :
    memoryWordsFrom (finalCopyMemory mem source result bytes) read columns =
      memoryWordsFrom mem read columns := by
  induction columns generalizing read with
  | zero => rfl
  | succ columns ih =>
      simp only [memoryWordsFrom]
      have hword :
          (finalCopyMemory mem source result bytes).readWithPadding read 32 =
            mem.readWithPadding read 32 := by
        unfold finalCopyMemory
        exact write_read_below_gen_from_extend mem mem source.toNat result.toNat
          bytes.toNat read 32 hbytes hsource hresult (by omega) (by omega)
          (by decide) (by decide)
      rw [show Modexp.MultiLimbMemoryModel.memoryWordNat
          (finalCopyMemory mem source result bytes) read =
          Modexp.MultiLimbMemoryModel.memoryWordNat mem read by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hword]]
      congr 1
      exact ih (read + 32) (by omega) (by omega)

/-- Actual candidate words inspected by the descending generated comparison, in little-endian
limb order. -/
def compareCandidateWords (mem : ByteArray) : Nat → CompareState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      compareCandidateWords mem n (compareAdvance state) ++
        [compareTWord mem state.activeWords state.tOff]

/-- Actual modulus words inspected by the descending generated comparison, in little-endian limb
order. -/
def compareModulusWords (mem : ByteArray) : Nat → CompareState → List UInt256
  | 0, _ => []
  | n + 1, state =>
      compareModulusWords mem n (compareAdvance state) ++
        [compareNWord mem state.activeWords state.tOff state.nOff]

/-- Tail-recursive comparison-state iteration in the order used by the executable selector. -/
def compareTailIterate : Nat → CompareState → CompareState
  | 0, state => state
  | n + 1, state => compareTailIterate n (compareAdvance state)

@[simp] theorem compareCandidateWords_length (mem : ByteArray)
    (n : Nat) (state : CompareState) :
    (compareCandidateWords mem n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [compareCandidateWords, ih]

@[simp] theorem compareModulusWords_length (mem : ByteArray)
    (n : Nat) (state : CompareState) :
    (compareModulusWords mem n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [compareModulusWords, ih]

/-- Appending an equal most-significant word preserves the descending comparison result. -/
theorem limbsLtMSB_append_equal (left right : List UInt256) (word : UInt256)
    (hlength : left.length = right.length) :
    limbsLtMSB (left ++ [word]) (right ++ [word]) ↔ limbsLtMSB left right := by
  rw [limbsLtMSB_iff (left ++ [word]) (right ++ [word]) (by simp [hlength]),
    limbsLtMSB_iff left right hlength]
  rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append, hlength]
  omega

/-- A differing equal-width high suffix determines comparison regardless of lower limbs. -/
theorem limbsLtMSB_append_of_suffix_ne
    (leftPrefix rightPrefix leftSuffix rightSuffix : List UInt256)
    (hprefix : leftPrefix.length = rightPrefix.length)
    (hsuffix : leftSuffix.length = rightSuffix.length)
    (hne : Modexp.wordLimbsToNat leftSuffix ≠
      Modexp.wordLimbsToNat rightSuffix) :
    limbsLtMSB (leftPrefix ++ leftSuffix) (rightPrefix ++ rightSuffix) ↔
      limbsLtMSB leftSuffix rightSuffix := by
  rw [limbsLtMSB_iff (leftPrefix ++ leftSuffix) (rightPrefix ++ rightSuffix) (by
      simp [hprefix, hsuffix]),
    limbsLtMSB_iff leftSuffix rightSuffix hsuffix]
  rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append, hprefix]
  have hleftBound := Modexp.wordLimbsToNat_lt_pow leftPrefix
  have hrightBound := Modexp.wordLimbsToNat_lt_pow rightPrefix
  rw [hprefix] at hleftBound
  let radix := UInt256.size ^ rightPrefix.length
  have hradix : 0 < radix := Nat.pow_pos (by norm_num [UInt256.size])
  change Modexp.wordLimbsToNat leftPrefix +
        radix * Modexp.wordLimbsToNat leftSuffix <
      Modexp.wordLimbsToNat rightPrefix +
        radix * Modexp.wordLimbsToNat rightSuffix ↔
      Modexp.wordLimbsToNat leftSuffix < Modexp.wordLimbsToNat rightSuffix
  constructor
  · intro hfull
    by_contra hsuffixLt
    have hreverse : Modexp.wordLimbsToNat rightSuffix <
        Modexp.wordLimbsToNat leftSuffix := by omega
    have hstep : Modexp.wordLimbsToNat rightSuffix + 1 ≤
        Modexp.wordLimbsToNat leftSuffix := by omega
    have hmul := Nat.mul_le_mul_left radix hstep
    have hfullReverse :
        Modexp.wordLimbsToNat rightPrefix +
            radix * Modexp.wordLimbsToNat rightSuffix <
          Modexp.wordLimbsToNat leftPrefix +
            radix * Modexp.wordLimbsToNat leftSuffix := by
      calc
        _ < radix + radix * Modexp.wordLimbsToNat rightSuffix := by omega
        _ = radix * (Modexp.wordLimbsToNat rightSuffix + 1) := by ring
        _ ≤ radix * Modexp.wordLimbsToNat leftSuffix := hmul
        _ ≤ Modexp.wordLimbsToNat leftPrefix +
            radix * Modexp.wordLimbsToNat leftSuffix := by omega
    omega
  · intro hsuffixLt
    have hstep : Modexp.wordLimbsToNat leftSuffix + 1 ≤
        Modexp.wordLimbsToNat rightSuffix := by omega
    have hmul := Nat.mul_le_mul_left radix hstep
    calc
      _ < radix + radix * Modexp.wordLimbsToNat leftSuffix := by omega
      _ = radix * (Modexp.wordLimbsToNat leftSuffix + 1) := by ring
      _ ≤ radix * Modexp.wordLimbsToNat rightSuffix := hmul
      _ ≤ Modexp.wordLimbsToNat rightPrefix +
          radix * Modexp.wordLimbsToNat rightSuffix := by omega

theorem limbsLtMSB_singleton_iff (left right : UInt256) :
    limbsLtMSB [left] [right] ↔ left.toNat < right.toNat := by
  simp only [limbsLtMSB, Modexp.wordLimbsToNat]
  simp

/-- The comparison selector's branch bit is exactly the strict ordering of every generated word
load that led to it. -/
theorem selectedCIOSCompare_doSub_zero_iff
    {fuel : Nat} {mem : ByteArray} {tP : UInt256} {state : CompareState}
    {prevTOff : UInt256} {selected : CIOSCompareSelection}
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectCIOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    selected.doSub = ⟨0⟩ ↔
      limbsLtMSB (compareCandidateWords mem selected.iterations state)
        (compareModulusWords mem selected.iterations state) := by
  induction fuel generalizing state prevTOff selected with
  | zero => simp [selectCIOSCompare] at hselect
  | succ fuel ih =>
      simp only [selectCIOSCompare] at hselect
      by_cases hgreater :
          (compareNWord mem state.activeWords state.tOff state.nOff).toNat <
            (compareTWord mem state.activeWords state.tOff).toNat
      · rw [if_pos hgreater] at hselect
        injection hselect with heq
        subst selected
        simp only [compareCandidateWords, compareModulusWords, List.nil_append]
        rw [limbsLtMSB_singleton_iff]
        constructor
        · intro hone
          norm_num [UInt256.size] at hone
        · intro hlt
          omega
      · rw [if_neg hgreater] at hselect
        by_cases hless :
            (compareTWord mem state.activeWords state.tOff).toNat <
              (compareNWord mem state.activeWords state.tOff state.nOff).toNat
        · rw [if_pos hless] at hselect
          injection hselect with heq
          subst selected
          simp only [compareCandidateWords, compareModulusWords, List.nil_append]
          rw [limbsLtMSB_singleton_iff]
          exact ⟨fun _ => hless, fun _ => True.intro⟩
        · rw [if_neg hless] at hselect
          have hequal : compareTWord mem state.activeWords state.tOff =
              compareNWord mem state.activeWords state.tOff state.nOff := by
            apply u256_inj
            omega
          by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
          · rw [if_pos hguard] at hselect
            let next : CompareState := compareAdvance state
            cases hrest : selectCIOSCompare fuel mem tP next.activeWords next.tOff
                next.nOff (comparePrev prevTOff) with
            | none =>
                have hrest' : selectCIOSCompare fuel mem tP
                    (compareAw state.activeWords state.tOff state.nOff) prevTOff
                    (comparePrev state.nOff) (comparePrev prevTOff) = none := by
                  simpa [next, compareAdvance, hprev] using hrest
                rw [hrest'] at hselect
                contradiction
            | some rest =>
                have hrest' : selectCIOSCompare fuel mem tP
                    (compareAw state.activeWords state.tOff state.nOff) prevTOff
                    (comparePrev state.nOff) (comparePrev prevTOff) = some rest := by
                  simpa [next, compareAdvance, hprev] using hrest
                rw [hrest'] at hselect
                injection hselect with heq
                subst selected
                have hih := ih (state := next) (prevTOff := comparePrev prevTOff)
                  (selected := rest) (by simp [next, compareAdvance, hprev]) hrest
                rw [hih]
                simp only [compareCandidateWords, compareModulusWords]
                rw [hequal]
                simpa only [next] using (limbsLtMSB_append_equal
                  (compareCandidateWords mem rest.iterations next)
                  (compareModulusWords mem rest.iterations next)
                  (compareNWord mem state.activeWords state.tOff state.nOff)
                  (by simp)).symm
          · rw [if_neg hguard] at hselect
            injection hselect with heq
            subst selected
            simp only [compareCandidateWords, compareModulusWords, List.nil_append]
            rw [limbsLtMSB_singleton_iff, hequal]
            constructor
            · intro hone
              norm_num [UInt256.size] at hone
            · intro hlt
              omega

/-
/- A selected comparison's active-word counter is repeated execution of its exact two-load
transition. -/
set_option maxRecDepth 2000 in
theorem selectedCIOSCompare_activeWords_eq_tailIterate
    {fuel : Nat} {mem : ByteArray} {tP : UInt256} {state : CompareState}
    {prevTOff : UInt256} {selected : CIOSCompareSelection}
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectCIOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    selected.activeWords = (compareTailIterate selected.iterations state).activeWords := by
  induction fuel generalizing state prevTOff selected with
  | zero => simp [selectCIOSCompare] at hselect
  | succ fuel ih =>
      simp only [selectCIOSCompare] at hselect
      by_cases hgreater :
          (compareNWord mem state.activeWords state.tOff state.nOff).toNat <
            (compareTWord mem state.activeWords state.tOff).toNat
      · rw [if_pos hgreater] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hgreater] at hselect
        by_cases hless :
            (compareTWord mem state.activeWords state.tOff).toNat <
              (compareNWord mem state.activeWords state.tOff state.nOff).toNat
        · rw [if_pos hless] at hselect
          injection hselect with heq
          subst selected
          rfl
        · rw [if_neg hless] at hselect
          by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
          · rw [if_pos hguard] at hselect
            let next := compareAdvance state
            cases hrest : selectCIOSCompare fuel mem tP next.activeWords next.tOff
                next.nOff (comparePrev prevTOff) with
            | none =>
                have hrest' : selectCIOSCompare fuel mem tP
                    (compareAw state.activeWords state.tOff state.nOff) prevTOff
                    (comparePrev state.nOff) (comparePrev prevTOff) = none := by
                  simpa [next, compareAdvance, hprev] using hrest
                rw [hrest'] at hselect
                contradiction
            | some rest =>
                have hrest' : selectCIOSCompare fuel mem tP
                    (compareAw state.activeWords state.tOff state.nOff) prevTOff
                    (comparePrev state.nOff) (comparePrev prevTOff) = some rest := by
                  simpa [next, compareAdvance, hprev] using hrest
                rw [hrest'] at hselect
                injection hselect with heq
                subst selected
                have hih := ih (state := next) (prevTOff := comparePrev prevTOff)
                  (selected := rest) (by simp [next, compareAdvance, hprev]) hrest
                simpa only [compareTailIterate, next] using hih
          · rw [if_neg hguard] at hselect
            injection hselect with heq
            subst selected
            rfl
-/

/-- Once the inspected words are identified as the high suffix of complete limb vectors, the
selector bit is the pure full-vector comparison. -/
theorem selectedCIOSCompare_doSub_zero_iff_fullWords
    {fuel : Nat} {mem : ByteArray} {tP : UInt256} {state : CompareState}
    {prevTOff : UInt256} {selected : CIOSCompareSelection}
    (candidate modulus candidatePrefix modulusPrefix : List UInt256)
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectCIOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected)
    (hcandidate : candidate = candidatePrefix ++
      compareCandidateWords mem selected.iterations state)
    (hmodulus : modulus = modulusPrefix ++
      compareModulusWords mem selected.iterations state)
    (hprefixLength : candidatePrefix.length = modulusPrefix.length)
    (hterminal :
      Modexp.wordLimbsToNat
          (compareCandidateWords mem selected.iterations state) ≠
        Modexp.wordLimbsToNat
          (compareModulusWords mem selected.iterations state) ∨
      (candidatePrefix = [] ∧ modulusPrefix = [])) :
    selected.doSub = ⟨0⟩ ↔ limbsLtMSB candidate modulus := by
  rw [selectedCIOSCompare_doSub_zero_iff hprev hselect, hcandidate, hmodulus]
  rcases hterminal with hne | ⟨hcempty, hmempty⟩
  · exact (limbsLtMSB_append_of_suffix_ne candidatePrefix modulusPrefix
      (compareCandidateWords mem selected.iterations state)
      (compareModulusWords mem selected.iterations state) hprefixLength (by simp) hne).symm
  · subst candidatePrefix
    subst modulusPrefix
    simp

/-- The descending-pointer helper subtracts exactly one word whenever its input is at least one
word. -/
theorem comparePrev_toNat (ptr : UInt256) (hptr : 32 ≤ ptr.toNat) :
    (comparePrev ptr).toNat = ptr.toNat - 32 := by
  unfold comparePrev
  rw [uadd_toNat, lnot31_toNat]
  have hp : ptr.toNat < UInt256.size := ptr.val.isLt
  rw [show ptr.toNat + (2 ^ 256 - 32) =
      UInt256.size + (ptr.toNat - 32) by
    simp only [UInt256.size]
    omega]
  have hdiff : ptr.toNat - 32 < UInt256.size := by omega
  simpa using Nat.mod_eq_of_lt hdiff

/-- Both comparison loads preserve memory coverage and a representable active-word count. -/
theorem compareAdvance_coverage (mem : ByteArray) (state : CompareState)
    (hcovered : MemoryCovered mem state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (htFit : (comparePrev state.tOff).toNat + 32 + 31 < UInt256.size)
    (hnFit : (comparePrev state.nOff).toNat + 32 + 31 < UInt256.size) :
    MemoryCovered mem (compareAdvance state).activeWords ∧
      (compareAdvance state).activeWords.toNat * 32 < UInt256.size := by
  have ht := readWords1_coverage mem state.activeWords (comparePrev state.tOff)
    hcovered hawFit htFit
  have hn := readWords1_coverage mem (compareAw1 state.activeWords state.tOff)
    (comparePrev state.nOff) (by simpa [compareAw1] using ht.1)
    (by simpa [compareAw1] using ht.2) hnFit
  simpa [compareAdvance, compareAw, compareAw1] using hn

/-- Under concrete pointer and memory geometry, the generated descending loads are exactly the
complete little-endian candidate and modulus vectors. -/
theorem compareWords_eq_memoryWordsFrom
    (columns : Nat) (mem : ByteArray) (state : CompareState)
    (candidateBase modulusBase : Nat)
    (htOff : state.tOff.toNat = candidateBase + 32 * columns)
    (hnOff : state.nOff.toNat = modulusBase + 32 * columns)
    (htFit : candidateBase + 32 * columns + 31 < UInt256.size)
    (hnFit : modulusBase + 32 * columns + 31 < UInt256.size)
    (htMem : candidateBase + 32 * columns ≤ mem.size)
    (hnMem : modulusBase + 32 * columns ≤ mem.size)
    (hcovered : MemoryCovered mem state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    compareCandidateWords mem columns state =
        memoryWordsFrom mem candidateBase columns ∧
      compareModulusWords mem columns state =
        memoryWordsFrom mem modulusBase columns := by
  induction columns generalizing state with
  | zero => simp [compareCandidateWords, compareModulusWords, memoryWordsFrom]
  | succ columns ih =>
      have htLo : 32 ≤ state.tOff.toNat := by rw [htOff]; omega
      have hnLo : 32 ≤ state.nOff.toNat := by rw [hnOff]; omega
      have htPrev : (comparePrev state.tOff).toNat =
          candidateBase + 32 * columns := by
        rw [comparePrev_toNat state.tOff htLo, htOff]
        omega
      have hnPrev : (comparePrev state.nOff).toNat =
          modulusBase + 32 * columns := by
        rw [comparePrev_toNat state.nOff hnLo, hnOff]
        omega
      have htCoverage := readWords1_coverage mem state.activeWords
        (comparePrev state.tOff) hcovered hawFit (by rw [htPrev]; omega)
      have htWord : compareTWord mem state.activeWords state.tOff =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
            (candidateBase + 32 * columns)) := by
        unfold compareTWord
        have hread := readWord_eq_memoryWordOf_covered mem state.activeWords
          (comparePrev state.tOff) hcovered hawFit (by rw [htPrev]; omega)
        simpa only [htPrev] using hread
      have hnWord : compareNWord mem state.activeWords state.tOff state.nOff =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
            (modulusBase + 32 * columns)) := by
        unfold compareNWord
        have hread := readWord_eq_memoryWordOf_covered mem
          (compareAw1 state.activeWords state.tOff) (comparePrev state.nOff)
          (by simpa [compareAw1] using htCoverage.1)
          (by simpa [compareAw1] using htCoverage.2) (by rw [hnPrev]; omega)
        simpa only [hnPrev] using hread
      let next := compareAdvance state
      have hnextCoverage := compareAdvance_coverage mem state hcovered hawFit
        (by rw [htPrev]; omega) (by rw [hnPrev]; omega)
      have hrest := ih next
        (by simpa [next, compareAdvance] using htPrev)
        (by simpa [next, compareAdvance] using hnPrev)
        (by omega) (by omega) (by omega) (by omega)
        hnextCoverage.1 hnextCoverage.2
      constructor
      · simp only [compareCandidateWords]
        rw [hrest.1, htWord, memoryWordsFrom_succ_eq_append]
      · simp only [compareModulusWords]
        rw [hrest.2, hnWord, memoryWordsFrom_succ_eq_append]

/- A successful comparison inspects a high suffix of the complete generated vectors. It stops
only at a differing word, or after consuming the complete vectors. -/
set_option maxRecDepth 10000 in
theorem selectedCIOSCompare_suffix_decomposition
    (columns : Nat) {fuel : Nat} {mem : ByteArray} {tP : UInt256}
    {state : CompareState} {prevTOff : UInt256} {selected : CIOSCompareSelection}
    (hcolumns : 0 < columns)
    (htOff : state.tOff.toNat = tP.toNat + 32 * columns)
    (hfit : tP.toNat + 32 * columns < UInt256.size)
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectCIOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    ∃ candidatePrefix modulusPrefix,
      compareCandidateWords mem columns state = candidatePrefix ++
          compareCandidateWords mem selected.iterations state ∧
      compareModulusWords mem columns state = modulusPrefix ++
          compareModulusWords mem selected.iterations state ∧
      candidatePrefix.length = modulusPrefix.length ∧
      (Modexp.wordLimbsToNat
            (compareCandidateWords mem selected.iterations state) ≠
          Modexp.wordLimbsToNat
            (compareModulusWords mem selected.iterations state) ∨
        (candidatePrefix = [] ∧ modulusPrefix = [])) := by
  induction columns generalizing fuel state prevTOff selected with
  | zero => omega
  | succ columns ih =>
      cases fuel with
      | zero => simp [selectCIOSCompare] at hselect
      | succ fuel =>
          simp only [selectCIOSCompare] at hselect
          let next := compareAdvance state
          have htLo : 32 ≤ state.tOff.toNat := by rw [htOff]; omega
          have hprevNat : prevTOff.toNat = tP.toNat + 32 * columns := by
            rw [hprev, comparePrev_toNat state.tOff htLo, htOff]
            omega
          by_cases hgreater :
              (compareNWord mem state.activeWords state.tOff state.nOff).toNat <
                (compareTWord mem state.activeWords state.tOff).toNat
          · rw [if_pos hgreater] at hselect
            injection hselect with heq
            subst selected
            refine ⟨compareCandidateWords mem columns next,
              compareModulusWords mem columns next, ?_, ?_, by simp, ?_⟩
            · rfl
            · rfl
            · left
              simp only [compareCandidateWords, compareModulusWords, List.nil_append]
              simp only [Modexp.wordLimbsToNat]
              omega
          · rw [if_neg hgreater] at hselect
            by_cases hless :
                (compareTWord mem state.activeWords state.tOff).toNat <
                  (compareNWord mem state.activeWords state.tOff state.nOff).toNat
            · rw [if_pos hless] at hselect
              injection hselect with heq
              subst selected
              refine ⟨compareCandidateWords mem columns next,
                compareModulusWords mem columns next, ?_, ?_, by simp, ?_⟩
              · rfl
              · rfl
              · left
                simp only [compareCandidateWords, compareModulusWords, List.nil_append]
                simp only [Modexp.wordLimbsToNat]
                omega
            · rw [if_neg hless] at hselect
              have hequal : compareTWord mem state.activeWords state.tOff =
                  compareNWord mem state.activeWords state.tOff state.nOff := by
                apply u256_inj
                omega
              by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
              · rw [if_pos hguard] at hselect
                have hcolumnsPos : 0 < columns := by
                  by_contra hzero
                  have hcolumnsZero : columns = 0 := by omega
                  subst columns
                  apply hguard
                  apply ugt_zero
                  have heqPrev : prevTOff.toNat = tP.toNat := by
                    simpa using hprevNat
                  omega
                cases hrest : selectCIOSCompare fuel mem tP next.activeWords next.tOff
                    next.nOff (comparePrev prevTOff) with
                | none =>
                    have hrest' : selectCIOSCompare fuel mem tP
                        (compareAw state.activeWords state.tOff state.nOff) prevTOff
                        (comparePrev state.nOff) (comparePrev prevTOff) = none := by
                      simpa [next, compareAdvance, hprev] using hrest
                    rw [hrest'] at hselect
                    contradiction
                | some rest =>
                    have hrest' : selectCIOSCompare fuel mem tP
                        (compareAw state.activeWords state.tOff state.nOff) prevTOff
                        (comparePrev state.nOff) (comparePrev prevTOff) = some rest := by
                      simpa [next, compareAdvance, hprev] using hrest
                    rw [hrest'] at hselect
                    injection hselect with heqSelection
                    subst selected
                    have hnextOff : next.tOff.toNat = tP.toNat + 32 * columns := by
                      change (comparePrev state.tOff).toNat =
                        tP.toNat + 32 * columns
                      rw [← hprev]
                      exact hprevNat
                    obtain ⟨candidatePrefix, modulusPrefix, hc, hm, hlen, hterminal⟩ :=
                      ih hcolumnsPos hnextOff (by omega)
                        (by simp [next, compareAdvance, hprev]) hrest
                    dsimp only [next] at hc hm hterminal ⊢
                    refine ⟨candidatePrefix, modulusPrefix, ?_, ?_, hlen, ?_⟩
                    · simp only [compareCandidateWords]
                      rw [hc]
                      simp [List.append_assoc]
                    · simp only [compareModulusWords]
                      rw [hm]
                      simp [List.append_assoc]
                    · rcases hterminal with hne | hempty
                      · left
                        simp only [compareCandidateWords, compareModulusWords]
                        rw [hequal]
                        simp only [Modexp.wordLimbsToNat_append,
                          compareCandidateWords_length, compareModulusWords_length]
                        omega
                      · exact Or.inr hempty
              · rw [if_neg hguard] at hselect
                have hcolumnsZero : columns = 0 := by
                  by_contra hpositive
                  apply hguard
                  apply ne_of_eq_of_ne (ugt_one (by rw [hprevNat]; omega))
                  native_decide
                subst columns
                injection hselect with heqSelection
                subst selected
                refine ⟨[], [], ?_, ?_, rfl, Or.inr ⟨rfl, rfl⟩⟩
                · simp [compareCandidateWords]
                · simp [compareModulusWords]

/-- The selected descending comparison decides the strict ordering of the complete candidate and
modulus memory vectors. -/
theorem selectedCIOSCompare_doSub_zero_iff_memoryWords
    (columns : Nat) {fuel : Nat} {mem : ByteArray} {tP : UInt256}
    {state : CompareState} {prevTOff : UInt256} {selected : CIOSCompareSelection}
    (candidateBase modulusBase : Nat)
    (hcolumns : 0 < columns)
    (htOff : state.tOff.toNat = candidateBase + 32 * columns)
    (hnOff : state.nOff.toNat = modulusBase + 32 * columns)
    (htBase : candidateBase = tP.toNat)
    (htFit : candidateBase + 32 * columns + 31 < UInt256.size)
    (hnFit : modulusBase + 32 * columns + 31 < UInt256.size)
    (htMem : candidateBase + 32 * columns ≤ mem.size)
    (hnMem : modulusBase + 32 * columns ≤ mem.size)
    (hcovered : MemoryCovered mem state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectCIOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    selected.doSub = ⟨0⟩ ↔
      limbsLtMSB (memoryWordsFrom mem candidateBase columns)
        (memoryWordsFrom mem modulusBase columns) := by
  have hfull := compareWords_eq_memoryWordsFrom columns mem state
    candidateBase modulusBase htOff hnOff htFit hnFit htMem hnMem hcovered hawFit
  obtain ⟨candidatePrefix, modulusPrefix, hc, hm, hlen, hterminal⟩ :=
    selectedCIOSCompare_suffix_decomposition columns hcolumns
      (by simpa [htBase] using htOff)
      (by rw [← htBase]; omega) hprev hselect
  apply selectedCIOSCompare_doSub_zero_iff_fullWords
    (memoryWordsFrom mem candidateBase columns)
    (memoryWordsFrom mem modulusBase columns)
    candidatePrefix modulusPrefix hprev hselect
  · rw [← hfull.1]
    exact hc
  · rw [← hfull.2]
    exact hm
  · exact hlen
  · exact hterminal

/-- A successful subtraction selector records repeated execution of the generated transition. -/
theorem selectCIOSSubtraction_final_eq_iterate
    {fuel : Nat} {stop : UInt256} {state : SubtractionState}
    {selected : CIOSSubtractionSelection}
    (hselect : selectCIOSSubtraction fuel stop state = some selected) :
    selected.final = subtractionIterate selected.iterations state := by
  induction fuel generalizing state selected with
  | zero => simp [selectCIOSSubtraction] at hselect
  | succ fuel ih =>
      simp only [selectCIOSSubtraction] at hselect
      let next := subtractionAdvance state
      by_cases hcontinue : next.leftPtr.lt stop ≠ ⟨0⟩
      · rw [if_pos hcontinue] at hselect
        cases hrest : selectCIOSSubtraction fuel stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            simpa only [next, subtractionIterate_advance] using
              ih (state := next) (selected := rest) hrest
      · rw [if_neg hcontinue] at hselect
        injection hselect with heq
        subst selected
        rfl

/-- On a nonwrapping word interval, a successful selector executes exactly every column. -/
theorem selectCIOSSubtraction_iterations_eq_geometry
    (columns : Nat) {fuel : Nat} {stop : UInt256} {state : SubtractionState}
    {selected : CIOSSubtractionSelection}
    (hcolumns : 0 < columns)
    (hselect : selectCIOSSubtraction fuel stop state = some selected)
    (hfit : state.leftPtr.toNat + 32 * columns < UInt256.size)
    (hstop : stop.toNat = state.leftPtr.toNat + 32 * columns) :
    selected.iterations = columns := by
  induction columns generalizing fuel state selected with
  | zero => omega
  | succ columns ih =>
      cases fuel with
      | zero => simp [selectCIOSSubtraction] at hselect
      | succ fuel =>
          simp only [selectCIOSSubtraction] at hselect
          let next := subtractionAdvance state
          have hstepFit : state.leftPtr.toNat + 32 < UInt256.size := by omega
          have hnextPtr : next.leftPtr.toNat = state.leftPtr.toNat + 32 := by
            simp [next, subtractionAdvance,
              uadd_word_lit32_toNat state.leftPtr hstepFit]
          cases columns with
          | zero =>
              have hexit : next.leftPtr.lt stop = ⟨0⟩ := by
                apply ult_zero
                rw [hnextPtr, hstop]
              rw [if_neg (by simpa [hexit])] at hselect
              injection hselect with heq
              subst selected
              rfl
          | succ columns =>
              have hcontinue : next.leftPtr.lt stop ≠ ⟨0⟩ := by
                apply ne_of_eq_of_ne (ult_one (by rw [hnextPtr, hstop]; omega))
                native_decide
              rw [if_pos hcontinue] at hselect
              cases hrest : selectCIOSSubtraction fuel stop next with
              | none => rw [hrest] at hselect; contradiction
              | some rest =>
                  rw [hrest] at hselect
                  injection hselect with heq
                  subst selected
                  have hrestCount := ih (state := next) (selected := rest)
                    (by omega) hrest (by rw [hnextPtr]; omega) (by
                      rw [hnextPtr, hstop]
                      omega)
                  change rest.iterations + 1 = columns + 1 + 1
                  omega

/-- Later sequential subtraction writes preserve an earlier complete output word. -/
theorem subtractionIterate_read_below
    (n : Nat) (state : SubtractionState) (read : Nat)
    (hwrites : ∀ j, j < n →
      let current := subtractionIterate j state
      current.leftPtr.toNat + 32 ≤ current.memory.size ∧
        read + 32 ≤ current.leftPtr.toNat) :
    (subtractionIterate n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := subtractionAdvance state
      have hfirst : state.leftPtr.toNat + 32 ≤ state.memory.size ∧
          read + 32 ≤ state.leftPtr.toNat := by
        simpa only [subtractionIterate] using hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          let current := subtractionIterate j next
          current.leftPtr.toNat + 32 ≤ current.memory.size ∧
            read + 32 ≤ current.leftPtr.toNat := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hwrites (j + 1) (by omega)
      have hrest := ih next htail
      rw [subtractionIterate, hrest]
      unfold next subtractionAdvance subtractionMemory
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirst.2

/-- The generated output collector is exactly the final memory range written by subtraction. -/
theorem subtractionOutputWords_eq_finalMemoryWords
    (n : Nat) (state : SubtractionState)
    (hfit : state.leftPtr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := subtractionIterate j state
      current.leftPtr.toNat + 32 ≤ current.memory.size) :
    subtractionOutputWords n state =
      memoryWordsFrom (subtractionIterate n state).memory state.leftPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := subtractionAdvance state
      have hstepFit : state.leftPtr.toNat + 32 < UInt256.size := by omega
      have hnextPtr : next.leftPtr.toNat = state.leftPtr.toNat + 32 := by
        simp [next, subtractionAdvance,
          uadd_word_lit32_toNat state.leftPtr hstepFit]
      have hnextWrites : ∀ j, j < n →
          let current := subtractionIterate j next
          current.leftPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, subtractionIterate_advance] using
          hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hnextPtr]; omega) hnextWrites
      have hfirstWrite : state.leftPtr.toNat + 32 ≤ state.memory.size := by
        simpa only [subtractionIterate] using hwrites 0 (by omega)
      have hgap : state.leftPtr.toNat - state.memory.size < USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        exact lt_usize 0 (by norm_num)
      have hstored :
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.leftPtr.toNat =
            (subtractionStep state.memory state.activeWords state.leftPtr
              state.rightPtr state.borrow).1.toNat := by
        exact subtractionMemory_word state.memory state.activeWords state.leftPtr
          state.rightPtr state.borrow hgap
      have hlater :
          (subtractionIterate n next).memory.readWithPadding state.leftPtr.toNat 32 =
            next.memory.readWithPadding state.leftPtr.toNat 32 := by
        apply subtractionIterate_read_below n next
        intro j hj
        have hwrite := hnextWrites j hj
        have hptr := subtractionIterate_leftPtr_toNat j next (by
          rw [hnextPtr]
          omega)
        constructor
        · exact hwrite
        · rw [hptr, hnextPtr]
          omega
      have hhead :
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              (subtractionIterate n next).memory state.leftPtr.toNat) =
            (subtractionStep state.memory state.activeWords state.leftPtr
              state.rightPtr state.borrow).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hlater]
        exact hstored
      simp only [subtractionOutputWords, subtractionIterate, memoryWordsFrom]
      rw [← hhead, htail, ← hnextPtr]

/-- A selected complete subtraction stores exactly the pure limbwise-subtraction result. -/
theorem selectedCIOSSubtraction_finalMemoryWords_eq_subLimbs
    (columns : Nat) {fuel : Nat} {stop : UInt256} (state : SubtractionState)
    (selected : CIOSSubtractionSelection)
    (hcolumns : 0 < columns)
    (hselect : selectCIOSSubtraction fuel stop state = some selected)
    (hfit : state.leftPtr.toNat + 32 * columns < UInt256.size)
    (hstop : stop.toNat = state.leftPtr.toNat + 32 * columns)
    (hwrites : ∀ j, j < columns →
      let current := subtractionIterate j state
      current.leftPtr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom selected.final.memory state.leftPtr.toNat columns =
      (Modexp.evmSubLimbs (subtractionLeftWords columns state)
        (subtractionRightWords columns state) state.borrow).1 := by
  have hcount := selectCIOSSubtraction_iterations_eq_geometry columns hcolumns
    hselect hfit hstop
  have hfinal := selectCIOSSubtraction_final_eq_iterate hselect
  rw [hcount] at hfinal
  have houtput := subtractionOutputWords_eq_finalMemoryWords columns state hfit hwrites
  have hcollectors := subtractionCollectors_eq_subLimbs columns state
  rw [hfinal, ← houtput]
  exact (congrArg Prod.fst hcollectors).symm

/-- The selected final copy either preserves the candidate or stores its exact limbwise
subtraction by the modulus. -/
theorem selectedCIOSCopy_memoryWords_eq
    (columns : Nat) {fuel : Nat} (mem : ByteArray)
    (aw source bytes doSub resultPtr nP resultBase : UInt256)
    (selected : CIOSCopySelection)
    (hcolumns : 0 < columns)
    (hbytes : bytes.toNat = 32 * columns)
    (hsource : source.toNat + 32 * columns ≤ mem.size)
    (hresult : resultPtr.toNat + 32 * columns ≤ mem.size)
    (hmodulus : nP.toNat + 32 * columns ≤ mem.size)
    (hdisjoint : nP.toNat + 32 * columns ≤ resultPtr.toNat)
    (hresultFit : resultPtr.toNat + 32 * columns + 31 < UInt256.size)
    (hmodulusFit : nP.toNat + 32 * columns + 31 < UInt256.size)
    (haccessFit : max resultPtr.toNat source.toNat + bytes.toNat + 31 < UInt256.size)
    (hstop : (⟨32⟩ + (bytes + resultBase)).toNat =
      resultPtr.toNat + 32 * columns)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectCIOSCopy fuel mem aw source bytes doSub resultPtr nP
      resultBase = some selected) :
    memoryWordsFrom selected.memory resultPtr.toNat columns =
      if doSub = ⟨0⟩ then
        memoryWordsFrom mem source.toNat columns
      else
        (Modexp.evmSubLimbs (memoryWordsFrom mem source.toNat columns)
          (memoryWordsFrom mem nP.toNat columns) ⟨0⟩).1 := by
  let copied := finalCopyMemory mem source resultPtr bytes
  let copiedAw := finalCopyAw aw source resultPtr bytes
  let stop := ⟨32⟩ + (bytes + resultBase)
  unfold selectCIOSCopy at hselect
  dsimp only at hselect
  by_cases hdoSub : doSub = ⟨0⟩
  · rw [if_pos hdoSub] at hselect ⊢
    injection hselect with heq
    subst selected
    exact finalCopyMemory_words_eq_source columns mem source resultPtr bytes
      hcolumns hbytes hsource (by omega)
  · rw [if_neg hdoSub] at hselect ⊢
    have hnonempty : resultPtr.lt stop ≠ ⟨0⟩ := by
      apply ne_of_eq_of_ne (ult_one (by
        change resultPtr.toNat < stop.toNat
        rw [hstop]
        omega))
      native_decide
    rw [if_neg hnonempty] at hselect
    let initial := finalSubtractionInitialState copied copiedAw resultPtr nP
    cases hsub : selectCIOSSubtraction fuel stop initial with
    | none => rw [hsub] at hselect; contradiction
    | some sub =>
        rw [hsub] at hselect
        injection hselect with heq
        subst selected
        have hbytesNe : bytes.toNat ≠ 0 := by rw [hbytes]; omega
        have hsourceBytes : source.toNat + bytes.toNat ≤ mem.size := by
          rw [hbytes]
          exact hsource
        have hresultBytes : resultPtr.toNat + bytes.toNat ≤ mem.size := by
          rw [hbytes]
          exact hresult
        have hcopiedSize := finalCopyMemory_size mem source resultPtr bytes
          hbytesNe hsourceBytes hresultBytes
        have hcopiedCoverage := finalCopy_coverage mem aw source resultPtr bytes
          hbytesNe hsourceBytes hresultBytes hcovered hawFit haccessFit
        have hsafety : ∀ j, j ≤ columns →
            (subtractionIterate j initial).memory.size = initial.memory.size ∧
              MemoryCovered (subtractionIterate j initial).memory
                (subtractionIterate j initial).activeWords ∧
              (subtractionIterate j initial).activeWords.toNat * 32 < UInt256.size := by
          intro j hj
          apply subtractionIterate_coverage_size j initial
          · simpa [initial, finalSubtractionInitialState] using
              (show resultPtr.toNat + 32 * j + 31 < UInt256.size by omega)
          · simpa [initial, finalSubtractionInitialState] using
              (show nP.toNat + 32 * j + 31 < UInt256.size by omega)
          · simpa [initial, finalSubtractionInitialState, copied, hcopiedSize] using
              (show resultPtr.toNat + 32 * j ≤ mem.size by omega)
          · simpa [initial, finalSubtractionInitialState, copied, hcopiedSize] using
              (show nP.toNat + 32 * j ≤ mem.size by omega)
          · simpa [initial, finalSubtractionInitialState, copied, copiedAw] using
              hcopiedCoverage.1
          · simpa [initial, finalSubtractionInitialState, copied, copiedAw] using
              hcopiedCoverage.2
        have hcoveredEach : ∀ j, j < columns →
            let current := subtractionIterate j initial
            MemoryCovered current.memory current.activeWords := by
          intro j hj
          exact (hsafety j (by omega)).2.1
        have hawFitEach : ∀ j, j < columns →
            let current := subtractionIterate j initial
            current.activeWords.toNat * 32 < UInt256.size := by
          intro j hj
          exact (hsafety j (by omega)).2.2
        have hwordsEach : ∀ j, j < columns →
            let current := subtractionIterate j initial
            current.leftPtr.toNat + 32 ≤ current.memory.size ∧
              current.rightPtr.toNat + 32 ≤ current.memory.size := by
          intro j hj
          have hleftPtr := subtractionIterate_leftPtr_toNat j initial (by
            simpa [initial, finalSubtractionInitialState] using
              (show resultPtr.toNat + 32 * j < UInt256.size by omega))
          have hrightPtr := subtractionIterate_rightPtr_toNat j initial (by
            simpa [initial, finalSubtractionInitialState] using
              (show nP.toNat + 32 * j < UInt256.size by omega))
          have hsize := (hsafety j (by omega)).1
          simp only
          rw [hleftPtr, hrightPtr, hsize]
          simpa [initial, finalSubtractionInitialState, copied, hcopiedSize] using
            (show resultPtr.toNat + 32 * j + 32 ≤ mem.size ∧
              nP.toNat + 32 * j + 32 ≤ mem.size by omega)
        have hleft := subtractionLeftWords_eq_initialMemoryWords columns initial
          (by simpa [initial, finalSubtractionInitialState] using hresultFit)
          hcoveredEach hawFitEach (fun j hj => (hwordsEach j hj).1)
        have hright := subtractionRightWords_eq_initialMemoryWords columns initial
          (by simpa [initial, finalSubtractionInitialState] using hresultFit)
          (by simpa [initial, finalSubtractionInitialState] using hmodulusFit)
          (by simpa [initial, finalSubtractionInitialState] using hdisjoint)
          hcoveredEach hawFitEach hwordsEach
        have hsubOutput := selectedCIOSSubtraction_finalMemoryWords_eq_subLimbs
          columns initial sub hcolumns hsub
          (by simpa [initial, finalSubtractionInitialState] using
            (show resultPtr.toNat + 32 * columns < UInt256.size by omega))
          (by simpa [initial, finalSubtractionInitialState, stop] using hstop)
          (fun j hj => (hwordsEach j hj).1)
        have hcopyWords := finalCopyMemory_words_eq_source columns mem source
          resultPtr bytes hcolumns hbytes hsource (by omega)
        have hmodulusWords := memoryWordsFrom_finalCopy_below columns mem source
          resultPtr bytes nP.toNat hbytesNe hsourceBytes (by omega) hmodulus hdisjoint
        rw [hleft, hright] at hsubOutput
        simp only [initial, finalSubtractionInitialState] at hsubOutput
        rw [hcopyWords, hmodulusWords] at hsubOutput
        exact hsubOutput

end Modexp.MultiLimbMontgomeryCIOSSemantic
