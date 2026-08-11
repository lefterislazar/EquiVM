import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSOperandLinks

/-! # CIOS scratch-zero semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Reading back a generated zero store is exact even when the store extends memory. -/
theorem memoryWordNat_zeroStore_eq
    (mem : ByteArray) (off : Nat) (hgap : off - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        ((⟨0⟩ : UInt256).toByteArray.write 0 mem off 32) off = 0 := by
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  simpa using fromByteArrayBigEndian_toByteArray (⟨0⟩ : UInt256)

/-- Later sequential zero stores preserve every complete range below the current zero pointer. -/
theorem ciosZeroIterate_memoryWords_below
    (n : Nat) (state : CIOSZeroState) (ptr count : Nat)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hmemory : state.ptr.toNat ≤ state.memory.size)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat) :
    memoryWordsFrom (ciosZeroIterate n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := ciosZeroAdvance state
      have hstepPtr : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, ciosZeroAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hstepSize : next.memory.size = max state.memory.size (state.ptr.toNat + 32) := by
        dsimp only [next, ciosZeroAdvance, ciosZeroMemory]
        exact toByteArray_write_size_eq_max (⟨0⟩ : UInt256) state.memory
          state.ptr.toNat (by
            rw [Nat.sub_eq_zero_of_le hmemory]
            exact lt_usize 0 (by norm_num))
      have hnextMemory : next.ptr.toNat ≤ next.memory.size := by
        rw [hstepPtr, hstepSize]
        exact Nat.le_max_right _ _
      have htail := ih next (by rw [hstepPtr]; omega) hnextMemory
        (by rw [hstepPtr]; omega)
      have hfirst := memoryWordsFrom_write_above (⟨0⟩ : UInt256).toByteArray
        state.memory state.ptr.toNat ptr count (by rw [toByteArray_size]) hmemory hbelow
      have hfirst' : memoryWordsFrom next.memory ptr count =
          memoryWordsFrom state.memory ptr count := by
        simpa only [next, ciosZeroAdvance, ciosZeroMemory] using hfirst
      calc
        memoryWordsFrom (ciosZeroIterate (n + 1) state).memory ptr count =
            memoryWordsFrom (ciosZeroIterate n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := hfirst'

/-- The sequential zero loop leaves exactly `n` zero words at its initial pointer. -/
theorem ciosZeroIterate_words_zero
    (n : Nat) (state : CIOSZeroState)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hmemory : state.memory.size ≤ state.ptr.toNat)
    (hgap : state.ptr.toNat - state.memory.size < USize.size) :
    memoryWordsFrom (ciosZeroIterate n state).memory state.ptr.toNat n =
      List.replicate n (⟨0⟩ : UInt256) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := ciosZeroAdvance state
      have hstepPtr : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, ciosZeroAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hstepSize : next.memory.size = state.ptr.toNat + 32 := by
        dsimp only [next, ciosZeroAdvance, ciosZeroMemory]
        rw [toByteArray_write_size_eq_max (⟨0⟩ : UInt256) state.memory
          state.ptr.toNat hgap]
        exact max_eq_right (by omega)
      have hnextMemory : next.memory.size ≤ next.ptr.toNat := by
        rw [hstepSize, hstepPtr]
      have hnextGap : next.ptr.toNat - next.memory.size < USize.size := by
        rw [hstepPtr, hstepSize, Nat.sub_self]
        exact lt_usize 0 (by norm_num)
      have htail := ih next (by rw [hstepPtr]; omega) hnextMemory hnextGap
      have hheadFrame := ciosZeroIterate_memoryWords_below n next state.ptr.toNat 1
        (by rw [hstepPtr]; omega) (by rw [hstepPtr, hstepSize]) (by rw [hstepPtr])
      have hhead : Modexp.MultiLimbMemoryModel.memoryWordNat
          (ciosZeroIterate n next).memory state.ptr.toNat = 0 := by
        have hframeWord : Modexp.MultiLimbMemoryModel.memoryWordNat
            (ciosZeroIterate n next).memory state.ptr.toNat =
              Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.ptr.toNat := by
          apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
          exact hheadFrame
        rw [hframeWord]
        simpa only [next, ciosZeroAdvance, ciosZeroMemory] using
          memoryWordNat_zeroStore_eq state.memory state.ptr.toNat hgap
      change UInt256.ofNat
          (Modexp.MultiLimbMemoryModel.memoryWordNat
            (ciosZeroIterate n next).memory state.ptr.toNat) ::
          memoryWordsFrom (ciosZeroIterate n next).memory (state.ptr.toNat + 32) n =
        (⟨0⟩ : UInt256) :: List.replicate n (⟨0⟩ : UInt256)
      rw [hhead]
      have hzeroWord : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl
      rw [hzeroWord]
      rw [← hstepPtr]
      rw [htail]

@[simp] theorem memoryWordsFrom_length (mem : ByteArray) (ptr n : Nat) :
    (memoryWordsFrom mem ptr n).length = n := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih => simp only [memoryWordsFrom, List.length_cons, ih]

/-- The canonical scratch natural is the radix interpretation of its contiguous `columns + 2`
word range. -/
theorem ciosScratchValue_eq_fullMemoryWords
    (columns : Nat) (tP tEnd tk1Off : UInt256) (state : CIOSOuterState)
    (htEnd : tEnd.toNat = tP.toNat + 32 * columns)
    (htk1 : tk1Off.toNat = tEnd.toNat + 32) :
    ciosScratchValue columns tP tEnd tk1Off state =
      Modexp.wordLimbsToNat
        (memoryWordsFrom state.memory tP.toNat (columns + 2)) := by
  unfold ciosScratchValue
  have hfirst := memoryWordsFrom_succ_eq_append state.memory tP.toNat columns
  have hsecond := memoryWordsFrom_succ_eq_append state.memory tP.toNat (columns + 1)
  rw [show columns + 2 = (columns + 1) + 1 by omega, hsecond, hfirst]
  rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append]
  simp only [memoryWordsFrom_length, List.length_append, List.length_singleton,
    Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
  rw [UInt256.toNat_ofNat_of_lt
    (memoryWordNat_lt_size state.memory (tP.toNat + 32 * columns))]
  rw [UInt256.toNat_ofNat_of_lt
    (memoryWordNat_lt_size state.memory (tP.toNat + 32 * (columns + 1)))]
  have hextraOff : tP.toNat + 32 * (columns + 1) = tk1Off.toNat := by
    rw [htk1, htEnd]
    omega
  rw [← htEnd, hextraOff]

/-- Zeroing the complete scratch range initializes the canonical CIOS accumulator to zero. -/
theorem ciosScratchValue_eq_zero_of_words_zero
    (columns : Nat) (tP tEnd tk1Off : UInt256) (state : CIOSOuterState)
    (htEnd : tEnd.toNat = tP.toNat + 32 * columns)
    (htk1 : tk1Off.toNat = tEnd.toNat + 32)
    (hzero : memoryWordsFrom state.memory tP.toNat (columns + 2) =
      List.replicate (columns + 2) (⟨0⟩ : UInt256)) :
    ciosScratchValue columns tP tEnd tk1Off state = 0 := by
  rw [ciosScratchValue_eq_fullMemoryWords columns tP tEnd tk1Off state htEnd htk1,
    hzero]
  exact Modexp.wordLimbsToNat_replicate_zero (columns + 2)

/-- A selected zero loop with the setup geometry initializes the later outer state's complete
scratch accumulator to zero. -/
theorem selectedCIOSZeroLoop_scratchValue_zero
    (columns : Nat) {fuel : Nat} {stop tP tEnd tk1Off : UInt256}
    (zeroState : CIOSZeroState) (selected : CIOSZeroSelection)
    (aOff : UInt256)
    (hselect : selectCIOSZeroLoop fuel stop zeroState = some selected)
    (hptr : zeroState.ptr = tP)
    (htEnd : tEnd.toNat = tP.toNat + 32 * columns)
    (htk1 : tk1Off.toNat = tEnd.toNat + 32)
    (hstop : stop.toNat = tP.toNat + 32 * (columns + 2))
    (hfit : tP.toNat + 32 * (columns + 2) < UInt256.size)
    (hmemory : zeroState.memory.size ≤ tP.toNat)
    (hgap : tP.toNat - zeroState.memory.size < USize.size) :
    ciosScratchValue columns tP tEnd tk1Off
        { aOff := aOff
          memory := selected.final.memory
          activeWords := selected.final.activeWords } = 0 := by
  have hcount := selectCIOSZeroLoop_iterations_eq_geometry (columns + 2) hselect
    (by simpa only [hptr] using hfit) (by simpa only [hptr] using hstop)
  have hfinal := selectCIOSZeroLoop_final_eq_iterate hselect
  have hzero := ciosZeroIterate_words_zero (columns + 2) zeroState
    (by simpa only [hptr] using hfit)
    (by simpa only [hptr] using hmemory)
    (by simpa only [hptr] using hgap)
  rw [hcount] at hfinal
  rw [← hfinal] at hzero
  apply ciosScratchValue_eq_zero_of_words_zero columns tP tEnd tk1Off
    { aOff := aOff
      memory := selected.final.memory
      activeWords := selected.final.activeWords }
    htEnd htk1
  simpa only [hptr] using hzero

end Modexp.MultiLimbMontgomeryCIOSSemantic
