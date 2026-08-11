import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSSemantic
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSOperandLinks

/-! # SOS collector-to-memory links

The off-diagonal and reduction column loops use the same memory transition as the generated
CIOS multiply pass.  These lemmas reuse its framing results while retaining the SOS state types
used by the exact execution selectors.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A consecutive memory-word window splits at an arbitrary limb boundary. -/
theorem memoryWordsFrom_add
    (mem : ByteArray) (ptr left right : Nat) :
    memoryWordsFrom mem ptr (left + right) =
      memoryWordsFrom mem ptr left ++
        memoryWordsFrom mem (ptr + 32 * left) right := by
  induction left generalizing ptr with
  | zero => simp [memoryWordsFrom]
  | succ left ih =>
      rw [show left + 1 + right = (left + right) + 1 by omega]
      simp only [memoryWordsFrom, List.cons_append]
      rw [ih]
      rw [show ptr + 32 + 32 * left = ptr + 32 * (left + 1) by omega]

def sosOffDiagonalMultiplyState (state : SOSOffDiagonalState) : MultiplyPassState where
  operandPtr := state.operandPtr
  resultPtr := state.resultPtr
  carry := state.carry
  memory := state.memory
  activeWords := state.activeWords

@[simp] theorem sosOffDiagonalMultiplyState_advance
    (a : UInt256) (state : SOSOffDiagonalState) :
    sosOffDiagonalMultiplyState (sosOffDiagonalAdvance a state) =
      multiplyPassAdvance a (sosOffDiagonalMultiplyState state) := by
  rfl

@[simp] theorem sosOffDiagonalMultiplyState_iterate
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    sosOffDiagonalMultiplyState (sosOffDiagonalIterate a n state) =
      multiplyPassIterate a n (sosOffDiagonalMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosOffDiagonalIterate, multiplyPassIterate]
      rw [ih, sosOffDiagonalMultiplyState_advance]

theorem sosOffDiagonalOperandWords_eq_multiplyPass
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    sosOffDiagonalOperandWords a n state =
      multiplyPassOperandWords a n (sosOffDiagonalMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosOffDiagonalOperandWords, multiplyPassOperandWords]
      rw [ih, sosOffDiagonalMultiplyState_advance]
      rfl

theorem sosOffDiagonalPriorWords_eq_multiplyPass
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    sosOffDiagonalPriorWords a n state =
      multiplyPassPriorWords a n (sosOffDiagonalMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosOffDiagonalPriorWords, multiplyPassPriorWords]
      rw [ih, sosOffDiagonalMultiplyState_advance]
      rfl

theorem sosOffDiagonalOutputWords_eq_multiplyPass
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    sosOffDiagonalOutputWords a n state =
      multiplyPassOutputWords a n (sosOffDiagonalMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosOffDiagonalOutputWords, multiplyPassOutputWords]
      rw [ih, sosOffDiagonalMultiplyState_advance]
      rfl

@[simp] theorem sosOffDiagonalOutputWords_length
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) :
    (sosOffDiagonalOutputWords a n state).length = n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih => simp [sosOffDiagonalOutputWords, ih]

theorem sosOffDiagonalIterate_resultPtr_toNat
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState)
    (hfit : state.resultPtr.toNat + 32 * n < UInt256.size) :
    (sosOffDiagonalIterate a n state).resultPtr.toNat =
      state.resultPtr.toNat + 32 * n := by
  have h := multiplyPassIterate_resultPtr_toNat a n
    (sosOffDiagonalMultiplyState state) hfit
  simpa only [← sosOffDiagonalMultiplyState_iterate] using h

/-- The off-diagonal operand collector is the original contiguous operand suffix. -/
theorem sosOffDiagonalOperandWords_eq_initialMemory
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState)
    (hoperandFit : state.operandPtr.toNat + 32 * n < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hseparate : state.operandPtr.toNat + 32 * n ≤ state.resultPtr.toNat)
    (hloads : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    sosOffDiagonalOperandWords a n state =
      memoryWordsFrom state.memory state.operandPtr.toNat n := by
  rw [sosOffDiagonalOperandWords_eq_multiplyPass]
  apply multiplyPassOperandWords_eq_initialMemory a n (sosOffDiagonalMultiplyState state)
    hoperandFit hresultFit hseparate
  · intro j hj
    simpa only [← sosOffDiagonalMultiplyState_iterate] using hloads j hj
  · intro j hj
    simpa only [← sosOffDiagonalMultiplyState_iterate] using hwrites j hj

/-- The words accumulated by an off-diagonal row are exactly its initial scratch window. -/
theorem sosOffDiagonalPriorWords_eq_initialMemory
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hloads : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    sosOffDiagonalPriorWords a n state =
      memoryWordsFrom state.memory state.resultPtr.toNat n := by
  rw [sosOffDiagonalPriorWords_eq_multiplyPass]
  apply multiplyPassPriorWords_eq_memoryWordsFrom a n (sosOffDiagonalMultiplyState state)
    hresultFit
  · intro j hj
    simpa only [← sosOffDiagonalMultiplyState_iterate] using hloads j hj
  · intro j hj
    simpa only [← sosOffDiagonalMultiplyState_iterate] using hwrites j hj

/-- The completed off-diagonal collector is exactly the final contiguous scratch window. -/
theorem sosOffDiagonalOutputWords_eq_finalMemory
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    sosOffDiagonalOutputWords a n state =
      memoryWordsFrom (sosOffDiagonalIterate a n state).memory state.resultPtr.toNat n := by
  rw [sosOffDiagonalOutputWords_eq_multiplyPass]
  have h := multiplyPassOutputWords_eq_finalMemory a n
    (sosOffDiagonalMultiplyState state) hresultFit (by
      intro j hj
      simpa only [← sosOffDiagonalMultiplyState_iterate] using hwrites j hj)
  simpa only [← sosOffDiagonalMultiplyState_iterate] using h

/-- An off-diagonal multiply pass preserves every complete consecutive range below its first
scratch destination. -/
theorem sosOffDiagonalIterate_memoryWords_below
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) (ptr count : Nat)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.resultPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (sosOffDiagonalIterate a n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  have h := multiplyPassIterate_memoryWords_below a n
    (sosOffDiagonalMultiplyState state) ptr count hresultFit hbelow (by
      intro j hj
      simpa only [← sosOffDiagonalMultiplyState_iterate] using hwrites j hj)
  simpa only [← sosOffDiagonalMultiplyState_iterate] using h

/-- The same pass preserves every complete consecutive range above its final destination. -/
theorem sosOffDiagonalIterate_memoryWords_above
    (a : UInt256) (n : Nat) (state : SOSOffDiagonalState) (ptr count : Nat)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (habove : state.resultPtr.toNat + 32 * n ≤ ptr)
    (hwrites : ∀ j, j < n →
      let current := sosOffDiagonalIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (sosOffDiagonalIterate a n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      have hread := multiplyPassIterate_read_above a n
        (sosOffDiagonalMultiplyState state) ptr (by
          intro j hj
          have hptr := multiplyPassIterate_resultPtr_toNat a j
            (sosOffDiagonalMultiplyState state) (by
              simpa [sosOffDiagonalMultiplyState] using
                (show state.resultPtr.toNat + 32 * j < UInt256.size by omega))
          refine ⟨?_, ?_⟩
          · simpa only [← sosOffDiagonalMultiplyState_iterate] using hwrites j hj
          · rw [hptr]
            change state.resultPtr.toNat + 32 * j + 32 ≤ ptr
            omega)
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (sosOffDiagonalIterate a n state).memory ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat state.memory ptr := by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        exact congrArg fromByteArrayBigEndian (by
          simpa only [← sosOffDiagonalMultiplyState_iterate] using hread)
      simp only [memoryWordsFrom]
      rw [hword, ih (ptr := ptr + 32) (by omega)]

/-- A word write that starts in concrete memory preserves all padded word reads above the written
word, including the case where the write extends memory by up to 32 bytes. -/
theorem memoryWordsFrom_wordWrite_below_extending
    (word : UInt256) (base : ByteArray) (dest ptr count : Nat)
    (hdest : dest ≤ base.size) (hbelow : dest + 32 ≤ ptr) :
    memoryWordsFrom (word.toByteArray.write 0 base dest 32) ptr count =
      memoryWordsFrom base ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      have hread :
          (word.toByteArray.write 0 base dest 32).readWithPadding ptr 32 =
            base.readWithPadding ptr 32 := by
        by_cases hin : dest + 32 ≤ base.size
        · exact write32_read_above_padded word.toByteArray base dest ptr
            (by rw [toByteArray_size]) hin hbelow
        · have hgap : dest - base.size < USize.size := by
            rw [Nat.sub_eq_zero_of_le hdest]
            exact lt_usize 0 (by norm_num)
          have hsize := toByteArray_write_size_eq_max word base dest hgap
          rw [readWithPadding_past_end base ptr 32 (by omega) (by decide)]
          rw [readWithPadding_past_end (word.toByteArray.write 0 base dest 32) ptr 32
            (by rw [hsize]; omega) (by decide)]
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (word.toByteArray.write 0 base dest 32) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat base ptr := by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hread]
      simp only [memoryWordsFrom]
      rw [hword, ih (ptr := ptr + 32) (by omega)]

def sosReductionMultiplyState (state : SOSReductionState) : MultiplyPassState where
  operandPtr := state.modulusPtr
  resultPtr := state.resultPtr
  carry := state.carry
  memory := state.memory
  activeWords := state.activeWords

@[simp] theorem sosReductionMultiplyState_advance
    (factor : UInt256) (state : SOSReductionState) :
    sosReductionMultiplyState (sosReductionAdvance factor state) =
      multiplyPassAdvance factor (sosReductionMultiplyState state) := by
  rfl

@[simp] theorem sosReductionMultiplyState_iterate
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    sosReductionMultiplyState (sosReductionIterate factor n state) =
      multiplyPassIterate factor n (sosReductionMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosReductionIterate, multiplyPassIterate]
      rw [ih, sosReductionMultiplyState_advance]

theorem sosReductionModulusWords_eq_multiplyPass
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    sosReductionModulusWords factor n state =
      multiplyPassOperandWords factor n (sosReductionMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosReductionModulusWords, multiplyPassOperandWords]
      rw [ih, sosReductionMultiplyState_advance]
      rfl

theorem sosReductionPriorWords_eq_multiplyPass
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    sosReductionPriorWords factor n state =
      multiplyPassPriorWords factor n (sosReductionMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosReductionPriorWords, multiplyPassPriorWords]
      rw [ih, sosReductionMultiplyState_advance]
      rfl

theorem sosReductionOutputWords_eq_multiplyPass
    (factor : UInt256) (n : Nat) (state : SOSReductionState) :
    sosReductionOutputWords factor n state =
      multiplyPassOutputWords factor n (sosReductionMultiplyState state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [sosReductionOutputWords, multiplyPassOutputWords]
      rw [ih, sosReductionMultiplyState_advance]
      rfl

/-- A reduction pass reads the original contiguous modulus suffix. -/
theorem sosReductionModulusWords_eq_initialMemory
    (factor : UInt256) (n : Nat) (state : SOSReductionState)
    (hoperandFit : state.modulusPtr.toNat + 32 * n < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hseparate : state.modulusPtr.toNat + 32 * n ≤ state.resultPtr.toNat)
    (hloads : ∀ j, j < n →
      let current := sosReductionIterate factor j state
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.modulusPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosReductionIterate factor j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    sosReductionModulusWords factor n state =
      memoryWordsFrom state.memory state.modulusPtr.toNat n := by
  rw [sosReductionModulusWords_eq_multiplyPass]
  apply multiplyPassOperandWords_eq_initialMemory factor n (sosReductionMultiplyState state)
    hoperandFit hresultFit hseparate
  · intro j hj
    simpa only [← sosReductionMultiplyState_iterate] using hloads j hj
  · intro j hj
    simpa only [← sosReductionMultiplyState_iterate] using hwrites j hj

/-- Reduction prior words are the scratch suffix present before that pass. -/
theorem sosReductionPriorWords_eq_initialMemory
    (factor : UInt256) (n : Nat) (state : SOSReductionState)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hloads : ∀ j, j < n →
      let current := sosReductionIterate factor j state
      (schoolbookOperands current.memory current.activeWords current.modulusPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosReductionIterate factor j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    sosReductionPriorWords factor n state =
      memoryWordsFrom state.memory state.resultPtr.toNat n := by
  rw [sosReductionPriorWords_eq_multiplyPass]
  apply multiplyPassPriorWords_eq_memoryWordsFrom factor n (sosReductionMultiplyState state)
    hresultFit
  · intro j hj
    simpa only [← sosReductionMultiplyState_iterate] using hloads j hj
  · intro j hj
    simpa only [← sosReductionMultiplyState_iterate] using hwrites j hj

/-- Reduction outputs are the final contiguous scratch suffix. -/
theorem sosReductionOutputWords_eq_finalMemory
    (factor : UInt256) (n : Nat) (state : SOSReductionState)
    (hresultFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := sosReductionIterate factor j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    sosReductionOutputWords factor n state =
      memoryWordsFrom (sosReductionIterate factor n state).memory state.resultPtr.toNat n := by
  rw [sosReductionOutputWords_eq_multiplyPass]
  have h := multiplyPassOutputWords_eq_finalMemory factor n
    (sosReductionMultiplyState state) hresultFit (by
      intro j hj
      simpa only [← sosReductionMultiplyState_iterate] using hwrites j hj)
  simpa only [← sosReductionMultiplyState_iterate] using h

/-! ## Doubling memory windows -/

theorem sosDoubleMemory_word
    (mem : ByteArray) (aw ptr carry : UInt256)
    (hgap : ptr.toNat - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (sosDoubleMemory mem aw ptr carry) ptr.toNat =
      (sosDoubleOutput mem aw ptr carry).toNat := by
  unfold sosDoubleMemory Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

theorem sosDoubleIterate_ptr_toNat
    (n : Nat) (state : SOSDoubleState)
    (hfit : state.ptr.toNat + 32 * n < UInt256.size) :
    (sosDoubleIterate n state).ptr.toNat = state.ptr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosDoubleAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosDoubleAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      change (sosDoubleIterate n next).ptr.toNat = _
      rw [ih next (by rw [hstep]; omega), hstep]
      omega

/-- Later doubling stores preserve every complete word below their destinations. -/
theorem sosDoubleIterate_read_below
    (n : Nat) (state : SOSDoubleState) (read : Nat)
    (hwrites : ∀ j, j < n →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size ∧
        read + 32 ≤ current.ptr.toNat) :
    (sosDoubleIterate n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosDoubleAdvance state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          let current := sosDoubleIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size ∧
            read + 32 ≤ current.ptr.toNat := by
        intro j hj
        simpa only [next, sosDoubleIterate_advance] using hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosDoubleIterate] using hfirst.1
      have hfirstBelow : read + 32 ≤ state.ptr.toNat := by
        simpa only [sosDoubleIterate] using hfirst.2
      rw [sosDoubleIterate, hrest]
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirstBelow

/-- Doubling reads exactly the initial contiguous scratch window. -/
theorem sosDoubleInputWords_eq_initialMemory
    (n : Nat) (state : SOSDoubleState)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hloads : ∀ j, j < n →
      let current := sosDoubleIterate j state
      (sosDoubleWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    sosDoubleInputWords n state = memoryWordsFrom state.memory state.ptr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosDoubleAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosDoubleAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have htailLoads : ∀ j, j < n →
          let current := sosDoubleIterate j next
          (sosDoubleWord current.memory current.activeWords current.ptr).toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
        intro j hj
        simpa only [next, sosDoubleIterate_advance] using hloads (j + 1) (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosDoubleIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosDoubleIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) htailLoads htailWrites
      have hheadNat := hloads 0 (by omega)
      have hhead : sosDoubleWord state.memory state.activeWords state.ptr =
          UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.ptr.toNat) := by
        apply u256_inj
        rw [show (sosDoubleIterate 0 state) = state by rfl] at hheadNat
        rw [hheadNat, UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosDoubleIterate] using hwrites 0 (by omega)
      have hframeRaw := memoryWordsFrom_write_below
        (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toByteArray
        state.memory state.ptr.toNat next.ptr.toNat n
        (by rw [toByteArray_size]) hfirstWrite (by rw [hstep])
      have hframe : memoryWordsFrom next.memory next.ptr.toNat n =
          memoryWordsFrom state.memory next.ptr.toNat n := by
        simpa only [next, sosDoubleAdvance, sosDoubleMemory] using hframeRaw
      simp only [sosDoubleInputWords, memoryWordsFrom]
      change sosDoubleWord state.memory state.activeWords state.ptr ::
          sosDoubleInputWords n next =
        UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.ptr.toNat) ::
          memoryWordsFrom state.memory (state.ptr.toNat + 32) n
      rw [hhead, htail, hframe, hstep]

/-- A completed doubling pass leaves its collector outputs in the final scratch window. -/
theorem sosDoubleOutputWords_eq_finalMemory
    (n : Nat) (state : SOSDoubleState)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := sosDoubleIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    sosDoubleOutputWords n state =
      memoryWordsFrom (sosDoubleIterate n state).memory state.ptr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosDoubleAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosDoubleAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosDoubleIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosDoubleIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) htailWrites
      have hlater :
          (sosDoubleIterate n next).memory.readWithPadding state.ptr.toNat 32 =
            next.memory.readWithPadding state.ptr.toNat 32 := by
        apply sosDoubleIterate_read_below
        intro j hj
        have hwrite := htailWrites j hj
        have hcurrentPtr := sosDoubleIterate_ptr_toNat j next (by rw [hstep]; omega)
        exact ⟨hwrite, by rw [hcurrentPtr, hstep]; omega⟩
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosDoubleIterate] using hwrites 0 (by omega)
      have hstored :
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.ptr.toNat =
            (sosDoubleOutput state.memory state.activeWords state.ptr state.carry).toNat := by
        apply sosDoubleMemory_word
        simp [Nat.sub_eq_zero_of_le (by omega : state.ptr.toNat ≤ state.memory.size),
          USize.size]
      have hhead : UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat
              (sosDoubleIterate n next).memory state.ptr.toNat) =
          sosDoubleOutput state.memory state.activeWords state.ptr state.carry := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat at hlater hstored ⊢
        rw [hlater]
        exact hstored
      simp only [sosDoubleOutputWords, sosDoubleIterate, memoryWordsFrom]
      change sosDoubleOutput state.memory state.activeWords state.ptr state.carry ::
          sosDoubleOutputWords n next =
        UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat
              (sosDoubleIterate n next).memory state.ptr.toNat) ::
          memoryWordsFrom (sosDoubleIterate n next).memory (state.ptr.toNat + 32) n
      rw [← hhead, htail, ← hstep]

end Modexp.MultiLimbMontgomerySOSSemantic
