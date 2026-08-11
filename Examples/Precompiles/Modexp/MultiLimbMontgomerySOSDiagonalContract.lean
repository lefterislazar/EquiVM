import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSOffDiagonalLoopContract

/-! # SOS diagonal addition and carry propagation semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem selectedSOSPropagation_final_eq_iterate
    {fuel : Nat} {state : SOSPropagateState} {selected : SOSPropagateSelection}
    (hselect : selectSOSPropagation fuel state = some selected) :
    selected.final = sosPropagateIterate selected.words state := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSPropagation] at hselect
  | succ fuel ih =>
      simp only [selectSOSPropagation] at hselect
      let next := sosPropagateAdvance state
      by_cases hzero : next.carry = ⟨0⟩
      · rw [if_pos hzero] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hzero] at hselect
        cases hrest : selectSOSPropagation fuel next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            simpa only [sosPropagateIterate, next] using ih hrest

theorem sosPropagateIterate_ptr_toNat
    (n : Nat) (state : SOSPropagateState)
    (hfit : state.ptr.toNat + 32 * n < UInt256.size) :
    (sosPropagateIterate n state).ptr.toNat = state.ptr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosPropagateAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      change (sosPropagateIterate n next).ptr.toNat = _
      rw [ih next (by rw [hstep]; omega), hstep]
      omega

theorem sosPropagateIterate_read_below
    (n : Nat) (state : SOSPropagateState) (read : Nat)
    (hwrites : ∀ j, j < n →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size ∧ read + 32 ≤ current.ptr.toNat) :
    (sosPropagateIterate n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          let current := sosPropagateIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size ∧ read + 32 ≤ current.ptr.toNat := by
        intro j hj
        simpa only [next, sosPropagateIterate_advance] using hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosPropagateIterate] using hfirst.1
      have hfirstBelow : read + 32 ≤ state.ptr.toNat := by
        simpa only [sosPropagateIterate] using hfirst.2
      rw [sosPropagateIterate, hrest]
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size]) (by omega) hfirstBelow

theorem sosPropagateIterate_memoryWords_below
    (n : Nat) (state : SOSPropagateState) (ptr count : Nat)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (sosPropagateIterate n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosPropagateAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosPropagateIterate] using hwrites 0 (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosPropagateIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosPropagateIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) (by rw [hstep]; omega) htailWrites
      have hfirst := memoryWordsFrom_write_above
        (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toByteArray
        state.memory state.ptr.toNat ptr count (by rw [toByteArray_size])
        (by omega) hbelow
      calc
        memoryWordsFrom (sosPropagateIterate (n + 1) state).memory ptr count =
            memoryWordsFrom (sosPropagateIterate n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := by
          simpa only [next, sosPropagateAdvance, sosPropagateMemory] using hfirst

theorem sosPropagateIterate_memoryWords_above
    (n : Nat) (state : SOSPropagateState) (ptr count : Nat)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (habove : state.ptr.toNat + 32 * n ≤ ptr)
    (hwrites : ∀ j, j < n →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom (sosPropagateIterate n state).memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosPropagateAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosPropagateIterate] using hwrites 0 (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosPropagateIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosPropagateIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) (by rw [hstep]; omega) htailWrites
      have hfirst := memoryWordsFrom_write_below
        (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toByteArray
        state.memory state.ptr.toNat ptr count (by rw [toByteArray_size]) hfirstWrite
        (by omega)
      calc
        memoryWordsFrom (sosPropagateIterate (n + 1) state).memory ptr count =
            memoryWordsFrom (sosPropagateIterate n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := by
          simpa only [next, sosPropagateAdvance, sosPropagateMemory] using hfirst

theorem sosPropagateInputWords_eq_initialMemory
    (n : Nat) (state : SOSPropagateState)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hloads : ∀ j, j < n →
      let current := sosPropagateIterate j state
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hwrites : ∀ j, j < n →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    sosPropagateInputWords n state = memoryWordsFrom state.memory state.ptr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosPropagateAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have htailLoads : ∀ j, j < n →
          let current := sosPropagateIterate j next
          (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
        intro j hj
        simpa only [next, sosPropagateIterate_advance] using hloads (j + 1) (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosPropagateIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosPropagateIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) htailLoads htailWrites
      have hheadNat := hloads 0 (by omega)
      have hhead : sosPropagateWord state.memory state.activeWords state.ptr =
          UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.ptr.toNat) := by
        apply u256_inj
        rw [show (sosPropagateIterate 0 state) = state by rfl] at hheadNat
        rw [hheadNat, UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosPropagateIterate] using hwrites 0 (by omega)
      have hframeRaw := memoryWordsFrom_write_below
        (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toByteArray
        state.memory state.ptr.toNat next.ptr.toNat n
        (by rw [toByteArray_size]) hfirstWrite (by rw [hstep])
      have hframe : memoryWordsFrom next.memory next.ptr.toNat n =
          memoryWordsFrom state.memory next.ptr.toNat n := by
        simpa only [next, sosPropagateAdvance, sosPropagateMemory] using hframeRaw
      simp only [sosPropagateInputWords, memoryWordsFrom]
      change sosPropagateWord state.memory state.activeWords state.ptr ::
          sosPropagateInputWords n next =
        UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.ptr.toNat) ::
          memoryWordsFrom state.memory (state.ptr.toNat + 32) n
      rw [hhead, htail, hframe, hstep]

theorem sosPropagateOutputWords_eq_finalMemory
    (n : Nat) (state : SOSPropagateState)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    sosPropagateOutputWords n state =
      memoryWordsFrom (sosPropagateIterate n state).memory state.ptr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := sosPropagateAdvance state
      have hstep : next.ptr.toNat = state.ptr.toNat + 32 := by
        dsimp only [next, sosPropagateAdvance]
        exact uadd_word_lit32_toNat state.ptr (by omega)
      have htailWrites : ∀ j, j < n →
          let current := sosPropagateIterate j next
          current.ptr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, sosPropagateIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstep]; omega) htailWrites
      have hfirstWrite : state.ptr.toNat + 32 ≤ state.memory.size := by
        simpa only [sosPropagateIterate] using hwrites 0 (by omega)
      have hlater :
          (sosPropagateIterate n next).memory.readWithPadding state.ptr.toNat 32 =
            next.memory.readWithPadding state.ptr.toNat 32 := by
        apply sosPropagateIterate_read_below
        intro j hj
        have hwrite := htailWrites j hj
        have hcurrentPtr := sosPropagateIterate_ptr_toNat j next (by rw [hstep]; omega)
        exact ⟨hwrite, by rw [hcurrentPtr, hstep]; omega⟩
      have hstored : Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.ptr.toNat =
          (sosPropagateValue state.memory state.activeWords state.ptr state.carry).toNat := by
        unfold next sosPropagateAdvance sosPropagateMemory
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [toByteArray_write_read_back_of_gap]
        · exact fromByteArrayBigEndian_toByteArray _
        · rw [Nat.sub_eq_zero_of_le (by omega : state.ptr.toNat ≤ state.memory.size)]
          exact lt_usize 0 (by norm_num)
      have hhead : UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat
              (sosPropagateIterate n next).memory state.ptr.toNat) =
          sosPropagateValue state.memory state.activeWords state.ptr state.carry := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat at hlater hstored ⊢
        rw [hlater]
        exact hstored
      simp only [sosPropagateOutputWords, sosPropagateIterate, memoryWordsFrom]
      change sosPropagateValue state.memory state.activeWords state.ptr state.carry ::
          sosPropagateOutputWords n next =
        UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat
              (sosPropagateIterate n next).memory state.ptr.toNat) ::
          memoryWordsFrom (sosPropagateIterate n next).memory (state.ptr.toNat + 32) n
      rw [← hhead, htail, ← hstep]

/-- A selected carry run adds its incoming carry to the exact concrete memory window. -/
theorem selectedSOSPropagation_value
    {fuel : Nat} (state : SOSPropagateState) (selected : SOSPropagateSelection)
    (hselect : selectSOSPropagation fuel state = some selected)
    (hptrFit : state.ptr.toNat + 32 * selected.words < UInt256.size)
    (hloads : ∀ j, j < selected.words →
      let current := sosPropagateIterate j state
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hwrites : ∀ j, j < selected.words →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory state.ptr.toNat selected.words) +
        UInt256.size ^ selected.words * selected.final.carry.toNat =
      Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.ptr.toNat selected.words) + state.carry.toNat := by
  have hfinal := selectedSOSPropagation_final_eq_iterate hselect
  have hrecompose := sosPropagateCollectors_recompose selected.words state
  rw [sosPropagateInputWords_eq_initialMemory selected.words state hptrFit hloads hwrites,
    sosPropagateOutputWords_eq_finalMemory selected.words state hptrFit hwrites] at hrecompose
  rw [← hfinal] at hrecompose
  exact hrecompose

theorem selectedSOSPropagation_value_final
    {fuel : Nat} (state : SOSPropagateState) (selected : SOSPropagateSelection)
    (hselect : selectSOSPropagation fuel state = some selected)
    (hptrFit : state.ptr.toNat + 32 * selected.words < UInt256.size)
    (hloads : ∀ j, j < selected.words →
      let current := sosPropagateIterate j state
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hwrites : ∀ j, j < selected.words →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.final.memory state.ptr.toNat selected.words) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom state.memory state.ptr.toNat selected.words) + state.carry.toNat := by
  have hvalue := selectedSOSPropagation_value state selected hselect hptrFit hloads hwrites
  rw [selectSOSPropagation_final_zero hselect] at hvalue
  simp only [UInt256.toNat, Nat.mul_zero, Nat.add_zero] at hvalue
  exact hvalue

theorem selectedSOSPropagation_memoryWords_below
    {fuel : Nat} (state : SOSPropagateState) (selected : SOSPropagateSelection)
    (ptr count : Nat)
    (hselect : selectSOSPropagation fuel state = some selected)
    (hptrFit : state.ptr.toNat + 32 * selected.words < UInt256.size)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat)
    (hwrites : ∀ j, j < selected.words →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom selected.final.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  rw [selectedSOSPropagation_final_eq_iterate hselect]
  exact sosPropagateIterate_memoryWords_below selected.words state ptr count
    hptrFit hbelow hwrites

theorem selectedSOSPropagation_memoryWords_above
    {fuel : Nat} (state : SOSPropagateState) (selected : SOSPropagateSelection)
    (ptr count : Nat)
    (hselect : selectSOSPropagation fuel state = some selected)
    (hptrFit : state.ptr.toNat + 32 * selected.words < UInt256.size)
    (habove : state.ptr.toNat + 32 * selected.words ≤ ptr)
    (hwrites : ∀ j, j < selected.words →
      let current := sosPropagateIterate j state
      current.ptr.toNat + 32 ≤ current.memory.size) :
    memoryWordsFrom selected.final.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  rw [selectedSOSPropagation_final_eq_iterate hselect]
  exact sosPropagateIterate_memoryWords_above selected.words state ptr count
    hptrFit habove hwrites

/-- The two fixed diagonal stores preserve every complete word range below them. -/
theorem sosDiagonalMemory_memoryWords_below
    (mem : ByteArray) (aw sOff aOff : UInt256) (ptr count : Nat)
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (hbelow : ptr + 32 * count ≤ sOff.toNat) :
    memoryWordsFrom (sosDiagonalMemory mem aw sOff aOff) ptr count =
      memoryWordsFrom mem ptr count := by
  have hsStep : (sOff + ⟨32⟩).toNat = sOff.toNat + 32 :=
    uadd_word_lit32_toNat sOff (by omega)
  have hfirst := memoryWordsFrom_write_above
    (sosDiagonalLow mem aw sOff aOff).toByteArray mem sOff.toNat ptr count
    (by rw [toByteArray_size]) (by omega) hbelow
  have hmem1Size : (sosDiagonalMemory1 mem aw sOff aOff).size = mem.size := by
    unfold sosDiagonalMemory1
    exact write_size_of_inBounds_from _ _ 0 sOff.toNat 32 (by decide)
      (by rw [toByteArray_size]) (by omega)
  have hsecond := memoryWordsFrom_write_above
    (sosDiagonalHigh mem aw sOff aOff).toByteArray
    (sosDiagonalMemory1 mem aw sOff aOff) (sOff + ⟨32⟩).toNat ptr count
    (by rw [toByteArray_size]) (by rw [hsStep, hmem1Size]; omega)
    (by rw [hsStep]; omega)
  unfold sosDiagonalMemory
  rw [hsecond]
  simpa only [sosDiagonalMemory1] using hfirst

/-- The two fixed diagonal stores preserve every complete word range starting above them. -/
theorem sosDiagonalMemory_memoryWords_above
    (mem : ByteArray) (aw sOff aOff : UInt256) (ptr count : Nat)
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (habove : sOff.toNat + 64 ≤ ptr) :
    memoryWordsFrom (sosDiagonalMemory mem aw sOff aOff) ptr count =
      memoryWordsFrom mem ptr count := by
  have hsStep : (sOff + ⟨32⟩).toNat = sOff.toNat + 32 :=
    uadd_word_lit32_toNat sOff (by omega)
  have hfirst := memoryWordsFrom_write_below
    (sosDiagonalLow mem aw sOff aOff).toByteArray mem sOff.toNat ptr count
    (by rw [toByteArray_size]) (by omega) (by omega)
  have hmem1Size : (sosDiagonalMemory1 mem aw sOff aOff).size = mem.size := by
    unfold sosDiagonalMemory1
    exact write_size_of_inBounds_from _ _ 0 sOff.toNat 32 (by decide)
      (by rw [toByteArray_size]) (by omega)
  have hsecond := memoryWordsFrom_write_below
    (sosDiagonalHigh mem aw sOff aOff).toByteArray
    (sosDiagonalMemory1 mem aw sOff aOff) (sOff + ⟨32⟩).toNat ptr count
    (by rw [toByteArray_size]) (by rw [hsStep, hmem1Size]; omega)
    (by rw [hsStep]; omega)
  unfold sosDiagonalMemory
  rw [hsecond]
  simpa only [sosDiagonalMemory1] using hfirst

/-- The fixed part of one diagonal row writes two adjacent limbs whose represented value, together
with its outgoing carry, is exactly the prior two-word value plus `a[i]^2`. -/
theorem sosDiagonalMemory_twoWords_value
    (mem : ByteArray) (aw sOff aOff : UInt256)
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (hai : (sosDiagonalAi mem aw aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat)
    (hlow : (sosDiagonalLowPrior mem aw sOff aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem sOff.toNat)
    (hhigh : (sosDiagonalHighPrior mem aw sOff aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem (sOff.toNat + 32)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (sosDiagonalMemory mem aw sOff aOff) sOff.toNat 2) +
        UInt256.size ^ 2 * (sosDiagonalCarry mem aw sOff aOff).toNat =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sOff.toNat 2) +
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 := by
  have hsStep : (sOff + ⟨32⟩).toNat = sOff.toNat + 32 :=
    uadd_word_lit32_toNat sOff (by omega)
  have hmem1Size : (sosDiagonalMemory1 mem aw sOff aOff).size = mem.size := by
    unfold sosDiagonalMemory1
    exact write_size_of_inBounds_from _ _ 0 sOff.toNat 32 (by decide)
      (by rw [toByteArray_size]) (by omega)
  have hlowStored : Modexp.MultiLimbMemoryModel.memoryWordNat
        (sosDiagonalMemory1 mem aw sOff aOff) sOff.toNat =
      (sosDiagonalLow mem aw sOff aOff).toNat := by
    unfold sosDiagonalMemory1 Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [toByteArray_write_read_back_of_gap]
    · exact fromByteArrayBigEndian_toByteArray _
    · rw [Nat.sub_eq_zero_of_le (by omega : sOff.toNat ≤ mem.size)]
      exact lt_usize 0 (by norm_num)
  have hlowFinal : Modexp.MultiLimbMemoryModel.memoryWordNat
        (sosDiagonalMemory mem aw sOff aOff) sOff.toNat =
      (sosDiagonalLow mem aw sOff aOff).toNat := by
    unfold sosDiagonalMemory Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
      (by rw [hmem1Size]; omega) (by rw [hsStep])]
    exact hlowStored
  have hhighStored : Modexp.MultiLimbMemoryModel.memoryWordNat
        (sosDiagonalMemory mem aw sOff aOff) (sOff.toNat + 32) =
      (sosDiagonalHigh mem aw sOff aOff).toNat := by
    unfold sosDiagonalMemory Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [hsStep, toByteArray_write_read_back_of_gap]
    · exact fromByteArrayBigEndian_toByteArray _
    · rw [hmem1Size, Nat.sub_eq_zero_of_le (by omega : sOff.toNat + 32 ≤ mem.size)]
      exact lt_usize 0 (by norm_num)
  have hrecompose := sosDiagonal_recompose mem aw sOff aOff
  rw [hai, hlow, hhigh] at hrecompose
  simp only [memoryWordsFrom, Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hlowFinal,
    UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hhighStored]
  rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _),
    UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
  exact hrecompose

/-- One selected diagonal row, including its data-dependent carry propagation, adds exactly the
full square of the selected operand limb to its concrete local scratch window. -/
theorem selectedSOSDiagonal_local_value
    {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (hai : (sosDiagonalAi mem aw aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat)
    (hlow : (sosDiagonalLowPrior mem aw sOff aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem sOff.toNat)
    (hhigh : (sosDiagonalHighPrior mem aw sOff aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem (sOff.toNat + 32))
    (hpropFit : (sOff + ⟨64⟩).toNat + 32 * selected.propagatedWords < UInt256.size)
    (hpropLoads : ∀ j, j < selected.propagatedWords →
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      let current := sosPropagateIterate j propState
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hpropWrites : ∀ j, j < selected.propagatedWords →
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      let current := sosPropagateIterate j propState
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory sOff.toNat
          (2 + selected.propagatedWords)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom mem sOff.toNat (2 + selected.propagatedWords)) +
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 := by
  let carry := sosDiagonalCarry mem aw sOff aOff
  let diagonalMemory := sosDiagonalMemory mem aw sOff aOff
  let diagonalAw := sosDiagonalAw aw sOff aOff
  let propState : SOSPropagateState := {
    carry := carry
    ptr := sOff + ⟨64⟩
    memory := diagonalMemory
    activeWords := diagonalAw }
  have hfixed := sosDiagonalMemory_twoWords_value mem aw sOff aOff hsFit hsRange
    hai hlow hhigh
  have hs64 : (sOff + ⟨64⟩).toNat = sOff.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt (by omega)]
  unfold selectSOSDiagonal at hselect
  dsimp only at hselect
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    change Modexp.wordLimbsToNat (memoryWordsFrom diagonalMemory sOff.toNat 2) = _
    change sosDiagonalCarry mem aw sOff aOff = ⟨0⟩ at hzero
    rw [hzero] at hfixed
    simp only [UInt256.toNat, Nat.mul_zero, Nat.add_zero] at hfixed
    exact hfixed
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation carryFuel propState with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        have hpFit : propState.ptr.toNat + 32 * propagation.words < UInt256.size := by
          simpa only [propState] using hpropFit
        have hpLoads : ∀ j, j < propagation.words →
            let current := sosPropagateIterate j propState
            (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
              Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat := by
          intro j hj
          simpa only [carry, propState, diagonalMemory, diagonalAw] using hpropLoads j hj
        have hpWrites : ∀ j, j < propagation.words →
            let current := sosPropagateIterate j propState
            current.ptr.toNat + 32 ≤ current.memory.size := by
          intro j hj
          simpa only [carry, propState, diagonalMemory, diagonalAw] using hpropWrites j hj
        have hpValue := selectedSOSPropagation_value_final propState propagation hprop
          hpFit hpLoads hpWrites
        have hpFrame := selectedSOSPropagation_memoryWords_below propState propagation
          sOff.toNat 2 hprop hpFit (by dsimp [propState]; rw [hs64]) hpWrites
        have hfixedAbove := sosDiagonalMemory_memoryWords_above mem aw sOff aOff
          propState.ptr.toNat propagation.words hsFit hsRange (by
            dsimp [propState]
            rw [hs64])
        have hfinalSplit := memoryWordsFrom_add propagation.final.memory sOff.toNat
          2 propagation.words
        have hinitialSplit := memoryWordsFrom_add mem sOff.toNat 2 propagation.words
        have hsplit : sOff.toNat + 32 * 2 = propState.ptr.toNat := by
          calc
            sOff.toNat + 32 * 2 = sOff.toNat + 64 := by omega
            _ = propState.ptr.toNat := hs64.symm
        rw [hsplit] at hfinalSplit hinitialSplit
        rw [hfinalSplit, hinitialSplit, Modexp.wordLimbsToNat_append,
          Modexp.wordLimbsToNat_append, memoryWordsFrom_length, hpFrame, hpValue]
        change _ + UInt256.size ^ 2 *
            (Modexp.wordLimbsToNat
              (memoryWordsFrom diagonalMemory propState.ptr.toNat propagation.words) +
              carry.toNat) = _
        rw [show memoryWordsFrom diagonalMemory propState.ptr.toNat propagation.words =
            memoryWordsFrom mem propState.ptr.toNat propagation.words by
          simpa [diagonalMemory] using hfixedAbove]
        change Modexp.wordLimbsToNat (memoryWordsFrom diagonalMemory sOff.toNat 2) +
            UInt256.size ^ 2 * carry.toNat =
          Modexp.wordLimbsToNat (memoryWordsFrom mem sOff.toNat 2) +
            Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 at hfixed
        change Modexp.wordLimbsToNat (memoryWordsFrom diagonalMemory sOff.toNat 2) +
            UInt256.size ^ 2 *
              (Modexp.wordLimbsToNat
                (memoryWordsFrom mem propState.ptr.toNat propagation.words) + carry.toNat) = _
        simp only [memoryWordsFrom_length]
        rw [Nat.mul_add]
        omega

theorem selectedSOSDiagonal_memoryWords_below
    {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection} (ptr count : Nat)
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (hpropFit :
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      propState.ptr.toNat + 32 * selected.propagatedWords < UInt256.size)
    (hpropWrites : ∀ j, j < selected.propagatedWords →
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      let current := sosPropagateIterate j propState
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hbelow : ptr + 32 * count ≤ sOff.toNat)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    memoryWordsFrom selected.finalMemory ptr count = memoryWordsFrom mem ptr count := by
  let carry := sosDiagonalCarry mem aw sOff aOff
  let diagonalMemory := sosDiagonalMemory mem aw sOff aOff
  let diagonalAw := sosDiagonalAw aw sOff aOff
  let propState : SOSPropagateState := {
    carry := carry
    ptr := sOff + ⟨64⟩
    memory := diagonalMemory
    activeWords := diagonalAw }
  have hfixed := sosDiagonalMemory_memoryWords_below mem aw sOff aOff ptr count
    hsFit hsRange hbelow
  have hs64 : (sOff + ⟨64⟩).toNat = sOff.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt (by omega)]
  unfold selectSOSDiagonal at hselect
  dsimp only at hselect
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    exact hfixed
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation carryFuel propState with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        have hpFit : propState.ptr.toNat + 32 * propagation.words < UInt256.size := by
          simpa only [propState] using hpropFit
        have hpWrites : ∀ j, j < propagation.words →
            let current := sosPropagateIterate j propState
            current.ptr.toNat + 32 ≤ current.memory.size := by
          intro j hj
          simpa only [carry, propState, diagonalMemory, diagonalAw] using hpropWrites j hj
        have hpFrame := selectedSOSPropagation_memoryWords_below propState propagation
          ptr count hprop hpFit (by dsimp [propState]; rw [hs64]; omega) hpWrites
        rw [hpFrame]
        exact hfixed

theorem selectedSOSDiagonal_memoryWords_above
    {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection} (ptr count : Nat)
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (hpropFit :
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      propState.ptr.toNat + 32 * selected.propagatedWords < UInt256.size)
    (hpropWrites : ∀ j, j < selected.propagatedWords →
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      let current := sosPropagateIterate j propState
      current.ptr.toNat + 32 ≤ current.memory.size)
    (habove : sOff.toNat + 32 * (2 + selected.propagatedWords) ≤ ptr)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    memoryWordsFrom selected.finalMemory ptr count = memoryWordsFrom mem ptr count := by
  let carry := sosDiagonalCarry mem aw sOff aOff
  let diagonalMemory := sosDiagonalMemory mem aw sOff aOff
  let diagonalAw := sosDiagonalAw aw sOff aOff
  let propState : SOSPropagateState := {
    carry := carry
    ptr := sOff + ⟨64⟩
    memory := diagonalMemory
    activeWords := diagonalAw }
  have hs64 : (sOff + ⟨64⟩).toNat = sOff.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt (by omega)]
  unfold selectSOSDiagonal at hselect
  dsimp only at hselect
  by_cases hzero : carry = ⟨0⟩
  · rw [if_pos hzero] at hselect
    injection hselect with heq
    subst selected
    exact sosDiagonalMemory_memoryWords_above mem aw sOff aOff ptr count
      hsFit hsRange (by omega)
  · rw [if_neg hzero] at hselect
    cases hprop : selectSOSPropagation carryFuel propState with
    | none => rw [hprop] at hselect; contradiction
    | some propagation =>
        rw [hprop] at hselect
        injection hselect with heq
        subst selected
        have hpFit : propState.ptr.toNat + 32 * propagation.words < UInt256.size := by
          simpa only [propState] using hpropFit
        have hpWrites : ∀ j, j < propagation.words →
            let current := sosPropagateIterate j propState
            current.ptr.toNat + 32 ≤ current.memory.size := by
          intro j hj
          simpa only [carry, propState, diagonalMemory, diagonalAw] using hpropWrites j hj
        have hpAbove : propState.ptr.toNat + 32 * propagation.words ≤ ptr := by
          change sOff.toNat + 32 * (2 + propagation.words) ≤ ptr at habove
          dsimp only [propState]
          rw [hs64]
          omega
        have hpFrame := selectedSOSPropagation_memoryWords_above propState propagation
          ptr count hprop hpFit hpAbove hpWrites
        rw [hpFrame]
        exact sosDiagonalMemory_memoryWords_above mem aw sOff aOff ptr count
          hsFit hsRange (by omega)

/-- Embedding a selected diagonal row in any sufficiently large scratch suffix adds exactly the
full square of its source limb and preserves the untouched high suffix. -/
theorem selectedSOSDiagonal_suffix_value
    (totalWords : Nat) {carryFuel : Nat} {mem : ByteArray} {aw sOff aOff : UInt256}
    {selected : SOSDiagonalSelection}
    (hsFit : sOff.toNat + 64 < UInt256.size)
    (hsRange : sOff.toNat + 64 ≤ mem.size)
    (hai : (sosDiagonalAi mem aw aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat)
    (hlow : (sosDiagonalLowPrior mem aw sOff aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem sOff.toNat)
    (hhigh : (sosDiagonalHighPrior mem aw sOff aOff).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem (sOff.toNat + 32))
    (hpropFit :
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      propState.ptr.toNat + 32 * selected.propagatedWords < UInt256.size)
    (hpropLoads : ∀ j, j < selected.propagatedWords →
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      let current := sosPropagateIterate j propState
      (sosPropagateWord current.memory current.activeWords current.ptr).toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.ptr.toNat)
    (hpropWrites : ∀ j, j < selected.propagatedWords →
      let carry := sosDiagonalCarry mem aw sOff aOff
      let propState : SOSPropagateState := {
        carry := carry
        ptr := sOff + ⟨64⟩
        memory := sosDiagonalMemory mem aw sOff aOff
        activeWords := sosDiagonalAw aw sOff aOff }
      let current := sosPropagateIterate j propState
      current.ptr.toNat + 32 ≤ current.memory.size)
    (hwindow : 2 + selected.propagatedWords ≤ totalWords)
    (hselect : selectSOSDiagonal carryFuel mem aw sOff aOff = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory sOff.toNat totalWords) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sOff.toNat totalWords) +
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 := by
  let localWords := 2 + selected.propagatedWords
  let highWords := totalWords - localWords
  have htotal : totalWords = localWords + highWords := by
    dsimp [localWords, highWords]
    omega
  have hlocal := selectedSOSDiagonal_local_value hsFit hsRange hai hlow hhigh
    hpropFit hpropLoads hpropWrites hselect
  change Modexp.wordLimbsToNat
        (memoryWordsFrom selected.finalMemory sOff.toNat localWords) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem sOff.toNat localWords) +
        Modexp.MultiLimbMemoryModel.memoryWordNat mem aOff.toNat ^ 2 at hlocal
  have hframe := selectedSOSDiagonal_memoryWords_above
    (sOff.toNat + 32 * localWords) highWords hsFit hsRange hpropFit hpropWrites
    (by rfl) hselect
  have hfinalSplit := memoryWordsFrom_add selected.finalMemory sOff.toNat
    localWords highWords
  have hinitialSplit := memoryWordsFrom_add mem sOff.toNat localWords highWords
  rw [htotal, hfinalSplit, hinitialSplit, Modexp.wordLimbsToNat_append,
    Modexp.wordLimbsToNat_append, memoryWordsFrom_length, hframe, hlocal]
  simp only [memoryWordsFrom_length]
  omega

end Modexp.MultiLimbMontgomerySOSSemantic
