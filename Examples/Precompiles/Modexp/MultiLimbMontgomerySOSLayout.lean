import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSCall
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSZeroLinks

/-! # SOS allocation and scratch layout -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomerySOSCall
open Modexp.MultiLimbMontgomeryCIOSCall
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def sosZeroAsCIOS (state : SOSZeroState) : CIOSZeroState where
  ptr := state.ptr
  memory := state.memory
  activeWords := state.activeWords

def sosZeroSelectionAsCIOS (selected : SOSZeroSelection) : CIOSZeroSelection where
  final := sosZeroAsCIOS selected.final
  iterations := selected.iterations
  steps := selected.steps
  gas := selected.gas

@[simp] theorem sosZeroAsCIOS_advance (state : SOSZeroState) :
    sosZeroAsCIOS (sosZeroAdvance state) = ciosZeroAdvance (sosZeroAsCIOS state) := by
  rfl

/-- The SOS and CIOS scratch-zero selectors are the same transition system with different state
type names. -/
theorem selectSOSZeroLoop_to_CIOS
    {fuel : Nat} {stop : UInt256} {state : SOSZeroState} {selected : SOSZeroSelection}
    (hselect : selectSOSZeroLoop fuel stop state = some selected) :
    selectCIOSZeroLoop fuel stop (sosZeroAsCIOS state) =
      some (sosZeroSelectionAsCIOS selected) := by
  induction fuel generalizing state selected with
  | zero => simp [selectSOSZeroLoop] at hselect
  | succ fuel ih =>
      simp only [selectSOSZeroLoop] at hselect
      simp only [selectCIOSZeroLoop]
      by_cases hexit : state.ptr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        have hexit' : (sosZeroAsCIOS state).ptr.lt stop = ⟨0⟩ := by
          simpa [sosZeroAsCIOS] using hexit
        rw [if_pos hexit']
        rfl
      · rw [if_neg hexit] at hselect
        have hexit' : (sosZeroAsCIOS state).ptr.lt stop ≠ ⟨0⟩ := by
          simpa [sosZeroAsCIOS] using hexit
        rw [if_neg hexit']
        cases hrest : selectSOSZeroLoop fuel stop (sosZeroAdvance state) with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have hmapped := ih hrest
            rw [← sosZeroAsCIOS_advance, hmapped]
            rfl

/-- Successful SOS scratch initialization inherits exact iteration count, final memory size, and
active-memory coverage from the common zero-loop transition. -/
theorem selectedSOSZeroLoop_coverage_geometry
    (n : Nat) (state : SOSZeroState) (selected : SOSZeroSelection)
    {fuel : Nat} {stop : UInt256}
    (hselect : selectSOSZeroLoop fuel stop state = some selected)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hmemory : state.memory.size ≤ state.ptr.toNat)
    (hgap : state.ptr.toNat - state.memory.size < USize.size)
    (hfit : state.ptr.toNat + 32 * n + 31 < UInt256.size)
    (hstop : stop.toNat = state.ptr.toNat + 32 * n) :
    selected.iterations = n ∧
      MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size := by
  have hmapped := selectSOSZeroLoop_to_CIOS hselect
  have hgeometry :=
    Modexp.MultiLimbMontgomeryCIOSSemantic.selectedCIOSZeroLoop_coverage_geometry
      n (sosZeroAsCIOS state) (sosZeroSelectionAsCIOS selected) hmapped
      hcovered hawFit hmemory hgap hfit hstop
  simpa [sosZeroSelectionAsCIOS, sosZeroAsCIOS] using hgeometry

/-- A successful SOS scratch-zero loop leaves a concrete zero limb at every initialized word. -/
theorem selectedSOSZeroLoop_words_zero
    (n : Nat) (state : SOSZeroState) (selected : SOSZeroSelection)
    {fuel : Nat} {stop : UInt256}
    (hselect : selectSOSZeroLoop fuel stop state = some selected)
    (hfit : state.ptr.toNat + 32 * n < UInt256.size)
    (hmemory : state.memory.size ≤ state.ptr.toNat)
    (hgap : state.ptr.toNat - state.memory.size < USize.size)
    (hstop : stop.toNat = state.ptr.toNat + 32 * n) :
    memoryWordsFrom selected.final.memory state.ptr.toNat n =
      List.replicate n (⟨0⟩ : UInt256) := by
  have hmapped := selectSOSZeroLoop_to_CIOS hselect
  have hcount := selectCIOSZeroLoop_iterations_eq_geometry n hmapped
    (by simpa [sosZeroAsCIOS] using hfit)
    (by simpa [sosZeroAsCIOS] using hstop)
  have hfinal := selectCIOSZeroLoop_final_eq_iterate hmapped
  have hzero := ciosZeroIterate_words_zero n (sosZeroAsCIOS state)
    (by simpa [sosZeroAsCIOS] using hfit)
    (by simpa [sosZeroAsCIOS] using hmemory)
    (by simpa [sosZeroAsCIOS] using hgap)
  rw [hcount] at hfinal
  rw [← hfinal] at hzero
  simpa [sosZeroSelectionAsCIOS, sosZeroAsCIOS] using hzero

/-- A possibly extending word store preserves every padded complete-word range below it. -/
theorem memoryWordsFrom_wordWrite_below_padded_of_gap
    (word : UInt256) (mem : ByteArray) (dest ptr count : Nat)
    (hmem32 : 32 ≤ mem.size) (hbelow : ptr + 32 * count ≤ dest)
    (hgap : dest - mem.size < USize.size) :
    memoryWordsFrom (word.toByteArray.write 0 mem dest 32) ptr count =
      memoryWordsFrom mem ptr count := by
  induction count generalizing ptr with
  | zero => rfl
  | succ count ih =>
      simp only [memoryWordsFrom]
      have hread := toByteArray_write_read_below_padded_of_gap word mem dest ptr hmem32
        (by omega) hgap
      have hword : Modexp.MultiLimbMemoryModel.memoryWordNat
            (word.toByteArray.write 0 mem dest 32) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr := by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        exact congrArg fromByteArrayBigEndian hread
      rw [hword]
      rw [ih (ptr + 32) (by omega)]

/-- A sequential zeroing pass preserves every padded word range below its initial destination,
including when the first store extends memory across a Solidity allocation gap. -/
theorem ciosZeroIterate_memoryWords_below_extending
    (n : Nat) (state : CIOSZeroState) (ptr count : Nat)
    (hptrFit : state.ptr.toNat + 32 * n < UInt256.size)
    (hmem32 : 32 ≤ state.memory.size)
    (hgap : state.ptr.toNat - state.memory.size < USize.size)
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
          state.ptr.toNat hgap
      have hfirst : memoryWordsFrom next.memory ptr count =
          memoryWordsFrom state.memory ptr count := by
        simpa only [next, ciosZeroAdvance, ciosZeroMemory] using
          memoryWordsFrom_wordWrite_below_padded_of_gap (⟨0⟩ : UInt256) state.memory
            state.ptr.toNat ptr count hmem32 hbelow hgap
      have hnextMem32 : 32 ≤ next.memory.size := by rw [hstepSize]; omega
      have hnextGap : next.ptr.toNat - next.memory.size < USize.size := by
        rw [hstepPtr, hstepSize, Nat.sub_eq_zero_of_le (Nat.le_max_right _ _)]
        exact lt_usize 0 (by norm_num)
      have htail := ih next (by rw [hstepPtr]; omega) hnextMem32 hnextGap
        (by rw [hstepPtr]; omega)
      calc
        memoryWordsFrom (ciosZeroIterate (n + 1) state).memory ptr count =
            memoryWordsFrom (ciosZeroIterate n next).memory ptr count := by rfl
        _ = memoryWordsFrom next.memory ptr count := htail
        _ = memoryWordsFrom state.memory ptr count := hfirst

/-- A successful SOS zero selector preserves every padded complete-word range below scratch. -/
theorem selectedSOSZeroLoop_memoryWords_below
    (n : Nat) (state : SOSZeroState) (selected : SOSZeroSelection)
    (ptr count : Nat) {fuel : Nat} {stop : UInt256}
    (hselect : selectSOSZeroLoop fuel stop state = some selected)
    (hfit : state.ptr.toNat + 32 * n < UInt256.size)
    (hmem32 : 32 ≤ state.memory.size)
    (hgap : state.ptr.toNat - state.memory.size < USize.size)
    (hstop : stop.toNat = state.ptr.toNat + 32 * n)
    (hbelow : ptr + 32 * count ≤ state.ptr.toNat) :
    memoryWordsFrom selected.final.memory ptr count =
      memoryWordsFrom state.memory ptr count := by
  have hmapped := selectSOSZeroLoop_to_CIOS hselect
  have hcount := selectCIOSZeroLoop_iterations_eq_geometry n hmapped
    (by simpa [sosZeroAsCIOS] using hfit)
    (by simpa [sosZeroAsCIOS] using hstop)
  have hfinal := selectCIOSZeroLoop_final_eq_iterate hmapped
  rw [hcount] at hfinal
  have hframe := ciosZeroIterate_memoryWords_below_extending n (sosZeroAsCIOS state)
    ptr count (by simpa [sosZeroAsCIOS] using hfit)
    (by simpa [sosZeroAsCIOS] using hmem32)
    (by simpa [sosZeroAsCIOS] using hgap)
    (by simpa [sosZeroAsCIOS] using hbelow)
  rw [← hfinal] at hframe
  simpa [sosZeroSelectionAsCIOS, sosZeroAsCIOS] using hframe

/-- A successful nonempty SOS zero selector extends concrete memory exactly to its stop word. -/
theorem selectedSOSZeroLoop_succ_memory_size
    (n : Nat) (state : SOSZeroState) (selected : SOSZeroSelection)
    {fuel : Nat} {stop : UInt256}
    (hselect : selectSOSZeroLoop fuel stop state = some selected)
    (hmemory : state.memory.size ≤ state.ptr.toNat)
    (hfit : state.ptr.toNat + 32 * (n + 1) < UInt256.size)
    (hgap : state.ptr.toNat - state.memory.size < USize.size)
    (hstop : stop.toNat = state.ptr.toNat + 32 * (n + 1)) :
    selected.final.memory.size = state.ptr.toNat + 32 * (n + 1) := by
  have hmapped := selectSOSZeroLoop_to_CIOS hselect
  have hcount := selectCIOSZeroLoop_iterations_eq_geometry (n + 1) hmapped
    (by simpa [sosZeroAsCIOS] using hfit)
    (by simpa [sosZeroAsCIOS] using hstop)
  have hfinal := selectCIOSZeroLoop_final_eq_iterate hmapped
  rw [hcount] at hfinal
  have hsize := Modexp.MultiLimbMontgomeryCIOSSemantic.ciosZeroIterate_succ_memory_size
    n (sosZeroAsCIOS state) (by simpa [sosZeroAsCIOS] using hmemory)
    (by simpa [sosZeroAsCIOS] using hfit)
    (by simpa [sosZeroAsCIOS] using hgap)
  rw [← hfinal] at hsize
  simpa [sosZeroSelectionAsCIOS, sosZeroAsCIOS] using hsize

/-- The deployed SOS setup initializes exactly `2 * words + 1` scratch words and leaves a covered
memory image whose concrete size reaches the scratch end. -/
theorem allocatedSOSZeroLoop_coverage
    (mem : ByteArray) (aw : UInt256) (fp words fuel : Nat)
    (selected : SOSZeroSelection)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwords : words ≤ 32)
    (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64) :
    let allocatedMemory :=
      storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
    let allocatedAw := newWordArrayWords aw fp words
    let sP := UInt256.ofNat (fp + wordArrayAllocationSize words)
    let kWord := UInt256.ofNat words
    let sEnd := sP + UInt256.shiftLeft kWord ⟨6⟩ + ⟨32⟩
    let zeroState : SOSZeroState := {
      ptr := sP
      memory := sosSetupMemory allocatedMemory sEnd
      activeWords := sosSetupAw allocatedAw }
    selectSOSZeroLoop fuel sEnd zeroState = some selected →
      selected.iterations = 2 * words + 1 ∧
      selected.final.memory.size =
        fp + wordArrayAllocationSize words + 32 * (2 * words + 1) ∧
      MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size := by
  dsimp only
  intro hselect
  let allocatedMemory :=
    storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
  let allocatedAw := newWordArrayWords aw fp words
  let sP := UInt256.ofNat (fp + wordArrayAllocationSize words)
  let kWord := UInt256.ofNat words
  let sEnd := sP + UInt256.shiftLeft kWord ⟨6⟩ + ⟨32⟩
  let zeroState : SOSZeroState := {
    ptr := sP
    memory := sosSetupMemory allocatedMemory sEnd
    activeWords := sosSetupAw allocatedAw }
  have hallocated := allocatedWordArray_coverage mem aw fp words hcovered hawFit
    hmemSize hmemLe hgap hbound
  have hsetup := ciosSetup_coverage allocatedMemory allocatedAw sEnd
    (by simpa [allocatedMemory, allocatedAw] using hallocated.1) hallocated.2
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize words)).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : allocatedMemory.size = fp + 32 := by
    dsimp [allocatedMemory]
    apply storeBytesLength_size
    · rwa [hsetSize]
    · rwa [hsetSize]
  have hsetupMemory : sosSetupMemory allocatedMemory sEnd =
      ciosSetupMemory allocatedMemory sEnd := rfl
  have hsetupAw : sosSetupAw allocatedAw = ciosSetupAw allocatedAw := rfl
  have hsetupSize : (sosSetupMemory allocatedMemory sEnd).size = fp + 32 := by
    rw [hsetupMemory]
    rw [ciosSetupMemory_size_of_96_le allocatedMemory sEnd (by rw [hallocatedSize]; omega)]
    exact hallocatedSize
  have hsPNat : sP.toNat = fp + wordArrayAllocationSize words := by
    apply UInt256.toNat_ofNat_of_lt
    unfold UInt256.size
    omega
  have hkWordNat : kWord.toNat = words := by
    apply UInt256.toNat_ofNat_of_lt
    unfold UInt256.size
    omega
  have hshiftNat : (UInt256.shiftLeft kWord ⟨6⟩).toNat = 64 * words := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide : ¬ ((⟨6⟩ : UInt256).val ≥ 256))]
    change (kWord.toNat <<< 6) % UInt256.size = 64 * words
    rw [hkWordNat, Nat.shiftLeft_eq]
    norm_num
    rw [Nat.mod_eq_of_lt (by
      unfold UInt256.size
      omega)]
    omega
  have hsEndNat : sEnd.toNat = sP.toNat + 64 * words + 32 := by
    have hsPLt : sP.toNat + 64 * words < UInt256.size := by
      rw [hsPNat]
      unfold UInt256.size wordArrayAllocationSize wordArrayPayloadSize
      omega
    have htotalLt : sP.toNat + 64 * words + 32 < UInt256.size := by
      unfold UInt256.size at hsPLt ⊢
      omega
    have hinner : (sP + UInt256.shiftLeft kWord ⟨6⟩).toNat =
        sP.toNat + 64 * words := by
      rw [uadd_toNat, hshiftNat, Nat.mod_eq_of_lt hsPLt]
    dsimp only [sEnd]
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide]
    rw [hinner, Nat.mod_eq_of_lt htotalLt]
  have hzeroMemory : zeroState.memory.size ≤ zeroState.ptr.toNat := by
    dsimp [zeroState]
    rw [hsetupSize, hsPNat]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hzeroGap : zeroState.ptr.toNat - zeroState.memory.size < USize.size := by
    dsimp [zeroState]
    rw [hsetupSize, hsPNat]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    apply lt_usize
    omega
  have hzeroFit : zeroState.ptr.toNat + 32 * (2 * words + 1) + 31 < UInt256.size := by
    dsimp [zeroState]
    rw [hsPNat]
    unfold UInt256.size wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hzeroStop : sEnd.toNat = zeroState.ptr.toNat + 32 * (2 * words + 1) := by
    dsimp [zeroState]
    rw [hsEndNat]
    omega
  have hgeometry := selectedSOSZeroLoop_coverage_geometry (2 * words + 1)
    zeroState selected hselect
    (by simpa [zeroState, hsetupMemory, hsetupAw] using hsetup.1)
    (by simpa [zeroState, hsetupAw] using hsetup.2)
    hzeroMemory hzeroGap hzeroFit hzeroStop
  have hmapped := selectSOSZeroLoop_to_CIOS hselect
  have hfinalMapped := selectCIOSZeroLoop_final_eq_iterate hmapped
  change sosZeroAsCIOS selected.final =
      ciosZeroIterate selected.iterations (sosZeroAsCIOS zeroState) at hfinalMapped
  rw [hgeometry.1] at hfinalMapped
  have hiterateSize := ciosZeroIterate_succ_memory_size (2 * words)
    (sosZeroAsCIOS zeroState) hzeroMemory (by
      change zeroState.ptr.toNat + 32 * (2 * words + 1) < UInt256.size
      omega) hzeroGap
  have hfinalSize : selected.final.memory.size =
      fp + wordArrayAllocationSize words + 32 * (2 * words + 1) := by
    have hsize := congrArg (fun state : CIOSZeroState => state.memory.size) hfinalMapped
    simpa [sosZeroAsCIOS, zeroState, hsPNat] using hsize.trans hiterateSize
  exact ⟨hgeometry.1, hfinalSize, hgeometry.2⟩

end Modexp.MultiLimbMontgomerySOSSemantic
