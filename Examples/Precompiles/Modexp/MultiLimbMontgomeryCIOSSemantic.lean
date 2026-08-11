import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSCall

/-! # Semantic composition of a complete CIOS outer iteration -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Every padded 32-byte memory word fits in one EVM word, independently of its address. -/
theorem memoryWordNat_lt_size (mem : ByteArray) (ptr : Nat) :
    Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr < UInt256.size := by
  have hbound := model_bytesToBigEndianNat_lt_pow (mem.readWithPadding ptr 32)
  rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian] at hbound
  have hsize := ByteArray.readWithPadding_size_le mem ptr 32
  have hpow : 256 ^ (mem.readWithPadding ptr 32).size ≤ 256 ^ 32 :=
    Nat.pow_le_pow_right (by omega) hsize
  unfold Modexp.MultiLimbMemoryModel.memoryWordNat
  have : fromByteArrayBigEndian (mem.readWithPadding ptr 32) < 256 ^ 32 :=
    lt_of_lt_of_le hbound hpow
  simpa [UInt256.size, pow_mul] using this

/-- A generated guarded word load agrees with the byte-array interpretation when its EVM access
is valid. -/
theorem readWord_toNat_of_valid (mem : ByteArray) (aw ptr : UInt256)
    (hsize : ptr.toNat < mem.size) (haw : ¬ ptr ≥ aw * ⟨32⟩) :
    (readWord mem aw ptr).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat := by
  unfold readWord
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩)]
  have hbound := memoryWordNat_lt_size mem ptr.toNat
  change
    (UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat)).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat
  rw [UInt256.toNat_ofNat_of_lt hbound]

/-- The byte-array memory is covered by the EVM active-word counter. -/
def MemoryCovered (mem : ByteArray) (aw : UInt256) : Prop :=
  mem.size ≤ 32 * aw.toNat

/-- Any complete in-bounds word of covered memory begins strictly below the active byte extent. -/
theorem wordBelowActive_of_covered (mem : ByteArray) (aw ptr : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hword : ptr.toNat + 32 ≤ mem.size) :
    ¬ ptr ≥ aw * ⟨32⟩ := by
  intro hge
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hgeNat : (aw * (⟨32⟩ : UInt256)).toNat ≤ ptr.toNat := by
    exact hge
  rw [hmul] at hgeNat
  unfold MemoryCovered at hcovered
  omega

/-- An in-bounds word load from covered memory automatically satisfies the generated active-word
guard, provided converting the active-word count to bytes does not wrap. -/
theorem readWord_toNat_of_covered (mem : ByteArray) (aw ptr : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hword : ptr.toNat + 32 ≤ mem.size) :
    (readWord mem aw ptr).toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr.toNat := by
  apply readWord_toNat_of_valid
  · omega
  · exact wordBelowActive_of_covered mem aw ptr hcovered hawFit hword

/-- A bounded memory expansion keeps its word count representable after conversion to bytes. -/
theorem machineM_mul32_lt_size {s off len : Nat}
    (hs : s * 32 < UInt256.size)
    (hoff : off + len + 31 < UInt256.size) :
    MachineState.M s off len * 32 < UInt256.size := by
  by_cases hlen : len = 0
  · simp [MachineState.M, hlen, hs]
  · simp only [MachineState.M]
    let needed := (off + len + 31) / 32
    have hneeded : needed * 32 < UInt256.size := by
      apply lt_of_le_of_lt (Nat.div_mul_le_self (off + len + 31) 32)
      exact hoff
    by_cases hle : s ≤ needed
    · rw [max_eq_right hle]
      exact hneeded
    · rw [max_eq_left (by omega : needed ≤ s)]
      exact hs

/-- A nonempty EVM memory access is covered by the word count returned by `MachineState.M`. -/
theorem machineM_access_le {s off len : Nat} (hlen : 0 < len) :
    off + len ≤ 32 * MachineState.M s off len := by
  cases len with
  | zero => omega
  | succ len =>
      simp only [MachineState.M]
      have hceil : off + (len + 1) ≤ 32 * ((off + (len + 1) + 31) / 32) := by
        have hdiv : (off + (len + 1) + 31) / 32 ≤
            (off + (len + 1) + 31) / 32 := le_rfl
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)] at hdiv
        omega
      have hmax : (off + (len + 1) + 31) / 32 ≤
          max s ((off + (len + 1) + 31) / 32) := Nat.le_max_right _ _
      nlinarith

/-- Updating active words for one 32-byte read preserves memory coverage and an unwrapped byte
extent. -/
theorem readWords1_coverage (mem : ByteArray) (aw ptr : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hptrFit : ptr.toNat + 32 + 31 < UInt256.size) :
    MemoryCovered mem (readWords1 aw ptr) ∧
      (readWords1 aw ptr).toNat * 32 < UInt256.size := by
  have hMFit := machineM_mul32_lt_size hawFit hptrFit
  have hMSize : MachineState.M aw.toNat ptr.toNat 32 < UInt256.size := by
    have hnonneg : 1 ≤ 32 := by decide
    have hle := Nat.mul_le_mul_left (MachineState.M aw.toNat ptr.toNat 32) hnonneg
    exact lt_of_le_of_lt (by simpa using hle) hMFit
  have hreadWords : (readWords1 aw ptr).toNat =
      MachineState.M aw.toNat ptr.toNat 32 := by
    unfold readWords1
    exact UInt256.toNat_ofNat_of_lt hMSize
  constructor
  · unfold MemoryCovered at hcovered ⊢
    rw [hreadWords]
    have hawLe : aw.toNat ≤ MachineState.M aw.toNat ptr.toNat 32 := by
      simp [MachineState.M]
    nlinarith
  · rwa [hreadWords]

/-- A representable general EVM memory expansion preserves coverage even when the access is wider
than one word. -/
theorem machineM_coverage (mem : ByteArray) (aw : UInt256) (off len : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hoffFit : off + len + 31 < UInt256.size) :
    let next := UInt256.ofNat (MachineState.M aw.toNat off len)
    MemoryCovered mem next ∧ next.toNat * 32 < UInt256.size := by
  dsimp only
  have hMFit := machineM_mul32_lt_size hawFit hoffFit
  have hMSize : MachineState.M aw.toNat off len < UInt256.size := by
    have hle := Nat.mul_le_mul_left (MachineState.M aw.toNat off len)
      (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hMFit
  constructor
  · unfold MemoryCovered at hcovered ⊢
    rw [UInt256.toNat_ofNat_of_lt hMSize]
    have hawLe : aw.toNat ≤ MachineState.M aw.toNat off len := by
      by_cases hlen : len = 0
      · simp [MachineState.M, hlen]
      · simp [MachineState.M, hlen]
    nlinarith
  · rw [UInt256.toNat_ofNat_of_lt hMSize]
    exact hMFit

/-- A bounded 32-byte word write has the expected maximum of the old size and written end. -/
theorem toByteArray_write_size_eq_max (word : UInt256) (mem : ByteArray) (off : Nat)
    (hgap : off - mem.size < USize.size) :
    (word.toByteArray.write 0 mem off 32).size = max mem.size (off + 32) := by
  by_cases hle : off ≤ mem.size
  · apply toByteArray_write32_size_of_le mem word off mem.size
      (max mem.size (off + 32)) rfl hle rfl
  · have hge : mem.size ≤ off := by omega
    apply toByteArray_write32_size_of_ge mem word off mem.size
      (max mem.size (off + 32)) rfl hge hgap
    simp [max_eq_right (by omega : mem.size ≤ off + 32)]

/-- A frontier-extending word write remains covered by the active-word update for that write. -/
theorem write32_coverage (word : UInt256) (mem : ByteArray) (aw ptr : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hptrFit : ptr.toNat + 32 + 31 < UInt256.size)
    (hgap : ptr.toNat - mem.size < USize.size) :
    MemoryCovered (word.toByteArray.write 0 mem ptr.toNat 32) (readWords1 aw ptr) ∧
      (readWords1 aw ptr).toNat * 32 < UInt256.size := by
  have hnext := readWords1_coverage mem aw ptr hcovered hawFit hptrFit
  have hMFit := machineM_mul32_lt_size hawFit hptrFit
  have hMSize : MachineState.M aw.toNat ptr.toNat 32 < UInt256.size := by
    have hle := Nat.mul_le_mul_left (MachineState.M aw.toNat ptr.toNat 32)
      (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hMFit
  have haccess : ptr.toNat + 32 ≤ 32 * (readWords1 aw ptr).toNat := by
    unfold readWords1
    rw [UInt256.toNat_ofNat_of_lt hMSize]
    exact machineM_access_le (by decide)
  constructor
  · unfold MemoryCovered at hnext ⊢
    rw [toByteArray_write_size_eq_max word mem ptr.toNat hgap]
    exact max_le (by simpa using hnext.1) haccess
  · exact hnext.2

/-- The fixed setup store at `0x40`, followed by solc's repeated active-word update for the
corresponding load, preserves covered memory. -/
theorem ciosSetup_coverage (mem : ByteArray) (aw stop : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MemoryCovered (ciosSetupMemory mem stop) (ciosSetupAw aw) ∧
      (ciosSetupAw aw).toNat * 32 < UInt256.size := by
  let ptr : UInt256 := ⟨64⟩
  have hptrFit : ptr.toNat + 32 + 31 < UInt256.size := by
    native_decide
  have hgap : ptr.toNat - mem.size < USize.size := by
    apply lt_of_le_of_lt (Nat.sub_le ptr.toNat mem.size)
    exact lt_usize 64 (by norm_num)
  have hwrite := write32_coverage stop mem aw ptr hcovered hawFit hptrFit hgap
  have hread := readWords1_coverage (ciosSetupMemory mem stop)
    (readWords1 aw ptr) ptr hwrite.1 hwrite.2 hptrFit
  simpa [ptr, ciosSetupMemory, ciosSetupAw, readWords1] using hread

/-- The fixed setup store at `0x40` does not change the size of an already initialized Solidity
memory image. -/
theorem ciosSetupMemory_size_of_96_le (mem : ByteArray) (stop : UInt256)
    (hmem : 96 ≤ mem.size) :
    (ciosSetupMemory mem stop).size = mem.size := by
  unfold ciosSetupMemory
  apply toByteArray_write32_size_of_le mem stop 64 mem.size mem.size rfl (by omega)
  omega

/-- One generated scratch-zero body preserves memory coverage whenever its concrete write address
is representable by both the EVM memory counter and the host byte array. -/
theorem ciosZeroAdvance_coverage (state : CIOSZeroState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : state.ptr.toNat + 32 + 31 < UInt256.size)
    (hgap : state.ptr.toNat - state.memory.size < USize.size) :
    MemoryCovered (ciosZeroAdvance state).memory
        (ciosZeroAdvance state).activeWords ∧
      (ciosZeroAdvance state).activeWords.toNat * 32 < UInt256.size := by
  simpa [ciosZeroAdvance, ciosZeroMemory, ciosZeroAw, readWords1] using
    write32_coverage (⟨0⟩ : UInt256) state.memory state.activeWords state.ptr
      hcovered hawFit hptrFit hgap

def ciosZeroIterate : Nat → CIOSZeroState → CIOSZeroState
  | 0, state => state
  | n + 1, state => ciosZeroIterate n (ciosZeroAdvance state)

/-- The scratch-zero pointer advances by exactly one word per generated loop body. -/
theorem ciosZeroIterate_ptr_toNat (n : Nat) (state : CIOSZeroState)
    (hfit : state.ptr.toNat + 32 * n < UInt256.size) :
    (ciosZeroIterate n state).ptr.toNat = state.ptr.toNat + 32 * n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      have hstepFit : state.ptr.toNat + 32 < UInt256.size := by
        omega
      have hstep : (ciosZeroAdvance state).ptr.toNat = state.ptr.toNat + 32 := by
        simp [ciosZeroAdvance, uadd_word_lit32_toNat state.ptr hstepFit]
      have hrestFit :
          (ciosZeroAdvance state).ptr.toNat + 32 * n < UInt256.size := by
        rw [hstep]
        omega
      rw [ciosZeroIterate]
      rw [ih (ciosZeroAdvance state) hrestFit, hstep]
      omega

/-- After at least one scratch-zero body, concrete byte-array memory reaches exactly the advanced
pointer. -/
theorem ciosZeroIterate_succ_memory_size (n : Nat) (state : CIOSZeroState)
    (hmemory : state.memory.size ≤ state.ptr.toNat)
    (hfit : state.ptr.toNat + 32 * (n + 1) < UInt256.size)
    (hgap : state.ptr.toNat - state.memory.size < USize.size) :
    (ciosZeroIterate (n + 1) state).memory.size =
      state.ptr.toNat + 32 * (n + 1) := by
  induction n generalizing state with
  | zero =>
      have hsize := toByteArray_write_size_eq_max (⟨0⟩ : UInt256)
        state.memory state.ptr.toNat hgap
      simp only [ciosZeroIterate, ciosZeroAdvance, ciosZeroMemory]
      rw [hsize, max_eq_right (by omega : state.memory.size ≤ state.ptr.toNat + 32)]
  | succ n ih =>
      have hstepFit : state.ptr.toNat + 32 < UInt256.size := by
        omega
      have hstepPtr : (ciosZeroAdvance state).ptr.toNat = state.ptr.toNat + 32 := by
        simp [ciosZeroAdvance, uadd_word_lit32_toNat state.ptr hstepFit]
      have hstepSize :
          (ciosZeroAdvance state).memory.size = state.ptr.toNat + 32 := by
        have hsize := toByteArray_write_size_eq_max (⟨0⟩ : UInt256)
          state.memory state.ptr.toNat hgap
        simp only [ciosZeroAdvance, ciosZeroMemory]
        rw [hsize, max_eq_right (by omega : state.memory.size ≤ state.ptr.toNat + 32)]
      have hnextMemory :
          (ciosZeroAdvance state).memory.size ≤ (ciosZeroAdvance state).ptr.toNat := by
        rw [hstepSize, hstepPtr]
      have hnextFit :
          (ciosZeroAdvance state).ptr.toNat + 32 * (n + 1) < UInt256.size := by
        rw [hstepPtr]
        omega
      have hnextGap :
          (ciosZeroAdvance state).ptr.toNat -
              (ciosZeroAdvance state).memory.size < USize.size := by
        rw [hstepPtr, hstepSize, Nat.sub_self]
        exact lt_usize 0 (by norm_num)
      rw [ciosZeroIterate]
      rw [ih (ciosZeroAdvance state) hnextMemory hnextFit hnextGap, hstepPtr]
      omega

/-- The final state recorded by the exact zero-loop selector is repeated execution of its
generated transition, with no summarized memory effect. -/
theorem selectCIOSZeroLoop_final_eq_iterate
    {fuel : Nat} {stop : UInt256} {state : CIOSZeroState}
    {selected : CIOSZeroSelection}
    (hselect : selectCIOSZeroLoop fuel stop state = some selected) :
    selected.final = ciosZeroIterate selected.iterations state := by
  induction fuel generalizing state selected with
  | zero => simp [selectCIOSZeroLoop] at hselect
  | succ fuel ih =>
      simp only [selectCIOSZeroLoop] at hselect
      by_cases hexit : state.ptr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        rfl
      · rw [if_neg hexit] at hselect
        cases hrest : selectCIOSZeroLoop fuel stop (ciosZeroAdvance state) with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            simpa [ciosZeroIterate] using
              ih (state := ciosZeroAdvance state) (selected := rest) hrest

/-- A successful selector has the iteration count determined by the guards along the concrete
transition sequence. -/
theorem selectCIOSZeroLoop_iterations_eq_of_guards
    (n : Nat) {fuel : Nat} {stop : UInt256} {state : CIOSZeroState}
    {selected : CIOSZeroSelection}
    (hselect : selectCIOSZeroLoop fuel stop state = some selected)
    (hcontinue : ∀ i, i < n → (ciosZeroIterate i state).ptr.lt stop ≠ ⟨0⟩)
    (hexit : (ciosZeroIterate n state).ptr.lt stop = ⟨0⟩) :
    selected.iterations = n := by
  induction n generalizing fuel state selected with
  | zero =>
      cases fuel with
      | zero => simp [selectCIOSZeroLoop] at hselect
      | succ fuel =>
          simp only [selectCIOSZeroLoop] at hselect
          rw [if_pos (by simpa [ciosZeroIterate] using hexit)] at hselect
          injection hselect with heq
          subst selected
          rfl
  | succ n ih =>
      cases fuel with
      | zero => simp [selectCIOSZeroLoop] at hselect
      | succ fuel =>
          simp only [selectCIOSZeroLoop] at hselect
          have hfirst : state.ptr.lt stop ≠ ⟨0⟩ := by
            simpa [ciosZeroIterate] using hcontinue 0 (by omega)
          rw [if_neg hfirst] at hselect
          cases hrest : selectCIOSZeroLoop fuel stop (ciosZeroAdvance state) with
          | none => rw [hrest] at hselect; contradiction
          | some rest =>
              rw [hrest] at hselect
              injection hselect with heq
              subst selected
              have hrestCount := ih (state := ciosZeroAdvance state) (selected := rest)
                hrest
                (fun i hi => by
                  simpa [ciosZeroIterate] using hcontinue (i + 1) (by omega))
                (by simpa [ciosZeroIterate] using hexit)
              change rest.iterations + 1 = n + 1
              omega

/-- For a nonwrapping word-aligned interval, selector success fixes the exact number of generated
zero bodies independently of its fuel allowance. -/
theorem selectCIOSZeroLoop_iterations_eq_geometry
    (n : Nat) {fuel : Nat} {stop : UInt256} {state : CIOSZeroState}
    {selected : CIOSZeroSelection}
    (hselect : selectCIOSZeroLoop fuel stop state = some selected)
    (hfit : state.ptr.toNat + 32 * n < UInt256.size)
    (hstop : stop.toNat = state.ptr.toNat + 32 * n) :
    selected.iterations = n := by
  apply selectCIOSZeroLoop_iterations_eq_of_guards n hselect
  · intro i hi
    have hiptr := ciosZeroIterate_ptr_toNat i state (by omega)
    apply ne_of_eq_of_ne (ult_one (by rw [hiptr, hstop]; omega))
    native_decide
  · apply ult_zero
    rw [ciosZeroIterate_ptr_toNat n state hfit, hstop]

/-- Coverage propagates through every concrete scratch-zero transition.  The safety hypotheses
are indexed by the actual intermediate states so they can later be discharged from allocation
geometry. -/
theorem ciosZeroIterate_coverage (n : Nat) (state : CIOSZeroState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : ∀ i, i < n →
      (ciosZeroIterate i state).ptr.toNat + 32 + 31 < UInt256.size)
    (hgap : ∀ i, i < n →
      (ciosZeroIterate i state).ptr.toNat - (ciosZeroIterate i state).memory.size < USize.size) :
    MemoryCovered (ciosZeroIterate n state).memory
        (ciosZeroIterate n state).activeWords ∧
      (ciosZeroIterate n state).activeWords.toNat * 32 < UInt256.size := by
  induction n generalizing state with
  | zero => exact ⟨hcovered, hawFit⟩
  | succ n ih =>
      have hstep := ciosZeroAdvance_coverage state hcovered hawFit
        (hptrFit 0 (by omega)) (hgap 0 (by omega))
      have hrest := ih (state := ciosZeroAdvance state) hstep.1 hstep.2
        (fun i hi => by
          simpa [ciosZeroIterate] using hptrFit (i + 1) (by omega))
        (fun i hi => by
          simpa [ciosZeroIterate] using hgap (i + 1) (by omega))
      simpa [ciosZeroIterate] using hrest

/-- The successful exact selector therefore preserves memory coverage through all of its
recorded zeroing iterations. -/
theorem selectedCIOSZeroLoop_coverage
    {fuel : Nat} {stop : UInt256} (state : CIOSZeroState)
    (selected : CIOSZeroSelection)
    (hselect : selectCIOSZeroLoop fuel stop state = some selected)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hptrFit : ∀ i, i < selected.iterations →
      (ciosZeroIterate i state).ptr.toNat + 32 + 31 < UInt256.size)
    (hgap : ∀ i, i < selected.iterations →
      (ciosZeroIterate i state).ptr.toNat -
          (ciosZeroIterate i state).memory.size < USize.size) :
    MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size := by
  rw [selectCIOSZeroLoop_final_eq_iterate hselect]
  exact ciosZeroIterate_coverage selected.iterations state hcovered hawFit hptrFit hgap

/-- Allocation-style geometry discharges every indexed safety premise of the selected zero loop
and fixes its exact iteration count. -/
theorem selectedCIOSZeroLoop_coverage_geometry
    (n : Nat) {fuel : Nat} {stop : UInt256} (state : CIOSZeroState)
    (selected : CIOSZeroSelection)
    (hselect : selectCIOSZeroLoop fuel stop state = some selected)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hmemory : state.memory.size ≤ state.ptr.toNat)
    (hgap : state.ptr.toNat - state.memory.size < USize.size)
    (hfit : state.ptr.toNat + 32 * n + 31 < UInt256.size)
    (hstop : stop.toNat = state.ptr.toNat + 32 * n) :
    selected.iterations = n ∧
      MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size := by
  have hcount := selectCIOSZeroLoop_iterations_eq_geometry n hselect (by omega) hstop
  have hcoverage := selectedCIOSZeroLoop_coverage state selected hselect hcovered hawFit
    (fun i hi => by
      rw [hcount] at hi
      rw [ciosZeroIterate_ptr_toNat i state (by omega)]
      omega)
    (fun i hi => by
      rw [hcount] at hi
      cases i with
      | zero => simpa [ciosZeroIterate] using hgap
      | succ i =>
          have hptr := ciosZeroIterate_ptr_toNat (i + 1) state (by omega)
          have hsize := ciosZeroIterate_succ_memory_size i state hmemory (by omega) hgap
          rw [hptr, hsize, Nat.sub_self]
          exact lt_usize 0 (by norm_num))
  exact ⟨hcount, hcoverage⟩

/-- The concrete word-array allocation used by `_montMul` is covered by the exact active-word
counter produced by solc's allocation helper. -/
theorem allocatedWordArray_coverage (mem : ByteArray) (aw : UInt256) (fp words : Nat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64) :
    let allocatedMemory :=
      storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
    MemoryCovered allocatedMemory (newWordArrayWords aw fp words) ∧
      (newWordArrayWords aw fp words).toNat * 32 < UInt256.size := by
  dsimp only
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize words)).size = mem.size :=
    setFreePtr_size hmemSize
  have hsetCovered :
      MemoryCovered (setFreePtr mem (fp + wordArrayAllocationSize words)) aw := by
    unfold MemoryCovered at hcovered ⊢
    rwa [hsetSize]
  have hfpLt64 : fp < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hfpWord : fp < UInt256.size := by
    unfold UInt256.size
    omega
  let fpWord := UInt256.ofNat fp
  have hfpWordNat : fpWord.toNat = fp := UInt256.toNat_ofNat_of_lt hfpWord
  have hfpFit : fpWord.toNat + 32 + 31 < UInt256.size := by
    rw [hfpWordNat]
    unfold UInt256.size
    omega
  have hsetGap :
      fpWord.toNat - (setFreePtr mem
        (fp + wordArrayAllocationSize words)).size < USize.size := by
    rw [hfpWordNat, hsetSize]
    exact hgap
  have hwrite := write32_coverage (UInt256.ofNat words)
    (setFreePtr mem (fp + wordArrayAllocationSize words)) aw fpWord
    hsetCovered hawFit hfpFit hsetGap
  have hstoredAw : readWords1 aw fpWord = newBytesStoreWords aw fp := by
    simp [readWords1, newBytesStoreWords, fpWord, hfpWordNat]
  rw [hstoredAw] at hwrite
  have hstoreMemory :
      (UInt256.ofNat words).toByteArray.write 0
          (setFreePtr mem (fp + wordArrayAllocationSize words)) fpWord.toNat 32 =
        storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words := by
    simp [storeBytesLength, fpWord, hfpWordNat]
  rw [hstoreMemory] at hwrite
  have hpayloadFit : fp + 32 + wordArrayPayloadSize words + 31 < UInt256.size := by
    unfold wordArrayAllocationSize at hbound
    unfold UInt256.size
    omega
  have hpayload := machineM_coverage
    (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words)
    (newBytesStoreWords aw fp) (fp + 32) (wordArrayPayloadSize words)
    hwrite.1 hwrite.2 hpayloadFit
  simpa [newWordArrayWords] using hpayload

/-- Instantiating the deployed CIOS setup with a bounded word-array allocation yields exactly
`words + 2` scratch-zero stores and a covered state at the first outer iteration. -/
theorem allocatedCIOSZeroLoop_coverage
    (mem : ByteArray) (aw : UInt256) (fp words fuel : Nat)
    (selected : CIOSZeroSelection)
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
    let tP := UInt256.ofNat (fp + wordArrayAllocationSize words)
    let kWords := UInt256.shiftLeft (UInt256.ofNat words) ⟨5⟩
    let tEnd := tP + kWords
    let stop := tEnd + ⟨64⟩
    let zeroState : CIOSZeroState := {
      ptr := tP
      memory := ciosSetupMemory allocatedMemory stop
      activeWords := ciosSetupAw allocatedAw }
    selectCIOSZeroLoop fuel stop zeroState = some selected →
      selected.iterations = words + 2 ∧
      selected.final.memory.size =
        fp + wordArrayAllocationSize words + 32 * (words + 2) ∧
      MemoryCovered selected.final.memory selected.final.activeWords ∧
      selected.final.activeWords.toNat * 32 < UInt256.size := by
  dsimp only
  intro hselect
  let allocatedMemory :=
    storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
  let allocatedAw := newWordArrayWords aw fp words
  let tP := UInt256.ofNat (fp + wordArrayAllocationSize words)
  let kWords := UInt256.shiftLeft (UInt256.ofNat words) ⟨5⟩
  let tEnd := tP + kWords
  let stop := tEnd + ⟨64⟩
  let zeroState : CIOSZeroState := {
    ptr := tP
    memory := ciosSetupMemory allocatedMemory stop
    activeWords := ciosSetupAw allocatedAw }
  have hallocated := allocatedWordArray_coverage mem aw fp words hcovered hawFit
    hmemSize hmemLe hgap hbound
  have hsetup := ciosSetup_coverage allocatedMemory allocatedAw stop
    (by simpa [allocatedMemory, allocatedAw] using hallocated.1) hallocated.2
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize words)).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : allocatedMemory.size = fp + 32 := by
    dsimp [allocatedMemory]
    apply storeBytesLength_size
    · rwa [hsetSize]
    · rwa [hsetSize]
  have hsetupSize : (ciosSetupMemory allocatedMemory stop).size = fp + 32 := by
    rw [ciosSetupMemory_size_of_96_le allocatedMemory stop (by rw [hallocatedSize]; omega)]
    exact hallocatedSize
  have htPNat : tP.toNat = fp + wordArrayAllocationSize words := by
    apply UInt256.toNat_ofNat_of_lt
    unfold UInt256.size
    omega
  have hkWordsNat : kWords.toNat = 32 * words := by
    dsimp [kWords]
    exact ushl5_ofNat_toNat words (by omega)
  have htEndNat : tEnd.toNat = tP.toNat + kWords.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt]
    rw [htPNat, hkWordsNat]
    unfold UInt256.size
    omega
  have hstopNat : stop.toNat = tEnd.toNat + 64 := by
    rw [uadd_toNat, show (⟨64⟩ : UInt256).toNat = 64 by decide,
      Nat.mod_eq_of_lt]
    rw [htEndNat, htPNat, hkWordsNat]
    unfold UInt256.size
    omega
  have hzeroMemory : zeroState.memory.size ≤ zeroState.ptr.toNat := by
    dsimp [zeroState]
    rw [hsetupSize, htPNat]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hzeroGap :
      zeroState.ptr.toNat - zeroState.memory.size < USize.size := by
    dsimp [zeroState]
    rw [hsetupSize, htPNat]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    apply lt_usize
    omega
  have hzeroFit : zeroState.ptr.toNat + 32 * (words + 2) + 31 < UInt256.size := by
    dsimp [zeroState]
    rw [htPNat]
    unfold UInt256.size wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hzeroStop : stop.toNat = zeroState.ptr.toNat + 32 * (words + 2) := by
    dsimp [zeroState]
    rw [hstopNat, htEndNat, htPNat, hkWordsNat]
    omega
  have hgeometry := selectedCIOSZeroLoop_coverage_geometry (words + 2) zeroState selected
    (by simpa [zeroState, stop, tEnd, kWords, tP, allocatedAw, allocatedMemory] using hselect)
    (by simpa [zeroState] using hsetup.1) hsetup.2 hzeroMemory hzeroGap hzeroFit hzeroStop
  have hfinalState : selected.final = ciosZeroIterate (words + 2) zeroState := by
    rw [selectCIOSZeroLoop_final_eq_iterate (by
      simpa [zeroState, stop, tEnd, kWords, tP, allocatedAw, allocatedMemory] using hselect)]
    rw [hgeometry.1]
  have hiterateSize := ciosZeroIterate_succ_memory_size (words + 1) zeroState
    hzeroMemory (by omega) hzeroGap
  have hfinalSize : selected.final.memory.size =
      fp + wordArrayAllocationSize words + 32 * (words + 2) := by
    rw [hfinalState]
    simpa [zeroState, htPNat, show words + 1 + 1 = words + 2 by omega] using hiterateSize
  exact ⟨hgeometry.1, hfinalSize, hgeometry.2⟩

/-- One in-bounds generated multiply column preserves covered memory and an unwrapped active-word
extent. -/
theorem multiplyPassAdvance_coverage (a : UInt256) (state : MultiplyPassState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hoperandFit : state.operandPtr.toNat + 32 + 31 < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 + 31 < UInt256.size)
    (hwrite : state.resultPtr.toNat + 32 ≤ state.memory.size) :
    MemoryCovered (multiplyPassAdvance a state).memory
        (multiplyPassAdvance a state).activeWords ∧
      (multiplyPassAdvance a state).activeWords.toNat * 32 < UInt256.size := by
  have h1 := readWords1_coverage state.memory state.activeWords state.operandPtr
    hcovered hawFit hoperandFit
  have h2 := readWords1_coverage state.memory
    (readWords1 state.activeWords state.operandPtr) state.resultPtr h1.1 h1.2 hresultFit
  have h3 := readWords1_coverage state.memory
    (readWords1 (readWords1 state.activeWords state.operandPtr) state.resultPtr)
    state.resultPtr h2.1 h2.2 hresultFit
  have hactive : MemoryCovered state.memory
        (multiplyPassAw state.activeWords state.operandPtr state.resultPtr) ∧
      (multiplyPassAw state.activeWords state.operandPtr state.resultPtr).toNat * 32 <
        UInt256.size := by
    simpa only [multiplyPassAw, readWords1] using h3
  have hsize : (multiplyPassMemory state.memory state.activeWords state.operandPtr
      state.resultPtr a state.carry).size = state.memory.size := by
    unfold multiplyPassMemory
    exact write_size_of_inBounds_from _ _ 0 state.resultPtr.toNat 32
      (by decide) (by rw [toByteArray_size]) hwrite
  constructor
  · unfold MemoryCovered at hactive ⊢
    simpa only [multiplyPassAdvance, hsize] using hactive.1
  · simpa only [multiplyPassAdvance] using hactive.2

/-- One in-bounds generated reduction column satisfies the same coverage invariant. -/
theorem schoolbookAdvance_coverage (a : UInt256) (state : SchoolbookState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hoperandFit : state.operandPtr.toNat + 32 + 31 < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 + 31 < UInt256.size)
    (hwritePtrFit : (schoolbookWritePtr state.resultPtr).toNat + 32 + 31 <
      UInt256.size)
    (hwrite : (schoolbookWritePtr state.resultPtr).toNat + 32 ≤ state.memory.size) :
    MemoryCovered (schoolbookAdvance a state).memory
        (schoolbookAdvance a state).activeWords ∧
      (schoolbookAdvance a state).activeWords.toNat * 32 < UInt256.size := by
  have h1 := readWords1_coverage state.memory state.activeWords state.operandPtr
    hcovered hawFit hoperandFit
  have h2 := readWords1_coverage state.memory
    (readWords1 state.activeWords state.operandPtr) state.resultPtr h1.1 h1.2 hresultFit
  have h3 := readWords1_coverage state.memory
    (readWords1 (readWords1 state.activeWords state.operandPtr) state.resultPtr)
    (schoolbookWritePtr state.resultPtr) h2.1 h2.2 hwritePtrFit
  have hactive : MemoryCovered state.memory
        (schoolbookAw state.activeWords state.operandPtr state.resultPtr) ∧
      (schoolbookAw state.activeWords state.operandPtr state.resultPtr).toNat * 32 <
        UInt256.size := by
    simpa only [schoolbookAw, readWords1] using h3
  have hsize : (schoolbookMemory state.memory state.activeWords state.operandPtr
      state.resultPtr a state.carry).size = state.memory.size := by
    unfold schoolbookMemory
    exact write_size_of_inBounds_from _ _ 0 (schoolbookWritePtr state.resultPtr).toNat 32
      (by decide) (by rw [toByteArray_size]) hwrite
  constructor
  · unfold MemoryCovered at hactive ⊢
    simpa only [schoolbookAdvance, hsize] using hactive.1
  · simpa only [schoolbookAdvance] using hactive.2

/-- The generated reduction write address is the preceding word when the source result pointer is
at least one word. -/
theorem schoolbookWritePtr_toNat (ptr : UInt256) (hlo : 32 ≤ ptr.toNat) :
    (schoolbookWritePtr ptr).toNat = ptr.toNat - 32 := by
  unfold schoolbookWritePtr
  rw [uadd_toNat, lnot31_toNat]
  have hp : ptr.toNat < UInt256.size := by
    simp [UInt256.toNat, ptr.val.isLt]
  rw [show ptr.toNat + (2 ^ 256 - 32) =
      UInt256.size + (ptr.toNat - 32) by
    simp only [UInt256.size]
    omega]
  have hdiff : ptr.toNat - 32 < UInt256.size := by omega
  simpa using (Nat.mod_eq_of_lt hdiff)

/-- A multiply pass whose whole result range lies in memory has every generated write in bounds,
and none of those writes changes the byte-array size. -/
theorem multiplyPassIterate_inBounds
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hptrFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hrange : state.resultPtr.toNat + 32 * n ≤ state.memory.size) :
    (∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) ∧
      (multiplyPassIterate a n state).memory.size = state.memory.size := by
  induction n generalizing state with
  | zero => simp [multiplyPassIterate]
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hfirst : state.resultPtr.toNat + 32 ≤ state.memory.size := by
        omega
      have hnextPtr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextSize : next.memory.size = state.memory.size := by
        dsimp [next, multiplyPassAdvance]
        unfold multiplyPassMemory
        exact write_size_of_inBounds_from _ _ 0 state.resultPtr.toNat 32
          (by decide) (by rw [toByteArray_size]) hfirst
      have hrest := ih next (by rw [hnextPtr]; omega) (by rw [hnextPtr, hnextSize]; omega)
      constructor
      · intro j hj
        cases j with
        | zero => simpa [multiplyPassIterate] using hfirst
        | succ j =>
            simpa only [next, multiplyPassIterate] using hrest.1 j (by omega)
      · simpa only [next, multiplyPassIterate, hnextSize] using hrest.2

/-- The analogous range fact for generated reduction columns also records both the prior-result
read range and the preceding-limb write range. -/
theorem schoolbookIterate_inBounds
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hresultLo : 32 ≤ state.resultPtr.toNat)
    (hptrFit : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hrange : state.resultPtr.toNat + 32 * n ≤ state.memory.size) :
    (∀ j, j < n →
      let current := schoolbookIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size) ∧
      (schoolbookIterate a n state).memory.size = state.memory.size := by
  induction n generalizing state with
  | zero => simp [schoolbookIterate]
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hresult : state.resultPtr.toNat + 32 ≤ state.memory.size := by
        omega
      have hwritePtr : (schoolbookWritePtr state.resultPtr).toNat + 32 =
          state.resultPtr.toNat := by
        rw [schoolbookWritePtr_toNat state.resultPtr hresultLo]
        omega
      have hwrite : (schoolbookWritePtr state.resultPtr).toNat + 32 ≤
          state.memory.size := by
        rw [hwritePtr]
        omega
      have hnextPtr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp [next, schoolbookAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextSize : next.memory.size = state.memory.size := by
        dsimp [next, schoolbookAdvance]
        unfold schoolbookMemory
        exact write_size_of_inBounds_from _ _ 0
          (schoolbookWritePtr state.resultPtr).toNat 32
          (by decide) (by rw [toByteArray_size]) hwrite
      have hrest := ih next (by rw [hnextPtr]; omega)
        (by rw [hnextPtr]; omega) (by rw [hnextPtr, hnextSize]; omega)
      constructor
      · intro j hj
        cases j with
        | zero => simpa [schoolbookIterate] using And.intro hresult hwrite
        | succ j =>
            simpa only [next, schoolbookIterate] using hrest.1 j (by omega)
      · simpa only [next, schoolbookIterate, hnextSize] using hrest.2

structure CIOSBoundaryCoverageFacts
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP nP : UInt256) : Prop where
  aw2Covered : MemoryCovered (ciosBoundaryMem1 mem aw tEnd multiplyCarry)
    (ciosBoundaryAw2 aw tEnd)
  aw2Fit : (ciosBoundaryAw2 aw tEnd).toNat * 32 < UInt256.size
  aw4Covered : MemoryCovered (ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off)
    (ciosBoundaryAw4 aw tEnd tk1Off)
  aw4Fit : (ciosBoundaryAw4 aw tEnd tk1Off).toNat * 32 < UInt256.size
  finalCovered : MemoryCovered (ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off)
    (ciosBoundaryAw aw tEnd tk1Off tP nP)
  finalFit : (ciosBoundaryAw aw tEnd tk1Off tP nP).toNat * 32 < UInt256.size
  mem1Size : (ciosBoundaryMem1 mem aw tEnd multiplyCarry).size = mem.size
  mem2Size : (ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off).size = mem.size

/-- The complete generated CIOS boundary block preserves covered memory and the concrete memory
size when its two scratch writes are in bounds. -/
theorem ciosBoundary_coverage
    (mem : ByteArray) (aw tEnd multiplyCarry tk1Off tP nP : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (htEndFit : tEnd.toNat + 32 + 31 < UInt256.size)
    (htk1Fit : tk1Off.toNat + 32 + 31 < UInt256.size)
    (htPFit : tP.toNat + 32 + 31 < UInt256.size)
    (hnPFit : nP.toNat + 32 + 31 < UInt256.size)
    (htEndWrite : tEnd.toNat + 32 ≤ mem.size)
    (htk1Write : tk1Off.toNat + 32 ≤ mem.size) :
    CIOSBoundaryCoverageFacts mem aw tEnd multiplyCarry tk1Off tP nP := by
  let mem1 := ciosBoundaryMem1 mem aw tEnd multiplyCarry
  let aw1 := ciosBoundaryAw1 aw tEnd
  let aw2 := ciosBoundaryAw2 aw tEnd
  let mem2 := ciosBoundaryMem2 mem aw tEnd multiplyCarry tk1Off
  let aw3 := ciosBoundaryAw3 aw tEnd tk1Off
  let aw4 := ciosBoundaryAw4 aw tEnd tk1Off
  let aw5 := ciosBoundaryAw5 aw tEnd tk1Off tP
  have hgapEnd : tEnd.toNat - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite1 := write32_coverage
    (ciosBoundaryTkNew mem aw tEnd multiplyCarry) mem aw tEnd
    hcovered hawFit htEndFit hgapEnd
  have hmem1Size : mem1.size = mem.size := by
    dsimp [mem1, ciosBoundaryMem1]
    exact write_size_of_inBounds_from _ _ 0 tEnd.toNat 32
      (by decide) (by rw [toByteArray_size]) htEndWrite
  have hcov1 : MemoryCovered mem1 aw1 ∧ aw1.toNat * 32 < UInt256.size := by
    simpa only [mem1, aw1, ciosBoundaryMem1, ciosBoundaryAw1] using hwrite1
  have hread1 := readWords1_coverage mem1 aw1 tEnd hcov1.1 hcov1.2 htEndFit
  have hcov2 : MemoryCovered mem1 aw2 ∧ aw2.toNat * 32 < UInt256.size := by
    simpa only [aw2, ciosBoundaryAw2, readWords1] using hread1
  have hgapTk1 : tk1Off.toNat - mem1.size < USize.size := by
    rw [hmem1Size, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite2 := write32_coverage
    (ciosBoundaryTk1 mem aw tEnd multiplyCarry tk1Off +
      ciosBoundaryOverflow mem aw tEnd multiplyCarry)
    mem1 aw2 tk1Off hcov2.1 hcov2.2 htk1Fit hgapTk1
  have hmem2Size : mem2.size = mem.size := by
    dsimp [mem2, ciosBoundaryMem2]
    rw [show ciosBoundaryMem1 mem aw tEnd multiplyCarry = mem1 by rfl]
    rw [write_size_of_inBounds_from _ _ 0 tk1Off.toNat 32
      (by decide) (by rw [toByteArray_size]) (by rw [hmem1Size]; exact htk1Write)]
    exact hmem1Size
  have hcov3 : MemoryCovered mem2 aw3 ∧ aw3.toNat * 32 < UInt256.size := by
    simpa only [mem1, mem2, aw2, aw3, ciosBoundaryMem2, ciosBoundaryAw3] using hwrite2
  have hread2 := readWords1_coverage mem2 aw3 tk1Off hcov3.1 hcov3.2 htk1Fit
  have hcov4 : MemoryCovered mem2 aw4 ∧ aw4.toNat * 32 < UInt256.size := by
    simpa only [aw4, ciosBoundaryAw4, readWords1] using hread2
  have hreadT0 := readWords1_coverage mem2 aw4 tP hcov4.1 hcov4.2 htPFit
  have hcov5 : MemoryCovered mem2 aw5 ∧ aw5.toNat * 32 < UInt256.size := by
    simpa only [aw5, ciosBoundaryAw5] using hreadT0
  have hreadN0 := readWords1_coverage mem2 aw5 nP hcov5.1 hcov5.2 hnPFit
  have hcovFinal :
      MemoryCovered mem2 (ciosBoundaryAw aw tEnd tk1Off tP nP) ∧
        (ciosBoundaryAw aw tEnd tk1Off tP nP).toNat * 32 < UInt256.size := by
    simpa only [ciosBoundaryAw] using hreadN0
  exact {
    aw2Covered := by simpa only [mem1, aw2] using hcov2.1
    aw2Fit := by simpa only [aw2] using hcov2.2
    aw4Covered := by simpa only [mem2, aw4] using hcov4.1
    aw4Fit := by simpa only [aw4] using hcov4.2
    finalCovered := by simpa only [mem2] using hcovFinal.1
    finalFit := by simpa only [mem2] using hcovFinal.2
    mem1Size := hmem1Size
    mem2Size := hmem2Size }

structure CIOSShiftCoverageFacts
    (mem : ByteArray) (aw reductionCarry shiftedOut tk1Off tEnd : UInt256) : Prop where
  aw2Covered : MemoryCovered (ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd)
    (ciosShiftAw2 aw shiftedOut tEnd)
  aw2Fit : (ciosShiftAw2 aw shiftedOut tEnd).toNat * 32 < UInt256.size
  finalCovered : MemoryCovered
    (ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd)
    (ciosShiftAw aw shiftedOut tk1Off tEnd)
  finalFit : (ciosShiftAw aw shiftedOut tk1Off tEnd).toNat * 32 < UInt256.size
  mem1Size : (ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd).size = mem.size
  mem2Size : (ciosShiftMem2 mem aw reductionCarry shiftedOut tk1Off tEnd).size = mem.size
  finalSize : (ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd).size = mem.size

/-- The complete generated final-shift block preserves coverage and the scratch-buffer size when
its three writes remain inside that buffer. -/
theorem ciosShift_coverage
    (mem : ByteArray) (aw reductionCarry shiftedOut tk1Off tEnd : UInt256)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hshiftedFit : shiftedOut.toNat + 32 + 31 < UInt256.size)
    (htk1Fit : tk1Off.toNat + 32 + 31 < UInt256.size)
    (htEndFit : tEnd.toNat + 32 + 31 < UInt256.size)
    (hshiftedWrite : shiftedOut.toNat + 32 ≤ mem.size)
    (htk1Write : tk1Off.toNat + 32 ≤ mem.size)
    (htEndWrite : tEnd.toNat + 32 ≤ mem.size) :
    CIOSShiftCoverageFacts mem aw reductionCarry shiftedOut tk1Off tEnd := by
  let aw1 := ciosShiftAw1 aw tEnd
  let mem1 := ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd
  let aw2 := ciosShiftAw2 aw shiftedOut tEnd
  let aw3 := ciosShiftAw3 aw shiftedOut tk1Off tEnd
  let mem2 := ciosShiftMem2 mem aw reductionCarry shiftedOut tk1Off tEnd
  let aw4 := ciosShiftAw4 aw shiftedOut tk1Off tEnd
  let finalMem := ciosShiftMemory mem aw reductionCarry shiftedOut tk1Off tEnd
  let finalAw := ciosShiftAw aw shiftedOut tk1Off tEnd
  have hreadEnd := readWords1_coverage mem aw tEnd hcovered hawFit htEndFit
  have hcov1 : MemoryCovered mem aw1 ∧ aw1.toNat * 32 < UInt256.size := by
    simpa only [aw1, ciosShiftAw1] using hreadEnd
  have hgapShifted : shiftedOut.toNat - mem.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite1 := write32_coverage
    (ciosShiftSum mem aw reductionCarry tEnd) mem aw1 shiftedOut
    hcov1.1 hcov1.2 hshiftedFit hgapShifted
  have hmem1Size : mem1.size = mem.size := by
    dsimp [mem1, ciosShiftMem1]
    exact write_size_of_inBounds_from _ _ 0 shiftedOut.toNat 32
      (by decide) (by rw [toByteArray_size]) hshiftedWrite
  have hcov2 : MemoryCovered mem1 aw2 ∧ aw2.toNat * 32 < UInt256.size := by
    simpa only [aw1, mem1, aw2, ciosShiftMem1, ciosShiftAw2, readWords1] using hwrite1
  have hreadTk1 := readWords1_coverage mem1 aw2 tk1Off hcov2.1 hcov2.2 htk1Fit
  have hcov3 : MemoryCovered mem1 aw3 ∧ aw3.toNat * 32 < UInt256.size := by
    simpa only [aw3, ciosShiftAw3] using hreadTk1
  have hgapEnd : tEnd.toNat - mem1.size < USize.size := by
    rw [hmem1Size, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite2 := write32_coverage
    (ciosShiftTk1 mem aw reductionCarry shiftedOut tk1Off tEnd +
      ciosShiftOverflow mem aw reductionCarry tEnd)
    mem1 aw3 tEnd hcov3.1 hcov3.2 htEndFit hgapEnd
  have hmem2Size : mem2.size = mem.size := by
    dsimp [mem2, ciosShiftMem2]
    rw [show ciosShiftMem1 mem aw reductionCarry shiftedOut tEnd = mem1 by rfl]
    rw [write_size_of_inBounds_from _ _ 0 tEnd.toNat 32
      (by decide) (by rw [toByteArray_size]) (by rw [hmem1Size]; exact htEndWrite)]
    exact hmem1Size
  have hcov4 : MemoryCovered mem2 aw4 ∧ aw4.toNat * 32 < UInt256.size := by
    simpa only [mem1, mem2, aw3, aw4, ciosShiftMem2, ciosShiftAw4, readWords1]
      using hwrite2
  have hgapTk1 : tk1Off.toNat - mem2.size < USize.size := by
    rw [hmem2Size, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite3 := write32_coverage (⟨0⟩ : UInt256) mem2 aw4 tk1Off
    hcov4.1 hcov4.2 htk1Fit hgapTk1
  have hfinalSize : finalMem.size = mem.size := by
    dsimp [finalMem, ciosShiftMemory]
    rw [show ciosShiftMem2 mem aw reductionCarry shiftedOut tk1Off tEnd = mem2 by rfl]
    rw [write_size_of_inBounds_from _ _ 0 tk1Off.toNat 32
      (by decide) (by rw [toByteArray_size]) (by rw [hmem2Size]; exact htk1Write)]
    exact hmem2Size
  have hcovFinal : MemoryCovered finalMem finalAw ∧
      finalAw.toNat * 32 < UInt256.size := by
    simpa only [mem2, aw4, finalMem, finalAw, ciosShiftMemory, ciosShiftAw, readWords1]
      using hwrite3
  exact {
    aw2Covered := by simpa only [mem1, aw2] using hcov2.1
    aw2Fit := by simpa only [aw2] using hcov2.2
    finalCovered := by simpa only [finalMem, finalAw] using hcovFinal.1
    finalFit := by simpa only [finalAw] using hcovFinal.2
    mem1Size := hmem1Size
    mem2Size := hmem2Size
    finalSize := hfinalSize }

/-- Coverage and active-word fit propagate through any finite multiply pass. -/
theorem multiplyPassIterate_coverage
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsteps : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size) :
    MemoryCovered (multiplyPassIterate a n state).memory
        (multiplyPassIterate a n state).activeWords ∧
      (multiplyPassIterate a n state).activeWords.toNat * 32 < UInt256.size := by
  induction n generalizing state with
  | zero => exact ⟨hcovered, hawFit⟩
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hfirst := hsteps 0 (by omega)
      have hnext := multiplyPassAdvance_coverage a state hcovered hawFit
        hfirst.1 hfirst.2.1 hfirst.2.2
      have htail : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
            current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
            current.resultPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        have heq : multiplyPassIterate a j next =
            multiplyPassIterate a (j + 1) state := by
          simpa only [next] using multiplyPassIterate_advance a j state
        rw [heq]
        exact hsteps (j + 1) (by omega)
      simpa only [multiplyPassIterate, next] using ih next hnext.1 hnext.2 htail

/-- Coverage and active-word fit likewise propagate through reduction columns. -/
theorem schoolbookIterate_coverage
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsteps : ∀ j, j < n →
      let current := schoolbookIterate a j state
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size) :
    MemoryCovered (schoolbookIterate a n state).memory
        (schoolbookIterate a n state).activeWords ∧
      (schoolbookIterate a n state).activeWords.toNat * 32 < UInt256.size := by
  induction n generalizing state with
  | zero => exact ⟨hcovered, hawFit⟩
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hfirst := hsteps 0 (by omega)
      have hnext := schoolbookAdvance_coverage a state hcovered hawFit
        hfirst.1 hfirst.2.1 hfirst.2.2.1 hfirst.2.2.2
      have htail : ∀ j, j < n →
          let current := schoolbookIterate a j next
          current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
            current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
            (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
            (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
        intro j hj
        have heq : schoolbookIterate a j next =
            schoolbookIterate a (j + 1) state := by
          simpa only [next] using schoolbookIterate_advance a j state
        rw [heq]
        exact hsteps (j + 1) (by omega)
      simpa only [schoolbookIterate, next] using ih next hnext.1 hnext.2 htail

/-- Covered reduction execution discharges every guarded prior-result load used by the generated
collector. -/
theorem schoolbookReadFacts_of_coverage
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsteps : ∀ j, j < n →
      let current := schoolbookIterate a j state
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size) :
    ∀ j, j < n →
      let current := schoolbookIterate a j state
      current.resultPtr.toNat < current.memory.size ∧
        ¬ current.resultPtr ≥
          readWords1 current.activeWords current.operandPtr * ⟨32⟩ := by
  intro j hj
  let current := schoolbookIterate a j state
  have hprefixSteps : ∀ i, i < j →
      let prior := schoolbookIterate a i state
      prior.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        prior.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr prior.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr prior.resultPtr).toNat + 32 ≤ prior.memory.size := by
    intro i hi
    have h := hsteps i (by omega)
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hcurrent := schoolbookIterate_coverage a j state hcovered hawFit hprefixSteps
  have hstep := hsteps j hj
  have hoperand := readWords1_coverage current.memory current.activeWords current.operandPtr
    (by simpa only [current] using hcurrent.1)
    (by simpa only [current] using hcurrent.2)
    (by simpa only [current] using hstep.1)
  have hresultWord : current.resultPtr.toNat + 32 ≤ current.memory.size := by
    simpa only [current] using hstep.2.2.2.2
  exact ⟨by omega, wordBelowActive_of_covered current.memory
    (readWords1 current.activeWords current.operandPtr) current.resultPtr
    hoperand.1 hoperand.2 hresultWord⟩

/-- The call-level definition of the completed multiply pass is exactly `columns` generated
columns, including the final explicit advance. -/
theorem ciosMultiplyFinal_eq_iterate
    (columns : Nat) (bP tP : UInt256) (state : CIOSOuterState)
    (hcolumns : 0 < columns) :
    ciosMultiplyFinal columns bP tP state =
      multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff)
        columns (ciosMultiplyInitial bP tP state) := by
  unfold ciosMultiplyFinal
  rw [multiplyPassAdvance_iterate]
  congr 2
  omega

/-- Likewise, the completed non-peeled reduction pass contains exactly `columns - 1` columns. -/
theorem ciosReductionFinal_eq_iterate
    (columns : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) (hcolumns : 1 < columns) :
    ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state =
      schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 1)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state) := by
  unfold ciosReductionFinal
  rw [schoolbookAdvance_iterate]
  congr 2
  omega

/-- Concrete memory and pointer geometry shared by every multi-limb CIOS outer iteration. -/
structure CIOSOuterLayout
    (columns : Nat)
    (bP tP tEnd tk1Off nP tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop where
  columnsGtOne : 1 < columns
  covered : MemoryCovered state.memory state.activeWords
  activeFit : state.activeWords.toNat * 32 < UInt256.size
  scratchFrontier : tk1Off.toNat + 32 ≤ state.memory.size
  scratchFit : tk1Off.toNat + 32 + 31 < UInt256.size
  aFit : state.aOff.toNat + 32 + 31 < UInt256.size
  bFit : bP.toNat + 32 * columns + 31 < UInt256.size
  reductionOperandFit :
    (nBefore + ⟨64⟩).toNat + 32 * (columns - 1) + 31 < UInt256.size
  nPFit : nP.toNat + 32 + 31 < UInt256.size
  multiplyStop : tEnd.toNat = tP.toNat + 32 * columns
  reductionStop : tEnd.toNat = tOff.toNat + 32 * (columns - 1)
  tOffLo : 32 ≤ tOff.toNat
  tk1OffEq : tk1Off.toNat = tEnd.toNat + 32
  shiftedOutEq : shiftedOut.toNat + 32 = tEnd.toNat

/-- The complete generated CIOS outer transition preserves covered memory, active-word
representability, and the exact scratch-buffer size. -/
theorem ciosOuterAdvance_coverage_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    MemoryCovered
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).memory
        (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).activeWords ∧
      (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).activeWords.toNat * 32 < UInt256.size ∧
      (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state).memory.size = state.memory.size := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have houter := readWords1_coverage state.memory state.activeWords state.aOff
    layout.covered layout.activeFit layout.aFit
  have hmultiplyInitial :
      MemoryCovered multiplyInitial.memory multiplyInitial.activeWords ∧
        multiplyInitial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [multiplyInitial, ciosMultiplyInitial, ciosOuterAw] using houter
  have hmultiplyBound : tP.toNat + 32 * columns + 31 < UInt256.size := by
    have hscratch := layout.scratchFit
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hmultiplyRange : tP.toNat + 32 * columns ≤ state.memory.size := by
    have hfrontier := layout.scratchFrontier
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hmultiplyInBounds := multiplyPassIterate_inBounds ai columns multiplyInitial
    (by simpa only [multiplyInitial, ciosMultiplyInitial] using
      (show tP.toNat + 32 * columns < UInt256.size by omega))
    (by simpa only [multiplyInitial, ciosMultiplyInitial] using hmultiplyRange)
  have hmultiplySteps : ∀ j, j < columns →
      let current := multiplyPassIterate ai j multiplyInitial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := multiplyPassIterate_operandPtr_toNat ai j multiplyInitial (by
      simpa only [multiplyInitial, ciosMultiplyInitial] using
        (show bP.toNat + 32 * j < UInt256.size by
          have hbound := layout.bFit
          omega))
    have hresult := multiplyPassIterate_resultPtr_toNat ai j multiplyInitial (by
      simpa only [multiplyInitial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * j < UInt256.size by omega))
    refine ⟨?_, ?_, ?_⟩
    · rw [hop]
      dsimp [multiplyInitial, ciosMultiplyInitial]
      have hbound := layout.bFit
      omega
    · rw [hresult]
      dsimp [multiplyInitial, ciosMultiplyInitial]
      omega
    · exact hmultiplyInBounds.1 j hj
  have hmultiplyCoverage := multiplyPassIterate_coverage ai columns multiplyInitial
    hmultiplyInitial.1 hmultiplyInitial.2 hmultiplySteps
  have hmultiplyFinalEq : multiplyFinal = multiplyPassIterate ai columns multiplyInitial := by
    simpa only [ai, multiplyInitial, multiplyFinal] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have hc := layout.columnsGtOne
        omega)
  have hmultiplyFinalCoverage :
      MemoryCovered multiplyFinal.memory multiplyFinal.activeWords ∧
        multiplyFinal.activeWords.toNat * 32 < UInt256.size := by
    rw [hmultiplyFinalEq]
    exact hmultiplyCoverage
  have hmultiplyFinalSize : multiplyFinal.memory.size = state.memory.size := by
    rw [hmultiplyFinalEq]
    rw [hmultiplyInBounds.2]
    rfl
  have htEndFit : tEnd.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have heq := layout.tk1OffEq
    omega
  have htPFit : tP.toNat + 32 + 31 < UInt256.size := by
    have hc := layout.columnsGtOne
    omega
  have htEndWrite : tEnd.toNat + 32 ≤ multiplyFinal.memory.size := by
    rw [hmultiplyFinalSize]
    have hfrontier := layout.scratchFrontier
    have heq := layout.tk1OffEq
    omega
  have hboundary := ciosBoundary_coverage multiplyFinal.memory multiplyFinal.activeWords
    tEnd multiplyFinal.carry tk1Off tP nP hmultiplyFinalCoverage.1
    hmultiplyFinalCoverage.2
    htEndFit layout.scratchFit htPFit layout.nPFit
    htEndWrite
    (by rw [hmultiplyFinalSize]; exact layout.scratchFrontier)
  have hreductionInitial :
      MemoryCovered reductionInitial.memory reductionInitial.activeWords ∧
        reductionInitial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [reductionInitial, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosAfterBoundaryAw, multiplyFinal] using
      And.intro hboundary.finalCovered hboundary.finalFit
  have hreductionInitialSize : reductionInitial.memory.size = state.memory.size := by
    dsimp [reductionInitial, ciosReductionInitial, ciosAfterBoundaryMemory]
    rw [show ciosMultiplyFinal columns bP tP state = multiplyFinal by rfl]
    exact hboundary.mem2Size.trans hmultiplyFinalSize
  have hreductionRange : tOff.toNat + 32 * (columns - 1) ≤
      reductionInitial.memory.size := by
    have hstop := layout.reductionStop
    have hsize := hreductionInitialSize
    have hfrontier := layout.scratchFrontier
    have heq := layout.tk1OffEq
    omega
  have hreductionBound :
      tOff.toNat + 32 * (columns - 1) + 31 < UInt256.size := by
    have hstop := layout.reductionStop
    have hfit := layout.scratchFit
    have heq := layout.tk1OffEq
    omega
  have hreductionOperandBound := layout.reductionOperandFit
  have hreductionInBounds := schoolbookIterate_inBounds factor (columns - 1)
    reductionInitial
    (by simpa only [reductionInitial, ciosReductionInitial] using layout.tOffLo)
    (by simpa only [reductionInitial, ciosReductionInitial] using
      (show tOff.toNat + 32 * (columns - 1) < UInt256.size by omega))
    (by simpa only [reductionInitial, ciosReductionInitial] using hreductionRange)
  have hreductionSteps : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j reductionInitial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := schoolbookIterate_operandPtr_toNat factor j reductionInitial (by
      simpa only [reductionInitial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by omega))
    have hresult := schoolbookIterate_resultPtr_toNat factor j reductionInitial (by
      simpa only [reductionInitial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by omega))
    have hresultLo : 32 ≤
        (schoolbookIterate factor j reductionInitial).resultPtr.toNat := by
      rw [hresult]
      simp only [reductionInitial, ciosReductionInitial]
      have hlo := layout.tOffLo
      omega
    have hwritePtr := schoolbookWritePtr_toNat
      (schoolbookIterate factor j reductionInitial).resultPtr hresultLo
    refine ⟨?_, ?_, ?_, (hreductionInBounds.1 j hj).2⟩
    · rw [hop]
      dsimp [reductionInitial, ciosReductionInitial]
      have hbound := layout.reductionOperandFit
      omega
    · rw [hresult]
      dsimp [reductionInitial, ciosReductionInitial]
      omega
    · rw [hwritePtr]
      rw [hresult]
      dsimp [reductionInitial, ciosReductionInitial]
      omega
  have hreductionCoverage := schoolbookIterate_coverage factor (columns - 1)
    reductionInitial hreductionInitial.1 hreductionInitial.2 hreductionSteps
  have hreductionFinalEq :
      reductionFinal = schoolbookIterate factor (columns - 1) reductionInitial := by
    simpa only [factor, reductionInitial, reductionFinal] using
      ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        state layout.columnsGtOne
  have hreductionFinalCoverage :
      MemoryCovered reductionFinal.memory reductionFinal.activeWords ∧
        reductionFinal.activeWords.toNat * 32 < UInt256.size := by
    rw [hreductionFinalEq]
    exact hreductionCoverage
  have hreductionFinalSize : reductionFinal.memory.size = state.memory.size := by
    rw [hreductionFinalEq, hreductionInBounds.2, hreductionInitialSize]
  have hshiftedFit : shiftedOut.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have hshifted := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have hshiftedWrite : shiftedOut.toNat + 32 ≤ reductionFinal.memory.size := by
    rw [hreductionFinalSize]
    have hfrontier := layout.scratchFrontier
    have hshifted := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have htEndShiftWrite : tEnd.toNat + 32 ≤ reductionFinal.memory.size := by
    rw [hreductionFinalSize]
    have hfrontier := layout.scratchFrontier
    have htk1 := layout.tk1OffEq
    omega
  have hshift := ciosShift_coverage reductionFinal.memory reductionFinal.activeWords
    reductionFinal.carry shiftedOut tk1Off tEnd hreductionFinalCoverage.1
    hreductionFinalCoverage.2 hshiftedFit layout.scratchFit htEndFit
    hshiftedWrite
    (by rw [hreductionFinalSize]; exact layout.scratchFrontier)
    htEndShiftWrite
  simpa only [ciosOuterAdvance, reductionFinal] using
    And.intro hshift.finalCovered
      (And.intro hshift.finalFit (hshift.finalSize.trans hreductionFinalSize))

/-- One successful outer transition re-establishes the same layout once the next source-limb
address is known to fit. -/
theorem CIOSOuterLayout.advance
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (hnextAFit :
      (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state).aOff.toNat + 32 + 31 < UInt256.size) :
    CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore shiftedOut
      (ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state) := by
  have hadvance := ciosOuterAdvance_coverage_of_layout columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore shiftedOut state layout
  refine {
    columnsGtOne := layout.columnsGtOne
    covered := hadvance.1
    activeFit := hadvance.2.1
    scratchFrontier := ?_
    scratchFit := layout.scratchFit
    aFit := hnextAFit
    bFit := layout.bFit
    reductionOperandFit := layout.reductionOperandFit
    nPFit := layout.nPFit
    multiplyStop := layout.multiplyStop
    reductionStop := layout.reductionStop
    tOffLo := layout.tOffLo
    tk1OffEq := layout.tk1OffEq
    shiftedOutEq := layout.shiftedOutEq }
  rw [hadvance.2.2]
  exact layout.scratchFrontier

/-- Coverage and exact memory size therefore hold after any finite number of concrete CIOS outer
iterations. -/
theorem ciosOuterIterate_layout
    (iterations columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state)
    (haFit : ∀ i, i ≤ iterations →
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut i state).aOff.toNat + 32 + 31 < UInt256.size) :
    CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore shiftedOut
        (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state) ∧
      (ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut iterations state).memory.size = state.memory.size := by
  induction iterations with
  | zero => exact ⟨layout, rfl⟩
  | succ iterations ih =>
      let current := ciosOuterIterate columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore shiftedOut iterations state
      have hcurrent := ih (fun i hi => haFit i (by omega))
      have hnextLayout := CIOSOuterLayout.advance columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut current hcurrent.1 (by
          simpa only [current, ciosOuterIterate] using haFit (iterations + 1) (by omega))
      refine ⟨?_, ?_⟩
      · simpa only [current, ciosOuterIterate] using hnextLayout
      · have hadvance := ciosOuterAdvance_coverage_of_layout columns bP tP tEnd tk1Off
          nP n0inv tOff nBefore shiftedOut current hcurrent.1
        simpa only [current, ciosOuterIterate] using hadvance.2.2.trans hcurrent.2

/-- The multiply collector always splits into its first low word and the remaining higher words. -/
theorem multiplyPassOutputWords_recompose_head
    (a : UInt256) (columns : Nat) (state : MultiplyPassState)
    (hcolumns : 0 < columns) :
    Modexp.wordLimbsToNat (multiplyPassOutputWords a columns state) =
      (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toNat +
        UInt256.size *
          Modexp.wordLimbsToNat (multiplyPassOutputWords a (columns - 1)
            (multiplyPassAdvance a state)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : columns ≠ 0)
  rfl

/-- Generated reduction columns preserve a padded word above every in-bounds destination. -/
theorem schoolbookIterate_read_above
    (a : UInt256) (n : Nat) (state : SchoolbookState) (read : Nat)
    (hwrites : ∀ j, j < n →
      let current := schoolbookIterate a j state
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ read) :
    (schoolbookIterate a n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          let current := schoolbookIterate a j next
          (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
            (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ read := by
        intro j hj
        have heq : schoolbookIterate a j next =
            schoolbookIterate a (j + 1) state := by
          simpa only [next] using schoolbookIterate_advance a j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      rw [schoolbookIterate, hrest]
      exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
        hfirst.1 hfirst.2

/-- Generated CIOS multiply columns satisfy the same framing property. -/
theorem multiplyPassIterate_read_above
    (a : UInt256) (n : Nat) (state : MultiplyPassState) (read : Nat)
    (hwrites : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ read) :
    (multiplyPassIterate a n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.resultPtr.toNat + 32 ≤ current.memory.size ∧
            current.resultPtr.toNat + 32 ≤ read := by
        intro j hj
        have heq : multiplyPassIterate a j next =
            multiplyPassIterate a (j + 1) state := by
          simpa only [next] using multiplyPassIterate_advance a j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      rw [multiplyPassIterate, hrest]
      exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
        hfirst.1 hfirst.2

/-- Multiply columns also preserve an earlier word below every subsequent in-bounds write. -/
theorem multiplyPassIterate_read_below
    (a : UInt256) (n : Nat) (state : MultiplyPassState) (read : Nat)
    (hwrites : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size ∧
        read + 32 ≤ current.resultPtr.toNat) :
    (multiplyPassIterate a n state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.resultPtr.toNat + 32 ≤ current.memory.size ∧
            read + 32 ≤ current.resultPtr.toNat := by
        intro j hj
        have heq : multiplyPassIterate a j next =
            multiplyPassIterate a (j + 1) state := by
          simpa only [next] using multiplyPassIterate_advance a j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstInBounds : state.resultPtr.toNat + 32 ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hfirst.1
      rw [multiplyPassIterate, hrest]
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirst.2

/-- Consecutive memory words, represented in the same little-endian limb order as the generated
collectors. -/
def memoryWordsFrom (mem : ByteArray) (ptr : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 =>
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr) ::
        memoryWordsFrom mem (ptr + 32) n

/-- Equality of one-word ranges recovers equality of their underlying natural values. -/
theorem memoryWordNat_eq_of_memoryWordsFrom_one_eq
    (left right : ByteArray) (ptr : Nat)
    (h : memoryWordsFrom left ptr 1 = memoryWordsFrom right ptr 1) :
    Modexp.MultiLimbMemoryModel.memoryWordNat left ptr =
      Modexp.MultiLimbMemoryModel.memoryWordNat right ptr := by
  have hhead := congrArg List.head? h
  have hwords : UInt256.ofNat
        (Modexp.MultiLimbMemoryModel.memoryWordNat left ptr) =
      UInt256.ofNat
        (Modexp.MultiLimbMemoryModel.memoryWordNat right ptr) := by
    apply Option.some.inj
    simpa only [memoryWordsFrom] using hhead
  have hnats := congrArg UInt256.toNat hwords
  simpa only [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] using hnats

/-- A complete consecutive word range is unchanged by an in-bounds 32-byte write below it. -/
theorem memoryWordsFrom_write_below
    (src base : ByteArray) (dest ptr n : Nat)
    (hsrc : 32 ≤ src.size) (hdest : dest + 32 ≤ base.size)
    (hbelow : dest + 32 ≤ ptr) :
    memoryWordsFrom (src.write 0 base dest 32) ptr n =
      memoryWordsFrom base ptr n := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih =>
      simp only [memoryWordsFrom]
      rw [show
        Modexp.MultiLimbMemoryModel.memoryWordNat (src.write 0 base dest 32) ptr =
            Modexp.MultiLimbMemoryModel.memoryWordNat base ptr by
          unfold Modexp.MultiLimbMemoryModel.memoryWordNat
          rw [write32_read_above_padded src base dest ptr hsrc hdest hbelow]]
      rw [ih (ptr + 32) (by omega)]

/-- A complete consecutive word range is also unchanged by a write starting above it. -/
theorem memoryWordsFrom_write_above
    (src base : ByteArray) (dest ptr n : Nat)
    (hsrc : 32 ≤ src.size) (hdest : dest ≤ base.size)
    (habove : ptr + 32 * n ≤ dest) :
    memoryWordsFrom (src.write 0 base dest 32) ptr n =
      memoryWordsFrom base ptr n := by
  induction n generalizing ptr with
  | zero => rfl
  | succ n ih =>
      simp only [memoryWordsFrom]
      rw [show
        Modexp.MultiLimbMemoryModel.memoryWordNat (src.write 0 base dest 32) ptr =
            Modexp.MultiLimbMemoryModel.memoryWordNat base ptr by
          unfold Modexp.MultiLimbMemoryModel.memoryWordNat
          rw [write32_read_below src base dest ptr hsrc hdest (by omega)]]
      rw [ih (ptr + 32) (by omega)]

/-- The prior-result collector of a reduction pass is exactly the consecutive range present before
the pass.  Earlier reduction columns write one word below every later source word. -/
theorem schoolbookPriorResultWords_eq_initialMemory
    (a : UInt256) (n : Nat) (state : SchoolbookState)
    (hptrLo : 32 ≤ state.resultPtr.toNat)
    (hptrHi : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hreads : ∀ j, j < n →
      let current := schoolbookIterate a j state
      current.resultPtr.toNat < current.memory.size ∧
        ¬ current.resultPtr ≥
          readWords1 current.activeWords current.operandPtr * ⟨32⟩)
    (hwrites : ∀ j, j < n →
      let current := schoolbookIterate a j state
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size) :
    schoolbookPriorResultWords a n state =
      memoryWordsFrom state.memory state.resultPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := schoolbookAdvance a state
      have hstepPtr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        exact uadd_word_lit32_toNat _ (by omega)
      have htailReads : ∀ j, j < n →
          let current := schoolbookIterate a j next
          current.resultPtr.toNat < current.memory.size ∧
            ¬ current.resultPtr ≥
              readWords1 current.activeWords current.operandPtr * ⟨32⟩ := by
        intro j hj
        have heq : schoolbookIterate a j next =
            schoolbookIterate a (j + 1) state := by
          simpa only [next] using schoolbookIterate_advance a j state
        rw [heq]
        exact hreads (j + 1) (by omega)
      have htailWrites : ∀ j, j < n →
          let current := schoolbookIterate a j next
          (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size := by
        intro j hj
        have heq : schoolbookIterate a j next =
            schoolbookIterate a (j + 1) state := by
          simpa only [next] using schoolbookIterate_advance a j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstepPtr]; omega) (by rw [hstepPtr]; omega)
        htailReads htailWrites
      have hfirstRead := hreads 0 (by omega)
      have hfirstWrite := hwrites 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
              state.resultPtr state.carry).2.1 =
            UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                state.memory state.resultPtr.toNat) := by
        change readWord state.memory (readWords1 state.activeWords state.operandPtr)
            state.resultPtr = UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                state.memory state.resultPtr.toNat)
        apply u256_inj
        rw [readWord_toNat_of_valid]
        · rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
        · simpa only [schoolbookIterate] using hfirstRead.1
        · simpa only [schoolbookIterate] using hfirstRead.2
      have hframeRaw := memoryWordsFrom_write_below
        (schoolbookStep state.memory state.activeWords state.operandPtr
          state.resultPtr a state.carry).1.toByteArray
        state.memory (schoolbookWritePtr state.resultPtr).toNat next.resultPtr.toNat n
        (by rw [toByteArray_size])
        (by simpa only [schoolbookIterate] using hfirstWrite)
        (by rw [schoolbookWritePtr_toNat _ hptrLo, hstepPtr]; omega)
      have hframe : memoryWordsFrom next.memory next.resultPtr.toNat n =
          memoryWordsFrom state.memory next.resultPtr.toNat n := by
        simpa only [next, schoolbookAdvance, schoolbookMemory] using hframeRaw
      simp only [schoolbookPriorResultWords, memoryWordsFrom]
      change
        (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).2.1 ::
            schoolbookPriorResultWords a n next =
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                state.memory state.resultPtr.toNat) ::
            memoryWordsFrom state.memory (state.resultPtr.toNat + 32) n
      rw [hhead, htail, hframe, hstepPtr]

/-- A completed multiply pass leaves exactly its collector outputs in its contiguous destination
range.  This statement follows the evolving generated memory, including every intermediate write.
-/
theorem multiplyPassOutputWords_eq_finalMemory
    (a : UInt256) (n : Nat) (state : MultiplyPassState)
    (hptr : state.resultPtr.toNat + 32 * n < UInt256.size)
    (hwrites : ∀ j, j < n →
      let current := multiplyPassIterate a j state
      current.resultPtr.toNat + 32 ≤ current.memory.size) :
    multiplyPassOutputWords a n state =
      memoryWordsFrom (multiplyPassIterate a n state).memory state.resultPtr.toNat n := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      let next := multiplyPassAdvance a state
      have hstepPtr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        exact uadd_word_lit32_toNat _ (by omega)
      have htailWrites : ∀ j, j < n →
          let current := multiplyPassIterate a j next
          current.resultPtr.toNat + 32 ≤ current.memory.size := by
        intro j hj
        have heq : multiplyPassIterate a j next =
            multiplyPassIterate a (j + 1) state := by
          simpa only [next] using multiplyPassIterate_advance a j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hstepPtr]; omega) htailWrites
      have hlater :
          (multiplyPassIterate a n next).memory.readWithPadding state.resultPtr.toNat 32 =
            next.memory.readWithPadding state.resultPtr.toNat 32 := by
        apply multiplyPassIterate_read_below
        intro j hj
        have hwrite := htailWrites j hj
        have hcurrentPtr := multiplyPassIterate_resultPtr_toNat a j next (by
          rw [hstepPtr]
          omega)
        exact ⟨hwrite, by rw [hcurrentPtr, hstepPtr]; omega⟩
      have hstored :
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory state.resultPtr.toNat =
            (schoolbookStep state.memory state.activeWords state.operandPtr
              state.resultPtr a state.carry).1.toNat := by
        apply multiplyPassMemory_word
        have hwrite := hwrites 0 (by omega)
        have hle : state.resultPtr.toNat ≤ state.memory.size := by
          simpa only [multiplyPassIterate] using (show
            (multiplyPassIterate a 0 state).resultPtr.toNat ≤
              (multiplyPassIterate a 0 state).memory.size by omega)
        simp [Nat.sub_eq_zero_of_le hle, USize.size]
      have hhead :
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                (multiplyPassIterate a n next).memory state.resultPtr.toNat) =
            (schoolbookStep state.memory state.activeWords state.operandPtr
              state.resultPtr a state.carry).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt]
        · rw [Modexp.MultiLimbMemoryModel.memoryWordNat]
          rw [hlater]
          exact hstored
        · exact memoryWordNat_lt_size _ _
      simp only [multiplyPassOutputWords, multiplyPassIterate, memoryWordsFrom]
      change
        (schoolbookStep state.memory state.activeWords state.operandPtr
            state.resultPtr a state.carry).1 :: multiplyPassOutputWords a n next =
          UInt256.ofNat
              (Modexp.MultiLimbMemoryModel.memoryWordNat
                (multiplyPassIterate a n next).memory state.resultPtr.toNat) ::
            memoryWordsFrom (multiplyPassIterate a n next).memory
              (state.resultPtr.toNat + 32) n
      rw [← hhead, htail, ← hstepPtr]

/-- The concrete CIOS boundary writes occur above the reduction source range, so the reduction
prior-result collector is exactly the tail emitted by the multiply pass. -/
theorem ciosReductionPrior_eq_multiplyTail
    (columns : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState)
    (hcolumns : 1 < columns)
    (htailPtr :
      (multiplyPassAdvance
        (ciosOuterAi state.memory state.activeWords state.aOff)
        (ciosMultiplyInitial bP tP state)).resultPtr.toNat = tOff.toNat)
    (hrangeEnd : tOff.toNat + 32 * (columns - 1) ≤ tEnd.toNat)
    (htEndLeTk1 : tEnd.toNat ≤ tk1Off.toNat)
    (hmultiplyPtr :
      (multiplyPassAdvance
          (ciosOuterAi state.memory state.activeWords state.aOff)
          (ciosMultiplyInitial bP tP state)).resultPtr.toNat +
        32 * (columns - 1) < UInt256.size)
    (hmultiplyWrites : ∀ j, j < columns - 1 →
      let current := multiplyPassIterate
        (ciosOuterAi state.memory state.activeWords state.aOff) j
        (multiplyPassAdvance
          (ciosOuterAi state.memory state.activeWords state.aOff)
          (ciosMultiplyInitial bP tP state))
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (hreductionLo : 32 ≤
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).resultPtr.toNat)
    (hreductionHi :
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state).resultPtr.toNat + 32 * (columns - 1) < UInt256.size)
    (hreductionReads : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state)
      current.resultPtr.toNat < current.memory.size ∧
        ¬ current.resultPtr ≥
          readWords1 current.activeWords current.operandPtr * ⟨32⟩)
    (hreductionWrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state)
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size)
    (htEndInBounds : tEnd.toNat ≤
      (ciosMultiplyFinal columns bP tP state).memory.size)
    (htk1InBounds : tk1Off.toNat ≤
      (ciosBoundaryMem1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).size) :
    schoolbookPriorResultWords
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 1)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state) =
      multiplyPassOutputWords
        (ciosOuterAi state.memory state.activeWords state.aOff) (columns - 1)
        (multiplyPassAdvance
          (ciosOuterAi state.memory state.activeWords state.aOff)
          (ciosMultiplyInitial bP tP state)) := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyTail := multiplyPassAdvance ai (ciosMultiplyInitial bP tP state)
  let final := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reduction := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hfinal : multiplyPassIterate ai (columns - 1) multiplyTail = final := by
    change multiplyPassIterate ai (columns - 1) multiplyTail =
      ciosMultiplyFinal columns bP tP state
    rw [ciosMultiplyFinal_eq_iterate columns bP tP state (by omega)]
    have hn : columns - 1 + 1 = columns := by omega
    rw [← hn]
    simpa only [multiplyTail] using
      (multiplyPassIterate_advance ai (columns - 1) (ciosMultiplyInitial bP tP state))
  have hmul := multiplyPassOutputWords_eq_finalMemory ai (columns - 1) multiplyTail
    (by simpa only [ai, multiplyTail] using hmultiplyPtr)
    (by simpa only [ai, multiplyTail] using hmultiplyWrites)
  rw [hfinal] at hmul
  have hred := schoolbookPriorResultWords_eq_initialMemory factor (columns - 1) reduction
    (by simpa only [reduction] using hreductionLo)
    (by simpa only [reduction] using hreductionHi)
    (by simpa only [factor, reduction] using hreductionReads)
    (by simpa only [factor, reduction] using hreductionWrites)
  let mem1 := ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry
  have hframe1 := memoryWordsFrom_write_above
    (ciosBoundaryTkNew final.memory final.activeWords tEnd final.carry).toByteArray
    final.memory tEnd.toNat tOff.toNat (columns - 1)
    (by rw [toByteArray_size]) (by simpa only [final] using htEndInBounds) hrangeEnd
  have hframe2 := memoryWordsFrom_write_above
    (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off +
      ciosBoundaryOverflow final.memory final.activeWords tEnd final.carry).toByteArray
    mem1 tk1Off.toNat tOff.toNat (columns - 1)
    (by rw [toByteArray_size]) (by simpa only [final, mem1] using htk1InBounds)
    (by omega)
  have hboundary : memoryWordsFrom reduction.memory tOff.toNat (columns - 1) =
      memoryWordsFrom final.memory tOff.toNat (columns - 1) := by
    have hboth := hframe2.trans hframe1
    simpa only [reduction, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosBoundaryMem2, mem1, final] using hboth
  rw [show
      schoolbookPriorResultWords factor (columns - 1) reduction =
          memoryWordsFrom reduction.memory tOff.toNat (columns - 1) by
        simpa only [reduction] using hred]
  rw [hboundary]
  rw [show tOff.toNat = multiplyTail.resultPtr.toNat by
    simpa only [ai, multiplyTail] using htailPtr.symm]
  exact hmul.symm

/-- The peeled reduction low word is the first concrete multiply output. -/
theorem ciosBoundaryLow_eq_firstMultiplyOutput
    (columns : Nat) (bP tP tEnd tk1Off : UInt256) (state : CIOSOuterState)
    (hcolumns : 0 < columns)
    (hrangeEnd : tP.toNat + 32 ≤ tEnd.toNat)
    (htEndLeTk1 : tEnd.toNat ≤ tk1Off.toNat)
    (hmultiplyPtr :
      (ciosMultiplyInitial bP tP state).resultPtr.toNat + 32 * columns < UInt256.size)
    (hmultiplyWrites : ∀ j, j < columns →
      let current := multiplyPassIterate
        (ciosOuterAi state.memory state.activeWords state.aOff) j
        (ciosMultiplyInitial bP tP state)
      current.resultPtr.toNat + 32 ≤ current.memory.size)
    (htEndInBounds : tEnd.toNat ≤
      (ciosMultiplyFinal columns bP tP state).memory.size)
    (htk1InBounds : tk1Off.toNat ≤
      (ciosBoundaryMem1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).size)
    (hreadSize : tP.toNat <
      (ciosBoundaryMem2
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off).size)
    (hreadAw : ¬ tP ≥
      ciosBoundaryAw4 (ciosMultiplyFinal columns bP tP state).activeWords
        tEnd tk1Off * ⟨32⟩) :
    (ciosBoundaryT0
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords
      tEnd (ciosMultiplyFinal columns bP tP state).carry tk1Off tP).toNat =
      (schoolbookStep state.memory (ciosOuterAw state.activeWords state.aOff)
        bP tP (ciosOuterAi state.memory state.activeWords state.aOff) ⟨0⟩).1.toNat := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  let final := ciosMultiplyFinal columns bP tP state
  let mem1 := ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry
  let mem2 := ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off
  have hmul := multiplyPassOutputWords_eq_finalMemory ai columns initial
    (by simpa only [initial] using hmultiplyPtr)
    (by simpa only [ai, initial] using hmultiplyWrites)
  rw [show multiplyPassIterate ai columns initial = final by
    simpa only [ai, initial, final] using
      (ciosMultiplyFinal_eq_iterate columns bP tP state hcolumns).symm] at hmul
  have hmulHead := congrArg List.head? hmul
  have hfirst :
      (schoolbookStep state.memory (ciosOuterAw state.activeWords state.aOff)
        bP tP ai ⟨0⟩).1 =
          UInt256.ofNat
            (Modexp.MultiLimbMemoryModel.memoryWordNat final.memory tP.toNat) := by
    have hc : columns = columns - 1 + 1 := by omega
    rw [hc] at hmulHead
    apply Option.some.inj
    simpa only [multiplyPassOutputWords, memoryWordsFrom, initial,
      ciosMultiplyInitial] using hmulHead
  have hframe1 := memoryWordsFrom_write_above
    (ciosBoundaryTkNew final.memory final.activeWords tEnd final.carry).toByteArray
    final.memory tEnd.toNat tP.toNat 1
    (by rw [toByteArray_size]) (by simpa only [final] using htEndInBounds)
    (by simpa using hrangeEnd)
  have hframe2 := memoryWordsFrom_write_above
    (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off +
      ciosBoundaryOverflow final.memory final.activeWords tEnd final.carry).toByteArray
    mem1 tk1Off.toNat tP.toNat 1
    (by rw [toByteArray_size]) (by simpa only [final, mem1] using htk1InBounds)
    (by omega)
  have hframeHead := congrArg List.head? (hframe2.trans hframe1)
  have hmem : Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tP.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat final.memory tP.toNat := by
    have hwords : UInt256.ofNat
          (Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tP.toNat) =
        UInt256.ofNat
          (Modexp.MultiLimbMemoryModel.memoryWordNat final.memory tP.toNat) := by
      apply Option.some.inj
      simpa only [memoryWordsFrom, mem2, mem1, ciosBoundaryMem2] using hframeHead
    have hnats := congrArg UInt256.toNat hwords
    simpa only [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] using hnats
  have hload := readWord_toNat_of_valid mem2
    (ciosBoundaryAw4 final.activeWords tEnd tk1Off) tP
    (by simpa only [final, mem2] using hreadSize)
    (by simpa only [final] using hreadAw)
  change (readWord mem2 (ciosBoundaryAw4 final.activeWords tEnd tk1Off) tP).toNat = _
  rw [hload, hmem, hfirst]
  exact (UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)).symm

/-- The reduction pass cannot disturb the upper carry word written by the CIOS boundary block. -/
theorem ciosShiftLow_eq_boundaryUpper
    (columns : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState)
    (hcolumns : 1 < columns)
    (htEndInBounds : tEnd.toNat ≤
      (ciosMultiplyFinal columns bP tP state).memory.size)
    (htEndBeforeTk1 : tEnd.toNat + 32 ≤ tk1Off.toNat)
    (htk1InBounds : tk1Off.toNat ≤
      (ciosBoundaryMem1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).size)
    (hreductionWrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state)
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat)
    (hreadSize : tEnd.toNat <
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).memory.size)
    (hreadAw : ¬ tEnd ≥
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).activeWords * ⟨32⟩) :
    (ciosShiftTk
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).activeWords tEnd).toNat =
      (ciosBoundaryTkNew
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).toNat := by
  let final := ciosMultiplyFinal columns bP tP state
  let mem1 := ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry
  let mem2 := ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reduction := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hstored : Modexp.MultiLimbMemoryModel.memoryWordNat mem1 tEnd.toNat =
      (ciosBoundaryTkNew final.memory final.activeWords tEnd final.carry).toNat := by
    unfold mem1 ciosBoundaryMem1 Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [toByteArray_write_read_back_of_gap]
    · exact fromByteArrayBigEndian_toByteArray _
    · have hle : tEnd.toNat ≤ final.memory.size := by
        simpa only [final] using htEndInBounds
      simp [Nat.sub_eq_zero_of_le hle, USize.size]
  have hframe2 := memoryWordsFrom_write_above
    (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off +
      ciosBoundaryOverflow final.memory final.activeWords tEnd final.carry).toByteArray
    mem1 tk1Off.toNat tEnd.toNat 1
    (by rw [toByteArray_size]) (by simpa only [final, mem1] using htk1InBounds)
    (by simpa using htEndBeforeTk1)
  have hmem2 : Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tEnd.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem1 tEnd.toNat := by
    apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
    simpa only [mem2, ciosBoundaryMem2] using hframe2
  have hpreserved : Modexp.MultiLimbMemoryModel.memoryWordNat
      reductionFinal.memory tEnd.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat reduction.memory tEnd.toNat := by
    have hframe := schoolbookIterate_read_above factor (columns - 1) reduction tEnd.toNat
      (by simpa only [factor, reduction] using hreductionWrites)
    rw [← ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state hcolumns] at hframe
    unfold Modexp.MultiLimbMemoryModel.memoryWordNat
    exact congrArg fromByteArrayBigEndian (by
      simpa only [reductionFinal] using hframe)
  have hload := readWord_toNat_of_valid reductionFinal.memory reductionFinal.activeWords tEnd
    (by simpa only [reductionFinal] using hreadSize)
    (by simpa only [reductionFinal] using hreadAw)
  change (readWord reductionFinal.memory reductionFinal.activeWords tEnd).toNat = _
  rw [hload, hpreserved]
  change Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tEnd.toNat = _
  rw [hmem2, hstored]

/-- The extra boundary carry word likewise survives reduction and the first final-shift write. -/
theorem ciosShiftExtra_eq_boundaryExtra
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (hcolumns : 1 < columns)
    (htk1InBounds : tk1Off.toNat ≤
      (ciosBoundaryMem1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).size)
    (hreductionWrites : ∀ j, j < columns - 1 →
      let current := schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state)
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tk1Off.toNat)
    (hshiftWriteInBounds : shiftedOut.toNat + 32 ≤
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).memory.size)
    (hshiftBelow : shiftedOut.toNat + 32 ≤ tk1Off.toNat)
    (hreadSize : tk1Off.toNat <
      (ciosShiftMem1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state).carry shiftedOut tEnd).size)
    (hreadAw : ¬ tk1Off ≥
      ciosShiftAw2
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state).activeWords shiftedOut tEnd * ⟨32⟩) :
    (ciosShiftTk1
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).activeWords
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).carry shiftedOut tk1Off tEnd).toNat =
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off +
          ciosBoundaryOverflow
            (ciosMultiplyFinal columns bP tP state).memory
            (ciosMultiplyFinal columns bP tP state).activeWords tEnd
            (ciosMultiplyFinal columns bP tP state).carry).toNat := by
  let final := ciosMultiplyFinal columns bP tP state
  let mem1 := ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry
  let mem2 := ciosBoundaryMem2 final.memory final.activeWords tEnd final.carry tk1Off
  let boundaryExtra := ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off +
    ciosBoundaryOverflow final.memory final.activeWords tEnd final.carry
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reduction := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let shiftMem1 := ciosShiftMem1 reductionFinal.memory reductionFinal.activeWords
    reductionFinal.carry shiftedOut tEnd
  have hstored : Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tk1Off.toNat =
      boundaryExtra.toNat := by
    unfold mem2 ciosBoundaryMem2 Modexp.MultiLimbMemoryModel.memoryWordNat
    rw [toByteArray_write_read_back_of_gap]
    · simpa only [boundaryExtra] using fromByteArrayBigEndian_toByteArray
        (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off +
          ciosBoundaryOverflow final.memory final.activeWords tEnd final.carry)
    · have hle : tk1Off.toNat ≤ mem1.size := by
        simpa only [final, mem1] using htk1InBounds
      have hle' : tk1Off.toNat ≤
          (ciosBoundaryMem1 final.memory final.activeWords tEnd final.carry).size := by
        simpa only [mem1] using hle
      simp [Nat.sub_eq_zero_of_le hle', USize.size]
  have hpreserved : Modexp.MultiLimbMemoryModel.memoryWordNat
      reductionFinal.memory tk1Off.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat reduction.memory tk1Off.toNat := by
    have hframe := schoolbookIterate_read_above factor (columns - 1) reduction tk1Off.toNat
      (by simpa only [factor, reduction] using hreductionWrites)
    rw [← ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state hcolumns] at hframe
    unfold Modexp.MultiLimbMemoryModel.memoryWordNat
    exact congrArg fromByteArrayBigEndian (by
      simpa only [reductionFinal] using hframe)
  have hshiftFrame := memoryWordsFrom_write_below
    (ciosShiftSum reductionFinal.memory reductionFinal.activeWords reductionFinal.carry
      tEnd).toByteArray reductionFinal.memory shiftedOut.toNat tk1Off.toNat 1
    (by rw [toByteArray_size])
    (by simpa only [reductionFinal] using hshiftWriteInBounds) hshiftBelow
  have hshiftMem : Modexp.MultiLimbMemoryModel.memoryWordNat shiftMem1 tk1Off.toNat =
      Modexp.MultiLimbMemoryModel.memoryWordNat reductionFinal.memory tk1Off.toNat := by
    apply memoryWordNat_eq_of_memoryWordsFrom_one_eq
    simpa only [shiftMem1, ciosShiftMem1] using hshiftFrame
  have hload := readWord_toNat_of_valid shiftMem1
    (ciosShiftAw2 reductionFinal.activeWords shiftedOut tEnd) tk1Off
    (by simpa only [reductionFinal, shiftMem1] using hreadSize)
    (by simpa only [reductionFinal] using hreadAw)
  change
    (readWord shiftMem1 (ciosShiftAw2 reductionFinal.activeWords shiftedOut tEnd)
      tk1Off).toNat = _
  rw [hload, hshiftMem, hpreserved]
  change Modexp.MultiLimbMemoryModel.memoryWordNat mem2 tk1Off.toNat = _
  rw [hstored]

/-- Cross-phase memory facts needed to identify the words loaded by reduction and final shifting
with the words written by the immediately preceding phase.  These are framing obligations, not
arithmetic assumptions. -/
structure CIOSPhaseLinks
    (columns : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop where
  reductionPrior :
    Modexp.wordLimbsToNat
        (schoolbookPriorResultWords
          (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
          (columns - 1)
          (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state)) =
      Modexp.wordLimbsToNat
        (multiplyPassOutputWords
          (ciosOuterAi state.memory state.activeWords state.aOff) (columns - 1)
          (multiplyPassAdvance
            (ciosOuterAi state.memory state.activeWords state.aOff)
            (ciosMultiplyInitial bP tP state)))
  boundaryLow :
    (ciosBoundaryT0
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords
      tEnd (ciosMultiplyFinal columns bP tP state).carry tk1Off tP).toNat =
      (schoolbookStep state.memory (ciosOuterAw state.activeWords state.aOff)
        bP tP (ciosOuterAi state.memory state.activeWords state.aOff) ⟨0⟩).1.toNat
  shiftLow :
    (ciosShiftTk
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
      tEnd).toNat =
      (ciosBoundaryTkNew
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry).toNat
  shiftExtra :
    (ciosShiftTk1
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
      shiftedOut tk1Off tEnd).toNat =
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off +
          ciosBoundaryOverflow
            (ciosMultiplyFinal columns bP tP state).memory
            (ciosMultiplyFinal columns bP tP state).activeWords tEnd
            (ciosMultiplyFinal columns bP tP state).carry).toNat

/-
structure CIOSReductionPriorBounds
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) where
  columnsGtOne : 1 < columns
  multiplyTailPtr :
    (multiplyPassAdvance
      (ciosOuterAi state.memory state.activeWords state.aOff)
      (ciosMultiplyInitial bP tP state)).resultPtr.toNat = tOff.toNat
  reductionRangeEnd : tOff.toNat + 32 * (columns - 1) ≤ tEnd.toNat
  tEndLeTk1 : tEnd.toNat ≤ tk1Off.toNat
  multiplyTailBound :
    (multiplyPassAdvance
        (ciosOuterAi state.memory state.activeWords state.aOff)
        (ciosMultiplyInitial bP tP state)).resultPtr.toNat +
      32 * (columns - 1) < UInt256.size
  multiplyTailWrites : ∀ j, j < columns - 1 →
    let current := multiplyPassIterate
      (ciosOuterAi state.memory state.activeWords state.aOff) j
      (multiplyPassAdvance
        (ciosOuterAi state.memory state.activeWords state.aOff)
        (ciosMultiplyInitial bP tP state))
    current.resultPtr.toNat + 32 ≤ current.memory.size
  reductionLo : 32 ≤
    (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).resultPtr.toNat
  reductionHi :
    (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).resultPtr.toNat + 32 * (columns - 1) < UInt256.size
  reductionReads : ∀ j, j < columns - 1 →
    let current := schoolbookIterate
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state)
    current.resultPtr.toNat < current.memory.size ∧
      ¬ current.resultPtr ≥ readWords1 current.activeWords current.operandPtr * ⟨32⟩
  reductionWrites : ∀ j, j < columns - 1 →
    let current := schoolbookIterate
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state)
    (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size
  tEndInMultiply : tEnd.toNat ≤ (ciosMultiplyFinal columns bP tP state).memory.size
  tk1InBoundary1 : tk1Off.toNat ≤
    (ciosBoundaryMem1
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry).size

structure CIOSBoundaryLowBounds
    (columns : Nat) (bP tP tEnd tk1Off : UInt256) (state : CIOSOuterState) where
  columnsPositive : 0 < columns
  rangeEnd : tP.toNat + 32 ≤ tEnd.toNat
  tEndLeTk1 : tEnd.toNat ≤ tk1Off.toNat
  multiplyBound :
    (ciosMultiplyInitial bP tP state).resultPtr.toNat +
      32 * columns < UInt256.size
  multiplyWrites : ∀ j, j < columns →
    let current := multiplyPassIterate
      (ciosOuterAi state.memory state.activeWords state.aOff) j
      (ciosMultiplyInitial bP tP state)
    current.resultPtr.toNat + 32 ≤ current.memory.size
  boundaryReadSize : tP.toNat <
    (ciosBoundaryMem2
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry tk1Off).size
  boundaryReadGuard : ¬ tP ≥
    ciosBoundaryAw4 (ciosMultiplyFinal columns bP tP state).activeWords
      tEnd tk1Off * ⟨32⟩

structure CIOSShiftLowBounds
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) where
  columnsGtOne : 1 < columns
  tEndInMultiply : tEnd.toNat ≤ (ciosMultiplyFinal columns bP tP state).memory.size
  tEndBeforeTk1 : tEnd.toNat + 32 ≤ tk1Off.toNat
  tk1InBoundary1 : tk1Off.toNat ≤
    (ciosBoundaryMem1
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry).size
  reductionWritesToEnd : ∀ j, j < columns - 1 →
    let current := schoolbookIterate
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state)
    (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat
  reductionFinalReadSize : tEnd.toNat <
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).memory.size
  reductionFinalReadGuard : ¬ tEnd ≥
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).activeWords * ⟨32⟩

structure CIOSShiftExtraFrameBounds
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) where
  columnsGtOne : 1 < columns
  tk1InBoundary1 : tk1Off.toNat ≤
    (ciosBoundaryMem1
      (ciosMultiplyFinal columns bP tP state).memory
      (ciosMultiplyFinal columns bP tP state).activeWords tEnd
      (ciosMultiplyFinal columns bP tP state).carry).size
  reductionWritesToTk1 : ∀ j, j < columns - 1 →
    let current := schoolbookIterate
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
      (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state)
    (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tk1Off.toNat

def CIOSShiftExtraReadSize
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop :=
  tk1Off.toNat <
    (ciosShiftMem1
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).memory
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).activeWords
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).carry shiftedOut tEnd).size

def CIOSShiftExtraReadGuard
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Prop :=
  ¬ tk1Off ≥
    ciosShiftAw2
      (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore state).activeWords shiftedOut tEnd * ⟨32⟩

structure CIOSShiftExtraReadBounds
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) where
  shiftedWrite : shiftedOut.toNat + 32 ≤
    (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore state).memory.size
  shiftedBelow : shiftedOut.toNat + 32 ≤ tk1Off.toNat
  shiftedReadSize : CIOSShiftExtraReadSize columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state
  shiftedReadGuard : CIOSShiftExtraReadGuard columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state

structure CIOSPhaseLinkBounds
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) where
  prior : CIOSReductionPriorBounds columns bP tP tEnd tk1Off nP n0inv tOff nBefore state
  boundary : CIOSBoundaryLowBounds columns bP tP tEnd tk1Off state
  shift : CIOSShiftLowBounds columns bP tP tEnd tk1Off nP n0inv tOff nBefore state
  extraFrame : CIOSShiftExtraFrameBounds columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore state
  extraRead : CIOSShiftExtraReadBounds columns bP tP tEnd tk1Off nP n0inv tOff
    nBefore shiftedOut state
-/

/-
/-- The concrete outer-iteration layout discharges every framing obligation between generated
CIOS phases. -/
set_option Elab.async false in
theorem ciosPhaseLinks_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    CIOSPhaseLinks columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut state := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hmultiplyBound : tP.toNat + 32 * columns + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hmultiplyRange : tP.toNat + 32 * columns ≤ state.memory.size := by
    have hfrontier := layout.scratchFrontier
    have hstop := layout.multiplyStop
    have htk1 := layout.tk1OffEq
    omega
  have hmultiplyInBounds := multiplyPassIterate_inBounds ai columns multiplyInitial
    (by simpa only [multiplyInitial, ciosMultiplyInitial] using
      (show tP.toNat + 32 * columns < UInt256.size by omega))
    (by simpa only [multiplyInitial, ciosMultiplyInitial] using hmultiplyRange)
  have houter := readWords1_coverage state.memory state.activeWords state.aOff
    layout.covered layout.activeFit layout.aFit
  have hmultiplyInitialCoverage :
      MemoryCovered multiplyInitial.memory multiplyInitial.activeWords ∧
        multiplyInitial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [multiplyInitial, ciosMultiplyInitial, ciosOuterAw] using houter
  have hmultiplySteps : ∀ j, j < columns →
      let current := multiplyPassIterate ai j multiplyInitial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := multiplyPassIterate_operandPtr_toNat ai j multiplyInitial (by
      simpa only [multiplyInitial, ciosMultiplyInitial] using
        (show bP.toNat + 32 * j < UInt256.size by
          have hfit := layout.bFit
          omega))
    have hresult := multiplyPassIterate_resultPtr_toNat ai j multiplyInitial (by
      simpa only [multiplyInitial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * j < UInt256.size by omega))
    refine ⟨?_, ?_, hmultiplyInBounds.1 j hj⟩
    · rw [hop]
      dsimp [multiplyInitial, ciosMultiplyInitial]
      have hfit := layout.bFit
      omega
    · rw [hresult]
      dsimp [multiplyInitial, ciosMultiplyInitial]
      omega
  have hmultiplyCoverage := multiplyPassIterate_coverage ai columns multiplyInitial
    hmultiplyInitialCoverage.1 hmultiplyInitialCoverage.2 hmultiplySteps
  have hmultiplyFinalEq : multiplyFinal = multiplyPassIterate ai columns multiplyInitial := by
    simpa only [ai, multiplyInitial, multiplyFinal] using
      ciosMultiplyFinal_eq_iterate columns bP tP state (by
        have hc := layout.columnsGtOne
        omega)
  have hmultiplyFinalCoverage :
      MemoryCovered multiplyFinal.memory multiplyFinal.activeWords ∧
        multiplyFinal.activeWords.toNat * 32 < UInt256.size := by
    rw [hmultiplyFinalEq]
    exact hmultiplyCoverage
  have hmultiplyFinalSize : multiplyFinal.memory.size = state.memory.size := by
    rw [hmultiplyFinalEq, hmultiplyInBounds.2]
    rfl
  have htEndFit : tEnd.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have heq := layout.tk1OffEq
    omega
  have htPFit : tP.toNat + 32 + 31 < UInt256.size := by
    have hc := layout.columnsGtOne
    omega
  have htEndWrite : tEnd.toNat + 32 ≤ multiplyFinal.memory.size := by
    rw [hmultiplyFinalSize]
    have hfrontier := layout.scratchFrontier
    have heq := layout.tk1OffEq
    omega
  have hboundary := ciosBoundary_coverage multiplyFinal.memory multiplyFinal.activeWords
    tEnd multiplyFinal.carry tk1Off tP nP hmultiplyFinalCoverage.1
    hmultiplyFinalCoverage.2 htEndFit layout.scratchFit htPFit layout.nPFit
    htEndWrite (by rw [hmultiplyFinalSize]; exact layout.scratchFrontier)
  have hreductionInitialCoverage :
      MemoryCovered reductionInitial.memory reductionInitial.activeWords ∧
        reductionInitial.activeWords.toNat * 32 < UInt256.size := by
    simpa only [reductionInitial, ciosReductionInitial, ciosAfterBoundaryMemory,
      ciosAfterBoundaryAw, multiplyFinal] using
      And.intro hboundary.finalCovered hboundary.finalFit
  have hreductionInitialSize : reductionInitial.memory.size = state.memory.size := by
    dsimp [reductionInitial, ciosReductionInitial, ciosAfterBoundaryMemory]
    rw [show ciosMultiplyFinal columns bP tP state = multiplyFinal by rfl]
    exact hboundary.mem2Size.trans hmultiplyFinalSize
  have hreductionBound :
      tOff.toNat + 32 * (columns - 1) + 31 < UInt256.size := by
    have hstop := layout.reductionStop
    have hfit := layout.scratchFit
    have heq := layout.tk1OffEq
    omega
  have hreductionRange : tOff.toNat + 32 * (columns - 1) ≤
      reductionInitial.memory.size := by
    have hstop := layout.reductionStop
    have hsize := hreductionInitialSize
    have hfrontier := layout.scratchFrontier
    have heq := layout.tk1OffEq
    omega
  have hreductionInBounds := schoolbookIterate_inBounds factor (columns - 1)
    reductionInitial
    (by simpa only [reductionInitial, ciosReductionInitial] using layout.tOffLo)
    (by simpa only [reductionInitial, ciosReductionInitial] using
      (show tOff.toNat + 32 * (columns - 1) < UInt256.size by omega))
    (by simpa only [reductionInitial, ciosReductionInitial] using hreductionRange)
  have hreductionSteps : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j reductionInitial
      current.operandPtr.toNat + 32 + 31 < UInt256.size ∧
        current.resultPtr.toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 + 31 < UInt256.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    have hop := schoolbookIterate_operandPtr_toNat factor j reductionInitial (by
      simpa only [reductionInitial, ciosReductionInitial] using
        (show (nBefore + ⟨64⟩).toNat + 32 * j < UInt256.size by
          have hfit := layout.reductionOperandFit
          omega))
    have hresult := schoolbookIterate_resultPtr_toNat factor j reductionInitial (by
      simpa only [reductionInitial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by omega))
    have hresultLo : 32 ≤
        (schoolbookIterate factor j reductionInitial).resultPtr.toNat := by
      rw [hresult]
      dsimp [reductionInitial, ciosReductionInitial]
      have hlo := layout.tOffLo
      omega
    have hwritePtr := schoolbookWritePtr_toNat
      (schoolbookIterate factor j reductionInitial).resultPtr hresultLo
    refine ⟨?_, ?_, ?_, (hreductionInBounds.1 j hj).2,
      (hreductionInBounds.1 j hj).1⟩
    · rw [hop]
      dsimp [reductionInitial, ciosReductionInitial]
      have hfit := layout.reductionOperandFit
      omega
    · rw [hresult]
      dsimp [reductionInitial, ciosReductionInitial]
      omega
    · rw [hwritePtr, hresult]
      dsimp [reductionInitial, ciosReductionInitial]
      omega
  have hreductionReads := schoolbookReadFacts_of_coverage factor (columns - 1)
    reductionInitial hreductionInitialCoverage.1 hreductionInitialCoverage.2
    hreductionSteps
  have hreductionCoverage := schoolbookIterate_coverage factor (columns - 1)
    reductionInitial hreductionInitialCoverage.1 hreductionInitialCoverage.2
    (fun j hj =>
      let h := hreductionSteps j hj
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
  have hreductionFinalEq :
      reductionFinal = schoolbookIterate factor (columns - 1) reductionInitial := by
    simpa only [factor, reductionInitial, reductionFinal] using
      ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off nP n0inv tOff nBefore
        state layout.columnsGtOne
  have hreductionFinalCoverage :
      MemoryCovered reductionFinal.memory reductionFinal.activeWords ∧
        reductionFinal.activeWords.toNat * 32 < UInt256.size := by
    rw [hreductionFinalEq]
    exact hreductionCoverage
  have hreductionFinalSize : reductionFinal.memory.size = state.memory.size := by
    rw [hreductionFinalEq, hreductionInBounds.2, hreductionInitialSize]
  have hshiftedFit : shiftedOut.toNat + 32 + 31 < UInt256.size := by
    have hfit := layout.scratchFit
    have hshifted := layout.shiftedOutEq
    have htk1 := layout.tk1OffEq
    omega
  have hshift := ciosShift_coverage reductionFinal.memory reductionFinal.activeWords
    reductionFinal.carry shiftedOut tk1Off tEnd hreductionFinalCoverage.1
    hreductionFinalCoverage.2 hshiftedFit layout.scratchFit htEndFit
    (by rw [hreductionFinalSize]; have h := layout.scratchFrontier
        have hs := layout.shiftedOutEq; have hk := layout.tk1OffEq; omega)
    (by rw [hreductionFinalSize]; exact layout.scratchFrontier)
    (by rw [hreductionFinalSize]; have h := layout.scratchFrontier
        have hk := layout.tk1OffEq; omega)
  have hmultiplyTailPtr :
      (multiplyPassAdvance ai multiplyInitial).resultPtr.toNat = tOff.toNat := by
    dsimp [multiplyInitial, ciosMultiplyInitial, multiplyPassAdvance]
    rw [uadd_word_lit32_toNat tP (by omega)]
    have hm := layout.multiplyStop
    have hr := layout.reductionStop
    omega
  have hmultiplyTailWrites : ∀ j, j < columns - 1 →
      let current := multiplyPassIterate ai j (multiplyPassAdvance ai multiplyInitial)
      current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro j hj
    simpa only [multiplyPassIterate_advance] using hmultiplyInBounds.1 (j + 1) (by omega)
  have htEndInMultiply : tEnd.toNat ≤ multiplyFinal.memory.size := by
    rw [hmultiplyFinalSize]
    have h := layout.scratchFrontier
    have hk := layout.tk1OffEq
    omega
  have htk1InBoundary1 : tk1Off.toNat ≤
      (ciosBoundaryMem1 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry).size := by
    rw [hboundary.mem1Size, hmultiplyFinalSize]
    have h := layout.scratchFrontier
    omega
  have hboundaryT0Guard : ¬ tP ≥
      ciosBoundaryAw4 multiplyFinal.activeWords tEnd tk1Off * ⟨32⟩ := by
    apply wordBelowActive_of_covered
      (ciosBoundaryMem2 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry tk1Off)
      (ciosBoundaryAw4 multiplyFinal.activeWords tEnd tk1Off) tP
      hboundary.aw4Covered hboundary.aw4Fit
    rw [hboundary.mem2Size, hmultiplyFinalSize]
    have h := layout.scratchFrontier
    have hc := layout.columnsGtOne
    have hm := layout.multiplyStop
    have hk := layout.tk1OffEq
    omega
  have htEndGuard : ¬ tEnd ≥ reductionFinal.activeWords * ⟨32⟩ := by
    apply wordBelowActive_of_covered reductionFinal.memory reductionFinal.activeWords tEnd
      hreductionFinalCoverage.1 hreductionFinalCoverage.2
    rw [hreductionFinalSize]
    have h := layout.scratchFrontier
    have hk := layout.tk1OffEq
    omega
  have htk1ShiftGuard : ¬ tk1Off ≥
      ciosShiftAw2 reductionFinal.activeWords shiftedOut tEnd * ⟨32⟩ := by
    apply wordBelowActive_of_covered
      (ciosShiftMem1 reductionFinal.memory reductionFinal.activeWords reductionFinal.carry
        shiftedOut tEnd)
      (ciosShiftAw2 reductionFinal.activeWords shiftedOut tEnd) tk1Off
      hshift.aw2Covered hshift.aw2Fit
    rw [hshift.mem1Size, hreductionFinalSize]
    exact layout.scratchFrontier
  have hreductionWritesToEnd : ∀ j, j < columns - 1 →
      let current := schoolbookIterate factor j reductionInitial
      (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ current.memory.size ∧
        (schoolbookWritePtr current.resultPtr).toNat + 32 ≤ tEnd.toNat := by
    intro j hj
    dsimp only
    have hstep := hreductionSteps j hj
    have hresult := schoolbookIterate_resultPtr_toNat factor j reductionInitial (by
      simpa only [reductionInitial, ciosReductionInitial] using
        (show tOff.toNat + 32 * j < UInt256.size by omega))
    have hlo : 32 ≤ (schoolbookIterate factor j reductionInitial).resultPtr.toNat := by
      rw [hresult]
      dsimp [reductionInitial, ciosReductionInitial]
      have h := layout.tOffLo
      omega
    rw [schoolbookWritePtr_toNat _ hlo, hresult]
    dsimp [reductionInitial, ciosReductionInitial]
    refine ⟨?_, ?_⟩
    · exact hstep.2.2.2.1
    · have hstop := layout.reductionStop
      omega
  refine {
    reductionPrior := ?_
    boundaryLow := ?_
    shiftLow := ?_
    shiftExtra := ?_ }
  · exact congrArg Modexp.wordLimbsToNat
      (ciosReductionPrior_eq_multiplyTail columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore state layout.columnsGtOne
        (by simpa only [ai, multiplyInitial] using hmultiplyTailPtr)
        (by have h := layout.reductionStop; omega)
        (by have h := layout.tk1OffEq; omega)
        (by rw [hmultiplyTailPtr]; omega)
        (by simpa only [ai, multiplyInitial] using hmultiplyTailWrites)
        (by simpa only [reductionInitial, ciosReductionInitial] using layout.tOffLo)
        (by
          simpa only [reductionInitial, ciosReductionInitial] using
            (show tOff.toNat + 32 * (columns - 1) < UInt256.size by omega))
        (by simpa only [factor, reductionInitial] using hreductionReads)
        (fun j hj => (hreductionInBounds.1 j hj).2)
        (by simpa only [multiplyFinal] using htEndInMultiply)
        (by simpa only [multiplyFinal] using htk1InBoundary1))
  · exact ciosBoundaryLow_eq_firstMultiplyOutput columns bP tP tEnd tk1Off state
      (by have h := layout.columnsGtOne; omega)
      (by
        have hc := layout.columnsGtOne
        have h := layout.multiplyStop
        omega)
      (by have h := layout.tk1OffEq; omega)
      (by simpa only [multiplyInitial, ciosMultiplyInitial] using
        (show tP.toNat + 32 * columns < UInt256.size by omega))
      (by simpa only [ai, multiplyInitial] using hmultiplyInBounds.1)
      (by simpa only [multiplyFinal] using htEndInMultiply)
      (by simpa only [multiplyFinal] using htk1InBoundary1)
      (by
        rw [hboundary.mem2Size, hmultiplyFinalSize]
        have h := layout.scratchFrontier
        have hc := layout.columnsGtOne
        have hm := layout.multiplyStop
        have hk := layout.tk1OffEq
        omega)
      (by simpa only [multiplyFinal] using hboundaryT0Guard)
  · exact ciosShiftLow_eq_boundaryUpper columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore state layout.columnsGtOne
      (by simpa only [multiplyFinal] using htEndInMultiply)
      (by have h := layout.tk1OffEq; omega)
      (by simpa only [multiplyFinal] using htk1InBoundary1)
      (by simpa only [factor, reductionInitial] using hreductionWritesToEnd)
      (by simpa only [reductionFinal] using
        (show tEnd.toNat < reductionFinal.memory.size by
          rw [hreductionFinalSize]
          have h := layout.scratchFrontier
          have hk := layout.tk1OffEq
          omega))
      (by simpa only [reductionFinal] using htEndGuard)
  · exact ciosShiftExtra_eq_boundaryExtra columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore shiftedOut state layout.columnsGtOne
      (by simpa only [multiplyFinal] using htk1InBoundary1)
      (by
        intro j hj
        have h := hreductionWritesToEnd j hj
        exact ⟨h.1, le_trans h.2 (by have hk := layout.tk1OffEq; omega)⟩)
      (by simpa only [reductionFinal] using
        (show shiftedOut.toNat + 32 ≤ reductionFinal.memory.size by
          rw [hreductionFinalSize]
          have h := layout.scratchFrontier
          have hs := layout.shiftedOutEq
          have hk := layout.tk1OffEq
          omega))
      (by
        have hs := layout.shiftedOutEq
        have hk := layout.tk1OffEq
        omega)
      (by simpa only [reductionFinal] using
        (show tk1Off.toNat <
            (ciosShiftMem1 reductionFinal.memory reductionFinal.activeWords
              reductionFinal.carry shiftedOut tEnd).size by
          rw [hshift.mem1Size, hreductionFinalSize]
          have h := layout.scratchFrontier
          omega))
      (by simpa only [reductionFinal] using htk1ShiftGuard)

/-
  refine { prior := ?_, boundary := ?_, shift := ?_, extraFrame := ?_, extraRead := ?_ }
  · exact {
      columnsGtOne := layout.columnsGtOne
      multiplyTailPtr := by simpa only [ai, multiplyInitial] using hmultiplyTailPtr
      reductionRangeEnd := by have h := layout.reductionStop; omega
      tEndLeTk1 := by have h := layout.tk1OffEq; omega
      multiplyTailBound := by rw [hmultiplyTailPtr]; omega
      multiplyTailWrites := by simpa only [ai, multiplyInitial] using hmultiplyTailWrites
      reductionLo := by
        simpa only [reductionInitial, ciosReductionInitial] using layout.tOffLo
      reductionHi := by
        simpa only [reductionInitial, ciosReductionInitial] using
          (show tOff.toNat + 32 * (columns - 1) < UInt256.size by omega)
      reductionReads := by simpa only [factor, reductionInitial] using hreductionReads
      reductionWrites := fun j hj => (hreductionInBounds.1 j hj).2
      tEndInMultiply := by simpa only [multiplyFinal] using htEndInMultiply
      tk1InBoundary1 := by simpa only [multiplyFinal] using htk1InBoundary1 }
  · exact {
      columnsPositive := by have h := layout.columnsGtOne; omega
      rangeEnd := by
        have hc := layout.columnsGtOne
        have h := layout.multiplyStop
        omega
      tEndLeTk1 := by have h := layout.tk1OffEq; omega
      multiplyBound := by
        simpa only [multiplyInitial, ciosMultiplyInitial] using
          (show tP.toNat + 32 * columns < UInt256.size by omega)
      multiplyWrites := by simpa only [ai, multiplyInitial] using hmultiplyInBounds.1
      boundaryReadSize := by
        rw [hboundary.mem2Size, hmultiplyFinalSize]
        have h := layout.scratchFrontier
        have hc := layout.columnsGtOne
        have hm := layout.multiplyStop
        have hk := layout.tk1OffEq
        omega
      boundaryReadGuard := by simpa only [multiplyFinal] using hboundaryT0Guard }
  · exact {
      columnsGtOne := layout.columnsGtOne
      tEndInMultiply := by simpa only [multiplyFinal] using htEndInMultiply
      tEndBeforeTk1 := by have h := layout.tk1OffEq; omega
      tk1InBoundary1 := by simpa only [multiplyFinal] using htk1InBoundary1
      reductionWritesToEnd := by
        simpa only [factor, reductionInitial] using hreductionWritesToEnd
      reductionFinalReadSize := by
        simpa only [reductionFinal] using
          (show tEnd.toNat < reductionFinal.memory.size by
            rw [hreductionFinalSize]
            have h := layout.scratchFrontier
            have hk := layout.tk1OffEq
            omega)
      reductionFinalReadGuard := by simpa only [reductionFinal] using htEndGuard }
  · exact {
      columnsGtOne := layout.columnsGtOne
      tk1InBoundary1 := by simpa only [multiplyFinal] using htk1InBoundary1
      reductionWritesToTk1 := by
        intro j hj
        have h := hreductionWritesToEnd j hj
        exact ⟨h.1, le_trans h.2 (by have hk := layout.tk1OffEq; omega)⟩ }
  · exact {
      shiftedWrite := by
        simpa only [reductionFinal] using
          (show shiftedOut.toNat + 32 ≤ reductionFinal.memory.size by
            rw [hreductionFinalSize]
            have h := layout.scratchFrontier
            have hs := layout.shiftedOutEq
            have hk := layout.tk1OffEq
            omega)
      shiftedBelow := by
        have hs := layout.shiftedOutEq
        have hk := layout.tk1OffEq
        omega
      shiftedReadSize := by
        unfold CIOSShiftExtraReadSize
        simpa only [reductionFinal] using
          (show tk1Off.toNat <
              (ciosShiftMem1 reductionFinal.memory reductionFinal.activeWords
                reductionFinal.carry shiftedOut tEnd).size by
            rw [hshift.mem1Size, hreductionFinalSize]
            have h := layout.scratchFrontier
            omega)
      shiftedReadGuard := by
        unfold CIOSShiftExtraReadGuard
        simpa only [reductionFinal] using htk1ShiftGuard }

theorem ciosPhaseLinks_of_layout
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (layout : CIOSOuterLayout columns bP tP tEnd tk1Off nP tOff nBefore
      shiftedOut state) :
    CIOSPhaseLinks columns bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut state := by
  have bounds := ciosPhaseLinkBounds_of_layout columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore shiftedOut state layout
  let prior := bounds.prior
  let boundary := bounds.boundary
  let shift := bounds.shift
  let extraFrame := bounds.extraFrame
  let extraRead := bounds.extraRead
  refine {
    reductionPrior := congrArg Modexp.wordLimbsToNat
      (ciosReductionPrior_eq_multiplyTail columns bP tP tEnd tk1Off nP n0inv tOff
        nBefore state prior.columnsGtOne prior.multiplyTailPtr prior.reductionRangeEnd
        prior.tEndLeTk1 prior.multiplyTailBound prior.multiplyTailWrites prior.reductionLo
        prior.reductionHi prior.reductionReads prior.reductionWrites prior.tEndInMultiply
        prior.tk1InBoundary1)
    boundaryLow := ciosBoundaryLow_eq_firstMultiplyOutput columns bP tP tEnd tk1Off state
      boundary.columnsPositive boundary.rangeEnd boundary.tEndLeTk1 boundary.multiplyBound
      boundary.multiplyWrites prior.tEndInMultiply prior.tk1InBoundary1
      boundary.boundaryReadSize boundary.boundaryReadGuard
    shiftLow := ciosShiftLow_eq_boundaryUpper columns bP tP tEnd tk1Off nP n0inv tOff
      nBefore state shift.columnsGtOne shift.tEndInMultiply shift.tEndBeforeTk1
      shift.tk1InBoundary1 shift.reductionWritesToEnd shift.reductionFinalReadSize
      shift.reductionFinalReadGuard
    shiftExtra := ciosShiftExtra_eq_boundaryExtra columns bP tP tEnd tk1Off nP n0inv
      tOff nBefore shiftedOut state extraFrame.columnsGtOne extraFrame.tk1InBoundary1
      extraFrame.reductionWritesToTk1 extraRead.shiftedWrite extraRead.shiftedBelow
      (by simpa only [CIOSShiftExtraReadSize] using extraRead.shiftedReadSize)
      (by simpa only [CIOSShiftExtraReadGuard] using extraRead.shiftedReadGuard) }
-/
-/

def ciosIterationPrior
    (columns : Nat) (bP tP tEnd tk1Off : UInt256) (state : CIOSOuterState) : Nat :=
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let initial := ciosMultiplyInitial bP tP state
  let final := ciosMultiplyFinal columns bP tP state
  Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns initial) +
    UInt256.size ^ columns *
      (ciosBoundaryTk final.memory final.activeWords tEnd).toNat +
    UInt256.size ^ (columns + 1) *
      (ciosBoundaryTk1 final.memory final.activeWords tEnd final.carry tk1Off).toNat

def ciosIterationMultiplier
    (columns : Nat) (bP tP : UInt256) (state : CIOSOuterState) : Nat :=
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  Modexp.wordLimbsToNat
    (multiplyPassOperandWords ai columns (ciosMultiplyInitial bP tP state))

def ciosIterationModulus
    (columns : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : Nat :=
  let final := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reduction := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  (ciosBoundaryN0 final.memory final.activeWords tEnd final.carry tk1Off tP nP).toNat +
    UInt256.size *
      Modexp.wordLimbsToNat
        (schoolbookOperandWords factor (columns - 1) reduction)

def ciosIterationNext
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) : Nat :=
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reduction := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let final := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  Modexp.wordLimbsToNat
      (schoolbookOutputWords factor (columns - 1) reduction) +
    UInt256.size ^ (columns - 1) *
      (ciosShiftSum final.memory final.activeWords final.carry tEnd).toNat +
    UInt256.size ^ columns *
      (ciosShiftTk1 final.memory final.activeWords final.carry shiftedOut tk1Off tEnd +
        ciosShiftOverflow final.memory final.activeWords final.carry tEnd).toNat

/-- One complete generated CIOS outer iteration satisfies the exact unbounded numerator
equation.  No modular congruence or output bound is used here. -/
theorem ciosOuterAdvance_recompose
    (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState)
    (hcolumns : 1 < columns)
    (hinv :
      (ciosBoundaryN0
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off tP nP).toNat *
          n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hboundaryFit :
      (ciosBoundaryTk1
        (ciosMultiplyFinal columns bP tP state).memory
        (ciosMultiplyFinal columns bP tP state).activeWords tEnd
        (ciosMultiplyFinal columns bP tP state).carry tk1Off).toNat +
        (ciosBoundaryOverflow
          (ciosMultiplyFinal columns bP tP state).memory
          (ciosMultiplyFinal columns bP tP state).activeWords tEnd
          (ciosMultiplyFinal columns bP tP state).carry).toNat < UInt256.size)
    (hshiftFit :
      (ciosShiftTk1
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
        (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
        shiftedOut tk1Off tEnd).toNat +
        (ciosShiftOverflow
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).memory
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).activeWords
          (ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv tOff nBefore state).carry
          tEnd).toNat < UInt256.size)
    (links : CIOSPhaseLinks columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut state) :
    UInt256.size *
        ciosIterationNext columns bP tP tEnd tk1Off nP n0inv tOff nBefore
          shiftedOut state =
      ciosIterationPrior columns bP tP tEnd tk1Off state +
        (ciosOuterAi state.memory state.activeWords state.aOff).toNat *
          ciosIterationMultiplier columns bP tP state +
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state).toNat *
          ciosIterationModulus columns bP tP tEnd tk1Off nP n0inv tOff nBefore
            state := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let multiplyFinal := ciosMultiplyFinal columns bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  let reductionFinal := ciosReductionFinal columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hmultiplyFinal := ciosMultiplyFinal_eq_iterate columns bP tP state (by omega)
  have hreductionFinal := ciosReductionFinal_eq_iterate columns bP tP tEnd tk1Off
    nP n0inv tOff nBefore state hcolumns
  have hmultiply := multiplyPassCollectors_recompose ai columns multiplyInitial
  rw [← hmultiplyFinal] at hmultiply
  have hmultiplyHead := multiplyPassOutputWords_recompose_head ai columns multiplyInitial
    (by omega)
  have hboundaryLow :
      (ciosBoundaryT0 multiplyFinal.memory multiplyFinal.activeWords tEnd
        multiplyFinal.carry tk1Off tP).toNat =
      (schoolbookStep multiplyInitial.memory multiplyInitial.activeWords
        multiplyInitial.operandPtr multiplyInitial.resultPtr ai
        multiplyInitial.carry).1.toNat := by
    simpa [ai, multiplyInitial, multiplyFinal, ciosMultiplyInitial] using
      links.boundaryLow
  have hmultiplyEq :
      (ciosBoundaryT0 multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry tk1Off tP).toNat +
        UInt256.size *
          Modexp.wordLimbsToNat
            (multiplyPassOutputWords ai (columns - 1)
              (multiplyPassAdvance ai multiplyInitial)) +
        UInt256.size ^ columns * multiplyFinal.carry.toNat =
      Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns multiplyInitial) +
        ai.toNat * Modexp.wordLimbsToNat
          (multiplyPassOperandWords ai columns multiplyInitial) := by
    rw [hboundaryLow]
    rw [← hmultiplyHead]
    simpa [multiplyInitial, ciosMultiplyInitial] using hmultiply
  have hmultiplyEq' :
      (ciosBoundaryT0 multiplyFinal.memory multiplyFinal.activeWords tEnd
          multiplyFinal.carry tk1Off tP).toNat +
        UInt256.size *
          Modexp.wordLimbsToNat
            (multiplyPassOutputWords ai (columns - 1)
              (multiplyPassAdvance ai multiplyInitial)) +
        UInt256.size ^ (columns - 1 + 1) * multiplyFinal.carry.toNat =
      Modexp.wordLimbsToNat (multiplyPassPriorWords ai columns multiplyInitial) +
        ai.toNat * Modexp.wordLimbsToNat
          (multiplyPassOperandWords ai columns multiplyInitial) := by
    simpa [show columns - 1 + 1 = columns by omega] using hmultiplyEq
  have hupper := ciosBoundaryUpper_recompose multiplyFinal.memory
    multiplyFinal.activeWords tEnd multiplyFinal.carry tk1Off hboundaryFit
  have hpeeled := ciosBoundaryPeeled_recompose multiplyFinal.memory
    multiplyFinal.activeWords tEnd multiplyFinal.carry tk1Off tP nP n0inv hinv
  have hreduction := schoolbookCollectors_recompose factor (columns - 1) reductionInitial
  rw [← hreductionFinal] at hreduction
  rw [links.reductionPrior] at hreduction
  have hshift := ciosShiftUpper_recompose reductionFinal.memory
    reductionFinal.activeWords reductionFinal.carry shiftedOut tk1Off tEnd hshiftFit
  rw [links.shiftLow, links.shiftExtra] at hshift
  have composed := montgomeryCIOS_columns_recompose
    (q := columns - 1)
    hmultiplyEq' hupper hpeeled hreduction hshift
  simpa [ciosIterationNext, ciosIterationPrior, ciosIterationMultiplier,
    ciosIterationModulus, ai, multiplyInitial, multiplyFinal, factor,
    reductionInitial, reductionFinal, show columns - 1 + 1 = columns by omega,
    show columns - 1 + 2 = columns + 1 by omega,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using composed

end Modexp.MultiLimbMontgomeryCIOSSemantic
