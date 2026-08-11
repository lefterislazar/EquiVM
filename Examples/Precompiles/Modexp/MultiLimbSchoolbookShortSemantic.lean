import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortContract
import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookOuterComplete

/-!
# Arithmetic semantics of the short-dividend copy

The execution copies only the effective low dividend words. This file proves that every higher
remainder word stays at its initialized zero value and therefore the complete fixed-width
remainder denotes the original effective dividend.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookShortSemantic

open MultiLimbSchoolbookShort
open MultiLimbSchoolbookNormalizationSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Stores to lower remainder indices preserve a selected higher remainder word. -/
theorem copyLoopMemory_preserves_word_above
    (mem : ByteArray) (aw dividend rem : UInt256) (n index : Nat)
    (hwrite : ∀ i, i < n -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (habove : ∀ i, i < n ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem index).toNat) :
    arrayWord (copyLoopMemory mem aw dividend rem n) aw rem index =
      arrayWord mem aw rem index := by
  induction n with
  | zero => rfl
  | succ n ih =>
      let current := copyLoopMemory mem aw dividend rem n
      let value := arrayWord current aw dividend n
      have hcurrentSize : current.size = mem.size :=
        copyLoopMemory_size_eq mem aw dividend rem n
          (fun i hi => hwrite i (by omega))
      have hstore : (arrayAddress rem n).toNat + 32 ≤ current.size := by
        rw [hcurrentSize]
        exact hwrite n (by omega)
      have hlocal : arrayWord (copyMemory current rem n value) aw rem index =
          arrayWord current aw rem index := by
        unfold arrayWord MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
          MultiLimbDivisionTrace.readWord copyMemory
        have hsize :
            (value.toByteArray.write 0 current (arrayAddress rem n).toNat 32).size =
              current.size := by
          exact toByteArray_write32_size_of_le current value (arrayAddress rem n).toNat
            current.size current.size rfl (by omega) (max_eq_left hstore)
        rw [hsize]
        rw [write32_read_above_padded value.toByteArray current
          (arrayAddress rem n).toNat (arrayAddress rem index).toNat
          (by rw [toByteArray_size]) hstore (habove n (by omega))]
      unfold copyLoopMemory
      change arrayWord (copyMemory current rem n value) aw rem index = _
      rw [hlocal]
      exact ih (fun i hi => hwrite i (by omega))
        (fun i hi => habove i (by omega))

/-- Pointwise equality of concrete array words lifts to equality of finite slices. -/
theorem arrayReadWords_eq_of_words
    (left right : ByteArray) (aw leftArray rightArray : UInt256)
    (start count : Nat)
    (hwords : ∀ i, i < count ->
      MultiLimbSchoolbookNormalization.arrayWord left aw leftArray (start + i) =
        MultiLimbSchoolbookNormalization.arrayWord right aw rightArray (start + i)) :
    arrayReadWords left aw leftArray start count =
      arrayReadWords right aw rightArray start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      have hhead := hwords 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [hhead]
      apply congrArg (fun words => _ :: words)
      apply ih
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hwords (i + 1) (by omega)

/-- A slice whose concrete words are all zero has natural value zero. -/
theorem arrayReadWords_toNat_eq_zero
    (mem : ByteArray) (aw array : UInt256) (start count : Nat)
    (hzero : ∀ i, i < count ->
      MultiLimbSchoolbookNormalization.arrayWord mem aw array (start + i) = ⟨0⟩) :
    Modexp.wordLimbsToNat (arrayReadWords mem aw array start count) = 0 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords, Modexp.wordLimbsToNat]
      have hhead := hzero 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [hhead]
      simp only [show (⟨0⟩ : UInt256).toNat = 0 by decide, zero_add]
      rw [ih (start + 1) (by
        intro i hi
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hzero (i + 1) (by omega))]
      simp

/-- Allocating the one-word quotient preserves a complete padded word below the new header.  This
is the memory fact used when the allocation makes an earlier array's implicit zero payload
concrete. -/
theorem shortAllocatedMemory_read_below
    (mem : ByteArray) (fp read : Nat)
    (hmemSize : 96 ≤ mem.size)
    (hgap : fp - mem.size < USize.size)
    (hread : 96 ≤ read) (hbelow : read + 32 ≤ fp) :
    (shortAllocatedMemory mem fp).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize 1)).size = mem.size :=
    setFreePtr_size hmemSize
  unfold shortAllocatedMemory
  rw [storeBytesLength_read_below_padded]
  · exact setFreePtr_read_above_padded hmemSize hread
  · rw [hsetSize]
    omega
  · exact hbelow
  · rw [hsetSize]
    exact hgap

/-- The one-word short-branch allocation installs its exact advanced Solidity free pointer. -/
theorem shortAllocatedMemory_freeRead
    (mem : ByteArray) (fp : Nat)
    (hmemSize : 96 ≤ mem.size) (hfp : 96 ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (shortAllocatedMemory mem fp).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (fp + wordArrayAllocationSize 1)) := by
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize 1)).size = mem.size :=
    setFreePtr_size hmemSize
  unfold shortAllocatedMemory
  rw [storeBytesLength_read_below_padded]
  · exact setFreePtr_read64 hmemSize
  · rw [hsetSize]
    omega
  · omega
  · rw [hsetSize]
    exact hgap

/-- A word in an earlier implicit-zero allocation gap is still zero after the short branch
allocates its quotient. -/
theorem shortAllocatedMemory_arrayWord_zero
    (mem : ByteArray) (aw rem : UInt256) (fp index : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : (shortAllocatedWords aw fp).toNat * 32 < UInt256.size)
    (hread : 96 ≤ (arrayAddress rem index).toNat)
    (hpast : mem.size ≤ (arrayAddress rem index).toNat)
    (hbelow : (arrayAddress rem index).toNat + 32 ≤ fp)
    (hactive : (arrayAddress rem index).toNat + 32 ≤
      32 * (shortAllocatedWords aw fp).toNat) :
    arrayWord (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp) rem index = ⟨0⟩ := by
  let address := arrayAddress rem index
  have hfinalSize : (shortAllocatedMemory mem fp).size = fp + 32 := by
    unfold shortAllocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size hmemSize]
      exact hmemLe
    · rw [setFreePtr_size hmemSize]
      exact hgap
  have hmul :
      (shortAllocatedWords aw fp * (⟨32⟩ : UInt256)).toNat =
        (shortAllocatedWords aw fp).toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := shortAllocatedWords aw fp) (b := (⟨32⟩ : UInt256)) hawFit
  have hnotActive : ¬ address ≥ shortAllocatedWords aw fp * ⟨32⟩ := by
    intro hge
    have hgeNat : (shortAllocatedWords aw fp * (⟨32⟩ : UInt256)).toNat ≤
        address.toNat := hge
    dsimp only [address] at hgeNat
    rw [hmul] at hgeNat
    omega
  unfold arrayWord MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by rw [hfinalSize]; omega, hnotActive⟩)]
  rw [shortAllocatedMemory_read_below mem fp address.toNat hmemSize hgap
    hread hbelow]
  rw [readWithPadding_past_end mem address.toNat 32 hpast (by decide),
    ← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
  native_decide

/-- The complete fixed-width short-branch remainder denotes the concrete effective dividend. -/
theorem copyLoopMemory_value
    (mem : ByteArray) (aw dividend rem : UInt256) (m k : Nat)
    (hmk : m ≤ k)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ i, i < m -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i, i < m -> ∀ j, j < m ->
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationBelow : ∀ i, i < k -> ∀ j, j < k -> i < j ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationActive : ∀ i, i < m ->
      (arrayAddress rem i).toNat + 32 ≤ 32 * aw.toNat)
    (hinitialHighZero : ∀ i, m ≤ i -> i < k -> arrayWord mem aw rem i = ⟨0⟩) :
    Modexp.wordLimbsToNat
        (arrayReadWords (copyLoopMemory mem aw dividend rem m) aw rem 0 k) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw dividend 0 m) := by
  let finalMem := copyLoopMemory mem aw dividend rem m
  have hlow : arrayReadWords finalMem aw rem 0 m =
      arrayReadWords mem aw dividend 0 m := by
    apply arrayReadWords_eq_of_words
    intro i hi
    have hcopied := copyLoopMemory_copied_word mem aw dividend rem m i hawFit hi hwrite
      hsourceBelow
      (fun i hiI j hiJ hij => hdestinationBelow i (by omega) j (by omega) hij)
      hdestinationActive
    simpa only [Nat.zero_add] using hcopied
  have hhighZero : Modexp.wordLimbsToNat
      (arrayReadWords finalMem aw rem m (k - m)) = 0 := by
    apply arrayReadWords_toNat_eq_zero
    intro i hi
    have hindex : m + i < k := by omega
    have hpreserved := copyLoopMemory_preserves_word_above mem aw dividend rem m (m + i)
      hwrite (by
        intro j hj
        exact hdestinationBelow j (by omega) (m + i) hindex (by omega))
    have hpreserved' :
        MultiLimbSchoolbookNormalization.arrayWord finalMem aw rem (m + i) =
          MultiLimbSchoolbookNormalization.arrayWord mem aw rem (m + i) := hpreserved
    rw [hpreserved']
    exact hinitialHighZero (m + i) (by omega) hindex
  have hsplit := MultiLimbSchoolbookOuterComplete.arrayReadWords_add finalMem aw rem 0 m
    (k - m)
  have hlength : m + (k - m) = k := Nat.add_sub_of_le hmk
  rw [hlength] at hsplit
  simp only [Nat.zero_add] at hsplit
  rw [hsplit, Modexp.wordLimbsToNat_append, arrayReadWords_length, hlow, hhighZero]
  simp

/-- Since an `m`-word value is below every nonzero `k`-word divisor when `m < k`, the copied
short remainder is ordinary modulo. -/
theorem copyLoopMemory_eq_mod
    (mem : ByteArray) (aw dividend rem : UInt256) (m k : Nat)
    (hmk : m < k)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ i, i < m -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i, i < m -> ∀ j, j < m ->
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationBelow : ∀ i, i < k -> ∀ j, j < k -> i < j ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationActive : ∀ i, i < m ->
      (arrayAddress rem i).toNat + 32 ≤ 32 * aw.toNat)
    (hinitialHighZero : ∀ i, m ≤ i -> i < k -> arrayWord mem aw rem i = ⟨0⟩)
    (divisorPrefix : List UInt256) (divisorTop : UInt256)
    (hdivisorLength : divisorPrefix.length + 1 = k)
    (hdivisorTop : divisorTop ≠ ⟨0⟩) :
    Modexp.wordLimbsToNat
        (arrayReadWords (copyLoopMemory mem aw dividend rem m) aw rem 0 k) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw dividend 0 m) %
        Modexp.wordLimbsToNat (divisorPrefix ++ [divisorTop]) := by
  have hvalue := copyLoopMemory_value mem aw dividend rem m k (by omega) hawFit hwrite
    hsourceBelow hdestinationBelow hdestinationActive hinitialHighZero
  have hdividendBound := Modexp.wordLimbsToNat_lt_pow
    (arrayReadWords mem aw dividend 0 m)
  have hdivisorLower : UInt256.size ^ (k - 1) ≤
      Modexp.wordLimbsToNat (divisorPrefix ++ [divisorTop]) := by
    have htopNat : 1 ≤ divisorTop.toNat := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hzero
      apply hdivisorTop
      apply u256_inj
      simpa using hzero
    rw [Modexp.wordLimbsToNat_append]
    simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
    have hlength : divisorPrefix.length = k - 1 := by omega
    rw [hlength]
    have hpowPos : 0 < UInt256.size ^ (k - 1) :=
      Nat.pow_pos (by norm_num [UInt256.size])
    nlinarith
  have hlt : Modexp.wordLimbsToNat (arrayReadWords mem aw dividend 0 m) <
      Modexp.wordLimbsToNat (divisorPrefix ++ [divisorTop]) := by
    rw [arrayReadWords_length] at hdividendBound
    have hpow : UInt256.size ^ m ≤ UInt256.size ^ (k - 1) := by
      exact Nat.pow_le_pow_right (by norm_num [UInt256.size]) (by omega)
    omega
  rw [Nat.mod_eq_of_lt hlt]
  exact hvalue

/-- The short copy is modulo the actual complete divisor slice in memory. -/
theorem copyLoopMemory_eq_concrete_mod
    (mem : ByteArray) (aw dividend rem divisor : UInt256) (m k : Nat)
    (hmk : m < k)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hwrite : ∀ i, i < m -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i, i < m -> ∀ j, j < m ->
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationBelow : ∀ i, i < k -> ∀ j, j < k -> i < j ->
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationActive : ∀ i, i < m ->
      (arrayAddress rem i).toNat + 32 ≤ 32 * aw.toNat)
    (hinitialHighZero : ∀ i, m ≤ i -> i < k -> arrayWord mem aw rem i = ⟨0⟩)
    (hdivisorTop :
      MultiLimbSchoolbookNormalization.arrayWord mem aw divisor (k - 1) ≠ ⟨0⟩) :
    Modexp.wordLimbsToNat
        (arrayReadWords (copyLoopMemory mem aw dividend rem m) aw rem 0 k) =
      Modexp.wordLimbsToNat (arrayReadWords mem aw dividend 0 m) %
        Modexp.wordLimbsToNat (arrayReadWords mem aw divisor 0 k) := by
  let divisorPrefix := arrayReadWords mem aw divisor 0 (k - 1)
  let top := MultiLimbSchoolbookNormalization.arrayWord mem aw divisor (k - 1)
  have hlength : divisorPrefix.length + 1 = k := by
    simp only [divisorPrefix, arrayReadWords_length]
    omega
  have hresult := copyLoopMemory_eq_mod mem aw dividend rem m k hmk hawFit hwrite
    hsourceBelow hdestinationBelow hdestinationActive hinitialHighZero divisorPrefix top hlength
    hdivisorTop
  have hsplit := MultiLimbSchoolbookOuterComplete.arrayReadWords_add mem aw divisor 0 (k - 1) 1
  have hsum : k - 1 + 1 = k := by omega
  rw [hsum] at hsplit
  simp only [Nat.zero_add, arrayReadWords, divisorPrefix, top] at hsplit
  rw [hsplit]
  exact hresult

end Modexp.MultiLimbSchoolbookShortSemantic
