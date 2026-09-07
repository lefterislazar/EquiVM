import Reasoning.Memory

/-! # Memory facts at CALL-family boundaries

The output copy is bounded by both the requested capacity and returned bytes. The
bundle below describes an already allocated output region, including empty and short
outputs. Its offsets and capacity are arbitrary; it assumes no Solidity free-pointer
layout. Input/output expansion is treated separately, including zero-sized regions.
-/

namespace Reasoning.Theory

open Ethereum Ethereum.EVM

/-- The CALL copy length as ordinary natural-number arithmetic. The bound prevents
truncation when converting the return-data size to an EVM word. -/
theorem callCopyLength_toNat (out : ByteArray) (capacity : UInt256)
    (hout : out.size < UInt256.size) :
    (min capacity (UInt256.ofNat out.size)).toNat = min capacity.toNat out.size := by
  change (if capacity ≤ UInt256.ofNat out.size then capacity else UInt256.ofNat out.size).toNat = _
  have hw : capacity ≤ UInt256.ofNat out.size ↔ capacity.toNat ≤ out.size := by
    change capacity.toNat ≤ (UInt256.ofNat out.size).toNat ↔ _
    rw [ulit_toNat' _ hout]
  by_cases h : capacity.toNat ≤ out.size
  · rw [if_pos (hw.mpr h), Nat.min_eq_left h]
  · rw [if_neg (fun hle => h (hw.mp hle)), ulit_toNat' _ hout,
      Nat.min_eq_right (by omega)]

private theorem write_size_inBounds (out mem : ByteArray) (offset len : ℕ)
    (hsrc : len ≤ out.size) (hbound : offset + len ≤ mem.size) :
    (out.write 0 mem offset len).size = mem.size := by
  by_cases hz : len = 0
  · subst len; rw [byteArray_write_len_zero]
  · rw [write_eq_gen out mem offset len hz hsrc hbound,
      ByteArray.size_append, ByteArray.size_append,
      ByteArray.size_extract, ByteArray.size_extract, ByteArray.size_extract]
    omega

private theorem write_read_word_inBounds (out mem : ByteArray) (offset len : ℕ)
    (hsrc : len ≤ out.size) (hbound : offset + len ≤ mem.size) (hword : 32 ≤ len) :
    (out.write 0 mem offset len).readWithPadding offset 32 = out.extract 0 32 := by
  have hpre : (mem.extract 0 offset).size = offset := by rw [ByteArray.size_extract]; omega
  have hcopy : (out.extract 0 len).size = len := by rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract _ offset (by rw [write_size_inBounds _ _ _ _ hsrc hbound]; omega),
    write_eq_gen out mem offset len (by omega) hsrc hbound,
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hpre, hcopy]; omega),
    extract_append_right_window _ _ _ _ (by rw [hpre]), hpre,
    Nat.sub_self, Nat.add_sub_cancel_left, extract_prefix _ _ _ _ hword]

private theorem write_read_above_inBounds (out mem : ByteArray) (offset len read : ℕ)
    (hsrc : len ≤ out.size) (hbound : offset + len ≤ mem.size)
    (habove : offset + len ≤ read) (hread : read + 32 ≤ mem.size) :
    (out.write 0 mem offset len).readWithPadding read 32 = mem.readWithPadding read 32 := by
  by_cases hz : len = 0
  · subst len; rw [byteArray_write_len_zero]
  have hleft : (mem.extract 0 offset ++ out.extract 0 len).size = offset + len := by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract _ read (by rw [write_size_inBounds _ _ _ _ hsrc hbound]; exact hread),
    readWithPadding_eq_extract _ read hread, write_eq_gen out mem offset len hz hsrc hbound,
    extract_append_right_window _ _ _ _ (by rw [hleft]; exact habove), hleft,
    extract_extract_BA,
    show offset + len + (read - (offset + len)) = read from by omega,
    show min (offset + len + (read + 32 - (offset + len))) mem.size = read + 32 from by omega]

/-- Facts about copying CALL return data into an allocated region. Reads outside
that region are preserved, and a full returned word can be read back at its start. -/
structure CallOutputFacts (mem out : ByteArray) (offset capacity : UInt256) : Prop where
  copyLength : (min capacity (UInt256.ofNat out.size)).toNat = min capacity.toNat out.size
  size : (out.write 0 mem offset.toNat (min capacity (UInt256.ofNat out.size)).toNat).size = mem.size
  readBelow : ∀ read, read + 32 ≤ offset.toNat →
    (out.write 0 mem offset.toNat (min capacity (UInt256.ofNat out.size)).toNat).readWithPadding read 32 =
      mem.readWithPadding read 32
  readAbove : ∀ read, offset.toNat + capacity.toNat ≤ read → read + 32 ≤ mem.size →
    (out.write 0 mem offset.toNat (min capacity (UInt256.ofNat out.size)).toNat).readWithPadding read 32 =
      mem.readWithPadding read 32
  readWord : 32 ≤ capacity.toNat → 32 ≤ out.size →
    (out.write 0 mem offset.toNat (min capacity (UInt256.ofNat out.size)).toNat).readWithPadding offset.toNat 32 =
      out.extract 0 32

theorem callOutputFacts (mem out : ByteArray) (offset capacity : UInt256)
    (hout : out.size < UInt256.size) (hbound : offset.toNat + capacity.toNat ≤ mem.size) :
    CallOutputFacts mem out offset capacity := by
  have hlen := callCopyLength_toNat out capacity hout
  have hsrc : (min capacity (UInt256.ofNat out.size)).toNat ≤ out.size := by
    rw [hlen]; exact Nat.min_le_right _ _
  have hcap : (min capacity (UInt256.ofNat out.size)).toNat ≤ capacity.toNat := by
    rw [hlen]; exact Nat.min_le_left _ _
  refine ⟨hlen, write_size_inBounds _ _ _ _ hsrc (by omega), ?_, ?_, ?_⟩
  · intro read hread
    by_cases hz : (min capacity (UInt256.ofNat out.size)).toNat = 0
    · rw [hz, byteArray_write_len_zero]
    · exact write_read_below_gen out mem _ _ read hz hsrc (by omega) hread
  · intro read habove hread
    exact write_read_above_inBounds out mem _ _ read hsrc (by omega) (by omega) hread
  · intro hcapacity houtput
    exact write_read_word_inBounds out mem _ _ hsrc (by omega) (by rw [hlen]; omega)

/-- An empty or already active memory region does not expand memory. -/
theorem memoryExpansion_eq_of_bounds (aw offset len : ℕ)
    (h : len = 0 ∨ offset + len ≤ aw * 32) : MachineState.M aw offset len = aw := by
  cases len with
  | zero => rfl
  | succ n =>
    simp only [MachineState.M]
    apply max_eq_left
    omega

/-- The active-word count at a CALL boundary stays fixed when both requested
regions are empty or already active. Uses natural arithmetic, without word overflow. -/
theorem callActiveWords_eq (aw inOffset inSize outOffset outSize : UInt256)
    (hin : inSize.toNat = 0 ∨ inOffset.toNat + inSize.toNat ≤ aw.toNat * 32)
    (hout : outSize.toNat = 0 ∨ outOffset.toNat + outSize.toNat ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
      outOffset.toNat outSize.toNat) = aw := by
  rw [memoryExpansion_eq_of_bounds _ _ _ hin, memoryExpansion_eq_of_bounds _ _ _ hout,
    u256_ofNat_toNat]

end Reasoning.Theory
