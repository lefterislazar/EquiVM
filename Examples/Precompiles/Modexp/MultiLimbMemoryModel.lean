import Examples.Precompiles.Modexp.MultiLimbGenerated
import Examples.Precompiles.Modexp.MultiLimbBackendModel

/-!
# Memory interpretation for generated multi-limb traces

The generated execution theorems expose byte-array writes.  These lemmas interpret the written
words as natural-number limbs, providing the representation consumed by the pure backend proofs.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMemoryModel

open MultiLimbGenerated

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Natural-number interpretation of one big-endian EVM memory word. -/
def memoryWordNat (mem : ByteArray) (off : Nat) : Nat :=
  fromByteArrayBigEndian (mem.readWithPadding off 32)

theorem memoryWordNat_toByteArray (word : UInt256) :
    memoryWordNat word.toByteArray 0 = word.toNat := by
  unfold memoryWordNat
  rw [readWithPadding_eq_extract _ 0 (by rw [toByteArray_size])]
  rw [show word.toByteArray.extract 0 (0 + 32) = word.toByteArray by
    simpa [toByteArray_size] using byteArray_extract_self word.toByteArray]
  exact fromByteArrayBigEndian_toByteArray word

/-- A trusted padded 32-byte field is the same natural value as an EVM memory-word read. -/
theorem memoryWordNat_eq_model (mem : ByteArray) (off : Nat) (hoff : off < 2 ^ 64) :
    memoryWordNat mem off = Model.bytesToNatPadded mem off 32 := by
  unfold memoryWordNat Model.bytesToNatPadded
  rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian]
  rw [← readWithPadding_eq_model_readPadded mem off 32 hoff (by decide)]

/-- Each generated full-word iteration stores exactly the word it loaded. -/
theorem fullWordIterationMemory_word
    (mem : ByteArray) (aw i dataPtr dataLen limbsPtr : UInt256)
    (hgap : (fullWordWriteAddress i limbsPtr).toNat - mem.size < USize.size) :
    memoryWordNat
        (fullWordIterationMemory mem aw i dataPtr dataLen limbsPtr)
        (fullWordWriteAddress i limbsPtr).toNat =
      (fullWordReadValue mem aw i dataPtr dataLen).toNat := by
  unfold fullWordIterationMemory memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- The optional most-significant partial iteration stores its shifted word exactly. -/
theorem partialWordMemory_word
    (mem : ByteArray) (aw dataPtr dataLen rem limbsPtr : UInt256)
    (hgap : (partialWordWriteAddress dataLen limbsPtr).toNat - mem.size < USize.size) :
    memoryWordNat (partialWordMemory mem aw dataPtr dataLen rem limbsPtr)
        (partialWordWriteAddress dataLen limbsPtr).toNat =
      (partialWordValue mem aw dataPtr rem).toNat := by
  unfold partialWordMemory memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- A full-word source load has the trusted field value whenever the EVM access guards hold. -/
theorem fullWordReadValue_toNat_eq_model
    (mem : ByteArray) (aw i dataPtr dataLen : UInt256)
    (hsize : (fullWordReadAddress i dataPtr dataLen).toNat < mem.size)
    (haw : ¬ fullWordReadAddress i dataPtr dataLen ≥ aw * ⟨32⟩)
    (hoff : (fullWordReadAddress i dataPtr dataLen).toNat < 2 ^ 64) :
    (fullWordReadValue mem aw i dataPtr dataLen).toNat =
      Model.bytesToNatPadded mem (fullWordReadAddress i dataPtr dataLen).toNat 32 := by
  unfold fullWordReadValue
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩)]
  rw [ulit_toNat' _ (by
    have hbound := model_bytesToNatPadded_lt_pow mem
      (fullWordReadAddress i dataPtr dataLen).toNat 32
    rw [← memoryWordNat_eq_model mem _ hoff] at hbound
    simpa [memoryWordNat, UInt256.size, pow_mul] using hbound)]
  exact memoryWordNat_eq_model mem _ hoff

/-- The partial-word source load is likewise the trusted 32-byte padded field. -/
theorem partialWordReadValue_toNat_eq_model
    (mem : ByteArray) (aw dataPtr : UInt256)
    (hsize : (partialWordReadAddress dataPtr).toNat < mem.size)
    (haw : ¬ partialWordReadAddress dataPtr ≥ aw * ⟨32⟩)
    (hoff : (partialWordReadAddress dataPtr).toNat < 2 ^ 64) :
    (partialWordReadValue mem aw dataPtr).toNat =
      Model.bytesToNatPadded mem (partialWordReadAddress dataPtr).toNat 32 := by
  unfold partialWordReadValue
  rw [if_neg (not_or.mpr ⟨by omega, haw⟩)]
  rw [ulit_toNat' _ (by
    have hbound := model_bytesToNatPadded_lt_pow mem
      (partialWordReadAddress dataPtr).toNat 32
    rw [← memoryWordNat_eq_model mem _ hoff] at hbound
    simpa [memoryWordNat, UInt256.size, pow_mul] using hbound)]
  exact memoryWordNat_eq_model mem _ hoff

/-- Right-aligning the first partial word produces exactly the trusted value of that byte prefix. -/
theorem partialWordValue_toNat_eq_model
    (mem : ByteArray) (aw dataPtr rem : UInt256)
    (hsize : (partialWordReadAddress dataPtr).toNat < mem.size)
    (haw : ¬ partialWordReadAddress dataPtr ≥ aw * ⟨32⟩)
    (hoff : (partialWordReadAddress dataPtr).toNat < 2 ^ 64)
    (hrem : rem.toNat ≤ 32) :
    (partialWordValue mem aw dataPtr rem).toNat =
      Model.bytesToNatPadded mem (partialWordReadAddress dataPtr).toNat rem.toNat := by
  have hmload : partialWordReadValue mem aw dataPtr =
      uInt256OfByteArray
        (mem.readBytes (partialWordReadAddress dataPtr).toNat 32) := by
    apply u256_inj
    rw [partialWordReadValue_toNat_eq_model mem aw dataPtr hsize haw hoff]
    exact (calldataWord_toNat_eq_model mem
      (partialWordReadAddress dataPtr).toNat hoff).symm
  unfold partialWordValue
  rw [hmload]
  exact operandWord_toNat_eq_model mem
    (partialWordReadAddress dataPtr).toNat rem hoff hrem

/-- Read a fixed number of little-endian limbs from a Solidity word-array payload. -/
def memoryLimbs (mem : ByteArray) (ptr count : Nat) : List Nat :=
  List.ofFn fun i : Fin count => memoryWordNat mem (ptr + 32 + 32 * i.val)

@[simp] theorem memoryLimbs_length (mem : ByteArray) (ptr count : Nat) :
    (memoryLimbs mem ptr count).length = count := by
  simp [memoryLimbs]

/-- Extending the observed payload by one limb appends the next padded memory word. -/
theorem memoryLimbs_succ (mem : ByteArray) (ptr count : Nat) :
    memoryLimbs mem ptr (count + 1) =
      memoryLimbs mem ptr count ++ [memoryWordNat mem (ptr + 32 + 32 * count)] := by
  unfold memoryLimbs
  rw [List.ofFn_succ']
  simp only [List.concat_eq_append]
  congr 1

/-- A padded word beginning at the concrete byte-array frontier is zero. -/
theorem memoryWordNat_past_end_zero (mem : ByteArray) (off : Nat)
    (hpast : mem.size ≤ off) :
    memoryWordNat mem off = 0 := by
  unfold memoryWordNat
  rw [readWithPadding_past_end mem off 32 hpast (by decide),
    ← zero_toByteArray_eq_zeroes32, fromByteArrayBigEndian_toByteArray]
  rfl

/-- Implicit zero limbs reserved after a materialized payload do not change its natural value. -/
theorem memoryLimbs_extend_zero_value
    (mem : ByteArray) (ptr count extra : Nat)
    (hpast : mem.size ≤ ptr + 32 + 32 * count) :
    limbsToNat (memoryLimbs mem ptr (count + extra)) =
      limbsToNat (memoryLimbs mem ptr count) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, memoryLimbs_succ, limbsToNat_eq_limbsToNatAt,
        limbsToNatAt_append]
      have hzero :
          memoryWordNat mem (ptr + 32 + 32 * (count + extra)) = 0 := by
        apply memoryWordNat_past_end_zero
        omega
      simp only [memoryLimbs_length, Nat.add_zero, limbsToNatAt, hzero, Nat.mul_zero]
      rw [← limbsToNat_eq_limbsToNatAt]
      exact ih

/-- The same implicit suffix is pointwise a list of zero limbs. -/
theorem memoryLimbs_extend_zero
    (mem : ByteArray) (ptr count extra : Nat)
    (hpast : mem.size ≤ ptr + 32 + 32 * count) :
    memoryLimbs mem ptr (count + extra) =
      memoryLimbs mem ptr count ++ List.replicate extra 0 := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [Nat.add_succ, memoryLimbs_succ, ih]
      have hzero : memoryWordNat mem (ptr + 32 + 32 * (count + extra)) = 0 := by
        apply memoryWordNat_past_end_zero
        omega
      rw [hzero, List.append_assoc]
      congr 1
      rw [List.replicate_add]
      rfl

/-- Equal padded words over an array payload induce equal concrete limb lists. -/
theorem memoryLimbs_eq_of_readWithPadding_eq
    (before after : ByteArray) (ptr count : Nat)
    (hread : ∀ i, i < count →
      after.readWithPadding (ptr + 32 + 32 * i) 32 =
        before.readWithPadding (ptr + 32 + 32 * i) 32) :
    memoryLimbs after ptr count = memoryLimbs before ptr count := by
  apply List.ext_getElem
  · simp
  · intro i hiAfter hiBefore
    simp only [memoryLimbs, List.getElem_ofFn, memoryWordNat]
    rw [hread i (by simpa using hiAfter)]

/-- Once conversion slots match the pure splitter, their aggregate natural value is the trusted
big-endian input field. -/
theorem memoryLimbs_value_eq_model
    (mem source : ByteArray) (ptr start len : Nat)
    (hlimbs : memoryLimbs mem ptr (bytesToLimbsPure source start len).length =
      bytesToLimbsPure source start len) :
    limbsToNat (memoryLimbs mem ptr (bytesToLimbsPure source start len).length) =
      Model.bytesToNatPadded source start len := by
  rw [hlimbs]
  exact limbsToNat_bytesToLimbsPure source start len

end Modexp.MultiLimbMemoryModel
