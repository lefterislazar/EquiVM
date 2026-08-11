import Examples.Precompiles.Modexp.MultiLimbReduceBaseContract
import Examples.Precompiles.Modexp.MultiLimbOddConversionSemantic
import Examples.Precompiles.Modexp.MultiLimbArrayReadSemantic

/-!
# Numeric semantics of Barrett base conversion

`reduceBase` allocates `max(ceil(baseSize / 32), k)` dividend limbs, while `bytesToLimbs`
materializes only the natural base width.  The remaining active payload is implicit zero EVM
memory.  This module proves that the exact guarded schoolbook observer still denotes the original
base byte object at the selected division width.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbReduceBaseSemantic

open MultiLimbReduceBase

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

/-- Allocating the selected-width base array preserves any older dynamic-array header below the
new allocation and keeps it within the enlarged active-memory frontier. -/
theorem baseAllocatedWideLoad_preserved
    (mem : ByteArray) (aw ptr : UInt256) (baseFp baseSize k : Nat)
    (hbasePos : 0 < baseSize)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hptr96 : 96 ≤ ptr.toNat) (hptrBelow : ptr.toNat + 32 ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64)
    (value : UInt256)
    (hread : mem.readWithPadding ptr.toNat 32 = UInt256.toByteArray value) :
    wideLoadWord (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k) ptr = value := by
  have hwordsPos : 0 < baseWords baseSize k := by
    unfold baseWords naturalWords
    omega
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocatedRead :
      (baseAllocatedMemory mem baseFp baseSize k).readWithPadding ptr.toNat 32 =
        mem.readWithPadding ptr.toNat 32 := by
    unfold baseAllocatedMemory
    rw [storeBytesLength_read_below_len_padded]
    · exact setFreePtr_read_above_len_padded hmemSize hptr96 (by omega) (by omega)
    · exact hptrBelow
    · omega
    · omega
    · rwa [hsetSize]
  have hallocationFit :
      baseFp + wordArrayAllocationSize (baseWords baseSize k) + 31 < UInt256.size :=
    lt_trans (by omega : baseFp + wordArrayAllocationSize (baseWords baseSize k) + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw baseFp
    (baseWords baseSize k) hwordsPos hawFit hallocationFit
  apply wideLoadWord_eq_of_read
  · rw [hallocatedSize]
    omega
  · apply MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
      (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k) ptr
    · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      rw [hallocatedSize]
      exact le_trans (by omega) hrange.1
    · exact hrange.2
    · rw [hallocatedSize]
      omega
  · exact hallocatedRead.trans hread

/-- Concrete size of the naturally materialized base conversion, independent of selected padding. -/
theorem convertedMemory_size_eq
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    (convertedMemory mem aw baseFp baseSize k basePtr).size =
      baseFp + 32 + 32 * naturalWords baseSize := by
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hnaturalLe : naturalWords baseSize ≤ baseWords baseSize k := Nat.le_max_left _ _
  have hnaturalFit : baseFp + 32 + 32 * naturalWords baseSize < UInt256.size := by
    have hfullFit : baseFp + 32 + 32 * baseWords baseSize k < UInt256.size := by
      have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      simpa [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hb
    omega
  simpa only [convertedMemory, u256_ofNat_toNat, naturalWords] using
    MultiLimbOddConversionSemantic.bytesToLimbsMemory_size_contiguous
      (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k)
      basePtr.toNat baseFp baseSize hbaseSize hallocatedSize (by
        simpa [naturalWords] using hnaturalFit)

/-- The nonempty base conversion materializes its natural limbs and leaves any selected wider
division payload as covered implicit zero memory. -/
theorem convertedGeometry
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    (convertedMemory mem aw baseFp baseSize k basePtr).size =
        baseFp + 32 + 32 * naturalWords baseSize ∧
      convertedWords mem aw baseFp baseSize k basePtr =
        baseAllocatedWords aw baseFp baseSize k ∧
      MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        (convertedMemory mem aw baseFp baseSize k basePtr)
        (convertedWords mem aw baseFp baseSize k basePtr) ∧
      (convertedWords mem aw baseFp baseSize k basePtr).toNat * 32 < UInt256.size := by
  have hnaturalPos : 0 < naturalWords baseSize := by
    unfold naturalWords
    omega
  have hnaturalLe : naturalWords baseSize ≤ baseWords baseSize k := Nat.le_max_left _ _
  have hbaseWordsPos : 0 < baseWords baseSize k := lt_of_lt_of_le hnaturalPos hnaturalLe
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocationFit :
      baseFp + wordArrayAllocationSize (baseWords baseSize k) + 31 < UInt256.size := by
    exact lt_trans
      (by omega : baseFp + wordArrayAllocationSize (baseWords baseSize k) + 31 <
        2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw baseFp
    (baseWords baseSize k) hbaseWordsPos hawFit hallocationFit
  have hnaturalRange :
      baseFp + 32 + 32 * naturalWords baseSize ≤
        baseFp + 32 + 32 * baseWords baseSize k := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 32 hnaturalLe) (baseFp + 32)
  have hnaturalFit : baseFp + 32 + 32 * naturalWords baseSize < UInt256.size := by
    have hfullFit : baseFp + 32 + 32 * baseWords baseSize k < UInt256.size := by
      have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      simpa [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hb
    omega
  have hconvertedSize :
      (convertedMemory mem aw baseFp baseSize k basePtr).size =
        baseFp + 32 + 32 * naturalWords baseSize := by
    simpa only [convertedMemory, u256_ofNat_toNat, naturalWords] using
      MultiLimbOddConversionSemantic.bytesToLimbsMemory_size_contiguous
        (baseAllocatedMemory mem baseFp baseSize k)
        (baseAllocatedWords aw baseFp baseSize k)
        basePtr.toNat baseFp baseSize hbaseSize hallocatedSize (by
          simpa [naturalWords] using hnaturalFit)
  have hconvertedWords :
      convertedWords mem aw baseFp baseSize k basePtr =
        baseAllocatedWords aw baseFp baseSize k := by
    simpa only [convertedWords, u256_ofNat_toNat] using
      MultiLimbOddConversionSemantic.bytesToLimbsActiveWords_eq_contiguous
        (baseAllocatedMemory mem baseFp baseSize k)
        (baseAllocatedWords aw baseFp baseSize k)
        basePtr.toNat baseFp baseSize
        hbaseSize hsourceBefore
        (by simpa [naturalWords] using le_trans hnaturalRange hrange.1)
        (by simpa [naturalWords] using hnaturalFit)
  refine ⟨hconvertedSize, hconvertedWords, ?_, ?_⟩
  · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hconvertedSize, hconvertedWords]
    exact le_trans hnaturalRange hrange.1
  · rw [hconvertedWords]
    exact hrange.2

/-- Base allocation and conversion preserve every older padded word ending before `baseFp`. -/
theorem convertedMemory_read_below
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k read : Nat)
    (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hread96 : 96 ≤ read) (hbelow : read + 32 ≤ baseFp)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    (convertedMemory mem aw baseFp baseSize k basePtr).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocatedRead :
      (baseAllocatedMemory mem baseFp baseSize k).readWithPadding read 32 =
        mem.readWithPadding read 32 := by
    unfold baseAllocatedMemory
    rw [storeBytesLength_read_below_len_padded]
    · exact setFreePtr_read_above_len_padded hmemSize hread96 (by omega) (by omega)
    · exact hbelow
    · omega
    · omega
    · rwa [hsetSize]
  have hnaturalLe : naturalWords baseSize ≤ baseWords baseSize k := Nat.le_max_left _ _
  have hnaturalFit :
      baseFp + 32 + 32 * ((baseSize + 31) / 32) < UInt256.size := by
    have hfullFit : baseFp + 32 + 32 * baseWords baseSize k < UInt256.size := by
      have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      simpa [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hb
    unfold naturalWords at hnaturalLe
    omega
  have hconvertedRead :=
    MultiLimbOddConversionSemantic.bytesToLimbsMemory_read_below_contiguous
      (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k)
      basePtr.toNat baseFp baseSize read hbaseSize hallocatedSize (by omega) hnaturalFit
  simpa only [convertedMemory, u256_ofNat_toNat] using hconvertedRead.trans hallocatedRead

/-- Base conversion preserves the allocator-written selected-width dividend header. -/
theorem convertedMemory_header_read
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    (convertedMemory mem aw baseFp baseSize k basePtr).readWithPadding baseFp 32 =
      UInt256.toByteArray (UInt256.ofNat (baseWords baseSize k)) := by
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hheader : (baseAllocatedMemory mem baseFp baseSize k).readWithPadding baseFp 32 =
      UInt256.toByteArray (UInt256.ofNat (baseWords baseSize k)) := by
    unfold baseAllocatedMemory
    apply storeBytesLength_read_self
    rwa [hsetSize]
  have hnaturalFit :
      baseFp + 32 + 32 * ((baseSize + 31) / 32) < UInt256.size := by
    have hfullFit : baseFp + 32 + 32 * baseWords baseSize k < UInt256.size := by
      have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      simpa [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hb
    have hnaturalLe : (baseSize + 31) / 32 ≤ baseWords baseSize k := Nat.le_max_left _ _
    omega
  have hpreserved := MultiLimbOddConversionSemantic.bytesToLimbsMemory_read_below_contiguous
    (baseAllocatedMemory mem baseFp baseSize k)
    (baseAllocatedWords aw baseFp baseSize k) basePtr.toNat baseFp baseSize baseFp
    hbaseSize hallocatedSize (by omega) hnaturalFit
  simpa only [convertedMemory, u256_ofNat_toNat] using hpreserved.trans hheader

/-- Base allocation and conversion preserve the allocator's advanced free pointer at `0x40`. -/
theorem convertedMemory_free_read
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseFp : 96 ≤ baseFp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    (convertedMemory mem aw baseFp baseSize k basePtr).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (baseFp + wordArrayAllocationSize (baseWords baseSize k))) := by
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocatedRead :
      (baseAllocatedMemory mem baseFp baseSize k).readWithPadding 64 32 =
        UInt256.toByteArray
          (UInt256.ofNat (baseFp + wordArrayAllocationSize (baseWords baseSize k))) := by
    unfold baseAllocatedMemory
    rw [storeBytesLength_read_below]
    · exact setFreePtr_read64 hmemSize
    · rw [hsetSize]
      exact hmemSize
    · exact hbaseFp
    · rwa [hsetSize]
  have hfit : baseFp + 32 + 32 * ((baseSize + 31) / 32) < UInt256.size := by
    have hnaturalLe : (baseSize + 31) / 32 ≤ baseWords baseSize k := Nat.le_max_left _ _
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    omega
  have hpreserved := MultiLimbOddConversionSemantic.bytesToLimbsMemory_read_below_contiguous
    (baseAllocatedMemory mem baseFp baseSize k) (baseAllocatedWords aw baseFp baseSize k)
    basePtr.toNat baseFp baseSize 64 hbaseSize hallocatedSize (by omega) hfit
  simpa only [convertedMemory, u256_ofNat_toNat] using hpreserved.trans hallocatedRead

/-- The materialized natural-width prefix of the converted array denotes the source base. -/
theorem convertedNaturalValue_eq_model
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hsource96 : 96 ≤ basePtr.toNat + 32)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (convertedMemory mem aw baseFp baseSize k basePtr)
      baseFp (naturalWords baseSize)) =
      Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
  have hnaturalPos : 0 < naturalWords baseSize := by
    unfold naturalWords
    omega
  have hnaturalLe : naturalWords baseSize ≤ baseWords baseSize k := Nat.le_max_left _ _
  have hbaseWordsPos : 0 < baseWords baseSize k := lt_of_lt_of_le hnaturalPos hnaturalLe
  have hsetSize :
      (setFreePtr mem (baseFp + wordArrayAllocationSize (baseWords baseSize k))).size =
        mem.size := setFreePtr_size hmemSize
  have hallocatedSize : (baseAllocatedMemory mem baseFp baseSize k).size = baseFp + 32 := by
    unfold baseAllocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocationFit :
      baseFp + wordArrayAllocationSize (baseWords baseSize k) + 31 < UInt256.size := by
    exact lt_trans
      (by omega : baseFp + wordArrayAllocationSize (baseWords baseSize k) + 31 <
        2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw baseFp
    (baseWords baseSize k) hbaseWordsPos hawFit hallocationFit
  have hnaturalRange :
      baseFp + 32 + 32 * naturalWords baseSize ≤
        baseFp + 32 + 32 * baseWords baseSize k := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left 32 hnaturalLe) (baseFp + 32)
  have hnaturalFit :
      baseFp + 32 + 32 * ((baseSize + 31) / 32) < UInt256.size := by
    have hfullFit : baseFp + 32 + 32 * baseWords baseSize k < UInt256.size := by
      have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      simpa [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hb
    unfold naturalWords at hnaturalRange
    omega
  have hallocated64 : (baseAllocatedMemory mem baseFp baseSize k).size < 2 ^ 64 := by
    rw [hallocatedSize]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hsourceRead :
      (baseAllocatedMemory mem baseFp baseSize k).readWithPadding
          (basePtr.toNat + 32) baseSize =
        mem.readWithPadding (basePtr.toNat + 32) baseSize := by
    unfold baseAllocatedMemory
    rw [storeBytesLength_read_below_len_padded]
    · exact setFreePtr_read_above_len_padded hmemSize hsource96 (by omega) (by omega)
    · exact hsourceBefore
    · omega
    · omega
    · rwa [hsetSize]
  have hsourceValue :
      Model.bytesToNatPadded (baseAllocatedMemory mem baseFp baseSize k)
          (basePtr.toNat + 32) baseSize =
        Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
    exact model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) (by omega)
      hsourceRead
  rw [← hsourceValue]
  simpa only [convertedMemory, u256_ofNat_toNat, naturalWords] using
    MultiLimbOddConversionSemantic.bytesToLimbsMemory_value_eq_model_contiguous
      (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k)
      basePtr.toNat baseFp baseSize hbaseSize hsourceBefore hallocatedSize
      (by simpa [naturalWords] using le_trans hnaturalRange hrange.1)
      hrange.2 hnaturalFit hallocated64

/-- Zero-padding the materialized conversion to the selected division width preserves its value. -/
theorem convertedPaddedValue_eq_model
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hsource96 : 96 ≤ basePtr.toNat + 32)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (convertedMemory mem aw baseFp baseSize k basePtr)
      baseFp (baseWords baseSize k)) =
      Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
  have hnaturalLe : naturalWords baseSize ≤ baseWords baseSize k := Nat.le_max_left _ _
  have hgeometry := convertedGeometry mem aw basePtr baseFp baseSize k
    hbasePos hbaseSize hmemSize hmemLe hgap hsourceBefore hawFit hbound
  calc
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
        (convertedMemory mem aw baseFp baseSize k basePtr)
        baseFp (baseWords baseSize k)) =
        limbsToNat (MultiLimbMemoryModel.memoryLimbs
          (convertedMemory mem aw baseFp baseSize k basePtr)
          baseFp (naturalWords baseSize +
            (baseWords baseSize k - naturalWords baseSize))) := by
          rw [Nat.add_sub_of_le hnaturalLe]
    _ = limbsToNat (MultiLimbMemoryModel.memoryLimbs
          (convertedMemory mem aw baseFp baseSize k basePtr)
          baseFp (naturalWords baseSize)) := by
          apply MultiLimbMemoryModel.memoryLimbs_extend_zero_value
          rw [hgeometry.1]
    _ = Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize :=
      convertedNaturalValue_eq_model mem aw basePtr baseFp baseSize k
        hbasePos hbaseSize hmemSize hmemLe hgap hsource96 hsourceBefore hawFit hbound

/-- The exact guarded dividend words consumed by `schoolbookDiv`, including selected zero
padding up to `max(ceil(baseSize/32), k)`, denote the original base byte object. -/
theorem convertedArray_value_eq_model
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hgap : baseFp - mem.size < USize.size)
    (hsource96 : 96 ≤ basePtr.toNat + 32)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64) :
    wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (convertedMemory mem aw baseFp baseSize k basePtr)
        (convertedWords mem aw baseFp baseSize k basePtr)
        (UInt256.ofNat baseFp) 0 (baseWords baseSize k)) =
      Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
  have hgeometry := convertedGeometry mem aw basePtr baseFp baseSize k
    hbasePos hbaseSize hmemSize hmemLe hgap hsourceBefore hawFit hbound
  have hfullFit : baseFp + 32 * (baseWords baseSize k + 1) < UInt256.size := by
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    omega
  rw [MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryLimbs
    (convertedMemory mem aw baseFp baseSize k basePtr)
    (convertedWords mem aw baseFp baseSize k basePtr)
    baseFp (baseWords baseSize k) hfullFit hgeometry.2.2.1 hgeometry.2.2.2]
  exact convertedPaddedValue_eq_model mem aw basePtr baseFp baseSize k
    hbasePos hbaseSize hmemSize hmemLe hgap hsource96 hsourceBefore hawFit hbound

/-- Remainder allocation preserves an older padded word ending before the new array header. -/
theorem remainderMemory_read_below
    (mem : ByteArray) (aw basePtr : UInt256)
    (baseFp remFp baseSize k read : Nat)
    (hconverted96 : 96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hread96 : 96 ≤ read) (hbelow : read + 32 ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size) :
    (remainderMemory mem aw baseFp remFp baseSize k basePtr).readWithPadding read 32 =
      (convertedMemory mem aw baseFp baseSize k basePtr).readWithPadding read 32 := by
  unfold remainderMemory
  rw [storeBytesLength_read_below_len_padded]
  · exact setFreePtr_read_above_len_padded hconverted96 hread96 (by omega) (by omega)
  · exact hbelow
  · omega
  · omega
  · rwa [setFreePtr_size hconverted96]

/-- The remainder allocation also preserves the selected-width dividend header. -/
theorem remainderMemory_baseHeader_read
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (hbaseBound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 ≤ remFp)
    (hconverted96 : 96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size) :
    (remainderMemory mem aw baseFp remFp baseSize k basePtr).readWithPadding baseFp 32 =
      UInt256.toByteArray (UInt256.ofNat (baseWords baseSize k)) := by
  have hpreserved := remainderMemory_read_below mem aw basePtr baseFp remFp baseSize k
    baseFp hconverted96 (by omega) hbaseEnd hremGap
  exact hpreserved.trans (convertedMemory_header_read mem aw basePtr baseFp baseSize k
    hbaseSize hmemSize hmemLe hbaseGap hbaseBound)

/-- The remainder allocator writes its selected limb count at the new array header. -/
theorem remainderMemory_remHeader_read
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hconverted96 : 96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size) :
    (remainderMemory mem aw baseFp remFp baseSize k basePtr).readWithPadding remFp 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  unfold remainderMemory
  apply storeBytesLength_read_self
  rwa [setFreePtr_size hconverted96]

/-- The active-word counter returned by remainder allocation covers its entire implicit payload. -/
theorem remainderWords_range
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hkPos : 0 < k)
    (hconvertedFit :
      (convertedWords mem aw baseFp baseSize k basePtr).toNat * 32 < UInt256.size)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64) :
    remFp + 32 + 32 * k ≤
        32 * (remainderWords mem aw baseFp remFp baseSize k basePtr).toNat ∧
      (remainderWords mem aw baseFp remFp baseSize k basePtr).toNat * 32 <
        UInt256.size := by
  apply MultiLimbOddConversionSemantic.newWordArrayWords_range
  · exact hkPos
  · exact hconvertedFit
  · exact lt_trans (by omega : remFp + wordArrayAllocationSize k + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])

/-- Remainder allocation leaves the newly advanced Solidity free pointer at `0x40`. -/
theorem remainderMemory_free_read
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hconverted96 : 96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hremFp : 96 ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size) :
    (remainderMemory mem aw baseFp remFp baseSize k basePtr).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (remFp + wordArrayAllocationSize k)) := by
  unfold remainderMemory
  rw [storeBytesLength_read_below]
  · exact setFreePtr_read64 hconverted96
  · rw [setFreePtr_size hconverted96]
    exact hconverted96
  · omega
  · rwa [setFreePtr_size hconverted96]

/-- The final `schoolbookDiv` allocation has covered memory and a representable active extent. -/
theorem remainderGeometry
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hkPos : 0 < k)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbaseBound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64)
    (hconvertedLe : (convertedMemory mem aw baseFp baseSize k basePtr).size ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64) :
    (remainderMemory mem aw baseFp remFp baseSize k basePtr).size = remFp + 32 ∧
      MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        (remainderMemory mem aw baseFp remFp baseSize k basePtr)
        (remainderWords mem aw baseFp remFp baseSize k basePtr) ∧
      (remainderWords mem aw baseFp remFp baseSize k basePtr).toNat * 32 <
        UInt256.size := by
  have hconverted := convertedGeometry mem aw basePtr baseFp baseSize k hbasePos hbaseSize
    hmemSize hmemLe hbaseGap hsourceBefore hawFit hbaseBound
  have hconverted96 :
      96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size := by
    rw [hconverted.1]
    omega
  have hsetSize :
      (setFreePtr (convertedMemory mem aw baseFp baseSize k basePtr)
        (remFp + wordArrayAllocationSize k)).size =
        (convertedMemory mem aw baseFp baseSize k basePtr).size :=
    setFreePtr_size hconverted96
  have hfinalSize :
      (remainderMemory mem aw baseFp remFp baseSize k basePtr).size = remFp + 32 := by
    unfold remainderMemory
    apply storeBytesLength_size
    · rwa [hsetSize]
    · rwa [hsetSize]
  have hremFit : remFp + wordArrayAllocationSize k + 31 < UInt256.size := by
    exact lt_trans (by omega : remFp + wordArrayAllocationSize k + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range
    (convertedWords mem aw baseFp baseSize k basePtr) remFp k hkPos
    hconverted.2.2.2 hremFit
  refine ⟨hfinalSize, ?_, hrange.2⟩
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
  rw [hfinalSize]
  exact le_trans (by omega) hrange.1

/-- The padded dividend payload remains the source base after allocating the remainder array. -/
theorem remainderPaddedBaseValue_eq_model
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (hsource96 : 96 ≤ basePtr.toNat + 32)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbaseBound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 + 32 * baseWords baseSize k ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (remainderMemory mem aw baseFp remFp baseSize k basePtr)
      baseFp (baseWords baseSize k)) =
      Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
  have hconverted := convertedGeometry mem aw basePtr baseFp baseSize k hbasePos hbaseSize
    hmemSize hmemLe hbaseGap hsourceBefore hawFit hbaseBound
  have hconverted96 :
      96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size := by
    rw [hconverted.1]
    omega
  rw [MultiLimbMemoryModel.memoryLimbs_eq_of_readWithPadding_eq
    (convertedMemory mem aw baseFp baseSize k basePtr)
    (remainderMemory mem aw baseFp remFp baseSize k basePtr)
    baseFp (baseWords baseSize k) (by
      intro i hi
      apply remainderMemory_read_below
      · exact hconverted96
      · omega
      · omega
      · exact hremGap)]
  exact convertedPaddedValue_eq_model mem aw basePtr baseFp baseSize k hbasePos hbaseSize
    hmemSize hmemLe hbaseGap hsource96 hsourceBefore hawFit hbaseBound

/-- At the real division-entry state, guarded dividend loads still denote the source base. -/
theorem remainderArrayBase_value_eq_model
    (mem : ByteArray) (aw basePtr : UInt256) (baseFp remFp baseSize k : Nat)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024) (hkPos : 0 < k)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (hsource96 : 96 ≤ basePtr.toNat + 32)
    (hsourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbaseBound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 + 32 * baseWords baseSize k ≤ remFp)
    (hconvertedLe : (convertedMemory mem aw baseFp baseSize k basePtr).size ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64) :
    wordLimbsToNat (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (remainderMemory mem aw baseFp remFp baseSize k basePtr)
      (remainderWords mem aw baseFp remFp baseSize k basePtr)
      (UInt256.ofNat baseFp) 0 (baseWords baseSize k)) =
      Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
  have hfinal := remainderGeometry mem aw basePtr baseFp remFp baseSize k hbasePos
    hbaseSize hkPos hmemSize hmemLe hbaseGap hsourceBefore hawFit hbaseBound
    hconvertedLe hremGap hremBound
  have hbaseFit : baseFp + 32 * (baseWords baseSize k + 1) < UInt256.size := by
    have hb := lt_trans hbaseBound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    omega
  rw [MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryLimbs
    (remainderMemory mem aw baseFp remFp baseSize k basePtr)
    (remainderWords mem aw baseFp remFp baseSize k basePtr)
    baseFp (baseWords baseSize k) hbaseFit hfinal.2.1 hfinal.2.2]
  exact remainderPaddedBaseValue_eq_model mem aw basePtr baseFp remFp baseSize k
    hbasePos hbaseSize hmemSize hmemLe hbaseGap hsource96 hsourceBefore hawFit
    hbaseBound hbaseEnd hremGap

end Modexp.MultiLimbReduceBaseSemantic
