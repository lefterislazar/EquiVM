import Examples.Precompiles.Modexp.MultiLimbBarrettConversionContract
import Examples.Precompiles.Modexp.MultiLimbReduceBaseSemantic

/-!
# Source-value semantics at the Barrett division entry

This module carries the converted modulus through base allocation, base conversion, and remainder
allocation.  It proves that both guarded arrays observed by the real `schoolbookDiv` entry retain
their source byte values after all intervening memory writes.
-/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbBarrettReduceBaseSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

def modulusMemory (mem : ByteArray) (aw : UInt256)
    (modulusFp dataPtr modulusSize : Nat) : ByteArray :=
  MultiLimbBarrettConversion.convertedMemory mem aw modulusFp dataPtr modulusSize

def modulusWords (mem : ByteArray) (aw : UInt256)
    (modulusFp dataPtr modulusSize : Nat) : UInt256 :=
  MultiLimbBarrettConversion.convertedWords mem aw modulusFp dataPtr modulusSize

def finalMemory (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat) : ByteArray :=
  MultiLimbReduceBase.remainderMemory
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize)
    baseFp remFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr

def finalWords (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat) : UInt256 :=
  MultiLimbReduceBase.remainderWords
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize)
    baseFp remFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr

/-- The composed modulus/base/remainder allocations provide covered memory at the concrete
`schoolbookDiv` entry. -/
theorem finalGeometry
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64) :
    (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize).size =
        remFp + 32 ∧
      MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize) ∧
      (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize).toNat *
          32 < UInt256.size := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  simpa only [finalMemory, finalWords, modulusMemory, modulusWords] using
    MultiLimbReduceBaseSemantic.remainderGeometry
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
      (MultiLimbBarrettConversion.words modulusSize) hbasePos hbaseSize (by
        unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
        omega) (by unfold modulusMemory; rw [hmodGeometry.1]; omega)
      hmodulusMemoryLe hbaseGap hbaseSourceBefore hmodGeometry.2.2.2
      hbaseAllocationBound hbaseConvertedLe hremGap hremBound

/-- The divisor header written by its allocator survives every later allocation. -/
theorem finalModulusHeader_read
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusEnd : modulusFp + 32 ≤ baseFp)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size) :
    ByteArray.readWithPadding
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        modulusFp 32 =
      UInt256.toByteArray
        (UInt256.ofNat (MultiLimbBarrettConversion.words modulusSize)) := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hmodulusMemory96 : 96 ≤
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size := by
    unfold modulusMemory
    rw [hmodGeometry.1]
    omega
  have hbaseConvertedSize := MultiLimbReduceBaseSemantic.convertedMemory_size_eq
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap hbaseAllocationBound
  have hbaseConverted96 : 96 ≤
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size := by
    rw [hbaseConvertedSize]
    omega
  have hbaseRead := MultiLimbReduceBaseSemantic.convertedMemory_read_below
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) modulusFp hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap (by omega) hmodulusEnd hbaseAllocationBound
  have hfinalRead := MultiLimbReduceBaseSemantic.remainderMemory_read_below
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) modulusFp hbaseConverted96 (by omega)
    (by omega) hremGap
  exact hfinalRead.trans (hbaseRead.trans
    (MultiLimbBarrettConversion.convertedMemory_header_read mem aw modulusFp dataPtr
      modulusSize hmodulusBound hmemSize hmemLe hmodulusGap hmodulusAllocationBound))

/-- The selected-width dividend header survives remainder allocation. -/
theorem finalBaseHeader_read
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 ≤ remFp)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size) :
    ByteArray.readWithPadding
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        baseFp 32 =
      UInt256.toByteArray (UInt256.ofNat (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize))) := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hmodulusMemory96 : 96 ≤
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size := by
    unfold modulusMemory
    rw [hmodGeometry.1]
    omega
  have hbaseConvertedSize := MultiLimbReduceBaseSemantic.convertedMemory_size_eq
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap hbaseAllocationBound
  have hbaseConverted96 : 96 ≤
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size := by
    rw [hbaseConvertedSize]
    omega
  simpa only [finalMemory, modulusMemory, modulusWords] using
    MultiLimbReduceBaseSemantic.remainderMemory_baseHeader_read
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
      (MultiLimbBarrettConversion.words modulusSize) hbaseSize hmodulusMemory96
      hmodulusMemoryLe hbaseGap hbaseAllocationBound hbaseEnd hbaseConverted96 hremGap

/-- The final free-pointer word names the first location after the remainder allocation. -/
theorem finalFree_read
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size) :
    ByteArray.readWithPadding
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        64 32 =
      UInt256.toByteArray (UInt256.ofNat (remFp + wordArrayAllocationSize
        (MultiLimbBarrettConversion.words modulusSize))) := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hmodulusMemory96 : 96 ≤
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size := by
    unfold modulusMemory
    rw [hmodGeometry.1]
    omega
  have hbaseConvertedSize := MultiLimbReduceBaseSemantic.convertedMemory_size_eq
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap hbaseAllocationBound
  have hbaseConverted96 : 96 ≤
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size := by
    rw [hbaseConvertedSize]
    omega
  simpa only [finalMemory, modulusMemory, modulusWords] using
    MultiLimbReduceBaseSemantic.remainderMemory_free_read
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
      (MultiLimbBarrettConversion.words modulusSize) hbaseConverted96 (by omega) hremGap

/-- The final remainder array has the selected modulus width in its concrete header. -/
theorem finalRemainderHeader_read
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size) :
    ByteArray.readWithPadding
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        remFp 32 =
      UInt256.toByteArray
        (UInt256.ofNat (MultiLimbBarrettConversion.words modulusSize)) := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hmodulusMemory96 : 96 ≤
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size := by
    unfold modulusMemory
    rw [hmodGeometry.1]
    omega
  have hbaseConvertedSize := MultiLimbReduceBaseSemantic.convertedMemory_size_eq
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap hbaseAllocationBound
  have hbaseConverted96 : 96 ≤
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size := by
    rw [hbaseConvertedSize]
    omega
  simpa only [finalMemory, modulusMemory, modulusWords] using
    MultiLimbReduceBaseSemantic.remainderMemory_remHeader_read
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
      (MultiLimbBarrettConversion.words modulusSize) hbaseConverted96 hremGap

/-- The fresh remainder array has a complete covered layout even though its zero payload is still
implicit beyond the concrete byte-array frontier. -/
theorem finalRemainderLayout
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64) :
    MultiLimbArrayReadSemantic.Layout
      (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      remFp (MultiLimbBarrettConversion.words modulusSize) := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hmodulusMemory96 : 96 ≤
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size := by
    unfold modulusMemory
    rw [hmodGeometry.1]
    omega
  have hbaseGeometry := MultiLimbReduceBaseSemantic.convertedGeometry
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbasePos hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap hbaseSourceBefore hmodGeometry.2.2.2 hbaseAllocationBound
  have hrange := MultiLimbReduceBaseSemantic.remainderWords_range
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) (by
      unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
      omega) hbaseGeometry.2.2.2 hremBound
  have hheader := finalRemainderHeader_read mem aw basePtr modulusFp dataPtr modulusSize
    baseFp remFp baseSize hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap
    hmodulusSourceBefore hawFit hmodulusAllocationBound hmodulusMemoryLe hbaseGap
    hbaseSize hbaseAllocationBound hremGap
  apply MultiLimbArrayReadSemantic.layout_of_geometry
  · have hb := lt_trans hremBound
      (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    omega
  · have hgeometry := finalGeometry mem aw basePtr modulusFp dataPtr modulusSize baseFp
      remFp baseSize hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap
      hmodulusSourceBefore hawFit hmodulusAllocationBound hmodulusMemoryLe hbaseGap
      hbasePos hbaseSize hbaseSourceBefore hbaseAllocationBound hbaseConvertedLe hremGap
      hremBound
    rw [hgeometry.1]
  · simpa only [finalWords, modulusMemory, modulusWords] using hrange.1
  · simpa only [finalWords, modulusMemory, modulusWords] using hrange.2
  · exact hheader

/-- Both arrays at PC 5199 have the ordinary covered layout required by trimming, short division,
and normalized Knuth division. -/
theorem finalLayouts
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusEnd : modulusFp + 32 +
      32 * MultiLimbBarrettConversion.words modulusSize ≤ baseFp)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 + 32 * MultiLimbReduceBase.baseWords baseSize
      (MultiLimbBarrettConversion.words modulusSize) ≤ remFp)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64) :
    MultiLimbArrayReadSemantic.Layout
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        baseFp (MultiLimbReduceBase.baseWords baseSize
          (MultiLimbBarrettConversion.words modulusSize)) ∧
      MultiLimbArrayReadSemantic.Layout
        (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
        modulusFp (MultiLimbBarrettConversion.words modulusSize) := by
  have hgeometry := finalGeometry mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp
    baseSize hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap
    hmodulusSourceBefore hawFit hmodulusAllocationBound hmodulusMemoryLe hbaseGap
    hbasePos hbaseSize hbaseSourceBefore hbaseAllocationBound hbaseConvertedLe hremGap
    hremBound
  have hbaseHeader := finalBaseHeader_read mem aw basePtr modulusFp dataPtr modulusSize
    baseFp remFp baseSize hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap
    hmodulusSourceBefore hawFit hmodulusAllocationBound hmodulusMemoryLe hbaseGap
    hbaseSize hbaseAllocationBound (by omega) hbaseConvertedLe hremGap
  have hmodulusHeader := finalModulusHeader_read mem aw basePtr modulusFp dataPtr
    modulusSize baseFp remFp baseSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound (by omega)
    hmodulusMemoryLe hbaseGap hbaseSize hbaseAllocationBound hbaseConvertedLe hremGap
  have hcovered := hgeometry.2.1
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
  constructor
  · apply MultiLimbArrayReadSemantic.layout_of_geometry
    · have hb := lt_trans hbaseAllocationBound
        (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega
    · rw [hgeometry.1]
      omega
    · rw [hgeometry.1] at hcovered
      omega
    · exact hgeometry.2.2
    · exact hbaseHeader
  · apply MultiLimbArrayReadSemantic.layout_of_geometry
    · have hb := lt_trans hmodulusAllocationBound
        (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
      unfold wordArrayAllocationSize wordArrayPayloadSize at hb
      omega
    · rw [hgeometry.1]
      omega
    · rw [hgeometry.1] at hcovered
      omega
    · exact hgeometry.2.2
    · exact hmodulusHeader

/-- The final padded divisor payload is unchanged by base and remainder allocation. -/
theorem finalModulusPaddedValue_eq_model
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmodulusFp : 96 ≤ modulusFp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSource96 : 96 ≤ dataPtr + 32)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound :
      modulusFp + wordArrayAllocationSize (MultiLimbBarrettConversion.words modulusSize) <
        2 ^ 64)
    (hmodulusEnd :
      modulusFp + 32 + 32 * MultiLimbBarrettConversion.words modulusSize ≤ baseFp)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      modulusFp (MultiLimbBarrettConversion.words modulusSize)) =
      Model.bytesToNatPadded mem (dataPtr + 32) modulusSize := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hbaseFp : 96 ≤ baseFp := by omega
  have hmodulusMemory96 : 96 ≤
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size := by
    unfold modulusMemory
    rw [hmodGeometry.1]
    omega
  have hbaseConvertedSize := MultiLimbReduceBaseSemantic.convertedMemory_size_eq
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbaseSize hmodulusMemory96
    hmodulusMemoryLe hbaseGap hbaseAllocationBound
  have hbaseConverted96 :
      96 ≤ (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size := by
    rw [hbaseConvertedSize]
    omega
  have hlimbs : MultiLimbMemoryModel.memoryLimbs
      (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      modulusFp (MultiLimbBarrettConversion.words modulusSize) =
    MultiLimbMemoryModel.memoryLimbs
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      modulusFp (MultiLimbBarrettConversion.words modulusSize) := by
    apply MultiLimbMemoryModel.memoryLimbs_eq_of_readWithPadding_eq
    intro i hi
    let read := modulusFp + 32 + 32 * i
    have hreadBelow : read + 32 ≤ baseFp := by
      dsimp only [read]
      omega
    have hbaseRead := MultiLimbReduceBaseSemantic.convertedMemory_read_below
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr
      baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) read hbaseSize
      hmodulusMemory96 hmodulusMemoryLe hbaseGap (by
        dsimp only [read]
        omega) hreadBelow hbaseAllocationBound
    have hfinalRead := MultiLimbReduceBaseSemantic.remainderMemory_read_below
      (modulusMemory mem aw modulusFp dataPtr modulusSize)
      (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr
      baseFp remFp baseSize (MultiLimbBarrettConversion.words modulusSize) read
      hbaseConverted96 (by dsimp only [read]; omega) (by
        have hbaseFpLe : baseFp ≤ remFp := by
          rw [hbaseConvertedSize] at hbaseConvertedLe
          omega
        omega) hremGap
    exact hfinalRead.trans hbaseRead
  rw [hlimbs]
  exact MultiLimbBarrettConversion.convertedMemory_value_eq_model mem aw modulusFp dataPtr
    modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe hmodulusGap
    hmodulusSource96 hmodulusSourceBefore hawFit hmodulusAllocationBound

/-- Guarded divisor loads at the final `schoolbookDiv` entry denote the source modulus. -/
theorem finalModulusArrayValue_eq_model
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmodulusFp : 96 ≤ modulusFp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSource96 : 96 ≤ dataPtr + 32)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusEnd : modulusFp + 32 +
      32 * MultiLimbBarrettConversion.words modulusSize ≤ baseFp)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64) :
    wordLimbsToNat (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      (UInt256.ofNat modulusFp) 0 (MultiLimbBarrettConversion.words modulusSize)) =
      Model.bytesToNatPadded mem (dataPtr + 32) modulusSize := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hfinalGeometry := MultiLimbReduceBaseSemantic.remainderGeometry
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbasePos hbaseSize (by
      unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
      omega) (by unfold modulusMemory; rw [hmodGeometry.1]; omega)
    hmodulusMemoryLe hbaseGap
    hbaseSourceBefore hmodGeometry.2.2.2 hbaseAllocationBound hbaseConvertedLe hremGap
    hremBound
  have hmodulusFit : modulusFp +
      32 * (MultiLimbBarrettConversion.words modulusSize + 1) < UInt256.size := by
    have hb := lt_trans hmodulusAllocationBound
      (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    omega
  rw [MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryLimbs
    (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
    (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
    modulusFp (MultiLimbBarrettConversion.words modulusSize) hmodulusFit
    hfinalGeometry.2.1 hfinalGeometry.2.2]
  exact finalModulusPaddedValue_eq_model mem aw basePtr modulusFp dataPtr modulusSize
    baseFp remFp baseSize hmodulusLarge hmodulusBound hmodulusFp hmemSize hmemLe
    hmodulusGap hmodulusSource96 hmodulusSourceBefore hawFit hmodulusAllocationBound
    hmodulusEnd hmodulusMemoryLe hbaseGap hbaseSize hbaseAllocationBound
    hbaseConvertedLe hremGap

/-- Guarded dividend loads at the same entry denote the source base after all allocations. -/
theorem finalBaseArrayValue_eq_model
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hbaseSource96 : 96 ≤ basePtr.toNat + 32)
    (hbaseBeforeModulus : basePtr.toNat + 32 + baseSize ≤ modulusFp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusMemoryLe :
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (modulusMemory mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 + 32 * MultiLimbReduceBase.baseWords baseSize
      (MultiLimbBarrettConversion.words modulusSize) ≤ remFp)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (modulusMemory mem aw modulusFp dataPtr modulusSize)
        (modulusWords mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64) :
    wordLimbsToNat (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (finalMemory mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      (finalWords mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize)
      (UInt256.ofNat baseFp) 0
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize))) =
      Model.bytesToNatPadded mem (basePtr.toNat + 32) baseSize := by
  have hmodGeometry := MultiLimbBarrettConversion.convertedGeometry
    mem aw modulusFp dataPtr modulusSize hmodulusLarge hmodulusBound hmemSize hmemLe
    hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
  have hbaseValue := MultiLimbReduceBaseSemantic.remainderArrayBase_value_eq_model
    (modulusMemory mem aw modulusFp dataPtr modulusSize)
    (modulusWords mem aw modulusFp dataPtr modulusSize) basePtr baseFp remFp baseSize
    (MultiLimbBarrettConversion.words modulusSize) hbasePos hbaseSize (by
      unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
      omega) (by unfold modulusMemory; rw [hmodGeometry.1]; omega) hmodulusMemoryLe
    hbaseGap hbaseSource96 hbaseSourceBefore hmodGeometry.2.2.2
    hbaseAllocationBound hbaseEnd hbaseConvertedLe hremGap hremBound
  have hsourceValue := MultiLimbBarrettConversion.convertedMemory_sourceValue_eq
    mem aw modulusFp dataPtr modulusSize (basePtr.toNat + 32) baseSize hmodulusBound
    hmemSize hmemLe hmodulusGap hbaseSource96 hbaseBeforeModulus hbasePos
    (lt_of_le_of_lt hbaseSize (by norm_num : 1024 < 2 ^ 64))
    hmodulusAllocationBound
  simpa only [finalMemory, finalWords, modulusMemory, modulusWords] using
    hbaseValue.trans hsourceValue

end Modexp.MultiLimbBarrettReduceBaseSemantic
