import Examples.Precompiles.Modexp.Allocation
import Examples.Precompiles.Modexp.MultiLimbBarrettDispatch
import Examples.Precompiles.Modexp.MultiLimbBytesToLimbsCall
import Examples.Precompiles.Modexp.MultiLimbOddConversionSemantic
import Examples.Precompiles.Modexp.MultiLimbArrayReadSemantic

/-!
# Direct Barrett modulus-conversion contract

This module composes the direct multi-limb Barrett body, the shared word-array allocator, and the
complete generated `bytesToLimbs` execution.  Its explicit memory premises are exactly the facts
the public copied-operand layout must provide: a valid free pointer before allocation and the
preserved modulus bytes object after allocation.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettConversion

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def words (modulusSize : Nat) : Nat :=
  MultiLimbBarrettDispatch.limbCount modulusSize

def allocatedMemory (mem : ByteArray) (fp modulusSize : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr mem (fp + wordArrayAllocationSize (words modulusSize)))
    fp (words modulusSize)

def allocatedWords (aw : UInt256) (fp modulusSize : Nat) : UInt256 :=
  newWordArrayWords aw fp (words modulusSize)

def continuation (exp base retBar result ret : UInt256) (modulusSize : Nat)
    (tail : List UInt256) : List UInt256 :=
  UInt256.ofNat (words modulusSize) :: ⟨1707⟩ :: base :: exp ::
    UInt256.ofNat (words modulusSize) :: ⟨1745⟩ :: result ::
    UInt256.ofNat modulusSize :: ⟨805⟩ :: retBar :: result :: ret :: tail

def convertedMemory (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat) :
    ByteArray :=
  MultiLimbGenerated.bytesToLimbsMemory
    (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
    (UInt256.ofNat dataPtr) (UInt256.ofNat fp) modulusSize

def convertedWords (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat) :
    UInt256 :=
  MultiLimbGenerated.bytesToLimbsActiveWords
    (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
    (UInt256.ofNat dataPtr) (UInt256.ofNat fp) modulusSize

def conversionGas (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat) : Nat :=
  98 + newWordArrayGas aw fp (words modulusSize) +
    MultiLimbGenerated.bytesToLimbsGas
      (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
      (UInt256.ofNat dataPtr) (UInt256.ofNat fp) modulusSize

def conversionSteps (modulusSize : Nat) : Nat :=
  109 + MultiLimbGenerated.bytesToLimbsSteps modulusSize

def scanConversionGas (mem : ByteArray) (aw : UInt256)
    (fp dataPtr modulusSize : Nat) : Nat :=
  239 + conversionGas mem aw fp dataPtr modulusSize

/-- Modulus allocation and conversion preserve every older bounded padded slice below `fp`. -/
theorem convertedMemory_read_below_len
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize read len : Nat)
    (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hread96 : 96 ≤ read) (hbelow : read + len ≤ fp)
    (hlenPos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    (convertedMemory mem aw fp dataPtr modulusSize).readWithPadding read len =
      mem.readWithPadding read len := by
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (words modulusSize))).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : (allocatedMemory mem fp modulusSize).size = fp + 32 := by
    unfold allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocatedRead :
      (allocatedMemory mem fp modulusSize).readWithPadding read len =
        mem.readWithPadding read len := by
    unfold allocatedMemory
    rw [storeBytesLength_read_below_len_padded]
    · exact setFreePtr_read_above_len_padded hmemSize hread96 hlenPos hlen64
    · exact hbelow
    · exact hlenPos
    · exact hlen64
    · rwa [hsetSize]
  have hconvertedFit :
      fp + 32 + 32 * ((modulusSize + 31) / 32) < UInt256.size := by
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    simpa [wordArrayAllocationSize, wordArrayPayloadSize, words,
      MultiLimbBarrettDispatch.limbCount, Nat.add_assoc] using hb
  have hconvertedRead :=
    MultiLimbOddConversionSemantic.bytesToLimbsMemory_read_below_len_contiguous
      (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
      dataPtr fp modulusSize read len hmodulusBound hallocatedSize (by omega)
      hlenPos hlen64 hconvertedFit
  exact hconvertedRead.trans hallocatedRead

/-- Any older byte object before the modulus allocation retains its trusted numeric value. -/
theorem convertedMemory_sourceValue_eq
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize read len : Nat)
    (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hread96 : 96 ≤ read) (hbelow : read + len ≤ fp)
    (hlenPos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    Model.bytesToNatPadded (convertedMemory mem aw fp dataPtr modulusSize) read len =
      Model.bytesToNatPadded mem read len := by
  exact model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) hlen64
    (convertedMemory_read_below_len mem aw fp dataPtr modulusSize read len
      hmodulusBound hmemSize hmemLe hgap hread96 hbelow hlenPos hlen64 hbound)

/-- The conversion payload stores preserve the allocator-written modulus array header. -/
theorem convertedMemory_header_read
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat)
    (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    (convertedMemory mem aw fp dataPtr modulusSize).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (words modulusSize)) := by
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (words modulusSize))).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : (allocatedMemory mem fp modulusSize).size = fp + 32 := by
    unfold allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hheader : (allocatedMemory mem fp modulusSize).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (words modulusSize)) := by
    unfold allocatedMemory
    apply storeBytesLength_read_self
    rwa [hsetSize]
  have hfit : fp + 32 + 32 * ((modulusSize + 31) / 32) < UInt256.size := by
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    simpa [wordArrayAllocationSize, wordArrayPayloadSize, words,
      MultiLimbBarrettDispatch.limbCount, Nat.add_assoc] using hb
  have hpreserved := MultiLimbOddConversionSemantic.bytesToLimbsMemory_read_below_contiguous
    (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
    dataPtr fp modulusSize fp hmodulusBound hallocatedSize (by omega) hfit
  exact hpreserved.trans hheader

/-- Modulus allocation and conversion preserve the allocator's newly advanced free pointer. -/
theorem convertedMemory_free_read
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat)
    (hmodulusBound : modulusSize ≤ 1024)
    (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    (convertedMemory mem aw fp dataPtr modulusSize).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (fp + wordArrayAllocationSize (words modulusSize))) := by
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (words modulusSize))).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : (allocatedMemory mem fp modulusSize).size = fp + 32 := by
    unfold allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocatedRead :
      (allocatedMemory mem fp modulusSize).readWithPadding 64 32 =
        UInt256.toByteArray
          (UInt256.ofNat (fp + wordArrayAllocationSize (words modulusSize))) := by
    unfold allocatedMemory
    rw [storeBytesLength_read_below]
    · exact setFreePtr_read64 hmemSize
    · rw [hsetSize]
      exact hmemSize
    · exact hfp
    · rwa [hsetSize]
  have hfit : fp + 32 + 32 * ((modulusSize + 31) / 32) < UInt256.size := by
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    simpa [wordArrayAllocationSize, wordArrayPayloadSize, words,
      MultiLimbBarrettDispatch.limbCount, Nat.add_assoc] using hb
  have hpreserved := MultiLimbOddConversionSemantic.bytesToLimbsMemory_read_below_contiguous
    (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
    dataPtr fp modulusSize 64 hmodulusBound hallocatedSize (by omega) hfit
  exact hpreserved.trans hallocatedRead

/-- Allocation followed by conversion produces a fully materialized, covered modulus array. -/
theorem convertedGeometry
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hsourceBefore : dataPtr + 32 + modulusSize ≤ fp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    (convertedMemory mem aw fp dataPtr modulusSize).size =
        fp + 32 + 32 * words modulusSize ∧
      convertedWords mem aw fp dataPtr modulusSize = allocatedWords aw fp modulusSize ∧
      MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        (convertedMemory mem aw fp dataPtr modulusSize)
        (convertedWords mem aw fp dataPtr modulusSize) ∧
      (convertedWords mem aw fp dataPtr modulusSize).toNat * 32 < UInt256.size := by
  have hwordsPos : 0 < words modulusSize := by
    unfold words MultiLimbBarrettDispatch.limbCount
    omega
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (words modulusSize))).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : (allocatedMemory mem fp modulusSize).size = fp + 32 := by
    unfold allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocationFit :
      fp + wordArrayAllocationSize (words modulusSize) + 31 < UInt256.size := by
    exact lt_trans (by omega : fp + wordArrayAllocationSize (words modulusSize) + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (words modulusSize) hwordsPos hawFit hallocationFit
  have hconvertedFit : fp + 32 + 32 * words modulusSize < UInt256.size := by
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    simpa [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hb
  have hconvertedSize :
      (convertedMemory mem aw fp dataPtr modulusSize).size =
        fp + 32 + 32 * words modulusSize := by
    unfold convertedMemory
    simpa [words, MultiLimbBarrettDispatch.limbCount] using
      MultiLimbOddConversionSemantic.bytesToLimbsMemory_size_contiguous
        (allocatedMemory mem fp modulusSize) (allocatedWords aw fp modulusSize)
        dataPtr fp modulusSize hmodulusBound hallocatedSize (by
          simpa [words, MultiLimbBarrettDispatch.limbCount] using hconvertedFit)
  have hconvertedWords :
      convertedWords mem aw fp dataPtr modulusSize = allocatedWords aw fp modulusSize := by
    unfold convertedWords
    apply MultiLimbOddConversionSemantic.bytesToLimbsActiveWords_eq_contiguous
    · exact hmodulusBound
    · exact hsourceBefore
    · simpa [words, MultiLimbBarrettDispatch.limbCount] using hrange.1
    · simpa [words, MultiLimbBarrettDispatch.limbCount] using hconvertedFit
  refine ⟨hconvertedSize, hconvertedWords, ?_, ?_⟩
  · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hconvertedSize, hconvertedWords]
    exact hrange.1
  · rw [hconvertedWords]
    exact hrange.2

/-- The concrete allocated-and-converted modulus array denotes exactly the source byte object. -/
theorem convertedMemory_value_eq_model
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hsource96 : 96 ≤ dataPtr + 32)
    (hsourceBefore : dataPtr + 32 + modulusSize ≤ fp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    limbsToNat (MultiLimbMemoryModel.memoryLimbs
      (convertedMemory mem aw fp dataPtr modulusSize) fp (words modulusSize)) =
    Model.bytesToNatPadded mem (dataPtr + 32) modulusSize := by
  have hwordsPos : 0 < words modulusSize := by
    unfold words MultiLimbBarrettDispatch.limbCount
    omega
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (words modulusSize))).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : (allocatedMemory mem fp modulusSize).size = fp + 32 := by
    unfold allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hallocationFit :
      fp + wordArrayAllocationSize (words modulusSize) + 31 < UInt256.size := by
    exact lt_trans (by omega : fp + wordArrayAllocationSize (words modulusSize) + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (words modulusSize) hwordsPos hawFit hallocationFit
  have hactive : fp + 32 + 32 * ((modulusSize + 31) / 32) ≤
      32 * (allocatedWords aw fp modulusSize).toNat := by
    simpa [allocatedWords, words, MultiLimbBarrettDispatch.limbCount] using hrange.1
  have hconvertedFit : fp + 32 + 32 * ((modulusSize + 31) / 32) < UInt256.size := by
    have hb := lt_trans hbound (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    simpa [wordArrayAllocationSize, wordArrayPayloadSize, words,
      MultiLimbBarrettDispatch.limbCount, Nat.add_assoc] using hb
  have hallocated64 : (allocatedMemory mem fp modulusSize).size < 2 ^ 64 := by
    rw [hallocatedSize]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hsourceRead :
      (allocatedMemory mem fp modulusSize).readWithPadding (dataPtr + 32) modulusSize =
        mem.readWithPadding (dataPtr + 32) modulusSize := by
    unfold allocatedMemory
    rw [storeBytesLength_read_below_len_padded]
    · exact setFreePtr_read_above_len_padded hmemSize hsource96 (by omega) (by omega)
    · exact hsourceBefore
    · omega
    · omega
    · rwa [hsetSize]
  have hsourceValue :
      Model.bytesToNatPadded (allocatedMemory mem fp modulusSize)
          (dataPtr + 32) modulusSize =
        Model.bytesToNatPadded mem (dataPtr + 32) modulusSize := by
    exact model_bytesToNatPadded_eq_of_readWithPadding (by omega) (by omega) (by omega)
      hsourceRead
  rw [← hsourceValue]
  unfold convertedMemory
  apply MultiLimbOddConversionSemantic.bytesToLimbsMemory_value_eq_model_contiguous
  · exact hmodulusBound
  · exact hsourceBefore
  · exact hallocatedSize
  · exact hactive
  · exact hrange.2
  · exact hconvertedFit
  · exact hallocated64

/-- The exact guarded word sequence consumed by schoolbook reduction denotes the source modulus. -/
theorem convertedArray_value_eq_model
    (mem : ByteArray) (aw : UInt256) (fp dataPtr modulusSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hsource96 : 96 ≤ dataPtr + 32)
    (hsourceBefore : dataPtr + 32 + modulusSize ≤ fp)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64) :
    wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (convertedMemory mem aw fp dataPtr modulusSize)
        (convertedWords mem aw fp dataPtr modulusSize)
        (UInt256.ofNat fp) 0 (words modulusSize)) =
      Model.bytesToNatPadded mem (dataPtr + 32) modulusSize := by
  have hgeometry := convertedGeometry mem aw fp dataPtr modulusSize
    hmodulusLarge hmodulusBound hmemSize hmemLe hgap hsourceBefore hawFit hbound
  have hfit : fp + 32 * (words modulusSize + 1) < UInt256.size := by
    have hcoveredEnd : fp + 32 + 32 * words modulusSize ≤
        32 * (convertedWords mem aw fp dataPtr modulusSize).toNat := by
      unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hgeometry
      omega
    nlinarith [hgeometry.2.2.2]
  rw [MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryLimbs
    (convertedMemory mem aw fp dataPtr modulusSize)
    (convertedWords mem aw fp dataPtr modulusSize) fp (words modulusSize)
    hfit hgeometry.2.2.1 hgeometry.2.2.2]
  exact convertedMemory_value_eq_model mem aw fp dataPtr modulusSize
    hmodulusLarge hmodulusBound hmemSize hmemLe hgap hsource96 hsourceBefore
    hawFit hbound

/-- Execute the first, modulus-side conversion of the direct multi-limb Barrett backend. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p modulusSize fp : Nat} {tail : List UInt256}
    {retBar result exp base ret : UInt256}
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (haccess : (UInt256.ofNat p).toNat + 32 ≤
      32 * (allocatedWords aw fp modulusSize).toNat)
    (hload : wideLoadWord (allocatedMemory mem fp modulusSize)
      (allocatedWords aw fp modulusSize) (UInt256.ofNat p) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 998)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1675⟩
      (UInt256.ofNat p :: exp :: UInt256.ofNat (words modulusSize) ::
        UInt256.ofNat modulusSize :: retBar :: result :: base :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
      (UInt256.ofNat fp :: continuation exp base retBar result ret modulusSize tail)
      (convertedMemory mem aw fp p modulusSize)
      (convertedWords mem aw fp p modulusSize)
      rdata acc (steps + conversionSteps modulusSize)
      (gasUsed + conversionGas mem aw fp p modulusSize) := by
  have hwords : words modulusSize ≤ 32 := by
    unfold words MultiLimbBarrettDispatch.limbCount
    omega
  have rd2836 := MultiLimbBarrettDispatch.bodyToFirstConversionCall
    (p := UInt256.ofNat p) (m := UInt256.ofNat modulusSize)
    (words := UInt256.ofNat (words modulusSize))
    (by omega) h
  have rd1487 := MultiLimbBarrettDispatch.conversionToAllocator
    (tail := continuation exp base retBar result ret modulusSize tail)
    (by simp [continuation]; omega) rd2836
  have rd2847 := newWordArrayExact
    (n := words modulusSize) (fp := fp) (ret := 2847)
    (tail := ⟨1700⟩ :: UInt256.ofNat p ::
      continuation exp base retBar result ret modulusSize tail)
    hwords hfp hbound hmemSize hmemLe hgap haw3 haw64 hfree hcalldata
    (by simp [continuation]; omega) (by native_decide) rd1487
  have rd1700 := MultiLimbBytesToLimbsCall.postAllocatorComplete
    (dataLen := modulusSize) (limbsPtr := UInt256.ofNat fp)
    (innerRet := ⟨1700⟩) (dataPtr := UInt256.ofNat p)
    (tail := continuation exp base retBar result ret modulusSize tail)
    (by simp [continuation]; omega) hmodulusBound haccess hload
    (by native_decide) (by
      simpa [allocatedMemory, allocatedWords] using rd2847)
  have normalized := rd1700.withIndices
    (k' := steps + conversionSteps modulusSize) (by
      unfold conversionSteps
      omega)
    (C' := gasUsed + conversionGas mem aw fp p modulusSize) (by
      unfold conversionGas
      omega)
  simpa [convertedMemory, convertedWords, continuation] using normalized

/-- Compose the significant-first-byte scan selector with modulus allocation and conversion. -/
theorem scanDirectExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p modulusSize fp retBar result exp base ret : Nat}
    {tail : List UInt256}
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hp32 : p + 32 < UInt256.size) (hpend : p + modulusSize + 31 < UInt256.size)
    (hactive : p + 64 ≤ 32 * aw.toNat)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (p + 32))) ≠ ⟨0⟩)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (words modulusSize) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (haccess : (UInt256.ofNat p).toNat + 32 ≤
      32 * (allocatedWords aw fp modulusSize).toNat)
    (hload : wideLoadWord (allocatedMemory mem fp modulusSize)
      (allocatedWords aw fp modulusSize) (UInt256.ofNat p) =
        UInt256.ofNat modulusSize)
    (htail : tail.length ≤ 998)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1592⟩
      (UInt256.ofNat p :: UInt256.ofNat modulusSize :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exp :: UInt256.ofNat base ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    ∃ finalSteps, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1700⟩
      (UInt256.ofNat fp :: continuation (UInt256.ofNat exp) (UInt256.ofNat base)
        (UInt256.ofNat retBar) (UInt256.ofNat result) (UInt256.ofNat ret)
        modulusSize tail)
      (convertedMemory mem aw fp p modulusSize)
      (convertedWords mem aw fp p modulusSize)
      rdata acc finalSteps (gasUsed + scanConversionGas mem aw fp p modulusSize) := by
  obtain ⟨bodySteps, rd1675⟩ := MultiLimbBarrettDispatch.scanDirectToBody
    hmodulusLarge hmodulusBound hp32 hpend hactive hfirst (by omega) h
  have rd1700 := exact hmodulusLarge hmodulusBound hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hfree hcalldata haccess hload htail rd1675
  refine ⟨bodySteps + conversionSteps modulusSize, ?_⟩
  simpa [scanConversionGas, Nat.add_assoc] using rd1700

end Modexp.MultiLimbBarrettConversion
