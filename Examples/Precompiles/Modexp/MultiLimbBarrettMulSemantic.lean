import Examples.Precompiles.Modexp.MultiLimbBarrettMulContract
import Examples.Precompiles.Modexp.MultiLimbBarrettSliceSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulFunctionSemantic
import Examples.Precompiles.Modexp.MultiLimbBarrettModel

/-! # Barrett full-product semantics -/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbBarrettMulSemantic

open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbSchoolbookMulTrace

/-! ## q1 allocation and copy geometry -/

/-- The q1 allocator materializes its header, including zero-filling any skipped high product
limbs before the header. -/
theorem q1AllocatedMemory_size
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (q1AllocatedMemory mem fp kWords).size = fp + 32 := by
  unfold q1AllocatedMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

theorem q1AllocatedPtr_toNat
    (fp kWords : Nat)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64) :
    (UInt256.ofNat fp).toNat = fp := by
  apply UInt256.toNat_ofNat_of_lt
  exact (show fp < 2 ^ 64 by omega).trans (by decide)

theorem q1AllocatedMemory_read64
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (q1AllocatedMemory mem fp kWords).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (fp + wordArrayAllocationSize (kWords + 2))) := by
  unfold q1AllocatedMemory
  rw [storeBytesLength_read64]
  · exact setFreePtr_read64 hmemSize
  · rw [setFreePtr_size hmemSize]
    omega
  · exact hmemSize.trans hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

theorem q1AllocatedMemory_words_below
    (mem : ByteArray) (fp kWords ptr words : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom (q1AllocatedMemory mem fp kWords) ptr words =
      memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hread : (q1AllocatedMemory mem fp kWords).readWithPadding ptr 32 =
          mem.readWithPadding ptr 32 := by
        unfold q1AllocatedMemory
        rw [storeBytesLength_read_below_padded]
        · exact setFreePtr_read_above_padded hmemSize hptrBase
        · rw [setFreePtr_size hmemSize]
          omega
        · omega
        · rw [setFreePtr_size hmemSize]
          exact hgap
      have htail := ih (ptr + 32) (by omega) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [hread, htail]

/-- q1 copies `k+1` limbs into a `k+2`-limb allocation, leaving one logical high zero limb. -/
theorem q1CopiedMemory_size
    (mem : ByteArray) (product : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32) :
    (q1CopiedMemory (q1AllocatedMemory mem fp kWords) (UInt256.ofNat fp)
      product kWords).size = fp + 32 + 32 * (kWords + 1) := by
  have hallocated := q1AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq1Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [q1AllocatedPtr_toNat fp kWords hbound]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  unfold q1CopiedMemory
  rw [hsrc, hdst, hlen, q1AllocatedPtr_toNat fp kWords hbound]
  have hwrite := write_end_size_from (q1AllocatedMemory mem fp kWords)
    (q1AllocatedMemory mem fp kWords) (product.toNat + 32 * kWords)
    (32 * (kWords + 1)) (by omega) (by rw [hallocated]; omega)
  rw [← hallocated, hwrite, hallocated]

/-- q1's payload copy leaves Solidity's free-pointer word unchanged. -/
theorem q1CopiedMemory_read64
    (mem : ByteArray) (product : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32) :
    (q1CopiedMemory (q1AllocatedMemory mem fp kWords) (UInt256.ofNat fp)
      product kWords).readWithPadding 64 32 =
      (q1AllocatedMemory mem fp kWords).readWithPadding 64 32 := by
  have hallocated := q1AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq1Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [q1AllocatedPtr_toNat fp kWords hbound]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  unfold q1CopiedMemory
  rw [hsrc, hdst, hlen, q1AllocatedPtr_toNat fp kWords hbound, ← hallocated]
  exact write_read_below_end_from (q1AllocatedMemory mem fp kWords)
    (q1AllocatedMemory mem fp kWords) (product.toNat + 32 * kWords)
    (32 * (kWords + 1)) 64 (by omega) (by rw [hallocated]; omega)
    (by rw [hallocated]; omega)

/-- q1 allocation and copy preserve every padded word at `0x60` or above whose end precedes the
new q1 header. -/
theorem q1CopiedMemory_read_below
    (mem : ByteArray) (product : UInt256) (fp kWords read : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32)
    (hreadBase : 96 ≤ read) (hbelow : read + 32 ≤ fp) :
    (q1CopiedMemory (q1AllocatedMemory mem fp kWords) (UInt256.ofNat fp)
      product kWords).readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hallocated := q1AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq1Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [q1AllocatedPtr_toNat fp kWords hbound]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  have hcopyFrame :
      (q1CopiedMemory (q1AllocatedMemory mem fp kWords) (UInt256.ofNat fp)
        product kWords).readWithPadding read 32 =
        (q1AllocatedMemory mem fp kWords).readWithPadding read 32 := by
    unfold q1CopiedMemory
    rw [hsrc, hdst, hlen, q1AllocatedPtr_toNat fp kWords hbound, ← hallocated]
    exact write_read_below_end_from (q1AllocatedMemory mem fp kWords)
      (q1AllocatedMemory mem fp kWords) (product.toNat + 32 * kWords)
      (32 * (kWords + 1)) read (by omega) (by rw [hallocated]; omega)
      (by rw [hallocated]; omega)
  rw [hcopyFrame]
  unfold q1AllocatedMemory
  rw [storeBytesLength_read_below_padded]
  · exact setFreePtr_read_above_padded hmemSize hreadBase
  · rw [setFreePtr_size hmemSize]
    omega
  · exact hbelow
  · rw [setFreePtr_size hmemSize]
    exact hgap

theorem q1CopiedMemory_words_below
    (mem : ByteArray) (product : UInt256) (fp kWords ptr words : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (q1CopiedMemory (q1AllocatedMemory mem fp kWords) (UInt256.ofNat fp)
          product kWords) ptr words =
      memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hread := q1CopiedMemory_read_below mem product fp kWords ptr hkPos hkWord
        hmemSize hmemLe hgap hbound hproductFit hsource hptrBase (by omega)
      have htail := ih (ptr + 32) (by omega) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [hread, htail]

theorem q1CopiedWords_range
    (aw product : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32) :
    fp + 32 + 32 * (kWords + 1) ≤
        32 * (q1CopiedWords (q1AllocatedWords aw fp kWords)
          (UInt256.ofNat fp) product kWords).toNat ∧
      (q1CopiedWords (q1AllocatedWords aw fp kWords)
        (UInt256.ofNat fp) product kWords).toNat * 32 < UInt256.size := by
  have harrayFit : fp + wordArrayAllocationSize (kWords + 2) + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize (kWords + 2) + 31 < 2 ^ 64 + 31)
      (by decide)
  have hallocatedRange := Modexp.MultiLimbOddConversionSemantic.newWordArrayWords_range
    aw fp (kWords + 2) (by omega) hawFit harrayFit
  have hfpNat := q1AllocatedPtr_toNat fp kWords hbound
  have hq1Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [hfpNat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q1CopySourceWord_toNat product kWords
    hkPos hkWord (by omega) hproductFit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q1CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq1Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q1CopyLengthWord_toNat kWords (by omega)
  let access := max (fp + 32) (product.toNat + 32 * kWords)
  have hsrcLe : product.toNat + 32 * kWords ≤ fp + 32 := by omega
  have haccessFit : access + 32 * (kWords + 1) + 31 < UInt256.size := by
    dsimp only [access]
    rw [max_eq_left hsrcLe]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega : fp + 32 + 32 * (kWords + 1) + 31 < 2 ^ 64) (by decide)
  have hmFit := Modexp.MultiLimbMontgomeryCIOSSemantic.machineM_mul32_lt_size
    hallocatedRange.2 haccessFit
  have hmLt : MachineState.M (q1AllocatedWords aw fp kWords).toNat access
      (32 * (kWords + 1)) < UInt256.size := by
    have hle := Nat.mul_le_mul_left
      (MachineState.M (q1AllocatedWords aw fp kWords).toNat access
        (32 * (kWords + 1))) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hmFit
  have hcopiedNat :
      (q1CopiedWords (q1AllocatedWords aw fp kWords)
        (UInt256.ofNat fp) product kWords).toNat =
        MachineState.M (q1AllocatedWords aw fp kWords).toNat access
          (32 * (kWords + 1)) := by
    unfold q1CopiedWords
    rw [hsrc, hdst, hlen, hfpNat]
    change (UInt256.ofNat
      (MachineState.M (q1AllocatedWords aw fp kWords).toNat access
        (32 * (kWords + 1)))).toNat = _
    rw [UInt256.toNat_ofNat_of_lt hmLt]
  constructor
  · rw [hcopiedNat]
    calc
      fp + 32 + 32 * (kWords + 1) ≤ access + 32 * (kWords + 1) :=
        Nat.add_le_add_right (by dsimp only [access]; exact le_max_left _ _) _
      _ ≤ 32 * MachineState.M (q1AllocatedWords aw fp kWords).toNat access
          (32 * (kWords + 1)) :=
        Modexp.MultiLimbMontgomeryCIOSSemantic.machineM_access_le (by omega)
  · rwa [hcopiedNat]

structure Q1SliceGeometry
    (copiedMem : ByteArray) (copiedAw loadedAw mu : UInt256) (nextFp : Nat) : Prop where
  muInMemory : mu.toNat < copiedMem.size
  muActive : ¬ mu ≥ copiedAw * ⟨32⟩
  covered : MemoryCovered copiedMem loadedAw
  activeWordsFit : loadedAw.toNat * 32 < UInt256.size
  memorySize96 : 96 ≤ copiedMem.size
  memoryLeNext : copiedMem.size ≤ nextFp
  nextGap : nextFp - copiedMem.size < USize.size
  activeWords3 : 3 ≤ loadedAw.toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ loadedAw * ⟨32⟩
  freePointerRead : copiedMem.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat nextFp)

/-- The q1 allocation, copy, and following `mu.length` load establish every geometry premise of
the second standalone multiplication. -/
theorem q1Slice_geometry
    (mem : ByteArray) (aw product mu : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32)
    (hmuEnd : mu.toNat + 32 ≤ fp) :
    let allocatedMem := q1AllocatedMemory mem fp kWords
    let allocatedAw := q1AllocatedWords aw fp kWords
    let q1 := UInt256.ofNat fp
    let copiedMem := q1CopiedMemory allocatedMem q1 product kWords
    let copiedAw := q1CopiedWords allocatedAw q1 product kWords
    let loadedAw := q1LoadedWords allocatedAw q1 product mu kWords
    Q1SliceGeometry copiedMem copiedAw loadedAw mu
      (fp + wordArrayAllocationSize (kWords + 2)) := by
  let allocatedMem := q1AllocatedMemory mem fp kWords
  let allocatedAw := q1AllocatedWords aw fp kWords
  let q1 := UInt256.ofNat fp
  let copiedMem := q1CopiedMemory allocatedMem q1 product kWords
  let copiedAw := q1CopiedWords allocatedAw q1 product kWords
  let loadedAw := q1LoadedWords allocatedAw q1 product mu kWords
  let nextFp := fp + wordArrayAllocationSize (kWords + 2)
  have hsize := q1CopiedMemory_size mem product fp kWords hkPos hkWord hmemSize hmemLe
    hgap hbound hproductFit hsource
  have hrange := q1CopiedWords_range aw product fp kWords hkPos hkWord hawFit hbound
    hproductFit hsource
  have hcopiedCovered : MemoryCovered copiedMem copiedAw := by
    unfold MemoryCovered
    simpa only [copiedMem, copiedAw, allocatedMem, allocatedAw, q1, hsize] using hrange.1
  have hfp64 : fp < 2 ^ 64 := lt_of_le_of_lt (Nat.le_add_right fp _) hbound
  have hmuFit64 : mu.toNat + 32 + 31 < 2 ^ 64 := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
    omega
  have hloaded := Modexp.MultiLimbMontgomeryCIOSSemantic.machineM_coverage
    copiedMem copiedAw mu.toNat 32 hcopiedCovered (by simpa only [copiedAw] using hrange.2)
    (lt_trans hmuFit64 (by decide))
  have hloadedDef : UInt256.ofNat (MachineState.M copiedAw.toNat mu.toNat 32) = loadedAw := by
    rfl
  have hloadedCovered : MemoryCovered copiedMem loadedAw := by
    simpa only [loadedAw, q1LoadedWords, copiedAw, allocatedAw, q1] using hloaded.1
  have hloadedFit : loadedAw.toNat * 32 < UInt256.size := by
    simpa only [loadedAw, q1LoadedWords, copiedAw, allocatedAw, q1] using hloaded.2
  have hcopiedMul : (copiedAw * (⟨32⟩ : UInt256)).toNat = copiedAw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := copiedAw) (b := (⟨32⟩ : UInt256))
        (by simpa only [copiedAw] using hrange.2)
  have hmuActive : ¬ mu ≥ copiedAw * ⟨32⟩ := by
    intro hge
    have hgeNat : (copiedAw * (⟨32⟩ : UInt256)).toNat ≤ mu.toNat := by simpa using hge
    rw [hcopiedMul] at hgeNat
    have hcover : fp + 32 + 32 * (kWords + 1) ≤ 32 * copiedAw.toNat := by
      simpa only [copiedAw] using hrange.1
    omega
  have hloaded3 : 3 ≤ loadedAw.toNat := by
    unfold MemoryCovered at hloadedCovered
    rw [show copiedMem.size = fp + 32 + 32 * (kWords + 1) by
      simpa only [copiedMem, allocatedMem, q1] using hsize] at hloadedCovered
    omega
  have hloaded64 : ¬ (⟨64⟩ : UInt256) ≥ loadedAw * ⟨32⟩ := by
    have hmul : (loadedAw * (⟨32⟩ : UInt256)).toNat = loadedAw.toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := loadedAw) (b := (⟨32⟩ : UInt256)) hloadedFit
    intro hge
    have hgeNat : (loadedAw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by simpa using hge
    rw [hmul] at hgeNat
    omega
  have hread := q1CopiedMemory_read64 mem product fp kWords hkPos hkWord hmemSize hmemLe
    hgap hbound hproductFit hsource
  exact {
    muInMemory := by
      rw [show copiedMem.size = fp + 32 + 32 * (kWords + 1) by
        simpa only [copiedMem, allocatedMem, q1] using hsize]
      omega
    muActive := hmuActive
    covered := hloadedCovered
    activeWordsFit := hloadedFit
    memorySize96 := by
      rw [show copiedMem.size = fp + 32 + 32 * (kWords + 1) by
        simpa only [copiedMem, allocatedMem, q1] using hsize]
      omega
    memoryLeNext := by
      rw [show copiedMem.size = fp + 32 + 32 * (kWords + 1) by
        simpa only [copiedMem, allocatedMem, q1] using hsize]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    nextGap := by
      rw [show copiedMem.size = fp + 32 + 32 * (kWords + 1) by
        simpa only [copiedMem, allocatedMem, q1] using hsize]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      have : 32 < USize.size := by native_decide
      omega
    activeWords3 := hloaded3
    activeWords64 := hloaded64
    freePointerRead := by
      rw [show copiedMem.readWithPadding 64 32 = allocatedMem.readWithPadding 64 32 by
        simpa only [copiedMem, allocatedMem, q1] using hread]
      simpa only [allocatedMem, nextFp] using
        q1AllocatedMemory_read64 mem fp kWords hmemSize hmemLe hgap
  }

/-! ## q3 allocation and copy geometry -/

/-- The q3 allocator initially materializes only the array header. -/
theorem q3AllocatedMemory_size
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (q3AllocatedMemory mem fp kWords).size = fp + 32 := by
  unfold q3AllocatedMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- The q3 pointer returned by the allocator has its ordinary natural value. -/
theorem q3AllocatedPtr_toNat
    (fp kWords : Nat)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64) :
    (UInt256.ofNat fp).toNat = fp := by
  apply UInt256.toNat_ofNat_of_lt
  exact (show fp < 2 ^ 64 by omega).trans (by decide)

/-- The q3 allocator stores its successor pointer in Solidity's free-pointer slot. -/
theorem q3AllocatedMemory_read64
    (mem : ByteArray) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (q3AllocatedMemory mem fp kWords).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (fp + wordArrayAllocationSize (kWords + 3))) := by
  unfold q3AllocatedMemory
  rw [storeBytesLength_read64]
  · exact setFreePtr_read64 hmemSize
  · rw [setFreePtr_size hmemSize]
    omega
  · exact hmemSize.trans hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

theorem q3AllocatedMemory_words_below
    (mem : ByteArray) (fp kWords ptr words : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom (q3AllocatedMemory mem fp kWords) ptr words =
      memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hread : (q3AllocatedMemory mem fp kWords).readWithPadding ptr 32 =
          mem.readWithPadding ptr 32 := by
        unfold q3AllocatedMemory
        rw [storeBytesLength_read_below_padded]
        · exact setFreePtr_read_above_padded hmemSize hptrBase
        · rw [setFreePtr_size hmemSize]
          omega
        · omega
        · rw [setFreePtr_size hmemSize]
          exact hgap
      have htail := ih (ptr + 32) (by omega) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [hread, htail]

/-- q3's `MCOPY` starts immediately after its header and materializes exactly its full payload. -/
theorem q3CopiedMemory_size
    (mem : ByteArray) (q2 : UInt256) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp + 32) :
    (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords).size =
      fp + wordArrayAllocationSize (kWords + 3) := by
  have hallocated := q3AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq3Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [q3AllocatedPtr_toNat fp kWords hbound]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q3CopySourceWord_toNat q2 kWords
    (by omega) hq2Fit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q3CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq3Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q3CopyLengthWord_toNat kWords (by omega)
  unfold q3CopiedMemory
  rw [hsrc, hdst, hlen, q3AllocatedPtr_toNat fp kWords hbound]
  have hwrite := write_end_size_from (q3AllocatedMemory mem fp kWords)
    (q3AllocatedMemory mem fp kWords) (q2.toNat + 32 * (kWords + 2))
    (32 * (kWords + 3)) (by omega) (by rw [hallocated]; omega)
  rw [← hallocated]
  rw [hwrite, hallocated]
  unfold wordArrayAllocationSize wordArrayPayloadSize
  omega

/-- q3's payload copy leaves Solidity's free-pointer word unchanged. -/
theorem q3CopiedMemory_read64
    (mem : ByteArray) (q2 : UInt256) (fp kWords : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp + 32) :
    (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords).readWithPadding
        64 32 =
      (q3AllocatedMemory mem fp kWords).readWithPadding 64 32 := by
  have hallocated := q3AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq3Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [q3AllocatedPtr_toNat fp kWords hbound]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q3CopySourceWord_toNat q2 kWords
    (by omega) hq2Fit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q3CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq3Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q3CopyLengthWord_toNat kWords (by omega)
  unfold q3CopiedMemory
  rw [hsrc, hdst, hlen, q3AllocatedPtr_toNat fp kWords hbound, ← hallocated]
  exact write_read_below_end_from (q3AllocatedMemory mem fp kWords)
    (q3AllocatedMemory mem fp kWords) (q2.toNat + 32 * (kWords + 2))
    (32 * (kWords + 3)) 64 (by omega) (by rw [hallocated]; omega)
    (by rw [hallocated]; omega)

/-- q3 allocation and copy preserve every earlier padded limb range below the q3 header. -/
theorem q3CopiedMemory_words_below
    (mem : ByteArray) (q2 : UInt256) (fp kWords ptr words : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp + 32)
    (hptrBase : 96 ≤ ptr) (hbelow : ptr + 32 * words ≤ fp) :
    memoryWordsFrom
        (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords)
        ptr words = memoryWordsFrom mem ptr words := by
  have hallocated := q3AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hq3Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [q3AllocatedPtr_toNat fp kWords hbound]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q3CopySourceWord_toNat q2 kWords
    (by omega) hq2Fit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q3CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq3Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q3CopyLengthWord_toNat kWords (by omega)
  have hread (read : Nat) (hreadBase : 96 ≤ read) (hreadBelow : read + 32 ≤ fp) :
      (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords
        ).readWithPadding read 32 = mem.readWithPadding read 32 := by
    have hcopyFrame :
        (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords
          ).readWithPadding read 32 =
          (q3AllocatedMemory mem fp kWords).readWithPadding read 32 := by
      unfold q3CopiedMemory
      rw [hsrc, hdst, hlen, q3AllocatedPtr_toNat fp kWords hbound, ← hallocated]
      exact write_read_below_end_from (q3AllocatedMemory mem fp kWords)
        (q3AllocatedMemory mem fp kWords) (q2.toNat + 32 * (kWords + 2))
        (32 * (kWords + 3)) read (by omega) (by rw [hallocated]; omega)
        (by rw [hallocated]; omega)
    rw [hcopyFrame]
    unfold q3AllocatedMemory
    rw [storeBytesLength_read_below_padded]
    · exact setFreePtr_read_above_padded hmemSize hreadBase
    · rw [setFreePtr_size hmemSize]
      omega
    · exact hreadBelow
    · rw [setFreePtr_size hmemSize]
      exact hgap
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      have hhead := hread ptr hptrBase (by omega)
      have htail := ih (ptr + 32) (by omega) (by omega)
      simp only [memoryWordsFrom, Modexp.MultiLimbMemoryModel.memoryWordNat]
      rw [hhead, htail]

/-- The active-word counter after q3's copy covers the fully materialized q3 payload and remains
representable as an EVM byte extent. -/
theorem q3CopiedWords_range
    (aw q2 : UInt256) (fp kWords : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp + 32) :
    fp + wordArrayAllocationSize (kWords + 3) ≤
        32 * (q3CopiedWords (q3AllocatedWords aw fp kWords)
          (UInt256.ofNat fp) q2 kWords).toNat ∧
      (q3CopiedWords (q3AllocatedWords aw fp kWords)
          (UInt256.ofNat fp) q2 kWords).toNat * 32 < UInt256.size := by
  have harrayFit : fp + wordArrayAllocationSize (kWords + 3) + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize (kWords + 3) + 31 < 2 ^ 64 + 31)
      (by decide)
  have hallocatedRange := Modexp.MultiLimbOddConversionSemantic.newWordArrayWords_range
    aw fp (kWords + 3) (by omega) hawFit harrayFit
  have hfpNat := q3AllocatedPtr_toNat fp kWords hbound
  have hq3Fit : (UInt256.ofNat fp).toNat + 32 < UInt256.size := by
    rw [hfpNat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hsrc := Modexp.MultiLimbBarrettSliceSemantic.q3CopySourceWord_toNat q2 kWords
    (by omega) hq2Fit
  have hdst := Modexp.MultiLimbBarrettSliceSemantic.q3CopyDestinationWord_toNat
    (UInt256.ofNat fp) hq3Fit
  have hlen := Modexp.MultiLimbBarrettSliceSemantic.q3CopyLengthWord_toNat kWords (by omega)
  let access := max (fp + 32) (q2.toNat + 32 * (kWords + 2))
  have haccessFit : access + 32 * (kWords + 3) + 31 < UInt256.size := by
    dsimp only [access]
    have hdestEnd : fp + 32 + 32 * (kWords + 3) < 2 ^ 64 := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hbound
      omega
    have hsrcEnd : q2.toNat + 32 * (kWords + 2) + 32 * (kWords + 3) ≤ fp + 32 := by
      omega
    have hsrcLe : q2.toNat + 32 * (kWords + 2) ≤ fp + 32 := by omega
    rw [max_eq_left hsrcLe]
    exact lt_trans (by omega : fp + 32 + 32 * (kWords + 3) + 31 < 2 ^ 64 + 31)
      (by decide)
  have hmFit := Modexp.MultiLimbMontgomeryCIOSSemantic.machineM_mul32_lt_size
    hallocatedRange.2 haccessFit
  have hmLt : MachineState.M (q3AllocatedWords aw fp kWords).toNat access
      (32 * (kWords + 3)) < UInt256.size := by
    have hle := Nat.mul_le_mul_left
      (MachineState.M (q3AllocatedWords aw fp kWords).toNat access
        (32 * (kWords + 3))) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hmFit
  have hcopiedNat :
      (q3CopiedWords (q3AllocatedWords aw fp kWords)
        (UInt256.ofNat fp) q2 kWords).toNat =
        MachineState.M (q3AllocatedWords aw fp kWords).toNat access
          (32 * (kWords + 3)) := by
    unfold q3CopiedWords
    rw [hsrc, hdst, hlen, hfpNat]
    change (UInt256.ofNat
      (MachineState.M (q3AllocatedWords aw fp kWords).toNat access
        (32 * (kWords + 3)))).toNat = _
    rw [UInt256.toNat_ofNat_of_lt hmLt]
  constructor
  · rw [hcopiedNat]
    have hmAccess := Modexp.MultiLimbMontgomeryCIOSSemantic.machineM_access_le
      (s := (q3AllocatedWords aw fp kWords).toNat) (off := access)
      (len := 32 * (kWords + 3)) (by omega)
    calc
      fp + wordArrayAllocationSize (kWords + 3) =
          fp + 32 + 32 * (kWords + 3) := by
            unfold wordArrayAllocationSize wordArrayPayloadSize
            omega
      _ ≤ access + 32 * (kWords + 3) :=
        Nat.add_le_add_right (by dsimp only [access]; exact le_max_left _ _) _
      _ ≤ 32 * MachineState.M (q3AllocatedWords aw fp kWords).toNat access
          (32 * (kWords + 3)) := hmAccess
  · rwa [hcopiedNat]

/-- The concrete q3 copy is covered by its exact post-`MCOPY` active-word counter. -/
theorem q3CopiedMemory_coverage
    (mem : ByteArray) (aw q2 : UInt256) (fp kWords : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ fp + 32) :
    MemoryCovered
        (q3CopiedMemory (q3AllocatedMemory mem fp kWords) (UInt256.ofNat fp) q2 kWords)
        (q3CopiedWords (q3AllocatedWords aw fp kWords) (UInt256.ofNat fp) q2 kWords) ∧
      (q3CopiedWords (q3AllocatedWords aw fp kWords)
        (UInt256.ofNat fp) q2 kWords).toNat * 32 < UInt256.size := by
  have hrange := q3CopiedWords_range aw q2 fp kWords hawFit hbound hq2Fit hsource
  constructor
  · unfold MemoryCovered
    rw [q3CopiedMemory_size mem q2 fp kWords hmemSize hmemLe hgap hbound hq2Fit hsource]
    exact hrange.1
  · exact hrange.2

/-- The first concrete Barrett product is exactly the full `k`-limb product `a*b`. -/
theorem firstProduct_value
    (mem : ByteArray) (aw a b : UInt256) (fp kWords : Nat)
    (hkPos : 0 < kWords) (hkBound : 2 * kWords ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp) :
    let initial := firstProductInitial mem aw fp kWords
    let final := firstProductFinal mem aw a b fp kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (2 * kWords)) =
      Modexp.wordLimbsToNat (memoryWordsFrom initial.memory (a.toNat + 32) kWords) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (b.toNat + 32) kWords) := by
  have hvalue := functionSchoolbookMul_value mem aw a b fp kWords kWords (by omega) hkPos
    hcovered hawFit hmemSize hmemLe hgap (by
      rw [show kWords + kWords = 2 * kWords by omega]
      exact hbound) haEnd hbEnd
  simpa only [firstProductInitial, firstProductFinal,
    show kWords + kWords = 2 * kWords by omega] using hvalue

/-- The first product establishes the complete allocator geometry needed by q1. -/
theorem firstProductFinal_geometry
    (mem : ByteArray) (aw a b : UInt256) (fp kWords : Nat)
    (hkBound : 2 * kWords ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp) :
    FunctionFinalGeometry (firstProductFinal mem aw a b fp kWords)
      (fp + wordArrayAllocationSize (2 * kWords)) := by
  have hgeometry := functionFinal_geometry mem aw a b fp kWords kWords
    (by omega) hcovered hawFit hmemSize hmemLe hgap (by
      rw [show kWords + kWords = 2 * kWords by omega]
      exact hbound) haEnd hbEnd
  simpa only [firstProductFinal, functionFinalState,
    show kWords + kWords = 2 * kWords by omega] using hgeometry

/-- A complete first product preserves an earlier padded header word. -/
theorem firstProductFinal_read32_below
    (mem : ByteArray) (aw a b : UInt256) (fp kWords read : Nat)
    (hkBound : 2 * kWords ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp)
    (hreadBase : 96 ≤ read) (hbelow : read + 32 ≤ fp) :
    (firstProductFinal mem aw a b fp kWords).memory.readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hrows := functionRows_read32_below_result mem aw a b fp kWords kWords kWords read
    (by omega) (by omega) hcovered hawFit hmemSize hmemLe hgap (by
      simpa only [show kWords + kWords = 2 * kWords by omega] using hbound)
    haEnd hbEnd (by
      have hinitialSize := functionAllocatedMemory_size mem fp kWords kWords
        hmemSize hmemLe hgap
      simpa only [functionInitialState, hinitialSize] using (by omega : read + 32 ≤ fp + 32))
    hbelow
  rw [show (firstProductFinal mem aw a b fp kWords).memory.readWithPadding read 32 =
      (functionInitialState mem aw fp kWords kWords).memory.readWithPadding read 32 by
    simpa only [firstProductFinal, functionFinalState] using hrows]
  dsimp only [functionInitialState, functionAllocatedMemory]
  rw [storeBytesLength_read_below_padded]
  · exact setFreePtr_read_above_padded hmemSize hreadBase
  · rw [setFreePtr_size hmemSize]
    omega
  · exact hbelow
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- The low `k+1` limbs retained for the later Barrett subtraction are the first full product
reduced modulo `B^(k+1)`. -/
theorem firstProduct_low_value
    (mem : ByteArray) (product : UInt256) (kWords productValue : Nat)
    (hkPos : 0 < kWords)
    (hfull : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (product.toNat + 32) (2 * kWords)) = productValue) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom mem (product.toNat + 32) (kWords + 1)) =
      productValue % UInt256.size ^ (kWords + 1) := by
  apply Modexp.MultiLimbBarrettSliceSemantic.memoryWordsFrom_low_value
    mem (product.toNat + 32) (kWords + 1) (kWords - 1) productValue
  simpa only [show kWords + 1 + (kWords - 1) = 2 * kWords by omega] using hfull

/-- The second concrete Barrett product is exactly the full `(k+2)`-limb product `q1*mu`. -/
theorem secondProduct_value
    (mem : ByteArray) (aw q1 mu : UInt256) (fp kWords : Nat)
    (hkBound : 2 * kWords + 4 ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq1End : q1.toNat + 32 * (kWords + 3) ≤ fp)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp) :
    let initial := secondProductInitial mem aw fp kWords
    let final := secondProductFinal mem aw q1 mu fp kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom final.memory (fp + 32) (2 * kWords + 4)) =
      Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (q1.toNat + 32) (kWords + 2)) *
        Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory (mu.toNat + 32) (kWords + 2)) := by
  have hvalue := functionSchoolbookMul_value mem aw q1 mu fp (kWords + 2) (kWords + 2)
    (by omega) (by omega) hcovered hawFit hmemSize hmemLe hgap (by
      rw [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega]
      exact hbound) hq1End hmuEnd
  simpa only [secondProductInitial, secondProductFinal,
    show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega] using hvalue

/-- The completed `q1*mu` product establishes every geometry premise for q3's following
allocation, including the exact successor free pointer. -/
theorem secondProductFinal_geometry
    (mem : ByteArray) (aw q1 mu : UInt256) (fp kWords : Nat)
    (hkBound : 2 * kWords + 4 ≤ 68)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq1End : q1.toNat + 32 * (kWords + 3) ≤ fp)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp) :
    FunctionFinalGeometry (secondProductFinal mem aw q1 mu fp kWords)
      (fp + wordArrayAllocationSize (2 * kWords + 4)) := by
  have hgeometry := functionFinal_geometry mem aw q1 mu fp (kWords + 2) (kWords + 2)
    (by omega) hcovered hawFit hmemSize hmemLe hgap (by
      rw [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega]
      exact hbound) hq1End hmuEnd
  simpa only [secondProductFinal, functionFinalState,
    show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega] using hgeometry

/-- The concrete q1 copy divides a known first-product value by `B^(k-1)`. -/
theorem q1Copied_value_of_product_value
    (mem : ByteArray) (q1 product : UInt256) (kWords productValue : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hkShift : kWords + 1 < 2 ^ 251)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hq1Fit : q1.toNat + 32 < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ mem.size)
    (hdest : q1.toNat + 32 ≤ mem.size)
    (hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (product.toNat + 32) (2 * kWords)) = productValue) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (q1CopiedMemory mem q1 product kWords)
          (q1.toNat + 32) (kWords + 1)) =
      productValue / UInt256.size ^ (kWords - 1) := by
  rw [Modexp.MultiLimbBarrettSliceSemantic.q1CopiedMemory_value mem q1 product kWords
    hkPos hkWord hkShift hproductFit hq1Fit hsource hdest, hproduct]

/-- The extra high word read by the second multiplier is the q1 allocation's implicit zero, so
the full `k+2`-word operand has the same value as the copied `k+1`-word slice. -/
theorem q1Copied_full_value_of_product_value
    (mem : ByteArray) (product : UInt256) (fp kWords productValue : Nat)
    (hkPos : 0 < kWords) (hkWord : kWords < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hproductFit : product.toNat + 32 * kWords < UInt256.size)
    (hsource : product.toNat + 32 * (2 * kWords + 1) ≤ fp + 32)
    (hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom (q1AllocatedMemory mem fp kWords)
        (product.toNat + 32) (2 * kWords)) = productValue) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom
          (q1CopiedMemory (q1AllocatedMemory mem fp kWords) (UInt256.ofNat fp)
            product kWords)
          (fp + 32) (kWords + 2)) =
      productValue / UInt256.size ^ (kWords - 1) := by
  let allocated := q1AllocatedMemory mem fp kWords
  let q1 := UInt256.ofNat fp
  let copied := q1CopiedMemory allocated q1 product kWords
  have hallocatedSize := q1AllocatedMemory_size mem fp kWords hmemSize hmemLe hgap
  have hcopiedSize := q1CopiedMemory_size mem product fp kWords hkPos hkWord hmemSize hmemLe
    hgap hbound hproductFit hsource
  have hq1Nat : q1.toNat = fp := q1AllocatedPtr_toNat fp kWords hbound
  have hq1Fit : q1.toNat + 32 < UInt256.size := by
    rw [hq1Nat]
    exact lt_trans (by omega : fp + 32 < 2 ^ 64 + 32) (by decide)
  have hlow := q1Copied_value_of_product_value allocated q1 product kWords productValue
    hkPos hkWord (by omega) hproductFit hq1Fit (by rw [hallocatedSize]; exact hsource)
    (by rw [hallocatedSize, hq1Nat]) (by simpa only [allocated] using hproduct)
  have hlast : Modexp.MultiLimbMemoryModel.memoryWordNat copied
      (fp + 32 + 32 * (kWords + 1)) = 0 := by
    apply memoryWordNat_past_end_zero
    simpa only [copied] using hcopiedSize.le
  have hsnoc := Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append
    copied (fp + 32) (kWords + 1)
  rw [show kWords + 1 + 1 = kWords + 2 by omega] at hsnoc
  rw [hq1Nat] at hlow
  rw [hsnoc, Modexp.wordLimbsToNat_append, hlow, hlast]
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 :=
    UInt256.toNat_ofNat_of_lt (by decide)
  simp only [Modexp.wordLimbsToNat, hzeroNat, Nat.zero_add, Nat.mul_zero, Nat.add_zero]

/-- The concrete q3 copy divides a known q2 product value by `B^(k+1)`. -/
theorem q3Copied_value_of_product_value
    (mem : ByteArray) (q3 q2 : UInt256) (kWords productValue : Nat)
    (hkShift : kWords + 3 < 2 ^ 251)
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hq3Fit : q3.toNat + 32 < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ mem.size)
    (hdest : q3.toNat + 32 ≤ mem.size)
    (hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (q2.toNat + 32) (2 * kWords + 4)) = productValue) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (q3CopiedMemory mem q3 q2 kWords)
          (q3.toNat + 32) (kWords + 3)) =
      productValue / UInt256.size ^ (kWords + 1) := by
  rw [Modexp.MultiLimbBarrettSliceSemantic.q3CopiedMemory_value mem q3 q2 kWords
    hkShift hq2Fit hq3Fit hsource hdest, hproduct]

/-- Once the full copied q3 array is the pure Barrett estimate, the low `k+1` limbs consumed by
the deployed truncated multiplication are that same estimate, not merely a residue. -/
theorem q3Copied_low_value
    (mem : ByteArray) (q3 : UInt256) (kWords nValue x : Nat)
    (hkPos : 0 < kWords)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hfull : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (q3.toNat + 32) (kWords + 3)) =
        Modexp.barrettQ3 kWords nValue x) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom mem (q3.toNat + 32) (kWords + 1)) =
      Modexp.barrettQ3 kWords nValue x := by
  have hlow := Modexp.MultiLimbBarrettSliceSemantic.memoryWordsFrom_low_value
    mem (q3.toNat + 32) (kWords + 1) 2 (Modexp.barrettQ3 kWords nValue x) (by
      simpa only [show kWords + 1 + 2 = kWords + 3 by omega] using hfull)
  rw [Nat.mod_eq_of_lt (Modexp.barrettQ3_lt_radix kWords nValue x hkPos
    hnNormalized hx)] at hlow
  exact hlow

/-- The concrete q3 copy exposes the exact pure Barrett estimate in the low `k+1` limbs when the
preceding full q1-by-mu product has its proved value. -/
theorem q3Copied_low_value_of_product_value
    (mem : ByteArray) (q3 q2 : UInt256) (kWords nValue x : Nat)
    (hkPos : 0 < kWords) (hkShift : kWords + 3 < 2 ^ 251)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hq2Fit : q2.toNat + 32 * (kWords + 2) < UInt256.size)
    (hq3Fit : q3.toNat + 32 < UInt256.size)
    (hsource : q2.toNat + 32 * (2 * kWords + 5) ≤ mem.size)
    (hdest : q3.toNat + 32 ≤ mem.size)
    (hproduct : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (q2.toNat + 32) (2 * kWords + 4)) =
        (x / UInt256.size ^ (kWords - 1)) *
          (UInt256.size ^ (2 * kWords) / nValue)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (q3CopiedMemory mem q3 q2 kWords)
          (q3.toNat + 32) (kWords + 1)) =
      Modexp.barrettQ3 kWords nValue x := by
  have hfull := q3Copied_value_of_product_value mem q3 q2 kWords
    ((x / UInt256.size ^ (kWords - 1)) *
      (UInt256.size ^ (2 * kWords) / nValue)) hkShift hq2Fit hq3Fit hsource hdest hproduct
  have hfull' : Modexp.wordLimbsToNat
      (memoryWordsFrom (q3CopiedMemory mem q3 q2 kWords)
        (q3.toNat + 32) (kWords + 3)) = Modexp.barrettQ3 kWords nValue x := by
    simpa only [Modexp.barrettQ3] using hfull
  exact q3Copied_low_value (q3CopiedMemory mem q3 q2 kWords) q3 kWords nValue x
    hkPos hnNormalized hx hfull'

/-- Compose both full schoolbook products and both Barrett slices.  The resulting q3-copy state
contains the pure Barrett estimate, the unchanged modulus, and the low subtraction window of the
original product. -/
theorem firstThroughQ3_values
    (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords aValue bValue nValue x : Nat)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (haBase : 96 ≤ a.toNat + 32) (hbBase : 96 ≤ b.toNat + 32)
    (hnBase : 96 ≤ n.toNat + 32) (hmuBase : 96 ≤ mu.toNat + 32)
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp)
    (hnEnd : n.toNat + 32 * (kWords + 1) ≤ fp)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp)
    (haValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (a.toNat + 32) kWords) = aValue)
    (hbValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (b.toNat + 32) kWords) = bValue)
    (hnValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (n.toNat + 32) kWords) = nValue)
    (hmuValue : Modexp.wordLimbsToNat
      (memoryWordsFrom mem (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue)
    (hxValue : aValue * bValue = x)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hx : x < UInt256.size ^ (2 * kWords)) :
    let firstFinal := firstProductFinal mem aw a b fp kWords
    let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
    let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
    let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
    let q1 := UInt256.ofNat q1Fp
    let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
    let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
    let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
    let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
    let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
    let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
    let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
    let q3 := UInt256.ofNat q3Fp
    let finalMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
    Modexp.wordLimbsToNat
        (memoryWordsFrom finalMem (q3.toNat + 32) (kWords + 1)) =
        Modexp.barrettQ3 kWords nValue x ∧
      Modexp.wordLimbsToNat
        (memoryWordsFrom finalMem (n.toNat + 32) kWords) = nValue ∧
      Modexp.wordLimbsToNat
        (memoryWordsFrom finalMem ((UInt256.ofNat fp).toNat + 32) (kWords + 1)) =
          x % UInt256.size ^ (kWords + 1) := by
  let firstFinal := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let finalMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  have hfirstGeometry := firstProductFinal_geometry mem aw a b fp kWords (by omega)
    hcovered hawFit hmemSize hmemLe hgap hfirstBound haEnd hbEnd
  have hproductNat : (UInt256.ofNat fp).toNat = fp :=
    functionResultPtr_toNat fp (2 * kWords) hfirstBound
  have hq1Nat : q1.toNat = q1Fp := by
    exact q1AllocatedPtr_toNat q1Fp kWords
      (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
  have hsecondNat : (UInt256.ofNat secondFp).toNat = secondFp := by
    exact functionResultPtr_toNat secondFp (2 * kWords + 4)
      (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
  have hsecondPayload64 : secondFp + 32 * (2 * kWords + 5) < 2 ^ 64 := by
    have hb := hsecondBound
    dsimp only [secondFp, q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb ⊢
    omega
  have hq3Nat : q3.toNat = q3Fp := by
    exact q3AllocatedPtr_toNat q3Fp kWords
      (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
  have haFrame := functionInitialState_words_below mem aw fp kWords kWords
    (a.toNat + 32) kWords hmemSize hgap haBase (by omega)
  have hbFrame := functionInitialState_words_below mem aw fp kWords kWords
    (b.toNat + 32) kWords hmemSize hgap hbBase (by omega)
  have hfirstValue := firstProduct_value mem aw a b fp kWords hkPos (by omega)
    hcovered hawFit hmemSize hmemLe hgap hfirstBound haEnd hbEnd
  have hfirstValue' : Modexp.wordLimbsToNat
      (memoryWordsFrom firstFinal.memory (fp + 32) (2 * kWords)) = x := by
    simpa only [firstFinal, firstProductInitial, haFrame, hbFrame, haValue, hbValue,
      hxValue] using hfirstValue
  have hproductLowFirst := firstProduct_low_value firstFinal.memory (UInt256.ofNat fp)
    kWords x hkPos (by simpa only [hproductNat] using hfirstValue')
  have hq1ProductFrame := q1AllocatedMemory_words_below firstFinal.memory q1Fp kWords
    ((UInt256.ofNat fp).toNat + 32) (2 * kWords)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by rw [hproductNat]; omega) (by
      rw [hproductNat]
      dsimp only [q1Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hq1ProductValue : Modexp.wordLimbsToNat
      (memoryWordsFrom q1Mem ((UInt256.ofNat fp).toNat + 32) (2 * kWords)) = x := by
    rw [show memoryWordsFrom q1Mem ((UInt256.ofNat fp).toNat + 32) (2 * kWords) =
      memoryWordsFrom firstFinal.memory ((UInt256.ofNat fp).toNat + 32) (2 * kWords) by
        simpa only [q1Mem] using hq1ProductFrame]
    simpa only [hproductNat] using hfirstValue'
  have hproductFit : (UInt256.ofNat fp).toNat + 32 * kWords < UInt256.size := by
    rw [hproductNat]
    exact lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstBound
      omega : fp + 32 * kWords < 2 ^ 64) (by decide)
  have hq1Source : (UInt256.ofNat fp).toNat + 32 * (2 * kWords + 1) ≤ q1Fp + 32 := by
    rw [hproductNat]
    dsimp only [q1Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq1Value := q1Copied_full_value_of_product_value firstFinal.memory
    (UInt256.ofNat fp) q1Fp kWords x hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source (by simpa only [q1Mem] using hq1ProductValue)
  have hmuFirstFrame := functionFinalState_words_below mem aw a b fp kWords kWords
    (mu.toNat + 32) (kWords + 2) (by omega) hcovered hawFit hmemSize hmemLe hgap
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hfirstBound)
    haEnd hbEnd hmuBase (by omega)
  have hmuCopiedFrame := q1CopiedMemory_words_below firstFinal.memory (UInt256.ofNat fp)
    q1Fp kWords (mu.toNat + 32) (kWords + 2) hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source hmuBase (by omega)
  have hmuCopiedValue : Modexp.wordLimbsToNat
      (memoryWordsFrom copiedMem (mu.toNat + 32) (kWords + 2)) =
        UInt256.size ^ (2 * kWords) / nValue := by
    rw [show memoryWordsFrom copiedMem (mu.toNat + 32) (kWords + 2) =
      memoryWordsFrom firstFinal.memory (mu.toNat + 32) (kWords + 2) by
        simpa only [copiedMem, q1Mem, q1] using hmuCopiedFrame]
    rw [show memoryWordsFrom firstFinal.memory (mu.toNat + 32) (kWords + 2) =
      memoryWordsFrom mem (mu.toNat + 32) (kWords + 2) by
        simpa only [firstFinal] using hmuFirstFrame, hmuValue]
  have hq1Geometry := q1Slice_geometry firstFinal.memory firstFinal.activeWords
    (UInt256.ofNat fp) mu q1Fp kWords hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.activeWordsFit)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source (by omega)
  have hq1InitialFrame := functionInitialState_words_below copiedMem copiedAw secondFp
    (kWords + 2) (kWords + 2) (q1.toNat + 32) (kWords + 2)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by rw [hq1Nat]; omega) (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hmuInitialFrame := functionInitialState_words_below copiedMem copiedAw secondFp
    (kWords + 2) (kWords + 2) (mu.toNat + 32) (kWords + 2)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    hmuBase (by omega)
  have hq1InitialValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (secondProductInitial copiedMem copiedAw secondFp kWords).memory
        (q1.toNat + 32) (kWords + 2)) =
        x / UInt256.size ^ (kWords - 1) := by
    rw [show memoryWordsFrom (secondProductInitial copiedMem copiedAw secondFp kWords).memory
        (q1.toNat + 32) (kWords + 2) =
      memoryWordsFrom copiedMem (q1.toNat + 32) (kWords + 2) by
        simpa only [secondProductInitial] using hq1InitialFrame]
    simpa only [hq1Nat, copiedMem, q1Mem, q1] using hq1Value
  have hmuInitialValue : Modexp.wordLimbsToNat
      (memoryWordsFrom (secondProductInitial copiedMem copiedAw secondFp kWords).memory
        (mu.toNat + 32) (kWords + 2)) = UInt256.size ^ (2 * kWords) / nValue := by
    rw [show memoryWordsFrom (secondProductInitial copiedMem copiedAw secondFp kWords).memory
        (mu.toNat + 32) (kWords + 2) =
      memoryWordsFrom copiedMem (mu.toNat + 32) (kWords + 2) by
        simpa only [secondProductInitial] using hmuInitialFrame, hmuCopiedValue]
  have hsecondValue := secondProduct_value copiedMem copiedAw q1 mu secondFp kWords
    (by omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by omega)
  have hsecondValue' : Modexp.wordLimbsToNat
      (memoryWordsFrom q2Final.memory (secondFp + 32) (2 * kWords + 4)) =
        (x / UInt256.size ^ (kWords - 1)) *
          (UInt256.size ^ (2 * kWords) / nValue) := by
    simpa only [q2Final, hq1InitialValue, hmuInitialValue] using hsecondValue
  have hsecondGeometry := secondProductFinal_geometry copiedMem copiedAw q1 mu
    secondFp kWords (by omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by omega)
  have hq2Fit : (UInt256.ofNat secondFp).toNat + 32 * (kWords + 2) < UInt256.size := by
    rw [hsecondNat]
    exact lt_trans (by omega : secondFp + 32 * (kWords + 2) < 2 ^ 64) (by decide)
  have hq2Source : (UInt256.ofNat secondFp).toNat + 32 * (2 * kWords + 5) ≤
      q3Fp + 32 := by
    rw [hsecondNat]
    dsimp only [q3Fp]
    unfold wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hq2Q3Frame := q3AllocatedMemory_words_below q2Final.memory q3Fp kWords
    ((UInt256.ofNat secondFp).toNat + 32) (2 * kWords + 4)
    (by simpa only [q2Final] using hsecondGeometry.memorySize96)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
    (by rw [hsecondNat]; omega) (by
      rw [hsecondNat]
      dsimp only [q3Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hq2Q3Value : Modexp.wordLimbsToNat
      (memoryWordsFrom q3Mem ((UInt256.ofNat secondFp).toNat + 32)
        (2 * kWords + 4)) =
        (x / UInt256.size ^ (kWords - 1)) *
          (UInt256.size ^ (2 * kWords) / nValue) := by
    rw [show memoryWordsFrom q3Mem ((UInt256.ofNat secondFp).toNat + 32)
        (2 * kWords + 4) =
      memoryWordsFrom q2Final.memory ((UInt256.ofNat secondFp).toNat + 32)
        (2 * kWords + 4) by simpa only [q3Mem] using hq2Q3Frame]
    simpa only [hsecondNat] using hsecondValue'
  have hq3Value := q3Copied_low_value_of_product_value q3Mem q3
    (UInt256.ofNat secondFp) kWords nValue x hkPos (by omega) hnNormalized hx
    hq2Fit (by
      rw [hq3Nat]
      exact lt_trans (by omega : q3Fp + 32 < 2 ^ 64 + 32) (by decide))
    (by
      have hq3Size := q3AllocatedMemory_size q2Final.memory q3Fp kWords
        (by simpa only [q2Final] using hsecondGeometry.memorySize96)
        (by simpa only [q2Final, q3Fp] using hsecondGeometry.memoryLeNext)
        (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
      rw [hq3Size]
      exact hq2Source)
    (by
      have hq3Size := q3AllocatedMemory_size q2Final.memory q3Fp kWords
        (by simpa only [q2Final] using hsecondGeometry.memorySize96)
        (by simpa only [q2Final, q3Fp] using hsecondGeometry.memoryLeNext)
        (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
      rw [hq3Nat, hq3Size])
    hq2Q3Value
  have hnEnd' : n.toNat + 32 + 32 * kWords ≤ fp := by omega
  have hnFirstFrame := functionFinalState_words_below mem aw a b fp kWords kWords
    (n.toNat + 32) kWords (by omega) hcovered hawFit hmemSize hmemLe hgap
    (by simpa only [show kWords + kWords = 2 * kWords by omega] using hfirstBound)
    haEnd hbEnd hnBase hnEnd'
  have hnQ1Frame := q1CopiedMemory_words_below firstFinal.memory (UInt256.ofNat fp)
    q1Fp kWords (n.toNat + 32) kWords hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source hnBase (by omega)
  have hnSecondFrame := functionFinalState_words_below copiedMem copiedAw q1 mu secondFp
    (kWords + 2) (kWords + 2) (n.toNat + 32) kWords (by omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega,
      secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by omega) hnBase (by omega)
  have hnQ3Frame := q3CopiedMemory_words_below q2Final.memory (UInt256.ofNat secondFp)
    q3Fp kWords (n.toNat + 32) kWords
    (by simpa only [q2Final] using hsecondGeometry.memorySize96)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.memoryLeNext)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
    hq2Fit hq2Source hnBase (by omega)
  have hnFinal : Modexp.wordLimbsToNat
      (memoryWordsFrom finalMem (n.toNat + 32) kWords) = nValue := by
    rw [show memoryWordsFrom finalMem (n.toNat + 32) kWords =
      memoryWordsFrom q2Final.memory (n.toNat + 32) kWords by
        simpa only [finalMem, q3Mem, q3] using hnQ3Frame]
    rw [show memoryWordsFrom q2Final.memory (n.toNat + 32) kWords =
      memoryWordsFrom copiedMem (n.toNat + 32) kWords by
        simpa only [q2Final] using hnSecondFrame]
    rw [show memoryWordsFrom copiedMem (n.toNat + 32) kWords =
      memoryWordsFrom firstFinal.memory (n.toNat + 32) kWords by
        simpa only [copiedMem, q1Mem, q1] using hnQ1Frame]
    rw [show memoryWordsFrom firstFinal.memory (n.toNat + 32) kWords =
      memoryWordsFrom mem (n.toNat + 32) kWords by
        simpa only [firstFinal] using hnFirstFrame, hnValue]
  have hproductQ1Frame := q1CopiedMemory_words_below firstFinal.memory
    (UInt256.ofNat fp) q1Fp kWords ((UInt256.ofNat fp).toNat + 32) (kWords + 1)
    hkPos (by omega)
    (by simpa only [firstFinal] using hfirstGeometry.memorySize96)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.memoryLeNext)
    (by simpa only [firstFinal, q1Fp] using hfirstGeometry.nextGap)
    (by simpa only [q1Fp, Nat.add_assoc] using hq1Bound)
    hproductFit hq1Source (by rw [hproductNat]; omega) (by
      rw [hproductNat]
      dsimp only [q1Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hproductSecondFrame := functionFinalState_words_below copiedMem copiedAw q1 mu
    secondFp (kWords + 2) (kWords + 2) ((UInt256.ofNat fp).toNat + 32)
    (kWords + 1) (by omega)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.covered)
    (by simpa only [copiedAw, q1Mem, q1Aw, q1] using hq1Geometry.activeWordsFit)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1] using hq1Geometry.memorySize96)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.memoryLeNext)
    (by simpa only [copiedMem, q1Mem, q1Aw, q1, secondFp, q1Fp] using
      hq1Geometry.nextGap)
    (by simpa only [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega,
      secondFp, q1Fp, Nat.add_assoc] using hsecondBound)
    (by
      rw [hq1Nat]
      dsimp only [secondFp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (by omega) (by rw [hproductNat]; omega) (by
      rw [hproductNat]
      dsimp only [secondFp, q1Fp]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hproductQ3Frame := q3CopiedMemory_words_below q2Final.memory
    (UInt256.ofNat secondFp) q3Fp kWords ((UInt256.ofNat fp).toNat + 32)
    (kWords + 1)
    (by simpa only [q2Final] using hsecondGeometry.memorySize96)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.memoryLeNext)
    (by simpa only [q2Final, q3Fp] using hsecondGeometry.nextGap)
    (by simpa only [q3Fp, secondFp, q1Fp, Nat.add_assoc] using hq3Bound)
    hq2Fit hq2Source (by rw [hproductNat]; omega) (by
      rw [hproductNat]
      dsimp only [q3Fp, secondFp, q1Fp]
      omega)
  have hproductFinal : Modexp.wordLimbsToNat
      (memoryWordsFrom finalMem ((UInt256.ofNat fp).toNat + 32) (kWords + 1)) =
        x % UInt256.size ^ (kWords + 1) := by
    rw [show memoryWordsFrom finalMem ((UInt256.ofNat fp).toNat + 32) (kWords + 1) =
      memoryWordsFrom q2Final.memory ((UInt256.ofNat fp).toNat + 32) (kWords + 1) by
        simpa only [finalMem, q3Mem, q3] using hproductQ3Frame]
    rw [show memoryWordsFrom q2Final.memory ((UInt256.ofNat fp).toNat + 32)
        (kWords + 1) =
      memoryWordsFrom copiedMem ((UInt256.ofNat fp).toNat + 32) (kWords + 1) by
        simpa only [q2Final] using hproductSecondFrame]
    rw [show memoryWordsFrom copiedMem ((UInt256.ofNat fp).toNat + 32) (kWords + 1) =
      memoryWordsFrom firstFinal.memory ((UInt256.ofNat fp).toNat + 32) (kWords + 1) by
        simpa only [copiedMem, q1Mem, q1] using hproductQ1Frame]
    simpa only [firstFinal] using hproductLowFirst
  exact ⟨by simpa only [finalMem, q3Mem, q3] using hq3Value, hnFinal, hproductFinal⟩

end Modexp.MultiLimbBarrettMulSemantic
