import Examples.Precompiles.Modexp.MultiLimbBarrettConstantContract
import Examples.Precompiles.Modexp.MultiLimbOddConversionSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookCompleteSemantic

/-!
# Concrete Barrett-constant numerator

The setup trace allocates `2*k+1` words, writes one at index `2*k`, and then allocates the
schoolbook remainder. This module proves that the dividend visible at PC 5199 is exactly
`B^(2*k)`, including all implicit-zero words made concrete by the high store.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbBarrettConstantSemantic

open MultiLimbBarrettConstant
open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookNormalizationSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dividendArrayAddress_toNat (fp k i : Nat) (hi : i ≤ 2 * k)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (arrayAddress (UInt256.ofNat fp) i).toNat = fp + 32 * (i + 1) := by
  have hfpWord : fp < UInt256.size := by
    unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have haddressFit :
      (UInt256.ofNat fp).toNat + 32 * (i + 1) < UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord]
    unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  simpa [UInt256.toNat_ofNat_of_lt hfpWord] using
    MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat fp) i haddressFit

theorem barrettDivisionMemory_size (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp) (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp) (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettDivisionMemory mem fp k).size = remainderPtr fp k + 32 := by
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap hfit
  have hstored96 : 96 ≤ (storedDividendMemory mem fp k).size := by
    rw [hstoredSize]
    omega
  unfold barrettDivisionMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hstored96, hstoredSize]
    rfl
  · rw [setFreePtr_size hstored96, hstoredSize]
    simp [remainderPtr]

/-- The second allocation preserves every complete dividend word. -/
theorem barrettDivisionMemory_read_dividend
    (mem : ByteArray) (fp k i : Nat)
    (hk : k ≤ 32) (hi : i ≤ 2 * k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettDivisionMemory mem fp k).readWithPadding
        (arrayAddress (UInt256.ofNat fp) i).toNat 32 =
      (storedDividendMemory mem fp k).readWithPadding
        (arrayAddress (UInt256.ofNat fp) i).toNat 32 := by
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap hfit
  have hstored96 : 96 ≤ (storedDividendMemory mem fp k).size := by
    rw [hstoredSize]
    omega
  have haddress := dividendArrayAddress_toNat fp k i hi hfit
  have hbelow :
      (arrayAddress (UInt256.ofNat fp) i).toNat + 32 ≤ remainderPtr fp k := by
    rw [haddress]
    unfold remainderPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
    omega
  unfold barrettDivisionMemory
  rw [storeBytesLength_read_below]
  · exact setFreePtr_read_above hstored96 (by rw [haddress]; omega)
      (by rw [hstoredSize]; exact hbelow)
  · rw [setFreePtr_size hstored96, hstoredSize]
    exact hbelow
  · exact hbelow
  · rw [setFreePtr_size hstored96, hstoredSize]
    simp [remainderPtr]

/-- Every word below index `2*k` remains allocator zero padding. -/
theorem storedDividendMemory_low_read_zero
    (mem : ByteArray) (fp k i : Nat)
    (hk : k ≤ 32) (hi : i < 2 * k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (storedDividendMemory mem fp k).readWithPadding
        (arrayAddress (UInt256.ofNat fp) i).toNat 32 =
      UInt256.toByteArray ⟨0⟩ := by
  have hbaseSize := dividendMemory_size mem fp k hmemSize hmemLe hgap
  have haddress := dividendArrayAddress_toNat fp k i (by omega) hfit
  have hhigh := dividendHighAddress_toNat fp k hfit
  have hwriteGap :
      (dividendHighAddress fp k).toNat - (dividendMemory mem fp k).size <
        USize.size := by
    rw [hhigh, hbaseSize]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hbelow :
      (arrayAddress (UInt256.ofNat fp) i).toNat + 32 ≤
        (dividendHighAddress fp k).toNat := by
    rw [haddress, hhigh]
    omega
  have hpast :
      (dividendMemory mem fp k).size ≤
        (arrayAddress (UInt256.ofNat fp) i).toNat := by
    rw [hbaseSize, haddress]
    omega
  unfold storedDividendMemory
  rw [toByteArray_write_read_below_padded_of_gap (⟨1⟩ : UInt256)
    (dividendMemory mem fp k) (dividendHighAddress fp k).toNat
    (arrayAddress (UInt256.ofNat fp) i).toNat
    (by rw [hbaseSize]; omega) hbelow hwriteGap]
  rw [readWithPadding_past_end (dividendMemory mem fp k)
    (arrayAddress (UInt256.ofNat fp) i).toNat 32 hpast (by decide),
    ← zero_toByteArray_eq_zeroes32]

/-- The final word is the concrete one written by PC 3119. -/
theorem storedDividendMemory_high_read_one
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (storedDividendMemory mem fp k).readWithPadding
        (arrayAddress (UInt256.ofNat fp) (2 * k)).toNat 32 =
      UInt256.toByteArray ⟨1⟩ := by
  have hbaseSize := dividendMemory_size mem fp k hmemSize hmemLe hgap
  have haddress := dividendArrayAddress_toNat fp k (2 * k) (by omega) hfit
  have hhigh := dividendHighAddress_toNat fp k hfit
  have hsame :
      arrayAddress (UInt256.ofNat fp) (2 * k) = dividendHighAddress fp k := by
    unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
      MultiLimbSchoolbookShort.arrayAddress dividendHighAddress
    rfl
  have hwriteGap :
      (dividendHighAddress fp k).toNat - (dividendMemory mem fp k).size <
        USize.size := by
    rw [hhigh, hbaseSize]
    have husize : 2048 < USize.size := by native_decide
    omega
  rw [hsame]
  unfold storedDividendMemory
  exact toByteArray_write_read_back_of_gap (⟨1⟩ : UInt256)
    (dividendMemory mem fp k) (dividendHighAddress fp k).toNat hwriteGap

/-- The two generated allocations cover the complete dividend and remainder payloads, and their
final active-word count remains representable as a byte extent. -/
theorem barrettDivisionWords_range (aw : UInt256) (fp k : Nat)
    (hkPos : 0 < k) (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    remainderPtr fp k + 32 + 32 * k ≤
        32 * (barrettDivisionWords aw fp k).toNat ∧
      (barrettDivisionWords aw fp k).toNat * 32 < UInt256.size := by
  have hfirst := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (dividendLength k) (by unfold dividendLength; omega) hawFit hfirstFit
  exact MultiLimbOddConversionSemantic.newWordArrayWords_range
    (dividendWords aw fp k) (remainderPtr fp k) k hkPos hfirst.2 hsecondFit

private theorem arrayWord_eq_of_covered_read
    (mem : ByteArray) (aw array value : UInt256) (index : Nat)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hword : (arrayAddress array index).toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding (arrayAddress array index).toNat 32 =
      UInt256.toByteArray value) :
    arrayWord mem aw array index = value := by
  have hactive := MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered mem aw
    (arrayAddress array index) hcovered hawFit hword
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress at hactive hread hword
  unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
    MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by omega, hactive⟩), hread,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- Equal concrete reads under independently covered active-memory states induce equal guarded
array words. -/
private theorem arrayWord_eq_of_covered_reads
    (left right : ByteArray) (leftAw rightAw leftArray rightArray : UInt256)
    (leftIndex rightIndex : Nat)
    (hleftCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered left leftAw)
    (hrightCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered right rightAw)
    (hleftAwFit : leftAw.toNat * 32 < UInt256.size)
    (hrightAwFit : rightAw.toNat * 32 < UInt256.size)
    (hleftWord : (arrayAddress leftArray leftIndex).toNat + 32 ≤ left.size)
    (hrightWord : (arrayAddress rightArray rightIndex).toNat + 32 ≤ right.size)
    (hread : left.readWithPadding (arrayAddress leftArray leftIndex).toNat 32 =
      right.readWithPadding (arrayAddress rightArray rightIndex).toNat 32) :
    arrayWord left leftAw leftArray leftIndex =
      arrayWord right rightAw rightArray rightIndex := by
  have hleftActive := MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
    left leftAw (arrayAddress leftArray leftIndex) hleftCovered hleftAwFit hleftWord
  have hrightActive := MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
    right rightAw (arrayAddress rightArray rightIndex) hrightCovered hrightAwFit hrightWord
  have hleftActive' :
      ¬ MultiLimbSchoolbookShort.arrayAddress leftArray leftIndex ≥ leftAw * ⟨32⟩ := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hleftActive
  have hrightActive' :
      ¬ MultiLimbSchoolbookShort.arrayAddress rightArray rightIndex ≥ rightAw * ⟨32⟩ := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hrightActive
  have hleftWord' :
      (MultiLimbSchoolbookShort.arrayAddress leftArray leftIndex).toNat + 32 ≤ left.size := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hleftWord
  have hrightWord' :
      (MultiLimbSchoolbookShort.arrayAddress rightArray rightIndex).toNat + 32 ≤ right.size := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hrightWord
  have hread' :
      left.readWithPadding
          (MultiLimbSchoolbookShort.arrayAddress leftArray leftIndex).toNat 32 =
        right.readWithPadding
          (MultiLimbSchoolbookShort.arrayAddress rightArray rightIndex).toNat 32 := by
    simpa only [arrayAddress, MultiLimbSchoolbookSingle.arrayAddress] using hread
  unfold arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
    MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by omega, hleftActive'⟩),
    if_neg (not_or.mpr ⟨by omega, hrightActive'⟩), hread']

private theorem arrayReadWords_eq_of_words_twoAw
    (left right : ByteArray) (leftAw rightAw leftArray rightArray : UInt256)
    (start count : Nat)
    (hwords : ∀ i, i < count ->
      arrayWord left leftAw leftArray (start + i) =
        arrayWord right rightAw rightArray (start + i)) :
    arrayReadWords left leftAw leftArray start count =
      arrayReadWords right rightAw rightArray start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [arrayReadWords]
      have hhead := hwords 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [hhead]
      apply congrArg (fun words => _ :: words)
      apply ih (start + 1)
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hwords (i + 1) (by omega)

/-- Every low dividend limb presented to schoolbook division is the allocator's concrete zero. -/
theorem barrettDivisionMemory_low_word_zero
    (mem : ByteArray) (aw : UInt256) (fp k i : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hi : i < 2 * k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    arrayWord (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      (UInt256.ofNat fp) i = ⟨0⟩ := by
  have hrange := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  have hsize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have haddress := dividendArrayAddress_toNat fp k i (by omega) hfirstFit
  have hword :
      (arrayAddress (UInt256.ofNat fp) i).toNat + 32 ≤
        (barrettDivisionMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold remainderPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    omega
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [barrettDivisionMemory_read_dividend mem fp k i hk (by omega) hfp hmemSize hmemLe
    hgap hfirstFit]
  exact storedDividendMemory_low_read_zero mem fp k i hk hi hfp hmemSize hmemLe hgap
    hfirstFit

/-- The most-significant dividend limb presented to schoolbook division is exactly one. -/
theorem barrettDivisionMemory_high_word_one
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    arrayWord (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      (UInt256.ofNat fp) (2 * k) = ⟨1⟩ := by
  have hrange := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  have hsize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have haddress := dividendArrayAddress_toNat fp k (2 * k) (by omega) hfirstFit
  have hword :
      (arrayAddress (UInt256.ofNat fp) (2 * k)).toNat + 32 ≤
        (barrettDivisionMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold remainderPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    omega
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [barrettDivisionMemory_read_dividend mem fp k (2 * k) hk (by omega) hfp hmemSize
    hmemLe hgap hfirstFit]
  exact storedDividendMemory_high_read_one mem fp k hk hmemSize hmemLe hgap hfirstFit

/-- The concrete Barrett dividend header survives its high-word store and the later remainder
allocation. -/
theorem barrettDivisionMemory_dividendHeaderRead
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettDivisionMemory mem fp k).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (dividendLength k)) := by
  have hbaseSize := dividendMemory_size mem fp k hmemSize hmemLe hgap
  have hhigh := dividendHighAddress_toNat fp k hfit
  have hwriteGap :
      (dividendHighAddress fp k).toNat - (dividendMemory mem fp k).size < USize.size := by
    rw [hhigh, hbaseSize]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hstoredRead : (storedDividendMemory mem fp k).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (dividendLength k)) := by
    unfold storedDividendMemory
    rw [toByteArray_write_read_below_padded_of_gap (⟨1⟩ : UInt256)
      (dividendMemory mem fp k) (dividendHighAddress fp k).toNat fp
      (by rw [hbaseSize]; omega) (by rw [hhigh]; omega) hwriteGap]
    unfold dividendMemory
    exact storeBytesLength_read_self (by rw [setFreePtr_size hmemSize]; exact hgap)
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap hfit
  have hstored96 : 96 ≤ (storedDividendMemory mem fp k).size := by
    rw [hstoredSize]
    omega
  have hfpBelowRem : fp + 32 ≤ remainderPtr fp k := by
    simp only [remainderPtr, wordArrayAllocationSize, wordArrayPayloadSize, dividendLength]
    omega
  have hremGap : remainderPtr fp k - (storedDividendMemory mem fp k).size < USize.size := by
    rw [hstoredSize]
    unfold remainderPtr
    have husize : 0 < USize.size := by native_decide
    omega
  unfold barrettDivisionMemory
  rw [storeBytesLength_read_below]
  · exact (setFreePtr_read_above hstored96 hfp (by
      rw [hstoredSize]
      exact hfpBelowRem)).trans hstoredRead
  · rw [setFreePtr_size hstored96, hstoredSize]
    exact hfpBelowRem
  · exact hfpBelowRem
  · rw [setFreePtr_size hstored96]
    exact hremGap

/-- The generated Barrett numerator is an ordinary covered array at the schoolbook entry. -/
theorem barrettDivisionDividendLayout
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    MultiLimbArrayReadSemantic.Layout (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) fp (dividendLength k) := by
  have hsize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hrange := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  apply MultiLimbArrayReadSemantic.layout_of_geometry
  · unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  · rw [hsize]
    unfold remainderPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact le_trans (by
      unfold remainderPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
      omega) hrange.1
  · exact hrange.2
  · exact barrettDivisionMemory_dividendHeaderRead mem fp k hk hfp hmemSize hmemLe hgap
      hfirstFit

/-- The concrete `2*k+1`-word numerator passed to schoolbook division denotes `B^(2*k)`. -/
theorem barrettDividend_value
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettDivisionMemory mem fp k)
          (barrettDivisionWords aw fp k) (UInt256.ofNat fp) 0 (dividendLength k)) =
      UInt256.size ^ (2 * k) := by
  have hlow :
      Modexp.wordLimbsToNat
          (arrayReadWords (barrettDivisionMemory mem fp k)
            (barrettDivisionWords aw fp k) (UInt256.ofNat fp) 0 (2 * k)) = 0 := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
    intro i hi
    simpa only [Nat.zero_add] using
      barrettDivisionMemory_low_word_zero mem aw fp k i hk hkPos hi hfp hmemSize
        hmemLe hgap hawFit hfirstFit hsecondFit
  have hhigh := barrettDivisionMemory_high_word_one mem aw fp k hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit
  unfold dividendLength
  rw [arrayReadWords_succ_append, Modexp.wordLimbsToNat_append,
    arrayReadWords_length, hlow]
  simp only [Nat.zero_add]
  rw [hhigh]
  simp only [Modexp.wordLimbsToNat,
    show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mul_zero, Nat.add_zero, Nat.mul_one]

def quotientPtr (fp k : Nat) : Nat :=
  remainderPtr fp k + wordArrayAllocationSize k

def quotientCount (k : Nat) : Nat :=
  MultiLimbSchoolbookKnuthPrefix.numQ (dividendLength k) k

def normalizedDividendPtr (fp k : Nat) : Nat :=
  quotientPtr fp k + wordArrayAllocationSize (quotientCount k)

def barrettQuotientMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthPrefix.quotientMemory (barrettDivisionMemory mem fp k)
    (quotientPtr fp k) (dividendLength k) k

def barrettUMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthPrefix.uMemory (barrettDivisionMemory mem fp k)
    (quotientPtr fp k) (normalizedDividendPtr fp k) (dividendLength k) k

def barrettCopiedMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthPrefix.copiedMemory (barrettDivisionMemory mem fp k)
    (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k

def barrettQuotientWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthPrefix.quotientWords (barrettDivisionWords aw fp k)
    (quotientPtr fp k) (dividendLength k) k

def barrettUWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthPrefix.uWords (barrettDivisionWords aw fp k)
    (quotientPtr fp k) (normalizedDividendPtr fp k) (dividendLength k) k

def barrettCopiedWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthPrefix.copiedWords (barrettDivisionWords aw fp k)
    (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k

def normalizedDivisorPtr (fp k : Nat) : Nat :=
  normalizedDividendPtr fp k + wordArrayAllocationSize (dividendLength k + 1)

def barrettVMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  MultiLimbSchoolbookNormalization.vMemory (barrettCopiedMemory mem fp k)
    (normalizedDivisorPtr fp k) k

def barrettVWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  MultiLimbSchoolbookNormalization.vWords (barrettCopiedWords aw fp k)
    (normalizedDivisorPtr fp k) k

def barrettPositiveDivisorResult
    (mem : ByteArray) (aw : UInt256) (fp k : Nat) (divisor top : UInt256) :
    MultiLimbSchoolbookNormalization.DivisorShiftResult :=
  MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor
    (UInt256.ofNat (normalizedDivisorPtr fp k)) k (MultiLimbClz.clzResult top).n

def barrettPositiveDividendResult
    (mem : ByteArray) (aw : UInt256) (fp k : Nat) (divisor top : UInt256) :
    MultiLimbSchoolbookNormalization.DivisorShiftResult :=
  MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor
    (UInt256.ofNat (normalizedDivisorPtr fp k))
    (UInt256.ofNat (normalizedDividendPtr fp k)) k (dividendLength k)
    (MultiLimbClz.clzResult top).n

def barrettPositiveMemory
    (mem : ByteArray) (aw : UInt256) (fp k : Nat) (divisor top : UInt256) : ByteArray :=
  MultiLimbSchoolbookNormalizationFunction.positiveMemory
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor
    (UInt256.ofNat (normalizedDivisorPtr fp k))
    (UInt256.ofNat (normalizedDividendPtr fp k)) k (dividendLength k)
    (MultiLimbClz.clzResult top).n

def barrettZeroMemory
    (mem : ByteArray) (fp k divisorPtr : Nat) : ByteArray :=
  MultiLimbSchoolbookNormalizationFunction.zeroMemory
    (barrettCopiedMemory mem fp k) divisorPtr (normalizedDivisorPtr fp k) k

def barrettZeroWords
    (aw : UInt256) (fp k divisorPtr : Nat) : UInt256 :=
  MultiLimbSchoolbookNormalizationFunction.zeroWords
    (barrettCopiedWords aw fp k) divisorPtr (normalizedDivisorPtr fp k) k

@[simp] theorem quotientCount_eq (k : Nat) : quotientCount k = k + 2 := by
  unfold quotientCount MultiLimbSchoolbookKnuthPrefix.numQ dividendLength
  omega

/-- The remainder allocation leaves the quotient pointer in Solidity's free-pointer word. -/
theorem barrettDivisionMemory_read64
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettDivisionMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (quotientPtr fp k)) := by
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap hfirstFit
  have hstored96 : 96 ≤ (storedDividendMemory mem fp k).size := by
    rw [hstoredSize]
    omega
  have hremLe : (storedDividendMemory mem fp k).size ≤ remainderPtr fp k := by
    rw [hstoredSize]
    rfl
  have hremGap : remainderPtr fp k - (storedDividendMemory mem fp k).size < USize.size := by
    rw [hstoredSize]
    have husize : 0 < USize.size := by native_decide
    simpa [remainderPtr] using husize
  unfold barrettDivisionMemory quotientPtr
  rw [storeBytesLength_read64 (by rw [setFreePtr_size hstored96]; omega)
    (by unfold remainderPtr; omega)
    (by rw [setFreePtr_size hstored96]; exact hremGap)]
  exact setFreePtr_read64 hstored96

/-- The generated numerator and remainder allocations preserve every complete source word above
Solidity's reserved prefix and below the first fresh allocation. -/
theorem barrettDivisionMemory_read_below_fp
    (mem : ByteArray) (fp k read : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hread96 : 96 ≤ read) (hreadBelow : read + 32 ≤ fp) :
    (barrettDivisionMemory mem fp k).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap hfirstFit
  have hstored96 : 96 ≤ (storedDividendMemory mem fp k).size := by
    rw [hstoredSize]
    omega
  have hremGap : remainderPtr fp k - (storedDividendMemory mem fp k).size < USize.size := by
    rw [hstoredSize]
    have husize : 0 < USize.size := by native_decide
    simpa [remainderPtr] using husize
  unfold barrettDivisionMemory
  rw [storeBytesLength_read_below_padded
    (by rw [setFreePtr_size hstored96]; omega)
    (by unfold remainderPtr; omega)
    (by rw [setFreePtr_size hstored96]; exact hremGap)]
  rw [setFreePtr_read_above_padded hstored96 hread96]
  exact storedDividendMemory_read_below_fp mem fp k read hk hmemSize hmemLe hgap
    hfirstFit hread96 hreadBelow

/-- The quotient allocation materializes exactly its header word at the fresh pointer. -/
theorem barrettQuotientMemory_size
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettQuotientMemory mem fp k).size = quotientPtr fp k + 32 := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqGap : quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  unfold barrettQuotientMemory MultiLimbSchoolbookKnuthPrefix.quotientMemory
    MultiLimbSchoolbookKnuthSetup.quotientMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hbase96, hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [setFreePtr_size hbase96]
    exact hqGap

/-- The quotient allocation advances Solidity's free pointer to the normalized dividend. -/
theorem barrettQuotientMemory_read64
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettQuotientMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (normalizedDividendPtr fp k)) := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqGap : quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  unfold barrettQuotientMemory MultiLimbSchoolbookKnuthPrefix.quotientMemory
    MultiLimbSchoolbookKnuthSetup.quotientMemory normalizedDividendPtr
  rw [storeBytesLength_read64 (by rw [setFreePtr_size hbase96]; exact hbase96)
    (by unfold quotientPtr remainderPtr; omega)
    (by rw [setFreePtr_size hbase96]; exact hqGap)]
  exact setFreePtr_read64 hbase96

/-- The quotient and `u` allocations both preserve every word of the Barrett numerator. -/
theorem barrettUMemory_read_dividend
    (mem : ByteArray) (fp k i : Nat)
    (hk : k ≤ 32) (hi : i ≤ 2 * k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettUMemory mem fp k).readWithPadding (fp + 32 + 32 * i) 32 =
      (barrettDivisionMemory mem fp k).readWithPadding (fp + 32 + 32 * i) 32 := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqGap :
      quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqRead :=
    MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (barrettDivisionMemory mem fp k) (quotientPtr fp k) (quotientCount k)
      (fp + 32 + 32 * i) hbase96 hqGap (by omega) (by
        unfold quotientPtr remainderPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
        omega)
  have hqSetSize :
      (setFreePtr (barrettDivisionMemory mem fp k)
        (quotientPtr fp k + wordArrayAllocationSize (quotientCount k))).size =
        (barrettDivisionMemory mem fp k).size := setFreePtr_size hbase96
  unfold quotientCount at hqSetSize
  have hqGap :
      quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqSize : (barrettQuotientMemory mem fp k).size = quotientPtr fp k + 32 := by
    unfold barrettQuotientMemory MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    apply storeBytesLength_size
    · rw [hqSetSize, hbaseSize]
      unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rwa [hqSetSize]
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by
    rw [hqSize]
    unfold quotientPtr remainderPtr
    omega
  have huGap :
      normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size < USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have huGap :
      normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size < USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have huRead :=
    MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (barrettQuotientMemory mem fp k) (normalizedDividendPtr fp k)
      (dividendLength k + 1) (fp + 32 + 32 * i) hq96 huGap (by omega) (by
        unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
          MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
        omega)
  unfold barrettUMemory at huRead
  unfold barrettQuotientMemory at hqRead
  exact huRead.trans hqRead

/-- The normalized-dividend allocation materializes its header exactly at its fresh pointer. -/
theorem barrettUMemory_size
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettUMemory mem fp k).size = normalizedDividendPtr fp k + 32 := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqSetSize :
      (setFreePtr (barrettDivisionMemory mem fp k)
        (quotientPtr fp k + wordArrayAllocationSize (quotientCount k))).size =
        (barrettDivisionMemory mem fp k).size := setFreePtr_size hbase96
  unfold quotientCount at hqSetSize
  have hqGap :
      quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqSize : (barrettQuotientMemory mem fp k).size = quotientPtr fp k + 32 := by
    unfold barrettQuotientMemory MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    apply storeBytesLength_size
    · rw [hqSetSize, hbaseSize]
      unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rwa [hqSetSize]
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by
    rw [hqSize]
    unfold quotientPtr remainderPtr
    omega
  have huGap :
      normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size < USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have huSetSize :
      (setFreePtr (barrettQuotientMemory mem fp k)
        (normalizedDividendPtr fp k + wordArrayAllocationSize (dividendLength k + 1))).size =
        (barrettQuotientMemory mem fp k).size := setFreePtr_size hq96
  unfold barrettQuotientMemory at huSetSize
  have hqSizeExpanded := hqSize
  unfold barrettQuotientMemory at hqSizeExpanded
  unfold barrettUMemory MultiLimbSchoolbookKnuthPrefix.uMemory
    MultiLimbSchoolbookKnuthSetup.uMemory
  apply storeBytesLength_size
  · rw [huSetSize, hqSizeExpanded]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rwa [huSetSize]

/-- The normalized-dividend allocation advances the free pointer to normalized divisor `v`. -/
theorem barrettUMemory_read64
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettUMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (normalizedDivisorPtr fp k)) := by
  have hqSize := barrettQuotientMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by
    rw [hqSize]
    unfold quotientPtr remainderPtr
    omega
  have hqGap : normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size <
      USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  change (storeBytesLength
    (setFreePtr (barrettQuotientMemory mem fp k)
      (normalizedDividendPtr fp k + wordArrayAllocationSize (dividendLength k + 1)))
    (normalizedDividendPtr fp k) (dividendLength k + 1)).readWithPadding 64 32 = _
  unfold normalizedDivisorPtr
  rw [storeBytesLength_read64 (by rw [setFreePtr_size hq96]; exact hq96)
    (by unfold normalizedDividendPtr quotientPtr remainderPtr; omega)
    (by rw [setFreePtr_size hq96]; exact hqGap)]
  exact setFreePtr_read64 hq96

/-- The deployed `MCOPY` starts at the end of the allocated `u` header and materializes all copied
numerator words. -/
theorem barrettCopiedMemory_size
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettCopiedMemory mem fp k).size =
      normalizedDividendPtr fp k + 32 + 32 * dividendLength k := by
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  unfold barrettCopiedMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
  change
    ((barrettUMemory mem fp k).write (fp + 32) (barrettUMemory mem fp k)
      (normalizedDividendPtr fp k + 32) (32 * dividendLength k)).size = _
  rw [← huSize]
  rw [write_end_size_from]
  · unfold dividendLength
    omega
  · rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega

/-- The setup `MCOPY` starts above the free-pointer word and therefore preserves it. -/
theorem barrettCopiedMemory_read64
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettCopiedMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (normalizedDivisorPtr fp k)) := by
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hsource : fp + 32 + 32 * dividendLength k ≤ (barrettUMemory mem fp k).size := by
    rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hread := write_read_below_end_from (barrettUMemory mem fp k)
    (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k) 64
    (by unfold dividendLength; omega) hsource (by rw [huSize]; omega)
  unfold barrettCopiedMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
    MultiLimbSchoolbookKnuthSetup.copiedUMemory
  rw [← huSize]
  exact hread.trans
    (barrettUMemory_read64 mem fp k hk hfp hmemSize hmemLe hgap hfirstFit)

/-- Every complete source word below the generated Barrett numerator survives the quotient and
`u` allocations and the numerator `MCOPY`. -/
theorem barrettCopiedMemory_read_below_fp
    (mem : ByteArray) (fp k read : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hread96 : 96 ≤ read) (hreadBelow : read + 32 ≤ fp) :
    (barrettCopiedMemory mem fp k).readWithPadding read 32 =
      (barrettDivisionMemory mem fp k).readWithPadding read 32 := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqGap : quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettDivisionMemory mem fp k) (quotientPtr fp k) (quotientCount k) read
    hbase96 hqGap hread96 (by unfold quotientPtr remainderPtr; omega)
  have hqSize := barrettQuotientMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by
    rw [hqSize]
    unfold quotientPtr remainderPtr
    omega
  have huGap : normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size <
      USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have huRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettQuotientMemory mem fp k) (normalizedDividendPtr fp k)
    (dividendLength k + 1) read hq96 huGap hread96 (by
      unfold normalizedDividendPtr quotientPtr remainderPtr
      omega)
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hsource : fp + 32 + 32 * dividendLength k ≤ (barrettUMemory mem fp k).size := by
    rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopyRead : (barrettCopiedMemory mem fp k).readWithPadding read 32 =
      (barrettUMemory mem fp k).readWithPadding read 32 := by
    have hread := write_read_below_end_from (barrettUMemory mem fp k)
      (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k) read
      (by unfold dividendLength; omega) hsource (by rw [huSize]; omega)
    unfold barrettCopiedMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
      MultiLimbSchoolbookKnuthSetup.copiedUMemory
    rw [← huSize]
    exact hread
  exact hcopyRead.trans (huRead.trans (hqRead.trans rfl))

/-- Allocating normalized divisor `v` extends across exactly the unused top `u` word and writes
the `v` header at the next free pointer. -/
theorem barrettVMemory_size
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).size = normalizedDivisorPtr fp k + 32 := by
  have hcopiedSize :=
    barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hcopied96 : 96 ≤ (barrettCopiedMemory mem fp k).size := by
    rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  unfold barrettVMemory MultiLimbSchoolbookNormalization.vMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hcopied96, hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [setFreePtr_size hcopied96, hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 32 < USize.size := by native_decide
    omega

/-- Allocating normalized divisor `v` advances Solidity's free pointer to the end of its full
payload, even though only the array header is concrete at this point. -/
theorem barrettVMemory_read64
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) := by
  have hcopiedSize :=
    barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hcopied96 : 96 ≤ (barrettCopiedMemory mem fp k).size := by
    rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hvGap : normalizedDivisorPtr fp k - (barrettCopiedMemory mem fp k).size <
      USize.size := by
    rw [hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 32 < USize.size := by native_decide
    omega
  unfold barrettVMemory MultiLimbSchoolbookNormalization.vMemory
  rw [storeBytesLength_read64 (by rw [setFreePtr_size hcopied96]; exact hcopied96)
    (by unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr; omega)
    (by rw [setFreePtr_size hcopied96]; exact hvGap)]
  exact setFreePtr_read64 hcopied96

/-- Every complete source word below the generated Barrett numerator survives all Knuth setup
allocations, the numerator `MCOPY`, and the normalized-divisor allocation. -/
theorem barrettVMemory_read_below_fp
    (mem : ByteArray) (fp k read : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hread96 : 96 ≤ read) (hreadBelow : read + 32 ≤ fp) :
    (barrettVMemory mem fp k).readWithPadding read 32 =
      (barrettDivisionMemory mem fp k).readWithPadding read 32 := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqGap : quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettDivisionMemory mem fp k) (quotientPtr fp k) (quotientCount k) read
    hbase96 hqGap hread96 (by unfold quotientPtr remainderPtr; omega)
  have hqSize := barrettQuotientMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by
    rw [hqSize]
    unfold quotientPtr remainderPtr
    omega
  have huGap : normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size <
      USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have huRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettQuotientMemory mem fp k) (normalizedDividendPtr fp k)
    (dividendLength k + 1) read hq96 huGap hread96 (by
      unfold normalizedDividendPtr quotientPtr remainderPtr
      omega)
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hsource : fp + 32 + 32 * dividendLength k ≤ (barrettUMemory mem fp k).size := by
    rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopyRead : (barrettCopiedMemory mem fp k).readWithPadding read 32 =
      (barrettUMemory mem fp k).readWithPadding read 32 := by
    have hread := write_read_below_end_from (barrettUMemory mem fp k)
      (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k) read
      (by unfold dividendLength; omega) hsource (by rw [huSize]; omega)
    unfold barrettCopiedMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
      MultiLimbSchoolbookKnuthSetup.copiedUMemory
    rw [← huSize]
    exact hread
  have hcopiedSize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hcopied96 : 96 ≤ (barrettCopiedMemory mem fp k).size := by
    rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hvGap : normalizedDivisorPtr fp k - (barrettCopiedMemory mem fp k).size <
      USize.size := by
    rw [hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 32 < USize.size := by native_decide
    omega
  have hvRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettCopiedMemory mem fp k) (normalizedDivisorPtr fp k) k read
    hcopied96 hvGap hread96 (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      omega)
  exact hvRead.trans (hcopyRead.trans (huRead.trans (hqRead.trans rfl)))

/-- The normalized-divisor allocation preserves every copied numerator word and the unused
top-`u` padding word immediately above it. -/
theorem barrettVMemory_read_u_word
    (mem : ByteArray) (fp k i : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hi : i ≤ dividendLength k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * i) 32 =
      (barrettCopiedMemory mem fp k).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * i) 32 := by
  have hcopiedSize :=
    barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hcopied96 : 96 ≤ (barrettCopiedMemory mem fp k).size := by
    rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hallocation :=
    MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (barrettCopiedMemory mem fp k) (normalizedDivisorPtr fp k) k
      (normalizedDividendPtr fp k + 32 + 32 * i) hcopied96 (by
        rw [hcopiedSize]
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        have husize : 32 < USize.size := by native_decide
        omega) (by
          unfold normalizedDividendPtr quotientPtr remainderPtr
          omega) (by
            unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
            omega)
  unfold barrettVMemory
  exact hallocation

/-- The allocator gap becomes the concrete zero top limb of Knuth's `m+1`-word `u` array. -/
theorem barrettVMemory_top_u_read_zero
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * dividendLength k) 32 =
      UInt256.toByteArray ⟨0⟩ := by
  rw [barrettVMemory_read_u_word mem fp k (dividendLength k) hk hkPos (by omega)
    hfp hmemSize hmemLe hgap hfirstFit]
  have hcopiedSize :=
    barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  rw [readWithPadding_past_end (barrettCopiedMemory mem fp k)
    (normalizedDividendPtr fp k + 32 + 32 * dividendLength k) 32 (by omega)
    (by norm_num), ← zero_toByteArray_eq_zeroes32]

/-- The zero-shift `MCOPY` begins at the end of the `v` header and materializes exactly its `k`
payload words. -/
theorem barrettZeroMemory_size
    (mem : ByteArray) (fp k divisorPtr : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).size =
      normalizedDivisorPtr fp k + 32 + 32 * k := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  change
    ((barrettVMemory mem fp k).write (divisorPtr + 32) (barrettVMemory mem fp k)
      (normalizedDivisorPtr fp k + 32) (32 * k)).size = _
  rw [← hvSize]
  rw [write_end_size_from]
  · omega
  · exact hsource

/-- Zero-shift divisor copying preserves every word of the complete `m+1`-word `u` array below
the fresh destination. -/
theorem barrettZeroMemory_read_u_word
    (mem : ByteArray) (fp k divisorPtr i : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hi : i ≤ dividendLength k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * i) 32 =
      (barrettVMemory mem fp k).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * i) 32 := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hread : normalizedDividendPtr fp k + 32 + 32 * i + 32 ≤
      (barrettVMemory mem fp k).size := by
    rw [hvSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  change
    ((barrettVMemory mem fp k).write (divisorPtr + 32) (barrettVMemory mem fp k)
      (normalizedDivisorPtr fp k + 32) (32 * k)).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * i) 32 = _
  rw [← hvSize]
  exact write_read_below_end_from (barrettVMemory mem fp k) (barrettVMemory mem fp k)
    (divisorPtr + 32) (32 * k) (normalizedDividendPtr fp k + 32 + 32 * i)
    (by omega) hsource hread

/-- Each zero-shift normalized-divisor word is exactly the corresponding concrete modulus word. -/
theorem barrettZeroMemory_read_v_word
    (mem : ByteArray) (fp k divisorPtr i : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hi : i < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding
        (normalizedDivisorPtr fp k + 32 + 32 * i) 32 =
      (barrettVMemory mem fp k).readWithPadding (divisorPtr + 32 + 32 * i) 32 := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
  exact MultiLimbSchoolbookNormalization.shiftZeroMemory_limb
    (barrettVMemory mem fp k) divisorPtr (normalizedDivisorPtr fp k) k i hkPos hi
    hsource (by rw [hvSize])

/-- After the deployed `MCOPY`, every normalized-dividend input word is the corresponding word of
the concrete Barrett numerator. -/
theorem barrettCopiedMemory_read_word
    (mem : ByteArray) (fp k i : Nat)
    (hk : k ≤ 32) (hi : i < dividendLength k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettCopiedMemory mem fp k).readWithPadding
        (normalizedDividendPtr fp k + 32 + 32 * i) 32 =
      (barrettDivisionMemory mem fp k).readWithPadding (fp + 32 + 32 * i) 32 := by
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hqGap :
      quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqSetSize :
      (setFreePtr (barrettDivisionMemory mem fp k)
        (quotientPtr fp k + wordArrayAllocationSize (quotientCount k))).size =
        (barrettDivisionMemory mem fp k).size := setFreePtr_size hbase96
  unfold quotientCount at hqSetSize
  have hqSize : (barrettQuotientMemory mem fp k).size = quotientPtr fp k + 32 := by
    unfold barrettQuotientMemory MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    apply storeBytesLength_size
    · rw [hqSetSize, hbaseSize]
      unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rwa [hqSetSize]
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by
    rw [hqSize]
    unfold quotientPtr remainderPtr
    omega
  have huGap :
      normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size < USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have huSetSize :
      (setFreePtr (barrettQuotientMemory mem fp k)
        (normalizedDividendPtr fp k + wordArrayAllocationSize (dividendLength k + 1))).size =
        (barrettQuotientMemory mem fp k).size := setFreePtr_size hq96
  unfold barrettQuotientMemory at huSetSize
  have hqSizeExpanded := hqSize
  unfold barrettQuotientMemory at hqSizeExpanded
  have huSize : (barrettUMemory mem fp k).size = normalizedDividendPtr fp k + 32 := by
    unfold barrettUMemory MultiLimbSchoolbookKnuthPrefix.uMemory
      MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [huSetSize, hqSizeExpanded]
      unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rwa [huSetSize]
  have hcopy := MultiLimbSchoolbookKnuthSetupSemantic.copiedUMemory_read_word
    (barrettUMemory mem fp k) (normalizedDividendPtr fp k) fp (dividendLength k) i
    (by unfold dividendLength; omega) hi (by
      rw [huSize]
      unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
        MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
      omega) (by rw [huSize])
  unfold barrettCopiedMemory at hcopy
  exact hcopy.trans (barrettUMemory_read_dividend mem fp k i hk (by
    unfold dividendLength at hi
    omega) hfp hmemSize hmemLe hgap hfirstFit)

/-- The exact active-word counter after Knuth's `MCOPY` covers the complete copied numerator and
remains representable as an EVM byte extent. -/
theorem barrettCopiedWords_range
    (aw : UInt256) (fp k : Nat) (hkPos : 0 < k)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size) :
    normalizedDividendPtr fp k + 32 + 32 * dividendLength k ≤
        32 * (barrettCopiedWords aw fp k).toNat ∧
      (barrettCopiedWords aw fp k).toNat * 32 < UInt256.size := by
  have hdivision := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  have hquotient := MultiLimbOddConversionSemantic.newWordArrayWords_range
    (barrettDivisionWords aw fp k) (quotientPtr fp k) (quotientCount k)
    (by rw [quotientCount_eq]; omega) hdivision.2 hquotientFit
  have hu := MultiLimbOddConversionSemantic.newWordArrayWords_range
    (barrettQuotientWords aw fp k) (normalizedDividendPtr fp k) (dividendLength k + 1)
    (by unfold dividendLength; omega) (by
      unfold barrettQuotientWords MultiLimbSchoolbookKnuthPrefix.quotientWords
        MultiLimbSchoolbookKnuthSetup.quotientWords
      exact hquotient.2) huFit
  have hcopyAccess :
      max (normalizedDividendPtr fp k + 32) (fp + 32) + 32 * dividendLength k + 31 <
        UInt256.size := by
    have hptr : fp + 32 ≤ normalizedDividendPtr fp k + 32 := by
      unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    rw [max_eq_left hptr]
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hmFit := MultiLimbMontgomeryCIOSSemantic.machineM_mul32_lt_size hu.2 hcopyAccess
  have hmLt :
      MachineState.M (barrettUWords aw fp k).toNat
        (max (normalizedDividendPtr fp k + 32) (fp + 32))
        (32 * dividendLength k) < UInt256.size := by
    have hle := Nat.mul_le_mul_left
      (MachineState.M (barrettUWords aw fp k).toNat
        (max (normalizedDividendPtr fp k + 32) (fp + 32))
        (32 * dividendLength k)) (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hmFit
  have hcopiedNat : (barrettCopiedWords aw fp k).toNat =
      MachineState.M (barrettUWords aw fp k).toNat
        (max (normalizedDividendPtr fp k + 32) (fp + 32))
        (32 * dividendLength k) := by
    unfold barrettCopiedWords MultiLimbSchoolbookKnuthPrefix.copiedWords
      MultiLimbSchoolbookKnuthSetup.copiedUWords
    change
      (UInt256.ofNat
        (MachineState.M (barrettUWords aw fp k).toNat
          (max (normalizedDividendPtr fp k + 32) (fp + 32))
          (32 * dividendLength k))).toNat = _
    rw [UInt256.toNat_ofNat_of_lt hmLt]
  constructor
  · rw [hcopiedNat]
    have hptr : fp + 32 ≤ normalizedDividendPtr fp k + 32 := by
      unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    have haccess := MultiLimbMontgomeryCIOSSemantic.machineM_access_le
      (s := (barrettUWords aw fp k).toNat)
      (off := normalizedDividendPtr fp k + 32) (len := 32 * dividendLength k)
      (by unfold dividendLength; omega)
    rw [max_eq_left hptr]
    exact haccess
  · rwa [hcopiedNat]

/-- The normalized-divisor allocation's active-word count covers its complete payload and every
earlier `u` word. -/
theorem barrettVWords_range
    (aw : UInt256) (fp k : Nat) (hkPos : 0 < k)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    normalizedDivisorPtr fp k + 32 + 32 * k ≤
        32 * (barrettVWords aw fp k).toNat ∧
      (barrettVWords aw fp k).toNat * 32 < UInt256.size := by
  have hcopied := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit
  have hv := MultiLimbOddConversionSemantic.newWordArrayWords_range
    (barrettCopiedWords aw fp k) (normalizedDivisorPtr fp k) k hkPos hcopied.2 hvFit
  simpa [barrettVWords, MultiLimbSchoolbookNormalization.vWords] using hv

/-- The zero-shift divisor `MCOPY` covers its complete destination and keeps the exact updated
active-word count representable. -/
theorem barrettZeroWords_range
    (aw : UInt256) (fp k divisorPtr : Nat) (hkPos : 0 < k)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
      UInt256.size) :
    normalizedDivisorPtr fp k + 32 + 32 * k ≤
        32 * (barrettZeroWords aw fp k divisorPtr).toNat ∧
      (barrettZeroWords aw fp k divisorPtr).toNat * 32 < UInt256.size := by
  have hv := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hmFit := MultiLimbMontgomeryCIOSSemantic.machineM_mul32_lt_size hv.2 hcopyFit
  have hmLt :
      MachineState.M (barrettVWords aw fp k).toNat
        (max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32)) (32 * k) <
        UInt256.size := by
    have hle := Nat.mul_le_mul_left
      (MachineState.M (barrettVWords aw fp k).toNat
        (max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32)) (32 * k))
      (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt (by simpa using hle) hmFit
  have hzeroNat : (barrettZeroWords aw fp k divisorPtr).toNat =
      MachineState.M (barrettVWords aw fp k).toNat
        (max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32)) (32 * k) := by
    unfold barrettZeroWords MultiLimbSchoolbookNormalizationFunction.zeroWords
      MultiLimbSchoolbookNormalization.shiftZeroWords
    change
      (UInt256.ofNat
        (MachineState.M (barrettVWords aw fp k).toNat
          (max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32))
          (32 * k))).toNat = _
    rw [UInt256.toNat_ofNat_of_lt hmLt]
  constructor
  · rw [hzeroNat]
    have haccess := MultiLimbMontgomeryCIOSSemantic.machineM_access_le
      (s := (barrettVWords aw fp k).toNat)
      (off := max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32))
      (len := 32 * k) (by omega)
    exact le_trans (by omega) haccess
  · rwa [hzeroNat]

/-- A copied normalized-dividend element has its ordinary array address whenever the generated
allocation fits. -/
theorem normalizedDividendArrayAddress_toNat (fp k i : Nat)
    (hi : i ≤ dividendLength k)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size) :
    (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) i).toNat =
      normalizedDividendPtr fp k + 32 * (i + 1) := by
  have hptrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have haddressFit :
      (UInt256.ofNat (normalizedDividendPtr fp k)).toNat + 32 * (i + 1) <
        UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hptrFit]
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  simpa [UInt256.toNat_ofNat_of_lt hptrFit] using
    MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit
      (UInt256.ofNat (normalizedDividendPtr fp k)) i haddressFit

/-- A normalized-divisor payload word has the ordinary fresh-array address under its allocation
fit condition. -/
theorem normalizedDivisorArrayAddress_toNat (fp k i : Nat)
    (hi : i ≤ k)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    (arrayAddress (UInt256.ofNat (normalizedDivisorPtr fp k)) i).toNat =
      normalizedDivisorPtr fp k + 32 * (i + 1) := by
  have hptrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have haddressFit :
      (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat + 32 * (i + 1) <
        UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hptrFit]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  simpa [UInt256.toNat_ofNat_of_lt hptrFit] using
    MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit
      (UInt256.ofNat (normalizedDivisorPtr fp k)) i haddressFit

/-- Ordinary element geometry for an arbitrary concrete source array pointer. -/
theorem concreteArrayAddress_toNat (ptr count i : Nat)
    (hi : i < count) (hfit : ptr + 32 * (count + 1) < UInt256.size) :
    (arrayAddress (UInt256.ofNat ptr) i).toNat = ptr + 32 * (i + 1) := by
  have hptrFit : ptr < UInt256.size := by omega
  have haddressFit : (UInt256.ofNat ptr).toNat + 32 * (i + 1) < UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hptrFit]
    omega
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  simpa [UInt256.toNat_ofNat_of_lt hptrFit] using
    MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat ptr) i haddressFit

/-- Every copied limb below the Barrett numerator's top limb is the concrete allocator zero. -/
theorem barrettCopiedMemory_low_word_zero
    (mem : ByteArray) (aw : UInt256) (fp k i : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hi : i < 2 * k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size) :
    arrayWord (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) i = ⟨0⟩ := by
  have hrange := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit
  have hsize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have haddress := normalizedDividendArrayAddress_toNat fp k i (by
    unfold dividendLength
    omega) huFit
  have hword :
      (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) i).toNat + 32 ≤
        (barrettCopiedMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold dividendLength
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    exact hrange.1
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [haddress, show normalizedDividendPtr fp k + 32 * (i + 1) =
    normalizedDividendPtr fp k + 32 + 32 * i by omega]
  rw [barrettCopiedMemory_read_word mem fp k i hk (by
    unfold dividendLength
    omega) hfp hmemSize hmemLe hgap hfirstFit]
  rw [show fp + 32 + 32 * i = (arrayAddress (UInt256.ofNat fp) i).toNat by
    rw [dividendArrayAddress_toNat fp k i (by omega) hfirstFit]
    omega]
  rw [barrettDivisionMemory_read_dividend mem fp k i hk (by omega) hfp hmemSize hmemLe
    hgap hfirstFit]
  exact storedDividendMemory_low_read_zero mem fp k i hk hi hfp hmemSize hmemLe hgap
    hfirstFit

/-- The copied Barrett numerator's most-significant limb is the concrete stored one. -/
theorem barrettCopiedMemory_high_word_one
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size) :
    arrayWord (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) (2 * k) = ⟨1⟩ := by
  have hrange := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit
  have hsize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have haddress := normalizedDividendArrayAddress_toNat fp k (2 * k) (by
    unfold dividendLength
    omega) huFit
  have hword :
      (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) (2 * k)).toNat + 32 ≤
        (barrettCopiedMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold dividendLength
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    exact hrange.1
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [haddress, show normalizedDividendPtr fp k + 32 * (2 * k + 1) =
    normalizedDividendPtr fp k + 32 + 32 * (2 * k) by omega]
  rw [barrettCopiedMemory_read_word mem fp k (2 * k) hk (by
    unfold dividendLength
    omega) hfp hmemSize hmemLe hgap hfirstFit]
  rw [show fp + 32 + 32 * (2 * k) =
    (arrayAddress (UInt256.ofNat fp) (2 * k)).toNat by
    rw [dividendArrayAddress_toNat fp k (2 * k) (by omega) hfirstFit]
    omega]
  rw [barrettDivisionMemory_read_dividend mem fp k (2 * k) hk (by omega) hfp hmemSize
    hmemLe hgap hfirstFit]
  exact storedDividendMemory_high_read_one mem fp k hk hmemSize hmemLe hgap hfirstFit

/-- The concrete numerator copied into Knuth's `u` array still denotes `B^(2*k)`. -/
theorem barrettCopiedDividend_value
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
          (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k)) =
      UInt256.size ^ (2 * k) := by
  have hlow :
      Modexp.wordLimbsToNat
          (arrayReadWords (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
            (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (2 * k)) = 0 := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
    intro i hi
    simpa only [Nat.zero_add] using
      barrettCopiedMemory_low_word_zero mem aw fp k i hk hkPos hi hfp hmemSize hmemLe
        hgap hawFit hfirstFit hsecondFit hquotientFit huFit
  have hhigh := barrettCopiedMemory_high_word_one mem aw fp k hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit
  unfold dividendLength
  rw [arrayReadWords_succ_append, Modexp.wordLimbsToNat_append,
    arrayReadWords_length, hlow]
  simp only [Nat.zero_add]
  rw [hhigh]
  simp only [Modexp.wordLimbsToNat,
    show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mul_zero, Nat.add_zero, Nat.mul_one]

/-- The normalized-divisor allocation preserves each low zero of the Barrett numerator under the
new active-word counter. -/
theorem barrettVMemory_low_u_word_zero
    (mem : ByteArray) (aw : UInt256) (fp k i : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hi : i < 2 * k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) i = ⟨0⟩ := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hsize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have haddress := normalizedDividendArrayAddress_toNat fp k i (by
    unfold dividendLength
    omega) huFit
  have hword :
      (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) i).toNat + 32 ≤
        (barrettVMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    unfold dividendLength
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettVMemory mem fp k) (barrettVWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    have hcoverage := hrange.1
    omega
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [haddress, show normalizedDividendPtr fp k + 32 * (i + 1) =
    normalizedDividendPtr fp k + 32 + 32 * i by omega]
  rw [barrettVMemory_read_u_word mem fp k i hk hkPos (by
    unfold dividendLength
    omega) hfp hmemSize hmemLe hgap hfirstFit]
  rw [barrettCopiedMemory_read_word mem fp k i hk (by
    unfold dividendLength
    omega) hfp hmemSize hmemLe hgap hfirstFit]
  rw [show fp + 32 + 32 * i = (arrayAddress (UInt256.ofNat fp) i).toNat by
    rw [dividendArrayAddress_toNat fp k i (by omega) hfirstFit]
    omega]
  rw [barrettDivisionMemory_read_dividend mem fp k i hk (by omega) hfp hmemSize hmemLe
    hgap hfirstFit]
  exact storedDividendMemory_low_read_zero mem fp k i hk hi hfp hmemSize hmemLe hgap
    hfirstFit

/-- The stored one remains the most-significant nonzero `u` limb after allocating `v`. -/
theorem barrettVMemory_high_u_word_one
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) (2 * k) = ⟨1⟩ := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hsize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have haddress := normalizedDividendArrayAddress_toNat fp k (2 * k) (by
    unfold dividendLength
    omega) huFit
  have hword :
      (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) (2 * k)).toNat + 32 ≤
        (barrettVMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    unfold dividendLength
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettVMemory mem fp k) (barrettVWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    have hcoverage := hrange.1
    omega
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [haddress, show normalizedDividendPtr fp k + 32 * (2 * k + 1) =
    normalizedDividendPtr fp k + 32 + 32 * (2 * k) by omega]
  rw [barrettVMemory_read_u_word mem fp k (2 * k) hk hkPos (by
    unfold dividendLength
    omega) hfp hmemSize hmemLe hgap hfirstFit]
  rw [barrettCopiedMemory_read_word mem fp k (2 * k) hk (by
    unfold dividendLength
    omega) hfp hmemSize hmemLe hgap hfirstFit]
  rw [show fp + 32 + 32 * (2 * k) =
    (arrayAddress (UInt256.ofNat fp) (2 * k)).toNat by
    rw [dividendArrayAddress_toNat fp k (2 * k) (by omega) hfirstFit]
    omega]
  rw [barrettDivisionMemory_read_dividend mem fp k (2 * k) hk (by omega) hfp hmemSize
    hmemLe hgap hfirstFit]
  exact storedDividendMemory_high_read_one mem fp k hk hmemSize hmemLe hgap hfirstFit

/-- The extra `u[m]` word is a guarded concrete zero after the `v` allocation. -/
theorem barrettVMemory_top_u_word_zero
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) (dividendLength k) = ⟨0⟩ := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hsize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have haddress := normalizedDividendArrayAddress_toNat fp k (dividendLength k)
    (by omega) huFit
  have hword :
      (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k))
        (dividendLength k)).toNat + 32 ≤ (barrettVMemory mem fp k).size := by
    rw [haddress, hsize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettVMemory mem fp k) (barrettVWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hsize]
    have hcoverage := hrange.1
    omega
  apply arrayWord_eq_of_covered_read _ _ _ _ _ hcovered hrange.2 hword
  rw [haddress, show normalizedDividendPtr fp k + 32 * (dividendLength k + 1) =
    normalizedDividendPtr fp k + 32 + 32 * dividendLength k by omega]
  exact barrettVMemory_top_u_read_zero mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit

/-- The full pre-normalization `m+1`-word dividend, including its concrete zero top limb, denotes
the original Barrett numerator. -/
theorem barrettVDividend_value
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) := by
  have hlow :
      Modexp.wordLimbsToNat
          (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
            (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (2 * k)) = 0 := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
    intro i hi
    simpa only [Nat.zero_add] using
      barrettVMemory_low_u_word_zero mem aw fp k i hk hkPos hi hfp hmemSize hmemLe
        hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hhigh := barrettVMemory_high_u_word_one mem aw fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have htop := barrettVMemory_top_u_word_zero mem aw fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hbase :
      Modexp.wordLimbsToNat
          (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
            (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k)) =
        UInt256.size ^ (2 * k) := by
    unfold dividendLength
    rw [arrayReadWords_succ_append, Modexp.wordLimbsToNat_append,
      arrayReadWords_length, hlow]
    simp only [Nat.zero_add]
    rw [hhigh]
    simp only [Modexp.wordLimbsToNat,
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mul_zero, Nat.add_zero, Nat.mul_one]
  rw [arrayReadWords_succ_append, Modexp.wordLimbsToNat_append,
    arrayReadWords_length, hbase]
  simp only [Nat.zero_add]
  rw [htop]
  simp [Modexp.wordLimbsToNat]

/-- The `m` words actually consumed by the in-place shift already denote the full Barrett
numerator; the separately allocated `u[m]` word is only the destination for outgoing carry. -/
theorem barrettVDividend_base_value
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k)) =
      UInt256.size ^ (2 * k) := by
  have hfull := barrettVDividend_value mem aw fp k hk hkPos hfp hmemSize hmemLe hgap
    hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have htop := barrettVMemory_top_u_word_zero mem aw fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  rw [arrayReadWords_succ_append, Modexp.wordLimbsToNat_append,
    arrayReadWords_length] at hfull
  simp only [Nat.zero_add] at hfull
  rw [htop] at hfull
  simpa [Modexp.wordLimbsToNat] using hfull

/-- Positive CLZ normalization of the concrete modulus into fresh `v` memory is exact
multiplication by the common shift factor. -/
theorem barrettPositiveDivisor_value
    (mem : ByteArray) (aw divisor top : UInt256) (fp k modulusNat : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k)
    (hshiftPos : 0 < (MultiLimbClz.clzResult top).n) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hsourceMem : ∀ j, j < k ->
      (arrayAddress divisor j).toNat + 32 ≤ (barrettVMemory mem fp k).size)
    (htop : arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      divisor (k - 1) = top)
    (hmodulus : Modexp.wordLimbsToNat
      (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
        divisor 0 k) = modulusNat) :
    let result := barrettPositiveDivisorResult mem aw fp k divisor top
    Modexp.wordLimbsToNat
        (arrayReadWords result.memory (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDivisorPtr fp k)) 0 k) =
      modulusNat * 2 ^ (MultiLimbClz.clzResult top).n := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hsize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hfrontier : ∀ j, j ≤ k ->
      (arrayAddress (UInt256.ofNat (normalizedDivisorPtr fp k)) j).toNat =
        (barrettVMemory mem fp k).size + 32 * j := by
    intro j hj
    rw [normalizedDivisorArrayAddress_toNat fp k j hj hvFit, hsize]
    omega
  have hactive : ∀ j, j < k ->
      (arrayAddress (UInt256.ofNat (normalizedDivisorPtr fp k)) j).toNat + 32 ≤
        32 * (barrettVWords aw fp k).toNat := by
    intro j hj
    rw [normalizedDivisorArrayAddress_toNat fp k j (by omega) hvFit]
    have hcoverage := hrange.1
    omega
  have hcarry :
      (MultiLimbSchoolbookNormalization.shiftDivisor (barrettVWords aw fp k) divisor
        (UInt256.ofNat (normalizedDivisorPtr fp k)) (MultiLimbClz.clzResult top).n
        0 k (barrettVMemory mem fp k) ⟨0⟩).carry = ⟨0⟩ := by
    have hzero :=
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_clz_finalCarry_eq_zero_frontier
        (barrettVWords aw fp k) divisor
        (UInt256.ofNat (normalizedDivisorPtr fp k)) top (k - 1)
        (barrettVMemory mem fp k) hshiftPos hrange.2
        (by
          intro j hj
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
            hfrontier j (by omega))
        (by
          intro j hj
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
            hactive j (by omega))
        (by
          intro j hj
          simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
            hsourceMem j (by omega))
        htop
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hzero
  have hnormalized :=
    MultiLimbSchoolbookNormalizationSemantic.normalizedDivisorArray_toNat_frontier
      (barrettVWords aw fp k) divisor (UInt256.ofNat (normalizedDivisorPtr fp k))
      (MultiLimbClz.clzResult top).n k (barrettVMemory mem fp k) hshiftPos
      (by have hn := MultiLimbClz.clzResult_n_le top; omega) hrange.2
      hfrontier hactive hsourceMem hcarry
  unfold barrettPositiveDivisorResult
    MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult
  rw [hmodulus] at hnormalized
  exact hnormalized

/-- Positive in-place normalization of the concrete `m+1`-word `u` array is exact multiplication
of the Barrett numerator by the same CLZ shift factor. -/
theorem barrettPositiveDividend_value
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k)
    (hshiftPos : 0 < (MultiLimbClz.clzResult top).n) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettPositiveMemory mem aw fp k divisor top)
          (barrettVWords aw fp k) (UInt256.ofNat (normalizedDividendPtr fp k))
          0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) * 2 ^ (MultiLimbClz.clzResult top).n := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hvFrontier : ∀ j, j ≤ k ->
      (arrayAddress v j).toNat = (barrettVMemory mem fp k).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k j hj hvFit, hvSize]
    omega
  have hvActive : ∀ j, j < k ->
      (arrayAddress v j).toNat + 32 ≤ 32 * (barrettVWords aw fp k).toNat := by
    intro j hj
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k j (by omega) hvFit]
    have hcoverage := hrange.1
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (barrettVMemory mem fp k).size + 32 * k := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (barrettVWords aw fp k) divisor v shift 0 k (barrettVMemory mem fp k) ⟨0⟩
      (by simpa only [Nat.zero_add] using hvFrontier)
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using hsize
  have huReadMem : ∀ i, i < dividendLength k + 1 ->
      (arrayAddress u i).toNat + 32 ≤ (barrettVMemory mem fp k).size := by
    intro i hi
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k i (by omega) huFit, hvSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huPreserved :
      arrayReadWords divisorResult.memory (barrettVWords aw fp k) u 0
          (dividendLength k) =
        arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k) u 0
          (dividendLength k) := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_eq_of_words
    intro i hi
    simpa only [Nat.zero_add, divisorResult] using
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_preserves_arrayWord_below_frontier
        (barrettVWords aw fp k) u divisor v shift i 0 k
        (barrettVMemory mem fp k) ⟨0⟩ hrange.2
        (by simpa only [Nat.zero_add] using hvFrontier)
        (by simpa only [Nat.zero_add] using hvActive)
        (huReadMem i (by omega))
  have huValue := barrettVDividend_base_value mem aw fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize]
    exact le_trans (huReadMem j (by omega)) (by omega)
  have huActive : ∀ j, j < dividendLength k + 1 ->
      (arrayAddress u j).toNat + 32 ≤ 32 * (barrettVWords aw fp k).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    have hcoverage := hrange.1
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize at hcoverage
    omega
  have huOrdered : ∀ i j, i < j -> j < dividendLength k ->
      (arrayAddress u i).toNat + 32 ≤ (arrayAddress u j).toNat := by
    intro i j hij hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k i (by omega) huFit,
      normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    omega
  have htopWrite :
      let result := MultiLimbSchoolbookNormalization.shiftDivisor
        (barrettVWords aw fp k) u u shift 0 (dividendLength k)
        divisorResult.memory ⟨0⟩
      (arrayAddress u (dividendLength k)).toNat + 32 ≤ result.memory.size := by
    dsimp only
    have hshiftSize :=
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
        (barrettVWords aw fp k) u u shift 0 (dividendLength k)
        divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    rw [hshiftSize, hdivisorResultSize]
    exact le_trans (huReadMem (dividendLength k) (by omega)) (by omega)
  have htopOrdered : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ (arrayAddress u (dividendLength k)).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit,
      normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    omega
  have hnormalized :=
    MultiLimbSchoolbookNormalizationSemantic.normalizedDividendArray_toNat
      (barrettVWords aw fp k) u shift (dividendLength k) divisorResult.memory
      hshiftPos (by have hn := MultiLimbClz.clzResult_n_le top; dsimp only [shift]; omega)
      hrange.2 (by simpa only [Nat.zero_add] using huWrite)
      (by
        intro j hj
        exact huActive j (by omega))
      huOrdered htopWrite (huActive (dividendLength k) (by omega)) htopOrdered
  rw [huPreserved, huValue] at hnormalized
  unfold barrettPositiveMemory
    MultiLimbSchoolbookNormalizationFunction.positiveMemory
    MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
  simpa [divisorResult, barrettPositiveDivisorResult, u, v, shift,
    MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hnormalized

/-- The subsequent in-place dividend shift and top-carry store are below `v`, so the final
positive-normalization memory still contains the exact shifted modulus. -/
theorem barrettPositiveDivisor_final_value
    (mem : ByteArray) (aw divisor top : UInt256) (fp k modulusNat : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k)
    (hshiftPos : 0 < (MultiLimbClz.clzResult top).n) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hsourceMem : ∀ j, j < k ->
      (arrayAddress divisor j).toNat + 32 ≤ (barrettVMemory mem fp k).size)
    (htop : arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      divisor (k - 1) = top)
    (hmodulus : Modexp.wordLimbsToNat
      (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
        divisor 0 k) = modulusNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettPositiveMemory mem aw fp k divisor top)
          (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k)) 0 k) =
      modulusNat * 2 ^ (MultiLimbClz.clzResult top).n := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor v u k
      (dividendLength k) shift
  have hdivisor := barrettPositiveDivisor_value mem aw divisor top fp k modulusNat hk hkPos
    hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
    hsourceMem htop hmodulus
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hvFrontier : ∀ j, j ≤ k ->
      (arrayAddress v j).toNat = (barrettVMemory mem fp k).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k j hj hvFit, hvSize]
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (barrettVMemory mem fp k).size + 32 * k := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (barrettVWords aw fp k) divisor v shift 0 k (barrettVMemory mem fp k) ⟨0⟩
      (by simpa only [Nat.zero_add] using hvFrontier)
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using hsize
  have huReadMem : ∀ i, i < dividendLength k + 1 ->
      (arrayAddress u i).toNat + 32 ≤ (barrettVMemory mem fp k).size := by
    intro i hi
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k i (by omega) huFit, hvSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize]
    exact le_trans (huReadMem j (by omega)) (by omega)
  have huBelowV : ∀ i j, i < k -> j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ (arrayAddress v i).toNat := by
    intro i j hi hj
    dsimp only [u, v]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit,
      normalizedDivisorArrayAddress_toNat fp k i (by omega) hvFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hshiftPreserved :
      arrayReadWords dividendResult.memory (barrettVWords aw fp k) v 0 k =
        arrayReadWords divisorResult.memory (barrettVWords aw fp k) v 0 k := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_eq_of_words
    intro i hi
    simpa only [Nat.zero_add, dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_preserves_arrayWord_above
        (barrettVWords aw fp k) v u u shift i 0 (dividendLength k)
        divisorResult.memory ⟨0⟩ (by
          intro j hj
          simpa only [Nat.zero_add] using huWrite j hj) (by
          intro j hj
          simpa only [Nat.zero_add] using huBelowV i j hi hj)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k) divisorResult.memory ⟨0⟩
      (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  have htopWrite : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize]
    exact le_trans (huReadMem (dividendLength k) (by omega)) (by omega)
  have htopBelowV : ∀ i, i < k ->
      (arrayAddress u (dividendLength k)).toNat + 32 ≤ (arrayAddress v i).toNat := by
    intro i hi
    dsimp only [u, v]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit,
      normalizedDivisorArrayAddress_toNat fp k i (by omega) hvFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopPreserved :
      arrayReadWords
          (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u
            (dividendLength k) dividendResult.carry)
          (barrettVWords aw fp k) v 0 k =
        arrayReadWords dividendResult.memory (barrettVWords aw fp k) v 0 k := by
    simpa only [MultiLimbSchoolbookNormalization.storeDividendTopCarry, Nat.zero_add] using
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_storeValue_above
        dividendResult.memory (barrettVWords aw fp k) v u dividendResult.carry 0 k
        (dividendLength k) htopWrite (by
          intro i hi
          simpa only [Nat.zero_add] using htopBelowV i hi)
  change Modexp.wordLimbsToNat
      (arrayReadWords
        (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u
          (dividendLength k) dividendResult.carry)
        (barrettVWords aw fp k) v 0 k) = _
  rw [htopPreserved, hshiftPreserved]
  simpa [divisorResult, v] using hdivisor

/-- The zero-CLZ `MCOPY` makes the normalized `v` slice exactly the original concrete modulus. -/
theorem barrettZeroDivisor_value
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr modulusNat : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
      UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size)
    (hdivisorFit : divisorPtr + 32 * (k + 1) < UInt256.size)
    (hmodulus : Modexp.wordLimbsToNat
      (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettZeroMemory mem fp k divisorPtr)
          (barrettZeroWords aw fp k divisorPtr)
          (UInt256.ofNat (normalizedDivisorPtr fp k)) 0 k) = modulusNat := by
  have hvRange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hzRange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hvCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettVMemory mem fp k) (barrettVWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hvSize]
    have hcoverage := hvRange.1
    omega
  have hzCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hzSize]
    exact hzRange.1
  have hslices :
      arrayReadWords (barrettZeroMemory mem fp k divisorPtr)
          (barrettZeroWords aw fp k divisorPtr)
          (UInt256.ofNat (normalizedDivisorPtr fp k)) 0 k =
        arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
          (UInt256.ofNat divisorPtr) 0 k := by
    apply arrayReadWords_eq_of_words_twoAw
    intro i hi
    simp only [Nat.zero_add]
    have hleftAddress := normalizedDivisorArrayAddress_toNat fp k i (by omega) hvFit
    have hrightAddress := concreteArrayAddress_toNat divisorPtr k i hi hdivisorFit
    apply arrayWord_eq_of_covered_reads _ _ _ _ _ _ _ _ hzCovered hvCovered
      hzRange.2 hvRange.2
    · rw [hleftAddress, hzSize]
      omega
    · rw [hrightAddress]
      omega
    · rw [hleftAddress, hrightAddress]
      rw [show normalizedDivisorPtr fp k + 32 * (i + 1) =
        normalizedDivisorPtr fp k + 32 + 32 * i by omega]
      rw [show divisorPtr + 32 * (i + 1) = divisorPtr + 32 + 32 * i by omega]
      exact barrettZeroMemory_read_v_word mem fp k divisorPtr i hk hkPos hi hfp
        hmemSize hmemLe hgap hfirstFit hsource
  rw [hslices, hmodulus]

/-- The zero-CLZ divisor copy leaves the complete `m+1`-word `u` value unchanged. -/
theorem barrettZeroDividend_value
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
      UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    Modexp.wordLimbsToNat
        (arrayReadWords (barrettZeroMemory mem fp k divisorPtr)
          (barrettZeroWords aw fp k divisorPtr)
          (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) := by
  have hvRange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hzRange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hvCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettVMemory mem fp k) (barrettVWords aw fp k) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hvSize]
    have hcoverage := hvRange.1
    omega
  have hzCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr) := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [hzSize]
    exact hzRange.1
  have hslices :
      arrayReadWords (barrettZeroMemory mem fp k divisorPtr)
          (barrettZeroWords aw fp k divisorPtr)
          (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k + 1) =
        arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDividendPtr fp k)) 0 (dividendLength k + 1) := by
    apply arrayReadWords_eq_of_words_twoAw
    intro i hi
    simp only [Nat.zero_add]
    have haddress := normalizedDividendArrayAddress_toNat fp k i (by omega) huFit
    apply arrayWord_eq_of_covered_reads _ _ _ _ _ _ _ _ hzCovered hvCovered
      hzRange.2 hvRange.2
    · rw [haddress, hzSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [haddress, hvSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [haddress]
      rw [show normalizedDividendPtr fp k + 32 * (i + 1) =
        normalizedDividendPtr fp k + 32 + 32 * i by omega]
      exact barrettZeroMemory_read_u_word mem fp k divisorPtr i hk hkPos (by omega) hfp
        hmemSize hmemLe hgap hfirstFit hsource
  rw [hslices]
  exact barrettVDividend_value mem aw fp k hk hkPos hfp hmemSize hmemLe hgap hawFit
    hfirstFit hsecondFit hquotientFit huFit hvFit

/-- The arbitrary Knuth semantic chain computes the Barrett constant once its two normalized
arrays are connected to the concrete numerator and modulus by their common shift factor. -/
theorem barrettConstantQuotient_eq
    {k shiftNat modulusNat : Nat}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {steps gas : Nat}
    (h : MultiLimbSchoolbookOuterComplete.SemanticContinuations
      k (dividendLength k + 1) (quotientCount k) u shift ret rem v quotient vTop
      normalizationMarker vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas)
    (hinputsLength : inputs.length = quotientCount k)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount k -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (inputs.length + k)) =
      UInt256.size ^ (2 * k) * 2 ^ shiftNat)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 k) =
      modulusNat * 2 ^ shiftNat) :
    MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
        (MultiLimbSchoolbookOuterComplete.quotientReadNats
          finalMem finalAw quotient (quotientCount k)) =
      UInt256.size ^ (2 * k) / modulusNat := by
  have hquotient :=
    MultiLimbSchoolbookCompleteSemantic.positiveShift_quotient_eq_original_div
      h hnonempty hnormalized hquotBelowU hdividend hdivisor
  rwa [hinputsLength] at hquotient

/-- The positive-CLZ concrete normalization state and arbitrary quotient loop produce the exact
Barrett constant. -/
theorem barrettPositiveConstantQuotient_eq
    {mem : ByteArray} {aw divisor top ret rem quotient vTop normalizationMarker : UInt256}
    {fp k modulusNat : Nat} {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {finalMem : ByteArray} {finalAw : UInt256} {steps gas : Nat}
    (hk : k ≤ 32) (hkPos : 0 < k)
    (hshiftPos : 0 < (MultiLimbClz.clzResult top).n) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hsourceMem : ∀ j, j < k ->
      (arrayAddress divisor j).toNat + 32 ≤ (barrettVMemory mem fp k).size)
    (htop : arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      divisor (k - 1) = top)
    (hmodulus : Modexp.wordLimbsToNat
      (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
        divisor 0 k) = modulusNat)
    (hsemantic : MultiLimbSchoolbookOuterComplete.SemanticContinuations
      k (dividendLength k + 1) (quotientCount k)
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (MultiLimbClz.clzResult top).n) ret rem
      (UInt256.ofNat (normalizedDivisorPtr fp k)) quotient vTop normalizationMarker
      vRest vSecond ⟨0, 0⟩ inputs
      (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
      finalMem finalAw steps gas)
    (hinputsLength : inputs.length = quotientCount k)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount k -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) sourceIndex).toNat) :
    MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
        (MultiLimbSchoolbookOuterComplete.quotientReadNats
          finalMem finalAw quotient (quotientCount k)) =
      UInt256.size ^ (2 * k) / modulusNat := by
  have hdividend := barrettPositiveDividend_value mem aw divisor top fp k hk hkPos
    hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hdivisor := barrettPositiveDivisor_final_value mem aw divisor top fp k modulusNat hk hkPos
    hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
    hsourceMem htop hmodulus
  apply barrettConstantQuotient_eq
    (shiftNat := (MultiLimbClz.clzResult top).n) (modulusNat := modulusNat)
    hsemantic hinputsLength hnonempty hnormalized hquotBelowU
  · have hlength : inputs.length + k = dividendLength k + 1 := by
      rw [hinputsLength, quotientCount_eq]
      unfold dividendLength
      omega
    simpa only [hlength] using hdividend
  · exact hdivisor

/-- The zero-CLZ concrete copy state and arbitrary quotient loop produce the same exact Barrett
constant. -/
theorem barrettZeroConstantQuotient_eq
    {mem : ByteArray} {aw ret rem quotient vTop normalizationMarker : UInt256}
    {fp k divisorPtr modulusNat : Nat} {vRest : List UInt256} {vSecond : UInt256}
    {inputs : List Nat} {finalMem : ByteArray} {finalAw : UInt256} {steps gas : Nat}
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
      UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size)
    (hdivisorFit : divisorPtr + 32 * (k + 1) < UInt256.size)
    (hmodulus : Modexp.wordLimbsToNat
      (arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (hsemantic : MultiLimbSchoolbookOuterComplete.SemanticContinuations
      k (dividendLength k + 1) (quotientCount k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) ⟨0⟩ ret rem
      (UInt256.ofNat (normalizedDivisorPtr fp k)) quotient vTop normalizationMarker
      vRest vSecond ⟨0, 0⟩ inputs (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr) finalMem finalAw steps gas)
    (hinputsLength : inputs.length = quotientCount k)
    (hnonempty : inputs ≠ [])
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hquotBelowU : ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount k -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress (UInt256.ofNat (normalizedDividendPtr fp k)) sourceIndex).toNat) :
    MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
        (MultiLimbSchoolbookOuterComplete.quotientReadNats
          finalMem finalAw quotient (quotientCount k)) =
      UInt256.size ^ (2 * k) / modulusNat := by
  have hdividend := barrettZeroDividend_value mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hdivisor := barrettZeroDivisor_value mem aw fp k divisorPtr modulusNat hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit
    hsource hdivisorFit hmodulus
  apply barrettConstantQuotient_eq (shiftNat := 0) (modulusNat := modulusNat)
    hsemantic hinputsLength hnonempty hnormalized hquotBelowU
  · have hlength : inputs.length + k = dividendLength k + 1 := by
      rw [hinputsLength, quotientCount_eq]
      unfold dividendLength
      omega
    simpa only [hlength, pow_zero, Nat.mul_one] using hdividend
  · simpa only [pow_zero, Nat.mul_one] using hdivisor

end Modexp.MultiLimbBarrettConstantSemantic
