import Examples.Precompiles.Modexp.MultiLimbSchoolbookNormalizationSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulMemorySemantic

/-!
# Concrete schoolbook-array observation

Generated schoolbook arithmetic observes Solidity arrays through guarded EVM word loads.  These
lemmas connect that observer to the shared byte-array limb model whenever the concrete memory is
covered by the active-word counter.  Keeping this bridge independent of Barrett lets conversion,
division, and multiplication proofs share the same representation boundary.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbArrayReadSemantic

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Concrete guarded layout facts shared by the trim, normalization, and copy loops. -/
structure Layout (mem : ByteArray) (aw : UInt256) (ptr count : Nat) : Prop where
  header : MultiLimbSchoolbookNormalization.arrayHeader mem aw (UInt256.ofNat ptr) =
    UInt256.ofNat count
  headerAw : MultiLimbSchoolbookNormalization.arrayAfterHeader aw (UInt256.ofNat ptr) = aw
  wordAw : ∀ i, i < count →
    MultiLimbSchoolbookNormalization.arrayAfterWord aw (UInt256.ofNat ptr) i = aw

/-- Ordinary covered Solidity-array geometry supplies all guarded layout facts. -/
theorem layout_of_geometry
    (mem : ByteArray) (aw : UInt256) (ptr count : Nat)
    (hptrFit : ptr + 32 * (count + 1) < UInt256.size)
    (hmem : ptr + 32 ≤ mem.size)
    (hactive : ptr + 32 + 32 * count ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding ptr 32 =
      UInt256.toByteArray (UInt256.ofNat count)) :
    Layout mem aw ptr count := by
  have hptr : ptr < UInt256.size := by omega
  have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hnotActive : ¬ UInt256.ofNat ptr ≥ aw * ⟨32⟩ := by
    intro hge
    have hgeNat : (aw * ⟨32⟩).toNat ≤ (UInt256.ofNat ptr).toNat := hge
    rw [hawMul, UInt256.toNat_ofNat_of_lt hptr] at hgeNat
    omega
  have hheader :
      MultiLimbSchoolbookNormalization.arrayHeader mem aw (UInt256.ofNat ptr) =
        UInt256.ofNat count := by
    unfold MultiLimbSchoolbookNormalization.arrayHeader
      MultiLimbSchoolbookSingle.arrayHeader MultiLimbSchoolbookShort.arrayHeader
      MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
    rw [if_neg (not_or.mpr ⟨by rw [UInt256.toNat_ofNat_of_lt hptr]; omega,
      hnotActive⟩), UInt256.toNat_ofNat_of_lt hptr, hread,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
  have hheaderAw :
      MultiLimbSchoolbookNormalization.arrayAfterHeader aw (UInt256.ofNat ptr) = aw := by
    unfold MultiLimbSchoolbookNormalization.arrayAfterHeader
      MultiLimbSchoolbookSingle.arrayAfterHeader MultiLimbSchoolbookShort.arrayAfterHeader
    apply MultiLimbOddCompare.afterHeader_eq_of_access
    rw [UInt256.toNat_ofNat_of_lt hptr]
    omega
  refine ⟨hheader, hheaderAw, ?_⟩
  intro i hi
  have haddress :
      (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) i).toNat =
        ptr + 32 * (i + 1) := by
    unfold MultiLimbSchoolbookNormalization.arrayAddress
      MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt hptr] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat ptr) i (by
        simpa [UInt256.toNat_ofNat_of_lt hptr] using
          (show ptr + 32 * (i + 1) < UInt256.size by omega))
  unfold MultiLimbSchoolbookNormalization.arrayAfterWord
    MultiLimbSchoolbookSingle.arrayAfterWord MultiLimbSchoolbookShort.arrayAfterWord
  apply MultiLimbOddCompare.afterHeader_eq_of_access
  change (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) i).toNat =
    ptr + 32 * (i + 1) at haddress
  rw [haddress]
  omega

/-- Equal concrete padded reads at an in-bounds, active array element give equal guarded words,
even when allocation changed the memory and active-word counter. -/
theorem arrayWord_eq_of_readWithPadding_eq
    (left right : ByteArray) (leftAw rightAw : UInt256) (ptr index : Nat)
    (hfit : ptr + 32 * (index + 1) < UInt256.size)
    (hleftMem : ptr + 32 * (index + 1) + 32 ≤ left.size)
    (hrightMem : ptr + 32 * (index + 1) + 32 ≤ right.size)
    (hleftActive : ptr + 32 * (index + 1) + 32 ≤ 32 * leftAw.toNat)
    (hrightActive : ptr + 32 * (index + 1) + 32 ≤ 32 * rightAw.toNat)
    (hleftAwFit : leftAw.toNat * 32 < UInt256.size)
    (hrightAwFit : rightAw.toNat * 32 < UInt256.size)
    (hread : left.readWithPadding (ptr + 32 * (index + 1)) 32 =
      right.readWithPadding (ptr + 32 * (index + 1)) 32) :
    MultiLimbSchoolbookNormalization.arrayWord left leftAw (UInt256.ofNat ptr) index =
      MultiLimbSchoolbookNormalization.arrayWord right rightAw (UInt256.ofNat ptr) index := by
  have hptr : ptr < UInt256.size := by omega
  have haddress :
      (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index).toNat =
        ptr + 32 * (index + 1) := by
    unfold MultiLimbSchoolbookNormalization.arrayAddress
      MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt hptr] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat ptr) index (by
        simpa [UInt256.toNat_ofNat_of_lt hptr] using hfit)
  have leftMul : (leftAw * (⟨32⟩ : UInt256)).toNat = leftAw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := leftAw) (b := (⟨32⟩ : UInt256)) hleftAwFit
  have rightMul : (rightAw * (⟨32⟩ : UInt256)).toNat = rightAw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := rightAw) (b := (⟨32⟩ : UInt256)) hrightAwFit
  have hleftGuard : ¬
      MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index ≥
        leftAw * ⟨32⟩ := by
    intro hge
    have hnat : (leftAw * ⟨32⟩).toNat ≤
        (MultiLimbSchoolbookNormalization.arrayAddress
          (UInt256.ofNat ptr) index).toNat := hge
    rw [haddress, leftMul] at hnat
    omega
  have hrightGuard : ¬
    MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index ≥
        rightAw * ⟨32⟩ := by
    intro hge
    have hnat : (rightAw * ⟨32⟩).toNat ≤
        (MultiLimbSchoolbookNormalization.arrayAddress
          (UInt256.ofNat ptr) index).toNat := hge
    rw [haddress, rightMul] at hnat
    omega
  have haddressShort :
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) index).toNat =
        ptr + 32 * (index + 1) := haddress
  have hleftGuardShort : ¬
      MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) index ≥
        leftAw * ⟨32⟩ := hleftGuard
  have hrightGuardShort : ¬
      MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) index ≥
        rightAw * ⟨32⟩ := hrightGuard
  unfold MultiLimbSchoolbookNormalization.arrayWord
    MultiLimbSchoolbookSingle.arrayWord MultiLimbSchoolbookShort.arrayWord
    MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by rw [haddressShort]; omega, hleftGuardShort⟩),
    if_neg (not_or.mpr ⟨by rw [haddressShort]; omega, hrightGuardShort⟩),
    haddressShort, hread]

/-- Different covered Solidity-array locations denote the same guarded word when their concrete
32-byte reads agree.  This is the observer bridge used for deployed `MCOPY` operations. -/
theorem arrayWord_eq_of_distinct_readWithPadding_eq
    (left right : ByteArray) (leftAw rightAw : UInt256)
    (leftPtr rightPtr index : Nat)
    (hleftFit : leftPtr + 32 * (index + 1) < UInt256.size)
    (hrightFit : rightPtr + 32 * (index + 1) < UInt256.size)
    (hleftMem : leftPtr + 32 * (index + 1) + 32 ≤ left.size)
    (hrightMem : rightPtr + 32 * (index + 1) + 32 ≤ right.size)
    (hleftActive : leftPtr + 32 * (index + 1) + 32 ≤ 32 * leftAw.toNat)
    (hrightActive : rightPtr + 32 * (index + 1) + 32 ≤ 32 * rightAw.toNat)
    (hleftAwFit : leftAw.toNat * 32 < UInt256.size)
    (hrightAwFit : rightAw.toNat * 32 < UInt256.size)
    (hread : left.readWithPadding (leftPtr + 32 * (index + 1)) 32 =
      right.readWithPadding (rightPtr + 32 * (index + 1)) 32) :
    MultiLimbSchoolbookNormalization.arrayWord left leftAw (UInt256.ofNat leftPtr) index =
      MultiLimbSchoolbookNormalization.arrayWord right rightAw
        (UInt256.ofNat rightPtr) index := by
  have hleftPtr : leftPtr < UInt256.size := by omega
  have hrightPtr : rightPtr < UInt256.size := by omega
  have hleftAddress :
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat leftPtr) index).toNat = leftPtr + 32 * (index + 1) := by
    unfold MultiLimbSchoolbookNormalization.arrayAddress
      MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt hleftPtr] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit
        (UInt256.ofNat leftPtr) index (by
          simpa [UInt256.toNat_ofNat_of_lt hleftPtr] using hleftFit)
  have hrightAddress :
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat rightPtr) index).toNat = rightPtr + 32 * (index + 1) := by
    unfold MultiLimbSchoolbookNormalization.arrayAddress
      MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt hrightPtr] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit
        (UInt256.ofNat rightPtr) index (by
          simpa [UInt256.toNat_ofNat_of_lt hrightPtr] using hrightFit)
  have hleftMul : (leftAw * (⟨32⟩ : UInt256)).toNat = leftAw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := leftAw) (b := (⟨32⟩ : UInt256)) hleftAwFit
  have hrightMul : (rightAw * (⟨32⟩ : UInt256)).toNat = rightAw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := rightAw) (b := (⟨32⟩ : UInt256)) hrightAwFit
  have hleftGuard : ¬
      MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat leftPtr) index ≥
        leftAw * ⟨32⟩ := by
    intro hge
    have hnat : (leftAw * ⟨32⟩).toNat ≤
        (MultiLimbSchoolbookNormalization.arrayAddress
          (UInt256.ofNat leftPtr) index).toNat := hge
    rw [hleftAddress, hleftMul] at hnat
    omega
  have hrightGuard : ¬
      MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat rightPtr) index ≥
        rightAw * ⟨32⟩ := by
    intro hge
    have hnat : (rightAw * ⟨32⟩).toNat ≤
        (MultiLimbSchoolbookNormalization.arrayAddress
          (UInt256.ofNat rightPtr) index).toNat := hge
    rw [hrightAddress, hrightMul] at hnat
    omega
  have hleftAddressShort :
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat leftPtr) index).toNat =
        leftPtr + 32 * (index + 1) := hleftAddress
  have hrightAddressShort :
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat rightPtr) index).toNat =
        rightPtr + 32 * (index + 1) := hrightAddress
  have hleftGuardShort : ¬
      MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat leftPtr) index ≥
        leftAw * ⟨32⟩ := hleftGuard
  have hrightGuardShort : ¬
      MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat rightPtr) index ≥
        rightAw * ⟨32⟩ := hrightGuard
  unfold MultiLimbSchoolbookNormalization.arrayWord
    MultiLimbSchoolbookSingle.arrayWord MultiLimbSchoolbookShort.arrayWord
    MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by rw [hleftAddressShort]; omega, hleftGuardShort⟩),
    if_neg (not_or.mpr ⟨by rw [hrightAddressShort]; omega, hrightGuardShort⟩),
    hleftAddressShort, hrightAddressShort, hread]

/-- Pointwise guarded-word equality lifts to finite slices even when allocation changed the
active-word counter. -/
theorem arrayReadWords_eq_of_words
    (left right : ByteArray) (leftAw rightAw leftArray rightArray : UInt256)
    (start count : Nat)
    (hwords : ∀ i, i < count →
      MultiLimbSchoolbookNormalization.arrayWord left leftAw leftArray (start + i) =
        MultiLimbSchoolbookNormalization.arrayWord right rightAw rightArray (start + i)) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        left leftAw leftArray start count =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        right rightAw rightArray start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords]
      have hhead := hwords 0 (by omega)
      simp only [Nat.add_zero] at hhead
      rw [hhead]
      apply congrArg (fun words => _ :: words)
      apply ih
      intro i hi
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hwords (i + 1) (by omega)

/-- Equality of finite guarded-array observations can be projected back to any covered word.
This induction-based form avoids dependent `List.getElem` transports when the two observations
have propositionally, rather than definitionally, equal list lengths. -/
theorem arrayWord_eq_of_arrayReadWords_eq
    (left right : ByteArray) (leftAw rightAw leftArray rightArray : UInt256)
    (start count i : Nat) (hi : i < count)
    (hwords : MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        left leftAw leftArray start count =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        right rightAw rightArray start count) :
    MultiLimbSchoolbookNormalization.arrayWord left leftAw leftArray (start + i) =
      MultiLimbSchoolbookNormalization.arrayWord right rightAw rightArray (start + i) := by
  induction count generalizing start i with
  | zero => omega
  | succ count ih =>
      simp only [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords] at hwords
      have hparts := List.cons.inj hwords
      cases i with
      | zero =>
          simpa only [Nat.add_zero] using hparts.1
      | succ i =>
          have htail := ih (start := start + 1) (i := i) (by omega) hparts.2
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using htail

/-- Element lookup in the finite guarded array observer. -/
theorem arrayReadWords_getElem
    (mem : ByteArray) (aw array : UInt256) (index count i : Nat)
    (hi : i < count) :
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw array index count)[i]'(by simpa using hi) =
      MultiLimbSchoolbookNormalization.arrayWord mem aw array (index + i) := by
  induction count generalizing index i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords,
            List.getElem_cons_succ]
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using
            ih (index + 1) i (by omega)

/-- A guarded schoolbook-array observation of a covered concrete word is the corresponding
byte-array word. -/
theorem arrayWord_toNat_eq_memoryWordNat
    (mem : ByteArray) (aw : UInt256) (ptr index : Nat)
    (hfit : ptr + 32 * (index + 1) < UInt256.size)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    (MultiLimbSchoolbookNormalization.arrayWord
      mem aw (UInt256.ofNat ptr) index).toNat =
      MultiLimbMemoryModel.memoryWordNat mem (ptr + 32 + 32 * index) := by
  have hptr : ptr < UInt256.size := by omega
  have haddress :
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat ptr) index).toNat = ptr + 32 * (index + 1) := by
    unfold MultiLimbSchoolbookNormalization.arrayAddress
      MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt hptr] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit
        (UInt256.ofNat ptr) index (by simpa [UInt256.toNat_ofNat_of_lt hptr] using hfit)
  have hread := MultiLimbSchoolbookMulTrace.readWord_eq_memoryWordOf_covered_padded
    mem aw
      (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index)
      hcovered hawFit
  unfold MultiLimbSchoolbookNormalization.arrayWord
    MultiLimbSchoolbookSingle.arrayWord MultiLimbSchoolbookShort.arrayWord
    MultiLimbOddCompare.loadedWord
  change (MultiLimbDivisionTrace.readWord mem aw
    (MultiLimbSchoolbookNormalization.arrayAddress
      (UInt256.ofNat ptr) index)).toNat = _
  have hnat := congrArg UInt256.toNat hread
  rw [UInt256.toNat_ofNat_of_lt
    (MultiLimbMontgomeryCIOSSemantic.memoryWordNat_lt_size mem _), haddress] at hnat
  have hoff : ptr + 32 * (index + 1) = ptr + 32 + 32 * index := by omega
  rw [← hoff]
  exact hnat

/-- Consecutive generated array loads expose exactly the concrete little-endian payload. -/
theorem arrayReadWords_map_toNat_eq_memoryLimbs
    (mem : ByteArray) (aw : UInt256) (ptr count : Nat)
    (hfit : ptr + 32 * (count + 1) < UInt256.size)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw (UInt256.ofNat ptr) 0 count).map UInt256.toNat =
      MultiLimbMemoryModel.memoryLimbs mem ptr count := by
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    have hi : i < count := by
      simpa using hiLeft
    rw [List.getElem_map,
      arrayReadWords_getElem mem aw (UInt256.ofNat ptr) 0 count i hi]
    simp only [MultiLimbMemoryModel.memoryLimbs, List.getElem_ofFn, Nat.zero_add]
    apply arrayWord_toNat_eq_memoryWordNat
    · omega
    · exact hcovered
    · exact hawFit

/-- The generated schoolbook observer and the shared pure limb observer assign the same value. -/
theorem arrayReadWords_value_eq_memoryLimbs
    (mem : ByteArray) (aw : UInt256) (ptr count : Nat)
    (hfit : ptr + 32 * (count + 1) < UInt256.size)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat ptr) 0 count) =
      limbsToNat (MultiLimbMemoryModel.memoryLimbs mem ptr count) := by
  rw [wordLimbsToNat_eq_limbsToNat,
    arrayReadWords_map_toNat_eq_memoryLimbs mem aw ptr count
      hfit hcovered hawFit]

/-- The shared consecutive-word observer has the same natural limbs as the finite memory model. -/
theorem memoryWordsFrom_map_toNat_eq_memoryLimbs
    (mem : ByteArray) (ptr count : Nat) :
    (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (ptr + 32) count).map
        UInt256.toNat =
      MultiLimbMemoryModel.memoryLimbs mem ptr count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append,
        List.map_append, MultiLimbMemoryModel.memoryLimbs_succ, ih]
      simp only [List.map_singleton]
      rw [UInt256.toNat_ofNat_of_lt
        (MultiLimbMontgomeryCIOSSemantic.memoryWordNat_lt_size mem
          (ptr + 32 + 32 * count))]

/-- A covered generated array and `memoryWordsFrom` assign the same little-endian natural value. -/
theorem arrayReadWords_value_eq_memoryWordsFrom
    (mem : ByteArray) (aw : UInt256) (ptr count : Nat)
    (hfit : ptr + 32 * (count + 1) < UInt256.size)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat ptr) 0 count) =
      wordLimbsToNat
        (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (ptr + 32) count) := by
  rw [arrayReadWords_value_eq_memoryLimbs mem aw ptr count hfit hcovered hawFit,
    wordLimbsToNat_eq_limbsToNat,
    memoryWordsFrom_map_toNat_eq_memoryLimbs mem ptr count]

end Modexp.MultiLimbArrayReadSemantic
