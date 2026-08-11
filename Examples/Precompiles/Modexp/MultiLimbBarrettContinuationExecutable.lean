import Examples.Precompiles.Modexp.MultiLimbBarrettConstantSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookContinuationExecutable

/-!
# Executable Barrett schoolbook continuation

This file instantiates the constructive Knuth continuation with the concrete Barrett allocator
layout.  The geometry is common to positive- and zero-CLZ normalization; only their concrete
memory packages and path gas differ.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettContinuationExecutable

open MultiLimbBarrettConstantSemantic
open MultiLimbBarrettConstant
open MultiLimbSchoolbookContinuationExecutable
open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookNormalizationSemantic
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookOuterSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- A concrete in-bounds active read of a stored array length is the guarded array header used by
the generated code. -/
theorem arrayHeader_eq_of_read
    (mem : ByteArray) (aw array : UInt256) (count : Nat)
    (hmem : array.toNat + 32 ≤ mem.size)
    (hactive : array.toNat + 32 ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding array.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat count)) :
    arrayHeader mem aw array = UInt256.ofNat count := by
  have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hnotActive : ¬ array ≥ aw * ⟨32⟩ := by
    intro hge
    have hgeNat : (aw * ⟨32⟩).toNat ≤ array.toNat := hge
    rw [hawMul] at hgeNat
    omega
  unfold arrayHeader MultiLimbSchoolbookSingle.arrayHeader
    MultiLimbSchoolbookShort.arrayHeader MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by omega, hnotActive⟩), hread,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- Guarded array-header observations are unchanged when the underlying raw header word is
unchanged; memory extent and active-word guards are pointer-only and therefore identical. -/
theorem arrayHeader_eq_of_readWithPadding_eq
    (before after : ByteArray) (aw array : UInt256)
    (hbefore : array.toNat < before.size)
    (hsize : before.size ≤ after.size)
    (hread : after.readWithPadding array.toNat 32 =
      before.readWithPadding array.toNat 32) :
    arrayHeader after aw array = arrayHeader before aw array := by
  unfold arrayHeader MultiLimbSchoolbookSingle.arrayHeader
    MultiLimbSchoolbookShort.arrayHeader MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  have hafter : ¬ array.toNat ≥ after.size := by omega
  have hbefore' : ¬ array.toNat ≥ before.size := by omega
  simp only [hafter, hbefore', false_or, hread]

/-- A fresh-destination normalization pass preserves every complete raw word below its initial
frontier while extending memory one word per iteration. -/
theorem shiftDivisor_read_below_frontier
    (aw divisor v : UInt256) (shift index count read : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hmem32 : 32 ≤ mem.size)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hbelow : read + 32 ≤ (arrayAddress v index).toNat) :
    (MultiLimbSchoolbookNormalization.shiftDivisor aw divisor v shift index count mem carry
      ).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 :=
        MultiLimbSchoolbookNormalizationSemantic.storeShiftedWord_size_frontier
          mem v word carry index shift hheadFrontier
      have hheadRead : nextMem.readWithPadding read 32 = mem.readWithPadding read 32 := by
        dsimp only [nextMem]
        unfold storeShiftedWord
        apply toByteArray_write_read_below_padded_of_gap
        · exact hmem32
        · exact hbelow
        · rw [hheadFrontier]
          have husize : 0 < USize.size := by native_decide
          omega
      have htailFrontier : ∀ j, j ≤ count ->
          (arrayAddress v (index + 1 + j)).toNat = nextMem.size + 32 * j := by
        intro j hj
        rw [hnextSize]
        have hf := hfrontier (j + 1) (by omega)
        simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
        omega
      have htailBelow : read + 32 ≤ (arrayAddress v (index + 1)).toNat := by
        have hf := hfrontier 1 (by omega)
        rw [hf]
        omega
      have htail := ih (index + 1) nextMem nextCarry (by rw [hnextSize]; omega)
        htailFrontier htailBelow
      change
        (MultiLimbSchoolbookNormalization.shiftDivisor aw divisor v shift (index + 1) count
          nextMem nextCarry).memory.readWithPadding read 32 = _
      exact htail.trans hheadRead

/-- The fresh-destination normalization loop itself constructs its generated validity
certificate. Unlike the older in-bounds layout constructor, this version follows the exact
one-word memory frontier extension performed by each `MSTORE`. -/
theorem validDivisorShiftOfFrontier
    (aw divisor v : UInt256) (kEff shift index count : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hmem32 : 32 ≤ mem.size)
    (hdivHeader : arrayHeader mem aw divisor = UInt256.ofNat kEff)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat kEff)
    (hdivHeaderAw : arrayAfterHeader aw divisor = aw)
    (hvHeaderAw : arrayAfterHeader aw v = aw)
    (hdivElementAw : ∀ j, index ≤ j -> j < index + count ->
      arrayAfterWord aw divisor j = aw)
    (hvElementAw : ∀ j, index ≤ j -> j < index + count ->
      arrayAfterWord aw v j = aw)
    (hfrontier : ∀ j, j ≤ count ->
      (arrayAddress v (index + j)).toNat = mem.size + 32 * j)
    (hdivisorBelow : ∀ j, index ≤ j -> j < index + count ->
      divisor.toNat + 32 ≤ (arrayAddress v j).toNat)
    (hvBelow : ∀ j, index ≤ j -> j < index + count ->
      v.toNat + 32 ≤ (arrayAddress v j).toNat) :
    MultiLimbSchoolbookNormalization.ValidDivisorShift aw divisor v kEff shift
      index count mem carry := by
  induction count generalizing index mem carry with
  | zero => exact MultiLimbSchoolbookNormalization.ValidDivisorShift.zero index mem carry
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadFrontier : (arrayAddress v index).toNat = mem.size := by
        simpa using hfrontier 0 (by omega)
      have hnextSize : nextMem.size = mem.size + 32 := by
        simpa [nextMem] using
          MultiLimbSchoolbookNormalizationSemantic.storeShiftedWord_size_frontier
            mem v word carry index shift hheadFrontier
      have hheadDivBelow : divisor.toNat + 32 ≤ (arrayAddress v index).toNat :=
        hdivisorBelow index (by omega) (by omega)
      have hheadVBelow : v.toNat + 32 ≤ (arrayAddress v index).toNat :=
        hvBelow index (by omega) (by omega)
      have hdivRead : nextMem.readWithPadding divisor.toNat 32 =
          mem.readWithPadding divisor.toNat 32 := by
        have hsingle := shiftDivisor_read_below_frontier aw divisor v shift index 1
          divisor.toNat mem carry hmem32 (by
            intro j hj
            exact hfrontier j (by omega)) hheadDivBelow
        simpa [nextMem, nextCarry, word, MultiLimbSchoolbookNormalization.shiftDivisor]
          using hsingle
      have hvRead : nextMem.readWithPadding v.toNat 32 =
          mem.readWithPadding v.toNat 32 := by
        have hsingle := shiftDivisor_read_below_frontier aw divisor v shift index 1
          v.toNat mem carry hmem32 (by
            intro j hj
            exact hfrontier j (by omega)) hheadVBelow
        simpa [nextMem, nextCarry, word, MultiLimbSchoolbookNormalization.shiftDivisor]
          using hsingle
      have hdivHeaderNext : arrayHeader nextMem aw divisor = UInt256.ofNat kEff :=
        (arrayHeader_eq_of_readWithPadding_eq mem nextMem aw divisor (by
          rw [hheadFrontier] at hheadDivBelow
          omega) (by rw [hnextSize]; omega) hdivRead).trans hdivHeader
      have hvHeaderNext : arrayHeader nextMem aw v = UInt256.ofNat kEff :=
        (arrayHeader_eq_of_readWithPadding_eq mem nextMem aw v (by
          rw [hheadFrontier] at hheadVBelow
          omega) (by rw [hnextSize]; omega) hvRead).trans hvHeader
      have hnextFrontier : ∀ j, j ≤ count ->
          (arrayAddress v (index + 1 + j)).toNat = nextMem.size + 32 * j := by
        intro j hj
        rw [hnextSize]
        have hf := hfrontier (j + 1) (by omega)
        simp only [Nat.add_assoc, Nat.add_comm 1 j] at hf ⊢
        omega
      have hrest := ih (index + 1) nextMem nextCarry (by rw [hnextSize]; omega)
        hdivHeaderNext hvHeaderNext
        (by
          intro j hj hlt
          exact hdivElementAw j (by omega) (by omega))
        (by
          intro j hj hlt
          exact hvElementAw j (by omega) (by omega))
        hnextFrontier
        (by
          intro j hj hlt
          exact hdivisorBelow j (by omega) (by omega))
        (by
          intro j hj hlt
          exact hvBelow j (by omega) (by omega))
      exact MultiLimbSchoolbookNormalization.ValidDivisorShift.succ index count mem carry
        hdivHeader hdivHeaderAw (hdivElementAw index (by omega) (by omega))
        hvHeader hvHeaderAw (hvElementAw index (by omega) (by omega)) hrest

/-- An in-bounds normalization pass preserves every raw word below all of its stores. -/
theorem shiftDivisor_read_below_inBounds
    (aw divisor v : UInt256) (shift index count read : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hmem32 : 32 ≤ mem.size)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (hbelow : ∀ j, j < count -> read + 32 ≤ (arrayAddress v (index + j)).toNat) :
    (MultiLimbSchoolbookNormalization.shiftDivisor aw divisor v shift index count mem carry
      ).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        MultiLimbSchoolbookNormalizationSemantic.storeShiftedWord_size_eq
          mem v word carry index shift hheadWrite
      have hheadRead : nextMem.readWithPadding read 32 = mem.readWithPadding read 32 := by
        dsimp only [nextMem]
        unfold storeShiftedWord
        apply toByteArray_write_read_below_padded_of_gap
        · exact hmem32
        · simpa using hbelow 0 (by omega)
        · have husize : 0 < USize.size := by native_decide
          omega
      have htail := ih (index + 1) nextMem nextCarry (by rw [hnextSize]; exact hmem32)
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbelow (j + 1) (by omega))
      change
        (MultiLimbSchoolbookNormalization.shiftDivisor aw divisor v shift (index + 1) count
          nextMem nextCarry).memory.readWithPadding read 32 = _
      exact htail.trans hheadRead

/-- An in-bounds normalization pass preserves every padded raw word above all of its stores. -/
theorem shiftDivisor_read_above_inBounds
    (aw divisor v : UInt256) (shift index count read : Nat)
    (mem : ByteArray) (carry : UInt256)
    (hwrite : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ mem.size)
    (habove : ∀ j, j < count ->
      (arrayAddress v (index + j)).toNat + 32 ≤ read) :
    (MultiLimbSchoolbookNormalization.shiftDivisor aw divisor v shift index count mem carry
      ).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction count generalizing index mem carry with
  | zero => rfl
  | succ count ih =>
      let word := arrayWord mem aw divisor index
      let nextMem := storeShiftedWord mem v index shift word carry
      let nextCarry := shiftedCarry word shift
      have hheadWrite : (arrayAddress v index).toNat + 32 ≤ mem.size := by
        simpa using hwrite 0 (by omega)
      have hnextSize : nextMem.size = mem.size :=
        MultiLimbSchoolbookNormalizationSemantic.storeShiftedWord_size_eq
          mem v word carry index shift hheadWrite
      have hheadRead : nextMem.readWithPadding read 32 = mem.readWithPadding read 32 := by
        dsimp only [nextMem]
        unfold storeShiftedWord
        exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
          hheadWrite (by simpa using habove 0 (by omega))
      have htail := ih (index + 1) nextMem nextCarry
        (by
          intro j hj
          rw [hnextSize]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hwrite (j + 1) (by omega))
        (by
          intro j hj
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using habove (j + 1) (by omega))
      change
        (MultiLimbSchoolbookNormalization.shiftDivisor aw divisor v shift (index + 1) count
          nextMem nextCarry).memory.readWithPadding read 32 = _
      exact htail.trans hheadRead

/-- Exact payload address in the preallocated Barrett remainder array. -/
theorem remainderArrayAddress_toNat
    (fp k i : Nat) (hi : i < k)
    (hfit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    (arrayAddress (UInt256.ofNat (remainderPtr fp k)) i).toNat =
      remainderPtr fp k + 32 * (i + 1) := by
  have hptrFit : remainderPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have haddressFit : (UInt256.ofNat (remainderPtr fp k)).toNat + 32 * (i + 1) <
      UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hptrFit]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit _ _ haddressFit,
    UInt256.toNat_ofNat_of_lt hptrFit]

/-- Exact payload address in the Barrett quotient array. -/
theorem quotientArrayAddress_toNat
    (fp k i : Nat) (hi : i < quotientCount k)
    (hfit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size) :
    (arrayAddress (UInt256.ofNat (quotientPtr fp k)) i).toNat =
      quotientPtr fp k + 32 * (i + 1) := by
  have hptrFit : quotientPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have haddressFit : (UInt256.ofNat (quotientPtr fp k)).toNat + 32 * (i + 1) <
      UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hptrFit]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit _ _ haddressFit,
    UInt256.toNat_ofNat_of_lt hptrFit]

/-- The full Barrett allocator layout satisfies the cursor-independent geometry required by every
schoolbook quotient digit.  In particular, a 32-limb divisor has a 34-word quotient and a
66-word aggregate window span; the divisor count itself remains bounded by 32. -/
theorem continuationGeometry
    (aw : UInt256) (fp k : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hactive : normalizedDivisorPtr fp k + 32 + 32 * k ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    ContinuationGeometry aw
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (quotientPtr fp k))
      k (dividendLength k + 1) (quotientCount k) := by
  have hqPtrFit : quotientPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
    omega
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hqNat : (UInt256.ofNat (quotientPtr fp k)).toNat = quotientPtr fp k :=
    UInt256.toNat_ofNat_of_lt hqPtrFit
  have huNat : (UInt256.ofNat (normalizedDividendPtr fp k)).toNat =
      normalizedDividendPtr fp k := UInt256.toNat_ofNat_of_lt huPtrFit
  have hvNat : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat =
      normalizedDivisorPtr fp k := UInt256.toNat_ofNat_of_lt hvPtrFit
  have hqAddress : ∀ i, i < quotientCount k ->
      (MultiLimbSchoolbookSingle.arrayAddress
        (UInt256.ofNat (quotientPtr fp k)) i).toNat = quotientPtr fp k + 32 * (i + 1) := by
    intro i hi
    unfold MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
    rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit, hqNat]
    unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
    omega
  have huAddress : ∀ i, i < dividendLength k + 1 ->
      (MultiLimbSchoolbookSingle.arrayAddress
        (UInt256.ofNat (normalizedDividendPtr fp k)) i).toNat =
          normalizedDividendPtr fp k + 32 * (i + 1) := by
    intro i hi
    exact normalizedDividendArrayAddress_toNat fp k i (by omega) huFit
  have hvAddress : ∀ i, i < k ->
      (MultiLimbSchoolbookSingle.arrayAddress
        (UInt256.ofNat (normalizedDivisorPtr fp k)) i).toNat =
          normalizedDivisorPtr fp k + 32 * (i + 1) := by
    intro i hi
    exact normalizedDivisorArrayAddress_toNat fp k i (by omega) hvFit
  have hqActive : quotientPtr fp k + 32 ≤ 32 * aw.toNat := by
    unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
      wordArrayPayloadSize at hactive
    omega
  have huActive : normalizedDividendPtr fp k + 32 ≤ 32 * aw.toNat := by
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize at hactive
    omega
  have hvActive : normalizedDivisorPtr fp k + 32 ≤ 32 * aw.toNat := by omega
  refine {
    hcountTwo := hkTwo
    hcountRange := hk
    hcountWord := by
      have hsize : 32 < UInt256.size := by decide
      omega
    hquotientCountPos := by rw [quotientCount_eq]; omega
    hquotientCountWord := by
      rw [quotientCount_eq]
      have : 34 < UInt256.size := by decide
      omega
    huCountEq := by rw [quotientCount_eq]; unfold dividendLength; omega
    hwindowRange := by rw [quotientCount_eq]; omega
    hawFit := hawFit
    hvFit := by
      rw [hvNat]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega
    huFit := by
      rw [huNat, quotientCount_eq]
      unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega
    hquotientFit := by
      rw [hqNat]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
      omega
    hvActive := by rw [hvNat]; omega
    huTopActive := by
      rw [huNat, quotientCount_eq]
      unfold normalizedDivisorPtr dividendLength wordArrayAllocationSize
        wordArrayPayloadSize at hactive
      omega
    htopBelowV := by
      rw [huNat, hvNat, quotientCount_eq]
      unfold normalizedDivisorPtr dividendLength wordArrayAllocationSize wordArrayPayloadSize
      omega
    hquotientPayloadBelowU := by
      rw [hqNat, huNat]
      unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    hvHeaderAw := arrayAfterHeader_eq_of_active aw
      (UInt256.ofNat (normalizedDivisorPtr fp k)) (by rw [hvNat]; exact hvActive)
    huHeaderAw := arrayAfterHeader_eq_of_active aw
      (UInt256.ofNat (normalizedDividendPtr fp k)) (by rw [huNat]; exact huActive)
    hquotientHeaderAw := arrayAfterHeader_eq_of_active aw
      (UInt256.ofNat (quotientPtr fp k)) (by rw [hqNat]; exact hqActive)
    hvWordAw := by
      intro i hi
      apply arrayAfterWord_eq_of_active
      rw [hvAddress i hi]
      omega
    huWordAw := by
      intro i hi
      apply arrayAfterWord_eq_of_active
      rw [huAddress i hi]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize at hactive
      omega
    hquotientWordAw := by
      intro i hi
      apply arrayAfterWord_eq_of_active
      rw [hqAddress i hi]
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize at hactive
      omega
  }

/-- Positive-CLZ normalization retains the allocator active-word count used by the quotient loop. -/
theorem positiveContinuationGeometry
    (aw : UInt256) (fp k : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    ContinuationGeometry (barrettVWords aw fp k)
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (quotientPtr fp k))
      k (dividendLength k + 1) (quotientCount k) := by
  have hrange := barrettVWords_range aw fp k (by omega) hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  exact continuationGeometry (barrettVWords aw fp k) fp k hkTwo hk hquotientFit huFit hvFit
    hrange.1 hrange.2

/-- The zero-CLZ copy path uses its exact post-`MCOPY` active-word count in the same layout. -/
theorem zeroContinuationGeometry
    (aw : UInt256) (fp k divisorPtr : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
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
    ContinuationGeometry (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (quotientPtr fp k))
      k (dividendLength k + 1) (quotientCount k) := by
  have hrange := barrettZeroWords_range aw fp k divisorPtr (by omega) hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  exact continuationGeometry (barrettZeroWords aw fp k divisorPtr) fp k hkTwo hk
    hquotientFit huFit hvFit hrange.1 hrange.2

/-- The fresh normalized-divisor allocation stores its raw `k` header bytes. -/
theorem barrettVMemory_vHeaderRead
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).readWithPadding (normalizedDivisorPtr fp k) 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  have hcopiedSize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hcopied96 : 96 ≤ (barrettCopiedMemory mem fp k).size := by
    rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hsetSize :
      (setFreePtr (barrettCopiedMemory mem fp k)
        (normalizedDivisorPtr fp k + wordArrayAllocationSize k)).size =
        (barrettCopiedMemory mem fp k).size := setFreePtr_size hcopied96
  have hvGap : normalizedDivisorPtr fp k -
      (setFreePtr (barrettCopiedMemory mem fp k)
        (normalizedDivisorPtr fp k + wordArrayAllocationSize k)).size < USize.size := by
    rw [hsetSize, hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 32 < USize.size := by native_decide
    omega
  unfold barrettVMemory MultiLimbSchoolbookNormalization.vMemory
  exact storeBytesLength_read_self hvGap

/-- The quotient, normalized-dividend, copy, and normalized-divisor allocations all retain the
earlier Barrett remainder header. -/
theorem barrettVMemory_remainderHeaderRead
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).readWithPadding (remainderPtr fp k) 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap hfirstFit
  have hstored96 : 96 ≤ (storedDividendMemory mem fp k).size := by
    rw [hstoredSize]
    omega
  have hremSetSize :
      (setFreePtr (storedDividendMemory mem fp k)
        (remainderPtr fp k + wordArrayAllocationSize k)).size =
          (storedDividendMemory mem fp k).size := setFreePtr_size hstored96
  have hremGap : remainderPtr fp k -
      (setFreePtr (storedDividendMemory mem fp k)
        (remainderPtr fp k + wordArrayAllocationSize k)).size < USize.size := by
    rw [hremSetSize, hstoredSize]
    unfold remainderPtr
    have husize : 0 < USize.size := by native_decide
    omega
  have hremRead : (barrettDivisionMemory mem fp k).readWithPadding
      (remainderPtr fp k) 32 = UInt256.toByteArray (UInt256.ofNat k) := by
    unfold barrettDivisionMemory
    exact storeBytesLength_read_self hremGap
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
  have hremReadQ : (barrettQuotientMemory mem fp k).readWithPadding
      (remainderPtr fp k) 32 =
        (barrettDivisionMemory mem fp k).readWithPadding (remainderPtr fp k) 32 := by
    have hread := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (barrettDivisionMemory mem fp k) (quotientPtr fp k) (quotientCount k)
      (remainderPtr fp k) hbase96 hqGap (by
        unfold remainderPtr
        omega) (by
          unfold quotientPtr remainderPtr wordArrayAllocationSize wordArrayPayloadSize
          omega)
    simpa only [barrettQuotientMemory, MultiLimbSchoolbookKnuthPrefix.quotientMemory,
      MultiLimbSchoolbookKnuthSetup.quotientMemory] using hread
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
  have huGap : normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size <
      USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hremReadU : (barrettUMemory mem fp k).readWithPadding (remainderPtr fp k) 32 =
      (barrettQuotientMemory mem fp k).readWithPadding (remainderPtr fp k) 32 := by
    have hread := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (barrettQuotientMemory mem fp k) (normalizedDividendPtr fp k)
      (dividendLength k + 1) (remainderPtr fp k) hq96 huGap (by
        unfold remainderPtr
        omega) (by
          unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
            wordArrayPayloadSize
          omega)
    simpa only [barrettUMemory, MultiLimbSchoolbookKnuthPrefix.uMemory,
      MultiLimbSchoolbookKnuthSetup.uMemory] using hread
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hsource : fp + 32 + 32 * dividendLength k ≤ (barrettUMemory mem fp k).size := by
    rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremReadCopied : (barrettCopiedMemory mem fp k).readWithPadding
      (remainderPtr fp k) 32 =
        (barrettUMemory mem fp k).readWithPadding (remainderPtr fp k) 32 := by
    have hread := write_read_below_end_from (barrettUMemory mem fp k)
      (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k) (remainderPtr fp k)
      (by unfold dividendLength; omega) hsource (by
        rw [huSize]
        unfold normalizedDividendPtr quotientPtr remainderPtr quotientCount dividendLength
          MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
        omega)
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
  have hremReadV := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettCopiedMemory mem fp k) (normalizedDivisorPtr fp k) k (remainderPtr fp k)
    hcopied96 hvGap (by
      unfold remainderPtr
      omega) (by
        unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega)
  exact hremReadV.trans (hremReadCopied.trans (hremReadU.trans (hremReadQ.trans hremRead)))

/-- The actual quotient allocation, `u` allocation, numerator `MCOPY`, and `v` allocation retain
the quotient and normalized-dividend header bytes written by their respective allocations. -/
theorem barrettVMemory_quHeaderReads
    (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (barrettVMemory mem fp k).readWithPadding (quotientPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (quotientCount k)) ∧
      (barrettVMemory mem fp k).readWithPadding (normalizedDividendPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (dividendLength k + 1)) := by
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
  have hqGap : quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
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
  have hqRead : (barrettQuotientMemory mem fp k).readWithPadding (quotientPtr fp k) 32 =
      UInt256.toByteArray (UInt256.ofNat (quotientCount k)) := by
    unfold barrettQuotientMemory MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    exact storeBytesLength_read_self (by rwa [hqSetSize])
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
  have huRead : (barrettUMemory mem fp k).readWithPadding
      (normalizedDividendPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (dividendLength k + 1)) := by
    have huSetSize :
        (setFreePtr (barrettQuotientMemory mem fp k)
          (normalizedDividendPtr fp k +
            wordArrayAllocationSize (dividendLength k + 1))).size =
          (barrettQuotientMemory mem fp k).size := setFreePtr_size hq96
    unfold barrettQuotientMemory at huSetSize huGap
    unfold barrettUMemory MultiLimbSchoolbookKnuthPrefix.uMemory
      MultiLimbSchoolbookKnuthSetup.uMemory
    exact storeBytesLength_read_self (by
      rw [huSetSize]
      exact huGap)
  have hqReadU : (barrettUMemory mem fp k).readWithPadding (quotientPtr fp k) 32 =
      (barrettQuotientMemory mem fp k).readWithPadding (quotientPtr fp k) 32 := by
    have hread := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (barrettQuotientMemory mem fp k) (normalizedDividendPtr fp k)
      (dividendLength k + 1) (quotientPtr fp k) hq96 huGap (by
        unfold quotientPtr remainderPtr
        omega) (by
        unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
        omega)
    simpa only [barrettUMemory, MultiLimbSchoolbookKnuthPrefix.uMemory,
      MultiLimbSchoolbookKnuthSetup.uMemory] using hread
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hsource : fp + 32 + 32 * dividendLength k ≤ (barrettUMemory mem fp k).size := by
    rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqReadCopied : (barrettCopiedMemory mem fp k).readWithPadding (quotientPtr fp k) 32 =
      (barrettUMemory mem fp k).readWithPadding (quotientPtr fp k) 32 := by
    have hread := write_read_below_end_from (barrettUMemory mem fp k)
      (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k) (quotientPtr fp k)
      (by unfold dividendLength; omega) hsource (by
        rw [huSize]
        unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
        omega)
    unfold barrettCopiedMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
      MultiLimbSchoolbookKnuthSetup.copiedUMemory
    rw [← huSize]
    exact hread
  have huReadCopied : (barrettCopiedMemory mem fp k).readWithPadding
      (normalizedDividendPtr fp k) 32 =
        (barrettUMemory mem fp k).readWithPadding (normalizedDividendPtr fp k) 32 := by
    have hread := write_read_below_end_from (barrettUMemory mem fp k)
      (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k)
      (normalizedDividendPtr fp k) (by unfold dividendLength; omega) hsource (by rw [huSize])
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
  have hqReadV := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettCopiedMemory mem fp k) (normalizedDivisorPtr fp k) k (quotientPtr fp k)
    hcopied96 hvGap (by unfold quotientPtr remainderPtr; omega) (by
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega)
  have huReadV := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettCopiedMemory mem fp k) (normalizedDivisorPtr fp k) k
    (normalizedDividendPtr fp k) hcopied96 hvGap (by
      unfold normalizedDividendPtr quotientPtr remainderPtr
      omega) (by
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        omega)
  constructor
  · exact hqReadV.trans (hqReadCopied.trans (hqReadU.trans hqRead))
  · exact huReadV.trans (huReadCopied.trans huRead)

/-- The fresh normalized-divisor allocation materializes its concrete `k` header under the exact
active-word counter used by normalization. -/
theorem barrettVMemory_vHeader
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
    arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) = UInt256.ofNat k := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvNat : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat =
      normalizedDivisorPtr fp k := UInt256.toNat_ofNat_of_lt hvPtrFit
  apply arrayHeader_eq_of_read
  · rw [hvNat, hvSize]
  · rw [hvNat]
    have := hrange.1
    omega
  · exact hrange.2
  · rw [hvNat]
    exact barrettVMemory_vHeaderRead mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit

/-- The positive path's fresh normalized-divisor pass is a concrete generated execution. Its
destination payload begins exactly at the current memory frontier, so each recursive store
extends memory by one word while retaining the source and destination headers. -/
theorem barrettPositiveDivisorValid
    (mem : ByteArray) (aw divisor : UInt256) (fp k shift : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    (hdivisorHeader : arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k)
      divisor = UInt256.ofNat k)
    (hdivisorHeaderAw : arrayAfterHeader (barrettVWords aw fp k) divisor =
      barrettVWords aw fp k)
    (hdivisorWordAw : ∀ j, j < k ->
      arrayAfterWord (barrettVWords aw fp k) divisor j = barrettVWords aw fp k)
    (hdivisorBelowV : divisor.toNat + 32 ≤ normalizedDivisorPtr fp k + 32) :
    MultiLimbSchoolbookNormalization.ValidDivisorShift
      (barrettVWords aw fp k) divisor (UInt256.ofNat (normalizedDivisorPtr fp k))
      k shift 0 k (barrettVMemory mem fp k) ⟨0⟩ := by
  have hkPos : 0 < k := by omega
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
  have hvHeader := barrettVMemory_vHeader mem aw fp k hk hkPos hfp hmemSize hmemLe hgap
    hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvNat := UInt256.toNat_ofNat_of_lt hvPtrFit
  apply validDivisorShiftOfFrontier
  · rw [hvSize]
    omega
  · exact hdivisorHeader
  · exact hvHeader
  · exact hdivisorHeaderAw
  · exact geometry.hvHeaderAw
  · intro j hj hlt
    exact hdivisorWordAw j (by omega)
  · intro j hj hlt
    exact geometry.hvWordAw j (by omega)
  · intro j hj
    simp only [Nat.zero_add]
    rw [normalizedDivisorArrayAddress_toNat fp k j (by omega) hvFit, hvSize]
    omega
  · intro j hj hlt
    rw [normalizedDivisorArrayAddress_toNat fp k j (by omega) hvFit]
    exact le_trans hdivisorBelowV (by omega)
  · intro j hj hlt
    rw [hvNat, normalizedDivisorArrayAddress_toNat fp k j (by omega) hvFit]
    omega

/-- After the fresh `v` shift, the positive path's `u` normalization is entirely in bounds. The
starting `u` header is derived through the concrete first-pass memory frame, after which the
existing layout constructor selects every generated in-place shift iteration. -/
theorem barrettPositiveDividendValid
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    MultiLimbSchoolbookNormalization.ValidDivisorShift
      (barrettVWords aw fp k) (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (normalizedDividendPtr fp k)) (dividendLength k + 1)
      (MultiLimbClz.clzResult top).n 0 (dividendLength k)
      (barrettPositiveDivisorResult mem aw fp k divisor top).memory ⟨0⟩ := by
  have hkPos : 0 < k := by omega
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hbase32 : 32 ≤ (barrettVMemory mem fp k).size := by rw [hvSize]; omega
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
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have huInitial : arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k) u =
      UInt256.ofNat (dividendLength k + 1) := by
    apply arrayHeader_eq_of_read
    · rw [huNat, hvSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [huNat]
      exact le_trans (by
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        omega) hrange.1
    · exact hrange.2
    · rw [huNat]
      exact (barrettVMemory_quHeaderReads mem fp k hk hkPos hfp hmemSize hmemLe hgap
        hfirstFit).2
  have huBelowV0 : normalizedDividendPtr fp k + 32 ≤ (arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k 0 (by omega) hvFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huRead : divisorResult.memory.readWithPadding (normalizedDividendPtr fp k) 32 =
      (barrettVMemory mem fp k).readWithPadding (normalizedDividendPtr fp k) 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k
        (normalizedDividendPtr fp k) (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) huBelowV0
  have huHeader : arrayHeader divisorResult.memory (barrettVWords aw fp k) u =
      UInt256.ofNat (dividendLength k + 1) := by
    apply (arrayHeader_eq_of_readWithPadding_eq (barrettVMemory mem fp k)
      divisorResult.memory (barrettVWords aw fp k) u (by
        rw [huNat, hvSize]
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        omega) (by rw [hdivisorResultSize]; omega) (by
          simpa only [u, huNat] using huRead)).trans
    exact huInitial
  apply MultiLimbSchoolbookNormalization.validDivisorShiftOfLayout
  · exact huHeader
  · exact huHeader
  · exact geometry.huHeaderAw
  · exact geometry.huHeaderAw
  · intro j hj hlt
    exact geometry.huWordAw j (by omega)
  · intro j hj hlt
    exact geometry.huWordAw j (by omega)
  · intro j hj hlt
    rw [hdivisorResultSize, hvSize]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro j hj hlt
    rw [huNat, normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    omega
  · intro j hj hlt
    rw [huNat, normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    omega

/-- The completed in-place `u` shift retains the concrete `m+1` header consumed by the generated
top-carry store. This is an intermediate PC-level fact, so it is proved before the final carry
write rather than inferred from the later quotient-loop state. -/
theorem barrettPositiveDividendResult_uHeader
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    arrayHeader (barrettPositiveDividendResult mem aw fp k divisor top).memory
        (barrettVWords aw fp k) (UInt256.ofNat (normalizedDividendPtr fp k)) =
      UInt256.ofNat (dividendLength k + 1) := by
  have hkPos : 0 < k := by omega
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := barrettPositiveDividendResult mem aw fp k divisor top
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
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
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have huInitial : arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k) u =
      UInt256.ofNat (dividendLength k + 1) := by
    apply arrayHeader_eq_of_read
    · rw [huNat, hvSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [huNat]
      exact le_trans (by
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        omega) hrange.1
    · exact hrange.2
    · rw [huNat]
      exact (barrettVMemory_quHeaderReads mem fp k hk hkPos hfp hmemSize hmemLe hgap
        hfirstFit).2
  have hbase32 : 32 ≤ (barrettVMemory mem fp k).size := by rw [hvSize]; omega
  have huBelowV0 : normalizedDividendPtr fp k + 32 ≤ (arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k 0 (by omega) hvFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huDivisorRead : divisorResult.memory.readWithPadding
      (normalizedDividendPtr fp k) 32 =
        (barrettVMemory mem fp k).readWithPadding (normalizedDividendPtr fp k) 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k
        (normalizedDividendPtr fp k) (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) huBelowV0
  have huHeader : arrayHeader divisorResult.memory (barrettVWords aw fp k) u =
      UInt256.ofNat (dividendLength k + 1) := by
    apply (arrayHeader_eq_of_readWithPadding_eq (barrettVMemory mem fp k)
      divisorResult.memory (barrettVWords aw fp k) u (by
        rw [huNat, hvSize]
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        omega) (by rw [hdivisorResultSize]; omega) (by
          simpa only [u, huNat] using huDivisorRead)).trans
    exact huInitial
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize, hvSize]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huBelow : ∀ j, j < dividendLength k ->
      normalizedDividendPtr fp k + 32 ≤ (arrayAddress u j).toNat := by
    intro j hj
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    omega
  have huResultRead : dividendResult.memory.readWithPadding
      (normalizedDividendPtr fp k) 32 =
        divisorResult.memory.readWithPadding (normalizedDividendPtr fp k) 32 := by
    simpa [dividendResult, barrettPositiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_below_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) (normalizedDividendPtr fp k) divisorResult.memory ⟨0⟩
        (by rw [hdivisorResultSize, hvSize]; omega)
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using huBelow)
  have hresultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k) divisorResult.memory ⟨0⟩
      (by simpa only [Nat.zero_add] using huWrite)
    simpa [dividendResult, barrettPositiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  apply (arrayHeader_eq_of_readWithPadding_eq divisorResult.memory dividendResult.memory
    (barrettVWords aw fp k) u (by
      rw [huNat, hdivisorResultSize, hvSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega) (by rw [hresultSize]) (by simpa only [u, huNat] using huResultRead)).trans
  exact huHeader

/-- Execute the complete positive-CLZ Barrett normalization from the real `_clz` return at PC
5368 to the quotient-loop entry at PC 5450. Both generated shift-loop validity certificates and
all intermediate/final headers are derived from the concrete Barrett layout. -/
theorem barrettPositiveNormalizationExact_of_vHeader
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw divisor top rem : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k ret : Nat} {tail : List UInt256}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
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
    (hvBound : normalizedDivisorPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcopiedFree : (barrettCopiedMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (normalizedDivisorPtr fp k)))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdivisorHeader : arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k)
      divisor = UInt256.ofNat k)
    (hdivisorHeaderAw : arrayAfterHeader (barrettVWords aw fp k) divisor =
      barrettVWords aw fp k)
    (hdivisorWordAw : ∀ j, j < k ->
      arrayAfterWord (barrettVWords aw fp k) divisor j = barrettVWords aw fp k)
    (hdivisorBelowV : divisor.toNat + 32 ≤ normalizedDivisorPtr fp k + 32)
    (hvHeader : arrayHeader (barrettPositiveMemory mem aw fp k divisor top)
      (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k)) =
        UInt256.ofNat k)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat (MultiLimbClz.clzResult top).n :: rem :: UInt256.ofNat ret ::
        UInt256.ofNat k :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat (quotientPtr fp k) :: UInt256.ofNat (normalizedDividendPtr fp k) ::
        UInt256.ofNat (quotientCount k) :: divisor :: tail)
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      rdata acc steps gasUsed) :
    let vTop := arrayWord (barrettPositiveMemory mem aw fp k divisor top)
      (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5450⟩
      (UInt256.ofNat (MultiLimbClz.clzResult top).n :: UInt256.ofNat ret :: rem ::
        UInt256.ofNat (quotientCount k) :: UInt256.ofNat k ::
        UInt256.ofNat (normalizedDivisorPtr fp k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: vTop :: ⟨1⟩ :: tail)
      (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
      rdata acc
      (steps + MultiLimbSchoolbookNormalizationFunction.positiveSteps
        (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor
        (UInt256.ofNat (normalizedDivisorPtr fp k))
        (UInt256.ofNat (normalizedDividendPtr fp k)) k (dividendLength k)
        (MultiLimbClz.clzResult top).n)
      (gasUsed + MultiLimbSchoolbookNormalizationFunction.positiveGas
        (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k) divisor
        (UInt256.ofNat (normalizedDivisorPtr fp k))
        (UInt256.ofNat (normalizedDividendPtr fp k)) (normalizedDivisorPtr fp k) k
        (dividendLength k) (MultiLimbClz.clzResult top).n) := by
  have hkPos : 0 < k := by omega
  have hshiftBound : (MultiLimbClz.clzResult top).n < 256 := by
    have hn := MultiLimbClz.clzResult_n_le top
    omega
  have hkWord : k < UInt256.size := by
    exact lt_of_le_of_lt hk (by norm_num [UInt256.size])
  have hmWord : dividendLength k < UInt256.size := by
    unfold dividendLength
    exact lt_of_le_of_lt (by omega : 2 * k + 1 ≤ 65) (by norm_num [UInt256.size])
  have hmSuccWord : dividendLength k + 1 < UInt256.size := by
    unfold dividendLength
    exact lt_of_le_of_lt (by omega : 2 * k + 1 + 1 ≤ 66) (by norm_num [UInt256.size])
  have hcopiedSize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hcopied96 : 96 ≤ (barrettCopiedMemory mem fp k).size := by
    rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hcopiedLe : (barrettCopiedMemory mem fp k).size ≤ normalizedDivisorPtr fp k := by
    rw [hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopiedGap : normalizedDivisorPtr fp k - (barrettCopiedMemory mem fp k).size <
      USize.size := by
    rw [hcopiedSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 32 < USize.size := by native_decide
    omega
  have hcopiedRange := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit
  have hcopiedAw3 : 3 ≤ (barrettCopiedWords aw fp k).toNat := by
    have := hcopiedRange.1
    unfold normalizedDividendPtr quotientPtr remainderPtr at this
    omega
  have hcopiedAw64 : ¬ (⟨64⟩ : UInt256) ≥
      barrettCopiedWords aw fp k * ⟨32⟩ := by
    have hmul : (barrettCopiedWords aw fp k * (⟨32⟩ : UInt256)).toNat =
        (barrettCopiedWords aw fp k).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := barrettCopiedWords aw fp k) (b := (⟨32⟩ : UInt256))
          hcopiedRange.2
    intro hle
    have hnat : (barrettCopiedWords aw fp k * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    have := hcopiedRange.1
    unfold normalizedDividendPtr quotientPtr remainderPtr at this
    omega
  have hdivisorValid := barrettPositiveDivisorValid mem aw divisor fp k
    (MultiLimbClz.clzResult top).n hkTwo hk hfp hmemSize hmemLe hgap hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hdivisorHeader hdivisorHeaderAw hdivisorWordAw
    hdivisorBelowV
  have hdividendValid := barrettPositiveDividendValid mem aw divisor top fp k hkTwo hk hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have huHeader := barrettPositiveDividendResult_uHeader mem aw divisor top fp k hkTwo hk hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
  let vTop := arrayWord (barrettPositiveMemory mem aw fp k divisor top)
    (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)
  have rd := MultiLimbSchoolbookNormalizationFunction.positiveExact
    (fp := normalizedDivisorPtr fp k) (kEff := k) (m := dividendLength k)
    (numQ := quotientCount k) (ret := ret)
    (quotient := UInt256.ofNat (quotientPtr fp k))
    (u := UInt256.ofNat (normalizedDividendPtr fp k)) (divisor := divisor)
    (vTop := vTop) hshiftPos hshiftBound hkPos hk hkWord hmWord hmSuccWord
    (by unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr; omega)
    hvBound hcopied96 hcopiedLe hcopiedGap hcopiedAw3 hcopiedAw64 hcopiedFree hcalldata
    hdivisorValid hdividendValid huHeader geometry.huHeaderAw
    (geometry.huWordAw (dividendLength k) (by omega)) hvHeader geometry.hvHeaderAw
    (geometry.hvWordAw (k - 1) (by omega)) rfl htail h
  simpa [barrettPositiveMemory, barrettPositiveDividendResult,
    barrettPositiveDivisorResult, barrettVMemory, barrettVWords, vTop] using rd

/-- The concrete active state after `v` allocation observes the retained quotient and `u`
headers. -/
theorem barrettVMemory_quHeaders
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
    arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat (quotientPtr fp k)) = UInt256.ofNat (quotientCount k) ∧
      arrayHeader (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat (normalizedDividendPtr fp k)) =
          UInt256.ofNat (dividendLength k + 1) := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hreads := barrettVMemory_quHeaderReads mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hqPtrFit : quotientPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
    omega
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  constructor
  · apply arrayHeader_eq_of_read
    · rw [hqNat, hvSize]
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    · rw [hqNat]
      have := hrange.1
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize at this
      omega
    · exact hrange.2
    · rw [hqNat]
      exact hreads.1
  · apply arrayHeader_eq_of_read
    · rw [huNat, hvSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [huNat]
      have := hrange.1
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize at this
      omega
    · exact hrange.2
    · rw [huNat]
      exact hreads.2

/-- The zero-CLZ `MCOPY` also preserves the earlier remainder header below its destination. -/
theorem barrettZeroMemory_remainderHeaderRead
    (mem : ByteArray) (fp k divisorPtr : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding (remainderPtr fp k) 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hread := write_read_below_end_from (barrettVMemory mem fp k)
    (barrettVMemory mem fp k) (divisorPtr + 32) (32 * k) (remainderPtr fp k)
    (by omega) hsource (by
      rw [hvSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hinitial := barrettVMemory_remainderHeaderRead mem fp k hk hkPos hfp hmemSize
    hmemLe hgap hfirstFit
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    shiftZeroMemory
  rw [← hvSize]
  exact hread.trans hinitial

/-- The zero-CLZ `MCOPY` begins immediately after the `v` header and preserves that raw header. -/
theorem barrettZeroMemory_vHeaderRead
    (mem : ByteArray) (fp k divisorPtr : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding
        (normalizedDivisorPtr fp k) 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hread := write_read_below_end_from (barrettVMemory mem fp k)
    (barrettVMemory mem fp k) (divisorPtr + 32) (32 * k)
    (normalizedDivisorPtr fp k) (by omega) hsource (by rw [hvSize])
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  rw [← hvSize]
  exact hread.trans (barrettVMemory_vHeaderRead mem fp k hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit)

/-- The zero-path copy also preserves the lower quotient and `u` raw headers. -/
theorem barrettZeroMemory_quHeaderReads
    (mem : ByteArray) (fp k divisorPtr : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding (quotientPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (quotientCount k)) ∧
      (barrettZeroMemory mem fp k divisorPtr).readWithPadding
          (normalizedDividendPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (dividendLength k + 1)) := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hreads := barrettVMemory_quHeaderReads mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hqBelow : quotientPtr fp k + 32 ≤ (barrettVMemory mem fp k).size := by
    rw [hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  have huBelow : normalizedDividendPtr fp k + 32 ≤ (barrettVMemory mem fp k).size := by
    rw [hvSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqFrame := write_read_below_end_from (barrettVMemory mem fp k)
    (barrettVMemory mem fp k) (divisorPtr + 32) (32 * k) (quotientPtr fp k)
    (by omega) hsource hqBelow
  have huFrame := write_read_below_end_from (barrettVMemory mem fp k)
    (barrettVMemory mem fp k) (divisorPtr + 32) (32 * k) (normalizedDividendPtr fp k)
    (by omega) hsource huBelow
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  rw [← hvSize]
  exact ⟨hqFrame.trans hreads.1, huFrame.trans hreads.2⟩

/-- The exact post-`MCOPY` active state observes the preserved concrete `v` header. -/
theorem barrettZeroMemory_vHeader
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
    arrayHeader (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) = UInt256.ofNat k := by
  have hrange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvNat : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat =
      normalizedDivisorPtr fp k := UInt256.toNat_ofNat_of_lt hvPtrFit
  apply arrayHeader_eq_of_read
  · rw [hvNat, hzSize]
    omega
  · rw [hvNat]
    have := hrange.1
    omega
  · exact hrange.2
  · rw [hvNat]
    exact barrettZeroMemory_vHeaderRead mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
      hgap hfirstFit hsource

/-- The zero-copy path's exact active state observes the preserved quotient and `u` headers. -/
theorem barrettZeroMemory_quHeaders
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
    arrayHeader (barrettZeroMemory mem fp k divisorPtr)
        (barrettZeroWords aw fp k divisorPtr) (UInt256.ofNat (quotientPtr fp k)) =
          UInt256.ofNat (quotientCount k) ∧
      arrayHeader (barrettZeroMemory mem fp k divisorPtr)
        (barrettZeroWords aw fp k divisorPtr)
        (UInt256.ofNat (normalizedDividendPtr fp k)) =
          UInt256.ofNat (dividendLength k + 1) := by
  have hrange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hreads := barrettZeroMemory_quHeaderReads mem fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hfirstFit hsource
  have hqPtrFit : quotientPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
    omega
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  constructor
  · apply arrayHeader_eq_of_read
    · rw [hqNat, hzSize]
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    · rw [hqNat]
      have := hrange.1
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize at this
      omega
    · exact hrange.2
    · rw [hqNat]
      exact hreads.1
  · apply arrayHeader_eq_of_read
    · rw [huNat, hzSize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [huNat]
      have := hrange.1
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize at this
      omega
    · exact hrange.2
    · rw [huNat]
      exact hreads.2

/-- The exact zero-copy state observes the original remainder allocation header. -/
theorem barrettZeroMemory_remainderHeader
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
    arrayHeader (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr) (UInt256.ofNat (remainderPtr fp k)) =
        UInt256.ofNat k := by
  have hrange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hremFit : remainderPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hsecondFit
    omega
  have hremNat := UInt256.toNat_ofNat_of_lt hremFit
  apply arrayHeader_eq_of_read
  · rw [hremNat, hzSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · rw [hremNat]
    exact le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega) hrange.1
  · exact hrange.2
  · rw [hremNat]
    exact barrettZeroMemory_remainderHeaderRead mem fp k divisorPtr hk hkPos hfp hmemSize
      hmemLe hgap hfirstFit hsource

/-- A nonzero top limb whose generated CLZ result is zero is already Knuth-normalized. -/
theorem normalizedTop_of_clz_zero
    (top : UInt256)
    (htopNe : top.toNat ≠ 0)
    (hshiftZero : (MultiLimbClz.clzResult top).n = 0) :
    UInt256.size ≤ 2 * top.toNat := by
  have hlower := MultiLimbClz.normalizedTop_lower htopNe
  have hrelation := MultiLimbClz.normalizedTop_relation top
  rw [hshiftZero, pow_zero, Nat.mul_one] at hrelation
  rw [hrelation] at hlower
  norm_num [UInt256.size] at hlower ⊢
  omega

/-- If a little-endian limb value reaches `radix^n * threshold`, its top limb reaches
`threshold`; the lower `n` limbs cannot carry a full additional radix power. -/
theorem top_toNat_ge_of_wordLimbsToNat_ge
    (low : List UInt256) (top : UInt256) (threshold : Nat)
    (hge : UInt256.size ^ low.length * threshold ≤
      Modexp.wordLimbsToNat (low ++ [top])) :
    threshold ≤ top.toNat := by
  have hlow := Modexp.wordLimbsToNat_lt_pow low
  rw [Modexp.wordLimbsToNat_append] at hge
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero] at hge
  by_contra hnot
  have htop : top.toNat + 1 ≤ threshold := by omega
  have hpow : 0 < UInt256.size ^ low.length := Nat.pow_pos (by
    norm_num [UInt256.size])
  nlinarith

/-- Positive normalization fills the fresh `v` payload but performs all later `u` writes in
bounds, so its final concrete byte extent is exactly the end of `v`. -/
theorem positiveMemory_size
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
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
    (barrettPositiveMemory mem aw fp k divisor top).size =
      normalizedDivisorPtr fp k + 32 + 32 * k := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor v u k
      (dividendLength k) shift
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
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k)
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  have htopWrite : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize]
    exact le_trans (huReadMem (dividendLength k) (by omega)) (by omega)
  change (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u
    (dividendLength k) dividendResult.carry).size = _
  have hstoreSize :
      (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u
        (dividendLength k) dividendResult.carry).size = dividendResult.memory.size := by
    simpa only [MultiLimbSchoolbookNormalization.storeDividendTopCarry,
      MultiLimbSchoolbookSingle.storeQuotient, arrayAddress] using
      MultiLimbSchoolbookSingle.storeQuotient_size_eq dividendResult.memory u
        (dividendLength k) dividendResult.carry htopWrite
  rw [hstoreSize, hdividendResultSize, hdivisorResultSize, hvSize]

/-- Positive normalization preserves the earlier remainder header through its frontier `v`
shift, in-place `u` shift, and final carry store. -/
theorem barrettPositiveMemory_remainderHeaderRead
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    (barrettPositiveMemory mem aw fp k divisor top).readWithPadding (remainderPtr fp k) 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor v u k
      (dividendLength k) shift
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hbase32 : 32 ≤ (barrettVMemory mem fp k).size := by rw [hvSize]; omega
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
  have hremBelowV0 : remainderPtr fp k + 32 ≤ (arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k 0 (by omega) hvFit]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  have hremDivisorRead : divisorResult.memory.readWithPadding (remainderPtr fp k) 32 =
      (barrettVMemory mem fp k).readWithPadding (remainderPtr fp k) 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k
        (remainderPtr fp k) (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) hremBelowV0
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremBelowU : ∀ j, j < dividendLength k ->
      remainderPtr fp k + 32 ≤ (arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDividendPtr quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize, hvSize]
    omega
  have hremDividendRead : dividendResult.memory.readWithPadding (remainderPtr fp k) 32 =
      divisorResult.memory.readWithPadding (remainderPtr fp k) 32 := by
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_below_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) (remainderPtr fp k) divisorResult.memory ⟨0⟩
        hdivisor32 (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using hremBelowU)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k)
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  have hremBelowTop : remainderPtr fp k + 32 ≤
      (arrayAddress u (dividendLength k)).toNat := by
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDividendPtr quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopWrite : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremTopRead : (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
      (remainderPtr fp k) 32 =
        dividendResult.memory.readWithPadding (remainderPtr fp k) 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 32).readWithPadding
        (remainderPtr fp k) 32 = _
    exact write32_read_below dividendResult.carry.toByteArray dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat (remainderPtr fp k)
      (by rw [toByteArray_size]) (by omega) hremBelowTop
  have hinitial := barrettVMemory_remainderHeaderRead mem fp k hk hkPos hfp hmemSize
    hmemLe hgap hfirstFit
  exact hremTopRead.trans (hremDividendRead.trans (hremDivisorRead.trans hinitial))

/-- Positive normalization preserves every complete pre-existing word below the first fresh
allocation. -/
theorem barrettPositiveMemory_read_below_fp
    (mem : ByteArray) (aw divisor top : UInt256) (fp k read : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread96 : 96 ≤ read) (hreadEnd : read + 32 ≤ fp) :
    (barrettPositiveMemory mem aw fp k divisor top).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor v u k
      (dividendLength k) shift
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hbase32 : 32 ≤ (barrettVMemory mem fp k).size := by rw [hvSize]; omega
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
  have hreadBelowV0 : read + 32 ≤ (arrayAddress v 0).toNat := by
    rw [hvFrontier 0 (by omega), hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hdivisorRead : divisorResult.memory.readWithPadding read 32 =
      (barrettVMemory mem fp k).readWithPadding read 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k read
        (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) hreadBelowV0
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hreadBelowU : ∀ j, j < dividendLength k ->
      read + 32 ≤ (arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize, hvSize]
    omega
  have hdividendRead : dividendResult.memory.readWithPadding read 32 =
      divisorResult.memory.readWithPadding read 32 := by
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_below_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) read divisorResult.memory ⟨0⟩ hdivisor32
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using hreadBelowU)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k)
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  have hreadBelowTop : read + 32 ≤ (arrayAddress u (dividendLength k)).toNat := by
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have htopWrite : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopRead : (barrettPositiveMemory mem aw fp k divisor top).readWithPadding read 32 =
      dividendResult.memory.readWithPadding read 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 32).readWithPadding read 32 = _
    exact write32_read_below dividendResult.carry.toByteArray dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat read (by rw [toByteArray_size])
      (by omega) hreadBelowTop
  exact htopRead.trans (hdividendRead.trans (hdivisorRead.trans
    ((barrettVMemory_read_below_fp mem fp k read hk hkPos hfp hmemSize hmemLe hgap
      hfirstFit hread96 hreadEnd).trans
        (barrettDivisionMemory_read_below_fp mem fp k read hk hfp hmemSize hmemLe hgap
          hfirstFit hread96 hreadEnd))))

/-- Positive normalization only writes above Solidity's allocator word, so the free pointer set
by the normalized-divisor allocation survives the complete normalization. -/
theorem barrettPositiveMemory_read64
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    (barrettPositiveMemory mem aw fp k divisor top).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor v u k
      (dividendLength k) shift
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hbase32 : 32 ≤ (barrettVMemory mem fp k).size := by rw [hvSize]; omega
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
  have h64BelowV0 : 64 + 32 ≤ (arrayAddress v 0).toNat := by
    rw [hvFrontier 0 (by omega)]
    rw [hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
    omega
  have h64DivisorRead : divisorResult.memory.readWithPadding 64 32 =
      (barrettVMemory mem fp k).readWithPadding 64 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k 64
        (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) h64BelowV0
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have h64BelowU : ∀ j, j < dividendLength k ->
      64 + 32 ≤ (arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize, hvSize]
    omega
  have h64DividendRead : dividendResult.memory.readWithPadding 64 32 =
      divisorResult.memory.readWithPadding 64 32 := by
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_below_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) 64 divisorResult.memory ⟨0⟩ hdivisor32
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using h64BelowU)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k)
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  have h64BelowTop : 64 + 32 ≤ (arrayAddress u (dividendLength k)).toNat := by
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDividendPtr quotientPtr remainderPtr
    omega
  have htopWrite : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have h64TopRead : (barrettPositiveMemory mem aw fp k divisor top).readWithPadding 64 32 =
      dividendResult.memory.readWithPadding 64 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 32).readWithPadding 64 32 = _
    exact write32_read_below dividendResult.carry.toByteArray dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 64 (by rw [toByteArray_size])
      (by omega) h64BelowTop
  exact h64TopRead.trans (h64DividendRead.trans (h64DivisorRead.trans
    (barrettVMemory_read64 mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit)))

/-- Zero-shift normalization copies only the fresh divisor payload, preserving the allocator
word set by the preceding allocation. -/
theorem barrettZeroMemory_read64
    (mem : ByteArray) (fp k divisorPtr : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hframe := write_read_below_end_from (barrettVMemory mem fp k)
    (barrettVMemory mem fp k) (divisorPtr + 32) (32 * k) 64 (by omega) hsource
    (by
      rw [hvSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      omega)
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  rw [← hvSize]
  exact hframe.trans
    (barrettVMemory_read64 mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit)

/-- Zero-shift normalization copies only the fresh divisor payload and preserves every complete
source word below the first fresh allocation. -/
theorem barrettZeroMemory_read_below_fp
    (mem : ByteArray) (fp k divisorPtr read : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size)
    (hread96 : 96 ≤ read) (hreadEnd : read + 32 ≤ fp) :
    (barrettZeroMemory mem fp k divisorPtr).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hframe := write_read_below_end_from (barrettVMemory mem fp k)
    (barrettVMemory mem fp k) (divisorPtr + 32) (32 * k) read (by omega) hsource
    (by
      rw [hvSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      omega)
  unfold barrettZeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  rw [← hvSize]
  exact hframe.trans
    ((barrettVMemory_read_below_fp mem fp k read hk hkPos hfp hmemSize hmemLe hgap
      hfirstFit hread96 hreadEnd).trans
        (barrettDivisionMemory_read_below_fp mem fp k read hk hfp hmemSize hmemLe hgap
          hfirstFit hread96 hreadEnd))

/-- The positive divisor frontier shift, in-place `u` shift, and final carry store preserve all
three allocator headers as raw 32-byte reads. -/
theorem barrettPositiveMemory_headerReads
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hkPos : 0 < k) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size) :
    (barrettPositiveMemory mem aw fp k divisor top).readWithPadding (quotientPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (quotientCount k)) ∧
      (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
          (normalizedDividendPtr fp k) 32 =
        UInt256.toByteArray (UInt256.ofNat (dividendLength k + 1)) ∧
      (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
          (normalizedDivisorPtr fp k) 32 = UInt256.toByteArray (UInt256.ofNat k) := by
  let u := UInt256.ofNat (normalizedDividendPtr fp k)
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let shift := (MultiLimbClz.clzResult top).n
  let divisorResult := barrettPositiveDivisorResult mem aw fp k divisor top
  let dividendResult := MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor v u k
      (dividendLength k) shift
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hbase32 : 32 ≤ (barrettVMemory mem fp k).size := by rw [hvSize]; omega
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
  have hqBelowV0 : quotientPtr fp k + 32 ≤ (arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k 0 (by omega) hvFit]
    unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  have huBelowV0 : normalizedDividendPtr fp k + 32 ≤ (arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k 0 (by omega) hvFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hvBelowV0 : normalizedDivisorPtr fp k + 32 ≤ (arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [normalizedDivisorArrayAddress_toNat fp k 0 (by omega) hvFit]
  have hqDivisorRead : divisorResult.memory.readWithPadding (quotientPtr fp k) 32 =
      (barrettVMemory mem fp k).readWithPadding (quotientPtr fp k) 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k
        (quotientPtr fp k) (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) hqBelowV0
  have huDivisorRead : divisorResult.memory.readWithPadding (normalizedDividendPtr fp k) 32 =
      (barrettVMemory mem fp k).readWithPadding (normalizedDividendPtr fp k) 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k
        (normalizedDividendPtr fp k) (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) huBelowV0
  have hvDivisorRead : divisorResult.memory.readWithPadding (normalizedDivisorPtr fp k) 32 =
      (barrettVMemory mem fp k).readWithPadding (normalizedDivisorPtr fp k) 32 := by
    simpa [divisorResult, barrettPositiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, v, shift] using
      shiftDivisor_read_below_frontier (barrettVWords aw fp k) divisor v shift 0 k
        (normalizedDivisorPtr fp k) (barrettVMemory mem fp k) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hvFrontier) hvBelowV0
  have huWrite : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqBelowU : ∀ j, j < dividendLength k ->
      quotientPtr fp k + 32 ≤ (arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huBelowU : ∀ j, j < dividendLength k ->
      normalizedDividendPtr fp k + 32 ≤ (arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    omega
  have huBelowV : ∀ j, j < dividendLength k ->
      (arrayAddress u j).toNat + 32 ≤ normalizedDivisorPtr fp k := by
    intro j hj
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k j (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize, hvSize]
    omega
  have hqDividendRead : dividendResult.memory.readWithPadding (quotientPtr fp k) 32 =
      divisorResult.memory.readWithPadding (quotientPtr fp k) 32 := by
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_below_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) (quotientPtr fp k) divisorResult.memory ⟨0⟩
        hdivisor32 (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using hqBelowU)
  have huDividendRead : dividendResult.memory.readWithPadding
      (normalizedDividendPtr fp k) 32 =
        divisorResult.memory.readWithPadding (normalizedDividendPtr fp k) 32 := by
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_below_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) (normalizedDividendPtr fp k) divisorResult.memory ⟨0⟩
        hdivisor32 (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using huBelowU)
  have hvDividendRead : dividendResult.memory.readWithPadding
      (normalizedDivisorPtr fp k) 32 =
        divisorResult.memory.readWithPadding (normalizedDivisorPtr fp k) 32 := by
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      Nat.zero_add] using shiftDivisor_read_above_inBounds (barrettVWords aw fp k) u u
        shift 0 (dividendLength k) (normalizedDivisorPtr fp k) divisorResult.memory ⟨0⟩
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using huBelowV)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (barrettVWords aw fp k) u u shift 0 (dividendLength k)
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult] using hsize
  have htopWrite : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopQBelow : quotientPtr fp k + 32 ≤ (arrayAddress u (dividendLength k)).toNat := by
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopUBelow : normalizedDividendPtr fp k + 32 ≤
      (arrayAddress u (dividendLength k)).toNat := by
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    omega
  have htopBelowV : (arrayAddress u (dividendLength k)).toNat + 32 ≤
      normalizedDivisorPtr fp k := by
    dsimp only [u]
    rw [normalizedDividendArrayAddress_toNat fp k (dividendLength k) (by omega) huFit]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hfinal32 : 32 ≤ dividendResult.memory.size := by
    rw [hdividendResultSize]
    exact hdivisor32
  have hqTopRead : (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
      (quotientPtr fp k) 32 = dividendResult.memory.readWithPadding (quotientPtr fp k) 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 32).readWithPadding (quotientPtr fp k) 32 = _
    exact toByteArray_write_read_below_padded_of_gap dividendResult.carry dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat (quotientPtr fp k) hfinal32 htopQBelow (by
        have husize : 0 < USize.size := by native_decide
        omega)
  have huTopRead : (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
      (normalizedDividendPtr fp k) 32 =
        dividendResult.memory.readWithPadding (normalizedDividendPtr fp k) 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 32).readWithPadding
        (normalizedDividendPtr fp k) 32 = _
    exact toByteArray_write_read_below_padded_of_gap dividendResult.carry dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat (normalizedDividendPtr fp k) hfinal32
      htopUBelow (by
        have husize : 0 < USize.size := by native_decide
        omega)
  have hvTopRead : (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
      (normalizedDivisorPtr fp k) 32 =
        dividendResult.memory.readWithPadding (normalizedDivisorPtr fp k) 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (arrayAddress u (dividendLength k)).toNat 32).readWithPadding
        (normalizedDivisorPtr fp k) 32 = _
    exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size]) htopWrite htopBelowV
  have hinitial := barrettVMemory_quHeaderReads mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hvInitial := barrettVMemory_vHeaderRead mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  exact ⟨hqTopRead.trans (hqDividendRead.trans (hqDivisorRead.trans hinitial.1)),
    huTopRead.trans (huDividendRead.trans (huDivisorRead.trans hinitial.2)),
    hvTopRead.trans (hvDividendRead.trans (hvDivisorRead.trans hvInitial))⟩

/-- The positive-normalization memory's raw header bytes are in bounds and active, so the
generated guarded loads observe all three concrete allocator lengths. -/
theorem barrettPositiveMemory_headers
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
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
    arrayHeader (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
        (UInt256.ofNat (quotientPtr fp k)) = UInt256.ofNat (quotientCount k) ∧
      arrayHeader (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDividendPtr fp k)) =
            UInt256.ofNat (dividendLength k + 1) ∧
      arrayHeader (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDivisorPtr fp k)) = UInt256.ofNat k := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hsize := positiveMemory_size mem aw divisor top fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hreads := barrettPositiveMemory_headerReads mem aw divisor top fp k hk hkPos hfp
    hmemSize hmemLe hgap hfirstFit huFit hvFit
  have hqPtrFit : quotientPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
    omega
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hvNat := UInt256.toNat_ofNat_of_lt hvPtrFit
  constructor
  · apply arrayHeader_eq_of_read
    · rw [hqNat, hsize]
      unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    · rw [hqNat]
      exact le_trans (by
        unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
          wordArrayPayloadSize
        omega) hrange.1
    · exact hrange.2
    · rw [hqNat]
      exact hreads.1
  constructor
  · apply arrayHeader_eq_of_read
    · rw [huNat, hsize]
      unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [huNat]
      exact le_trans (by
        unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
        omega) hrange.1
    · exact hrange.2
    · rw [huNat]
      exact hreads.2.1
  · apply arrayHeader_eq_of_read
    · rw [hvNat, hsize]
      omega
    · rw [hvNat]
      exact le_trans (by omega) hrange.1
    · exact hrange.2
    · rw [hvNat]
      exact hreads.2.2

/-- The exact positive-normalization state observes the original remainder allocation header. -/
theorem barrettPositiveMemory_remainderHeader
    (mem : ByteArray) (aw divisor top : UInt256) (fp k : Nat)
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
    arrayHeader (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
      (UInt256.ofNat (remainderPtr fp k)) = UInt256.ofNat k := by
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hsize := positiveMemory_size mem aw divisor top fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hremFit : remainderPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hsecondFit
    omega
  have hremNat := UInt256.toNat_ofNat_of_lt hremFit
  apply arrayHeader_eq_of_read
  · rw [hremNat, hsize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · rw [hremNat]
    exact le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega) hrange.1
  · exact hrange.2
  · rw [hremNat]
    exact barrettPositiveMemory_remainderHeaderRead mem aw divisor top fp k hk hkPos hfp
      hmemSize hmemLe hgap hfirstFit huFit hvFit

/-- The concrete positive shift makes the final divisor top limb Knuth-normalized. The proof
retains the complete source modulus and final shifted-divisor computations, using lower limbs
only through their strict inability to carry into the next radix position. -/
theorem barrettPositiveMemory_normalizedTop
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
        divisor 0 k) = modulusNat)
    (htopNe : top.toNat ≠ 0) :
    UInt256.size ≤ 2 *
      (arrayWord (barrettPositiveMemory mem aw fp k divisor top)
        (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k))
        (k - 1)).toNat := by
  let sourceLow := arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k)
    divisor 0 (k - 1)
  have hsourceSplit :
      arrayReadWords (barrettVMemory mem fp k) (barrettVWords aw fp k) divisor 0 k =
        sourceLow ++ [top] := by
    have hsplit := arrayReadWords_succ_append (barrettVMemory mem fp k)
      (barrettVWords aw fp k) divisor 0 (k - 1)
    have hcount : k - 1 + 1 = k := by omega
    rw [hcount] at hsplit
    simpa only [Nat.zero_add, htop, sourceLow] using hsplit
  have hsourceTopBound : UInt256.size ^ (k - 1) * top.toNat ≤ modulusNat := by
    rw [← hmodulus, hsourceSplit, Modexp.wordLimbsToNat_append,
      arrayReadWords_length]
    simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
    omega
  have hnormalizedSource : 2 ^ 255 ≤
      top.toNat * 2 ^ (MultiLimbClz.clzResult top).n := by
    rw [← MultiLimbClz.normalizedTop_relation top]
    exact MultiLimbClz.normalizedTop_lower htopNe
  have hscaledTop : UInt256.size ^ (k - 1) * 2 ^ 255 ≤
      modulusNat * 2 ^ (MultiLimbClz.clzResult top).n := by
    calc
      UInt256.size ^ (k - 1) * 2 ^ 255 ≤
          UInt256.size ^ (k - 1) *
            (top.toNat * 2 ^ (MultiLimbClz.clzResult top).n) :=
        Nat.mul_le_mul_left _ hnormalizedSource
      _ = (UInt256.size ^ (k - 1) * top.toNat) *
          2 ^ (MultiLimbClz.clzResult top).n := by ring
      _ ≤ modulusNat * 2 ^ (MultiLimbClz.clzResult top).n :=
        Nat.mul_le_mul_right _ hsourceTopBound
  let v := UInt256.ofNat (normalizedDivisorPtr fp k)
  let finalLow := arrayReadWords (barrettPositiveMemory mem aw fp k divisor top)
    (barrettVWords aw fp k) v 0 (k - 1)
  let finalTop := arrayWord (barrettPositiveMemory mem aw fp k divisor top)
    (barrettVWords aw fp k) v (k - 1)
  have hfinalSplit :
      arrayReadWords (barrettPositiveMemory mem aw fp k divisor top)
          (barrettVWords aw fp k) v 0 k = finalLow ++ [finalTop] := by
    have hsplit := arrayReadWords_succ_append
      (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k) v 0 (k - 1)
    have hcount : k - 1 + 1 = k := by omega
    rw [hcount] at hsplit
    simpa only [Nat.zero_add, finalLow, finalTop] using hsplit
  have hfinalValue := barrettPositiveDivisor_final_value mem aw divisor top fp k modulusNat
    hk hkPos hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit
    huFit hvFit hsourceMem htop hmodulus
  have hfinalBound : UInt256.size ^ finalLow.length * 2 ^ 255 ≤
      Modexp.wordLimbsToNat (finalLow ++ [finalTop]) := by
    rw [arrayReadWords_length]
    rw [← hfinalSplit]
    simpa only [v] using hscaledTop.trans_eq hfinalValue.symm
  have htopLower : 2 ^ 255 ≤ finalTop.toNat :=
    top_toNat_ge_of_wordLimbsToNat_ge finalLow finalTop (2 ^ 255) hfinalBound
  change UInt256.size ≤ 2 * finalTop.toNat
  norm_num [UInt256.size] at htopLower ⊢
  omega

/-- Concrete headers, top normalization, and byte extent determine the divisor decomposition
consumed by the generated q-hat loop; the caller does not supply `vRest`, `vSecond`, or `vTop`. -/
theorem continuationMemory_exists
    {mem : ByteArray} {aw u v quotient : UInt256}
    {count uCount quotientCount : Nat}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat count)
    (hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hnormalized : UInt256.size ≤ 2 * (arrayWord mem aw v (count - 1)).toNat)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size) :
    ∃ vRest vSecond vTop,
      vSecond = arrayWord mem aw v (count - 2) ∧
        vTop = arrayWord mem aw v (count - 1) ∧
        ContinuationMemory geometry vRest vSecond vTop mem := by
  let vRest := divisorReadSlice mem aw v 0 (count - 2)
  let vSecond := arrayWord mem aw v (count - 2)
  let vTop := arrayWord mem aw v (count - 1)
  have hsecond := divisorReadWord_eq_arrayWord mem aw v (count - 2) count (by
    have := geometry.hcountTwo
    omega) geometry.hvFit
  have htop := divisorReadWord_eq_arrayWord mem aw v (count - 1) count (by
    have := geometry.hcountTwo
    omega) geometry.hvFit
  have hvSlice := divisorReadSlice_lastTwo mem aw v count geometry.hcountTwo
  rw [hsecond, htop] at hvSlice
  refine ⟨vRest, vSecond, vTop, rfl, rfl, {
    huHeader := huHeader
    hvHeader := hvHeader
    hquotientHeader := hquotientHeader
    hvSlice := ?_
    hvSecondWord := rfl
    hnormalized := hnormalized
    hvMem := hvMem
    huTopMem := ?_
  }⟩
  · simpa only [vRest, vSecond, vTop] using hvSlice
  · exact le_trans geometry.htopBelowV (le_trans (by omega) hvMem)

/-- A bound on the complete concrete dividend implies the generated first-window bound. The
proof splits off the `quotientCount - 1` low words and identifies the remaining segment with the
actual guarded loads at the initial cursor. -/
theorem initialWindow_lt_radix_mul_of_full_bound
    {mem : ByteArray} {aw u v quotient : UInt256}
    {count uCount quotientCount : Nat}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (hfull : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (quotientCount + count)) <
      UInt256.size ^ (quotientCount - 1) *
        (UInt256.size * Modexp.wordLimbsToNat (divisorReadSlice mem aw v 0 count))) :
    MultiLimbSchoolbookDivisionSemantic.windowNat
        (windowReadSlice mem aw u quotientCount 0 count)
        (MultiLimbDivisionTrace.readWord mem aw
          (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
            (UInt256.ofNat quotientCount) (UInt256.ofNat count))) <
      UInt256.size * Modexp.wordLimbsToNat (divisorReadSlice mem aw v 0 count) := by
  have hcursorPos := geometry.hquotientCountPos
  have hmodel := windowModel_eq_arraySegment mem aw u quotientCount count hcursorPos
    geometry.hwindowRange (lt_of_le_of_lt geometry.hwindowRange (by
      norm_num [UInt256.size])) (by
        have := geometry.huFit
        omega)
  have hsplit := MultiLimbSchoolbookOuterComplete.arrayReadWords_add mem aw u 0
    (quotientCount - 1) (count + 1)
  have hcount : quotientCount - 1 + (count + 1) = quotientCount + count := by omega
  rw [hcount, Nat.zero_add] at hsplit
  have hvalue :
      Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 (quotientCount + count)) =
        Modexp.wordLimbsToNat (arrayReadWords mem aw u 0 (quotientCount - 1)) +
          UInt256.size ^ (quotientCount - 1) *
            MultiLimbSchoolbookDivisionSemantic.windowNat
              (windowReadSlice mem aw u quotientCount 0 count)
              (MultiLimbDivisionTrace.readWord mem aw
                (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
                  (UInt256.ofNat quotientCount) (UInt256.ofNat count))) := by
    rw [hsplit, Modexp.wordLimbsToNat_append,
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length, hmodel]
  have hpow : 0 < UInt256.size ^ (quotientCount - 1) := Nat.pow_pos (by
    norm_num [UInt256.size])
  rw [hvalue] at hfull
  nlinarith

/-- The Barrett numerator is strictly below the scale required for the initial Knuth window. The
common normalization factor is retained explicitly and cancels arithmetically; it is not omitted
from either computation. -/
theorem barrettFullBound
    (k shift modulusNat : Nat)
    (hkTwo : 2 ≤ k)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat) :
    UInt256.size ^ (2 * k) * 2 ^ shift <
      UInt256.size ^ (quotientCount k - 1) *
        (UInt256.size * (modulusNat * 2 ^ shift)) := by
  have hbase : 1 < UInt256.size := by norm_num [UInt256.size]
  have hpow : UInt256.size ^ (2 * k) < UInt256.size ^ (2 * k + 1) :=
    Nat.pow_lt_pow_right hbase (by omega)
  have hfactor :
      UInt256.size ^ (2 * k + 1) =
        UInt256.size ^ (quotientCount k - 1) *
          (UInt256.size * UInt256.size ^ (k - 1)) := by
    rw [quotientCount_eq]
    have hq : k + 2 - 1 = k + 1 := by omega
    have hexponent : 2 * k + 1 = (k + 1) + (1 + (k - 1)) := by omega
    rw [hq, hexponent, pow_add, pow_add, pow_one]
    rw [pow_add, pow_one]
  have hbaseBound : UInt256.size ^ (2 * k) <
      UInt256.size ^ (quotientCount k - 1) * (UInt256.size * modulusNat) := by
    calc
      UInt256.size ^ (2 * k) < UInt256.size ^ (2 * k + 1) := hpow
      _ = UInt256.size ^ (quotientCount k - 1) *
          (UInt256.size * UInt256.size ^ (k - 1)) := hfactor
      _ ≤ UInt256.size ^ (quotientCount k - 1) *
          (UInt256.size * modulusNat) := Nat.mul_le_mul_left _
            (Nat.mul_le_mul_left UInt256.size hmodulusLower)
  have hshiftPos : 0 < 2 ^ shift := by positivity
  have hscaled := Nat.mul_lt_mul_of_pos_right hbaseBound hshiftPos
  calc
    UInt256.size ^ (2 * k) * 2 ^ shift <
        (UInt256.size ^ (quotientCount k - 1) *
          (UInt256.size * modulusNat)) * 2 ^ shift := hscaled
    _ = UInt256.size ^ (quotientCount k - 1) *
        (UInt256.size * (modulusNat * 2 ^ shift)) := by ring

/-- Exact normalized-array values discharge the generated first-window premise for Barrett. -/
theorem barrettInitialWindowBound
    {mem : ByteArray} {aw u v quotient : UInt256}
    (k shift modulusNat : Nat)
    (geometry : ContinuationGeometry aw u v quotient k (dividendLength k + 1)
      (quotientCount k))
    (hkTwo : 2 ≤ k)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) * 2 ^ shift)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 k) =
      modulusNat * 2 ^ shift) :
    MultiLimbSchoolbookDivisionSemantic.windowNat
        (windowReadSlice mem aw u (quotientCount k) 0 k)
        (MultiLimbDivisionTrace.readWord mem aw
          (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
            (UInt256.ofNat (quotientCount k)) (UInt256.ofNat k))) <
      UInt256.size * Modexp.wordLimbsToNat (divisorReadSlice mem aw v 0 k) := by
  apply initialWindow_lt_radix_mul_of_full_bound geometry
  have hlength : quotientCount k + k = dividendLength k + 1 := by
    rw [quotientCount_eq]
    unfold dividendLength
    omega
  rw [hlength, hdividend,
    MultiLimbSchoolbookCompleteSemantic.divisorReadSlice_eq_arrayReadWords, hdivisor]
  exact barrettFullBound k shift modulusNat hkTwo hmodulusLower

/-- The concrete quotient payload ends before the `u` header, so every quotient digit store is
below every source word whose preservation is used by the final pure-value theorem. -/
theorem quotientBelowU
    {aw u v quotient : UInt256} {count uCount quotientCount : Nat}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount) :
    ∀ quotientIndex sourceIndex,
      quotientIndex < quotientCount -> sourceIndex < quotientIndex ->
      (arrayAddress quotient quotientIndex).toNat + 32 ≤
        (arrayAddress u sourceIndex).toNat := by
  intro quotientIndex sourceIndex hquotientIndex hsourceIndex
  have hquotientAddress := MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit
    quotient quotientIndex (by
      have := geometry.hquotientFit
      omega)
  have huAddress := MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit u sourceIndex (by
    have := geometry.huFit
    omega)
  have hquotientBelowU :
      quotient.toNat + 32 * (quotientIndex + 1) + 32 ≤ u.toNat := by
    exact le_trans (by
      have := hquotientIndex
      omega) geometry.hquotientPayloadBelowU
  unfold arrayAddress MultiLimbSchoolbookSingle.arrayAddress
    MultiLimbSchoolbookShort.arrayAddress
  rw [hquotientAddress, huAddress]
  exact le_trans hquotientBelowU (by omega)

/-- One concrete normalized Barrett memory constructs the complete descending schoolbook
execution. All estimate/correction choices, intermediate memories, steps, and gas are produced by
the executable continuation theorem. -/
theorem semanticContinuations_exists_of_memory
    {mem : ByteArray} {aw u shift ret rem v quotient normalizationMarker : UInt256}
    {count uCount quotientCount : Nat}
    (geometry : ContinuationGeometry aw u v quotient count uCount quotientCount)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat count)
    (hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat quotientCount)
    (hnormalized : UInt256.size ≤ 2 * (arrayWord mem aw v (count - 1)).toNat)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (hbound :
      MultiLimbSchoolbookDivisionSemantic.windowNat
          (windowReadSlice mem aw u quotientCount 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat quotientCount) (UInt256.ofNat count))) <
        UInt256.size * Modexp.wordLimbsToNat
          (divisorReadSlice mem aw v 0 count)) :
    ∃ (vRest : List UInt256) (vSecond vTop : UInt256) (inputs : List Nat)
        (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount ∧
        vTop = arrayWord mem aw v (count - 1) ∧
        MultiLimbSchoolbookOuterComplete.SemanticContinuations
          count uCount quotientCount u shift ret rem v quotient vTop normalizationMarker
          vRest vSecond ⟨0, 0⟩ inputs mem aw finalMem finalAw steps gas := by
  obtain ⟨vRest, vSecond, vTop, hvSecond, hvTop, memory⟩ :=
    continuationMemory_exists geometry huHeader
    hvHeader hquotientHeader hnormalized hvMem
  have hdivisor : divisorReadSlice mem aw v 0 count = vRest ++ [vSecond, vTop] :=
    memory.hvSlice
  have hbound' :
      MultiLimbSchoolbookDivisionSemantic.windowNat
          (windowReadSlice mem aw u quotientCount 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat quotientCount) (UInt256.ofNat count))) <
        UInt256.size * Modexp.wordLimbsToNat (vRest ++ [vSecond, vTop]) := by
    rw [← hdivisor]
    exact hbound
  let input := MultiLimbSchoolbookDivisionSemantic.windowNat
    (windowReadSlice mem aw u quotientCount 0 count)
    (MultiLimbDivisionTrace.readWord mem aw
      (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
        (UInt256.ofNat quotientCount) (UInt256.ofNat count)))
  have hwindow :
      MultiLimbSchoolbookDivisionSemantic.windowNat
          (windowReadSlice mem aw u quotientCount 0 count)
          (MultiLimbDivisionTrace.readWord mem aw
            (MultiLimbSchoolbookDivision.multiplySubtractUAddress u
              (UInt256.ofNat quotientCount) (UInt256.ofNat count))) =
        (⟨0, 0⟩ : MultiLimbSchoolbookOuterSemantic.DivisionFoldState).remainder *
            UInt256.size + input := by
    simp only [Nat.zero_mul, Nat.zero_add, input]
  obtain ⟨inputs, finalMem, finalAw, steps, gas, hlength, hsemantic⟩ :=
    MultiLimbSchoolbookContinuationExecutable.semanticContinuations_exists geometry memory
      geometry.hquotientCountPos (by omega) hwindow hbound'
  exact ⟨vRest, vSecond, vTop, inputs, finalMem, finalAw, steps, gas, hlength, hvTop,
    hsemantic⟩

/-- Exact Barrett numerator/divisor values and concrete final-memory facts construct the full
schoolbook continuation with no trace certificate supplied by the caller. -/
theorem barrettSemanticContinuations_exists_of_values
    {mem : ByteArray} {aw u ret rem v quotient normalizationMarker : UInt256}
    (k shift modulusNat : Nat)
    (geometry : ContinuationGeometry aw u v quotient k (dividendLength k + 1)
      (quotientCount k))
    (hkTwo : 2 ≤ k)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat (dividendLength k + 1))
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat k)
    (hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat (quotientCount k))
    (hnormalized : UInt256.size ≤ 2 * (arrayWord mem aw v (k - 1)).toNat)
    (hvMem : v.toNat + 32 * (k + 1) ≤ mem.size)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) * 2 ^ shift)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 k) =
      modulusNat * 2 ^ shift) :
    ∃ (vRest : List UInt256) (vSecond vTop : UInt256) (inputs : List Nat)
        (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        vTop = arrayWord mem aw v (k - 1) ∧
        MultiLimbSchoolbookOuterComplete.SemanticContinuations
          k (dividendLength k + 1) (quotientCount k) u (UInt256.ofNat shift) ret rem
          v quotient vTop normalizationMarker vRest vSecond ⟨0, 0⟩ inputs
          mem aw finalMem finalAw steps gas := by
  have hbound := barrettInitialWindowBound k shift modulusNat geometry hkTwo hmodulusLower
    hdividend hdivisor
  exact semanticContinuations_exists_of_memory (shift := UInt256.ofNat shift)
    (ret := ret) (rem := rem) (normalizationMarker := normalizationMarker)
    geometry huHeader hvHeader hquotientHeader hnormalized hvMem hbound

/-- The constructed concrete execution stores the pure Barrett constant. Exact steps and gas stay
attached to the same selected `SemanticContinuations` witness used for the value proof. -/
theorem barrettQuotient_exists_of_values
    {mem : ByteArray} {aw u ret rem v quotient normalizationMarker : UInt256}
    (k shift modulusNat : Nat)
    (geometry : ContinuationGeometry aw u v quotient k (dividendLength k + 1)
      (quotientCount k))
    (hkTwo : 2 ≤ k)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat (dividendLength k + 1))
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat k)
    (hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat (quotientCount k))
    (hnormalized : UInt256.size ≤ 2 * (arrayWord mem aw v (k - 1)).toNat)
    (hvMem : v.toNat + 32 * (k + 1) ≤ mem.size)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) * 2 ^ shift)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 k) =
      modulusNat * 2 ^ shift) :
    ∃ (vRest : List UInt256) (vSecond vTop : UInt256) (inputs : List Nat)
        (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        MultiLimbSchoolbookOuterComplete.SemanticContinuations
          k (dividendLength k + 1) (quotientCount k) u (UInt256.ofNat shift) ret rem
          v quotient vTop normalizationMarker vRest vSecond ⟨0, 0⟩ inputs
          mem aw finalMem finalAw steps gas ∧
        MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
            (MultiLimbSchoolbookOuterComplete.quotientReadNats
              finalMem finalAw quotient (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat := by
  obtain ⟨vRest, vSecond, vTop, inputs, finalMem, finalAw, steps, gas, hlength,
      hvTop, hsemantic⟩ := barrettSemanticContinuations_exists_of_values k shift modulusNat geometry
        hkTwo hmodulusLower huHeader hvHeader hquotientHeader hnormalized hvMem
        hdividend hdivisor
  have hnonempty : inputs ≠ [] := by
    intro hempty
    rw [hempty, List.length_nil, quotientCount_eq] at hlength
    omega
  have hdividend' : Modexp.wordLimbsToNat
      (arrayReadWords mem aw u 0 (inputs.length + k)) =
        UInt256.size ^ (2 * k) * 2 ^ shift := by
    have hcount : inputs.length + k = dividendLength k + 1 := by
      rw [hlength, quotientCount_eq]
      unfold dividendLength
      omega
    simpa only [hcount] using hdividend
  have hnormalized' : UInt256.size ≤ 2 * vTop.toNat := by
    rw [hvTop]
    exact hnormalized
  have hquotient := barrettConstantQuotient_eq hsemantic hlength hnonempty hnormalized'
    (quotientBelowU geometry) hdividend' hdivisor
  exact ⟨vRest, vSecond, vTop, inputs, finalMem, finalAw, steps, gas, hlength,
    hsemantic, hquotient⟩

/-- The same constructed semantic witness executes the generated loop at PC 5450 and proves the
pure Barrett quotient. The initial and terminal `RDx` states therefore use the selected trace's
own exact steps, gas, final memory, and active-word count. -/
theorem barrettQuotientExecution_exists_of_values
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw u ret rem v quotient vTop normalizationMarker : UInt256}
    (k shift modulusNat : Nat)
    (geometry : ContinuationGeometry aw u v quotient k (dividendLength k + 1)
      (quotientCount k))
    (hkTwo : 2 ≤ k)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat (dividendLength k + 1))
    (hvHeader : arrayHeader mem aw v = UInt256.ofNat k)
    (hquotientHeader : arrayHeader mem aw quotient = UInt256.ofNat (quotientCount k))
    (hvTop : arrayWord mem aw v (k - 1) = vTop)
    (hnormalized : UInt256.size ≤ 2 * vTop.toNat)
    (hvMem : v.toNat + 32 * (k + 1) ≤ mem.size)
    (hdividend : Modexp.wordLimbsToNat
        (arrayReadWords mem aw u 0 (dividendLength k + 1)) =
      UInt256.size ^ (2 * k) * 2 ^ shift)
    (hdivisor : Modexp.wordLimbsToNat (arrayReadWords mem aw v 0 k) =
      modulusNat * 2 ^ shift)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (UInt256.ofNat shift :: ret :: rem :: UInt256.ofNat (quotientCount k) ::
        UInt256.ofNat k :: v :: quotient :: u :: vTop :: normalizationMarker :: tail)
      mem aw rdata acc initialSteps initialGas) :
    ∃ (vRest : List UInt256) (vSecond : UInt256) (inputs : List Nat)
        (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        MultiLimbSchoolbookOuterComplete.SemanticContinuations
          k (dividendLength k + 1) (quotientCount k) u (UInt256.ofNat shift) ret rem
          v quotient vTop normalizationMarker vRest vSecond ⟨0, 0⟩ inputs
          mem aw finalMem finalAw steps gas ∧
        MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
            (MultiLimbSchoolbookOuterComplete.quotientReadNats
              finalMem finalAw quotient (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat ∧
        RDx runtimeBytecode ee g s0 ⟨5457⟩
          (⟨5894⟩ :: (⟨0⟩ : UInt256).isZero :: ⟨0⟩ :: UInt256.ofNat shift ::
            ret :: rem :: ⟨0⟩ :: UInt256.ofNat k :: v :: quotient :: u :: vTop ::
            normalizationMarker :: tail)
          finalMem finalAw rdata acc (initialSteps + steps + 5) (initialGas + gas + 13) := by
  have hnormalizedMemory : UInt256.size ≤ 2 * (arrayWord mem aw v (k - 1)).toNat := by
    rw [hvTop]
    exact hnormalized
  obtain ⟨vRest, vSecond, selectedTop, inputs, finalMem, finalAw, steps, gas, hlength,
      hselectedTop, hsemantic⟩ := barrettSemanticContinuations_exists_of_values
        k shift modulusNat geometry hkTwo hmodulusLower huHeader hvHeader hquotientHeader
        hnormalizedMemory hvMem hdividend hdivisor
  have htopEq : selectedTop = vTop := hselectedTop.trans hvTop
  rw [htopEq] at hsemantic
  have hnonempty : inputs ≠ [] := by
    intro hempty
    rw [hempty, List.length_nil, quotientCount_eq] at hlength
    omega
  have hdividend' : Modexp.wordLimbsToNat
      (arrayReadWords mem aw u 0 (inputs.length + k)) =
        UInt256.size ^ (2 * k) * 2 ^ shift := by
    have hcount : inputs.length + k = dividendLength k + 1 := by
      rw [hlength, quotientCount_eq]
      unfold dividendLength
      omega
    simpa only [hcount] using hdividend
  have hquotient := barrettConstantQuotient_eq hsemantic hlength hnonempty hnormalized
    (quotientBelowU geometry) hdividend' hdivisor
  have hexecution := MultiLimbSchoolbookOuterComplete.semanticDivisionLoopExact hsemantic
    hnonempty geometry.hcountWord hdepth (by simpa only [hlength] using h)
  exact ⟨vRest, vSecond, inputs, finalMem, finalAw, steps, gas, hlength, hsemantic,
    hquotient, hexecution⟩

/-- The selected quotient chain preserves the concrete return-loop geometry and both source and
remainder headers. The lower header premise is a raw allocator observation, not a postulated final
header. -/
theorem semanticContinuations_returnHeaders
    {mem finalMem : ByteArray} {aw finalAw : UInt256}
    {u shift ret rem v quotient vTop normalizationMarker : UInt256}
    {count uCount quotientCount : Nat}
    {vRest : List UInt256} {vSecond : UInt256}
    {state : DivisionFoldState} {inputs : List Nat} {steps gas : Nat}
    (hsemantic : MultiLimbSchoolbookOuterComplete.SemanticContinuations
      count uCount quotientCount u shift ret rem v quotient vTop normalizationMarker
      vRest vSecond state inputs mem aw finalMem finalAw steps gas)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat count)
    (hremMem : rem.toNat < mem.size)
    (hremBelowU : rem.toNat + 32 ≤ u.toNat + 32)
    (hremBelowQuotient : ∀ jj, jj < quotientCount ->
      rem.toNat + 32 ≤ (arrayAddress quotient jj).toNat)
    (hquotBelowU : ∀ jj, jj < quotientCount ->
      (arrayAddress quotient jj).toNat + 32 ≤ u.toNat) :
    finalAw = aw ∧ finalMem.size = mem.size ∧
      arrayHeader finalMem finalAw u = UInt256.ofNat uCount ∧
      arrayHeader finalMem finalAw rem = UInt256.ofNat count := by
  have hgeometry :=
    MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry hsemantic
  have huFinal :=
    MultiLimbSchoolbookContinuationExecutable.semanticContinuations_preserves_u_header
      hsemantic hquotBelowU
  have hremRead :=
    MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
      hremBelowU hremBelowQuotient
  have hremFinal : arrayHeader finalMem aw rem = arrayHeader mem aw rem :=
    arrayHeader_eq_of_readWithPadding_eq mem finalMem aw rem hremMem (by omega) hremRead
  refine ⟨hgeometry.1, hgeometry.2, ?_, ?_⟩
  · exact huFinal.trans huHeader
  · simpa only [hgeometry.1] using hremFinal.trans hremHeader

/-- In-bounds remainder-copy writes construct the complete zero-shift return certificate. Header
preservation is derived at every recursive state. -/
theorem validCopyRangeOfLayout
    {mem : ByteArray} {aw u rem : UInt256}
    (uCount kEff index count : Nat)
    (hfinish : index + count = kEff)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : ∀ i, i < kEff -> arrayAfterWord aw u i = aw)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : ∀ i, i < kEff -> arrayAfterWord aw rem i = aw)
    (huMem : u.toNat < mem.size)
    (hremMem : rem.toNat < mem.size)
    (hwrite : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hwriteBelowU : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ u.toNat)
    (hheaderBelowWrite : ∀ i, i < kEff ->
      rem.toNat + 32 ≤ (arrayAddress rem i).toNat) :
    MultiLimbSchoolbookZeroShiftRemainder.ValidCopy aw u rem uCount kEff index count mem := by
  induction count generalizing index mem with
  | zero =>
      exact MultiLimbSchoolbookZeroShiftRemainder.ValidCopy.zero index mem
  | succ remaining ih =>
      have hi : index < kEff := by omega
      let word := arrayWord mem aw u index
      let nextMem := MultiLimbSchoolbookDenormalization.storeRemainderWord mem rem index word
      have hnextSize : nextMem.size = mem.size := by
        simpa only [nextMem] using
          MultiLimbSchoolbookDenormalizationSemantic.storeRemainderWord_size_eq
            mem rem word index (hwrite index hi)
      have huRead : nextMem.readWithPadding u.toNat 32 =
          mem.readWithPadding u.toNat 32 := by
        dsimp only [nextMem]
        unfold MultiLimbSchoolbookDenormalization.storeRemainderWord
        exact write32_read_above_padded word.toByteArray mem (arrayAddress rem index).toNat
          u.toNat (by rw [toByteArray_size]) (hwrite index hi) (hwriteBelowU index hi)
      have hremRead : nextMem.readWithPadding rem.toNat 32 =
          mem.readWithPadding rem.toNat 32 := by
        dsimp only [nextMem]
        unfold MultiLimbSchoolbookDenormalization.storeRemainderWord
        exact write32_read_below word.toByteArray mem (arrayAddress rem index).toNat
          rem.toNat (by rw [toByteArray_size])
          (by have := hwrite index hi; omega) (hheaderBelowWrite index hi)
      have huHeaderNext : arrayHeader nextMem aw u = UInt256.ofNat uCount :=
        (arrayHeader_eq_of_readWithPadding_eq mem nextMem aw u huMem (by omega)
          huRead).trans huHeader
      have hremHeaderNext : arrayHeader nextMem aw rem = UInt256.ofNat kEff :=
        (arrayHeader_eq_of_readWithPadding_eq mem nextMem aw rem hremMem (by omega)
          hremRead).trans hremHeader
      refine MultiLimbSchoolbookZeroShiftRemainder.ValidCopy.step index remaining mem hi
        hkEffLe hkEffWord huCountWord huHeader huHeaderAw (huWordAw index hi)
        hremHeader hremHeaderAw (hremWordAw index hi) ?_
      exact ih (index := index + 1) (mem := nextMem) (by omega) huHeaderNext
        hremHeaderNext (by omega) (by omega)
        (by intro i hi'; rw [hnextSize]; exact hwrite i hi')

/-- Specialization of `validCopyRangeOfLayout` to all returned limbs. -/
theorem validCopyOfLayout
    {mem : ByteArray} {aw u rem : UInt256}
    (uCount kEff : Nat)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : ∀ i, i < kEff -> arrayAfterWord aw u i = aw)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : ∀ i, i < kEff -> arrayAfterWord aw rem i = aw)
    (huMem : u.toNat < mem.size)
    (hremMem : rem.toNat < mem.size)
    (hwrite : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hwriteBelowU : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ u.toNat)
    (hheaderBelowWrite : ∀ i, i < kEff ->
      rem.toNat + 32 ≤ (arrayAddress rem i).toNat) :
    MultiLimbSchoolbookZeroShiftRemainder.ValidCopy aw u rem uCount kEff 0 kEff mem := by
  exact validCopyRangeOfLayout uCount kEff 0 kEff (by omega) hkEffLe hkEffWord
    huCountWord huHeader huHeaderAw huWordAw hremHeader hremHeaderAw hremWordAw huMem
    hremMem hwrite hwriteBelowU hheaderBelowWrite

/-- In-bounds denormalization writes construct an arbitrary consecutive positive-shift return
certificate. Both stores in a nonterminal cycle preserve the real `uCount` header. -/
theorem validDenormalizeRangeOfLayout
    {mem : ByteArray} {aw u rem : UInt256}
    (uCount kEff shift index count : Nat)
    (hfinish : index + count = kEff)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : ∀ i, i < kEff -> arrayAfterWord aw u i = aw)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : ∀ i, i < kEff -> arrayAfterWord aw rem i = aw)
    (huMem : u.toNat < mem.size)
    (hremMem : rem.toNat < mem.size)
    (hwrite : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hwriteActive : ∀ i, i < kEff ->
      (arrayAddress rem i).toNat + 32 ≤ 32 * aw.toNat)
    (hwriteBelowU : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ u.toNat)
    (hheaderBelowWrite : ∀ i, i < kEff ->
      rem.toNat + 32 ≤ (arrayAddress rem i).toNat) :
    MultiLimbSchoolbookDenormalization.ValidDenormalize aw u rem uCount kEff shift
      index count mem := by
  induction count generalizing index mem with
  | zero =>
      exact MultiLimbSchoolbookDenormalization.ValidDenormalize.zero index mem
  | succ remaining ih =>
      have hi : index < kEff := by omega
      cases remaining with
      | zero =>
          exact MultiLimbSchoolbookDenormalization.ValidDenormalize.terminal index mem
            (by omega) hkEffLe hkEffWord huCountWord huHeader huHeaderAw
            (huWordAw index hi) hremHeader hremHeaderAw (hremWordAw index hi)
      | succ rest =>
          have hiNext : index + 1 < kEff := by omega
          let word := arrayWord mem aw u index
          let low := MultiLimbSchoolbookDenormalization.denormalizedLowWord word shift
          let lowMem := MultiLimbSchoolbookDenormalization.storeRemainderWord mem rem index low
          let next := arrayWord lowMem aw u (index + 1)
          let output := MultiLimbSchoolbookDenormalization.denormalizedWord word next shift
          let nextMem :=
            MultiLimbSchoolbookDenormalization.storeRemainderWord lowMem rem index output
          have hlowSize : lowMem.size = mem.size := by
            simpa only [lowMem] using
              MultiLimbSchoolbookDenormalizationSemantic.storeRemainderWord_size_eq
                mem rem low index (hwrite index hi)
          have huLowRead : lowMem.readWithPadding u.toNat 32 =
              mem.readWithPadding u.toNat 32 := by
            dsimp only [lowMem]
            unfold MultiLimbSchoolbookDenormalization.storeRemainderWord
            exact write32_read_above_padded low.toByteArray mem (arrayAddress rem index).toNat
              u.toNat (by rw [toByteArray_size]) (hwrite index hi) (hwriteBelowU index hi)
          have hremLowRead : lowMem.readWithPadding rem.toNat 32 =
              mem.readWithPadding rem.toNat 32 := by
            dsimp only [lowMem]
            unfold MultiLimbSchoolbookDenormalization.storeRemainderWord
            exact write32_read_below low.toByteArray mem (arrayAddress rem index).toNat
              rem.toNat (by rw [toByteArray_size])
              (by have := hwrite index hi; omega) (hheaderBelowWrite index hi)
          have huHeaderLow : arrayHeader lowMem aw u = UInt256.ofNat uCount :=
            (arrayHeader_eq_of_readWithPadding_eq mem lowMem aw u huMem (by omega)
              huLowRead).trans huHeader
          have hremHeaderLow : arrayHeader lowMem aw rem = UInt256.ofNat kEff :=
            (arrayHeader_eq_of_readWithPadding_eq mem lowMem aw rem hremMem (by omega)
              hremLowRead).trans hremHeader
          have hremLowWord : arrayWord lowMem aw rem index = low := by
            simpa only [lowMem] using
              MultiLimbSchoolbookDenormalizationSemantic.arrayWord_storeRemainder_self
                mem aw rem low index hawFit (hwrite index hi) (hwriteActive index hi)
          have hnextSize : nextMem.size = mem.size := by
            have hsize :=
              MultiLimbSchoolbookDenormalizationSemantic.storeRemainderWord_size_eq
                lowMem rem output index (by rw [hlowSize]; exact hwrite index hi)
            simpa only [nextMem, hlowSize] using hsize
          have huNextRead : nextMem.readWithPadding u.toNat 32 =
              lowMem.readWithPadding u.toNat 32 := by
            dsimp only [nextMem]
            unfold MultiLimbSchoolbookDenormalization.storeRemainderWord
            exact write32_read_above_padded output.toByteArray lowMem
              (arrayAddress rem index).toNat u.toNat (by rw [toByteArray_size])
              (by rw [hlowSize]; exact hwrite index hi) (hwriteBelowU index hi)
          have hremNextRead : nextMem.readWithPadding rem.toNat 32 =
              lowMem.readWithPadding rem.toNat 32 := by
            dsimp only [nextMem]
            unfold MultiLimbSchoolbookDenormalization.storeRemainderWord
            exact write32_read_below output.toByteArray lowMem (arrayAddress rem index).toNat
              rem.toNat (by rw [toByteArray_size])
              (by rw [hlowSize]; have := hwrite index hi; omega)
              (hheaderBelowWrite index hi)
          have huHeaderNext : arrayHeader nextMem aw u = UInt256.ofNat uCount :=
            (arrayHeader_eq_of_readWithPadding_eq lowMem nextMem aw u (by omega) (by omega)
              huNextRead).trans huHeaderLow
          have hremHeaderNext : arrayHeader nextMem aw rem = UInt256.ofNat kEff :=
            (arrayHeader_eq_of_readWithPadding_eq lowMem nextMem aw rem (by omega) (by omega)
              hremNextRead).trans hremHeaderLow
          refine MultiLimbSchoolbookDenormalization.ValidDenormalize.step index rest mem
            hiNext hkEffLe hkEffWord huCountWord huHeader huHeaderAw (huWordAw index hi)
            hremHeader hremHeaderAw (hremWordAw index hi) huHeaderLow
            (huWordAw (index + 1) hiNext) hremHeaderLow ?_ ?_
          · simpa only [word, low] using hremLowWord
          · exact ih (index := index + 1) (mem := nextMem) (by omega) huHeaderNext
              hremHeaderNext (by omega) (by omega)
              (by intro i hi'; rw [hnextSize]; exact hwrite i hi')

/-- Specialization of `validDenormalizeRangeOfLayout` to all returned limbs. -/
theorem validDenormalizeOfLayout
    {mem : ByteArray} {aw u rem : UInt256}
    (uCount kEff shift : Nat)
    (hkEffLe : kEff ≤ uCount)
    (hkEffWord : kEff < UInt256.size)
    (huCountWord : uCount < UInt256.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (huHeader : arrayHeader mem aw u = UInt256.ofNat uCount)
    (huHeaderAw : arrayAfterHeader aw u = aw)
    (huWordAw : ∀ i, i < kEff -> arrayAfterWord aw u i = aw)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat kEff)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremWordAw : ∀ i, i < kEff -> arrayAfterWord aw rem i = aw)
    (huMem : u.toNat < mem.size)
    (hremMem : rem.toNat < mem.size)
    (hwrite : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hwriteActive : ∀ i, i < kEff ->
      (arrayAddress rem i).toNat + 32 ≤ 32 * aw.toNat)
    (hwriteBelowU : ∀ i, i < kEff -> (arrayAddress rem i).toNat + 32 ≤ u.toNat)
    (hheaderBelowWrite : ∀ i, i < kEff ->
      rem.toNat + 32 ≤ (arrayAddress rem i).toNat) :
    MultiLimbSchoolbookDenormalization.ValidDenormalize aw u rem uCount kEff shift
      0 kEff mem := by
  exact validDenormalizeRangeOfLayout uCount kEff shift 0 kEff (by omega) hkEffLe
    hkEffWord huCountWord hawFit huHeader huHeaderAw huWordAw hremHeader hremHeaderAw
    hremWordAw huMem hremMem hwrite hwriteActive hwriteBelowU hheaderBelowWrite

/-- The concrete positive-CLZ normalization memory constructs the complete schoolbook execution
and stores the pure Barrett constant. No array header, normalized-top fact, continuation trace,
result memory, or gas value is supplied by the caller. -/
theorem barrettPositiveQuotient_exists
    {mem : ByteArray} {aw divisor top ret rem : UInt256}
    (fp k modulusNat : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
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
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (htopNe : top.toNat ≠ 0) :
    ∃ (vRest : List UInt256) (vSecond vTop : UInt256) (inputs : List Nat)
        (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        MultiLimbSchoolbookOuterComplete.SemanticContinuations
          k (dividendLength k + 1) (quotientCount k)
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (MultiLimbClz.clzResult top).n) ret rem
          (UInt256.ofNat (normalizedDivisorPtr fp k))
          (UInt256.ofNat (quotientPtr fp k)) vTop ⟨1⟩ vRest vSecond ⟨0, 0⟩ inputs
          (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
          finalMem finalAw steps gas ∧
        MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
            (MultiLimbSchoolbookOuterComplete.quotientReadNats finalMem finalAw
              (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat := by
  have hkPos : 0 < k := by omega
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
  have hheaders := barrettPositiveMemory_headers mem aw divisor top fp k hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hnormalized := barrettPositiveMemory_normalizedTop mem aw divisor top fp k modulusNat
    hk hkPos hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit
    huFit hvFit hsourceMem htop hmodulus htopNe
  have hsize := positiveMemory_size mem aw divisor top fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvMem : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat + 32 * (k + 1) ≤
      (barrettPositiveMemory mem aw fp k divisor top).size := by
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit, hsize]
    omega
  have hdividend := barrettPositiveDividend_value mem aw divisor top fp k hk hkPos
    hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hdivisor := barrettPositiveDivisor_final_value mem aw divisor top fp k modulusNat
    hk hkPos hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit
    huFit hvFit hsourceMem htop hmodulus
  exact barrettQuotient_exists_of_values k (MultiLimbClz.clzResult top).n modulusNat
    geometry hkTwo hmodulusLower hheaders.2.1 hheaders.2.2 hheaders.1 hnormalized hvMem
    hdividend hdivisor

/-- The concrete zero-CLZ normalization memory constructs the complete schoolbook execution and
stores the pure Barrett constant. No array header, continuation trace, result memory, or gas value
is supplied by the caller. -/
theorem barrettZeroQuotient_exists
    {mem : ByteArray} {aw ret rem top : UInt256}
    (fp k divisorPtr modulusNat : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (htop : arrayWord (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1) = top)
    (htopNe : top.toNat ≠ 0)
    (hshiftZero : (MultiLimbClz.clzResult top).n = 0) :
    ∃ (vRest : List UInt256) (vSecond vTop : UInt256) (inputs : List Nat)
        (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        MultiLimbSchoolbookOuterComplete.SemanticContinuations
          k (dividendLength k + 1) (quotientCount k)
          (UInt256.ofNat (normalizedDividendPtr fp k)) (UInt256.ofNat 0) ret rem
          (UInt256.ofNat (normalizedDivisorPtr fp k))
          (UInt256.ofNat (quotientPtr fp k)) vTop ⟨0⟩ vRest vSecond ⟨0, 0⟩ inputs
          (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr)
          finalMem finalAw steps gas ∧
        MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
            (MultiLimbSchoolbookOuterComplete.quotientReadNats finalMem finalAw
              (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat := by
  have hkPos : 0 < k := by omega
  let geometry := zeroContinuationGeometry aw fp k divisorPtr hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hheaders := barrettZeroMemory_quHeaders mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hvHeader := barrettZeroMemory_vHeader mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hnormalized : UInt256.size ≤ 2 *
      (arrayWord (barrettZeroMemory mem fp k divisorPtr)
        (barrettZeroWords aw fp k divisorPtr)
        (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)).toNat := by
    rw [htop]
    exact normalizedTop_of_clz_zero top htopNe hshiftZero
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvMem : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat + 32 * (k + 1) ≤
      (barrettZeroMemory mem fp k divisorPtr).size := by
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit, hzSize]
    omega
  have hdividend := barrettZeroDividend_value mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hdivisor := barrettZeroDivisor_value mem aw fp k divisorPtr modulusNat hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit
    hsource hdivisorFit hmodulus
  exact barrettQuotient_exists_of_values k 0 modulusNat geometry hkTwo hmodulusLower
    hheaders.2 hvHeader hheaders.1 hnormalized hvMem (by
      simpa only [pow_zero, Nat.mul_one] using hdividend) (by
      simpa only [pow_zero, Nat.mul_one] using hdivisor)

/-- A selected zero-CLZ quotient continuation determines the complete direct-copy return
certificate for the concrete Barrett remainder allocation. -/
theorem barrettZeroValidCopy
    {mem : ByteArray} {aw ret vTop : UInt256}
    {vRest : List UInt256} {vSecond : UInt256} {inputs : List Nat}
    {finalMem : ByteArray} {finalAw : UInt256} {steps gas : Nat}
    (fp k divisorPtr : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    (hsemantic : MultiLimbSchoolbookOuterComplete.SemanticContinuations
      k (dividendLength k + 1) (quotientCount k)
      (UInt256.ofNat (normalizedDividendPtr fp k)) ⟨0⟩ ret
      (UInt256.ofNat (remainderPtr fp k))
      (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (quotientPtr fp k)) vTop ⟨0⟩ vRest vSecond ⟨0, 0⟩ inputs
      (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr)
      finalMem finalAw steps gas) :
    MultiLimbSchoolbookZeroShiftRemainder.ValidCopy finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (remainderPtr fp k)) (dividendLength k + 1) k 0 k finalMem := by
  have hkPos : 0 < k := by omega
  let geometry := zeroContinuationGeometry aw fp k divisorPtr hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hheaders := barrettZeroMemory_quHeaders mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hremHeader := barrettZeroMemory_remainderHeader mem aw fp k divisorPtr hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit
    hsource
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hrange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hremFit : remainderPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hsecondFit
    omega
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hqPtrFit : quotientPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hquotientFit
    omega
  have hremNat := UInt256.toNat_ofNat_of_lt hremFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have hreturn := semanticContinuations_returnHeaders hsemantic hheaders.2 hremHeader
    (by
      rw [hremNat, hzSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega)
    (by rw [hremNat, huNat]; unfold normalizedDividendPtr quotientPtr; omega)
    (by
      intro jj hj
      rw [hremNat, quotientArrayAddress_toNat fp k jj hj hquotientFit]
      unfold quotientPtr
      omega)
    (by
      intro jj hj
      rw [quotientArrayAddress_toNat fp k jj hj hquotientFit, huNat]
      unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hremActive : remainderPtr fp k + 32 + 32 * k ≤ 32 * finalAw.toNat := by
    rw [hreturn.1]
    exact le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega) hrange.1
  have huHeaderAw : arrayAfterHeader finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k)) = finalAw := by
    rw [hreturn.1]
    exact geometry.huHeaderAw
  have huWordAw : ∀ i, i < k -> arrayAfterWord finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k)) i = finalAw := by
    intro i hi
    rw [hreturn.1]
    exact geometry.huWordAw i (by unfold dividendLength; omega)
  have hremHeaderAw : arrayAfterHeader finalAw (UInt256.ofNat (remainderPtr fp k)) =
      finalAw := by
    apply arrayAfterHeader_eq_of_active
    rw [hremNat]
    omega
  have hremWordAw : ∀ i, i < k ->
      arrayAfterWord finalAw (UInt256.ofNat (remainderPtr fp k)) i = finalAw := by
    intro i hi
    apply arrayAfterWord_eq_of_active
    change (arrayAddress (UInt256.ofNat (remainderPtr fp k)) i).toNat + 32 ≤
      32 * finalAw.toNat
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit]
    omega
  have huCountWord : dividendLength k + 1 < UInt256.size := by
    unfold dividendLength
    exact lt_of_le_of_lt (by omega : 2 * k + 1 + 1 ≤ 66)
      (by norm_num [UInt256.size])
  apply validCopyOfLayout (dividendLength k + 1) k (by unfold dividendLength; omega)
    geometry.hcountWord huCountWord hreturn.2.2.1 huHeaderAw huWordAw
    hreturn.2.2.2 hremHeaderAw hremWordAw
  · rw [huNat, hreturn.2.1, hzSize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hremNat, hreturn.2.1, hzSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · intro i hi
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit, hreturn.2.1, hzSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · intro i hi
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit, huNat]
    unfold normalizedDividendPtr quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [hremNat, remainderArrayAddress_toNat fp k i hi hsecondFit]
    omega

/-- A selected positive-CLZ quotient continuation determines the complete denormalization return
certificate for the concrete Barrett remainder allocation. -/
theorem barrettPositiveValidDenormalize
    {mem : ByteArray} {aw divisor top ret vTop : UInt256}
    {vRest : List UInt256} {vSecond : UInt256} {inputs : List Nat}
    {finalMem : ByteArray} {finalAw : UInt256} {steps gas : Nat}
    (fp k : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    (hsemantic : MultiLimbSchoolbookOuterComplete.SemanticContinuations
      k (dividendLength k + 1) (quotientCount k)
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (MultiLimbClz.clzResult top).n) ret
      (UInt256.ofNat (remainderPtr fp k))
      (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (quotientPtr fp k)) vTop ⟨1⟩ vRest vSecond ⟨0, 0⟩ inputs
      (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
      finalMem finalAw steps gas) :
    MultiLimbSchoolbookDenormalization.ValidDenormalize finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (remainderPtr fp k)) (dividendLength k + 1) k
      (MultiLimbClz.clzResult top).n 0 k finalMem := by
  have hkPos : 0 < k := by omega
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
  have hheaders := barrettPositiveMemory_headers mem aw divisor top fp k hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hremHeader := barrettPositiveMemory_remainderHeader mem aw divisor top fp k hk hkPos
    hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hsize := positiveMemory_size mem aw divisor top fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hremFit : remainderPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hsecondFit
    omega
  have huPtrFit : normalizedDividendPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hremNat := UInt256.toNat_ofNat_of_lt hremFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hreturn := semanticContinuations_returnHeaders hsemantic hheaders.2.1 hremHeader
    (by
      rw [hremNat, hsize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega)
    (by rw [hremNat, huNat]; unfold normalizedDividendPtr quotientPtr; omega)
    (by
      intro jj hj
      rw [hremNat, quotientArrayAddress_toNat fp k jj hj hquotientFit]
      unfold quotientPtr
      omega)
    (by
      intro jj hj
      rw [quotientArrayAddress_toNat fp k jj hj hquotientFit, huNat]
      unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have hremActive : remainderPtr fp k + 32 + 32 * k ≤ 32 * finalAw.toNat := by
    rw [hreturn.1]
    exact le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega) hrange.1
  have huHeaderAw : arrayAfterHeader finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k)) = finalAw := by
    rw [hreturn.1]
    exact geometry.huHeaderAw
  have huWordAw : ∀ i, i < k -> arrayAfterWord finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k)) i = finalAw := by
    intro i hi
    rw [hreturn.1]
    exact geometry.huWordAw i (by unfold dividendLength; omega)
  have hremHeaderAw : arrayAfterHeader finalAw (UInt256.ofNat (remainderPtr fp k)) =
      finalAw := by
    apply arrayAfterHeader_eq_of_active
    rw [hremNat]
    omega
  have hremWordAw : ∀ i, i < k ->
      arrayAfterWord finalAw (UInt256.ofNat (remainderPtr fp k)) i = finalAw := by
    intro i hi
    apply arrayAfterWord_eq_of_active
    change (arrayAddress (UInt256.ofNat (remainderPtr fp k)) i).toNat + 32 ≤
      32 * finalAw.toNat
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit]
    omega
  have huCountWord : dividendLength k + 1 < UInt256.size := by
    unfold dividendLength
    exact lt_of_le_of_lt (by omega : 2 * k + 1 + 1 ≤ 66)
      (by norm_num [UInt256.size])
  have hfinalAwFit : finalAw.toNat * 32 < UInt256.size := by
    rw [hreturn.1]
    exact hrange.2
  apply validDenormalizeOfLayout (dividendLength k + 1) k
    (MultiLimbClz.clzResult top).n (by unfold dividendLength; omega)
    geometry.hcountWord huCountWord hfinalAwFit hreturn.2.2.1 huHeaderAw huWordAw
    hreturn.2.2.2 hremHeaderAw hremWordAw
  · rw [huNat, hreturn.2.1, hsize]
    unfold normalizedDivisorPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hremNat, hreturn.2.1, hsize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · intro i hi
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit, hreturn.2.1, hsize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · intro i hi
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit]
    omega
  · intro i hi
    rw [remainderArrayAddress_toNat fp k i hi hsecondFit, huNat]
    unfold normalizedDividendPtr quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [hremNat, remainderArrayAddress_toNat fp k i hi hsecondFit]
    omega

/-- Execute the complete positive-CLZ quotient and denormalization return to the concrete caller
while retaining the pure Barrett quotient and exact selected gas. -/
theorem barrettPositiveDivisionReturn_exists
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw divisor top : UInt256}
    (fp k modulusNat retPc : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
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
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (htopNe : top.toNat ≠ 0)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (UInt256.ofNat (MultiLimbClz.clzResult top).n :: UInt256.ofNat retPc ::
        UInt256.ofNat (remainderPtr fp k) :: UInt256.ofNat (quotientCount k) ::
        UInt256.ofNat k :: UInt256.ofNat (normalizedDivisorPtr fp k) ::
        UInt256.ofNat (quotientPtr fp k) :: UInt256.ofNat (normalizedDividendPtr fp k) ::
        arrayWord (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1) :: ⟨1⟩ :: tail)
      (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
      rdata acc initialSteps initialGas) :
    ∃ (inputs : List Nat) (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        finalAw = barrettVWords aw fp k ∧
        finalMem.size = normalizedDivisorPtr fp k + 32 + 32 * k ∧
        (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
          ).memory.readWithPadding 64 32 = UInt256.toByteArray
            (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) ∧
        (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
          ).memory.readWithPadding (quotientPtr fp k) 32 =
            UInt256.toByteArray (UInt256.ofNat (quotientCount k)) ∧
        (∀ read, 96 ≤ read → read + 32 ≤ fp →
          (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
            (UInt256.ofNat (normalizedDividendPtr fp k))
            (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
            ).memory.readWithPadding read 32 = mem.readWithPadding read 32) ∧
        MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
            (MultiLimbSchoolbookOuterComplete.quotientReadNats finalMem finalAw
              (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat ∧
        let result := MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
        RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
          (UInt256.ofNat (remainderPtr fp k) :: UInt256.ofNat (quotientPtr fp k) :: tail)
          result.memory finalAw rdata acc
          (((initialSteps + steps + 5) + 23) + result.steps + 6)
          (((initialGas + gas + 13) + 73) + result.gas + 26) := by
  have hkPos : 0 < k := by omega
  have hshiftBound : (MultiLimbClz.clzResult top).n < 256 := by
    have hn := MultiLimbClz.clzResult_n_le top
    omega
  let geometry := positiveContinuationGeometry aw fp k hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit
  let normalizedTop := arrayWord (barrettPositiveMemory mem aw fp k divisor top)
    (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)
  have hheaders := barrettPositiveMemory_headers mem aw divisor top fp k hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hnormalized := barrettPositiveMemory_normalizedTop mem aw divisor top fp k modulusNat
    hk hkPos hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit
    huFit hvFit hsourceMem htop hmodulus htopNe
  have hsize := positiveMemory_size mem aw divisor top fp k hk hkPos hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvMem : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat + 32 * (k + 1) ≤
      (barrettPositiveMemory mem aw fp k divisor top).size := by
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit, hsize]
    omega
  have hdividend := barrettPositiveDividend_value mem aw divisor top fp k hk hkPos
    hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  have hdivisor := barrettPositiveDivisor_final_value mem aw divisor top fp k modulusNat
    hk hkPos hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit
    huFit hvFit hsourceMem htop hmodulus
  obtain ⟨vRest, vSecond, inputs, finalMem, finalAw, steps, gas, hlength, hsemantic,
      hquotient, hexecution⟩ := barrettQuotientExecution_exists_of_values k
        (MultiLimbClz.clzResult top).n modulusNat geometry hkTwo hmodulusLower hheaders.2.1
        hheaders.2.2 hheaders.1 (by rfl) hnormalized hvMem hdividend hdivisor hdepth
        (by simpa only [normalizedTop] using h)
  have hdenormalize := barrettPositiveValidDenormalize fp k hkTwo hk hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hsemantic
  have hfinalSize : finalMem.size = normalizedDivisorPtr fp k + 32 + 32 * k := by
    rw [(MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry hsemantic).2]
    exact hsize
  have hfinalAw : finalAw = barrettVWords aw fp k :=
    (MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry hsemantic).1
  have hquotientRead64 : finalMem.readWithPadding 64 32 =
      (barrettPositiveMemory mem aw fp k divisor top).readWithPadding 64 32 := by
    apply MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
    · rw [UInt256.toNat_ofNat_of_lt (by
          unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
            wordArrayPayloadSize at huFit ⊢
          omega)]
      unfold normalizedDividendPtr quotientPtr remainderPtr
      omega
    · intro jj hj
      change 64 + 32 ≤ (arrayAddress (UInt256.ofNat (quotientPtr fp k)) jj).toNat
      rw [quotientArrayAddress_toNat fp k jj hj hquotientFit]
      unfold quotientPtr remainderPtr
      omega
  have hresultRead64 :
      (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
        (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
        ).memory.readWithPadding 64 32 = UInt256.toByteArray
          (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) := by
    have hframe :=
      MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_preserves_read_below
        finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 64 0 k finalMem
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit, hfinalSize]
          unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit]
          unfold remainderPtr
          omega)
    exact hframe.trans (hquotientRead64.trans
      (barrettPositiveMemory_read64 mem aw divisor top fp k hk hkPos hfp hmemSize
        hmemLe hgap hfirstFit huFit hvFit))
  have hresultReadBelow : ∀ read, 96 ≤ read → read + 32 ≤ fp →
      (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
        (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
        ).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
    intro read hread96 hreadEnd
    have hquotientRead : finalMem.readWithPadding read 32 =
        (barrettPositiveMemory mem aw fp k divisor top).readWithPadding read 32 := by
      apply MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
      · rw [UInt256.toNat_ofNat_of_lt (by
            unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
              wordArrayPayloadSize at huFit ⊢
            omega)]
        unfold normalizedDividendPtr quotientPtr remainderPtr
        omega
      · intro jj hj
        change read + 32 ≤ (arrayAddress (UInt256.ofNat (quotientPtr fp k)) jj).toNat
        rw [quotientArrayAddress_toNat fp k jj hj hquotientFit]
        unfold quotientPtr remainderPtr
        omega
    have hframe :=
      MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_preserves_read_below
        finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n read 0 k finalMem
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit, hfinalSize]
          unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit]
          unfold remainderPtr
          omega)
    exact hframe.trans (hquotientRead.trans
      (barrettPositiveMemory_read_below_fp mem aw divisor top fp k read hk hkPos hfp
        hmemSize hmemLe hgap hfirstFit huFit hvFit hread96 hreadEnd))
  have hresultQuotientHeader :
      (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
        (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
        ).memory.readWithPadding (quotientPtr fp k) 32 =
          UInt256.toByteArray (UInt256.ofNat (quotientCount k)) := by
    have hquotientRead : finalMem.readWithPadding (quotientPtr fp k) 32 =
        (barrettPositiveMemory mem aw fp k divisor top).readWithPadding
          (quotientPtr fp k) 32 := by
      apply MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
      · rw [UInt256.toNat_ofNat_of_lt (by
            unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
              wordArrayPayloadSize at huFit ⊢
            omega)]
        unfold normalizedDividendPtr
        omega
      · intro jj hj
        change quotientPtr fp k + 32 ≤
          (arrayAddress (UInt256.ofNat (quotientPtr fp k)) jj).toNat
        rw [quotientArrayAddress_toNat fp k jj hj hquotientFit]
        omega
    have hframe :=
      MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_preserves_read_above
        finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n
        (quotientPtr fp k) 0 k finalMem
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit, hfinalSize]
          unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit]
          unfold quotientPtr remainderPtr wordArrayAllocationSize wordArrayPayloadSize
          omega)
    exact hframe.trans (hquotientRead.trans
      (barrettPositiveMemory_headerReads mem aw divisor top fp k hk hkPos hfp hmemSize
        hmemLe hgap hfirstFit huFit hvFit).1)
  have rdSetup := MultiLimbSchoolbookDenormalization.normalizedLoopSetupExact
    (by omega) hexecution
  have rdReturn := MultiLimbSchoolbookDenormalization.denormalizeAllExact hshiftPos
    hshiftBound hdenormalize hret (by omega) rdSetup
  exact ⟨inputs, finalMem, finalAw, steps, gas, hlength, hfinalAw, hfinalSize,
    hresultRead64, hresultQuotientHeader, hresultReadBelow, hquotient, rdReturn⟩

/-- Execute the complete zero-CLZ quotient and direct-copy return to the concrete caller while
retaining the pure Barrett quotient and exact selected gas. -/
theorem barrettZeroDivisionReturn_exists
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas : Nat} {tail : List UInt256}
    {mem : ByteArray} {aw top : UInt256}
    (fp k divisorPtr modulusNat retPc : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
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
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (htop : arrayWord (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1) = top)
    (htopNe : top.toNat ≠ 0)
    (hshiftZero : (MultiLimbClz.clzResult top).n = 0)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat retPc) = true)
    (hdepth : tail.length ≤ 996)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (⟨0⟩ :: UInt256.ofNat retPc :: UInt256.ofNat (remainderPtr fp k) ::
        UInt256.ofNat (quotientCount k) :: UInt256.ofNat k ::
        UInt256.ofNat (normalizedDivisorPtr fp k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: top :: ⟨0⟩ :: tail)
      (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr)
      rdata acc initialSteps initialGas) :
    ∃ (inputs : List Nat) (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        finalAw = barrettZeroWords aw fp k divisorPtr ∧
        finalMem.size = normalizedDivisorPtr fp k + 32 + 32 * k ∧
        (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.readWithPadding 64 32 =
            UInt256.toByteArray
              (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) ∧
        (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.readWithPadding
            (quotientPtr fp k) 32 =
              UInt256.toByteArray (UInt256.ofNat (quotientCount k)) ∧
        (∀ read, 96 ≤ read → read + 32 ≤ fp →
          (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
            (UInt256.ofNat (normalizedDividendPtr fp k))
            (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.readWithPadding read 32 =
              mem.readWithPadding read 32) ∧
        MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
            (MultiLimbSchoolbookOuterComplete.quotientReadNats finalMem finalAw
              (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat ∧
        let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem
        RDx runtimeBytecode ee g s0 (UInt256.ofNat retPc)
          (UInt256.ofNat (remainderPtr fp k) :: UInt256.ofNat (quotientPtr fp k) :: tail)
          copied.memory finalAw rdata acc
          ((initialSteps + steps + 5) + 58 * k + 30)
          ((initialGas + gas + 13) + 208 * k + 100) := by
  have hkPos : 0 < k := by omega
  let geometry := zeroContinuationGeometry aw fp k divisorPtr hkTwo hk hawFit hfirstFit
    hsecondFit hquotientFit huFit hvFit hcopyFit
  have hheaders := barrettZeroMemory_quHeaders mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hvHeader := barrettZeroMemory_vHeader mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hnormalized : UInt256.size ≤ 2 * top.toNat := by
    exact normalizedTop_of_clz_zero top htopNe hshiftZero
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hvPtrFit : normalizedDivisorPtr fp k < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvMem : (UInt256.ofNat (normalizedDivisorPtr fp k)).toNat + 32 * (k + 1) ≤
      (barrettZeroMemory mem fp k divisorPtr).size := by
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit, hzSize]
    omega
  have hdividend := barrettZeroDividend_value mem aw fp k divisorPtr hk hkPos hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource
  have hdivisor := barrettZeroDivisor_value mem aw fp k divisorPtr modulusNat hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit
    hsource hdivisorFit hmodulus
  obtain ⟨vRest, vSecond, inputs, finalMem, finalAw, steps, gas, hlength, hsemantic,
      hquotient, hexecution⟩ := barrettQuotientExecution_exists_of_values k 0 modulusNat
        geometry hkTwo hmodulusLower hheaders.2 hvHeader hheaders.1 htop hnormalized hvMem
        (by simpa only [pow_zero, Nat.mul_one] using hdividend)
        (by simpa only [pow_zero, Nat.mul_one] using hdivisor) hdepth h
  have hfinalSize : finalMem.size = normalizedDivisorPtr fp k + 32 + 32 * k := by
    rw [(MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry hsemantic).2,
      hzSize]
  have hfinalAw : finalAw = barrettZeroWords aw fp k divisorPtr :=
    (MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry hsemantic).1
  have hquotientRead64 : finalMem.readWithPadding 64 32 =
      (barrettZeroMemory mem fp k divisorPtr).readWithPadding 64 32 := by
    apply MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
    · rw [UInt256.toNat_ofNat_of_lt (by
          unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
            wordArrayPayloadSize at huFit ⊢
          omega)]
      unfold normalizedDividendPtr quotientPtr remainderPtr
      omega
    · intro jj hj
      change 64 + 32 ≤ (arrayAddress (UInt256.ofNat (quotientPtr fp k)) jj).toNat
      rw [quotientArrayAddress_toNat fp k jj hj hquotientFit]
      unfold quotientPtr remainderPtr
      omega
  have hcopiedRead64 :
      (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
        (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.readWithPadding 64 32 =
          UInt256.toByteArray
            (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k)) := by
    have hframe :=
      MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_preserves_read_below
        finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) 64 0 k finalMem
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit, hfinalSize]
          unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit]
          unfold remainderPtr
          omega)
    exact hframe.trans (hquotientRead64.trans
      (barrettZeroMemory_read64 mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe hgap
        hfirstFit hsource))
  have hcopiedReadBelow : ∀ read, 96 ≤ read → read + 32 ≤ fp →
      (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
        (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.readWithPadding read 32 =
          mem.readWithPadding read 32 := by
    intro read hread96 hreadEnd
    have hquotientRead : finalMem.readWithPadding read 32 =
        (barrettZeroMemory mem fp k divisorPtr).readWithPadding read 32 := by
      apply MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
      · rw [UInt256.toNat_ofNat_of_lt (by
            unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
              wordArrayPayloadSize at huFit ⊢
            omega)]
        unfold normalizedDividendPtr quotientPtr remainderPtr
        omega
      · intro jj hj
        change read + 32 ≤ (arrayAddress (UInt256.ofNat (quotientPtr fp k)) jj).toNat
        rw [quotientArrayAddress_toNat fp k jj hj hquotientFit]
        unfold quotientPtr remainderPtr
        omega
    have hframe :=
      MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_preserves_read_below
        finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) read 0 k finalMem
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit, hfinalSize]
          unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit]
          unfold remainderPtr
          omega)
    exact hframe.trans (hquotientRead.trans
      (barrettZeroMemory_read_below_fp mem fp k divisorPtr read hk hkPos hfp hmemSize
        hmemLe hgap hfirstFit hsource hread96 hreadEnd))
  have hcopiedQuotientHeader :
      (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
        (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.readWithPadding
          (quotientPtr fp k) 32 =
            UInt256.toByteArray (UInt256.ofNat (quotientCount k)) := by
    have hquotientRead : finalMem.readWithPadding (quotientPtr fp k) 32 =
        (barrettZeroMemory mem fp k divisorPtr).readWithPadding (quotientPtr fp k) 32 := by
      apply MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame hsemantic
      · rw [UInt256.toNat_ofNat_of_lt (by
            unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
              wordArrayPayloadSize at huFit ⊢
            omega)]
        unfold normalizedDividendPtr
        omega
      · intro jj hj
        change quotientPtr fp k + 32 ≤
          (arrayAddress (UInt256.ofNat (quotientPtr fp k)) jj).toNat
        rw [quotientArrayAddress_toNat fp k jj hj hquotientFit]
        omega
    have hframe :=
      MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_preserves_read_above
        finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
        (UInt256.ofNat (remainderPtr fp k)) (quotientPtr fp k) 0 k finalMem
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit, hfinalSize]
          unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
        (by
          intro j hj
          simp only [Nat.zero_add]
          rw [remainderArrayAddress_toNat fp k j hj hsecondFit]
          unfold quotientPtr remainderPtr wordArrayAllocationSize wordArrayPayloadSize
          omega)
    exact hframe.trans (hquotientRead.trans
      (barrettZeroMemory_quHeaderReads mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
        hgap hfirstFit hsource).1)
  have hcopy := barrettZeroValidCopy fp k divisorPtr hkTwo hk hfp hmemSize hmemLe hgap
    hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit hsource hsemantic
  have rdReturn := MultiLimbSchoolbookZeroShiftRemainder.zeroShiftRemainderExact
    geometry.hcountWord hcopy hret (by omega) hexecution
  exact ⟨inputs, finalMem, finalAw, steps, gas, hlength, hfinalAw, hfinalSize,
    hcopiedRead64, hcopiedQuotientHeader, hcopiedReadBelow, hquotient, rdReturn⟩

end Modexp.MultiLimbBarrettContinuationExecutable
