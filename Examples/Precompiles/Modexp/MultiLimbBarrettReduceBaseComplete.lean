import Examples.Precompiles.Modexp.MultiLimbBarrettReduceBaseKnuth

/-!
# Complete constructive Barrett base reduction

This module exposes one selector for every deployed `reduceBase` branch at PC 5199.  The Knuth
constructors retain the generated quotient/correction selector, rather than hiding the arithmetic
behind an existential execution result.  The only additional allocator premise reserves the
largest branch-local workspace: at most 69 EVM words for quotient, dividend, and divisor arrays.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReduceBaseComplete

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

abbrev EntryFacts := MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
abbrev KnuthSelection := MultiLimbBarrettReduceBaseExecutable.KnuthSelection

/-- Maximum branch-local workspace for `m ≤ 32`, `2 ≤ k ≤ m`:
`(m-k+2) + (m+2) + (k+1) = 2m+5 ≤ 69` words, including array headers. -/
def workspaceBytes : Nat := 32 * 69

/-- A computationally explicit selection of every PC 5199 branch. -/
inductive Selection
    (mem : ByteArray) (aw : UInt256)
    (dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat) : Type
  | allZero
      (zero : ∀ i, i < dividendCount →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩) :
      Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp
  | short
      (m zeroLimbs : Nat) (top : UInt256)
      (mPos : 0 < m) (countEq : dividendCount = m + zeroLimbs)
      (zero : ∀ i, m ≤ i → i < m + zeroLimbs →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
      (topEq : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
        (m - 1) = top)
      (topNe : top ≠ ⟨0⟩) (ltDivisor : m < divisorCount) :
      Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp
  | knuthZero
      (m zeroLimbs : Nat) (top : UInt256)
      (mPos : 0 < m) (countEq : dividendCount = m + zeroLimbs)
      (zero : ∀ i, m ≤ i → i < m + zeroLimbs →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
      (topEq : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
        (m - 1) = top)
      (topNe : top ≠ ⟨0⟩) (divisorLe : divisorCount ≤ m)
      (shiftZero : (MultiLimbClz.clzResult
        (MultiLimbBarrettReduceBaseKnuth.setupTop mem aw fp dividendPtr divisorPtr
          m divisorCount)).n = 0)
      (selected : KnuthSelection divisorCount (m + 1)
        (MultiLimbBarrettReduceBaseKnuth.numQ m divisorCount)
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount)) ⟨0⟩
        ⟨3010⟩ (UInt256.ofNat remPtr)
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount))
        (UInt256.ofNat fp) ⟨0⟩
        (MultiLimbBarrettReduceBaseKnuth.zeroMemory mem fp dividendPtr divisorPtr
          m divisorCount)
        (MultiLimbBarrettReduceBaseKnuth.zeroWords aw fp dividendPtr divisorPtr
          m divisorCount)) :
      Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp
  | knuthPositive
      (m zeroLimbs shift : Nat) (top : UInt256)
      (mPos : 0 < m) (countEq : dividendCount = m + zeroLimbs)
      (zero : ∀ i, m ≤ i → i < m + zeroLimbs →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
      (topEq : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
        (m - 1) = top)
      (topNe : top ≠ ⟨0⟩) (divisorLe : divisorCount ≤ m)
      (shiftPos : 0 < shift)
      (shiftEq : shift = (MultiLimbClz.clzResult
        (MultiLimbBarrettReduceBaseKnuth.setupTop mem aw fp dividendPtr divisorPtr
          m divisorCount)).n)
      (selected : KnuthSelection divisorCount (m + 1)
        (MultiLimbBarrettReduceBaseKnuth.numQ m divisorCount)
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat shift) ⟨3010⟩ (UInt256.ofNat remPtr)
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount))
        (UInt256.ofNat fp) ⟨1⟩
        (MultiLimbBarrettReduceBaseKnuth.positiveMemory mem aw fp dividendPtr divisorPtr
          m divisorCount shift)
        (MultiLimbBarrettReduceBaseKnuth.normalizedWords aw fp dividendPtr m divisorCount
          divisorPtr)) :
      Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp

namespace Selection

/-- The single maximal-workspace bound implies each exact Knuth allocation bound. -/
theorem allocationBounds
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hmLe : m ≤ dividendCount) (hkLe : divisorCount ≤ m)
    (hworkspace : fp + workspaceBytes < 2 ^ 64) :
    fp + wordArrayAllocationSize
          (MultiLimbBarrettReduceBaseKnuth.numQ m divisorCount) < 2 ^ 64 ∧
      MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount +
          wordArrayAllocationSize (m + 1) < 2 ^ 64 ∧
      MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
          wordArrayAllocationSize divisorCount < 2 ^ 64 := by
  have hmBound := facts.dividendBound
  have hkTwo := facts.divisorTwo
  simp only [workspaceBytes, MultiLimbBarrettReduceBaseKnuth.numQ,
    MultiLimbBarrettReduceBaseKnuth.uFp, MultiLimbBarrettReduceBaseKnuth.vFp,
    MultiLimbSchoolbookKnuthPrefix.numQ, wordArrayAllocationSize,
    wordArrayPayloadSize] at hworkspace ⊢
  omega

/-- Every valid concrete entry has an exposed complete branch selector. -/
theorem exists_of_entry
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64) :
    Nonempty (Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) := by
  cases MultiLimbBarrettReduceBaseSelection.branchSelection_exists
      mem aw dividendPtr dividendCount divisorCount with
  | allZero zero =>
      exact ⟨.allZero zero⟩
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      exact ⟨.short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor⟩
  | knuth m zeroLimbs top mPos countEq zero topEq topNe divisorLe =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      let shift := (MultiLimbClz.clzResult
        (MultiLimbBarrettReduceBaseKnuth.setupTop mem aw fp dividendPtr divisorPtr
          m divisorCount)).n
      by_cases hshiftZero : shift = 0
      · obtain ⟨selected⟩ := MultiLimbBarrettReduceBaseKnuth.zeroSelection_exists facts
          mPos hmLe divisorLe hquotient hu hv (by simpa only [shift] using hshiftZero)
        exact ⟨.knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe
          (by simpa only [shift] using hshiftZero) selected⟩
      · have hshiftPos : 0 < shift := Nat.pos_of_ne_zero hshiftZero
        obtain ⟨selected⟩ := MultiLimbBarrettReduceBaseKnuth.positiveSelection_exists facts
          mPos hmLe divisorLe hquotient hu hv hshiftPos (by rfl)
        exact ⟨.knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe
          divisorLe hshiftPos (by rfl) selected⟩

/-- Concrete memory produced by the selected branch at the common PC 1707 return. -/
def finalMemory
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat} :
    Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp → ByteArray
  | .allZero _ => MultiLimbSchoolbookZero.allocatedMemory mem fp
  | .short m _ _ _ _ _ _ _ _ =>
      MultiLimbSchoolbookShort.copyLoopMemory
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m
  | .knuthZero m _ _ _ _ _ _ _ _ _ selected =>
      (MultiLimbSchoolbookZeroShiftRemainder.copyRange selected.finalAw
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) 0 divisorCount selected.finalMem).memory
  | .knuthPositive m _ shift _ _ _ _ _ _ _ _ _ selected =>
      (MultiLimbSchoolbookDenormalization.denormalizeRange selected.finalAw
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) shift 0 divisorCount selected.finalMem).memory

/-- Active memory word count produced by the selected branch. -/
def finalWords
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat} :
    Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp → UInt256
  | .allZero _ => MultiLimbSchoolbookZero.allocatedWords aw fp
  | .short _ _ _ _ _ _ _ _ _ => MultiLimbSchoolbookShort.shortAllocatedWords aw fp
  | .knuthZero _ _ _ _ _ _ _ _ _ _ selected => selected.finalAw
  | .knuthPositive _ _ _ _ _ _ _ _ _ _ _ _ selected => selected.finalAw

/-- Solidity free-memory pointer left by the selected reduction path. -/
def finalFreePtr
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat} :
    Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp → Nat
  | .allZero _ => fp + wordArrayAllocationSize 1
  | .short _ _ _ _ _ _ _ _ _ => fp + wordArrayAllocationSize 1
  | .knuthZero m _ _ _ _ _ _ _ _ _ _ =>
      MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount
  | .knuthPositive m _ _ _ _ _ _ _ _ _ _ _ _ =>
      MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount

/-- Every selected reduction result is covered by its exact active-word counter, which remains
representable as an EVM byte extent. -/
theorem finalCoverageAndFit
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbMontgomeryCIOSSemantic.MemoryCovered selected.finalMemory selected.finalWords ∧
      selected.finalWords.toNat * 32 < UInt256.size := by
  cases selected with
  | allZero zero =>
      have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
        lt_trans (by
          have := facts.nextAllocationBound
          omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
          (by norm_num [UInt256.size])
      have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1
        (by omega) facts.awFit hfit
      have hsize : (MultiLimbSchoolbookZero.allocatedMemory mem fp).size = fp + 32 := by
        unfold MultiLimbSchoolbookZero.allocatedMemory
          MultiLimbSchoolbookShort.shortAllocatedMemory
        apply storeBytesLength_size
        · rw [setFreePtr_size facts.memory96]
          exact facts.memoryLeFp
        · rw [setFreePtr_size facts.memory96]
          exact facts.fpGap
      constructor
      · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        change (MultiLimbSchoolbookZero.allocatedMemory mem fp).size ≤
          32 * (MultiLimbSchoolbookZero.allocatedWords aw fp).toNat
        rw [hsize]
        simpa only [MultiLimbSchoolbookZero.allocatedWords,
          MultiLimbSchoolbookShort.shortAllocatedWords] using le_trans (by omega) hrange.1
      · change (MultiLimbSchoolbookZero.allocatedWords aw fp).toNat * 32 < UInt256.size
        simpa only [MultiLimbSchoolbookZero.allocatedWords,
          MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
        lt_trans (by
          have := facts.nextAllocationBound
          omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
          (by norm_num [UInt256.size])
      have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1
        (by omega) facts.awFit hfit
      have hallocatedSize :
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
        unfold MultiLimbSchoolbookShort.shortAllocatedMemory
        apply storeBytesLength_size
        · rw [setFreePtr_size facts.memory96]
          exact facts.memoryLeFp
        · rw [setFreePtr_size facts.memory96]
          exact facts.fpGap
      have hwrite : ∀ i, i < m ->
          (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size := by
        intro i hi
        rw [show MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i =
            MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat remPtr) i by rfl,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr i (by
            exact lt_trans (by
              have := facts.remainderEndBeforeFp
              omega : remPtr + 32 * (i + 1) < 2 ^ 64)
              (by norm_num [UInt256.size])), hallocatedSize]
        have := facts.remainderEndBeforeFp
        omega
      have hsize := MultiLimbSchoolbookShort.copyLoopMemory_size_eq
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m hwrite
      constructor
      · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        change (MultiLimbSchoolbookShort.copyLoopMemory
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
          (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m).size ≤
            32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat
        rw [hsize, hallocatedSize]
        simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
          le_trans (by omega) hrange.1
      · change (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat * 32 <
          UInt256.size
        simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2
  | knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe shiftZero branch =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      let geometry := MultiLimbBarrettReduceBaseKnuth.continuationGeometry facts mPos hmLe
        divisorLe hquotient hu hv
      have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
        branch.semantic
      have hzSize := MultiLimbBarrettReduceBaseKnuth.zeroMemory_size facts mPos hmLe hquotient
      have hwrite : ∀ j, j < divisorCount ->
          (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) j).toNat + 32 ≤ branch.finalMem.size := by
        intro j hj
        rw [hfinal.2, hzSize,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr j (by
            exact lt_trans (by
              have := facts.remainderEndBeforeFp
              have := hquotient
              omega : remPtr + 32 * (j + 1) < 2 ^ 64)
              (by norm_num [UInt256.size]))]
        have := facts.remainderEndBeforeFp
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      have hcopySize := MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_size_eq
        branch.finalAw (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem (by
          intro j hj
          simpa only [Nat.zero_add] using hwrite j hj)
      constructor
      · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        change (MultiLimbSchoolbookZeroShiftRemainder.copyRange branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem).memory.size ≤
            32 * branch.finalAw.toNat
        have hvPtrFit : MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount <
            UInt256.size := by
          exact lt_trans (by
            have := hv
            omega : MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount < 2 ^ 64)
            (by norm_num [UInt256.size])
        calc
          _ = branch.finalMem.size := hcopySize
          _ = (MultiLimbBarrettReduceBaseKnuth.zeroMemory mem fp dividendPtr divisorPtr
              m divisorCount).size := hfinal.2
          _ = MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount + 32 +
              32 * divisorCount := hzSize
          _ ≤ 32 * branch.finalAw.toNat := by
            rw [hfinal.1,
              MultiLimbBarrettReduceBaseKnuth.zeroWords_eq_normalizedWords facts mPos
                hmLe divisorLe hquotient hu hv]
            have hactive := geometry.hvActive
            rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
            omega
      · change branch.finalAw.toNat * 32 < UInt256.size
        rw [hfinal.1,
          MultiLimbBarrettReduceBaseKnuth.zeroWords_eq_normalizedWords facts mPos hmLe
            divisorLe hquotient hu hv]
        exact geometry.hawFit
  | knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe divisorLe shiftPos
      shiftEq branch =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      let geometry := MultiLimbBarrettReduceBaseKnuth.continuationGeometry facts mPos hmLe
        divisorLe hquotient hu hv
      have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
        branch.semantic
      have hpSize := MultiLimbBarrettReduceBaseKnuth.positiveMemory_size facts mPos hmLe
        hquotient hu hv (shift := shift)
      have hwrite : ∀ j, j < divisorCount ->
          (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) j).toNat + 32 ≤ branch.finalMem.size := by
        intro j hj
        rw [hfinal.2, hpSize,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr j (by
            exact lt_trans (by
              have := facts.remainderEndBeforeFp
              have := hquotient
              omega : remPtr + 32 * (j + 1) < 2 ^ 64)
              (by norm_num [UInt256.size]))]
        have := facts.remainderEndBeforeFp
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      have hdenormalizeSize :=
        MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_size_eq branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem (by
            intro j hj
            simpa only [Nat.zero_add] using hwrite j hj)
      constructor
      · unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
        change (MultiLimbSchoolbookDenormalization.denormalizeRange branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem).memory.size ≤
            32 * branch.finalAw.toNat
        have hvPtrFit : MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount <
            UInt256.size := by
          exact lt_trans (by
            have := hv
            omega : MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount < 2 ^ 64)
            (by norm_num [UInt256.size])
        calc
          _ = branch.finalMem.size := hdenormalizeSize
          _ = (MultiLimbBarrettReduceBaseKnuth.positiveMemory mem aw fp dividendPtr divisorPtr
              m divisorCount shift).size := hfinal.2
          _ = MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount + 32 +
              32 * divisorCount := hpSize
          _ ≤ 32 * branch.finalAw.toNat := by
            rw [hfinal.1]
            have hactive := geometry.hvActive
            rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
            omega
      · change branch.finalAw.toNat * 32 < UInt256.size
        rw [hfinal.1]
        exact geometry.hawFit

/-- Every selected reduction branch preserves complete words through the remainder header. This
single frame covers the persistent modulus array and the remainder length word consumed by the
subsequent Barrett-constant computation. -/
theorem finalReadBelowRemainderHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp read : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hread96 : 96 ≤ read) (hreadEnd : read + 32 ≤ remPtr + 32) :
    selected.finalMemory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  cases selected with
  | allZero zero =>
      simpa only [finalMemory, MultiLimbSchoolbookZero.allocatedMemory] using
        MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_read_below mem fp read
          facts.memory96 facts.fpGap hread96 (by
            have := facts.remainderEndBeforeFp
            omega)
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      have hallocated :
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).readWithPadding read 32 =
            mem.readWithPadding read 32 :=
        MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_read_below mem fp read
          facts.memory96 facts.fpGap hread96 (by
            have := facts.remainderEndBeforeFp
            omega)
      have hallocatedSize :
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
        unfold MultiLimbSchoolbookShort.shortAllocatedMemory
        apply storeBytesLength_size
        · rw [setFreePtr_size facts.memory96]
          exact facts.memoryLeFp
        · rw [setFreePtr_size facts.memory96]
          exact facts.fpGap
      have hremFit : remPtr + 32 * (divisorCount + 1) < UInt256.size :=
        lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hworkspace
          omega : remPtr + 32 * (divisorCount + 1) < 2 ^ 64)
          (by norm_num [UInt256.size])
      have haddress : ∀ i, i < divisorCount →
          (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat =
            remPtr + 32 * (i + 1) := by
        intro i hi
        rw [show MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i =
            MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat remPtr) i by rfl,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr i (by omega)]
      have hwrite : ∀ i, i < m →
          (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size := by
        intro i hi
        rw [haddress i (by omega), hallocatedSize]
        have := facts.remainderEndBeforeFp
        omega
      have hcopy := MultiLimbSchoolbookShort.copyLoopMemory_read_below
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m read hwrite (by
          intro i hi
          rw [haddress i (by omega)]
          omega)
      exact hcopy.trans hallocated
  | knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe shiftZero branch =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
        branch.semantic
      have hsemantic :=
        MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame
          (read := read) branch.semantic (by
            rw [UInt256.toNat_ofNat_of_lt (lt_trans (by
              have := hu
              omega : MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            have := facts.remainderEndBeforeFp
            unfold MultiLimbBarrettReduceBaseKnuth.uFp wordArrayAllocationSize
              wordArrayPayloadSize
            omega) (by
            intro j hj
            change read + 32 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
              (UInt256.ofNat fp) j).toNat
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat fp j (lt_trans (by
              have := hquotient
              unfold wordArrayAllocationSize wordArrayPayloadSize at hquotient
              omega : fp + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
            have := facts.remainderEndBeforeFp
            omega)
      have hinitial :
          (MultiLimbBarrettReduceBaseKnuth.zeroMemory mem fp dividendPtr divisorPtr m
            divisorCount).readWithPadding read 32 = mem.readWithPadding read 32 :=
        (MultiLimbBarrettReduceBaseKnuth.zeroMemory_read_below facts mPos hmLe hquotient
          (by
            have := facts.remainderEndBeforeFp
            unfold MultiLimbBarrettReduceBaseKnuth.vFp
              MultiLimbBarrettReduceBaseKnuth.uFp wordArrayAllocationSize
              wordArrayPayloadSize
            omega)).trans
          ((MultiLimbBarrettReduceBaseKnuth.vMemory_read_below facts mPos hmLe hquotient
            hread96 (by
              have := facts.remainderEndBeforeFp
              unfold MultiLimbBarrettReduceBaseKnuth.vFp
                MultiLimbBarrettReduceBaseKnuth.uFp wordArrayAllocationSize
                wordArrayPayloadSize
              omega)).trans
            (MultiLimbBarrettReduceBaseKnuth.setupMemory_read_below facts mPos hmLe
              hread96 (by have := facts.remainderEndBeforeFp; omega)))
      have hzSize := MultiLimbBarrettReduceBaseKnuth.zeroMemory_size facts mPos hmLe hquotient
      have hwrite : ∀ j, j < divisorCount →
          (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) j).toNat + 32 ≤ branch.finalMem.size := by
        intro j hj
        rw [hfinal.2, hzSize,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr j (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
        have := facts.remainderEndBeforeFp
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      have hcopy := MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_preserves_read_below
        branch.finalAw (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) read 0 divisorCount branch.finalMem (by
          intro j hj
          simpa only [Nat.zero_add] using hwrite j hj) (by
          intro j hj
          rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr (0 + j) (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (0 + j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
          omega)
      exact hcopy.trans (hsemantic.trans hinitial)
  | knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe divisorLe shiftPos
      shiftEq branch =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
        branch.semantic
      have hsemantic :=
        MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame
          (read := read) branch.semantic (by
            rw [UInt256.toNat_ofNat_of_lt (lt_trans (by
              have := hu
              omega : MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            have := facts.remainderEndBeforeFp
            unfold MultiLimbBarrettReduceBaseKnuth.uFp wordArrayAllocationSize
              wordArrayPayloadSize
            omega) (by
            intro j hj
            change read + 32 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
              (UInt256.ofNat fp) j).toNat
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat fp j (lt_trans (by
              have := hquotient
              unfold wordArrayAllocationSize wordArrayPayloadSize at hquotient
              omega : fp + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
            have := facts.remainderEndBeforeFp
            omega)
      have hinitial := MultiLimbBarrettReduceBaseKnuth.positiveMemory_read_below
        (shift := shift) facts mPos hmLe hquotient hu hv hread96 (by
          have := facts.remainderEndBeforeFp
          omega : read + 32 ≤ fp)
      have hpSize := MultiLimbBarrettReduceBaseKnuth.positiveMemory_size facts mPos hmLe
        hquotient hu hv (shift := shift)
      have hwrite : ∀ j, j < divisorCount →
          (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) j).toNat + 32 ≤ branch.finalMem.size := by
        intro j hj
        rw [hfinal.2, hpSize,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr j (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
        have := facts.remainderEndBeforeFp
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      have hdenormalize :=
        MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_preserves_read_below
          branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift read 0 divisorCount branch.finalMem (by
            intro j hj
            simpa only [Nat.zero_add] using hwrite j hj) (by
            intro j hj
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr (0 + j) (lt_trans (by
              have := facts.remainderEndBeforeFp
              omega : remPtr + 32 * (0 + j + 1) < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            omega)
      exact hdenormalize.trans (hsemantic.trans hinitial)

/-- The selected path leaves a valid Solidity allocator state at its exposed free pointer. -/
theorem finalAllocatorGeometry
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    96 ≤ selected.finalMemory.size ∧
      selected.finalMemory.size ≤ selected.finalFreePtr ∧
      selected.finalFreePtr - selected.finalMemory.size < USize.size ∧
      selected.finalMemory.readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat selected.finalFreePtr) := by
  cases selected with
  | allZero zero =>
      have hsize : (MultiLimbSchoolbookZero.allocatedMemory mem fp).size = fp + 32 := by
        unfold MultiLimbSchoolbookZero.allocatedMemory
          MultiLimbSchoolbookShort.shortAllocatedMemory
        apply storeBytesLength_size
        · rw [setFreePtr_size facts.memory96]
          exact facts.memoryLeFp
        · rw [setFreePtr_size facts.memory96]
          exact facts.fpGap
      refine ⟨?_, ?_, ?_, ?_⟩
      · change 96 ≤ (MultiLimbSchoolbookZero.allocatedMemory mem fp).size
        rw [hsize]
        have := facts.fp96
        omega
      · change (MultiLimbSchoolbookZero.allocatedMemory mem fp).size ≤
          fp + wordArrayAllocationSize 1
        rw [hsize]
        simp only [wordArrayAllocationSize, wordArrayPayloadSize]
        omega
      · change fp + wordArrayAllocationSize 1 -
          (MultiLimbSchoolbookZero.allocatedMemory mem fp).size < USize.size
        rw [hsize]
        simp only [finalFreePtr, wordArrayAllocationSize, wordArrayPayloadSize]
        have : 32 < USize.size := by native_decide
        omega
      · simpa only [finalMemory, finalFreePtr,
          MultiLimbSchoolbookZero.allocatedMemory] using
          MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_freeRead mem fp
            facts.memory96 facts.fp96 facts.fpGap
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      have hallocatedSize :
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
        unfold MultiLimbSchoolbookShort.shortAllocatedMemory
        apply storeBytesLength_size
        · rw [setFreePtr_size facts.memory96]
          exact facts.memoryLeFp
        · rw [setFreePtr_size facts.memory96]
          exact facts.fpGap
      have hwrite : ∀ i, i < m →
          (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size := by
        intro i hi
        rw [show MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i =
            MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat remPtr) i by rfl,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr i (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
          hallocatedSize]
        have := facts.remainderEndBeforeFp
        omega
      have hsize := MultiLimbSchoolbookShort.copyLoopMemory_size_eq
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m hwrite
      have hread := MultiLimbSchoolbookShort.copyLoopMemory_read_below
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m 64 hwrite (by
          intro i hi
          change 96 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) i).toNat
          rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr i (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
          have := facts.divisorPtr96
          have := facts.divisorEndBeforeDividend
          have := facts.dividendEndBeforeRemainder
          omega)
      have hfree := MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_freeRead mem fp
        facts.memory96 facts.fp96 facts.fpGap
      refine ⟨?_, ?_, ?_, ?_⟩
      · change 96 ≤ (MultiLimbSchoolbookShort.copyLoopMemory
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
          (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m).size
        rw [hsize, hallocatedSize]
        have := facts.fp96
        omega
      · change (MultiLimbSchoolbookShort.copyLoopMemory
          (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
          (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m).size ≤
            fp + wordArrayAllocationSize 1
        rw [hsize, hallocatedSize]
        simp only [wordArrayAllocationSize, wordArrayPayloadSize]
        omega
      · change fp + wordArrayAllocationSize 1 -
          (MultiLimbSchoolbookShort.copyLoopMemory
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
            (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
            (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m).size < USize.size
        rw [hsize, hallocatedSize]
        simp only [wordArrayAllocationSize, wordArrayPayloadSize]
        have : 32 < USize.size := by native_decide
        omega
      · simpa only [finalMemory, finalFreePtr] using hread.trans hfree
  | knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe shiftZero branch =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
        branch.semantic
      have hzSize := MultiLimbBarrettReduceBaseKnuth.zeroMemory_size facts mPos hmLe hquotient
      have hwrite : ∀ j, j < divisorCount →
          (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) j).toNat + 32 ≤ branch.finalMem.size := by
        intro j hj
        rw [hfinal.2, hzSize,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr j (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
        have := facts.remainderEndBeforeFp
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      have hcopySize := MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_size_eq
        branch.finalAw (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem (by
          intro j hj
          simpa only [Nat.zero_add] using hwrite j hj)
      have hcopyRead :=
        MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_preserves_read_below
          branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) 64 0 divisorCount branch.finalMem (by
            intro j hj
            simpa only [Nat.zero_add] using hwrite j hj) (by
            intro j hj
            change 96 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
              (UInt256.ofNat remPtr) (0 + j)).toNat
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr (0 + j) (lt_trans (by
              have := facts.remainderEndBeforeFp
              omega : remPtr + 32 * (0 + j + 1) < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            have := facts.divisorPtr96
            have := facts.divisorEndBeforeDividend
            have := facts.dividendEndBeforeRemainder
            omega)
      have hsemantic :=
        MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame
          (read := 64) branch.semantic (by
            rw [UInt256.toNat_ofNat_of_lt (lt_trans (by
              have := hu
              omega : MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            unfold MultiLimbBarrettReduceBaseKnuth.uFp wordArrayAllocationSize
              wordArrayPayloadSize
            have := facts.fp96
            omega) (by
            intro j hj
            change 96 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
              (UInt256.ofNat fp) j).toNat
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat fp j (lt_trans (by
              have := hquotient
              unfold wordArrayAllocationSize wordArrayPayloadSize at hquotient
              omega : fp + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
            have := facts.fp96
            omega)
      have hzeroRead := MultiLimbBarrettReduceBaseKnuth.zeroMemory_read_below (ptr := 64)
        facts mPos hmLe hquotient (by
          unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
            wordArrayAllocationSize wordArrayPayloadSize
          have := facts.fp96
          omega)
      have hvFree := MultiLimbBarrettReduceBaseKnuth.vMemory_freeRead facts mPos hmLe hquotient
      have houtputSize :
          (MultiLimbSchoolbookZeroShiftRemainder.copyRange branch.finalAw
            (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
            (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem).memory.size =
              MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
                wordArrayAllocationSize divisorCount := by
        calc
          _ = branch.finalMem.size := hcopySize
          _ = (MultiLimbBarrettReduceBaseKnuth.zeroMemory mem fp dividendPtr divisorPtr
              m divisorCount).size := hfinal.2
          _ = MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount + 32 +
              32 * divisorCount := hzSize
          _ = _ := by simp only [wordArrayAllocationSize, wordArrayPayloadSize]; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (MultiLimbSchoolbookZeroShiftRemainder.copyRange branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem).memory.size ≥ 96
        rw [houtputSize]
        have := facts.fp96
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      · change (MultiLimbSchoolbookZeroShiftRemainder.copyRange branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem).memory.size ≤
            MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
              wordArrayAllocationSize divisorCount
        rw [houtputSize]
      · change MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
          wordArrayAllocationSize divisorCount -
          (MultiLimbSchoolbookZeroShiftRemainder.copyRange branch.finalAw
            (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
            (UInt256.ofNat remPtr) 0 divisorCount branch.finalMem).memory.size < USize.size
        rw [houtputSize]
        simp only [Nat.sub_self]
        native_decide
      · simpa only [finalMemory, finalFreePtr] using
          hcopyRead.trans (hsemantic.trans (hzeroRead.trans hvFree))
  | knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe divisorLe shiftPos
      shiftEq branch =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
        branch.semantic
      have hpSize := MultiLimbBarrettReduceBaseKnuth.positiveMemory_size facts mPos hmLe
        hquotient hu hv (shift := shift)
      have hwrite : ∀ j, j < divisorCount →
          (MultiLimbSchoolbookNormalization.arrayAddress
            (UInt256.ofNat remPtr) j).toNat + 32 ≤ branch.finalMem.size := by
        intro j hj
        rw [hfinal.2, hpSize,
          MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr j (lt_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
        have := facts.remainderEndBeforeFp
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      have hdenormalizeSize :=
        MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_size_eq branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem (by
            intro j hj
            simpa only [Nat.zero_add] using hwrite j hj)
      have hdenormalizeRead :=
        MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_preserves_read_below
          branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift 64 0 divisorCount branch.finalMem (by
            intro j hj
            simpa only [Nat.zero_add] using hwrite j hj) (by
            intro j hj
            change 96 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
              (UInt256.ofNat remPtr) (0 + j)).toNat
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat remPtr (0 + j) (lt_trans (by
              have := facts.remainderEndBeforeFp
              omega : remPtr + 32 * (0 + j + 1) < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            have := facts.divisorPtr96
            have := facts.divisorEndBeforeDividend
            have := facts.dividendEndBeforeRemainder
            omega)
      have hsemantic :=
        MultiLimbSchoolbookOuterComplete.semanticContinuations_read_below_frame
          (read := 64) branch.semantic (by
            rw [UInt256.toNat_ofNat_of_lt (lt_trans (by
              have := hu
              omega : MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount < 2 ^ 64)
              (by norm_num [UInt256.size]))]
            unfold MultiLimbBarrettReduceBaseKnuth.uFp wordArrayAllocationSize
              wordArrayPayloadSize
            have := facts.fp96
            omega) (by
            intro j hj
            change 96 ≤ (MultiLimbSchoolbookNormalization.arrayAddress
              (UInt256.ofNat fp) j).toNat
            rw [MultiLimbBarrettReduceBaseKnuth.arrayAddressNat fp j (lt_trans (by
              have := hquotient
              unfold wordArrayAllocationSize wordArrayPayloadSize at hquotient
              omega : fp + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
            have := facts.fp96
            omega)
      have hpositiveRead :=
        MultiLimbBarrettReduceBaseKnuth.positiveMemory_read_below_vMemory
          (shift := shift) facts mPos hmLe hquotient hu hv (by
            have := facts.fp96
            omega : 64 + 32 ≤ fp)
      have hvFree := MultiLimbBarrettReduceBaseKnuth.vMemory_freeRead facts mPos hmLe hquotient
      have houtputSize :
          (MultiLimbSchoolbookDenormalization.denormalizeRange branch.finalAw
            (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
            (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem).memory.size =
              MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
                wordArrayAllocationSize divisorCount := by
        calc
          _ = branch.finalMem.size := hdenormalizeSize
          _ = (MultiLimbBarrettReduceBaseKnuth.positiveMemory mem aw fp dividendPtr
              divisorPtr m divisorCount shift).size := hfinal.2
          _ = MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount + 32 +
              32 * divisorCount := hpSize
          _ = _ := by simp only [wordArrayAllocationSize, wordArrayPayloadSize]; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · change (MultiLimbSchoolbookDenormalization.denormalizeRange branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem).memory.size ≥ 96
        rw [houtputSize]
        have := facts.fp96
        unfold MultiLimbBarrettReduceBaseKnuth.vFp MultiLimbBarrettReduceBaseKnuth.uFp
        omega
      · change (MultiLimbSchoolbookDenormalization.denormalizeRange branch.finalAw
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem).memory.size ≤
            MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
              wordArrayAllocationSize divisorCount
        rw [houtputSize]
      · change MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount +
          wordArrayAllocationSize divisorCount -
          (MultiLimbSchoolbookDenormalization.denormalizeRange branch.finalAw
            (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
            (UInt256.ofNat remPtr) shift 0 divisorCount branch.finalMem).memory.size <
              USize.size
        rw [houtputSize]
        simp only [Nat.sub_self]
        native_decide
      · simpa only [finalMemory, finalFreePtr] using
          hdenormalizeRead.trans (hsemantic.trans (hpositiveRead.trans hvFree))

/-- Every branch advances the free pointer beyond the reduction-entry workspace pointer. -/
theorem entryFp_le_finalFreePtr
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    fp ≤ selected.finalFreePtr := by
  cases selected <;>
    simp only [finalFreePtr, wordArrayAllocationSize, wordArrayPayloadSize,
      MultiLimbBarrettReduceBaseKnuth.vFp, MultiLimbBarrettReduceBaseKnuth.uFp] <;>
    omega

/-- Every selected reduction branch leaves its free pointer inside the documented maximal
69-word workspace reserved at the PC 5199 entry. -/
theorem finalFreePtr_le_workspace
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    selected.finalFreePtr ≤ fp + workspaceBytes := by
  cases selected with
  | allZero zero =>
      simp only [finalFreePtr, workspaceBytes, wordArrayAllocationSize,
        wordArrayPayloadSize]
      omega
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      simp only [finalFreePtr, workspaceBytes, wordArrayAllocationSize,
        wordArrayPayloadSize]
      omega
  | knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe shiftZero branch =>
      have hmLe : m ≤ dividendCount := by omega
      have hmBound := facts.dividendBound
      have hkBound := facts.divisorBound
      simp only [finalFreePtr, workspaceBytes, MultiLimbBarrettReduceBaseKnuth.vFp,
        MultiLimbBarrettReduceBaseKnuth.uFp, MultiLimbBarrettReduceBaseKnuth.numQ,
        MultiLimbSchoolbookKnuthPrefix.numQ, wordArrayAllocationSize,
        wordArrayPayloadSize]
      omega
  | knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe divisorLe shiftPos
      shiftEq branch =>
      have hmLe : m ≤ dividendCount := by omega
      have hmBound := facts.dividendBound
      have hkBound := facts.divisorBound
      simp only [finalFreePtr, workspaceBytes, MultiLimbBarrettReduceBaseKnuth.vFp,
        MultiLimbBarrettReduceBaseKnuth.uFp, MultiLimbBarrettReduceBaseKnuth.numQ,
        MultiLimbSchoolbookKnuthPrefix.numQ, wordArrayAllocationSize,
        wordArrayPayloadSize]
      omega

/-- The selector frame lifts from padded words to the consecutive-word representation used by
the constant and exponentiation phases. -/
theorem finalMemoryWordsBelowRemainderHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp ptr words : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hptr96 : 96 ≤ ptr) (hptrEnd : ptr + 32 * words ≤ remPtr + 32) :
    MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom selected.finalMemory ptr words =
      MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      simp only [MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom]
      rw [show MultiLimbMemoryModel.memoryWordNat selected.finalMemory ptr =
          MultiLimbMemoryModel.memoryWordNat mem ptr by
        unfold MultiLimbMemoryModel.memoryWordNat
        rw [finalReadBelowRemainderHeader (read := ptr) facts hworkspace selected hptr96
          (by omega)]]
      congr 1
      exact ih (ptr := ptr + 32) (by omega) (by omega)

/-- The reduction result retains the fixed-width remainder header expected by later callers. -/
theorem finalRemainderHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    selected.finalMemory.readWithPadding remPtr 32 =
      UInt256.toByteArray (UInt256.ofNat divisorCount) := by
  exact (finalReadBelowRemainderHeader (read := remPtr) facts hworkspace selected (by
    have := facts.divisorPtr96
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    omega) (by omega)).trans facts.remainderHeaderRead

/-- The persistent divisor header also survives every selected reduction branch. -/
theorem finalDivisorHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    selected.finalMemory.readWithPadding divisorPtr 32 =
      UInt256.toByteArray (UInt256.ofNat divisorCount) := by
  exact (finalReadBelowRemainderHeader (read := divisorPtr) facts hworkspace selected
    facts.divisorPtr96 (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega)).trans facts.divisorHeaderRead

/-- The final persistent divisor payload denotes the same natural value as the concrete divisor
observed at reduction entry. -/
theorem finalDivisorMemoryValue
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    wordLimbsToNat
        (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom selected.finalMemory
          (divisorPtr + 32) divisorCount) =
      wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  rw [finalMemoryWordsBelowRemainderHeader (ptr := divisorPtr + 32)
    (words := divisorCount) facts hworkspace selected (by
      have := facts.divisorPtr96
      omega) (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega)]
  symm
  apply MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryWordsFrom
  · exact lt_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hworkspace
      omega : divisorPtr + 32 * (divisorCount + 1) < 2 ^ 64)
      (by norm_num [UInt256.size])
  · exact facts.memoryCovered
  · exact facts.awFit

/-- Exact step increment for the selected deployed path. -/
def stepDelta
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat} :
    Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp → Nat
  | .allZero _ => MultiLimbBarrettReduceBaseExecutable.zeroReturnSteps dividendCount
  | .short m zeroLimbs _ _ _ _ _ _ _ =>
      MultiLimbBarrettReduceBaseExecutable.shortReturnSteps m zeroLimbs
  | .knuthZero m zeroLimbs _ _ _ _ _ _ _ _ selected =>
      134 + 72 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalSteps mem aw fp
          (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount) dividendPtr m divisorCount
          (UInt256.ofNat divisorPtr) +
        152 + selected.steps + 5 + 58 * divisorCount + 30 + 5
  | .knuthPositive m zeroLimbs shift _ _ _ _ _ _ _ _ _ selected =>
      let denormalized := MultiLimbSchoolbookDenormalization.denormalizeRange selected.finalAw
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) shift 0 divisorCount selected.finalMem
      134 + 72 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalSteps mem aw fp
          (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount) dividendPtr m divisorCount
          (UInt256.ofNat divisorPtr) +
        MultiLimbSchoolbookNormalizationFunction.positiveSteps
          (MultiLimbBarrettReduceBaseKnuth.vMemory mem fp dividendPtr m divisorCount)
          (MultiLimbBarrettReduceBaseKnuth.normalizedWords aw fp dividendPtr m divisorCount
            divisorPtr)
          (UInt256.ofNat divisorPtr)
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount))
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          divisorCount m shift + selected.steps + 5 + 23 + denormalized.steps + 6 + 5

/-- Exact gas increment for the selected deployed path. -/
def gasDelta
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat} :
    Selection mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp → Nat
  | .allZero _ => MultiLimbBarrettReduceBaseExecutable.zeroReturnGas aw fp dividendCount
  | .short m zeroLimbs _ _ _ _ _ _ _ =>
      MultiLimbBarrettReduceBaseExecutable.shortReturnGas aw fp m zeroLimbs
  | .knuthZero m zeroLimbs _ _ _ _ _ _ _ _ selected =>
      491 + 270 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalGas mem aw fp
          (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount) dividendPtr m divisorCount
          (UInt256.ofNat divisorPtr) +
        MultiLimbSchoolbookNormalizationFunction.zeroGas
          (MultiLimbBarrettReduceBaseKnuth.setupWords aw fp dividendPtr m divisorCount
            divisorPtr)
          divisorPtr (MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount) divisorCount +
        selected.gas + 13 + 208 * divisorCount + 100 + 17
  | .knuthPositive m zeroLimbs shift _ _ _ _ _ _ _ _ _ selected =>
      let denormalized := MultiLimbSchoolbookDenormalization.denormalizeRange selected.finalAw
        (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
        (UInt256.ofNat remPtr) shift 0 divisorCount selected.finalMem
      491 + 270 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalGas mem aw fp
          (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount) dividendPtr m divisorCount
          (UInt256.ofNat divisorPtr) +
        MultiLimbSchoolbookNormalizationFunction.positiveGas
          (MultiLimbBarrettReduceBaseKnuth.setupMemory mem fp dividendPtr m divisorCount)
          (MultiLimbBarrettReduceBaseKnuth.setupWords aw fp dividendPtr m divisorCount
            divisorPtr)
          (UInt256.ofNat divisorPtr)
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount))
          (UInt256.ofNat (MultiLimbBarrettReduceBaseKnuth.uFp fp m divisorCount))
          (MultiLimbBarrettReduceBaseKnuth.vFp fp m divisorCount) divisorCount m shift +
        selected.gas + 13 + 73 + denormalized.gas + 26 + 17

/-- Execute the selected PC 5199 branch to its common PC 1707 return with exact path-sensitive
steps and gas. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {tail : List UInt256}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 993)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat divisorPtr :: tail)
      selected.finalMemory selected.finalWords rdata acc
      (steps + selected.stepDelta) (gasUsed + selected.gasDelta) := by
  cases selected with
  | allZero zero =>
      exact MultiLimbBarrettReduceBaseSelection.allZeroReturnExact facts zero hcalldata
        (by omega) h
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      exact MultiLimbBarrettReduceBaseSelection.shortReturnExact facts mPos countEq zero
        topEq topNe ltDivisor hcalldata (by omega) h
  | knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe shiftZero selected =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have rd := MultiLimbBarrettReduceBaseKnuth.selectedZeroExact facts mPos countEq zero
        topEq topNe divisorLe hquotient hu hv shiftZero selected hcalldata htail h
      apply rd.withIndices
      · simp only [stepDelta]
        omega
      · simp only [gasDelta]
        omega
  | knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe divisorLe shiftPos
      shiftEq selected =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have rd := MultiLimbBarrettReduceBaseKnuth.selectedPositiveExact facts mPos countEq zero
        topEq topNe divisorLe hquotient hu hv shiftPos shiftEq selected hcalldata htail h
      apply rd.withIndices
      · simp only [stepDelta]
        omega
      · simp only [gasDelta]
        omega

/-- The all-zero branch's unchanged remainder allocation denotes zero, hence the entry dividend
modulo the concrete divisor. -/
theorem allZeroResult_eq_entry_mod
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (zero : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩) :
    wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (MultiLimbSchoolbookZero.allocatedMemory mem fp)
          (MultiLimbSchoolbookZero.allocatedWords aw fp)
          (UInt256.ofNat remPtr) 0 divisorCount) =
      wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat dividendPtr) 0 dividendCount) %
        wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  have hentry := MultiLimbBarrettReduceBaseSelection.allZeroEntryValue facts zero
  have hnext := facts.nextAllocationBound
  have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1 (by omega)
    facts.awFit hfit
  have hresult : wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (MultiLimbSchoolbookZero.allocatedMemory mem fp)
        (MultiLimbSchoolbookZero.allocatedWords aw fp)
        (UInt256.ofNat remPtr) 0 divisorCount) = 0 := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
    intro i hi
    have haddressFit : remPtr + 32 * (i + 1) < UInt256.size :=
      lt_trans (by
        have := facts.remainderEndBeforeFp
        omega : remPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])
    have haddress :
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat =
          remPtr + 32 * (i + 1) := by
      unfold MultiLimbSchoolbookShort.arrayAddress
      simpa [UInt256.toNat_ofNat_of_lt (by omega : remPtr < UInt256.size)] using
        MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat remPtr) i (by
          simpa [UInt256.toNat_ofNat_of_lt (by omega : remPtr < UInt256.size)] using
            haddressFit)
    have hword := MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_arrayWord_zero
      mem aw (UInt256.ofNat remPtr) fp i facts.memory96 facts.memoryLeFp facts.fpGap
      (by simpa only [MultiLimbSchoolbookZero.allocatedWords,
          MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2)
      (by
        calc
          96 ≤ remPtr := by
            have := facts.divisorPtr96
            have := facts.divisorEndBeforeDividend
            have := facts.dividendEndBeforeRemainder
            omega
          _ ≤ remPtr + 32 * (i + 1) := by omega
          _ = (MultiLimbSchoolbookShort.arrayAddress
              (UInt256.ofNat remPtr) i).toNat := haddress.symm)
      (by rw [haddress, facts.memorySizeEq]; omega)
      (by
        calc
          (MultiLimbSchoolbookShort.arrayAddress
                (UInt256.ofNat remPtr) i).toNat + 32 =
              remPtr + 32 * (i + 1) + 32 := congrArg (fun x => x + 32) haddress
          _ ≤ fp := by
            have := facts.remainderEndBeforeFp
            omega)
      (by
        rw [haddress]
        simpa only [MultiLimbSchoolbookZero.allocatedWords,
          MultiLimbSchoolbookShort.shortAllocatedWords] using
          le_trans (by
            have := facts.remainderEndBeforeFp
            omega : remPtr + 32 * (i + 1) + 32 ≤ fp)
            (le_trans (by omega) hrange.1))
    simpa only [Nat.zero_add] using hword
  rw [hresult, hentry]
  simp

/-- The selected concrete result is the full PC 5199 dividend modulo the full concrete divisor.
The theorem follows the same q-hat and correction choices as `exact`. -/
theorem result_eq_entry_mod
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          selected.finalMemory selected.finalWords (UInt256.ofNat remPtr) 0 divisorCount) =
      wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat dividendPtr) 0 dividendCount) %
        wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  cases selected with
  | allZero zero =>
      exact allZeroResult_eq_entry_mod facts zero
  | short m zeroLimbs top mPos countEq zero topEq topNe ltDivisor =>
      exact MultiLimbBarrettReduceBaseSelection.shortResult_eq_entry_mod facts mPos
        countEq zero ltDivisor
  | knuthZero m zeroLimbs top mPos countEq zero topEq topNe divisorLe shiftZero selected =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have hbranch := MultiLimbBarrettReduceBaseKnuth.selectedZeroResult_eq_mod facts mPos
        hmLe divisorLe hquotient hu hv shiftZero selected
      have htrimmed := MultiLimbBarrettReduceBaseSelection.trimmedValue_eq_entry countEq zero
      simpa only [finalMemory, finalWords, htrimmed] using hbranch
  | knuthPositive m zeroLimbs shift top mPos countEq zero topEq topNe divisorLe shiftPos
      shiftEq selected =>
      have hmLe : m ≤ dividendCount := by omega
      obtain ⟨hquotient, hu, hv⟩ := allocationBounds facts hmLe divisorLe hworkspace
      have hbranch := MultiLimbBarrettReduceBaseKnuth.selectedPositiveResult_eq_mod facts mPos
        hmLe divisorLe hquotient hu hv shiftPos shiftEq selected
      have htrimmed := MultiLimbBarrettReduceBaseSelection.trimmedValue_eq_entry countEq zero
      simpa only [finalMemory, finalWords, htrimmed] using hbranch

/-- The concrete final remainder payload, read through the persistent-memory representation used
by Barrett exponentiation, is the original dividend reduced modulo the original divisor. -/
theorem resultMemoryValue_eq_entry_mod
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (facts : EntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hworkspace : fp + workspaceBytes < 2 ^ 64)
    (selected : Selection mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    wordLimbsToNat
        (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom selected.finalMemory
          (remPtr + 32) divisorCount) =
      wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat dividendPtr) 0 dividendCount) %
        wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  have hgeometry := finalCoverageAndFit facts hworkspace selected
  have hremFit : remPtr + 32 * (divisorCount + 1) < UInt256.size := by
    have hfpBound : fp < 2 ^ 64 := by
      have := hworkspace
      omega
    exact lt_of_le_of_lt (by
      have := facts.remainderEndBeforeFp
      omega : remPtr + 32 * (divisorCount + 1) ≤ fp) (lt_trans hfpBound (by
        norm_num [UInt256.size]))
  rw [← MultiLimbArrayReadSemantic.arrayReadWords_value_eq_memoryWordsFrom
    selected.finalMemory selected.finalWords remPtr divisorCount hremFit
      hgeometry.1 hgeometry.2]
  exact result_eq_entry_mod facts hworkspace selected

end Selection

end Modexp.MultiLimbBarrettReduceBaseComplete
