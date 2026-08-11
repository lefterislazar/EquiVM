import Examples.Precompiles.Modexp.MultiLimbBarrettReduceBaseSemantic
import Examples.Precompiles.Modexp.MultiLimbBarrettReduceBaseExecutable
import Examples.Precompiles.Modexp.MultiLimbSchoolbookTrimSelection

/-!
# Constructive Barrett base-reduction selection

This module turns the concrete allocator state at PC 5199 into the branch facts consumed by the
generated schoolbook execution.  In particular, the divisor top word is derived from the same
first source byte tested by the deployed Barrett scanner, and the dividend trim result is selected
by inspecting every concrete guarded limb.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReduceBaseSelection

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

/-- Concrete facts shared by every deployed `schoolbookDiv` branch at PC 5199.  `fp` is the
post-remainder-allocation free pointer used by the next branch-local allocation. -/
structure DivisionEntryFacts
    (mem : ByteArray) (aw : UInt256) (dividendPtr divisorPtr remPtr : Nat)
    (dividendCount divisorCount fp : Nat) : Prop where
  dividendLayout : MultiLimbArrayReadSemantic.Layout mem aw dividendPtr dividendCount
  divisorLayout : MultiLimbArrayReadSemantic.Layout mem aw divisorPtr divisorCount
  remainderLayout : MultiLimbArrayReadSemantic.Layout mem aw remPtr divisorCount
  dividendHeaderRead : mem.readWithPadding dividendPtr 32 =
    UInt256.toByteArray (UInt256.ofNat dividendCount)
  divisorHeaderRead : mem.readWithPadding divisorPtr 32 =
    UInt256.toByteArray (UInt256.ofNat divisorCount)
  remainderHeaderRead : mem.readWithPadding remPtr 32 =
    UInt256.toByteArray (UInt256.ofNat divisorCount)
  divisorTopNonzero : MultiLimbSchoolbookNormalization.arrayWord
    mem aw (UInt256.ofNat divisorPtr) (divisorCount - 1) ≠ ⟨0⟩
  dividendBound : dividendCount ≤ 32
  divisorTwo : 2 ≤ divisorCount
  divisorBound : divisorCount ≤ 32
  fp96 : 96 ≤ fp
  nextAllocationBound : fp + wordArrayAllocationSize 1 < 2 ^ 64
  memory96 : 96 ≤ mem.size
  memoryLeFp : mem.size ≤ fp
  fpGap : fp - mem.size < USize.size
  divisorPtr96 : 96 ≤ divisorPtr
  divisorEndBeforeDividend : divisorPtr + 32 + 32 * divisorCount ≤ dividendPtr
  dividendEndBeforeRemainder : dividendPtr + 32 + 32 * dividendCount ≤ remPtr
  remainderEndBeforeFp : remPtr + 32 + 32 * divisorCount ≤ fp
  memorySizeEq : mem.size = remPtr + 32
  memoryCovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw
  awFit : aw.toNat * 32 < UInt256.size
  aw3 : 3 ≤ aw.toNat
  aw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
  freeRead : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp)

namespace DivisionEntryFacts

theorem dividendHeader
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbSchoolbookTrim.dividendHeader mem aw (UInt256.ofNat dividendPtr) =
      UInt256.ofNat dividendCount := by
  simpa only [MultiLimbSchoolbookTrim.dividendHeader,
    MultiLimbSchoolbookNormalization.arrayHeader,
    MultiLimbSchoolbookSingle.arrayHeader] using facts.dividendLayout.header

theorem dividendHeaderAw
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbSchoolbookTrim.dividendAfterHeader aw (UInt256.ofNat dividendPtr) = aw := by
  simpa only [MultiLimbSchoolbookTrim.dividendAfterHeader,
    MultiLimbSchoolbookNormalization.arrayAfterHeader,
    MultiLimbSchoolbookSingle.arrayAfterHeader] using facts.dividendLayout.headerAw

theorem dividendWordAw
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (i : Nat) (hi : i < dividendCount) :
    MultiLimbSchoolbookTrim.dividendAfterWord aw (UInt256.ofNat dividendPtr) i = aw := by
  simpa only [MultiLimbSchoolbookTrim.dividendAfterWord,
    MultiLimbSchoolbookNormalization.arrayAfterWord,
    MultiLimbSchoolbookSingle.arrayAfterWord] using facts.dividendLayout.wordAw i hi

theorem divisorHeader
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbSchoolbookDivisorTrim.divisorHeader mem aw (UInt256.ofNat divisorPtr) =
      UInt256.ofNat divisorCount := by
  simpa only [MultiLimbSchoolbookDivisorTrim.divisorHeader,
    MultiLimbSchoolbookNormalization.arrayHeader,
    MultiLimbSchoolbookSingle.arrayHeader] using facts.divisorLayout.header

theorem divisorHeaderAw
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbSchoolbookDivisorTrim.divisorAfterHeader aw (UInt256.ofNat divisorPtr) = aw := by
  simpa only [MultiLimbSchoolbookDivisorTrim.divisorAfterHeader,
    MultiLimbSchoolbookNormalization.arrayAfterHeader,
    MultiLimbSchoolbookSingle.arrayAfterHeader] using facts.divisorLayout.headerAw

theorem divisorTopAw
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbSchoolbookDivisorTrim.divisorAfterWord aw (UInt256.ofNat divisorPtr)
      (divisorCount - 1) = aw := by
  simpa only [MultiLimbSchoolbookDivisorTrim.divisorAfterWord,
    MultiLimbSchoolbookNormalization.arrayAfterWord,
    MultiLimbSchoolbookSingle.arrayAfterWord] using
      facts.divisorLayout.wordAw (divisorCount - 1) (by
        have := facts.divisorTwo
        omega)

/-- Allocating the branch-local one-word quotient preserves all three prior array layouts and
extends the active observer beyond them. -/
theorem allocatedLayouts
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbArrayReadSemantic.Layout
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) dividendPtr dividendCount ∧
      MultiLimbArrayReadSemantic.Layout
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) divisorPtr divisorCount ∧
      MultiLimbArrayReadSemantic.Layout
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) remPtr divisorCount := by
  have hnext := facts.nextAllocationBound
  have hdivisorEnd := facts.divisorEndBeforeDividend
  have hdividendEnd := facts.dividendEndBeforeRemainder
  have hremainderEnd := facts.remainderEndBeforeFp
  have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1 (by omega)
    facts.awFit hfit
  have hallocatedSize :
      (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
    unfold MultiLimbSchoolbookShort.shortAllocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size facts.memory96]
      exact facts.memoryLeFp
    · rw [setFreePtr_size facts.memory96]
      exact facts.fpGap
  have hdivisor96 := facts.divisorPtr96
  have hdividend96 : 96 ≤ dividendPtr := by omega
  have hrem96 : 96 ≤ remPtr := by omega
  have build : ∀ ptr count,
      96 ≤ ptr → ptr + 32 + 32 * count ≤ fp →
      mem.readWithPadding ptr 32 = UInt256.toByteArray (UInt256.ofNat count) →
      MultiLimbArrayReadSemantic.Layout
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) ptr count := by
    intro ptr count hptr96 hend hheader
    apply MultiLimbArrayReadSemantic.layout_of_geometry
    · have hfp64 : fp < 2 ^ 64 := by omega
      exact lt_trans (by omega) (by norm_num [UInt256.size] : 2 ^ 64 < UInt256.size)
    · rw [hallocatedSize]
      omega
    · simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
        le_trans hend (by omega : fp ≤ fp + 32 + 32 * 1) |>.trans hrange.1
    · simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2
    · exact (MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_read_below
        mem fp ptr facts.memory96 facts.fpGap hptr96 (by omega)).trans hheader
  exact ⟨build dividendPtr dividendCount hdividend96 (by omega) facts.dividendHeaderRead,
    build divisorPtr divisorCount hdivisor96 (by omega) facts.divisorHeaderRead,
    build remPtr divisorCount hrem96 facts.remainderEndBeforeFp facts.remainderHeaderRead⟩

/-- The branch-local quotient allocation preserves every word of an older physically materialized
operand ending before the remainder header. -/
theorem allocatedOperandWords_eq
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp ptr count : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hptr96 : 96 ≤ ptr)
    (hend : ptr + 32 + 32 * count ≤ remPtr) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat ptr) 0 count =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat ptr) 0 count := by
  have hnext := facts.nextAllocationBound
  have hremEnd := facts.remainderEndBeforeFp
  have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1 (by omega)
    facts.awFit hfit
  have hallocatedSize :
      (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
    unfold MultiLimbSchoolbookShort.shortAllocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size facts.memory96]
      exact facts.memoryLeFp
    · rw [setFreePtr_size facts.memory96]
      exact facts.fpGap
  have hcovered := facts.memoryCovered
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
  apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
  intro i hi
  simp only [Nat.zero_add]
  have hwordFit : ptr + 32 * (i + 1) < UInt256.size := by
    exact lt_trans (by omega : ptr + 32 * (i + 1) < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hread := MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_read_below
    mem fp (ptr + 32 * (i + 1)) facts.memory96 facts.fpGap (by omega) (by omega)
  apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
  · exact hwordFit
  · rw [hallocatedSize]
    omega
  · rw [facts.memorySizeEq]
    omega
  · simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : ptr + 32 * (i + 1) + 32 ≤ fp) (le_trans (by omega) hrange.1)
  · exact le_trans (by rw [facts.memorySizeEq]; omega) hcovered
  · simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2
  · exact facts.awFit
  · exact hread

/-- The physically preserved divisor top remains nonzero after branch-local quotient allocation. -/
theorem allocatedDivisorTopNonzero
    {mem : ByteArray} {aw : UInt256} {dividendPtr divisorPtr remPtr : Nat}
    {dividendCount divisorCount fp : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp) :
    MultiLimbSchoolbookNormalization.arrayWord
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat divisorPtr) (divisorCount - 1) ≠ ⟨0⟩ := by
  have hnext := facts.nextAllocationBound
  have hdivisorEnd := facts.divisorEndBeforeDividend
  have hdividendEnd := facts.dividendEndBeforeRemainder
  have hremainderEnd := facts.remainderEndBeforeFp
  have hmemorySize := facts.memorySizeEq
  have hdivisor96 := facts.divisorPtr96
  have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1 (by omega)
    facts.awFit hfit
  have hallocatedSize :
      (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
    unfold MultiLimbSchoolbookShort.shortAllocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size facts.memory96]
      exact facts.memoryLeFp
    · rw [setFreePtr_size facts.memory96]
      exact facts.fpGap
  have hcovered := facts.memoryCovered
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
  have hindex : divisorCount - 1 < divisorCount := by
    have := facts.divisorTwo
    omega
  have hcount : divisorCount - 1 + 1 = divisorCount := by
    have := facts.divisorTwo
    omega
  have hwordFit : divisorPtr + 32 * ((divisorCount - 1) + 1) < UInt256.size := by
    rw [hcount]
    exact lt_trans (by omega : divisorPtr + 32 * divisorCount < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hread := MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_read_below
    mem fp (divisorPtr + 32 * ((divisorCount - 1) + 1)) facts.memory96 facts.fpGap
    (by omega) (by rw [hcount]; omega)
  have hleftMem : divisorPtr + 32 * ((divisorCount - 1) + 1) + 32 ≤
      (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size := by
    rw [hcount, hallocatedSize]
    omega
  have hrightMem : divisorPtr + 32 * ((divisorCount - 1) + 1) + 32 ≤ mem.size := by
    rw [hcount, hmemorySize]
    omega
  have hleftActive : divisorPtr + 32 * ((divisorCount - 1) + 1) + 32 ≤
      32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat := by
    rw [hcount]
    simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : divisorPtr + 32 * divisorCount + 32 ≤ fp)
        (le_trans (by omega) hrange.1)
  have hrightActive : divisorPtr + 32 * ((divisorCount - 1) + 1) + 32 ≤
      32 * aw.toNat := by
    exact le_trans hrightMem hcovered
  have heq := MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
    (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp) mem
    (MultiLimbSchoolbookShort.shortAllocatedWords aw fp) aw divisorPtr
    (divisorCount - 1) hwordFit hleftMem hrightMem hleftActive hrightActive
    (by simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2)
    facts.awFit hread
  intro hzero
  apply facts.divisorTopNonzero
  rw [← heq]
  exact hzero

end DivisionEntryFacts

/-- Execute the exact all-zero dividend scan, branch-local allocation, and Barrett return using
only the shared PC5199 entry facts. -/
theorem allZeroReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {tail : List UInt256}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hzero : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1005)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat divisorPtr :: tail)
      (MultiLimbSchoolbookZero.allocatedMemory mem fp)
      (MultiLimbSchoolbookZero.allocatedWords aw fp)
      rdata acc (steps + MultiLimbBarrettReduceBaseExecutable.zeroReturnSteps dividendCount)
      (gasUsed + MultiLimbBarrettReduceBaseExecutable.zeroReturnGas aw fp dividendCount) := by
  apply MultiLimbBarrettReduceBaseExecutable.zeroDivisionReturnExact
  · exact facts.dividendBound
  · exact facts.dividendHeader
  · exact facts.dividendHeaderAw
  · exact facts.dividendWordAw
  · exact hzero
  · exact facts.fp96
  · exact facts.nextAllocationBound
  · exact facts.memory96
  · exact facts.memoryLeFp
  · exact facts.fpGap
  · exact facts.aw3
  · exact facts.aw64
  · exact facts.freeRead
  · exact hcalldata
  · exact htail
  · exact h

/-- An all-zero trim outcome identifies the complete entry dividend value as zero. -/
theorem allZeroEntryValue
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    (_facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hzero : ∀ i, i < dividendCount →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩) :
    wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw
        (UInt256.ofNat dividendPtr) 0 dividendCount) = 0 :=
  MultiLimbSchoolbookTrimSelection.allZero_value mem aw (UInt256.ofNat dividendPtr)
    dividendCount hzero

/-- Removing the selected high zero limbs does not change the concrete dividend value. -/
theorem trimmedValue_eq_entry
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr dividendCount m zeroLimbs : Nat}
    (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩) :
    wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat dividendPtr) 0 dividendCount) =
      wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat dividendPtr) 0 m) := by
  have hhighZero : wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw
        (UInt256.ofNat dividendPtr) m zeroLimbs) = 0 := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
    intro i hi
    simpa only [MultiLimbSchoolbookNormalization.arrayWord,
      MultiLimbSchoolbookSingle.arrayWord, MultiLimbSchoolbookTrim.dividendWord,
      Nat.add_assoc] using hzero (m + i) (by omega) (by omega)
  have hsplit := MultiLimbSchoolbookOuterComplete.arrayReadWords_add mem aw
    (UInt256.ofNat dividendPtr) 0 m zeroLimbs
  have hsum : m + zeroLimbs = dividendCount := by omega
  rw [hsum] at hsplit
  simp only [Nat.zero_add] at hsplit
  rw [hsplit, wordLimbsToNat_append,
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length, hhighZero]
  simp

/-- Execute the selected positive short-dividend branch, including both leading-zero scans, the
size dispatch, the concrete copy loop, and Barrett's PC 3010 return. -/
theorem shortReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {m zeroLimbs : Nat} {top : UInt256} {tail : List UInt256}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hmPos : 0 < m) (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (htop : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
      (m - 1) = top)
    (htopNonzero : top ≠ ⟨0⟩)
    (hshort : m < divisorCount)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1005)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat divisorPtr :: tail)
      (MultiLimbSchoolbookShort.copyLoopMemory
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m)
      (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
      rdata acc (steps + MultiLimbBarrettReduceBaseExecutable.shortReturnSteps m zeroLimbs)
      (gasUsed + MultiLimbBarrettReduceBaseExecutable.shortReturnGas aw fp m zeroLimbs) := by
  have hdividendTopAw := facts.dividendWordAw (m - 1) (by omega)
  have hdivisorTopAw := facts.divisorTopAw
  let divisorTop := MultiLimbSchoolbookNormalization.arrayWord mem aw
    (UInt256.ofNat divisorPtr) (divisorCount - 1)
  have hdivisorTopEq : MultiLimbSchoolbookDivisorTrim.divisorWord mem aw
      (UInt256.ofNat divisorPtr) (divisorCount - 1) = divisorTop := by
    rfl
  have rdBranch := MultiLimbSchoolbookNonzeroPrefix.exactToSelectedSizeBranch
    (tail := ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
    (m := m) (zeroLimbs := zeroLimbs) (divisorCount := divisorCount)
    (dividendCount := dividendCount) (dividendTop := top) (divisorTop := divisorTop)
    (by simp only [List.length_cons]; omega) hmPos hcount facts.divisorTwo
    (by have := facts.dividendBound; omega) facts.divisorBound facts.dividendHeader
    facts.dividendHeaderAw
    (fun i hmi hi => facts.dividendWordAw i (by omega)) hzero hdividendTopAw htop
    htopNonzero facts.divisorHeader facts.divisorHeaderAw hdivisorTopAw hdivisorTopEq
    facts.divisorTopNonzero h
  have rd6214 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6214⟩
      (UInt256.ofNat divisorCount :: UInt256.ofNat m :: UInt256.ofNat remPtr ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorPtr ::
        ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc (steps + 134 + 72 * zeroLimbs)
      (gasUsed + 491 + 270 * zeroLimbs) := by
    simpa [MultiLimbSchoolbookNonzeroPrefix.sizeBranchPc, hshort] using rdBranch
  have layouts := facts.allocatedLayouts
  have hnext := facts.nextAllocationBound
  have hdivisorEnd := facts.divisorEndBeforeDividend
  have hdividendEnd := facts.dividendEndBeforeRemainder
  have hremainderEnd := facts.remainderEndBeforeFp
  have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1 (by omega)
    facts.awFit hfit
  have hallocatedSize :
      (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
    unfold MultiLimbSchoolbookShort.shortAllocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size facts.memory96]
      exact facts.memoryLeFp
    · rw [setFreePtr_size facts.memory96]
      exact facts.fpGap
  have addressNat : ∀ ptr i, ptr + 32 * (i + 1) < UInt256.size →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) i).toNat =
        ptr + 32 * (i + 1) := by
    intro ptr i hptr
    unfold MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt (by omega : ptr < UInt256.size)] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat ptr) i (by
        simpa [UInt256.toNat_ofNat_of_lt (by omega : ptr < UInt256.size)] using hptr)
  have hfpWord : fp < UInt256.size :=
    lt_trans (by omega : fp < 2 ^ 64) (by norm_num [UInt256.size])
  have hdividendPtrWord : dividendPtr < UInt256.size := by omega
  have hremPtrWord : remPtr < UInt256.size := by omega
  have hwrite : ∀ i, i < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size := by
    intro i hi
    rw [addressNat remPtr i (by omega), hallocatedSize]
    omega
  have hdivHeaderBelow : ∀ j, j < m →
      (UInt256.ofNat dividendPtr).toNat + 32 ≤
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) j).toNat := by
    intro j hj
    rw [UInt256.toNat_ofNat_of_lt hdividendPtrWord, addressNat remPtr j (by omega)]
    omega
  have hdivElementBelow : ∀ i, i < m → ∀ j, j < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat dividendPtr) i).toNat + 32 ≤
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) j).toNat := by
    intro i hi j hj
    rw [addressNat dividendPtr i (by omega), addressNat remPtr j (by omega)]
    omega
  have hremHeaderBelow : ∀ j, j < m →
      (UInt256.ofNat remPtr).toNat + 32 ≤
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) j).toNat := by
    intro j hj
    rw [UInt256.toNat_ofNat_of_lt hremPtrWord, addressNat remPtr j (by omega)]
    omega
  have hremElementBelow : ∀ i, i < m → ∀ j, j < m → i < j →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) j).toNat := by
    intro i hi j hj hij
    rw [addressNat remPtr i (by omega), addressNat remPtr j (by omega)]
    omega
  have hdivHeaderActive : (UInt256.ofNat dividendPtr).toNat + 32 ≤
      32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hdividendPtrWord]
    simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : dividendPtr + 32 ≤ fp) (le_trans (by omega) hrange.1)
  have hdivElementActive : ∀ i, i < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat dividendPtr) i).toNat + 32 ≤
        32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat := by
    intro i hi
    rw [addressNat dividendPtr i (by omega)]
    simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : dividendPtr + 32 * (i + 1) + 32 ≤ fp) (le_trans (by omega) hrange.1)
  have hremHeaderActive : (UInt256.ofNat remPtr).toNat + 32 ≤
      32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hremPtrWord]
    simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : remPtr + 32 ≤ fp) (le_trans (by omega) hrange.1)
  have hremElementActive : ∀ i, i < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
        32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat := by
    intro i hi
    rw [addressNat remPtr i (by omega)]
    simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : remPtr + 32 * (i + 1) + 32 ≤ fp) (le_trans (by omega) hrange.1)
  have rd3010AndWords := MultiLimbSchoolbookShort.executeThroughReturnOfLayout
    (fp := fp) (m := m) (dividendCount := dividendCount) (remCount := divisorCount)
    (tail := ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
    facts.fp96 facts.nextAllocationBound facts.memory96 facts.memoryLeFp facts.fpGap
    facts.aw3 facts.aw64 facts.freeRead hcalldata
    (by simp only [List.length_cons]; omega) (by omega) (by omega)
    facts.dividendBound facts.divisorBound (by
      simpa only [MultiLimbSchoolbookNormalization.arrayHeader,
        MultiLimbSchoolbookSingle.arrayHeader] using layouts.1.header) (by
      simpa only [MultiLimbSchoolbookNormalization.arrayHeader,
        MultiLimbSchoolbookSingle.arrayHeader] using layouts.2.2.header)
    hwrite hdivHeaderBelow hdivElementBelow hremHeaderBelow hremElementBelow
    (by simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2)
    hdivHeaderActive hdivElementActive hremHeaderActive hremElementActive
    (by native_decide) rd6214
  have rd1707 := MultiLimbBarrettConstant.divisionReturnExact
    (tail := tail) (by omega) rd3010AndWords.1
  exact rd1707.withIndices
    (by simp [MultiLimbBarrettReduceBaseExecutable.shortReturnSteps,
      MultiLimbSchoolbookShortFunction.totalSteps]; omega)
    (by simp [MultiLimbBarrettReduceBaseExecutable.shortReturnGas,
      MultiLimbSchoolbookShortFunction.totalGas]; omega)

/-- The exact short-copy result is the complete entry dividend modulo the complete concrete
divisor.  Trimmed dividend limbs and untouched high remainder limbs are both proved zero. -/
theorem shortResult_eq_entry_mod
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m zeroLimbs : Nat}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hmPos : 0 < m) (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (hshort : m < divisorCount) :
    wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (MultiLimbSchoolbookShort.copyLoopMemory
            (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
            (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
            (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) m)
          (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
          (UInt256.ofNat remPtr) 0 divisorCount) =
      wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat dividendPtr) 0 dividendCount) %
        wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  have hnext := facts.nextAllocationBound
  have hdivisorEnd := facts.divisorEndBeforeDividend
  have hdividendEnd := facts.dividendEndBeforeRemainder
  have hremainderEnd := facts.remainderEndBeforeFp
  have hmemorySize := facts.memorySizeEq
  have hrem96 : 96 ≤ remPtr := by
    have := facts.divisorPtr96
    omega
  have hfit : fp + wordArrayAllocationSize 1 + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize 1 + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp 1 (by omega)
    facts.awFit hfit
  have hallocatedSize :
      (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size = fp + 32 := by
    unfold MultiLimbSchoolbookShort.shortAllocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size facts.memory96]
      exact facts.memoryLeFp
    · rw [setFreePtr_size facts.memory96]
      exact facts.fpGap
  have addressNat : ∀ ptr i, ptr + 32 * (i + 1) < UInt256.size →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) i).toNat =
        ptr + 32 * (i + 1) := by
    intro ptr i hptr
    unfold MultiLimbSchoolbookShort.arrayAddress
    simpa [UInt256.toNat_ofNat_of_lt (by omega : ptr < UInt256.size)] using
      MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat ptr) i (by
        simpa [UInt256.toNat_ofNat_of_lt (by omega : ptr < UInt256.size)] using hptr)
  have hwrite : ∀ i, i < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp).size := by
    intro i hi
    rw [addressNat remPtr i (by
      exact lt_trans (by omega : remPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])), hallocatedSize]
    omega
  have hsourceBelow : ∀ i, i < m → ∀ j, j < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat dividendPtr) i).toNat + 32 ≤
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) j).toNat := by
    intro i hi j hj
    rw [addressNat dividendPtr i (by
      exact lt_trans (by omega : dividendPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])),
      addressNat remPtr j (by
        exact lt_trans (by omega : remPtr + 32 * (j + 1) < 2 ^ 64)
          (by norm_num [UInt256.size]))]
    omega
  have hdestinationBelow : ∀ i, i < divisorCount → ∀ j, j < divisorCount → i < j →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
        (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) j).toNat := by
    intro i hi j hj hij
    rw [addressNat remPtr i (by
      exact lt_trans (by omega : remPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])),
      addressNat remPtr j (by
        exact lt_trans (by omega : remPtr + 32 * (j + 1) < 2 ^ 64)
          (by norm_num [UInt256.size]))]
    omega
  have hdestinationActive : ∀ i, i < m →
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat remPtr) i).toNat + 32 ≤
        32 * (MultiLimbSchoolbookShort.shortAllocatedWords aw fp).toNat := by
    intro i hi
    rw [addressNat remPtr i (by
      exact lt_trans (by omega : remPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size]))]
    simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
      le_trans (by omega : remPtr + 32 * (i + 1) + 32 ≤ fp)
        (le_trans (by omega) hrange.1)
  have hinitialHighZero : ∀ i, m ≤ i → i < divisorCount →
      MultiLimbSchoolbookNormalization.arrayWord
        (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
        (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
        (UInt256.ofNat remPtr) i = ⟨0⟩ := by
    intro i hmi hi
    have haddrFit : remPtr + 32 * (i + 1) < UInt256.size :=
      lt_trans (by omega : remPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])
    apply MultiLimbSchoolbookShortSemantic.shortAllocatedMemory_arrayWord_zero
    · exact facts.memory96
    · exact facts.memoryLeFp
    · exact facts.fpGap
    · simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2
    · rw [addressNat remPtr i haddrFit]
      omega
    · rw [addressNat remPtr i haddrFit, hmemorySize]
      omega
    · rw [addressNat remPtr i haddrFit]
      omega
    · rw [addressNat remPtr i haddrFit]
      simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using
        le_trans (by omega : remPtr + 32 * (i + 1) + 32 ≤ fp)
          (le_trans (by omega) hrange.1)
  have hresult := MultiLimbSchoolbookShortSemantic.copyLoopMemory_eq_concrete_mod
    (MultiLimbSchoolbookShort.shortAllocatedMemory mem fp)
    (MultiLimbSchoolbookShort.shortAllocatedWords aw fp)
    (UInt256.ofNat dividendPtr) (UInt256.ofNat remPtr) (UInt256.ofNat divisorPtr)
    m divisorCount hshort
    (by simpa only [MultiLimbSchoolbookShort.shortAllocatedWords] using hrange.2)
    hwrite hsourceBelow hdestinationBelow hdestinationActive hinitialHighZero
    facts.allocatedDivisorTopNonzero
  have hdividend96 : 96 ≤ dividendPtr := by
    have := facts.divisorPtr96
    omega
  have hallocatedDividend := facts.allocatedOperandWords_eq hdividend96 (count := m) (by
    omega)
  have hallocatedDivisor := facts.allocatedOperandWords_eq facts.divisorPtr96
    (ptr := divisorPtr) (count := divisorCount) (by omega)
  have hhighZero : wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw
        (UInt256.ofNat dividendPtr) m zeroLimbs) = 0 := by
    apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
    intro i hi
    simpa only [MultiLimbSchoolbookNormalization.arrayWord,
      MultiLimbSchoolbookSingle.arrayWord, MultiLimbSchoolbookTrim.dividendWord,
      Nat.add_assoc] using hzero (m + i) (by omega) (by omega)
  have hsplit := MultiLimbSchoolbookOuterComplete.arrayReadWords_add mem aw
    (UInt256.ofNat dividendPtr) 0 m zeroLimbs
  have hsum : m + zeroLimbs = dividendCount := by omega
  rw [hsum] at hsplit
  simp only [Nat.zero_add] at hsplit
  have htrimmedValue : wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw
        (UInt256.ofNat dividendPtr) 0 dividendCount) =
      wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw
          (UInt256.ofNat dividendPtr) 0 m) := by
    rw [hsplit, wordLimbsToNat_append,
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length, hhighZero]
    simp
  rw [hresult, hallocatedDividend, hallocatedDivisor, htrimmedValue]

/-- Execute the concrete leading-zero scans and size comparison for a selected Knuth branch. -/
theorem knuthPrefixExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {m zeroLimbs : Nat} {top : UInt256} {tail : List UInt256}
    (facts : DivisionEntryFacts mem aw dividendPtr divisorPtr remPtr
      dividendCount divisorCount fp)
    (hmPos : 0 < m) (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (htop : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
      (m - 1) = top)
    (htopNonzero : top ≠ ⟨0⟩)
    (hknuth : divisorCount ≤ m)
    (htail : tail.length ≤ 1005)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5287⟩
      (UInt256.ofNat divisorCount :: UInt256.ofNat m :: UInt256.ofNat remPtr ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorPtr ::
        ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc (steps + 134 + 72 * zeroLimbs)
      (gasUsed + 491 + 270 * zeroLimbs) := by
  have hdividendTopAw := facts.dividendWordAw (m - 1) (by omega)
  let divisorTop := MultiLimbSchoolbookNormalization.arrayWord mem aw
    (UInt256.ofNat divisorPtr) (divisorCount - 1)
  have hdivisorTopEq : MultiLimbSchoolbookDivisorTrim.divisorWord mem aw
      (UInt256.ofNat divisorPtr) (divisorCount - 1) = divisorTop := by rfl
  have rdBranch := MultiLimbSchoolbookNonzeroPrefix.exactToSelectedSizeBranch
    (tail := ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
    (m := m) (zeroLimbs := zeroLimbs) (divisorCount := divisorCount)
    (dividendCount := dividendCount) (dividendTop := top) (divisorTop := divisorTop)
    (by simp only [List.length_cons]; omega) hmPos hcount facts.divisorTwo
    (by have := facts.dividendBound; omega) facts.divisorBound facts.dividendHeader
    facts.dividendHeaderAw (fun i hmi hi => facts.dividendWordAw i (by omega)) hzero
    hdividendTopAw htop htopNonzero facts.divisorHeader facts.divisorHeaderAw
    facts.divisorTopAw hdivisorTopEq facts.divisorTopNonzero h
  have hnotShort : ¬m < divisorCount := by omega
  simpa [MultiLimbSchoolbookNonzeroPrefix.sizeBranchPc, hnotShort] using rdBranch

/-- The top divisor load at PC 5199 is nonzero because the deployed scanner selected a nonzero
first modulus byte and the final converted array still denotes that source modulus. -/
theorem finalDivisorTop_nonzero
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmodulusFp : 96 ≤ modulusFp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSource96 : 96 ≤ dataPtr + 32)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hsource256 : dataPtr + 32 < UInt256.size)
    (hsource64 : dataPtr + 32 < 2 ^ 64)
    (hsourceActive : dataPtr + 64 ≤ 32 * aw.toNat)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (dataPtr + 32))) ≠ ⟨0⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusEnd : modulusFp + 32 +
      32 * MultiLimbBarrettConversion.words modulusSize ≤ baseFp)
    (hmodulusMemoryLe :
      (MultiLimbBarrettReduceBaseSemantic.modulusMemory
        mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (MultiLimbBarrettReduceBaseSemantic.modulusMemory
        mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize)
        (MultiLimbBarrettReduceBaseSemantic.modulusWords
          mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize)
        (MultiLimbBarrettReduceBaseSemantic.modulusWords
          mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayWord
        (MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw basePtr modulusFp dataPtr
          modulusSize baseFp remFp baseSize)
        (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
          modulusSize baseFp remFp baseSize)
        (UInt256.ofNat modulusFp)
        (MultiLimbBarrettConversion.words modulusSize - 1) ≠ ⟨0⟩ := by
  have hlower := MultiLimbBarrettDispatch.modulusLimbLower_of_firstByte mem aw dataPtr
    modulusSize hmodulusLarge hsource256 hsource64 hsourceActive hawFit hfirst
  have hvalue := MultiLimbBarrettReduceBaseSemantic.finalModulusArrayValue_eq_model
    mem aw basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge
    hmodulusBound hmodulusFp hmemSize hmemLe hmodulusGap hmodulusSource96
    hmodulusSourceBefore hawFit hmodulusAllocationBound hmodulusEnd hmodulusMemoryLe
    hbaseGap hbasePos hbaseSize hbaseSourceBefore hbaseAllocationBound hbaseConvertedLe
    hremGap hremBound
  apply MultiLimbSchoolbookTrimSelection.top_nonzero_of_value_lower
  · unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  · rw [hvalue]
    simpa only [MultiLimbBarrettConversion.words] using hlower

/-- The real conversion/allocation chain constructs every compact PC5199 selector fact. -/
theorem finalEntryFacts
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat)
    (hmodulusLarge : 32 < modulusSize) (hmodulusBound : modulusSize ≤ 1024)
    (hmodulusFp : 96 ≤ modulusFp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ modulusFp)
    (hmodulusGap : modulusFp - mem.size < USize.size)
    (hmodulusSource96 : 96 ≤ dataPtr + 32)
    (hmodulusSourceBefore : dataPtr + 32 + modulusSize ≤ modulusFp)
    (hsource256 : dataPtr + 32 < UInt256.size)
    (hsource64 : dataPtr + 32 < 2 ^ 64)
    (hsourceActive : dataPtr + 64 ≤ 32 * aw.toNat)
    (hfirst : UInt256.byteAt ⟨0⟩
      (wideLoadWord mem aw (UInt256.ofNat (dataPtr + 32))) ≠ ⟨0⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmodulusAllocationBound : modulusFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hmodulusEnd : modulusFp + 32 +
      32 * MultiLimbBarrettConversion.words modulusSize ≤ baseFp)
    (hmodulusMemoryLe :
      (MultiLimbBarrettReduceBaseSemantic.modulusMemory
        mem aw modulusFp dataPtr modulusSize).size ≤ baseFp)
    (hbaseGap : baseFp -
      (MultiLimbBarrettReduceBaseSemantic.modulusMemory
        mem aw modulusFp dataPtr modulusSize).size < USize.size)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024)
    (hbaseSourceBefore : basePtr.toNat + 32 + baseSize ≤ baseFp)
    (hbaseAllocationBound : baseFp + wordArrayAllocationSize
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) < 2 ^ 64)
    (hbaseEnd : baseFp + 32 + 32 * MultiLimbReduceBase.baseWords baseSize
      (MultiLimbBarrettConversion.words modulusSize) ≤ remFp)
    (hbaseConvertedLe :
      (MultiLimbReduceBase.convertedMemory
        (MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize)
        (MultiLimbBarrettReduceBaseSemantic.modulusWords
          mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size ≤ remFp)
    (hremGap : remFp -
      (MultiLimbReduceBase.convertedMemory
        (MultiLimbBarrettReduceBaseSemantic.modulusMemory
          mem aw modulusFp dataPtr modulusSize)
        (MultiLimbBarrettReduceBaseSemantic.modulusWords
          mem aw modulusFp dataPtr modulusSize)
        baseFp baseSize (MultiLimbBarrettConversion.words modulusSize) basePtr).size <
        USize.size)
    (hremBound : remFp + wordArrayAllocationSize
      (MultiLimbBarrettConversion.words modulusSize) < 2 ^ 64)
    (hnextBound : remFp + wordArrayAllocationSize
        (MultiLimbBarrettConversion.words modulusSize) + wordArrayAllocationSize 1 <
      2 ^ 64) :
    DivisionEntryFacts
      (MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw basePtr modulusFp dataPtr
        modulusSize baseFp remFp baseSize)
      (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
        modulusSize baseFp remFp baseSize)
      baseFp modulusFp remFp
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize))
      (MultiLimbBarrettConversion.words modulusSize)
      (remFp + wordArrayAllocationSize (MultiLimbBarrettConversion.words modulusSize)) := by
  have hgeometry := MultiLimbBarrettReduceBaseSemantic.finalGeometry mem aw basePtr
    modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge hmodulusBound
    hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
    hmodulusMemoryLe hbaseGap hbasePos hbaseSize hbaseSourceBefore hbaseAllocationBound
    hbaseConvertedLe hremGap hremBound
  have hlayouts := MultiLimbBarrettReduceBaseSemantic.finalLayouts mem aw basePtr
    modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge hmodulusBound
    hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
    hmodulusEnd hmodulusMemoryLe hbaseGap hbasePos hbaseSize hbaseSourceBefore
    hbaseAllocationBound hbaseEnd hbaseConvertedLe hremGap hremBound
  have hremLayout := MultiLimbBarrettReduceBaseSemantic.finalRemainderLayout mem aw basePtr
    modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge hmodulusBound
    hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
    hmodulusMemoryLe hbaseGap hbasePos hbaseSize hbaseSourceBefore hbaseAllocationBound
    hbaseConvertedLe hremGap hremBound
  have hbaseHeader := MultiLimbBarrettReduceBaseSemantic.finalBaseHeader_read mem aw basePtr
    modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge hmodulusBound
    hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
    hmodulusMemoryLe hbaseGap hbaseSize hbaseAllocationBound (by omega)
    hbaseConvertedLe hremGap
  have hmodulusHeader := MultiLimbBarrettReduceBaseSemantic.finalModulusHeader_read mem aw
    basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge
    hmodulusBound hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit
    hmodulusAllocationBound (by omega) hmodulusMemoryLe hbaseGap hbaseSize
    hbaseAllocationBound hbaseConvertedLe hremGap
  have hremHeader := MultiLimbBarrettReduceBaseSemantic.finalRemainderHeader_read mem aw
    basePtr modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge
    hmodulusBound hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit
    hmodulusAllocationBound hmodulusMemoryLe hbaseGap hbaseSize hbaseAllocationBound hremGap
  have htop := finalDivisorTop_nonzero mem aw basePtr modulusFp dataPtr modulusSize
    baseFp remFp baseSize hmodulusLarge hmodulusBound hmodulusFp hmemSize hmemLe
    hmodulusGap hmodulusSource96 hmodulusSourceBefore hsource256 hsource64 hsourceActive
    hfirst hawFit hmodulusAllocationBound hmodulusEnd hmodulusMemoryLe hbaseGap
    hbasePos hbaseSize hbaseSourceBefore hbaseAllocationBound hbaseConvertedLe hremGap
    hremBound
  have hfree := MultiLimbBarrettReduceBaseSemantic.finalFree_read mem aw basePtr
    modulusFp dataPtr modulusSize baseFp remFp baseSize hmodulusLarge hmodulusBound
    hmemSize hmemLe hmodulusGap hmodulusSourceBefore hawFit hmodulusAllocationBound
    hmodulusMemoryLe hbaseGap hbaseSize hbaseAllocationBound hbaseConvertedLe hremGap
  have hkTwo : 2 ≤ MultiLimbBarrettConversion.words modulusSize := by
    unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hkBound : MultiLimbBarrettConversion.words modulusSize ≤ 32 := by
    unfold MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hbaseWordsBound : MultiLimbReduceBase.baseWords baseSize
      (MultiLimbBarrettConversion.words modulusSize) ≤ 32 := by
    unfold MultiLimbReduceBase.baseWords MultiLimbReduceBase.naturalWords
    omega
  have hremFp : 96 ≤ remFp := by omega
  have hcovered := hgeometry.2.1
  have hcoveredNat := hcovered
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcoveredNat
  rw [hgeometry.1] at hcoveredNat
  have haw3 : 3 ≤
      (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
        modulusSize baseFp remFp baseSize).toNat := by
    omega
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥
      MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
        modulusSize baseFp remFp baseSize * ⟨32⟩ := by
    have hmul :
        (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
          modulusSize baseFp remFp baseSize * (⟨32⟩ : UInt256)).toNat =
        (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
          modulusSize baseFp remFp baseSize).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat
          (a := MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp
            dataPtr modulusSize baseFp remFp baseSize)
          (b := (⟨32⟩ : UInt256)) hgeometry.2.2
    intro hle
    have hnat :
        (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
          modulusSize baseFp remFp baseSize * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  refine {
    dividendLayout := hlayouts.1
    divisorLayout := hlayouts.2
    remainderLayout := hremLayout
    dividendHeaderRead := hbaseHeader
    divisorHeaderRead := hmodulusHeader
    remainderHeaderRead := hremHeader
    divisorTopNonzero := htop
    dividendBound := hbaseWordsBound
    divisorTwo := hkTwo
    divisorBound := hkBound
    fp96 := by omega
    nextAllocationBound := hnextBound
    memory96 := by rw [hgeometry.1]; omega
    memoryLeFp := by
      rw [hgeometry.1]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    fpGap := by
      rw [hgeometry.1]
      unfold wordArrayAllocationSize wordArrayPayloadSize
      have : 32 * 32 < USize.size := by native_decide
      omega
    divisorPtr96 := hmodulusFp
    divisorEndBeforeDividend := hmodulusEnd
    dividendEndBeforeRemainder := hbaseEnd
    remainderEndBeforeFp := by
      unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    memorySizeEq := hgeometry.1
    memoryCovered := hcovered
    awFit := hgeometry.2.2
    aw3 := haw3
    aw64 := haw64
    freeRead := hfree
  }

/-- The real guarded dividend payload always has a constructive deployed trim outcome. -/
theorem finalDividendSelection_exists
    (mem : ByteArray) (aw basePtr : UInt256)
    (modulusFp dataPtr modulusSize baseFp remFp baseSize : Nat) :
    MultiLimbSchoolbookTrimSelection.Selection
      (MultiLimbBarrettReduceBaseSemantic.finalMemory mem aw basePtr modulusFp dataPtr
        modulusSize baseFp remFp baseSize)
      (MultiLimbBarrettReduceBaseSemantic.finalWords mem aw basePtr modulusFp dataPtr
        modulusSize baseFp remFp baseSize)
      (UInt256.ofNat baseFp)
      (MultiLimbReduceBase.baseWords baseSize
        (MultiLimbBarrettConversion.words modulusSize)) :=
  MultiLimbSchoolbookTrimSelection.selection_exists _ _ _ _

/-- Exposed total branch chosen by the deployed dividend scan and size comparison. -/
inductive BranchSelection
    (mem : ByteArray) (aw : UInt256) (dividendPtr dividendCount divisorCount : Nat) : Prop
  | allZero
      (zero : ∀ i, i < dividendCount →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩) :
      BranchSelection mem aw dividendPtr dividendCount divisorCount
  | short
      (m zeroLimbs : Nat) (top : UInt256)
      (mPos : 0 < m) (countEq : dividendCount = m + zeroLimbs)
      (zero : ∀ i, m ≤ i → i < m + zeroLimbs →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
      (topEq : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
        (m - 1) = top)
      (topNe : top ≠ ⟨0⟩) (ltDivisor : m < divisorCount) :
      BranchSelection mem aw dividendPtr dividendCount divisorCount
  | knuth
      (m zeroLimbs : Nat) (top : UInt256)
      (mPos : 0 < m) (countEq : dividendCount = m + zeroLimbs)
      (zero : ∀ i, m ≤ i → i < m + zeroLimbs →
        MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
      (topEq : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
        (m - 1) = top)
      (topNe : top ≠ ⟨0⟩) (divisorLe : divisorCount ≤ m) :
      BranchSelection mem aw dividendPtr dividendCount divisorCount

/-- Every concrete PC5199 dividend has exactly one of the deployed top-level branch shapes. -/
theorem branchSelection_exists
    (mem : ByteArray) (aw : UInt256) (dividendPtr dividendCount divisorCount : Nat) :
    BranchSelection mem aw dividendPtr dividendCount divisorCount := by
  cases MultiLimbSchoolbookTrimSelection.selection_exists
      mem aw (UInt256.ofNat dividendPtr) dividendCount with
  | allZero zero => exact .allZero zero
  | nonzero m zeroLimbs top mPos countEq zero topEq topNe =>
      by_cases hshort : m < divisorCount
      · exact .short m zeroLimbs top mPos countEq zero topEq topNe hshort
      · exact .knuth m zeroLimbs top mPos countEq zero topEq topNe (by omega)

end Modexp.MultiLimbBarrettReduceBaseSelection
