import Examples.Precompiles.Modexp.MultiLimbBarrettConstantSemantic
import Examples.Precompiles.Modexp.MultiLimbBarrettContinuationExecutable
import Examples.Precompiles.Modexp.MultiLimbSchoolbookNonzeroPrefix

/-!
# Complete Barrett-constant execution

This module composes the concrete `B^(2*k)` numerator created by
`_computeBarrettConstant` with the deployed schoolbook division.  In particular, the numerator's
written high limb forces the non-short Knuth branch; this is not a proof-only path assumption.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettConstantComplete

open MultiLimbBarrettConstant
open MultiLimbBarrettConstantSemantic
open MultiLimbSchoolbookNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Pointwise preservation of quotient words lifts to the little-endian quotient observer. -/
theorem quotientReadNats_eq_of_words
    (after before : ByteArray) (aw quotient : UInt256) (count : Nat) :
    (∀ i, i < count -> arrayWord after aw quotient i = arrayWord before aw quotient i) ->
      MultiLimbSchoolbookOuterComplete.quotientReadNats after aw quotient count =
        MultiLimbSchoolbookOuterComplete.quotientReadNats before aw quotient count := by
  induction count with
  | zero => intro; rfl
  | succ count ih =>
      intro hwords
      simp only [MultiLimbSchoolbookOuterComplete.quotientReadNats]
      rw [ih (fun i hi => hwords i (by omega))]
      have hword := hwords count (by omega)
      change MultiLimbSchoolbookSingle.arrayWord after aw quotient count =
        MultiLimbSchoolbookSingle.arrayWord before aw quotient count at hword
      rw [hword]

/-- The quotient observer is the natural-word view of the same concrete consecutive payload used
by the Barrett exponent invariant. -/
theorem quotientReadNats_eq_memoryWordsFrom_map
    (mem : ByteArray) (aw : UInt256) (ptr count : Nat)
    (hfit : ptr + 32 * (count + 1) < UInt256.size)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MultiLimbSchoolbookOuterComplete.quotientReadNats mem aw (UInt256.ofNat ptr) count =
      (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (ptr + 32) count).map
        UInt256.toNat := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [MultiLimbSchoolbookOuterComplete.quotientReadNats,
        MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append, List.map_append,
        ih (by omega)]
      simp only [List.map_singleton]
      congr 2
      rw [UInt256.toNat_ofNat_of_lt
        (MultiLimbMontgomeryCIOSSemantic.memoryWordNat_lt_size mem (ptr + 32 + 32 * count))]
      exact MultiLimbArrayReadSemantic.arrayWord_toNat_eq_memoryWordNat mem aw ptr count
        (by omega) hcovered hawFit

/-- At radix `2^256`, the schoolbook quotient evaluator and the shared limb evaluator coincide. -/
theorem natLimbsToNat_size_eq_limbsToNat (limbs : List Nat) :
    MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size limbs =
      Modexp.limbsToNat limbs := by
  induction limbs with
  | nil => rfl
  | cons limb limbs ih =>
      simp only [MultiLimbSchoolbookOuterComplete.natLimbsToNat, Modexp.limbsToNat, ih]
      rw [show UInt256.size = 256 ^ 32 by norm_num [UInt256.size]]

/-- The exposed quotient value is exactly the shared `memoryWordsFrom` value. -/
theorem quotientReadNats_value_eq_memoryWordsFrom
    (mem : ByteArray) (aw : UInt256) (ptr count : Nat)
    (hfit : ptr + 32 * (count + 1) < UInt256.size)
    (hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
        (MultiLimbSchoolbookOuterComplete.quotientReadNats mem aw
          (UInt256.ofNat ptr) count) =
      Modexp.wordLimbsToNat
        (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom mem (ptr + 32) count) := by
  rw [natLimbsToNat_size_eq_limbsToNat, Modexp.wordLimbsToNat_eq_limbsToNat]
  rw [quotientReadNats_eq_memoryWordsFrom_map mem aw ptr count hfit hcovered hawFit]

/-- The concrete modulus top limb read by the Knuth setup. -/
def setupTop (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat) : UInt256 :=
  arrayWord (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
    (UInt256.ofNat divisorPtr) (k - 1)

/-- The concrete `B^(2*k)` numerator forces the deployed non-short Knuth branch. -/
theorem knuthBranchExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k divisorPtr : Nat} {tail : List UInt256}
    {rem : UInt256}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hdivisorLayout : MultiLimbArrayReadSemantic.Layout
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k) divisorPtr k)
    (hdivisorTopNonzero : arrayWord (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) (UInt256.ofNat divisorPtr) (k - 1) ≠ ⟨0⟩)
    (hdepth : tail.length ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨5199⟩
      (rem :: UInt256.ofNat (dividendLength k) :: UInt256.ofNat fp :: ⟨3124⟩ ::
        UInt256.ofNat k :: UInt256.ofNat divisorPtr :: tail)
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨5287⟩
      (UInt256.ofNat k :: UInt256.ofNat (dividendLength k) :: rem :: UInt256.ofNat fp ::
        ⟨3124⟩ :: UInt256.ofNat divisorPtr :: tail)
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      rdata acc (steps + 134) (gasUsed + 491) := by
  have hkPos : 0 < k := by omega
  have hdividendLayout := barrettDivisionDividendLayout mem aw fp k hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit
  have hselected := MultiLimbSchoolbookNonzeroPrefix.exactToSelectedSizeBranch
    (m := dividendLength k) (zeroLimbs := 0) (divisorCount := k)
    (dividendCount := dividendLength k) (dividend := UInt256.ofNat fp)
    (ret := ⟨3124⟩) (divisor := UInt256.ofNat divisorPtr)
    (dividendTop := ⟨1⟩)
    (divisorTop := arrayWord (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) (UInt256.ofNat divisorPtr) (k - 1))
    hdepth (by unfold dividendLength; omega) (by simp) hkTwo
    (by unfold dividendLength; omega) hk
    hdividendLayout.header hdividendLayout.headerAw
    (by intro i hi; omega)
    (by intro i hi; omega)
    (hdividendLayout.wordAw (dividendLength k - 1) (by unfold dividendLength; omega))
    (by
      simpa [dividendLength] using
        barrettDivisionMemory_high_word_one mem aw fp k hk hkPos hfp hmemSize hmemLe
          hgap hawFit hfirstFit hsecondFit)
    (by native_decide)
    hdivisorLayout.header hdivisorLayout.headerAw
    (hdivisorLayout.wordAw (k - 1) (by omega)) rfl hdivisorTopNonzero h
  have hpc : MultiLimbSchoolbookNonzeroPrefix.sizeBranchPc (dividendLength k) k = 5287 := by
    simp [MultiLimbSchoolbookNonzeroPrefix.sizeBranchPc, dividendLength]
    omega
  rw [hpc] at hselected
  simpa using hselected

/-- Execute the concrete quotient/`u` allocations, `MCOPY`, divisor-top load, and `_clz` call. -/
theorem setupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k divisorPtr : Nat} {tail : List UInt256}
    {rem : UInt256}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientBound : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) < 2 ^ 64)
    (huBound : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) < 2 ^ 64)
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp)
    (hdivisorHeaderRead : (barrettDivisionMemory mem fp k).readWithPadding divisorPtr 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5287⟩
      (UInt256.ofNat k :: UInt256.ofNat (dividendLength k) :: rem :: UInt256.ofNat fp ::
        ⟨3124⟩ :: UInt256.ofNat divisorPtr :: tail)
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      rdata acc steps gasUsed) :
    let result := MultiLimbSchoolbookKnuthPrefix.clzResultOf
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
      (UInt256.ofNat divisorPtr)
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat result.n :: rem :: ⟨3124⟩ :: UInt256.ofNat k ::
        UInt256.ofNat (dividendLength k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: UInt256.ofNat (quotientCount k) ::
        UInt256.ofNat divisorPtr :: tail)
      (barrettCopiedMemory mem fp k)
      (MultiLimbSchoolbookKnuthPrefix.finalWords (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr))
      rdata acc
      (steps + MultiLimbSchoolbookKnuthPrefix.totalSteps
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr))
      (gasUsed + MultiLimbSchoolbookKnuthPrefix.totalGas
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr)) := by
  have hkPos : 0 < k := by omega
  have hmBound : dividendLength k ≤ 65 := by unfold dividendLength; omega
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hbase96 : 96 ≤ (barrettDivisionMemory mem fp k).size := by
    rw [hbaseSize]
    unfold remainderPtr
    omega
  have hbaseLeQ : (barrettDivisionMemory mem fp k).size ≤ quotientPtr fp k := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hbaseGapQ : quotientPtr fp k - (barrettDivisionMemory mem fp k).size < USize.size := by
    rw [hbaseSize]
    unfold quotientPtr wordArrayAllocationSize wordArrayPayloadSize
    have husize : 2048 < USize.size := by native_decide
    omega
  have hdivisionRange := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  have hbaseAw3 : 3 ≤ (barrettDivisionWords aw fp k).toNat := by
    have := hdivisionRange.1
    unfold remainderPtr at this
    omega
  have hbaseAw64 : ¬ (⟨64⟩ : UInt256) ≥ barrettDivisionWords aw fp k * ⟨32⟩ := by
    have hmul : (barrettDivisionWords aw fp k * (⟨32⟩ : UInt256)).toNat =
        (barrettDivisionWords aw fp k).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := barrettDivisionWords aw fp k) (b := (⟨32⟩ : UInt256))
          hdivisionRange.2
    intro hle
    have hnat : (barrettDivisionWords aw fp k * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hqFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size := lt_trans (by omega : quotientPtr fp k +
        wordArrayAllocationSize (quotientCount k) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range
    (barrettDivisionWords aw fp k) (quotientPtr fp k) (quotientCount k)
    (by rw [quotientCount_eq]; omega) hdivisionRange.2 hqFit
  have hqSize := barrettQuotientMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hq96 : 96 ≤ (barrettQuotientMemory mem fp k).size := by rw [hqSize]; omega
  have hqLeU : (barrettQuotientMemory mem fp k).size ≤ normalizedDividendPtr fp k := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : normalizedDividendPtr fp k - (barrettQuotientMemory mem fp k).size <
      USize.size := by
    rw [hqSize]
    unfold normalizedDividendPtr wordArrayAllocationSize wordArrayPayloadSize
    rw [quotientCount_eq]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hqAw3 : 3 ≤ (barrettQuotientWords aw fp k).toNat := by
    have := hqRange.1
    change 3 ≤ (newWordArrayWords (barrettDivisionWords aw fp k)
      (quotientPtr fp k) (quotientCount k)).toNat
    omega
  have hqAwFit : (barrettQuotientWords aw fp k).toNat * 32 < UInt256.size := by
    unfold barrettQuotientWords MultiLimbSchoolbookKnuthPrefix.quotientWords
      MultiLimbSchoolbookKnuthSetup.quotientWords
    exact hqRange.2
  have hqAw64 : ¬ (⟨64⟩ : UInt256) ≥ barrettQuotientWords aw fp k * ⟨32⟩ := by
    have hmul : (barrettQuotientWords aw fp k * (⟨32⟩ : UInt256)).toNat =
        (barrettQuotientWords aw fp k).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := barrettQuotientWords aw fp k) (b := (⟨32⟩ : UInt256)) hqAwFit
    intro hle
    have hnat : (barrettQuotientWords aw fp k * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size :=
    lt_trans (by omega : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range
    (barrettQuotientWords aw fp k) (normalizedDividendPtr fp k)
    (dividendLength k + 1) (by unfold dividendLength; omega) hqAwFit huFit
  have huSize := barrettUMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hqRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettDivisionMemory mem fp k) (quotientPtr fp k) (quotientCount k) divisorPtr
    hbase96 hbaseGapQ hdivisorPtr96 (by
      unfold quotientPtr remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega)
  have huRead := MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
    (barrettQuotientMemory mem fp k) (normalizedDividendPtr fp k)
    (dividendLength k + 1) divisorPtr hq96 hqGapU hdivisorPtr96 (by
      unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
        wordArrayPayloadSize
      omega)
  have hsource : fp + 32 + 32 * dividendLength k ≤ (barrettUMemory mem fp k).size := by
    rw [huSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
      MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopyRead : (barrettCopiedMemory mem fp k).readWithPadding divisorPtr 32 =
      (barrettUMemory mem fp k).readWithPadding divisorPtr 32 := by
    have hread := write_read_below_end_from (barrettUMemory mem fp k)
      (barrettUMemory mem fp k) (fp + 32) (32 * dividendLength k) divisorPtr
      (by unfold dividendLength; omega) hsource
      (le_trans (by omega : divisorPtr + 32 ≤ fp + 32 + 32 * dividendLength k) hsource)
    unfold barrettCopiedMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
      MultiLimbSchoolbookKnuthSetup.copiedUMemory
    rw [← huSize]
    exact hread
  have hcopiedSize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hcopiedRange := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hqFit huFit
  have hdivisorHeader : MultiLimbOddCompare.headerWord (barrettCopiedMemory mem fp k)
      (barrettCopiedWords aw fp k) (UInt256.ofNat divisorPtr) = UInt256.ofNat k := by
    change arrayHeader _ _ _ = _
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size])),
        hcopiedSize]
      omega
    · rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size]))]
      exact le_trans (by omega) hcopiedRange.1
    · exact hcopiedRange.2
    · rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size]))]
      exact hcopyRead.trans (huRead.trans (hqRead.trans hdivisorHeaderRead))
  simpa only [barrettQuotientMemory, barrettQuotientWords, barrettUMemory, barrettUWords,
    barrettCopiedMemory, barrettCopiedWords, quotientCount] using
    MultiLimbSchoolbookKnuthPrefix.exact
      (quotientFp := quotientPtr fp k) (uFp := normalizedDividendPtr fp k)
      (dividendPtr := fp) (ret := 3124) (m := dividendLength k) (kEff := k)
      (tail := tail) hkPos (by unfold dividendLength; omega) hmBound
      (by unfold quotientPtr remainderPtr; omega) hquotientBound hbase96 hbaseLeQ
      hbaseGapQ hbaseAw3 hbaseAw64
      (barrettDivisionMemory_read64 mem fp k hk hfp hmemSize hmemLe hgap hfirstFit)
      hcalldata (by unfold normalizedDividendPtr quotientPtr remainderPtr; omega) huBound
      hq96 hqLeU hqGapU hqAw3 hqAw64
      (barrettQuotientMemory_read64 mem fp k hk hfp hmemSize hmemLe hgap hfirstFit)
      (by
        unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
        omega)
      (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huBound
        omega)
      hdivisorHeader (by omega) h

/-- Both setup `MLOAD`s are in the existing active extent, and `_clz` receives the concrete
copied modulus top limb. -/
theorem setupObserver
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size)
    (hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size)
    (huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp) :
    MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr) = barrettCopiedWords aw fp k ∧
      MultiLimbSchoolbookKnuthPrefix.finalWords (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr) = barrettCopiedWords aw fp k ∧
      MultiLimbSchoolbookKnuthPrefix.clzResultOf
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr) = MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr) := by
  have hkPos : 0 < k := by omega
  have hcopiedRange := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit
  have hdivisorFit : divisorPtr < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  have htopFit : divisorPtr + 32 * ((k - 1) + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  have htopNat :
      (MultiLimbSchoolbookKnuthPrefix.topAddress (UInt256.ofNat divisorPtr) k).toNat =
        divisorPtr + 32 * k := by
    unfold MultiLimbSchoolbookKnuthPrefix.topAddress
    rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit _ _ (by
      rw [UInt256.toNat_ofNat_of_lt hdivisorFit]
      exact htopFit), UInt256.toNat_ofNat_of_lt hdivisorFit]
    omega
  have hheaderWords :
      MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr) = barrettCopiedWords aw fp k := by
    unfold MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords barrettCopiedWords
    apply MultiLimbOddCompare.afterHeader_eq_of_access
    rw [UInt256.toNat_ofNat_of_lt hdivisorFit]
    exact le_trans (by
      unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
        MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
      omega : divisorPtr + 32 ≤
        normalizedDividendPtr fp k + 32 + 32 * dividendLength k) hcopiedRange.1
  have hfinalWords :
      MultiLimbSchoolbookKnuthPrefix.finalWords (barrettDivisionWords aw fp k)
        (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
        (UInt256.ofNat divisorPtr) = barrettCopiedWords aw fp k := by
    unfold MultiLimbSchoolbookKnuthPrefix.finalWords MultiLimbClz.afterTopLoad
    rw [hheaderWords]
    apply MultiLimbOddCompare.afterHeader_eq_of_access
    rw [htopNat]
    exact le_trans (by
      unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
        MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
      omega : divisorPtr + 32 * k + 32 ≤
        normalizedDividendPtr fp k + 32 + 32 * dividendLength k) hcopiedRange.1
  refine ⟨hheaderWords, hfinalWords, ?_⟩
  unfold MultiLimbSchoolbookKnuthPrefix.clzResultOf setupTop
    MultiLimbClz.loadedTopWord arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
  rw [hheaderWords]
  rfl

/-- The original modulus remains a covered array after the complete Knuth setup and `v`
allocation. -/
theorem vDivisorLayout
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
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
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp)
    (hdivisorHeaderRead : (barrettDivisionMemory mem fp k).readWithPadding divisorPtr 32 =
      UInt256.toByteArray (UInt256.ofNat k)) :
    MultiLimbArrayReadSemantic.Layout (barrettVMemory mem fp k)
      (barrettVWords aw fp k) divisorPtr k := by
  have hkPos : 0 < k := by omega
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hvRange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  apply MultiLimbArrayReadSemantic.layout_of_geometry
  · unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  · rw [hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega : divisorPtr + 32 + 32 * k ≤ normalizedDivisorPtr fp k + 32 + 32 * k)
      hvRange.1
  · exact hvRange.2
  · exact (barrettVMemory_read_below_fp mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
      hgap hfirstFit hdivisorPtr96 (by omega)).trans hdivisorHeaderRead

/-- All guarded modulus limbs survive the quotient/`u` allocations and numerator `MCOPY`. -/
theorem copiedDivisorWords_eq_division
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
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
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k := by
  have hkPos : 0 < k := by omega
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hcopiedSize := barrettCopiedMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap
    hfirstFit
  have hbaseRange := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  have hcopiedRange := barrettCopiedWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit
  apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
  intro i hi
  simp only [Nat.zero_add]
  have hfit : divisorPtr + 32 * (k + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
  · omega
  · rw [hcopiedSize]
    unfold normalizedDividendPtr quotientPtr remainderPtr wordArrayAllocationSize
      wordArrayPayloadSize
    omega
  · rw [hbaseSize]
    unfold remainderPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact le_trans (by
      unfold normalizedDividendPtr quotientPtr remainderPtr dividendLength quotientCount
        MultiLimbSchoolbookKnuthPrefix.numQ wordArrayAllocationSize wordArrayPayloadSize
      omega) hcopiedRange.1
  · exact le_trans (by
      unfold remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega) hbaseRange.1
  · exact hcopiedRange.2
  · exact hbaseRange.2
  · exact barrettCopiedMemory_read_below_fp mem fp k (divisorPtr + 32 * (i + 1))
      hk hkPos hfp hmemSize hmemLe hgap hfirstFit (by omega) (by omega)

/-- Allocating normalized divisor `v` also preserves the complete guarded modulus observation. -/
theorem vDivisorWords_eq_division
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
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
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k := by
  have hkPos : 0 < k := by omega
  have hbaseSize := barrettDivisionMemory_size mem fp k hk hfp hmemSize hmemLe hgap hfirstFit
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hbaseRange := barrettDivisionWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
  have hvRange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
  intro i hi
  simp only [Nat.zero_add]
  have hfit : divisorPtr + 32 * (k + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
  · omega
  · rw [hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hbaseSize]
    unfold remainderPtr wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega) hvRange.1
  · exact le_trans (by
      unfold remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega) hbaseRange.1
  · exact hvRange.2
  · exact hbaseRange.2
  · exact barrettVMemory_read_below_fp mem fp k (divisorPtr + 32 * (i + 1))
      hk hkPos hfp hmemSize hmemLe hgap hfirstFit (by omega) (by omega)

/-- The word passed to `_clz` is exactly the top modulus limb later consumed by normalization. -/
theorem setupTop_eq_vTop
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
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
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp) :
    arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat divisorPtr) (k - 1) = setupTop mem aw fp k divisorPtr := by
  have hcopied := copiedDivisorWords_eq_division mem aw fp k divisorPtr hkTwo hk hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hdivisorPtr96
    hdivisorEnd
  have hv := vDivisorWords_eq_division mem aw fp k divisorPtr hkTwo hk hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hdivisorPtr96 hdivisorEnd
  have hcopiedTop := MultiLimbArrayReadSemantic.arrayWord_eq_of_arrayReadWords_eq
    (barrettCopiedMemory mem fp k) (barrettDivisionMemory mem fp k)
    (barrettCopiedWords aw fp k) (barrettDivisionWords aw fp k)
    (UInt256.ofNat divisorPtr) (UInt256.ofNat divisorPtr) 0 k (k - 1) (by omega) hcopied
  have hvTop := MultiLimbArrayReadSemantic.arrayWord_eq_of_arrayReadWords_eq
    (barrettVMemory mem fp k) (barrettDivisionMemory mem fp k)
    (barrettVWords aw fp k) (barrettDivisionWords aw fp k)
    (UInt256.ofNat divisorPtr) (UInt256.ofNat divisorPtr) 0 k (k - 1) (by omega) hv
  unfold setupTop
  simpa only [Nat.zero_add] using hvTop.trans hcopiedTop.symm

/-- Every concrete source limb is in memory at the positive-normalization entry. -/
theorem vDivisorSource
    (mem : ByteArray) (fp k divisorPtr : Nat)
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp) :
    ∀ j, j < k →
      (arrayAddress (UInt256.ofNat divisorPtr) j).toNat + 32 ≤
        (barrettVMemory mem fp k).size := by
  intro j hj
  have hkPos : 0 < k := by omega
  have hfit : divisorPtr + 32 * (k + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  rw [concreteArrayAddress_toNat divisorPtr k j hj hfit,
    barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit]
  unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
    wordArrayAllocationSize wordArrayPayloadSize
  omega

/-- A nonzero concrete top limb supplies the radix lower bound required by schoolbook division. -/
theorem modulusLower_of_top_nonzero
    (mem : ByteArray) (aw array top : UInt256) (k modulusNat : Nat)
    (hkPos : 0 < k)
    (htop : arrayWord mem aw array (k - 1) = top)
    (htopNe : top ≠ ⟨0⟩)
    (hmodulus : Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw array 0 k) =
        modulusNat) :
    UInt256.size ^ (k - 1) ≤ modulusNat := by
  have hsplit := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_succ_append
    mem aw array 0 (k - 1)
  have hkEq : k - 1 + 1 = k := by omega
  rw [hkEq] at hsplit
  simp only [Nat.zero_add] at hsplit
  have htopNat : 0 < top.toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact htopNe (uint256_toNat_eq_zero hzero)
  rw [hsplit, Modexp.wordLimbsToNat_append, htop] at hmodulus
  simp only [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length,
    Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero] at hmodulus
  rw [← hmodulus]
  have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
  have hpow : 0 < UInt256.size ^ (k - 1) := Nat.pow_pos hsizePos
  nlinarith

/-- The zero-shift `MCOPY` presents the same top modulus limb that selected the zero-CLZ path. -/
theorem zeroTop_eq_setupTop
    (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat)
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
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp) :
    arrayWord (barrettZeroMemory mem fp k divisorPtr)
        (barrettZeroWords aw fp k divisorPtr)
        (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1) =
      setupTop mem aw fp k divisorPtr := by
  have hkPos : 0 < k := by omega
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size := by
    rw [hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
      UInt256.size := by
    rw [max_eq_left (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega)]
    simp only [wordArrayAllocationSize, wordArrayPayloadSize] at hvFit
    omega
  have hzSize := barrettZeroMemory_size mem fp k divisorPtr hk hkPos hfp hmemSize hmemLe
    hgap hfirstFit hsource
  have hvRange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit
  have hzRange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit hcopyFit
  have hrightFit : divisorPtr + 32 * (k + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
    omega
  have hword := MultiLimbArrayReadSemantic.arrayWord_eq_of_distinct_readWithPadding_eq
    (barrettZeroMemory mem fp k divisorPtr) (barrettVMemory mem fp k)
    (barrettZeroWords aw fp k divisorPtr) (barrettVWords aw fp k)
    (normalizedDivisorPtr fp k) divisorPtr (k - 1)
    (by unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit; omega)
    (by omega)
    (by rw [hzSize]; omega)
    (by
      rw [hvSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega)
    (le_trans (by omega) hzRange.1)
    (le_trans (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega) hvRange.1)
    hzRange.2 hvRange.2
    (by
      rw [show normalizedDivisorPtr fp k + 32 * ((k - 1) + 1) =
        normalizedDivisorPtr fp k + 32 + 32 * (k - 1) by omega,
        show divisorPtr + 32 * ((k - 1) + 1) =
          divisorPtr + 32 + 32 * (k - 1) by omega]
      exact barrettZeroMemory_read_v_word mem fp k divisorPtr (k - 1) hk hkPos (by omega)
        hfp hmemSize hmemLe hgap hfirstFit hsource)
  exact hword.trans (setupTop_eq_vTop mem aw fp k divisorPtr hkTwo hk hfp hmemSize hmemLe
    hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hdivisorPtr96 hdivisorEnd)

/-- Execute the complete positive-CLZ normalization from the concrete setup state. -/
theorem positiveNormalizationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k divisorPtr : Nat} {tail : List UInt256}
    {rem : UInt256}
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
    (hvBound : normalizedDivisorPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp)
    (hdivisorHeaderRead : (barrettDivisionMemory mem fp k).readWithPadding divisorPtr 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hshiftPos : 0 < (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n :: rem ::
        ⟨3124⟩ :: UInt256.ofNat k :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat (quotientPtr fp k) :: UInt256.ofNat (normalizedDividendPtr fp k) ::
        UInt256.ofNat (quotientCount k) :: UInt256.ofNat divisorPtr :: tail)
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      rdata acc steps gasUsed) :
    let vTop := arrayWord
      (barrettPositiveMemory mem aw fp k (UInt256.ofNat divisorPtr)
        (setupTop mem aw fp k divisorPtr))
      (barrettVWords aw fp k) (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5450⟩
      (UInt256.ofNat (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n ::
        ⟨3124⟩ :: rem :: UInt256.ofNat (quotientCount k) :: UInt256.ofNat k ::
        UInt256.ofNat (normalizedDivisorPtr fp k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: vTop :: ⟨1⟩ :: tail)
      (barrettPositiveMemory mem aw fp k (UInt256.ofNat divisorPtr)
        (setupTop mem aw fp k divisorPtr))
      (barrettVWords aw fp k) rdata acc
      (steps + MultiLimbSchoolbookNormalizationFunction.positiveSteps
        (barrettVMemory mem fp k) (barrettVWords aw fp k) (UInt256.ofNat divisorPtr)
        (UInt256.ofNat (normalizedDivisorPtr fp k))
        (UInt256.ofNat (normalizedDividendPtr fp k)) k (dividendLength k)
        (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n)
      (gasUsed + MultiLimbSchoolbookNormalizationFunction.positiveGas
        (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
        (UInt256.ofNat divisorPtr) (UInt256.ofNat (normalizedDivisorPtr fp k))
        (UInt256.ofNat (normalizedDividendPtr fp k)) (normalizedDivisorPtr fp k) k
        (dividendLength k) (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n) := by
  have hkPos : 0 < k := by omega
  have hlayout := vDivisorLayout mem aw fp k divisorPtr hkTwo hk hfp hmemSize hmemLe hgap
    hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hdivisorPtr96 hdivisorEnd
    hdivisorHeaderRead
  have hheaders := MultiLimbBarrettContinuationExecutable.barrettPositiveMemory_headers
    mem aw (UInt256.ofNat divisorPtr) (setupTop mem aw fp k divisorPtr) fp k hk hkPos hfp
    hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
  apply MultiLimbBarrettContinuationExecutable.barrettPositiveNormalizationExact_of_vHeader
    hkTwo hk hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit
    huFit hvFit hvBound
    (barrettCopiedMemory_read64 mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit)
    hcalldata hlayout.header hlayout.headerAw (fun j hj => hlayout.wordAw j hj)
  · rw [UInt256.toNat_ofNat_of_lt (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
      omega : divisorPtr < UInt256.size)]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  · exact hheaders.2.2
  · exact htail
  · exact h

/-- Execute the complete zero-CLZ allocation and divisor `MCOPY` from the concrete setup state. -/
theorem zeroNormalizationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k divisorPtr : Nat} {tail : List UInt256}
    {rem : UInt256}
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
    (hvBound : normalizedDivisorPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (⟨0⟩ :: rem :: ⟨3124⟩ :: UInt256.ofNat k :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat (quotientPtr fp k) :: UInt256.ofNat (normalizedDividendPtr fp k) ::
        UInt256.ofNat (quotientCount k) :: UInt256.ofNat divisorPtr :: tail)
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      rdata acc steps gasUsed) :
    let vTop := arrayWord (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5450⟩
      (⟨0⟩ :: ⟨3124⟩ :: rem :: UInt256.ofNat (quotientCount k) :: UInt256.ofNat k ::
        UInt256.ofNat (normalizedDivisorPtr fp k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: vTop :: ⟨0⟩ :: tail)
      (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr)
      rdata acc (steps + 152)
      (gasUsed + MultiLimbSchoolbookNormalizationFunction.zeroGas
        (barrettCopiedWords aw fp k) divisorPtr (normalizedDivisorPtr fp k) k) := by
  have hkPos : 0 < k := by omega
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
  have hcopiedAw64 : ¬ (⟨64⟩ : UInt256) ≥ barrettCopiedWords aw fp k * ⟨32⟩ := by
    have hmul : (barrettCopiedWords aw fp k * (⟨32⟩ : UInt256)).toNat =
        (barrettCopiedWords aw fp k).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := barrettCopiedWords aw fp k) (b := (⟨32⟩ : UInt256))
          hcopiedRange.2
    intro hle
    have hnat : (barrettCopiedWords aw fp k * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
  have hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size := by
    rw [hvSize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
      UInt256.size := by
    rw [max_eq_left (by
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega)]
    simp only [wordArrayAllocationSize, wordArrayPayloadSize] at hvFit
    omega
  have hgeometry := MultiLimbBarrettContinuationExecutable.zeroContinuationGeometry aw fp k
    divisorPtr hkTwo hk hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hcopyFit
  have hvHeader := MultiLimbBarrettContinuationExecutable.barrettZeroMemory_vHeader mem aw
    fp k divisorPtr hk hkPos hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit
    hquotientFit huFit hvFit hcopyFit hsource
  apply MultiLimbSchoolbookNormalizationFunction.zeroExact hkPos hk
    (lt_of_le_of_lt hk (by norm_num [UInt256.size]))
    (by
      have hsize : 1024 < UInt256.size := by norm_num [UInt256.size]
      omega)
    (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
      omega)
    (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)
    (by unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr; omega)
    hvBound hcopied96 hcopiedLe hcopiedGap hcopiedAw3 hcopiedAw64
    (barrettCopiedMemory_read64 mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit)
    hcalldata hvHeader hgeometry.hvHeaderAw (hgeometry.hvWordAw (k - 1) (by omega)) rfl
    (by omega) h

/-- Return a completed positive-CLZ schoolbook division through `_computeBarrettConstant`'s
`3124` continuation.  The quotient-loop witnesses and exact selected gas remain exposed. -/
theorem positiveDivisionConstantReturn_exists
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas : Nat} {callerTail : List UInt256}
    {mem : ByteArray} {aw divisor top : UInt256}
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
    (hsourceMem : ∀ j, j < k →
      (arrayAddress divisor j).toNat + 32 ≤ (barrettVMemory mem fp k).size)
    (htop : arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      divisor (k - 1) = top)
    (hmodulus : Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettVMemory mem fp k) (barrettVWords aw fp k)
        divisor 0 k) = modulusNat)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (htopNe : top.toNat ≠ 0)
    (hdepth : callerTail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (UInt256.ofNat (MultiLimbClz.clzResult top).n :: ⟨3124⟩ ::
        UInt256.ofNat (remainderPtr fp k) :: UInt256.ofNat (quotientCount k) ::
        UInt256.ofNat k :: UInt256.ofNat (normalizedDivisorPtr fp k) ::
        UInt256.ofNat (quotientPtr fp k) :: UInt256.ofNat (normalizedDividendPtr fp k) ::
        arrayWord (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
          (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1) :: ⟨1⟩ ::
        ⟨1718⟩ :: callerTail)
      (barrettPositiveMemory mem aw fp k divisor top) (barrettVWords aw fp k)
      rdata acc initialSteps initialGas) :
    ∃ (inputs : List Nat) (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        finalAw = barrettVWords aw fp k ∧
        (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
          ).memory.size = normalizedDivisorPtr fp k + wordArrayAllocationSize k ∧
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
            (MultiLimbSchoolbookOuterComplete.quotientReadNats
              (MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
                (UInt256.ofNat (normalizedDividendPtr fp k))
                (UInt256.ofNat (remainderPtr fp k))
                (MultiLimbClz.clzResult top).n 0 k finalMem).memory finalAw
              (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat ∧
        let result := MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
        RDx runtimeBytecode ee g s0 ⟨1718⟩
          (UInt256.ofNat (quotientPtr fp k) :: callerTail)
          result.memory finalAw rdata acc
          ((((initialSteps + steps + 5) + 23) + result.steps + 6) + 4)
          ((((initialGas + gas + 13) + 73) + result.gas + 26) + 14) := by
  obtain ⟨inputs, finalMem, finalAw, steps, gas, hlength, hfinalAw, hfinalSize,
      hfinalRead, hquotientHeader, hfinalFrame, hquotient, rd3124⟩ :=
    MultiLimbBarrettContinuationExecutable.barrettPositiveDivisionReturn_exists
      fp k modulusNat 3124 hkTwo hk hshiftPos hfp hmemSize hmemLe hgap hawFit hfirstFit
      hsecondFit hquotientFit huFit hvFit hsourceMem htop hmodulus hmodulusLower htopNe
      (by native_decide) (by simp only [List.length_cons]; omega) h
  let result := MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
    (UInt256.ofNat (normalizedDividendPtr fp k))
    (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
  have hresultSize : result.memory.size =
      normalizedDivisorPtr fp k + wordArrayAllocationSize k := by
    have hsize := MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_size_eq
      finalAw (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (remainderPtr fp k)) (MultiLimbClz.clzResult top).n 0 k finalMem
      (by
        intro j hj
        simp only [Nat.zero_add]
        rw [MultiLimbBarrettContinuationExecutable.remainderArrayAddress_toNat fp k j hj
          hsecondFit, hfinalSize]
        unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega)
    calc
      result.memory.size = finalMem.size := by simpa only [result] using hsize
      _ = normalizedDivisorPtr fp k + wordArrayAllocationSize k := by
        simpa only [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using
          hfinalSize
  have hquotientWords : ∀ i, i < quotientCount k ->
      arrayWord result.memory finalAw (UInt256.ofNat (quotientPtr fp k)) i =
        arrayWord finalMem finalAw (UInt256.ofNat (quotientPtr fp k)) i := by
    intro i hi
    dsimp only [result]
    apply MultiLimbSchoolbookDenormalizationSemantic.denormalizeRange_preserves_arrayWord_above
    · intro j hj
      simp only [Nat.zero_add]
      rw [MultiLimbBarrettContinuationExecutable.remainderArrayAddress_toNat fp k j hj
        hsecondFit, hfinalSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    · intro j hj
      simp only [Nat.zero_add]
      rw [MultiLimbBarrettContinuationExecutable.remainderArrayAddress_toNat fp k j hj
        hsecondFit,
        MultiLimbBarrettContinuationExecutable.quotientArrayAddress_toNat fp k i hi
          hquotientFit]
      unfold quotientPtr remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
  have hquotientResult :
      MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
          (MultiLimbSchoolbookOuterComplete.quotientReadNats result.memory finalAw
            (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
        UInt256.size ^ (2 * k) / modulusNat := by
    rw [quotientReadNats_eq_of_words _ _ _ _ _ hquotientWords]
    exact hquotient
  refine ⟨inputs, finalMem, finalAw, steps, gas, hlength, hfinalAw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [result] using hresultSize
  · simpa only [result] using hfinalRead
  · simpa only [result] using hquotientHeader
  · simpa only [result] using hfinalFrame
  · simpa only [result] using hquotientResult
  dsimp only
  exact MultiLimbBarrettConstant.constantReturnExact (ret := 1718)
    (by native_decide) (by omega) rd3124

/-- Return a completed zero-CLZ schoolbook division through `_computeBarrettConstant`'s `3124`
continuation while retaining the selected quotient-loop witnesses and exact gas. -/
theorem zeroDivisionConstantReturn_exists
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {initialSteps initialGas : Nat} {callerTail : List UInt256}
    {mem : ByteArray} {aw top : UInt256}
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
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat)
    (htop : arrayWord (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1) = top)
    (htopNe : top.toNat ≠ 0)
    (hshiftZero : (MultiLimbClz.clzResult top).n = 0)
    (hdepth : callerTail.length ≤ 995)
    (h : RDx runtimeBytecode ee g s0 ⟨5450⟩
      (⟨0⟩ :: ⟨3124⟩ :: UInt256.ofNat (remainderPtr fp k) ::
        UInt256.ofNat (quotientCount k) :: UInt256.ofNat k ::
        UInt256.ofNat (normalizedDivisorPtr fp k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: top :: ⟨0⟩ :: ⟨1718⟩ :: callerTail)
      (barrettZeroMemory mem fp k divisorPtr) (barrettZeroWords aw fp k divisorPtr)
      rdata acc initialSteps initialGas) :
    ∃ (inputs : List Nat) (finalMem : ByteArray) (finalAw : UInt256) (steps gas : Nat),
      inputs.length = quotientCount k ∧
        finalAw = barrettZeroWords aw fp k divisorPtr ∧
        (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory.size =
            normalizedDivisorPtr fp k + wordArrayAllocationSize k ∧
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
            (MultiLimbSchoolbookOuterComplete.quotientReadNats
              (MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
                (UInt256.ofNat (normalizedDividendPtr fp k))
                (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem).memory finalAw
              (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
          UInt256.size ^ (2 * k) / modulusNat ∧
        let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
          (UInt256.ofNat (normalizedDividendPtr fp k))
          (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem
        RDx runtimeBytecode ee g s0 ⟨1718⟩
          (UInt256.ofNat (quotientPtr fp k) :: callerTail)
          copied.memory finalAw rdata acc
          (((initialSteps + steps + 5) + 58 * k + 30) + 4)
          (((initialGas + gas + 13) + 208 * k + 100) + 14) := by
  obtain ⟨inputs, finalMem, finalAw, steps, gas, hlength, hfinalAw, hfinalSize,
      hfinalRead, hquotientHeader, hfinalFrame, hquotient, rd3124⟩ :=
    MultiLimbBarrettContinuationExecutable.barrettZeroDivisionReturn_exists
      fp k divisorPtr modulusNat 3124 hkTwo hk hfp hmemSize hmemLe hgap hawFit hfirstFit
      hsecondFit hquotientFit huFit hvFit hcopyFit hsource hdivisorFit hmodulus
      hmodulusLower htop htopNe hshiftZero (by native_decide)
      (by simp only [List.length_cons]; omega) h
  let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
    (UInt256.ofNat (normalizedDividendPtr fp k))
    (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem
  have hcopiedSize : copied.memory.size =
      normalizedDivisorPtr fp k + wordArrayAllocationSize k := by
    have hsize := MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_size_eq finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem (by
        intro j hj
        simp only [Nat.zero_add]
        rw [MultiLimbBarrettContinuationExecutable.remainderArrayAddress_toNat fp k j hj
          hsecondFit, hfinalSize]
        unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega)
    calc
      copied.memory.size = finalMem.size := by simpa only [copied] using hsize
      _ = normalizedDivisorPtr fp k + wordArrayAllocationSize k := by
        simpa only [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using
          hfinalSize
  have hquotientWords : ∀ i, i < quotientCount k ->
      arrayWord copied.memory finalAw (UInt256.ofNat (quotientPtr fp k)) i =
        arrayWord finalMem finalAw (UInt256.ofNat (quotientPtr fp k)) i := by
    intro i hi
    dsimp only [copied]
    apply MultiLimbSchoolbookZeroShiftRemainderSemantic.copyRange_preserves_arrayWord_above
    · intro j hj
      simp only [Nat.zero_add]
      rw [MultiLimbBarrettContinuationExecutable.remainderArrayAddress_toNat fp k j hj
        hsecondFit, hfinalSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    · intro j hj
      simp only [Nat.zero_add]
      rw [MultiLimbBarrettContinuationExecutable.remainderArrayAddress_toNat fp k j hj
        hsecondFit,
        MultiLimbBarrettContinuationExecutable.quotientArrayAddress_toNat fp k i hi
          hquotientFit]
      unfold quotientPtr remainderPtr wordArrayAllocationSize wordArrayPayloadSize
      omega
  have hquotientCopied :
      MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
          (MultiLimbSchoolbookOuterComplete.quotientReadNats copied.memory finalAw
            (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
        UInt256.size ^ (2 * k) / modulusNat := by
    rw [quotientReadNats_eq_of_words _ _ _ _ _ hquotientWords]
    exact hquotient
  refine ⟨inputs, finalMem, finalAw, steps, gas, hlength, hfinalAw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [copied] using hcopiedSize
  · simpa only [copied] using hfinalRead
  · simpa only [copied] using hquotientHeader
  · simpa only [copied] using hfinalFrame
  · simpa only [copied] using hquotientCopied
  dsimp only
  exact MultiLimbBarrettConstant.constantReturnExact (ret := 1718)
    (by native_decide) (by omega) rd3124

/-- The normalization path selected by the concrete modulus top limb. -/
inductive ClzPath where
  | zero
  | positive
  deriving DecidableEq, Repr

/-- Exposed exact selection for the complete normalization, quotient, remainder return, and
`_computeBarrettConstant` return from PC 5368 to PC 1718. -/
structure Selection
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (sourceMemory : ByteArray) (fp k modulusNat initialSteps initialGas : Nat)
    (callerTail : List UInt256) where
  path : ClzPath
  inputs : List Nat
  finalMemory : ByteArray
  finalWords : UInt256
  loopSteps : Nat
  loopGas : Nat
  stepDelta : Nat
  gasDelta : Nat
  inputsLength : inputs.length = quotientCount k
  finalMemorySize : finalMemory.size =
    normalizedDivisorPtr fp k + wordArrayAllocationSize k
  finalFreePointer : finalMemory.readWithPadding 64 32 = UInt256.toByteArray
    (UInt256.ofNat (normalizedDivisorPtr fp k + wordArrayAllocationSize k))
  quotientHeader : finalMemory.readWithPadding (quotientPtr fp k) 32 =
    UInt256.toByteArray (UInt256.ofNat (quotientCount k))
  finalReadBelow : ∀ read, 96 ≤ read → read + 32 ≤ fp →
    finalMemory.readWithPadding read 32 = sourceMemory.readWithPadding read 32
  workspaceCovered : normalizedDivisorPtr fp k + wordArrayAllocationSize k ≤
    32 * finalWords.toNat
  finalWordsFit : finalWords.toNat * 32 < UInt256.size
  quotient_eq :
    MultiLimbSchoolbookOuterComplete.natLimbsToNat UInt256.size
        (MultiLimbSchoolbookOuterComplete.quotientReadNats finalMemory finalWords
          (UInt256.ofNat (quotientPtr fp k)) (quotientCount k)) =
      UInt256.size ^ (2 * k) / modulusNat
  exactExecution : RDx runtimeBytecode ee g s0 ⟨1718⟩
    (UInt256.ofNat (quotientPtr fp k) :: callerTail)
    finalMemory finalWords rdata acc
    (initialSteps + stepDelta) (initialGas + gasDelta)

namespace Selection

/-- The selected concrete quotient payload is the computed Barrett constant in the exact memory
representation required by the exponent loop. -/
theorem quotientMemoryValue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata sourceMemory : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fp k modulusNat initialSteps initialGas : Nat} {callerTail : List UInt256}
    (selected : Selection (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
      sourceMemory fp k modulusNat initialSteps initialGas callerTail) :
    Modexp.wordLimbsToNat
        (MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom selected.finalMemory
          (quotientPtr fp k + 32) (quotientCount k)) =
      UInt256.size ^ (2 * k) / modulusNat := by
  have hcovered : MultiLimbMontgomeryCIOSSemantic.MemoryCovered
      selected.finalMemory selected.finalWords := by
    unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered
    rw [selected.finalMemorySize]
    exact selected.workspaceCovered
  have hfit : quotientPtr fp k + 32 * (quotientCount k + 1) < UInt256.size := by
    have hactive := selected.workspaceCovered
    have hawFit := selected.finalWordsFit
    unfold normalizedDivisorPtr normalizedDividendPtr wordArrayAllocationSize
      wordArrayPayloadSize at hactive
    omega
  rw [← quotientReadNats_value_eq_memoryWordsFrom selected.finalMemory selected.finalWords
    (quotientPtr fp k) (quotientCount k) hfit hcovered selected.finalWordsFit]
  exact selected.quotient_eq

/-- Exact fixed/setup step prefix from `_computeBarrettConstant` entry at PC 1707 to the common
post-CLZ branch point at PC 5368. -/
def callPrefixSteps (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat) : Nat :=
  28 + 198 + 134 +
    MultiLimbSchoolbookKnuthPrefix.totalSteps
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
      (UInt256.ofNat divisorPtr)

/-- Exact memory- and path-sensitive gas prefix from PC 1707 through the real `_clz` call. -/
def callPrefixGas (mem : ByteArray) (aw : UInt256) (fp k divisorPtr : Nat) : Nat :=
  99 +
    (150 + newWordArrayGas aw fp (dividendLength k) +
      newWordArrayGas (dividendWords aw fp k) (remainderPtr fp k) k) +
    491 +
    MultiLimbSchoolbookKnuthPrefix.totalGas
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      (quotientPtr fp k) (normalizedDividendPtr fp k) fp (dividendLength k) k
      (UInt256.ofNat divisorPtr)

/-- The complete PC 1707 step delta selected by the concrete CLZ and quotient paths. -/
def callStepDelta
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fp k modulusNat initialSteps initialGas : Nat} {callerTail : List UInt256}
    (mem : ByteArray) (aw : UInt256) (divisorPtr : Nat)
    (selected : Selection (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
      mem fp k modulusNat initialSteps initialGas callerTail) : Nat :=
  callPrefixSteps mem aw fp k divisorPtr + selected.stepDelta

/-- The complete PC 1707 gas delta selected by the concrete CLZ and quotient paths. -/
def callGasDelta
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {fp k modulusNat initialSteps initialGas : Nat} {callerTail : List UInt256}
    (mem : ByteArray) (aw : UInt256) (divisorPtr : Nat)
    (selected : Selection (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
      mem fp k modulusNat initialSteps initialGas callerTail) : Nat :=
  callPrefixGas mem aw fp k divisorPtr + selected.gasDelta

/-- Every valid concrete PC 5368 state has one exposed, path-sensitive Barrett-constant
selection.  Branching is solely on the actual `_clz` result. -/
theorem exists_of_setup
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k divisorPtr modulusNat : Nat} {callerTail : List UInt256}
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
    (hvBound : normalizedDivisorPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp)
    (hdivisorHeaderRead : (barrettDivisionMemory mem fp k).readWithPadding divisorPtr 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hmodulus : Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (hdivisorTopNonzero : arrayWord (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) (UInt256.ofNat divisorPtr) (k - 1) ≠ ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : callerTail.length ≤ 994)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n ::
        UInt256.ofNat (remainderPtr fp k) :: ⟨3124⟩ :: UInt256.ofNat k ::
        UInt256.ofNat (dividendLength k) :: UInt256.ofNat (quotientPtr fp k) ::
        UInt256.ofNat (normalizedDividendPtr fp k) :: UInt256.ofNat (quotientCount k) ::
        UInt256.ofNat divisorPtr :: ⟨1718⟩ :: callerTail)
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      rdata acc steps gasUsed) :
    Nonempty (Selection (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) mem fp k modulusNat steps gasUsed callerTail) := by
  have hkPos : 0 < k := by omega
  have hvWords := vDivisorWords_eq_division mem aw fp k divisorPtr hkTwo hk hfp hmemSize
    hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hdivisorPtr96
    hdivisorEnd
  have hmodulusV : Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettVMemory mem fp k) (barrettVWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat := by
    rw [hvWords]
    exact hmodulus
  have htopV := setupTop_eq_vTop mem aw fp k divisorPtr hkTwo hk hfp hmemSize hmemLe hgap
    hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hdivisorPtr96 hdivisorEnd
  have hdivisionTop := MultiLimbArrayReadSemantic.arrayWord_eq_of_arrayReadWords_eq
    (barrettVMemory mem fp k) (barrettDivisionMemory mem fp k)
    (barrettVWords aw fp k) (barrettDivisionWords aw fp k)
    (UInt256.ofNat divisorPtr) (UInt256.ofNat divisorPtr) 0 k (k - 1) (by omega) hvWords
  have hdivisionTop' : arrayWord (barrettVMemory mem fp k) (barrettVWords aw fp k)
      (UInt256.ofNat divisorPtr) (k - 1) =
        arrayWord (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
          (UInt256.ofNat divisorPtr) (k - 1) := by
    simpa only [Nat.zero_add] using hdivisionTop
  have htopEntry : arrayWord (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) (UInt256.ofNat divisorPtr) (k - 1) =
        setupTop mem aw fp k divisorPtr := by
    exact hdivisionTop'.symm.trans htopV
  have htopNe : setupTop mem aw fp k divisorPtr ≠ ⟨0⟩ := by
    rw [← htopEntry]
    exact hdivisorTopNonzero
  have htopNatNe : (setupTop mem aw fp k divisorPtr).toNat ≠ 0 := by
    intro hzero
    exact htopNe (uint256_toNat_eq_zero hzero)
  have hmodulusLower : UInt256.size ^ (k - 1) ≤ modulusNat :=
    modulusLower_of_top_nonzero (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) (UInt256.ofNat divisorPtr)
      (arrayWord (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (UInt256.ofNat divisorPtr) (k - 1)) k modulusNat hkPos rfl
      hdivisorTopNonzero hmodulus
  have hsourceMem := vDivisorSource mem fp k divisorPtr hkTwo hk hfp hmemSize hmemLe hgap
    hfirstFit hdivisorEnd
  by_cases hshiftZero :
      (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n = 0
  · have hzeroState := h
    rw [hshiftZero] at hzeroState
    have rd5450 := zeroNormalizationExact hkTwo hk hfp hmemSize hmemLe hgap hawFit
      hfirstFit hsecondFit hquotientFit huFit hvFit hvBound hdivisorEnd hcalldata
      (by simpa using Nat.succ_le_succ hdepth) hzeroState
    let zeroTop := arrayWord (barrettZeroMemory mem fp k divisorPtr)
      (barrettZeroWords aw fp k divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k)) (k - 1)
    have hzeroTop : zeroTop = setupTop mem aw fp k divisorPtr := by
      exact zeroTop_eq_setupTop mem aw fp k divisorPtr hkTwo hk hfp hmemSize hmemLe hgap
        hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hdivisorPtr96 hdivisorEnd
    have hzeroTopNe : zeroTop.toNat ≠ 0 := by rw [hzeroTop]; exact htopNatNe
    have hzeroClz : (MultiLimbClz.clzResult zeroTop).n = 0 := by
      rw [hzeroTop]
      exact hshiftZero
    have hcopyFit : max (normalizedDivisorPtr fp k + 32) (divisorPtr + 32) + 32 * k + 31 <
        UInt256.size := by
      rw [max_eq_left (by
        unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega)]
      simp only [wordArrayAllocationSize, wordArrayPayloadSize] at hvFit
      omega
    have hvSize := barrettVMemory_size mem fp k hk hkPos hfp hmemSize hmemLe hgap hfirstFit
    have hsource : divisorPtr + 32 + 32 * k ≤ (barrettVMemory mem fp k).size := by
      rw [hvSize]
      unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hdivisorFit : divisorPtr + 32 * (k + 1) < UInt256.size := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hfirstFit
      omega
    obtain ⟨inputs, finalMem, finalAw, loopSteps, loopGas, hlength, hfinalAw,
        hfinalSize, hfinalRead, hquotientHeader, hfinalFrame, hquotient, rd1718⟩ :=
      zeroDivisionConstantReturn_exists (top := zeroTop) (callerTail := callerTail)
        fp k divisorPtr modulusNat hkTwo hk
        hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit
        hcopyFit hsource hdivisorFit hmodulusV hmodulusLower rfl hzeroTopNe hzeroClz
        (by omega) (by simpa only [zeroTop] using rd5450)
    let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (remainderPtr fp k)) 0 k finalMem
    let stepDelta := 152 + loopSteps + 5 + 58 * k + 30 + 4
    let gasDelta := MultiLimbSchoolbookNormalizationFunction.zeroGas
      (barrettCopiedWords aw fp k) divisorPtr (normalizedDivisorPtr fp k) k +
      loopGas + 13 + 208 * k + 100 + 14
    have hrange := barrettZeroWords_range aw fp k divisorPtr hkPos hawFit hfirstFit
      hsecondFit hquotientFit huFit hvFit hcopyFit
    have hcovered : normalizedDivisorPtr fp k + wordArrayAllocationSize k ≤
        32 * finalAw.toNat := by
      rw [hfinalAw]
      simpa only [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hrange.1
    have hwordsFit : finalAw.toNat * 32 < UInt256.size := by
      rw [hfinalAw]
      exact hrange.2
    refine ⟨{
      path := .zero
      inputs := inputs
      finalMemory := copied.memory
      finalWords := finalAw
      loopSteps := loopSteps
      loopGas := loopGas
      stepDelta := stepDelta
      gasDelta := gasDelta
      inputsLength := hlength
      finalMemorySize := by simpa only [copied] using hfinalSize
      finalFreePointer := by simpa only [copied] using hfinalRead
      quotientHeader := by simpa only [copied] using hquotientHeader
      finalReadBelow := by simpa only [copied] using hfinalFrame
      workspaceCovered := hcovered
      finalWordsFit := hwordsFit
      quotient_eq := hquotient
      exactExecution := ?_ }⟩
    simpa only [copied, stepDelta, gasDelta, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      using rd1718
  · have hshiftPos : 0 <
        (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n :=
      Nat.pos_of_ne_zero hshiftZero
    have rd5450 := positiveNormalizationExact hkTwo hk hfp hmemSize hmemLe hgap hawFit
      hfirstFit hsecondFit hquotientFit huFit hvFit hvBound hdivisorPtr96 hdivisorEnd
      hdivisorHeaderRead
      hshiftPos hcalldata (by simp only [List.length_cons]; omega) h
    obtain ⟨inputs, finalMem, finalAw, loopSteps, loopGas, hlength, hfinalAw,
        hfinalSize, hfinalRead, hquotientHeader, hfinalFrame, hquotient, rd1718⟩ :=
      positiveDivisionConstantReturn_exists fp k modulusNat hkTwo hk hshiftPos hfp hmemSize
        hmemLe hgap hawFit hfirstFit hsecondFit hquotientFit huFit hvFit hsourceMem htopV
        hmodulusV hmodulusLower htopNatNe (by omega) rd5450
    let result := MultiLimbSchoolbookDenormalization.denormalizeRange finalAw
      (UInt256.ofNat (normalizedDividendPtr fp k))
      (UInt256.ofNat (remainderPtr fp k))
      (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n 0 k finalMem
    let normalizationSteps := MultiLimbSchoolbookNormalizationFunction.positiveSteps
      (barrettVMemory mem fp k) (barrettVWords aw fp k) (UInt256.ofNat divisorPtr)
      (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (normalizedDividendPtr fp k)) k (dividendLength k)
      (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n
    let normalizationGas := MultiLimbSchoolbookNormalizationFunction.positiveGas
      (barrettCopiedMemory mem fp k) (barrettCopiedWords aw fp k)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (normalizedDivisorPtr fp k))
      (UInt256.ofNat (normalizedDividendPtr fp k)) (normalizedDivisorPtr fp k) k
      (dividendLength k) (MultiLimbClz.clzResult (setupTop mem aw fp k divisorPtr)).n
    let stepDelta := normalizationSteps + loopSteps + 5 + 23 + result.steps + 6 + 4
    let gasDelta := normalizationGas + loopGas + 13 + 73 + result.gas + 26 + 14
    have hrange := barrettVWords_range aw fp k hkPos hawFit hfirstFit hsecondFit
      hquotientFit huFit hvFit
    have hcovered : normalizedDivisorPtr fp k + wordArrayAllocationSize k ≤
        32 * finalAw.toNat := by
      rw [hfinalAw]
      simpa only [wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using hrange.1
    have hwordsFit : finalAw.toNat * 32 < UInt256.size := by
      rw [hfinalAw]
      exact hrange.2
    refine ⟨{
      path := .positive
      inputs := inputs
      finalMemory := result.memory
      finalWords := finalAw
      loopSteps := loopSteps
      loopGas := loopGas
      stepDelta := stepDelta
      gasDelta := gasDelta
      inputsLength := hlength
      finalMemorySize := by simpa only [result] using hfinalSize
      finalFreePointer := by simpa only [result] using hfinalRead
      quotientHeader := by simpa only [result] using hquotientHeader
      finalReadBelow := by simpa only [result] using hfinalFrame
      workspaceCovered := hcovered
      finalWordsFit := hwordsFit
      quotient_eq := hquotient
      exactExecution := ?_ }⟩
    simpa only [result, normalizationSteps, normalizationGas, stepDelta, gasDelta,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd1718

/-- Enter at the exposed `_computeBarrettConstant` selector, execute its concrete numerator
construction and forced non-short schoolbook prefix, then construct the exact CLZ-path selector. -/
theorem exists_of_call
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k divisorPtr modulusNat : Nat} {callerTail : List UInt256}
    {baseReduced exponent : UInt256}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hfirstBound : fp + wordArrayAllocationSize (dividendLength k) < 2 ^ 64)
    (hsecondBound : remainderPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hquotientBound : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) < 2 ^ 64)
    (huBound : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) < 2 ^ 64)
    (hvBound : normalizedDivisorPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hdivisorPtr96 : 96 ≤ divisorPtr)
    (hdivisorEnd : divisorPtr + 32 * (k + 1) ≤ fp)
    (hdivisorHeaderRead : (barrettDivisionMemory mem fp k).readWithPadding divisorPtr 32 =
      UInt256.toByteArray (UInt256.ofNat k))
    (hdivisorLayout : MultiLimbArrayReadSemantic.Layout
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k) divisorPtr k)
    (hmodulus : Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
        (UInt256.ofNat divisorPtr) 0 k) = modulusNat)
    (hdivisorTopNonzero : arrayWord (barrettDivisionMemory mem fp k)
      (barrettDivisionWords aw fp k) (UInt256.ofNat divisorPtr) (k - 1) ≠ ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : callerTail.length ≤ 990)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (baseReduced :: UInt256.ofNat divisorPtr :: exponent :: UInt256.ofNat k :: callerTail)
      mem aw rdata acc steps gasUsed) :
    Nonempty (Selection (ee := I) (g := g) (s0 := initState cA gh bl σ σ₀ g A I)
      (rdata := rdata) (acc := acc) mem fp k modulusNat
      (steps + callPrefixSteps mem aw fp k divisorPtr)
      (gasUsed + callPrefixGas mem aw fp k divisorPtr)
      (exponent :: UInt256.ofNat divisorPtr :: baseReduced :: UInt256.ofNat k :: callerTail)) := by
  have hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size :=
    lt_trans (by omega : fp + wordArrayAllocationSize (dividendLength k) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hsecondFit : remainderPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : remainderPtr fp k + wordArrayAllocationSize k + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hquotientFit : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      UInt256.size :=
    lt_trans (by omega : quotientPtr fp k + wordArrayAllocationSize (quotientCount k) + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have huFit : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < UInt256.size :=
    lt_trans (by omega : normalizedDividendPtr fp k +
      wordArrayAllocationSize (dividendLength k + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvFit : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 < UInt256.size :=
    lt_trans (by omega : normalizedDivisorPtr fp k + wordArrayAllocationSize k + 31 <
      2 ^ 64 + 31) (by norm_num [UInt256.size])
  have rd3094 := MultiLimbBarrettConstant.lengthExact hk (by omega) h
  have rd5199 := MultiLimbBarrettConstant.divisionEntryExact hk hfp hfirstBound hsecondBound
    hmemSize hmemLe hgap haw3 haw64 hawFit hread hcalldata (by
      simp only [List.length_cons]
      omega) rd3094
  have rd5287 := knuthBranchExact hkTwo hk hfp hmemSize hmemLe hgap hawFit hfirstFit
    hsecondFit hdivisorLayout hdivisorTopNonzero (by
      simp only [List.length_cons]
      omega) rd5199
  have rd5368 := setupExact hkTwo hk hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit
    hquotientBound huBound hdivisorPtr96 hdivisorEnd hdivisorHeaderRead hcalldata (by
      simp only [List.length_cons]
      omega) rd5287
  have hobserver := setupObserver mem aw fp k divisorPtr hkTwo hk hawFit hfirstFit hsecondFit
    hquotientFit huFit hdivisorEnd
  rw [hobserver.2.1, hobserver.2.2] at rd5368
  simpa only [callPrefixSteps, callPrefixGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    exists_of_setup hkTwo hk hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondFit
      hquotientFit huFit hvFit hvBound hdivisorPtr96 hdivisorEnd hdivisorHeaderRead hmodulus
      hdivisorTopNonzero hcalldata (by
        simp only [List.length_cons]
        omega) rd5368

/-- Project a selected PC 1707 execution with its complete exact step and gas deltas. -/
theorem exact_of_call
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256}
    {steps gasUsed fp k divisorPtr modulusNat : Nat} {callerTail : List UInt256}
    (selected : Selection (ee := ee) (g := g) (s0 := s0) (rdata := rdata) (acc := acc)
      mem fp k modulusNat (steps + callPrefixSteps mem aw fp k divisorPtr)
      (gasUsed + callPrefixGas mem aw fp k divisorPtr) callerTail) :
    RDx runtimeBytecode ee g s0 ⟨1718⟩
      (UInt256.ofNat (quotientPtr fp k) :: callerTail)
      selected.finalMemory selected.finalWords rdata acc
      (steps + callStepDelta mem aw divisorPtr selected)
      (gasUsed + callGasDelta mem aw divisorPtr selected) := by
  simpa only [callStepDelta, callGasDelta, Nat.add_assoc] using selected.exactExecution

end Selection

end Modexp.MultiLimbBarrettConstantComplete
