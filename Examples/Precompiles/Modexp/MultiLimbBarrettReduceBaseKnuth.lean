import Examples.Precompiles.Modexp.MultiLimbBarrettReduceBaseSelection
import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupSemantic

/-!
# Constructive Knuth branch for Barrett base reduction

This module composes the selected non-short PC 5199 branch through the real quotient and
normalized-dividend allocations, `MCOPY`, divisor-top load, and `_clz`.  Subsequent theorems attach
the zero/positive normalization selectors and the complete quotient loop to this exact state.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReduceBaseKnuth

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def numQ (m k : Nat) : Nat := MultiLimbSchoolbookKnuthPrefix.numQ m k

def uFp (fp m k : Nat) : Nat := fp + wordArrayAllocationSize (numQ m k)

def vFp (fp m k : Nat) : Nat :=
  uFp fp m k + wordArrayAllocationSize (m + 1)

def setupMemory (mem : ByteArray) (fp dividendPtr m k : Nat) : ByteArray :=
  MultiLimbSchoolbookKnuthPrefix.copiedMemory mem fp (uFp fp m k) dividendPtr m k

def setupWords (aw : UInt256) (fp dividendPtr m k divisorPtr : Nat) : UInt256 :=
  MultiLimbSchoolbookKnuthPrefix.finalWords aw fp (uFp fp m k) dividendPtr m k
    (UInt256.ofNat divisorPtr)

def normalizedWords (aw : UInt256) (fp dividendPtr m k divisorPtr : Nat) : UInt256 :=
  MultiLimbSchoolbookNormalization.vWords
    (setupWords aw fp dividendPtr m k divisorPtr) (vFp fp m k) k

def vMemory (mem : ByteArray) (fp dividendPtr m k : Nat) : ByteArray :=
  MultiLimbSchoolbookNormalization.vMemory
    (setupMemory mem fp dividendPtr m k) (vFp fp m k) k

def positiveDivisorResult (mem : ByteArray) (aw : UInt256)
    (fp dividendPtr divisorPtr m k shift : Nat) :
    MultiLimbSchoolbookNormalization.DivisorShiftResult :=
  MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult
    (vMemory mem fp dividendPtr m k)
    (normalizedWords aw fp dividendPtr m k divisorPtr)
    (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m k)) k shift

def positiveDividendResult (mem : ByteArray) (aw : UInt256)
    (fp dividendPtr divisorPtr m k shift : Nat) :
    MultiLimbSchoolbookNormalization.DivisorShiftResult :=
  MultiLimbSchoolbookNormalizationFunction.positiveDividendResult
    (vMemory mem fp dividendPtr m k)
    (normalizedWords aw fp dividendPtr m k divisorPtr)
    (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m k))
    (UInt256.ofNat (uFp fp m k)) k m shift

def positiveMemory (mem : ByteArray) (aw : UInt256)
    (fp dividendPtr divisorPtr m k shift : Nat) : ByteArray :=
  MultiLimbSchoolbookNormalizationFunction.positiveMemory
    (vMemory mem fp dividendPtr m k)
    (normalizedWords aw fp dividendPtr m k divisorPtr)
    (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m k))
    (UInt256.ofNat (uFp fp m k)) k m shift

def zeroMemory (mem : ByteArray) (fp dividendPtr divisorPtr m k : Nat) : ByteArray :=
  MultiLimbSchoolbookNormalizationFunction.zeroMemory
    (setupMemory mem fp dividendPtr m k) divisorPtr (vFp fp m k) k

def zeroWords (aw : UInt256) (fp dividendPtr divisorPtr m k : Nat) : UInt256 :=
  MultiLimbSchoolbookNormalizationFunction.zeroWords
    (setupWords aw fp dividendPtr m k divisorPtr) divisorPtr (vFp fp m k) k

def setupTop (mem : ByteArray) (aw : UInt256)
    (fp dividendPtr divisorPtr m k : Nat) : UInt256 :=
  MultiLimbClz.loadedTopWord (setupMemory mem fp dividendPtr m k)
    (MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords aw fp (uFp fp m k)
      dividendPtr m k (UInt256.ofNat divisorPtr))
    (MultiLimbSchoolbookKnuthPrefix.topAddress (UInt256.ofNat divisorPtr) k)

/-- Concrete payload addresses for any allocator pointer used by this branch. -/
theorem arrayAddressNat
    (ptr index : Nat)
    (hfit : ptr + 32 * (index + 1) < UInt256.size) :
    (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index).toNat =
      ptr + 32 * (index + 1) := by
  have hptr : ptr < UInt256.size := by omega
  unfold MultiLimbSchoolbookNormalization.arrayAddress
    MultiLimbSchoolbookSingle.arrayAddress MultiLimbSchoolbookShort.arrayAddress
  simpa [UInt256.toNat_ofNat_of_lt hptr] using
    MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit (UInt256.ofNat ptr) index (by
      simpa [UInt256.toNat_ofNat_of_lt hptr] using hfit)

/-- A covered guarded array observer is zero whenever its concrete padded read is the zero word.
The address may be at or beyond the current physical byte extent. -/
theorem arrayWord_eq_zero_of_read_zero
    (mem : ByteArray) (aw : UInt256) (ptr index : Nat)
    (hfit : ptr + 32 * (index + 1) < UInt256.size)
    (hactive : ptr + 32 * (index + 1) + 32 ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding (ptr + 32 * (index + 1)) 32 =
      UInt256.toByteArray ⟨0⟩) :
    MultiLimbSchoolbookNormalization.arrayWord mem aw (UInt256.ofNat ptr) index = ⟨0⟩ := by
  have hptr : ptr < UInt256.size := by omega
  have haddress :
      (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index).toNat =
        ptr + 32 * (index + 1) := arrayAddressNat ptr index hfit
  have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hactiveGuard : ¬
      MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat ptr) index ≥
        aw * ⟨32⟩ := by
    intro hge
    have hnat : (aw * ⟨32⟩).toNat ≤
        (MultiLimbSchoolbookNormalization.arrayAddress
          (UInt256.ofNat ptr) index).toNat := hge
    rw [haddress, hawMul] at hnat
    omega
  have haddressShort :
      (MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) index).toNat =
        ptr + 32 * (index + 1) := haddress
  have hactiveGuardShort : ¬
      MultiLimbSchoolbookShort.arrayAddress (UInt256.ofNat ptr) index ≥ aw * ⟨32⟩ :=
    hactiveGuard
  unfold MultiLimbSchoolbookNormalization.arrayWord
    MultiLimbSchoolbookSingle.arrayWord MultiLimbSchoolbookShort.arrayWord
    MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
    MultiLimbDivisionTrace.readWord
  by_cases hmem : ptr + 32 * (index + 1) ≥ mem.size
  · rw [if_pos (Or.inl (by rwa [haddressShort]))]
  · rw [if_neg (not_or.mpr ⟨by rwa [haddressShort], hactiveGuardShort⟩), haddressShort, hread,
      fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- A concrete nonzero top limb gives the usual radix lower bound for the complete array. -/
theorem arrayValueLowerOfTopNonzero
    (mem : ByteArray) (aw array top : UInt256) (count : Nat)
    (hcount : 0 < count)
    (htop : MultiLimbSchoolbookNormalization.arrayWord mem aw array (count - 1) = top)
    (htopNonzero : top ≠ ⟨0⟩) :
    UInt256.size ^ (count - 1) ≤
      Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw array 0 count) := by
  have hsplit := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_succ_append
    mem aw array 0 (count - 1)
  have hcountEq : count - 1 + 1 = count := by omega
  rw [hcountEq] at hsplit
  simp only [Nat.zero_add] at hsplit
  have htopNat : 0 < top.toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact htopNonzero (uint256_toNat_eq_zero hzero)
  rw [hsplit, Modexp.wordLimbsToNat_append, htop]
  have hlowNonnegative : 0 ≤ Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw array 0 (count - 1)) :=
    Nat.zero_le _
  simp only [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length,
    Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero] at *
  have hpow : 0 < UInt256.size ^ (count - 1) :=
    Nat.pow_pos (by norm_num [UInt256.size])
  nlinarith

/-- Generic initial-window radix bound for normalized Knuth division.  Both operands retain the
same CLZ factor, so the proof still passes through the scaled computations used by bytecode. -/
theorem normalizedFullBound
    (m k shift dividend divisor : Nat)
    (hkPos : 0 < k) (hkLe : k ≤ m)
    (hdividend : dividend < UInt256.size ^ m)
    (hdivisor : UInt256.size ^ (k - 1) ≤ divisor) :
    dividend * 2 ^ shift <
      UInt256.size ^ (numQ m k - 1) *
        (UInt256.size * (divisor * 2 ^ shift)) := by
  have hq : numQ m k - 1 = m - k := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hexponent : m = (m - k) + (1 + (k - 1)) := by omega
  have hradix : UInt256.size ^ m =
      UInt256.size ^ (m - k) * (UInt256.size * UInt256.size ^ (k - 1)) := by
    calc
      UInt256.size ^ m = UInt256.size ^ ((m - k) + (1 + (k - 1))) :=
        congrArg (fun exponent => UInt256.size ^ exponent) hexponent
      _ = UInt256.size ^ (m - k) *
          (UInt256.size * UInt256.size ^ (k - 1)) := by
        rw [pow_add, pow_add, pow_one]
  have hbase : dividend <
      UInt256.size ^ (m - k) * (UInt256.size * divisor) := by
    calc
      dividend < UInt256.size ^ m := hdividend
      _ = UInt256.size ^ (m - k) *
          (UInt256.size * UInt256.size ^ (k - 1)) := hradix
      _ ≤ UInt256.size ^ (m - k) * (UInt256.size * divisor) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdivisor)
  have hscaled := Nat.mul_lt_mul_of_pos_right hbase (show 0 < 2 ^ shift by positivity)
  rw [hq]
  calc
    dividend * 2 ^ shift <
        (UInt256.size ^ (m - k) * (UInt256.size * divisor)) * 2 ^ shift := hscaled
    _ = UInt256.size ^ (m - k) * (UInt256.size * (divisor * 2 ^ shift)) := by ring

/-- The real quotient/`u` allocations and `MCOPY` leave memory at the end of the copied `m`
payload words.  The unmaterialized `u[m]` carry word accounts for the one-word gap before `v`. -/
theorem setupMemory_size
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64) :
    (setupMemory mem fp dividendPtr m divisorCount).size =
      uFp fp m divisorCount + 32 + 32 * m := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.divisorTwo
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qMem := MultiLimbSchoolbookKnuthPrefix.quotientMemory mem fp m divisorCount
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqSetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))).size =
        mem.size := setFreePtr_size facts.memory96
  have hqSize : qMem.size = fp + 32 := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).size = fp + 32
    apply storeBytesLength_size
    · rw [hqSetSize]
      exact facts.memoryLeFp
    · rw [hqSetSize]
      exact facts.fpGap
  have hq96 : 96 ≤ qMem.size := by
    rw [hqSize]
    have := facts.fp96
    omega
  have hqLeU : qMem.size ≤ uFp fp m divisorCount := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : uFp fp m divisorCount - qMem.size < USize.size := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 * 32 < USize.size := by native_decide
    omega
  let uMem := MultiLimbSchoolbookKnuthPrefix.uMemory mem fp
    (uFp fp m divisorCount) m divisorCount
  have huSetSize : (setFreePtr qMem
      (uFp fp m divisorCount + wordArrayAllocationSize (m + 1))).size = qMem.size :=
    setFreePtr_size hq96
  have huSize : uMem.size = uFp fp m divisorCount + 32 := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [huSetSize]
      exact hqLeU
    · rw [huSetSize]
      exact hqGapU
  have hsource : dividendPtr + 32 + 32 * m ≤ uMem.size := by
    rw [huSize]
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    omega
  have hsize := write_end_size_from uMem uMem (dividendPtr + 32) (32 * m)
    (by omega) hsource
  dsimp only [uMem] at hsize
  unfold setupMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
    MultiLimbSchoolbookKnuthSetup.copiedUMemory
  rw [← huSize]
  exact hsize

/-- `MCOPY` and the two divisor loads are wholly covered by the `u` allocation, so setup does not
silently change the guarded-array observer after that allocation. -/
theorem setupWords_eq_uWords
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    setupWords aw fp dividendPtr m divisorCount divisorPtr =
      MultiLimbSchoolbookKnuthPrefix.uWords aw fp (uFp fp m divisorCount) m divisorCount := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.divisorTwo
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have hdividendBeforeU : dividendPtr + 32 ≤ uFp fp m divisorCount := by
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold uFp
    omega
  have hmax : max (uFp fp m divisorCount + 32) (dividendPtr + 32) =
      uFp fp m divisorCount + 32 := max_eq_left (by omega)
  have hcopyCovered : max (uFp fp m divisorCount + 32) (dividendPtr + 32) + 32 * m ≤
      32 * uAw.toNat := by
    rw [hmax, huAwEq]
    exact le_trans (by omega) huRange.1
  have hcopied : MultiLimbSchoolbookKnuthPrefix.copiedWords aw fp
      (uFp fp m divisorCount) dividendPtr m divisorCount = uAw := by
    unfold MultiLimbSchoolbookKnuthPrefix.copiedWords
      MultiLimbSchoolbookKnuthSetup.copiedUWords
    rw [machineM_eq_of_access hcopyCovered]
    exact u256_ofNat_toNat uAw
  have hdivisorPtrFit : divisorPtr < UInt256.size :=
    lt_trans (by
      have := facts.divisorPtr96
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hdivisorHeaderActive : (UInt256.ofNat divisorPtr).toNat + 32 ≤ 32 * uAw.toNat := by
    rw [UInt256.toNat_ofNat_of_lt hdivisorPtrFit, huAwEq]
    exact le_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      omega : divisorPtr + 32 ≤ uFp fp m divisorCount + 32 + 32 * (m + 1)) huRange.1
  have htopFit : divisorPtr + 32 * divisorCount < UInt256.size := by
    exact lt_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : divisorPtr + 32 * divisorCount < 2 ^ 64)
      (by norm_num [UInt256.size])
  have htopAddress :
      (MultiLimbSchoolbookKnuthPrefix.topAddress (UInt256.ofNat divisorPtr) divisorCount).toNat =
        divisorPtr + 32 * divisorCount := by
    unfold MultiLimbSchoolbookKnuthPrefix.topAddress
    have hindex : divisorCount - 1 + 1 = divisorCount := by
      have := facts.divisorTwo
      omega
    rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit]
    · rw [UInt256.toNat_ofNat_of_lt hdivisorPtrFit, hindex]
    · rw [UInt256.toNat_ofNat_of_lt hdivisorPtrFit, hindex]
      exact htopFit
  have htopActive :
      (MultiLimbSchoolbookKnuthPrefix.topAddress
        (UInt256.ofNat divisorPtr) divisorCount).toNat + 32 ≤ 32 * uAw.toNat := by
    rw [htopAddress, huAwEq]
    exact le_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      omega : divisorPtr + 32 * divisorCount + 32 ≤
        uFp fp m divisorCount + 32 + 32 * (m + 1)) huRange.1
  unfold setupWords MultiLimbSchoolbookKnuthPrefix.finalWords
    MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords MultiLimbClz.afterTopLoad
  rw [hcopied, MultiLimbOddCompare.afterHeader_eq_of_access uAw _ hdivisorHeaderActive,
    MultiLimbOddCompare.afterHeader_eq_of_access uAw _ htopActive]

/-- The setup `MCOPY` itself remains within the active extent of the `u` allocation. -/
theorem copiedWords_eq_uWords
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    MultiLimbSchoolbookKnuthPrefix.copiedWords aw fp (uFp fp m divisorCount)
      dividendPtr m divisorCount =
      MultiLimbSchoolbookKnuthPrefix.uWords aw fp (uFp fp m divisorCount) m divisorCount := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have hmax : max (uFp fp m divisorCount + 32) (dividendPtr + 32) =
      uFp fp m divisorCount + 32 := max_eq_left (by
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold uFp
    omega)
  unfold MultiLimbSchoolbookKnuthPrefix.copiedWords
    MultiLimbSchoolbookKnuthSetup.copiedUWords
  rw [machineM_eq_of_access]
  · exact u256_ofNat_toNat uAw
  · rw [hmax]
    change uFp fp m divisorCount + 32 + 32 * m ≤ 32 * uAw.toNat
    rw [huAwEq]
    exact le_trans (by omega) huRange.1

/-- The divisor-header load and following top load are both covered, so the CLZ input observer is
the same active-word counter as the final PC 5368 state. -/
theorem setupHeaderWords_eq_setupWords
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords aw fp (uFp fp m divisorCount)
      dividendPtr m divisorCount (UInt256.ofNat divisorPtr) =
      setupWords aw fp dividendPtr m divisorCount divisorPtr := by
  have hcopied := copiedWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hfinal := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have hdivisorFit : divisorPtr < UInt256.size := by
    exact lt_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hactive : (UInt256.ofNat divisorPtr).toNat + 32 ≤ 32 * uAw.toNat := by
    rw [UInt256.toNat_ofNat_of_lt hdivisorFit, huAwEq]
    exact le_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      unfold uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) huRange.1
  unfold MultiLimbSchoolbookKnuthPrefix.divisorHeaderWords
  rw [hcopied, MultiLimbOddCompare.afterHeader_eq_of_access uAw _ hactive, hfinal]

/-- The exact `_clz` argument is the top guarded divisor word in the setup memory. -/
theorem setupTop_eq_setupArrayTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    setupTop mem aw fp dividendPtr divisorPtr m divisorCount =
      MultiLimbSchoolbookNormalization.arrayWord
        (setupMemory mem fp dividendPtr m divisorCount)
        (setupWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat divisorPtr) (divisorCount - 1) := by
  have hwords := setupHeaderWords_eq_setupWords facts hmPos hmDividend
    hquotientBound huBound
  unfold setupTop MultiLimbClz.loadedTopWord
    MultiLimbSchoolbookNormalization.arrayWord MultiLimbSchoolbookSingle.arrayWord
    MultiLimbSchoolbookShort.arrayWord MultiLimbOddCompare.loadedWord
    MultiLimbSchoolbookKnuthPrefix.topAddress
    MultiLimbSchoolbookShort.arrayAddress
  rw [hwords]

/-- The setup allocations and append-at-end `MCOPY` preserve every complete pre-existing word
below the quotient allocation pointer. -/
theorem setupMemory_read_below
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m ptr : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hptr96 : 96 ≤ ptr) (hptrEnd : ptr + 32 ≤ fp) :
    (setupMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 =
      mem.readWithPadding ptr 32 := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.divisorTwo
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  let qMem := MultiLimbSchoolbookKnuthPrefix.quotientMemory mem fp m divisorCount
  have hqRead : qMem.readWithPadding ptr 32 = mem.readWithPadding ptr 32 := by
    simpa only [qMem, MultiLimbSchoolbookKnuthPrefix.quotientMemory,
      MultiLimbSchoolbookKnuthSetup.quotientMemory, numQ] using
      MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below mem fp
        (numQ m divisorCount) ptr facts.memory96 facts.fpGap hptr96 hptrEnd
  have hqSetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))).size =
        mem.size := setFreePtr_size facts.memory96
  have hqSize : qMem.size = fp + 32 := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).size = fp + 32
    apply storeBytesLength_size
    · rw [hqSetSize]
      exact facts.memoryLeFp
    · rw [hqSetSize]
      exact facts.fpGap
  have hq96 : 96 ≤ qMem.size := by
    rw [hqSize]
    have := facts.fp96
    omega
  have hqLeU : qMem.size ≤ uFp fp m divisorCount := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : uFp fp m divisorCount - qMem.size < USize.size := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 * 32 < USize.size := by native_decide
    omega
  let uMem := MultiLimbSchoolbookKnuthPrefix.uMemory mem fp
    (uFp fp m divisorCount) m divisorCount
  have huRead : uMem.readWithPadding ptr 32 = qMem.readWithPadding ptr 32 := by
    simpa only [uMem, MultiLimbSchoolbookKnuthPrefix.uMemory,
      MultiLimbSchoolbookKnuthSetup.uMemory] using
      MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below qMem
        (uFp fp m divisorCount) (m + 1) ptr hq96 hqGapU hptr96 (by
          exact le_trans hptrEnd (by unfold uFp; omega))
  have huSetSize : (setFreePtr qMem
      (uFp fp m divisorCount + wordArrayAllocationSize (m + 1))).size = qMem.size :=
    setFreePtr_size hq96
  have huSize : uMem.size = uFp fp m divisorCount + 32 := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [huSetSize]
      exact hqLeU
    · rw [huSetSize]
      exact hqGapU
  have hsource : dividendPtr + 32 + 32 * m ≤ uMem.size := by
    rw [huSize]
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    omega
  have hcopy := write_read_below_end_from uMem uMem (dividendPtr + 32) (32 * m)
    ptr (by omega) hsource (by rw [huSize]; omega)
  dsimp only [uMem] at hcopy
  unfold setupMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
    MultiLimbSchoolbookKnuthSetup.copiedUMemory
  rw [← huSize]
  exact hcopy.trans (huRead.trans hqRead)

/-- The second allocator installs `vFp` at Solidity's free-pointer slot, and `MCOPY` starts above
that slot. -/
theorem setupMemory_freeRead
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) :
    (setupMemory mem fp dividendPtr m divisorCount).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (vFp fp m divisorCount)) := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.divisorTwo
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  let qMem := MultiLimbSchoolbookKnuthPrefix.quotientMemory mem fp m divisorCount
  have hqSetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))).size =
        mem.size := setFreePtr_size facts.memory96
  have hqSize : qMem.size = fp + 32 := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).size = fp + 32
    apply storeBytesLength_size
    · rw [hqSetSize]
      exact facts.memoryLeFp
    · rw [hqSetSize]
      exact facts.fpGap
  have hq96 : 96 ≤ qMem.size := by
    rw [hqSize]
    have := facts.fp96
    omega
  have hqLeU : qMem.size ≤ uFp fp m divisorCount := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : uFp fp m divisorCount - qMem.size < USize.size := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 * 32 < USize.size := by native_decide
    omega
  let uMem := MultiLimbSchoolbookKnuthPrefix.uMemory mem fp
    (uFp fp m divisorCount) m divisorCount
  have huSetSize : (setFreePtr qMem
      (uFp fp m divisorCount + wordArrayAllocationSize (m + 1))).size = qMem.size :=
    setFreePtr_size hq96
  have huSize : uMem.size = uFp fp m divisorCount + 32 := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [huSetSize]
      exact hqLeU
    · rw [huSetSize]
      exact hqGapU
  have huFree : uMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (vFp fp m divisorCount)) := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    change (storeBytesLength (setFreePtr qMem (vFp fp m divisorCount))
      (uFp fp m divisorCount) (m + 1)).readWithPadding 64 32 = _
    rw [storeBytesLength_read_below]
    · exact setFreePtr_read64 hq96
    · rw [setFreePtr_size hq96]
      exact hq96
    · unfold uFp
      unfold wordArrayAllocationSize wordArrayPayloadSize
      have := facts.fp96
      omega
    · rw [setFreePtr_size hq96]
      exact hqGapU
  have hsource : dividendPtr + 32 + 32 * m ≤ uMem.size := by
    rw [huSize]
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    omega
  have hcopy := write_read_below_end_from uMem uMem (dividendPtr + 32) (32 * m)
    64 (by omega) hsource (by rw [huSize]; omega)
  dsimp only [uMem] at hcopy
  unfold setupMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
    MultiLimbSchoolbookKnuthSetup.copiedUMemory
  rw [← huSize]
  exact hcopy.trans huFree

/-- Raw quotient and normalized-dividend headers installed by the two real allocations and
preserved by the following append-at-end copy. -/
theorem setupMemory_newHeaderReads
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) :
    (setupMemory mem fp dividendPtr m divisorCount).readWithPadding fp 32 =
        UInt256.toByteArray (UInt256.ofNat (numQ m divisorCount)) ∧
      (setupMemory mem fp dividendPtr m divisorCount).readWithPadding
          (uFp fp m divisorCount) 32 =
        UInt256.toByteArray (UInt256.ofNat (m + 1)) := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  let qMem := MultiLimbSchoolbookKnuthPrefix.quotientMemory mem fp m divisorCount
  have hqSetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))).size =
        mem.size := setFreePtr_size facts.memory96
  have hqHeader : qMem.readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (numQ m divisorCount)) := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    apply storeBytesLength_read_self
    rw [setFreePtr_size facts.memory96]
    exact facts.fpGap
  have hqSize : qMem.size = fp + 32 := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).size = fp + 32
    apply storeBytesLength_size
    · rw [hqSetSize]
      exact facts.memoryLeFp
    · rw [hqSetSize]
      exact facts.fpGap
  have hq96 : 96 ≤ qMem.size := by
    rw [hqSize]
    have := facts.fp96
    omega
  have hqLeU : qMem.size ≤ uFp fp m divisorCount := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : uFp fp m divisorCount - qMem.size < USize.size := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 * 32 < USize.size := by native_decide
    omega
  let uMem := MultiLimbSchoolbookKnuthPrefix.uMemory mem fp
    (uFp fp m divisorCount) m divisorCount
  have hqHeaderU : uMem.readWithPadding fp 32 = qMem.readWithPadding fp 32 := by
    simpa only [uMem, MultiLimbSchoolbookKnuthPrefix.uMemory,
      MultiLimbSchoolbookKnuthSetup.uMemory] using
      MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below qMem
        (uFp fp m divisorCount) (m + 1) fp hq96 hqGapU facts.fp96 (by
          unfold uFp wordArrayAllocationSize wordArrayPayloadSize
          omega)
  have huHeader : uMem.readWithPadding (uFp fp m divisorCount) 32 =
      UInt256.toByteArray (UInt256.ofNat (m + 1)) := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_read_self
    rw [setFreePtr_size hq96]
    exact hqGapU
  have huSize : uMem.size = uFp fp m divisorCount + 32 := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size hq96]
      exact hqLeU
    · rw [setFreePtr_size hq96]
      exact hqGapU
  have hsource : dividendPtr + 32 + 32 * m ≤ uMem.size := by
    rw [huSize]
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    omega
  have hcopyQ := write_read_below_end_from uMem uMem (dividendPtr + 32) (32 * m)
    fp (by omega) hsource (by rw [huSize]; unfold uFp; omega)
  have hcopyU := write_read_below_end_from uMem uMem (dividendPtr + 32) (32 * m)
    (uFp fp m divisorCount) (by omega) hsource (by rw [huSize])
  dsimp only [uMem] at hcopyQ hcopyU
  unfold setupMemory MultiLimbSchoolbookKnuthPrefix.copiedMemory
    MultiLimbSchoolbookKnuthSetup.copiedUMemory
  rw [← huSize]
  exact ⟨hcopyQ.trans (hqHeaderU.trans hqHeader), hcopyU.trans huHeader⟩

/-- All arrays visible at PC 5368 under the concrete post-setup memory observer. -/
structure SetupLayouts
    (mem : ByteArray) (aw : UInt256)
    (fp uPtr divisorPtr remPtr quotientCount m divisorCount : Nat) : Prop where
  quotient : MultiLimbArrayReadSemantic.Layout mem aw fp quotientCount
  dividend : MultiLimbArrayReadSemantic.Layout mem aw uPtr (m + 1)
  divisor : MultiLimbArrayReadSemantic.Layout mem aw divisorPtr divisorCount
  remainder : MultiLimbArrayReadSemantic.Layout mem aw remPtr divisorCount

/-- Construct every PC 5368 layout from the entry layouts and the actual allocation/copy frame. -/
theorem setupLayouts
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    SetupLayouts (setupMemory mem fp dividendPtr m divisorCount)
      (setupWords aw fp dividendPtr m divisorCount divisorPtr)
      fp (uFp fp m divisorCount) divisorPtr remPtr
      (numQ m divisorCount) m divisorCount := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have hsetupAw : setupWords aw fp dividendPtr m divisorCount divisorPtr = uAw :=
    setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hheaders := setupMemory_newHeaderReads facts hmPos hmDividend
  have hdivisorRead := setupMemory_read_below facts hmPos hmDividend facts.divisorPtr96
    (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      omega)
  have hrem96 : 96 ≤ remPtr := by
    have := facts.divisorPtr96
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    omega
  have hremRead := setupMemory_read_below facts hmPos hmDividend hrem96 (by
    have := facts.remainderEndBeforeFp
    omega)
  have hsetupFit : uAw.toNat * 32 < UInt256.size := by
    rw [huAwEq]
    exact huRange.2
  have hactiveEnd : vFp fp m divisorCount ≤ 32 * uAw.toNat := by
    rw [huAwEq]
    simpa only [vFp, wordArrayAllocationSize, wordArrayPayloadSize, Nat.add_assoc] using
      huRange.1
  have hvBound : vFp fp m divisorCount < 2 ^ 64 := by
    simpa only [vFp] using huBound
  have build : ∀ ptr count,
      ptr + 32 ≤ (setupMemory mem fp dividendPtr m divisorCount).size →
      ptr + 32 + 32 * count ≤ vFp fp m divisorCount →
      (setupMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 =
        UInt256.toByteArray (UInt256.ofNat count) →
      MultiLimbArrayReadSemantic.Layout
        (setupMemory mem fp dividendPtr m divisorCount) uAw ptr count := by
    intro ptr count hmem hbefore hread
    apply MultiLimbArrayReadSemantic.layout_of_geometry
    · exact lt_trans (by omega : ptr + 32 * (count + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])
    · exact hmem
    · exact le_trans (by omega) hactiveEnd
    · exact hsetupFit
    · exact hread
  rw [hsetupAw]
  refine {
    quotient := build fp (numQ m divisorCount) ?_ ?_ hheaders.1
    dividend := build (uFp fp m divisorCount) (m + 1) ?_ ?_ hheaders.2
    divisor := build divisorPtr divisorCount ?_ ?_ (hdivisorRead.trans facts.divisorHeaderRead)
    remainder := build remPtr divisorCount ?_ ?_ (hremRead.trans facts.remainderHeaderRead)
  }
  · rw [hsetupSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hsetupSize]
    omega
  · unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hsetupSize]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hsetupSize]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega

/-- A physically materialized operand below the remainder header has the same guarded words after
the complete Knuth setup, despite both memory and the active-word counter changing. -/
theorem setupOriginalWords_eq
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m ptr count : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hptr96 : 96 ≤ ptr) (hend : ptr + 32 + 32 * count ≤ remPtr) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (setupMemory mem fp dividendPtr m divisorCount)
        (setupWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat ptr) 0 count =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat ptr) 0 count := by
  have hsetupAw := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hcovered := facts.memoryCovered
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
  apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
  intro i hi
  simp only [Nat.zero_add]
  have hwordFit : ptr + 32 * (i + 1) < UInt256.size :=
    lt_trans (by
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : ptr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])
  have hread := setupMemory_read_below facts hmPos hmDividend (ptr := ptr + 32 * (i + 1))
    (by omega) (by
      have := facts.remainderEndBeforeFp
      omega)
  apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
  · exact hwordFit
  · rw [hsetupSize]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [facts.memorySizeEq]
    omega
  · rw [hsetupAw]
    exact le_trans (by
      have := facts.remainderEndBeforeFp
      unfold uFp wordArrayAllocationSize wordArrayPayloadSize
      omega : ptr + 32 * (i + 1) + 32 ≤
        uFp fp m divisorCount + 32 + 32 * (m + 1)) huRange.1
  · exact le_trans (by rw [facts.memorySizeEq]; omega) hcovered
  · rw [hsetupAw]
    exact huRange.2
  · exact facts.awFit
  · exact hread

/-- One concrete word in the setup `u` payload is the corresponding original dividend word. -/
theorem setupMemory_copiedRead
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m i : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hi : i < m) :
    (setupMemory mem fp dividendPtr m divisorCount).readWithPadding
        (uFp fp m divisorCount + 32 + 32 * i) 32 =
      mem.readWithPadding (dividendPtr + 32 + 32 * i) 32 := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  let qMem := MultiLimbSchoolbookKnuthPrefix.quotientMemory mem fp m divisorCount
  have hqSetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))).size =
        mem.size := setFreePtr_size facts.memory96
  have hqSize : qMem.size = fp + 32 := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).size = fp + 32
    apply storeBytesLength_size
    · rw [hqSetSize]
      exact facts.memoryLeFp
    · rw [hqSetSize]
      exact facts.fpGap
  have hq96 : 96 ≤ qMem.size := by
    rw [hqSize]
    have := facts.fp96
    omega
  have hqLeU : qMem.size ≤ uFp fp m divisorCount := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : uFp fp m divisorCount - qMem.size < USize.size := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 * 32 < USize.size := by native_decide
    omega
  let uMem := MultiLimbSchoolbookKnuthPrefix.uMemory mem fp
    (uFp fp m divisorCount) m divisorCount
  have huSize : uMem.size = uFp fp m divisorCount + 32 := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size hq96]
      exact hqLeU
    · rw [setFreePtr_size hq96]
      exact hqGapU
  have hsource : dividendPtr + 32 + 32 * m ≤ uMem.size := by
    rw [huSize]
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    omega
  have hdest : uFp fp m divisorCount + 32 ≤ uMem.size := by rw [huSize]
  have hcopied := MultiLimbSchoolbookKnuthSetupSemantic.copiedUMemory_read_word
    uMem (uFp fp m divisorCount) dividendPtr m i hmPos hi hsource hdest
  have hsourceFrame := write_read_below_end_from uMem uMem (dividendPtr + 32) (32 * m)
    (dividendPtr + 32 + 32 * i) (by omega) hsource (by
      rw [huSize]
      omega)
  have hsourceOld := setupMemory_read_below facts hmPos hmDividend
    (ptr := dividendPtr + 32 + 32 * i) (by
      have := facts.divisorPtr96
      have := facts.divisorEndBeforeDividend
      omega) (by
        have := facts.dividendEndBeforeRemainder
        have := facts.remainderEndBeforeFp
        omega)
  rw [huSize] at hsourceFrame
  have hresult := hcopied.trans (hsourceFrame.symm.trans hsourceOld)
  simpa only [setupMemory, MultiLimbSchoolbookKnuthPrefix.copiedMemory, uMem] using hresult

/-- The concrete `u[0..m)` observer is exactly the selected trimmed dividend observer. -/
theorem setupDividendWords_eq
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (setupMemory mem fp dividendPtr m divisorCount)
        (setupWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat (uFp fp m divisorCount)) 0 m =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat dividendPtr) 0 m := by
  have hsetupAw := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hcovered := facts.memoryCovered
  unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered at hcovered
  apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
  intro i hi
  simp only [Nat.zero_add]
  have hleftFit : uFp fp m divisorCount + 32 * (i + 1) < UInt256.size :=
    lt_trans (by
      have := huBound
      unfold wordArrayAllocationSize wordArrayPayloadSize at huBound
      omega : uFp fp m divisorCount + 32 * (i + 1) < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hrightFit : dividendPtr + 32 * (i + 1) < UInt256.size :=
    lt_trans (by
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : dividendPtr + 32 * (i + 1) < 2 ^ 64)
      (by norm_num [UInt256.size])
  apply MultiLimbArrayReadSemantic.arrayWord_eq_of_distinct_readWithPadding_eq
  · exact hleftFit
  · exact hrightFit
  · rw [hsetupSize]
    omega
  · rw [facts.memorySizeEq]
    have := facts.dividendEndBeforeRemainder
    omega
  · rw [hsetupAw]
    exact le_trans (by omega) huRange.1
  · exact le_trans (by
      rw [facts.memorySizeEq]
      have := facts.dividendEndBeforeRemainder
      omega) hcovered
  · rw [hsetupAw]
    exact huRange.2
  · exact facts.awFit
  · simpa only [Nat.add_assoc, Nat.add_comm 32 (32 * i)] using
      setupMemory_copiedRead facts hmPos hmDividend hi

/-- Pointer and active-memory geometry for every descending quotient digit after allocating `v`.
This is generic in the selected dividend length; no Barrett-constant `m = 2k` specialization is
used. -/
theorem continuationGeometry
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookContinuationExecutable.ContinuationGeometry
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount))
      (UInt256.ofNat (vFp fp m divisorCount)) (UInt256.ofNat fp)
      divisorCount (m + 1) (numQ m divisorCount) := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    have := facts.dividendBound
    have := facts.divisorTwo
    omega
  have hmBound : m ≤ 32 := by
    have := facts.dividendBound
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have huAwFit : uAw.toNat * 32 < UInt256.size := by
    rw [huAwEq]
    exact huRange.2
  have hsetupAw : setupWords aw fp dividendPtr m divisorCount divisorPtr = uAw :=
    setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvRange := MultiLimbOddConversionSemantic.newWordArrayWords_range uAw
    (vFp fp m divisorCount) divisorCount (by have := facts.divisorTwo; omega)
    huAwFit hvFit
  have hqPtrFit : fp < UInt256.size := by
    exact lt_trans (by omega : fp < 2 ^ 64) (by norm_num [UInt256.size])
  have huPtrFit : uFp fp m divisorCount < UInt256.size := by
    exact lt_trans (by omega : uFp fp m divisorCount < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hvPtrFit : vFp fp m divisorCount < UInt256.size := by
    exact lt_trans (by omega : vFp fp m divisorCount < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hvNat := UInt256.toNat_ofNat_of_lt hvPtrFit
  have hawEq : normalizedWords aw fp dividendPtr m divisorCount divisorPtr =
      newWordArrayWords uAw (vFp fp m divisorCount) divisorCount := by
    unfold normalizedWords MultiLimbSchoolbookNormalization.vWords
    rw [hsetupAw]
  have hactive : vFp fp m divisorCount + 32 + 32 * divisorCount ≤
      32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    rw [hawEq]
    exact hvRange.1
  have hawFit :
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat * 32 <
        UInt256.size := by
    rw [hawEq]
    exact hvRange.2
  have hqHeaderActive : (UInt256.ofNat fp).toNat + 32 ≤
      32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    rw [hqNat]
    exact le_trans (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hactive
  have huHeaderActive : (UInt256.ofNat (uFp fp m divisorCount)).toNat + 32 ≤
      32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    rw [huNat]
    exact le_trans (by
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hactive
  have hvHeaderActive : (UInt256.ofNat (vFp fp m divisorCount)).toNat + 32 ≤
      32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    rw [hvNat]
    omega
  refine {
    hcountTwo := facts.divisorTwo
    hcountRange := facts.divisorBound
    hcountWord := lt_of_le_of_lt facts.divisorBound
      (by norm_num [UInt256.size] : 32 < UInt256.size)
    hquotientCountPos := hnumQPos
    hquotientCountWord := lt_of_le_of_lt hnumQBound
      (by norm_num [UInt256.size] : 32 < UInt256.size)
    huCountEq := by unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ; omega
    hwindowRange := by unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ; omega
    hawFit := hawFit
    hvFit := by
      rw [hvNat]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega
    huFit := by
      rw [huNat]
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega
    hquotientFit := by
      rw [hqNat]
      unfold wordArrayAllocationSize wordArrayPayloadSize at hqFit
      omega
    hvActive := by
      rw [hvNat]
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm (32 * divisorCount) 32]
        using hactive
    huTopActive := by
      rw [huNat]
      exact le_trans (by
        unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
        unfold vFp wordArrayAllocationSize wordArrayPayloadSize
        omega) hactive
    htopBelowV := by
      rw [huNat, hvNat]
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    hquotientPayloadBelowU := by
      rw [hqNat, huNat]
      unfold uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    hvHeaderAw := MultiLimbSchoolbookContinuationExecutable.arrayAfterHeader_eq_of_active _ _
      hvHeaderActive
    huHeaderAw := MultiLimbSchoolbookContinuationExecutable.arrayAfterHeader_eq_of_active _ _
      huHeaderActive
    hquotientHeaderAw :=
      MultiLimbSchoolbookContinuationExecutable.arrayAfterHeader_eq_of_active _ _
        hqHeaderActive
    hvWordAw := by
      intro i hi
      apply MultiLimbSchoolbookContinuationExecutable.arrayAfterWord_eq_of_active
      have haddress :
          (MultiLimbSchoolbookSingle.arrayAddress
            (UInt256.ofNat (vFp fp m divisorCount)) i).toNat =
            vFp fp m divisorCount + 32 * (i + 1) := arrayAddressNat _ _ (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
        omega)
      rw [haddress]
      exact le_trans (by omega) hactive
    huWordAw := by
      intro i hi
      apply MultiLimbSchoolbookContinuationExecutable.arrayAfterWord_eq_of_active
      have haddress :
          (MultiLimbSchoolbookSingle.arrayAddress
            (UInt256.ofNat (uFp fp m divisorCount)) i).toNat =
            uFp fp m divisorCount + 32 * (i + 1) := arrayAddressNat _ _ (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega)
      rw [haddress]
      exact le_trans (by
        unfold vFp wordArrayAllocationSize wordArrayPayloadSize
        omega) hactive
    hquotientWordAw := by
      intro i hi
      apply MultiLimbSchoolbookContinuationExecutable.arrayAfterWord_eq_of_active
      have haddress :
          (MultiLimbSchoolbookSingle.arrayAddress (UInt256.ofNat fp) i).toNat =
            fp + 32 * (i + 1) := arrayAddressNat _ _ (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hqFit
        omega)
      rw [haddress]
      exact le_trans (by
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega) hactive
  }

/-- The zero-CLZ `MCOPY` is wholly inside the active range established by allocating `v`, so it
does not change the exact active-word counter used by the quotient continuation. -/
theorem zeroWords_eq_normalizedWords
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    zeroWords aw fp dividendPtr divisorPtr m divisorCount =
      normalizedWords aw fp dividendPtr m divisorCount divisorPtr := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
    have := hvBound
    omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hactive := geometry.hvActive
  rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
  have hmax : max (vFp fp m divisorCount + 32) (divisorPtr + 32) =
      vFp fp m divisorCount + 32 := max_eq_left (by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp
    omega)
  have hcopyCovered : max (vFp fp m divisorCount + 32) (divisorPtr + 32) +
      32 * divisorCount ≤
        32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    rw [hmax]
    omega
  unfold zeroWords MultiLimbSchoolbookNormalizationFunction.zeroWords
    MultiLimbSchoolbookNormalization.shiftZeroWords normalizedWords
  rw [machineM_eq_of_access (by simpa only [normalizedWords] using hcopyCovered)]
  exact u256_ofNat_toNat _

/-- Allocating the normalized divisor materializes exactly its header at the old free pointer. -/
theorem vMemory_size
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64) :
    (vMemory mem fp dividendPtr m divisorCount).size = vFp fp m divisorCount + 32 := by
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsetupLe : (setupMemory mem fp dividendPtr m divisorCount).size ≤
      vFp fp m divisorCount := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hgap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  unfold vMemory MultiLimbSchoolbookNormalization.vMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hsetup96]
    exact hsetupLe
  · rw [setFreePtr_size hsetup96]
    exact hgap

/-- The fresh `v` allocation preserves every complete word below its header. -/
theorem vMemory_read_below
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m ptr : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (hptr96 : 96 ≤ ptr) (hptr : ptr + 32 ≤ vFp fp m divisorCount) :
    (vMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 =
      (setupMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 := by
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hgap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  simpa only [vMemory, MultiLimbSchoolbookNormalization.vMemory] using
    MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
      (setupMemory mem fp dividendPtr m divisorCount) (vFp fp m divisorCount)
      divisorCount ptr hsetup96 hgap hptr96 hptr

/-- The fresh normalized-divisor allocation installs its exact advanced free pointer. -/
theorem vMemory_freeRead
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64) :
    (vMemory mem fp dividendPtr m divisorCount).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (vFp fp m divisorCount + wordArrayAllocationSize divisorCount)) := by
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hgap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  unfold vMemory MultiLimbSchoolbookNormalization.vMemory
  rw [storeBytesLength_read_below_padded]
  · exact setFreePtr_read64 hsetup96
  · rw [setFreePtr_size hsetup96]
    omega
  · unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    have := facts.fp96
    omega
  · rw [setFreePtr_size hsetup96]
    exact hgap

/-- Zero-shift normalization starts copying at the end of the materialized `v` header and writes
exactly the complete divisor payload. -/
theorem zeroMemory_size
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64) :
    (zeroMemory mem fp dividendPtr divisorPtr m divisorCount).size =
      vFp fp m divisorCount + 32 + 32 * divisorCount := by
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hsource : divisorPtr + 32 + 32 * divisorCount ≤
      (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  unfold zeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  change ((vMemory mem fp dividendPtr m divisorCount).write (divisorPtr + 32)
    (vMemory mem fp dividendPtr m divisorCount) (vFp fp m divisorCount + 32)
    (32 * divisorCount)).size = _
  rw [← hvSize, write_end_size_from]
  · have := facts.divisorTwo
    omega
  · exact hsource

/-- The zero-shift `MCOPY` preserves every complete raw word at or below the `v` header. -/
theorem zeroMemory_read_below
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m ptr : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (hptr : ptr + 32 ≤ vFp fp m divisorCount + 32) :
    (zeroMemory mem fp dividendPtr divisorPtr m divisorCount).readWithPadding ptr 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 := by
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hsource : divisorPtr + 32 + 32 * divisorCount ≤
      (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  unfold zeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
    MultiLimbSchoolbookNormalization.shiftZeroMemory
  change ((vMemory mem fp dividendPtr m divisorCount).write (divisorPtr + 32)
    (vMemory mem fp dividendPtr m divisorCount) (vFp fp m divisorCount + 32)
    (32 * divisorCount)).readWithPadding ptr 32 = _
  rw [← hvSize]
  exact write_read_below_end_from (vMemory mem fp dividendPtr m divisorCount)
    (vMemory mem fp dividendPtr m divisorCount) (divisorPtr + 32)
    (32 * divisorCount) ptr (by have := facts.divisorTwo; omega) hsource (by rwa [hvSize])

/-- Each copied zero-shift `v` limb is the corresponding original divisor limb in the
post-allocation memory. -/
theorem zeroMemory_read_v_word
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m i : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (hi : i < divisorCount) :
    (zeroMemory mem fp dividendPtr divisorPtr m divisorCount).readWithPadding
        (vFp fp m divisorCount + 32 + 32 * i) 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding
        (divisorPtr + 32 + 32 * i) 32 := by
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hsource : divisorPtr + 32 + 32 * divisorCount ≤
      (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  unfold zeroMemory MultiLimbSchoolbookNormalizationFunction.zeroMemory
  exact MultiLimbSchoolbookNormalization.shiftZeroMemory_limb
    (vMemory mem fp dividendPtr m divisorCount) divisorPtr (vFp fp m divisorCount)
    divisorCount i (by have := facts.divisorTwo; omega) hi hsource (by rw [hvSize])

/-- A physically materialized original operand has the same guarded slice after allocating `v`. -/
theorem vOriginalWords_eq
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m ptr count : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hptr96 : 96 ≤ ptr) (hend : ptr + 32 + 32 * count ≤ remPtr) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (vMemory mem fp dividendPtr m divisorCount)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat ptr) 0 count =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat ptr) 0 count := by
  have hsetupAw := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have huAwFit : uAw.toNat * 32 < UInt256.size := by rw [huAwEq]; exact huRange.2
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvRange := MultiLimbOddConversionSemantic.newWordArrayWords_range uAw
    (vFp fp m divisorCount) divisorCount (by have := facts.divisorTwo; omega)
    huAwFit hvFit
  have hawEq : normalizedWords aw fp dividendPtr m divisorCount divisorPtr =
      newWordArrayWords uAw (vFp fp m divisorCount) divisorCount := by
    unfold normalizedWords MultiLimbSchoolbookNormalization.vWords
    rw [hsetupAw]
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hsetupEq := setupOriginalWords_eq facts hmPos hmDividend hquotientBound huBound
    hptr96 hend
  have hvSetup :
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (vMemory mem fp dividendPtr m divisorCount)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat ptr) 0 count =
        MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (setupMemory mem fp dividendPtr m divisorCount)
          (setupWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat ptr) 0 count := by
    apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
    intro i hi
    simp only [Nat.zero_add]
    have hwordFit : ptr + 32 * (i + 1) < UInt256.size :=
      lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : ptr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])
    have hread := vMemory_read_below facts hmPos hmDividend hquotientBound
      (ptr := ptr + 32 * (i + 1)) (by omega) (by
        have := facts.remainderEndBeforeFp
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega)
    apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
    · exact hwordFit
    · rw [hvSize]
      have := facts.remainderEndBeforeFp
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hsetupSize]
      have := facts.remainderEndBeforeFp
      unfold uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hawEq]
      exact le_trans (by
        have := facts.remainderEndBeforeFp
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega) hvRange.1
    · rw [hsetupAw]
      change ptr + 32 * (i + 1) + 32 ≤ 32 * uAw.toNat
      rw [huAwEq]
      exact le_trans (by
        have := facts.remainderEndBeforeFp
        unfold uFp wordArrayAllocationSize wordArrayPayloadSize
        omega) huRange.1
    · rw [hawEq]
      exact hvRange.2
    · rw [hsetupAw]
      exact huAwFit
    · exact hread
  exact hvSetup.trans hsetupEq

/-- The top source limb in the freshly allocated normalization state is exactly the word passed
to `_clz` during setup. -/
theorem vDivisorTop_eq_setupTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayWord
      (vMemory mem fp dividendPtr m divisorCount)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (divisorCount - 1) =
        setupTop mem aw fp dividendPtr divisorPtr m divisorCount := by
  have hdivisorEnd : divisorPtr + 32 + 32 * divisorCount ≤ remPtr := by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    omega
  have hsetupAw := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have huAwFit : uAw.toNat * 32 < UInt256.size := by rw [huAwEq]; exact huRange.2
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvRange := MultiLimbOddConversionSemantic.newWordArrayWords_range uAw
    (vFp fp m divisorCount) divisorCount (by have := facts.divisorTwo; omega)
    huAwFit hvFit
  have hawEq : normalizedWords aw fp dividendPtr m divisorCount divisorPtr =
      newWordArrayWords uAw (vFp fp m divisorCount) divisorCount := by
    unfold normalizedWords MultiLimbSchoolbookNormalization.vWords
    rw [hsetupAw]
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hindex : divisorCount - 1 + 1 = divisorCount := by
    have := facts.divisorTwo
    omega
  have hwordFit : divisorPtr + 32 * ((divisorCount - 1) + 1) < UInt256.size :=
    lt_trans (by
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : divisorPtr + 32 * ((divisorCount - 1) + 1) < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hread := vMemory_read_below facts hmPos hmDividend hquotientBound
    (ptr := divisorPtr + 32 * ((divisorCount - 1) + 1)) (by
      have := facts.divisorPtr96
      omega) (by
        have := facts.divisorEndBeforeDividend
        have := facts.dividendEndBeforeRemainder
        have := facts.remainderEndBeforeFp
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega)
  have hword : MultiLimbSchoolbookNormalization.arrayWord
      (vMemory mem fp dividendPtr m divisorCount)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (divisorCount - 1) =
    MultiLimbSchoolbookNormalization.arrayWord
      (setupMemory mem fp dividendPtr m divisorCount)
      (setupWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (divisorCount - 1) := by
    apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
    · exact hwordFit
    · rw [hvSize, hindex]
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hsetupSize, hindex]
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      unfold uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hawEq, hindex]
      exact le_trans (by
        have := facts.divisorEndBeforeDividend
        have := facts.dividendEndBeforeRemainder
        have := facts.remainderEndBeforeFp
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega) hvRange.1
    · rw [hsetupAw]
      change divisorPtr + 32 * ((divisorCount - 1) + 1) + 32 ≤ 32 * uAw.toNat
      rw [huAwEq, hindex]
      exact le_trans (by
        have := facts.divisorEndBeforeDividend
        have := facts.dividendEndBeforeRemainder
        have := facts.remainderEndBeforeFp
        unfold uFp wordArrayAllocationSize wordArrayPayloadSize
        omega) huRange.1
    · rw [hawEq]
      exact hvRange.2
    · rw [hsetupAw]
      exact huAwFit
    · exact hread
  exact hword.trans (setupTop_eq_setupArrayTop facts hmPos hmDividend
    hquotientBound huBound).symm

/-- The shift returned by the composed setup theorem is exactly `_clz` applied to the concrete
top word named by this module.  Keeping this equality explicit avoids later reasoning about two
definitionally equal, but syntactically different, generated trace models. -/
theorem setupClzResult_eq
    (mem : ByteArray) (aw : UInt256)
    (fp dividendPtr divisorPtr m divisorCount : Nat) :
    MultiLimbSchoolbookKnuthPrefix.clzResultOf mem aw fp (uFp fp m divisorCount)
        dividendPtr m divisorCount (UInt256.ofNat divisorPtr) =
      MultiLimbClz.clzResult
        (setupTop mem aw fp dividendPtr divisorPtr m divisorCount) := by
  rfl

/-- Every shift selected by the deployed `_clz` trace fits the normalization helpers' word-sized
shift precondition. -/
theorem setupClzShift_lt_256
    (mem : ByteArray) (aw : UInt256)
    (fp dividendPtr divisorPtr m divisorCount : Nat) :
    (MultiLimbSchoolbookKnuthPrefix.clzResultOf mem aw fp (uFp fp m divisorCount)
      dividendPtr m divisorCount (UInt256.ofNat divisorPtr)).n < 256 := by
  rw [setupClzResult_eq]
  have := MultiLimbClz.clzResult_n_le
    (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)
  omega

/-- The concrete CLZ input remains nonzero after setup and allocation of `v`. -/
theorem setupTop_ne_zero
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    setupTop mem aw fp dividendPtr divisorPtr m divisorCount ≠ ⟨0⟩ := by
  rw [← vDivisorTop_eq_setupTop facts hmPos hmDividend hquotientBound huBound hvBound]
  have hslice := vOriginalWords_eq facts hmPos hmDividend hquotientBound huBound hvBound
    facts.divisorPtr96 (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega : divisorPtr + 32 + 32 * divisorCount ≤ remPtr)
  have hi : divisorCount - 1 < divisorCount := by
    have := facts.divisorTwo
    omega
  have htop := MultiLimbArrayReadSemantic.arrayWord_eq_of_arrayReadWords_eq
    (vMemory mem fp dividendPtr m divisorCount) mem
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) aw
    (UInt256.ofNat divisorPtr) (UInt256.ofNat divisorPtr)
    0 divisorCount (divisorCount - 1) hi hslice
  simp only [Nat.zero_add] at htop
  exact htop.trans_ne facts.divisorTopNonzero

/-- The top limb produced by the CLZ-selected normalization satisfies Knuth's radix-half bound. -/
theorem normalizedSetupTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    UInt256.size ≤ 2 *
      (MultiLimbClz.normalizedTop
        (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).toNat := by
  have hnonzero := setupTop_ne_zero facts hmPos hmDividend hquotientBound huBound hvBound
  have hlower := MultiLimbClz.normalizedTop_lower
    (x := setupTop mem aw fp dividendPtr divisorPtr m divisorCount) (by
      intro hzero
      exact hnonzero (uint256_toNat_eq_zero hzero))
  norm_num [UInt256.size] at hlower ⊢
  omega

/-- The second allocator covers the complete `m+1`-word `u` payload in its guarded active-word
counter.  This includes the final carry slot even though setup initially copies only `m` words. -/
theorem setupWords_uCoverage
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64) :
    uFp fp m divisorCount + 32 + 32 * (m + 1) ≤
        32 * (setupWords aw fp dividendPtr m divisorCount divisorPtr).toNat ∧
      (setupWords aw fp dividendPtr m divisorCount divisorPtr).toNat * 32 < UInt256.size := by
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by
        omega : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  have hsetupAw := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  rw [hsetupAw]
  change uFp fp m divisorCount + 32 + 32 * (m + 1) ≤
      32 * (MultiLimbSchoolbookKnuthPrefix.uWords aw fp
        (uFp fp m divisorCount) m divisorCount).toNat ∧ _
  simpa only [MultiLimbSchoolbookKnuthPrefix.uWords,
    MultiLimbSchoolbookKnuthSetup.uWords, qAw, hqAwEq] using huRange

/-- Allocation of `v` preserves the complete copied `u[0..m)` observer, whose value is the
selected trimmed dividend from the original memory. -/
theorem vDividendWords_eq
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (vMemory mem fp dividendPtr m divisorCount)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat (uFp fp m divisorCount)) 0 m =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat dividendPtr) 0 m := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hsetupCoverage := setupWords_uCoverage facts hmPos hmDividend hquotientBound huBound
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hvSetup : MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (vMemory mem fp dividendPtr m divisorCount)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) 0 m =
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (setupMemory mem fp dividendPtr m divisorCount)
      (setupWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) 0 m := by
    apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
    intro i hi
    simp only [Nat.zero_add]
    have huPtrFit : uFp fp m divisorCount < UInt256.size :=
      lt_trans (by
        have := huBound
        omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
    have hfit : uFp fp m divisorCount + 32 * (i + 1) < UInt256.size := by
      have hfull := geometry.huFit
      rw [huNat] at hfull
      omega
    have hread := vMemory_read_below facts hmPos hmDividend hquotientBound
      (ptr := uFp fp m divisorCount + 32 * (i + 1)) (by
        unfold uFp
        have := facts.fp96
        omega) (by
          unfold vFp wordArrayAllocationSize wordArrayPayloadSize
          omega)
    apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
    · exact hfit
    · rw [hvSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hsetupSize]
      omega
    · have hactive := geometry.huTopActive
      have hcount := geometry.huCountEq
      rw [huNat] at hactive
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hactive hcount
      omega
    · exact le_trans (by omega) hsetupCoverage.1
    · exact geometry.hawFit
    · exact hsetupCoverage.2
    · exact hread
  exact hvSetup.trans
    (setupDividendWords_eq facts hmPos hmDividend hquotientBound huBound)

/-- The generated fresh-frontier divisor loop computes the original concrete divisor multiplied
by the exact CLZ factor.  In particular, the proof establishes that the discarded carry is zero;
it does not model the normalized divisor by an assumed value. -/
theorem positiveDivisorResult_value
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n) :
    Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat (vFp fp m divisorCount)) 0 divisorCount) =
      Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) * 2 ^ shift := by
  let geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hdivisorFit : divisorPtr + 32 * divisorCount < UInt256.size :=
    lt_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : divisorPtr + 32 * divisorCount < 2 ^ 64)
      (by norm_num [UInt256.size])
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hactive : ∀ j, j < divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) j).toNat + 32 ≤
        32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    intro j hj
    have hfull := geometry.hvActive
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hfull
    omega
  have hsourceMem : ∀ j, j < divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat divisorPtr) j).toNat + 32 ≤
        (vMemory mem fp dividendPtr m divisorCount).size := by
    intro j hj
    rw [arrayAddressNat divisorPtr j (by omega), hvSize]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htop := vDivisorTop_eq_setupTop facts hmPos hmDividend hquotientBound huBound
    hvBound
  have hcountSucc : divisorCount - 1 + 1 = divisorCount := by
    have := facts.divisorTwo
    omega
  have hcarry :
      (MultiLimbSchoolbookNormalization.shiftDivisor
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount)) shift
        0 divisorCount (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩).carry = ⟨0⟩ := by
    rw [hshift]
    have hzero :=
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_clz_finalCarry_eq_zero_frontier
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
        (setupTop mem aw fp dividendPtr divisorPtr m divisorCount) (divisorCount - 1)
        (vMemory mem fp dividendPtr m divisorCount) (by simpa [← hshift] using hshiftPos)
        geometry.hawFit
        (by
          intro j hj
          rw [hcountSucc] at hj
          simpa only [Nat.zero_add] using hfrontier j hj)
        (by
          intro j hj
          rw [hcountSucc] at hj
          simpa only [Nat.zero_add] using hactive j hj)
        (by
          intro j hj
          rw [hcountSucc] at hj
          simpa only [Nat.zero_add] using hsourceMem j hj)
        htop
    simpa only [hcountSucc] using hzero
  have hnormalized :=
    MultiLimbSchoolbookNormalizationSemantic.normalizedDivisorArray_toNat_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount)) shift
      divisorCount (vMemory mem fp dividendPtr m divisorCount) hshiftPos
      (by
        rw [hshift]
        exact setupClzShift_lt_256 mem aw fp dividendPtr divisorPtr m divisorCount)
      geometry.hawFit hfrontier hactive hsourceMem hcarry
  have hsource := vOriginalWords_eq facts hmPos hmDividend hquotientBound huBound hvBound
    facts.divisorPtr96 (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega : divisorPtr + 32 + 32 * divisorCount ≤ remPtr)
  simpa only [positiveDivisorResult,
    MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using
    hnormalized.trans (congrArg (fun value => value * 2 ^ shift)
      (congrArg Modexp.wordLimbsToNat hsource))

/-- The generated in-place `u` loop and its explicit final carry store compute the selected
trimmed dividend multiplied by the same exact CLZ factor. -/
theorem positiveDividend_value
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n) :
    Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat (uFp fp m divisorCount)) 0 (m + 1)) =
      Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat dividendPtr) 0 m) * 2 ^ shift := by
  let geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  let u := UInt256.ofNat (uFp fp m divisorCount)
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let divisorResult := positiveDivisorResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hvActive : ∀ j, j < divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat + 32 ≤
        32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    have hfull := geometry.hvActive
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hfull
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) v shift 0 divisorCount
      (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hfrontier)
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have huReadMem : ∀ i, i < m + 1 →
      (MultiLimbSchoolbookNormalization.arrayAddress u i).toNat + 32 ≤
        (vMemory mem fp dividendPtr m divisorCount).size := by
    intro i hi
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) i (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega), hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huPreserved :
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords divisorResult.memory
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u 0 m =
        MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (vMemory mem fp dividendPtr m divisorCount)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u 0 m := by
    apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
    intro i hi
    simpa only [Nat.zero_add, divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_preserves_arrayWord_below_frontier
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u
        (UInt256.ofNat divisorPtr) v shift i 0 divisorCount
        (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩ geometry.hawFit
        (by simpa only [Nat.zero_add] using hfrontier)
        (by simpa only [Nat.zero_add] using hvActive)
        (huReadMem i (by omega))
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize]
    exact le_trans (huReadMem j (by omega)) (by omega)
  have huActive : ∀ j, j < m + 1 →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    have hfull := geometry.huTopActive
    have hcount := geometry.huCountEq
    have huPtrFit : uFp fp m divisorCount < UInt256.size := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega
    rw [UInt256.toNat_ofNat_of_lt huPtrFit] at hfull
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hfull hcount
    omega
  have huOrdered : ∀ i j, i < j → j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u i).toNat + 32 ≤
        (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat := by
    intro i j hij hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) i (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega),
      arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega)]
    omega
  have htopWrite :
      let result := MultiLimbSchoolbookNormalization.shiftDivisor
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u u shift
        0 m divisorResult.memory ⟨0⟩
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
        result.memory.size := by
    dsimp only
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u u shift 0 m
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    rw [hsize, hdivisorResultSize]
    exact le_trans (huReadMem m (by omega)) (by omega)
  have htopOrdered : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega),
      arrayAddressNat (uFp fp m divisorCount) m (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega)]
    omega
  have hnormalized :=
    MultiLimbSchoolbookNormalizationSemantic.normalizedDividendArray_toNat
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u shift m
      divisorResult.memory hshiftPos
      (by
        rw [hshift]
        exact setupClzShift_lt_256 mem aw fp dividendPtr divisorPtr m divisorCount)
      geometry.hawFit (by simpa only [Nat.zero_add] using huWrite)
      (by
        intro j hj
        exact huActive j (by omega))
      huOrdered htopWrite (huActive m (by omega)) htopOrdered
  have hbase := vDividendWords_eq facts hmPos hmDividend hknuth hquotientBound huBound
    hvBound
  rw [huPreserved] at hnormalized
  simpa only [positiveMemory,
    MultiLimbSchoolbookNormalizationFunction.positiveMemory,
    MultiLimbSchoolbookNormalizationFunction.positiveDividendResult,
    positiveDividendResult, divisorResult, positiveDivisorResult,
    MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, u, v] using
    hnormalized.trans (congrArg (fun value => value * 2 ^ shift)
      (congrArg Modexp.wordLimbsToNat hbase))

/-- The later in-place dividend shift and final carry store are below `v`, so the final positive
normalization memory retains the exact shifted divisor computed at the frontier. -/
theorem positiveDivisor_final_value
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n) :
    Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat (vFp fp m divisorCount)) 0 divisorCount) =
      Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) * 2 ^ shift := by
  let geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  let u := UInt256.ofNat (uFp fp m divisorCount)
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let divisorResult := positiveDivisorResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  let dividendResult := positiveDividendResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  have hdivisor := positiveDivisorResult_value facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound hshiftPos hshift
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) v shift 0 divisorCount
      (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hfrontier)
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have huReadMem : ∀ i, i < m + 1 →
      (MultiLimbSchoolbookNormalization.arrayAddress u i).toNat + 32 ≤
        (vMemory mem fp dividendPtr m divisorCount).size := by
    intro i hi
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) i (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega), hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize]
    exact le_trans (huReadMem j (by omega)) (by omega)
  have huBelowV : ∀ i j, i < divisorCount → j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        (MultiLimbSchoolbookNormalization.arrayAddress v i).toNat := by
    intro i j hi hj
    dsimp only [u, v]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega),
      arrayAddressNat (vFp fp m divisorCount) i (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
        omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hshiftPreserved :
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords dividendResult.memory
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 divisorCount =
        MultiLimbSchoolbookNormalizationSemantic.arrayReadWords divisorResult.memory
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 divisorCount := by
    apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
    intro i hi
    simpa only [Nat.zero_add, dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult] using
      MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_preserves_arrayWord_above
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v u u shift
        i 0 m divisorResult.memory ⟨0⟩
        (by
          intro j hj
          simpa only [Nat.zero_add] using huWrite j hj)
        (by
          intro j hj
          simpa only [Nat.zero_add] using huBelowV i j hi hj)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u u shift 0 m
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult] using hsize
  have htopWrite : (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize]
    exact le_trans (huReadMem m (by omega)) (by omega)
  have htopBelowV : ∀ i, i < divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
        (MultiLimbSchoolbookNormalization.arrayAddress v i).toNat := by
    intro i hi
    dsimp only [u, v]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega),
      arrayAddressNat (vFp fp m divisorCount) i (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
        omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopPreserved :
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u m
            dividendResult.carry)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 divisorCount =
        MultiLimbSchoolbookNormalizationSemantic.arrayReadWords dividendResult.memory
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 divisorCount := by
    simpa only [MultiLimbSchoolbookNormalization.storeDividendTopCarry, Nat.zero_add] using
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_storeValue_above
        dividendResult.memory
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v u
        dividendResult.carry 0 divisorCount m htopWrite (by
          intro i hi
          simpa only [Nat.zero_add] using htopBelowV i hi)
  change Modexp.wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u m
          dividendResult.carry)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 divisorCount) = _
  rw [htopPreserved, hshiftPreserved]
  simpa only [divisorResult, v, positiveDivisorResult] using hdivisor

/-- The original concrete divisor top word is the exact word supplied to `_clz`. -/
theorem originalDivisorTop_eq_setupTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayWord mem aw (UInt256.ofNat divisorPtr)
        (divisorCount - 1) =
      setupTop mem aw fp dividendPtr divisorPtr m divisorCount := by
  have hslice := vOriginalWords_eq facts hmPos hmDividend hquotientBound huBound hvBound
    facts.divisorPtr96 (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega : divisorPtr + 32 + 32 * divisorCount ≤ remPtr)
  have hi : divisorCount - 1 < divisorCount := by
    have := facts.divisorTwo
    omega
  have hword := MultiLimbArrayReadSemantic.arrayWord_eq_of_arrayReadWords_eq
    (vMemory mem fp dividendPtr m divisorCount) mem
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) aw
    (UInt256.ofNat divisorPtr) (UInt256.ofNat divisorPtr)
    0 divisorCount (divisorCount - 1) hi hslice
  simp only [Nat.zero_add] at hword
  exact hword.symm.trans
    (vDivisorTop_eq_setupTop facts hmPos hmDividend hquotientBound huBound hvBound)

/-- The final positive-normalization top limb satisfies the half-radix premise consumed by the
generated q-hat loop.  This follows from the exact scaled source and final computations. -/
theorem positiveMemory_normalizedTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n) :
    UInt256.size ≤ 2 *
      (MultiLimbSchoolbookNormalization.arrayWord
        (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat (vFp fp m divisorCount)) (divisorCount - 1)).toNat := by
  let top := setupTop mem aw fp dividendPtr divisorPtr m divisorCount
  let modulusNat := Modexp.wordLimbsToNat
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw (UInt256.ofNat divisorPtr) 0 divisorCount)
  let sourceLow := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
    mem aw (UInt256.ofNat divisorPtr) 0 (divisorCount - 1)
  have htop := originalDivisorTop_eq_setupTop facts hmPos hmDividend hquotientBound
    huBound hvBound
  have hsourceSplit :
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat divisorPtr) 0 divisorCount =
        sourceLow ++ [top] := by
    have hsplit := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_succ_append
      mem aw (UInt256.ofNat divisorPtr) 0 (divisorCount - 1)
    have hcount : divisorCount - 1 + 1 = divisorCount := by
      have := facts.divisorTwo
      omega
    rw [hcount] at hsplit
    simpa only [Nat.zero_add, htop, sourceLow, top] using hsplit
  have hsourceTopBound : UInt256.size ^ (divisorCount - 1) * top.toNat ≤ modulusNat := by
    dsimp only [modulusNat]
    rw [hsourceSplit, Modexp.wordLimbsToNat_append,
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length]
    simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
    omega
  have htopNe : top.toNat ≠ 0 := by
    intro hzero
    exact setupTop_ne_zero facts hmPos hmDividend hquotientBound huBound hvBound
      (uint256_toNat_eq_zero hzero)
  have hnormalizedSource : 2 ^ 255 ≤ top.toNat * 2 ^ shift := by
    rw [hshift, ← MultiLimbClz.normalizedTop_relation top]
    exact MultiLimbClz.normalizedTop_lower htopNe
  have hscaledTop : UInt256.size ^ (divisorCount - 1) * 2 ^ 255 ≤
      modulusNat * 2 ^ shift := by
    calc
      UInt256.size ^ (divisorCount - 1) * 2 ^ 255 ≤
          UInt256.size ^ (divisorCount - 1) * (top.toNat * 2 ^ shift) :=
        Nat.mul_le_mul_left _ hnormalizedSource
      _ = (UInt256.size ^ (divisorCount - 1) * top.toNat) * 2 ^ shift := by ring
      _ ≤ modulusNat * 2 ^ shift := Nat.mul_le_mul_right _ hsourceTopBound
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let finalLow := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
    (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 (divisorCount - 1)
  let finalTop := MultiLimbSchoolbookNormalization.arrayWord
    (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v (divisorCount - 1)
  have hfinalSplit :
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0 divisorCount =
        finalLow ++ [finalTop] := by
    have hsplit := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_succ_append
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) v 0
      (divisorCount - 1)
    have hcount : divisorCount - 1 + 1 = divisorCount := by
      have := facts.divisorTwo
      omega
    rw [hcount] at hsplit
    simpa only [Nat.zero_add, finalLow, finalTop] using hsplit
  have hfinalValue := positiveDivisor_final_value facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound hshiftPos hshift
  have hfinalBound : UInt256.size ^ finalLow.length * 2 ^ 255 ≤
      Modexp.wordLimbsToNat (finalLow ++ [finalTop]) := by
    rw [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length]
    rw [← hfinalSplit]
    simpa only [modulusNat, v] using hscaledTop.trans_eq hfinalValue.symm
  have htopLower : 2 ^ 255 ≤ finalTop.toNat :=
    MultiLimbBarrettContinuationExecutable.top_toNat_ge_of_wordLimbsToNat_ge
      finalLow finalTop (2 ^ 255) hfinalBound
  change UInt256.size ≤ 2 * finalTop.toNat
  norm_num [UInt256.size] at htopLower ⊢
  omega

/-- Positive normalization fills the fresh `v` payload and performs every later `u` write in
bounds, so the final byte extent is exactly the end of `v`. -/
theorem positiveMemory_size
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).size =
      vFp fp m divisorCount + 32 + 32 * divisorCount := by
  let u := UInt256.ofNat (uFp fp m divisorCount)
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let divisorResult := positiveDivisorResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  let dividendResult := positiveDividendResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) v shift 0 divisorCount
      (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hfrontier)
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have huReadMem : ∀ i, i < m + 1 →
      (MultiLimbSchoolbookNormalization.arrayAddress u i).toNat + 32 ≤
        (vMemory mem fp dividendPtr m divisorCount).size := by
    intro i hi
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) i (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega), hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        divisorResult.memory.size := by
    intro j hj
    rw [hdivisorResultSize]
    exact le_trans (huReadMem j (by omega)) (by omega)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) u u shift 0 m
      divisorResult.memory ⟨0⟩ (by simpa only [Nat.zero_add] using huWrite)
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult] using hsize
  have htopWrite : (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize]
    exact le_trans (huReadMem m (by omega)) (by omega)
  change (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u m
    dividendResult.carry).size = _
  have hstoreSize :
      (MultiLimbSchoolbookNormalization.storeDividendTopCarry dividendResult.memory u m
        dividendResult.carry).size = dividendResult.memory.size := by
    simpa only [MultiLimbSchoolbookNormalization.storeDividendTopCarry,
      MultiLimbSchoolbookSingle.storeQuotient,
      MultiLimbSchoolbookNormalization.arrayAddress] using
      MultiLimbSchoolbookSingle.storeQuotient_size_eq dividendResult.memory u m
        dividendResult.carry htopWrite
  rw [hstoreSize, hdividendResultSize, hdivisorResultSize, hvSize]

/-- Positive normalization writes only into the fresh `u` and `v` workspaces, so every complete
word below the quotient allocation retains its post-`v`-allocation value. -/
theorem positiveMemory_read_below_vMemory
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift read : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hreadEnd : read + 32 ≤ fp) :
    (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
        read 32 = (vMemory mem fp dividendPtr m divisorCount).readWithPadding read 32 := by
  let stateAw := normalizedWords aw fp dividendPtr m divisorCount divisorPtr
  let u := UInt256.ofNat (uFp fp m divisorCount)
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let divisorResult := positiveDivisorResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  let dividendResult := positiveDividendResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hbase32 : 32 ≤ (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.fp96
    unfold vFp uFp
    omega
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount
      (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hfrontier)
    simpa only [stateAw, divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have hreadBelowV0 : read + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hreadDivisor : divisorResult.memory.readWithPadding read 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding read 32 := by
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, stateAw, v,
      Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount read
        (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hfrontier) hreadBelowV0
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        divisorResult.memory.size := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega), hdivisorResultSize, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hreadBelowU : ∀ j, j < m → read + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize]
    omega
  have hreadDividend : dividendResult.memory.readWithPadding read 32 =
      divisorResult.memory.readWithPadding read 32 := by
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult, stateAw, u, Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_inBounds
        stateAw u u shift 0 m read divisorResult.memory ⟨0⟩ hdivisor32
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using hreadBelowU)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      stateAw u u shift 0 m divisorResult.memory ⟨0⟩
      (by simpa only [Nat.zero_add] using huWrite)
    simpa only [stateAw, dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult] using hsize
  have htopWrite : (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hreadBelowTop : read + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat := by
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hfinal32 : 32 ≤ dividendResult.memory.size := by
    rw [hdividendResultSize]
    exact hdivisor32
  have hreadTop :
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
          read 32 = dividendResult.memory.readWithPadding read 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat 32).readWithPadding
        read 32 = _
    exact toByteArray_write_read_below_padded_of_gap dividendResult.carry
      dividendResult.memory (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat
      read hfinal32 hreadBelowTop (by
        have husize : 0 < USize.size := by native_decide
        have := htopWrite
        omega)
  exact hreadTop.trans (hreadDividend.trans hreadDivisor)

/-- Every complete pre-existing word above Solidity's reserved prefix and below the quotient
allocation remains unchanged through positive normalization. -/
theorem positiveMemory_read_below
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift read : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hread96 : 96 ≤ read) (hreadEnd : read + 32 ≤ fp) :
    (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
        read 32 = mem.readWithPadding read 32 := by
  exact (positiveMemory_read_below_vMemory facts hmPos hmDividend hquotientBound huBound
    hvBound hreadEnd).trans
      ((vMemory_read_below facts hmPos hmDividend hquotientBound hread96 (by
          unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
          omega)).trans
        (setupMemory_read_below facts hmPos hmDividend hread96 hreadEnd))

/-- All three allocator headers survive the complete positive normalization computation. -/
theorem positiveMemory_headers
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayHeader
        (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat fp) = UInt256.ofNat (numQ m divisorCount) ∧
      MultiLimbSchoolbookNormalization.arrayHeader
          (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat (uFp fp m divisorCount)) = UInt256.ofNat (m + 1) ∧
        MultiLimbSchoolbookNormalization.arrayHeader
          (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat (vFp fp m divisorCount)) = UInt256.ofNat divisorCount := by
  let stateAw := normalizedWords aw fp dividendPtr m divisorCount divisorPtr
  let q := UInt256.ofNat fp
  let u := UInt256.ofNat (uFp fp m divisorCount)
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let divisorResult := positiveDivisorResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  let dividendResult := positiveDividendResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hfinalSize := positiveMemory_size facts hmPos hmDividend hquotientBound huBound
    hvBound (shift := shift)
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqPtrFit : fp < UInt256.size := lt_trans (by
    have := hquotientBound
    omega : fp < 2 ^ 64) (by norm_num [UInt256.size])
  have huPtrFit : uFp fp m divisorCount < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have hvPtrFit : vFp fp m divisorCount < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hvNat := UInt256.toNat_ofNat_of_lt hvPtrFit
  have hbase32 : 32 ≤ (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.fp96
    unfold vFp uFp
    omega
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsetupGap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  have hsetupReads := setupMemory_newHeaderReads facts hmPos hmDividend
  have hqInitialRead : (vMemory mem fp dividendPtr m divisorCount).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (numQ m divisorCount)) :=
    (vMemory_read_below facts hmPos hmDividend hquotientBound facts.fp96 (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega)).trans hsetupReads.1
  have huInitialRead : (vMemory mem fp dividendPtr m divisorCount).readWithPadding
      (uFp fp m divisorCount) 32 = UInt256.toByteArray (UInt256.ofNat (m + 1)) :=
    (vMemory_read_below facts hmPos hmDividend hquotientBound (by
      unfold uFp
      have := facts.fp96
      omega) (by
        unfold vFp wordArrayAllocationSize wordArrayPayloadSize
        omega)).trans hsetupReads.2
  have hvInitialRead : (vMemory mem fp dividendPtr m divisorCount).readWithPadding
      (vFp fp m divisorCount) 32 = UInt256.toByteArray (UInt256.ofNat divisorCount) := by
    unfold vMemory MultiLimbSchoolbookNormalization.vMemory
    apply storeBytesLength_read_self
    rw [setFreePtr_size hsetup96]
    exact hsetupGap
  have initialHeaders :
      MultiLimbSchoolbookNormalization.arrayHeader
          (vMemory mem fp dividendPtr m divisorCount) stateAw q =
            UInt256.ofNat (numQ m divisorCount) ∧
        MultiLimbSchoolbookNormalization.arrayHeader
            (vMemory mem fp dividendPtr m divisorCount) stateAw u =
              UInt256.ofNat (m + 1) ∧
          MultiLimbSchoolbookNormalization.arrayHeader
            (vMemory mem fp dividendPtr m divisorCount) stateAw v =
              UInt256.ofNat divisorCount := by
    have hactive : vFp fp m divisorCount + 32 * (divisorCount + 1) ≤
        32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
      simpa only [UInt256.toNat_ofNat_of_lt hvPtrFit] using geometry.hvActive
    constructor
    · apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_read
      · rw [hqNat, hvSize]
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      · rw [hqNat]
        change fp + 32 ≤ 32 *
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat
        exact le_trans (by
          unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
          omega) hactive
      · exact geometry.hawFit
      · simpa only [q, hqNat] using hqInitialRead
    constructor
    · apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_read
      · rw [huNat, hvSize]
        unfold vFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      · rw [huNat]
        change uFp fp m divisorCount + 32 ≤ 32 *
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat
        exact le_trans (by
          unfold vFp wordArrayAllocationSize wordArrayPayloadSize
          omega) hactive
      · exact geometry.hawFit
      · simpa only [u, huNat] using huInitialRead
    · apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_read
      · rw [hvNat, hvSize]
      · rw [hvNat]
        change vFp fp m divisorCount + 32 ≤ 32 *
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat
        exact le_trans (by omega) hactive
      · exact geometry.hawFit
      · simpa only [v, hvNat] using hvInitialRead
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount
      (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hfrontier)
    simpa only [stateAw, divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have hqBelowV0 : fp + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huBelowV0 : uFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hvBelowV0 : vFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
  have hqDivisorRead : divisorResult.memory.readWithPadding fp 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding fp 32 := by
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, stateAw, v,
      Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount fp
        (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hfrontier) hqBelowV0
  have huDivisorRead : divisorResult.memory.readWithPadding (uFp fp m divisorCount) 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding
        (uFp fp m divisorCount) 32 := by
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, stateAw, v,
      Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount
        (uFp fp m divisorCount) (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
        hbase32 (by simpa only [Nat.zero_add] using hfrontier) huBelowV0
  have hvDivisorRead : divisorResult.memory.readWithPadding (vFp fp m divisorCount) 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding
        (vFp fp m divisorCount) 32 := by
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, stateAw, v,
      Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount
        (vFp fp m divisorCount) (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
        hbase32 (by simpa only [Nat.zero_add] using hfrontier) hvBelowV0
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        divisorResult.memory.size := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega), hdivisorResultSize, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqBelowU : ∀ j, j < m → fp + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huBelowU : ∀ j, j < m → uFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    omega
  have huBelowV : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        vFp fp m divisorCount := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize]
    omega
  have hqDividendRead : dividendResult.memory.readWithPadding fp 32 =
      divisorResult.memory.readWithPadding fp 32 := by
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult, stateAw, u, Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_inBounds
        stateAw u u shift 0 m fp divisorResult.memory ⟨0⟩ hdivisor32
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using hqBelowU)
  have huDividendRead : dividendResult.memory.readWithPadding (uFp fp m divisorCount) 32 =
      divisorResult.memory.readWithPadding (uFp fp m divisorCount) 32 := by
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult, stateAw, u, Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_inBounds
        stateAw u u shift 0 m (uFp fp m divisorCount) divisorResult.memory ⟨0⟩
        hdivisor32 (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using huBelowU)
  have hvDividendRead : dividendResult.memory.readWithPadding (vFp fp m divisorCount) 32 =
      divisorResult.memory.readWithPadding (vFp fp m divisorCount) 32 := by
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult, stateAw, u, Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_above_inBounds
        stateAw u u shift 0 m (vFp fp m divisorCount) divisorResult.memory ⟨0⟩
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using huBelowV)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      stateAw u u shift 0 m divisorResult.memory ⟨0⟩
      (by simpa only [Nat.zero_add] using huWrite)
    simpa only [stateAw, dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult] using hsize
  have htopWrite : (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopQBelow : fp + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat := by
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have htopUBelow : uFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat := by
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    omega
  have htopBelowV :
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
        vFp fp m divisorCount := by
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hfinal32 : 32 ≤ dividendResult.memory.size := by
    rw [hdividendResultSize]
    exact hdivisor32
  have hqTopRead :
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
          fp 32 = dividendResult.memory.readWithPadding fp 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat 32).readWithPadding fp 32 = _
    exact toByteArray_write_read_below_padded_of_gap dividendResult.carry
      dividendResult.memory (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat fp
      hfinal32 htopQBelow (by
        have husize : 0 < USize.size := by native_decide
        have := htopWrite
        omega)
  have huTopRead :
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
          (uFp fp m divisorCount) 32 =
        dividendResult.memory.readWithPadding (uFp fp m divisorCount) 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat 32).readWithPadding
        (uFp fp m divisorCount) 32 = _
    exact toByteArray_write_read_below_padded_of_gap dividendResult.carry
      dividendResult.memory (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat
      (uFp fp m divisorCount) hfinal32 htopUBelow
      (by
        have husize : 0 < USize.size := by native_decide
        have := htopWrite
        omega)
  have hvTopRead :
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
          (vFp fp m divisorCount) 32 =
        dividendResult.memory.readWithPadding (vFp fp m divisorCount) 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat 32).readWithPadding
        (vFp fp m divisorCount) 32 = _
    exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size]) htopWrite htopBelowV
  have hqDivHeader : MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory
      stateAw q = MultiLimbSchoolbookNormalization.arrayHeader
        (vMemory mem fp dividendPtr m divisorCount) stateAw q := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hqNat, hvSize]
      omega
    · rw [hdivisorResultSize]
      omega
    · simpa only [q, hqNat] using hqDivisorRead
  have huDivHeader : MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory
      stateAw u = MultiLimbSchoolbookNormalization.arrayHeader
        (vMemory mem fp dividendPtr m divisorCount) stateAw u := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [huNat, hvSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hdivisorResultSize]
      omega
    · simpa only [u, huNat] using huDivisorRead
  have hvDivHeader : MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory
      stateAw v = MultiLimbSchoolbookNormalization.arrayHeader
        (vMemory mem fp dividendPtr m divisorCount) stateAw v := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hvNat, hvSize]
      omega
    · rw [hdivisorResultSize]
      omega
    · simpa only [v, hvNat] using hvDivisorRead
  have hqDividendHeader : MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory
      stateAw q = MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory stateAw q := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hqNat, hdivisorResultSize, hvSize]
      omega
    · rw [hdividendResultSize]
    · simpa only [q, hqNat] using hqDividendRead
  have huDividendHeader : MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory
      stateAw u = MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory stateAw u := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [huNat, hdivisorResultSize, hvSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hdividendResultSize]
    · simpa only [u, huNat] using huDividendRead
  have hvDividendHeader : MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory
      stateAw v = MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory stateAw v := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hvNat, hdivisorResultSize, hvSize]
      omega
    · rw [hdividendResultSize]
    · simpa only [v, hvNat] using hvDividendRead
  have hqFinalHeader : MultiLimbSchoolbookNormalization.arrayHeader
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift) stateAw q =
        MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory stateAw q := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hqNat, hdividendResultSize, hdivisorResultSize, hvSize]
      omega
    · rw [hfinalSize, hdividendResultSize, hdivisorResultSize, hvSize]
    · simpa only [q, hqNat] using hqTopRead
  have huFinalHeader : MultiLimbSchoolbookNormalization.arrayHeader
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift) stateAw u =
        MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory stateAw u := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [huNat, hdividendResultSize, hdivisorResultSize, hvSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hfinalSize, hdividendResultSize, hdivisorResultSize, hvSize]
    · simpa only [u, huNat] using huTopRead
  have hvFinalHeader : MultiLimbSchoolbookNormalization.arrayHeader
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift) stateAw v =
        MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory stateAw v := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hvNat, hdividendResultSize, hdivisorResultSize, hvSize]
      omega
    · rw [hfinalSize, hdividendResultSize, hdivisorResultSize, hvSize]
    · simpa only [v, hvNat] using hvTopRead
  exact ⟨hqFinalHeader.trans (hqDividendHeader.trans (hqDivHeader.trans initialHeaders.1)),
    huFinalHeader.trans (huDividendHeader.trans (huDivHeader.trans initialHeaders.2.1)),
    hvFinalHeader.trans (hvDividendHeader.trans
      (hvDivHeader.trans initialHeaders.2.2))⟩

/-- Concrete positive normalization constructs the complete exposed quotient selector.  The
initial-window premise is derived from the original finite arrays and both exact scaled-value
equations; no quotient digit or correction branch is assumed. -/
theorem positiveSelection_exists
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n) :
    Nonempty (MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat shift) ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨1⟩
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)) := by
  let geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hheaders := positiveMemory_headers facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound (shift := shift)
  have hnormalized := positiveMemory_normalizedTop facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound hshiftPos hshift
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvPtrFit : vFp fp m divisorCount < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
    omega
  have hvMem : (UInt256.ofNat (vFp fp m divisorCount)).toNat +
      32 * (divisorCount + 1) ≤
        (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).size := by
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit,
      positiveMemory_size facts hmPos hmDividend hquotientBound huBound hvBound]
    omega
  have hdividendValue := positiveDividend_value facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound hshiftPos hshift
  have hdivisorValue := positiveDivisor_final_value facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound hshiftPos hshift
  let dividendNat := Modexp.wordLimbsToNat
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw (UInt256.ofNat dividendPtr) 0 m)
  let divisorNat := Modexp.wordLimbsToNat
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw (UInt256.ofNat divisorPtr) 0 divisorCount)
  have hdividendBound : dividendNat < UInt256.size ^ m := by
    have hbound := Modexp.wordLimbsToNat_lt_pow
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat dividendPtr) 0 m)
    rw [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length] at hbound
    exact hbound
  have hdivisorLower : UInt256.size ^ (divisorCount - 1) ≤ divisorNat := by
    exact arrayValueLowerOfTopNonzero mem aw (UInt256.ofNat divisorPtr)
      (MultiLimbSchoolbookNormalization.arrayWord mem aw (UInt256.ofNat divisorPtr)
        (divisorCount - 1)) divisorCount (by
          have := facts.divisorTwo
          omega) rfl facts.divisorTopNonzero
  have hfullMath := normalizedFullBound m divisorCount shift dividendNat divisorNat
    (by have := facts.divisorTwo; omega) hknuth hdividendBound hdivisorLower
  have hfull : Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat (uFp fp m divisorCount)) 0
          (numQ m divisorCount + divisorCount)) <
      UInt256.size ^ (numQ m divisorCount - 1) *
        (UInt256.size * Modexp.wordLimbsToNat
          (MultiLimbSchoolbookIterationSemantic.divisorReadSlice
            (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
            (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
            (UInt256.ofNat (vFp fp m divisorCount)) 0 divisorCount)) := by
    have hlength : numQ m divisorCount + divisorCount = m + 1 := by
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
      omega
    rw [hlength, hdividendValue,
      MultiLimbSchoolbookCompleteSemantic.divisorReadSlice_eq_arrayReadWords,
      hdivisorValue]
    exact hfullMath
  have hbound :=
    MultiLimbBarrettContinuationExecutable.initialWindow_lt_radix_mul_of_full_bound
      geometry hfull
  exact MultiLimbBarrettReduceBaseExecutable.knuthSelection_exists_of_memory
    geometry hheaders.2.1 hheaders.2.2 hheaders.1 hnormalized hvMem hbound

/-- Every array header and active-word accessor after the fresh normalized-divisor allocation. -/
structure VLayouts
    (mem : ByteArray) (aw : UInt256)
    (fp uPtr vPtr divisorPtr remPtr quotientCount m divisorCount : Nat) : Prop where
  quotient : MultiLimbArrayReadSemantic.Layout mem aw fp quotientCount
  dividend : MultiLimbArrayReadSemantic.Layout mem aw uPtr (m + 1)
  divisor : MultiLimbArrayReadSemantic.Layout mem aw divisorPtr divisorCount
  remainder : MultiLimbArrayReadSemantic.Layout mem aw remPtr divisorCount
  normalizedDivisor : MultiLimbArrayReadSemantic.Layout mem aw vPtr divisorCount

/-- Construct the complete guarded layout immediately after the real `v` allocation. -/
theorem vLayouts
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    VLayouts (vMemory mem fp dividendPtr m divisorCount)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      fp (uFp fp m divisorCount) (vFp fp m divisorCount) divisorPtr remPtr
      (numQ m divisorCount) m divisorCount := by
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hgap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  have hsetupAw := setupWords_eq_uWords facts hmPos hmDividend hquotientBound huBound
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have huAwFit : uAw.toNat * 32 < UInt256.size := by rw [huAwEq]; exact huRange.2
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvRange := MultiLimbOddConversionSemantic.newWordArrayWords_range uAw
    (vFp fp m divisorCount) divisorCount (by have := facts.divisorTwo; omega)
    huAwFit hvFit
  have hawEq : normalizedWords aw fp dividendPtr m divisorCount divisorPtr =
      newWordArrayWords uAw (vFp fp m divisorCount) divisorCount := by
    unfold normalizedWords MultiLimbSchoolbookNormalization.vWords
    rw [hsetupAw]
  have hactive : vFp fp m divisorCount + 32 + 32 * divisorCount ≤
      32 * (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    rw [hawEq]
    exact hvRange.1
  have hawFit :
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr).toNat * 32 <
        UInt256.size := by rw [hawEq]; exact hvRange.2
  have preserve : ∀ ptr,
      96 ≤ ptr → ptr + 32 ≤ vFp fp m divisorCount →
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 =
        (setupMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 := by
    intro ptr hptr96 hptr
    simpa only [vMemory, MultiLimbSchoolbookNormalization.vMemory] using
      MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below
        (setupMemory mem fp dividendPtr m divisorCount) (vFp fp m divisorCount)
        divisorCount ptr hsetup96 hgap hptr96 hptr
  have hvHeaderRead : (vMemory mem fp dividendPtr m divisorCount).readWithPadding
      (vFp fp m divisorCount) 32 = UInt256.toByteArray (UInt256.ofNat divisorCount) := by
    unfold vMemory MultiLimbSchoolbookNormalization.vMemory
    apply storeBytesLength_read_self
    rw [setFreePtr_size hsetup96]
    exact hgap
  have build : ∀ ptr count,
      96 ≤ ptr → ptr + 32 ≤ (vMemory mem fp dividendPtr m divisorCount).size →
      ptr + 32 + 32 * count ≤ vFp fp m divisorCount + 32 + 32 * divisorCount →
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding ptr 32 =
        UInt256.toByteArray (UInt256.ofNat count) →
      MultiLimbArrayReadSemantic.Layout
        (vMemory mem fp dividendPtr m divisorCount)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) ptr count := by
    intro ptr count hptr96 hmem hbefore hread
    apply MultiLimbArrayReadSemantic.layout_of_geometry
    · exact lt_trans (by
        have := hvBound
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvBound
        omega : ptr + 32 * (count + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])
    · exact hmem
    · exact le_trans (by omega) hactive
    · exact hawFit
    · exact hread
  have hfp96 := facts.fp96
  have hu96 : 96 ≤ uFp fp m divisorCount := by unfold uFp; omega
  have hv96 : 96 ≤ vFp fp m divisorCount := by unfold vFp uFp; omega
  have hdivisor96 := facts.divisorPtr96
  have hrem96 : 96 ≤ remPtr := by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    omega
  have hqBeforeV : fp + 32 ≤ vFp fp m divisorCount := by
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huBeforeV : uFp fp m divisorCount + 32 ≤ vFp fp m divisorCount := by
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqRead := preserve fp hfp96 hqBeforeV
  have huRead := preserve (uFp fp m divisorCount) hu96 huBeforeV
  have hdivisorRead := preserve divisorPtr hdivisor96 (by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp
    omega)
  have hremRead := preserve remPtr hrem96 (by
    have := facts.remainderEndBeforeFp
    unfold vFp uFp
    omega)
  have hnewHeaders := setupMemory_newHeaderReads facts hmPos hmDividend
  have hdivisorHeader := (setupMemory_read_below facts hmPos hmDividend
    facts.divisorPtr96 (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      omega)).trans facts.divisorHeaderRead
  have hremHeader := (setupMemory_read_below facts hmPos hmDividend hrem96 (by
    have := facts.remainderEndBeforeFp
    omega)).trans facts.remainderHeaderRead
  have hqMem : fp + 32 ≤ (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    exact le_trans hqBeforeV (by omega)
  have hqActiveEnd : fp + 32 + 32 * numQ m divisorCount ≤
      vFp fp m divisorCount + 32 + 32 * divisorCount := by
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huMem : uFp fp m divisorCount + 32 ≤
      (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    exact le_trans huBeforeV (by omega)
  have huActiveEnd : uFp fp m divisorCount + 32 + 32 * (m + 1) ≤
      vFp fp m divisorCount + 32 + 32 * divisorCount := by
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisorMem : divisorPtr + 32 ≤
      (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisorActiveEnd : divisorPtr + 32 + 32 * divisorCount ≤
      vFp fp m divisorCount + 32 + 32 * divisorCount := by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremMem : remPtr + 32 ≤ (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremActiveEnd : remPtr + 32 + 32 * divisorCount ≤
      vFp fp m divisorCount + 32 + 32 * divisorCount := by
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  refine {
    quotient := build fp (numQ m divisorCount) hfp96 hqMem hqActiveEnd
      (hqRead.trans hnewHeaders.1)
    dividend := build (uFp fp m divisorCount) (m + 1) hu96
      huMem huActiveEnd (huRead.trans hnewHeaders.2)
    divisor := build divisorPtr divisorCount hdivisor96 hdivisorMem hdivisorActiveEnd
      (hdivisorRead.trans hdivisorHeader)
    remainder := build remPtr divisorCount hrem96 hremMem hremActiveEnd
      (hremRead.trans hremHeader)
    normalizedDivisor := build (vFp fp m divisorCount) divisorCount hv96
      (by rw [hvSize]) (by omega) hvHeaderRead
  }

/-- The in-range zero-shift copy preserves all existing headers and active guards while filling
the normalized-divisor payload. -/
theorem zeroLayouts
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    VLayouts (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
      fp (uFp fp m divisorCount) (vFp fp m divisorCount) divisorPtr remPtr
      (numQ m divisorCount) m divisorCount := by
  have initial := vLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hzSize := zeroMemory_size facts hmPos hmDividend hquotientBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have transfer : ∀ ptr count,
      ptr < UInt256.size → ptr + 32 ≤ vFp fp m divisorCount + 32 →
      MultiLimbArrayReadSemantic.Layout
        (vMemory mem fp dividendPtr m divisorCount)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr) ptr count →
      MultiLimbArrayReadSemantic.Layout
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (zeroWords aw fp dividendPtr divisorPtr m divisorCount) ptr count := by
    intro ptr count hptrFit hptr layout
    have hheader : MultiLimbSchoolbookNormalization.arrayHeader
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat ptr) =
      MultiLimbSchoolbookNormalization.arrayHeader
        (vMemory mem fp dividendPtr m divisorCount)
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat ptr) := by
      apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
      · rw [UInt256.toNat_ofNat_of_lt hptrFit, hvSize]
        omega
      · rw [hvSize, hzSize]
        omega
      · rw [UInt256.toNat_ofNat_of_lt hptrFit]
        exact zeroMemory_read_below facts hmPos hmDividend hquotientBound hptr
    refine {
      header := ?_
      headerAw := ?_
      wordAw := ?_
    }
    · rw [hawEq]
      exact hheader.trans layout.header
    · rw [hawEq]
      exact layout.headerAw
    · intro i hi
      rw [hawEq]
      exact layout.wordAw i hi
  have hfpFit : fp < UInt256.size := lt_trans (by
    have := hquotientBound
    omega : fp < 2 ^ 64) (by norm_num [UInt256.size])
  have huFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
    have := huBound
    omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
    have := hvBound
    omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hdivisorFit : divisorPtr < UInt256.size := lt_trans (by
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    have := hquotientBound
    omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hremFit : remPtr < UInt256.size := lt_trans (by
    have := facts.remainderEndBeforeFp
    have := hquotientBound
    omega : remPtr < 2 ^ 64) (by norm_num [UInt256.size])
  refine {
    quotient := transfer fp (numQ m divisorCount) hfpFit (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) initial.quotient
    dividend := transfer (uFp fp m divisorCount) (m + 1) huFit (by
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega) initial.dividend
    divisor := transfer divisorPtr divisorCount hdivisorFit (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      unfold vFp uFp
      omega) initial.divisor
    remainder := transfer remPtr divisorCount hremFit (by
      have := facts.remainderEndBeforeFp
      unfold vFp uFp
      omega) initial.remainder
    normalizedDivisor := transfer (vFp fp m divisorCount) divisorCount hvFit (by omega)
      initial.normalizedDivisor
  }

/-- The zero-shift `MCOPY` materializes a normalized-divisor array whose complete guarded slice
is exactly the original divisor slice. -/
theorem zeroDivisorWords_eq
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
        (UInt256.ofNat (vFp fp m divisorCount)) 0 divisorCount =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat divisorPtr) 0 divisorCount := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hzSize := zeroMemory_size facts hmPos hmDividend hquotientBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have hcopied : MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
      (UInt256.ofNat (vFp fp m divisorCount)) 0 divisorCount =
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (vMemory mem fp dividendPtr m divisorCount)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) 0 divisorCount := by
    apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
    intro i hi
    simp only [Nat.zero_add]
    apply MultiLimbArrayReadSemantic.arrayWord_eq_of_distinct_readWithPadding_eq
    · exact lt_trans (by
        have := hvBound
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvBound
        omega : vFp fp m divisorCount + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])
    · exact lt_trans (by
        have := facts.divisorEndBeforeDividend
        have := facts.dividendEndBeforeRemainder
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : divisorPtr + 32 * (i + 1) < 2 ^ 64)
        (by norm_num [UInt256.size])
    · rw [hzSize]
      omega
    · rw [hvSize]
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hawEq]
      have hactive := geometry.hvActive
      have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
        have := hvBound
        omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
      rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
      omega
    · have hactive := geometry.hvActive
      have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
        have := hvBound
        omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
      rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      exact le_trans (by
        unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
        omega) hactive
    · rw [hawEq]
      exact geometry.hawFit
    · exact geometry.hawFit
    · simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm (32 * i) 32] using
        zeroMemory_read_v_word (i := i) facts hmPos hmDividend hquotientBound hi
  exact hcopied.trans (vOriginalWords_eq facts hmPos hmDividend hquotientBound huBound
    hvBound facts.divisorPtr96 (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      omega))

/-- The top limb observed after zero normalization is the exact CLZ input loaded from the
original divisor. -/
theorem zeroTop_eq_setupTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayWord
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
        (UInt256.ofNat (vFp fp m divisorCount)) (divisorCount - 1) =
      setupTop mem aw fp dividendPtr divisorPtr m divisorCount := by
  have hslice := zeroDivisorWords_eq facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hi : divisorCount - 1 < divisorCount := by
    have := facts.divisorTwo
    omega
  have hword := MultiLimbArrayReadSemantic.arrayWord_eq_of_arrayReadWords_eq
    (zeroMemory mem fp dividendPtr divisorPtr m divisorCount) mem
    (zeroWords aw fp dividendPtr divisorPtr m divisorCount) aw
    (UInt256.ofNat (vFp fp m divisorCount)) (UInt256.ofNat divisorPtr)
    0 divisorCount (divisorCount - 1) hi hslice
  simp only [Nat.zero_add] at hword
  exact hword.trans (originalDivisorTop_eq_setupTop facts hmPos hmDividend hquotientBound
    huBound hvBound)

/-- A zero CLZ result means the copied top limb already satisfies Knuth's half-radix premise. -/
theorem zeroMemory_normalizedTop
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftZero : (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n = 0) :
    UInt256.size ≤ 2 *
      (MultiLimbSchoolbookNormalization.arrayWord
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
        (UInt256.ofNat (vFp fp m divisorCount)) (divisorCount - 1)).toNat := by
  rw [zeroTop_eq_setupTop facts hmPos hmDividend hknuth hquotientBound huBound hvBound]
  apply MultiLimbBarrettContinuationExecutable.normalizedTop_of_clz_zero
  · intro hzero
    exact setupTop_ne_zero facts hmPos hmDividend hquotientBound huBound hvBound
      (uint256_toNat_eq_zero hzero)
  · exact hshiftZero

/-- Zero normalization preserves the copied `u[0..m)` payload exactly. -/
theorem zeroDividendPrefix_eq
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
        (UInt256.ofNat (uFp fp m divisorCount)) 0 m =
      MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat dividendPtr) 0 m := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hzSize := zeroMemory_size facts hmPos hmDividend hquotientBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have hpreserved : MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) 0 m =
    MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      (vMemory mem fp dividendPtr m divisorCount)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) 0 m := by
    apply MultiLimbArrayReadSemantic.arrayReadWords_eq_of_words
    intro i hi
    simp only [Nat.zero_add]
    apply MultiLimbArrayReadSemantic.arrayWord_eq_of_readWithPadding_eq
    · have hfit := geometry.huFit
      have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
        have := huBound
        omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
      rw [UInt256.toNat_ofNat_of_lt huPtrFit] at hfit
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hfit
      omega
    · rw [hzSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hvSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hawEq]
      have hactive := geometry.huTopActive
      have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
        have := huBound
        omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
      rw [UInt256.toNat_ofNat_of_lt huPtrFit] at hactive
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hactive
      omega
    · have hactive := geometry.huTopActive
      have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
        have := huBound
        omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
      rw [UInt256.toNat_ofNat_of_lt huPtrFit] at hactive
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hactive
      omega
    · rw [hawEq]
      exact geometry.hawFit
    · exact geometry.hawFit
    · simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc,
        Nat.add_comm (32 * i) 32] using
        zeroMemory_read_below facts hmPos hmDividend hquotientBound (ptr :=
          uFp fp m divisorCount + 32 * (i + 1)) (by
            unfold vFp wordArrayAllocationSize wordArrayPayloadSize
            omega)
  exact hpreserved.trans (vDividendWords_eq facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound)

/-- The allocated extra `u[m]` word is the padded zero carry word, and the zero-shift copy leaves
it untouched. -/
theorem zeroDividendTop_eq_zero
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayWord
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
        (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
        (UInt256.ofNat (uFp fp m divisorCount)) m = ⟨0⟩ := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have hfit : uFp fp m divisorCount + 32 * (m + 1) < UInt256.size := by
    have hfull := geometry.huFit
    have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
      have := huBound
      omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt huPtrFit] at hfull
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hfull
    omega
  have hread : (zeroMemory mem fp dividendPtr divisorPtr m divisorCount).readWithPadding
      (uFp fp m divisorCount + 32 * (m + 1)) 32 = UInt256.toByteArray ⟨0⟩ := by
    calc
      _ = (vMemory mem fp dividendPtr m divisorCount).readWithPadding
          (uFp fp m divisorCount + 32 * (m + 1)) 32 :=
        zeroMemory_read_below facts hmPos hmDividend hquotientBound (by
          unfold vFp wordArrayAllocationSize wordArrayPayloadSize
          omega)
      _ = (setupMemory mem fp dividendPtr m divisorCount).readWithPadding
          (uFp fp m divisorCount + 32 * (m + 1)) 32 :=
        vMemory_read_below facts hmPos hmDividend hquotientBound (by
          have := facts.fp96
          unfold uFp
          omega) (by
            unfold vFp wordArrayAllocationSize wordArrayPayloadSize
            omega)
      _ = UInt256.toByteArray ⟨0⟩ := by
        rw [readWithPadding_past_end (setupMemory mem fp dividendPtr m divisorCount)
          (uFp fp m divisorCount + 32 * (m + 1)) 32 (by rw [hsetupSize]; omega)
          (by norm_num), ← zero_toByteArray_eq_zeroes32]
  rw [hawEq]
  apply arrayWord_eq_zero_of_read_zero
  · exact hfit
  · have hactive := geometry.huTopActive
    have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
      have := huBound
      omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt huPtrFit] at hactive
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hactive
    omega
  · exact geometry.hawFit
  · exact hread

/-- The complete `(m+1)`-word zero-shift dividend denotes the original `m`-word trimmed
dividend; the allocated top carry contributes exactly zero. -/
theorem zeroDividend_value
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
          (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
          (UInt256.ofNat (uFp fp m divisorCount)) 0 (m + 1)) =
      Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          mem aw (UInt256.ofNat dividendPtr) 0 m) := by
  have hsplit := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_succ_append
    (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
    (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
    (UInt256.ofNat (uFp fp m divisorCount)) 0 m
  have hprefix := zeroDividendPrefix_eq facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have htop := zeroDividendTop_eq_zero facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  rw [hsplit]
  simp only [Nat.zero_add]
  rw [htop, Modexp.wordLimbsToNat_append, hprefix]
  simp only [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length,
    Modexp.wordLimbsToNat, Nat.mul_zero, Nat.add_zero]
  norm_num

/-- Concrete zero normalization constructs the complete exposed quotient selector from the exact
copied dividend and divisor values. -/
theorem zeroSelection_exists
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftZero : (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n = 0) :
    Nonempty (MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) ⟨0⟩ ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨0⟩
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)) := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have zeroGeometry : MultiLimbSchoolbookContinuationExecutable.ContinuationGeometry
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount))
      (UInt256.ofNat (vFp fp m divisorCount)) (UInt256.ofNat fp)
      divisorCount (m + 1) (numQ m divisorCount) := by
    rw [hawEq]
    exact geometry
  have layouts := zeroLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hnormalized := zeroMemory_normalizedTop facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound hshiftZero
  have hzSize := zeroMemory_size facts hmPos hmDividend hquotientBound
  have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
    have := hvBound
    omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hvMem : (UInt256.ofNat (vFp fp m divisorCount)).toNat +
      32 * (divisorCount + 1) ≤
        (zeroMemory mem fp dividendPtr divisorPtr m divisorCount).size := by
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit, hzSize]
    omega
  have hdividendValue := zeroDividend_value facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have hdivisorValue := zeroDivisorWords_eq facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  let dividendNat := Modexp.wordLimbsToNat
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw (UInt256.ofNat dividendPtr) 0 m)
  let divisorNat := Modexp.wordLimbsToNat
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
      mem aw (UInt256.ofNat divisorPtr) 0 divisorCount)
  have hdividendBound : dividendNat < UInt256.size ^ m := by
    have hbound := Modexp.wordLimbsToNat_lt_pow
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw (UInt256.ofNat dividendPtr) 0 m)
    rw [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length] at hbound
    exact hbound
  have hdivisorLower : UInt256.size ^ (divisorCount - 1) ≤ divisorNat := by
    exact arrayValueLowerOfTopNonzero mem aw (UInt256.ofNat divisorPtr)
      (MultiLimbSchoolbookNormalization.arrayWord mem aw (UInt256.ofNat divisorPtr)
        (divisorCount - 1)) divisorCount (by
          have := facts.divisorTwo
          omega) rfl facts.divisorTopNonzero
  have hfullMath := normalizedFullBound m divisorCount 0 dividendNat divisorNat
    (by have := facts.divisorTwo; omega) hknuth hdividendBound hdivisorLower
  have hfull : Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
          (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
          (UInt256.ofNat (uFp fp m divisorCount)) 0
          (numQ m divisorCount + divisorCount)) <
      UInt256.size ^ (numQ m divisorCount - 1) *
        (UInt256.size * Modexp.wordLimbsToNat
          (MultiLimbSchoolbookIterationSemantic.divisorReadSlice
            (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
            (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
            (UInt256.ofNat (vFp fp m divisorCount)) 0 divisorCount)) := by
    have hlength : numQ m divisorCount + divisorCount = m + 1 := by
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
      omega
    rw [hlength, hdividendValue,
      MultiLimbSchoolbookCompleteSemantic.divisorReadSlice_eq_arrayReadWords,
      hdivisorValue]
    simpa only [pow_zero, Nat.mul_one] using hfullMath
  have hbound :=
    MultiLimbBarrettContinuationExecutable.initialWindow_lt_radix_mul_of_full_bound
      zeroGeometry hfull
  exact MultiLimbBarrettReduceBaseExecutable.knuthSelection_exists_of_memory
    zeroGeometry layouts.dividend.header layouts.normalizedDivisor.header
    layouts.quotient.header hnormalized hvMem hbound

/-- The positive-CLZ divisor pass is exactly the generated append-at-frontier shift loop. -/
theorem positiveDivisorValid
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.ValidDivisorShift
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
      divisorCount shift 0 divisorCount (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩ := by
  have layouts := vLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  apply MultiLimbBarrettContinuationExecutable.validDivisorShiftOfFrontier
  · rw [hvSize]
    omega
  · exact layouts.divisor.header
  · exact layouts.normalizedDivisor.header
  · exact layouts.divisor.headerAw
  · exact layouts.normalizedDivisor.headerAw
  · intro j hj hlt
    exact layouts.divisor.wordAw j (by omega)
  · intro j hj hlt
    exact layouts.normalizedDivisor.wordAw j (by omega)
  · intro j hj
    simp only [Nat.zero_add]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  · intro j hj hlt
    have hdivisorFit : divisorPtr < UInt256.size := by
      exact lt_trans (by
        have := facts.divisorEndBeforeDividend
        have := facts.dividendEndBeforeRemainder
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : divisorPtr < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt hdivisorFit,
      arrayAddressNat (vFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
        omega)]
    have := facts.divisorEndBeforeDividend
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro j hj hlt
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit,
      arrayAddressNat (vFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
        omega)]
    omega

/-- After shifting the fresh divisor, the in-place `u[0..m)` pass satisfies every generated
header, access, and write obligation. -/
theorem positiveDividendValid
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.ValidDivisorShift
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat (uFp fp m divisorCount))
      (m + 1) shift 0 m
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
      ⟨0⟩ := by
  have layouts := vLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvFrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorResultSize :
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory.size =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
      shift 0 divisorCount (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hvFrontier)
    simpa only [positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have huPtrFit : uFp fp m divisorCount < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have huBelowV0 : uFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) 0).toNat := by
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huRead :
      ((positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
          ).readWithPadding (uFp fp m divisorCount) 32 =
        (vMemory mem fp dividendPtr m divisorCount).readWithPadding
          (uFp fp m divisorCount) 32 := by
    simpa only [positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount)) shift
        0 divisorCount (uFp fp m divisorCount)
        (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
        (by rw [hvSize]; omega)
        (by simpa only [Nat.zero_add] using hvFrontier) huBelowV0
  have huHeader : MultiLimbSchoolbookNormalization.arrayHeader
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) = UInt256.ofNat (m + 1) := by
    apply (MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
      (vMemory mem fp dividendPtr m divisorCount)
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) ?_ ?_ ?_).trans
    · exact layouts.dividend.header
    · rw [UInt256.toNat_ofNat_of_lt huPtrFit, hvSize]
      unfold vFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hdivisorResultSize]
      omega
    · simpa only [UInt256.toNat_ofNat_of_lt huPtrFit] using huRead
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
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega), hdivisorResultSize, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro j hj hlt
    rw [UInt256.toNat_ofNat_of_lt huPtrFit,
      arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega)]
    omega
  · intro j hj hlt
    rw [UInt256.toNat_ofNat_of_lt huPtrFit,
      arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega)]
    omega

/-- The fresh divisor shift preserves the concrete `u` header below its frontier writes. -/
theorem positiveDivisorResult_uHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayHeader
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) = UInt256.ofNat (m + 1) := by
  have layouts := vLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvFrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hresultSize :
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory.size =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
      shift 0 divisorCount (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hvFrontier)
    simpa only [positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have huPtrFit : uFp fp m divisorCount < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have huBelowV0 : uFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) 0).toNat := by
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huRead :
      ((positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
        ).readWithPadding (uFp fp m divisorCount) 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding
        (uFp fp m divisorCount) 32 := by
    simpa only [positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount)) shift
        0 divisorCount (uFp fp m divisorCount)
        (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
        (by rw [hvSize]; omega)
        (by simpa only [Nat.zero_add] using hvFrontier) huBelowV0
  apply (MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    (vMemory mem fp dividendPtr m divisorCount)
    (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
    (UInt256.ofNat (uFp fp m divisorCount)) ?_ ?_ ?_).trans
  · exact layouts.dividend.header
  · rw [UInt256.toNat_ofNat_of_lt huPtrFit, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hresultSize]
    omega
  · simpa only [UInt256.toNat_ofNat_of_lt huPtrFit] using huRead

/-- The completed in-place dividend shift still exposes the real `m+1` header. -/
theorem positiveDividendResult_uHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayHeader
      (positiveDividendResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) = UInt256.ofNat (m + 1) := by
  have huHeader := positiveDivisorResult_uHeader facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound (shift := shift)
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by omega : vFp fp m divisorCount +
        wordArrayAllocationSize divisorCount + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hvFrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (vFp fp m divisorCount)) j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorSize :
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory.size =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
      shift 0 divisorCount (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hvFrontier)
    simpa only [positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (uFp fp m divisorCount)) j).toNat + 32 ≤
        (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory.size := by
    intro j hj
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega), hdivisorSize, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have huPtrFit : uFp fp m divisorCount < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
    omega
  have huBelow : ∀ j, j < m → uFp fp m divisorCount + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress
        (UInt256.ofNat (uFp fp m divisorCount)) j).toNat := by
    intro j hj
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    omega
  have huRead :
      ((positiveDividendResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
        ).readWithPadding (uFp fp m divisorCount) 32 =
      ((positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
        ).readWithPadding (uFp fp m divisorCount) 32 := by
    simpa only [positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult,
      positiveDivisorResult, Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_inBounds
        (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
        (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat (uFp fp m divisorCount))
        shift 0 m (uFp fp m divisorCount)
        (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory ⟨0⟩
        (by rw [hdivisorSize, hvSize]; omega)
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using huBelow)
  have hresultSize :
      (positiveDividendResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory.size =
        (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat (uFp fp m divisorCount))
      shift 0 m
      (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory ⟨0⟩
      (by simpa only [Nat.zero_add] using huWrite)
    simpa only [positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult,
      positiveDivisorResult] using hsize
  apply (MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    (positiveDivisorResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
    (positiveDividendResult mem aw fp dividendPtr divisorPtr m divisorCount shift).memory
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
    (UInt256.ofNat (uFp fp m divisorCount)) ?_ ?_ ?_).trans
  · exact huHeader
  · rw [UInt256.toNat_ofNat_of_lt huPtrFit, hdivisorSize, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hresultSize]
  · simpa only [UInt256.toNat_ofNat_of_lt huPtrFit] using huRead
/-- Execute the selected Knuth setup from PC 5287 through the concrete `_clz` return. -/
theorem setupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    {tail : List UInt256}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hknuth : divisorCount ≤ m) (hmDividend : m ≤ dividendCount)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5287⟩
      (UInt256.ofNat divisorCount :: UInt256.ofNat m :: UInt256.ofNat remPtr ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorPtr ::
        ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    let result := MultiLimbSchoolbookKnuthPrefix.clzResultOf mem aw fp
      (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr)
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat result.n :: UInt256.ofNat remPtr :: ⟨3010⟩ ::
        UInt256.ofNat divisorCount :: UInt256.ofNat m :: UInt256.ofNat fp ::
        UInt256.ofNat (uFp fp m divisorCount) :: UInt256.ofNat (numQ m divisorCount) ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      (MultiLimbSchoolbookKnuthPrefix.copiedMemory mem fp (uFp fp m divisorCount)
        dividendPtr m divisorCount)
      (MultiLimbSchoolbookKnuthPrefix.finalWords aw fp (uFp fp m divisorCount)
        dividendPtr m divisorCount (UInt256.ofNat divisorPtr))
      rdata acc
      (steps + MultiLimbSchoolbookKnuthPrefix.totalSteps mem aw fp
        (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr))
      (gasUsed + MultiLimbSchoolbookKnuthPrefix.totalGas mem aw fp
        (uFp fp m divisorCount) dividendPtr m divisorCount
          (UInt256.ofNat divisorPtr)) := by
  have hmBound : m ≤ 32 := by
    have := facts.dividendBound
    omega
  have hdivisorEnd := facts.divisorEndBeforeDividend
  have hdividendEnd := facts.dividendEndBeforeRemainder
  have hremainderEnd := facts.remainderEndBeforeFp
  have hkTwo := facts.divisorTwo
  have hkBound := facts.divisorBound
  have hnumQPos : 0 < numQ m divisorCount := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hnumQBound : numQ m divisorCount ≤ 32 := by
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  have hqFit : fp + wordArrayAllocationSize (numQ m divisorCount) + 31 <
      UInt256.size := lt_trans (by omega : fp + wordArrayAllocationSize
        (numQ m divisorCount) + 31 < 2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hqRange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (numQ m divisorCount) hnumQPos facts.awFit hqFit
  let qMem := MultiLimbSchoolbookKnuthPrefix.quotientMemory mem fp m divisorCount
  let qAw := MultiLimbSchoolbookKnuthPrefix.quotientWords aw fp m divisorCount
  have hqSetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))).size =
        mem.size := setFreePtr_size facts.memory96
  have hqSize : qMem.size = fp + 32 := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).size = fp + 32
    apply storeBytesLength_size
    · rw [hqSetSize]
      exact facts.memoryLeFp
    · rw [hqSetSize]
      exact facts.fpGap
  have hq96 : 96 ≤ qMem.size := by rw [hqSize]; omega
  have hqLeU : qMem.size ≤ uFp fp m divisorCount := by
    rw [hqSize]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hqGapU : uFp fp m divisorCount - qMem.size < USize.size := by
    have hgapEq : uFp fp m divisorCount - qMem.size = 32 * numQ m divisorCount := by
      rw [hqSize]
      unfold uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    rw [hgapEq]
    have : 32 * 32 < USize.size := by native_decide
    omega
  have hqFree : qMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (uFp fp m divisorCount)) := by
    dsimp only [qMem]
    unfold MultiLimbSchoolbookKnuthPrefix.quotientMemory
      MultiLimbSchoolbookKnuthSetup.quotientMemory
    change (storeBytesLength
      (setFreePtr mem (fp + wordArrayAllocationSize (numQ m divisorCount))) fp
      (numQ m divisorCount)).readWithPadding 64 32 = _
    unfold uFp
    rw [storeBytesLength_read_below]
    · exact setFreePtr_read64 facts.memory96
    · rw [setFreePtr_size facts.memory96]
      exact facts.memory96
    · exact facts.fp96
    · rw [setFreePtr_size facts.memory96]
      exact facts.fpGap
  have hqAwEq : qAw = newWordArrayWords aw fp (numQ m divisorCount) := rfl
  have hqAw3 : 3 ≤ qAw.toNat := by
    rw [hqAwEq]
    have hfp96 := facts.fp96
    have := hqRange.1
    omega
  have hqAw64 : ¬ (⟨64⟩ : UInt256) ≥ qAw * ⟨32⟩ := by
    have hmul : (qAw * (⟨32⟩ : UInt256)).toNat = qAw.toNat * 32 := by
      rw [hqAwEq]
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := newWordArrayWords aw fp (numQ m divisorCount))
          (b := (⟨32⟩ : UInt256)) hqRange.2
    intro hle
    have hnat : (qAw * ⟨32⟩).toNat ≤ 64 := hle
    rw [hmul] at hnat
    omega
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by omega : uFp fp m divisorCount +
        wordArrayAllocationSize (m + 1) + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have huRange := MultiLimbOddConversionSemantic.newWordArrayWords_range qAw
    (uFp fp m divisorCount) (m + 1) (by omega)
    (by rw [hqAwEq]; exact hqRange.2) huFit
  let uMem := MultiLimbSchoolbookKnuthPrefix.uMemory mem fp
    (uFp fp m divisorCount) m divisorCount
  let uAw := MultiLimbSchoolbookKnuthPrefix.uWords aw fp
    (uFp fp m divisorCount) m divisorCount
  have huSetSize : (setFreePtr qMem
      (uFp fp m divisorCount + wordArrayAllocationSize (m + 1))).size = qMem.size :=
    setFreePtr_size hq96
  have huSize : uMem.size = uFp fp m divisorCount + 32 := by
    dsimp only [uMem]
    unfold MultiLimbSchoolbookKnuthPrefix.uMemory MultiLimbSchoolbookKnuthSetup.uMemory
    apply storeBytesLength_size
    · rw [huSetSize]
      exact hqLeU
    · rw [huSetSize]
      exact hqGapU
  have huAwEq : uAw = newWordArrayWords qAw (uFp fp m divisorCount) (m + 1) := rfl
  have hdividendBeforeU : dividendPtr + 32 ≤ uFp fp m divisorCount := by
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    unfold uFp
    omega
  have hmax : max (uFp fp m divisorCount + 32) (dividendPtr + 32) =
      uFp fp m divisorCount + 32 := max_eq_left (by omega)
  have hcopyCovered : max (uFp fp m divisorCount + 32) (dividendPtr + 32) + 32 * m ≤
      32 * uAw.toNat := by
    rw [hmax, huAwEq]
    exact le_trans (by omega) huRange.1
  have hcopiedAw : MultiLimbSchoolbookKnuthPrefix.copiedWords aw fp
      (uFp fp m divisorCount) dividendPtr m divisorCount = uAw := by
    unfold MultiLimbSchoolbookKnuthPrefix.copiedWords
      MultiLimbSchoolbookKnuthSetup.copiedUWords
    rw [machineM_eq_of_access hcopyCovered]
    exact u256_ofNat_toNat uAw
  have hdivisorReadQ : qMem.readWithPadding divisorPtr 32 =
      mem.readWithPadding divisorPtr 32 := by
    simpa only [qMem, MultiLimbSchoolbookKnuthPrefix.quotientMemory,
      MultiLimbSchoolbookKnuthSetup.quotientMemory, numQ] using
      MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below mem fp
        (numQ m divisorCount) divisorPtr facts.memory96 facts.fpGap facts.divisorPtr96
        (by omega)
  have hdivisorReadU : uMem.readWithPadding divisorPtr 32 =
      qMem.readWithPadding divisorPtr 32 := by
    simpa only [uMem, MultiLimbSchoolbookKnuthPrefix.uMemory,
      MultiLimbSchoolbookKnuthSetup.uMemory] using
      MultiLimbSchoolbookKnuthSetupSemantic.allocatedWordArray_read_below qMem
        (uFp fp m divisorCount) (m + 1) divisorPtr hq96 hqGapU facts.divisorPtr96
        (by omega)
  have hsource : dividendPtr + 32 + 32 * m ≤ uMem.size := by
    rw [huSize]
    have := facts.dividendEndBeforeRemainder
    have := facts.remainderEndBeforeFp
    omega
  have hcopyRead :
      (MultiLimbSchoolbookKnuthPrefix.copiedMemory mem fp (uFp fp m divisorCount)
        dividendPtr m divisorCount).readWithPadding divisorPtr 32 =
      uMem.readWithPadding divisorPtr 32 := by
    have hread := write_read_below_end_from uMem uMem (dividendPtr + 32) (32 * m)
      divisorPtr (by omega) hsource (by rw [huSize]; omega)
    dsimp only [uMem] at hread ⊢
    unfold MultiLimbSchoolbookKnuthPrefix.copiedMemory
      MultiLimbSchoolbookKnuthSetup.copiedUMemory
    rw [← huSize]
    exact hread
  have hcopiedSize :
      (MultiLimbSchoolbookKnuthPrefix.copiedMemory mem fp (uFp fp m divisorCount)
        dividendPtr m divisorCount).size = uMem.size + 32 * m := by
    have hsize := write_end_size_from uMem uMem (dividendPtr + 32) (32 * m)
      (by omega) hsource
    dsimp only [uMem] at hsize ⊢
    unfold MultiLimbSchoolbookKnuthPrefix.copiedMemory
      MultiLimbSchoolbookKnuthSetup.copiedUMemory
    rw [← huSize]
    exact hsize
  have hdivisorHeader : MultiLimbOddCompare.headerWord
      (MultiLimbSchoolbookKnuthPrefix.copiedMemory mem fp (uFp fp m divisorCount)
        dividendPtr m divisorCount)
      (MultiLimbSchoolbookKnuthPrefix.copiedWords aw fp (uFp fp m divisorCount)
        dividendPtr m divisorCount)
      (UInt256.ofNat divisorPtr) = UInt256.ofNat divisorCount := by
    change MultiLimbSchoolbookNormalization.arrayHeader _ _ _ = _
    rw [hcopiedAw]
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : divisorPtr < 2 ^ 64)
          (by norm_num [UInt256.size])), hcopiedSize, huSize]
      omega
    · rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : divisorPtr < 2 ^ 64)
          (by norm_num [UInt256.size])), huAwEq]
      exact le_trans (by omega) huRange.1
    · rw [huAwEq]
      exact huRange.2
    · rw [UInt256.toNat_ofNat_of_lt (by
        exact lt_trans (by omega : divisorPtr < 2 ^ 64)
          (by norm_num [UInt256.size]))]
      exact hcopyRead.trans (hdivisorReadU.trans
        (hdivisorReadQ.trans facts.divisorHeaderRead))
  simpa only [numQ, uFp] using
    MultiLimbSchoolbookKnuthPrefix.exact
      (quotientFp := fp) (uFp := uFp fp m divisorCount) (dividendPtr := dividendPtr)
      (ret := 3010) (m := m) (kEff := divisorCount)
      (tail := ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      (by omega) hknuth (by omega) facts.fp96 hquotientBound facts.memory96
      facts.memoryLeFp facts.fpGap facts.aw3 facts.aw64 facts.freeRead hcalldata
      (by unfold uFp; omega) huBound hq96 hqLeU hqGapU hqAw3 hqAw64 hqFree
      (by
        exact lt_trans (by omega : dividendPtr + 32 < 2 ^ 64)
          (by norm_num [UInt256.size]))
      (by
        exact lt_trans (by
          unfold wordArrayAllocationSize wordArrayPayloadSize at huBound
          omega : uFp fp m divisorCount + 32 < 2 ^ 64)
          (by norm_num [UInt256.size]))
      hdivisorHeader (by simp only [List.length_cons]; omega) h

/-- Compose the deployed high-zero scan and non-short selector with the complete Knuth setup.
The result retains both the selected zero-limb count and the concrete CLZ cost. -/
theorem selectedSetupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {m zeroLimbs : Nat} {top : UInt256} {tail : List UInt256}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (htop : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
      (m - 1) = top)
    (htopNonzero : top ≠ ⟨0⟩)
    (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 995)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    let result := MultiLimbSchoolbookKnuthPrefix.clzResultOf mem aw fp
      (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr)
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5368⟩
      (UInt256.ofNat result.n :: UInt256.ofNat remPtr :: ⟨3010⟩ ::
        UInt256.ofNat divisorCount :: UInt256.ofNat m :: UInt256.ofNat fp ::
        UInt256.ofNat (uFp fp m divisorCount) :: UInt256.ofNat (numQ m divisorCount) ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      (MultiLimbSchoolbookKnuthPrefix.copiedMemory mem fp (uFp fp m divisorCount)
        dividendPtr m divisorCount)
      (MultiLimbSchoolbookKnuthPrefix.finalWords aw fp (uFp fp m divisorCount)
        dividendPtr m divisorCount (UInt256.ofNat divisorPtr))
      rdata acc
      (steps + 134 + 72 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalSteps mem aw fp
          (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr))
      (gasUsed + 491 + 270 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalGas mem aw fp
          (uFp fp m divisorCount) dividendPtr m divisorCount
            (UInt256.ofNat divisorPtr)) := by
  have rd5287 := MultiLimbBarrettReduceBaseSelection.knuthPrefixExact facts hmPos hcount
    hzero htop htopNonzero hknuth (by omega) h
  have rd5368 := setupExact facts hmPos hknuth (by
    have := facts.dividendBound
    omega) hquotientBound huBound hcalldata htail rd5287
  exact rd5368.withIndices (by omega) (by omega)

/-- The original remainder allocation header survives complete positive normalization. -/
theorem positiveMemory_remainderHeader
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64) :
    MultiLimbSchoolbookNormalization.arrayHeader
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
      (UInt256.ofNat remPtr) = UInt256.ofNat divisorCount := by
  let stateAw := normalizedWords aw fp dividendPtr m divisorCount divisorPtr
  let u := UInt256.ofNat (uFp fp m divisorCount)
  let v := UInt256.ofNat (vFp fp m divisorCount)
  let rem := UInt256.ofNat remPtr
  let divisorResult := positiveDivisorResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  let dividendResult := positiveDividendResult mem aw fp dividendPtr divisorPtr m
    divisorCount shift
  have layouts := vLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hvSize := vMemory_size facts hmPos hmDividend hquotientBound
  have hfinalSize := positiveMemory_size facts hmPos hmDividend hquotientBound huBound
    hvBound (shift := shift)
  have huFit : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
      UInt256.size := lt_trans (by
        omega : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hvFit : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
      UInt256.size := lt_trans (by
        omega : vFp fp m divisorCount + wordArrayAllocationSize divisorCount + 31 <
          2 ^ 64 + 31) (by norm_num [UInt256.size])
  have hremPtrFit : remPtr < UInt256.size := lt_trans (by
    have := facts.remainderEndBeforeFp
    have := hquotientBound
    omega : remPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have hremNat := UInt256.toNat_ofNat_of_lt hremPtrFit
  have hbase32 : 32 ≤ (vMemory mem fp dividendPtr m divisorCount).size := by
    rw [hvSize]
    have := facts.fp96
    unfold vFp uFp
    omega
  have hfrontier : ∀ j, j ≤ divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress v j).toNat =
        (vMemory mem fp dividendPtr m divisorCount).size + 32 * j := by
    intro j hj
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega), hvSize]
    omega
  have hdivisorResultSize : divisorResult.memory.size =
      (vMemory mem fp dividendPtr m divisorCount).size + 32 * divisorCount := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_frontier
      stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount
      (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩
      (by simpa only [Nat.zero_add] using hfrontier)
    simpa only [stateAw, divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult] using hsize
  have hremBelowV0 : remPtr + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress v 0).toNat := by
    dsimp only [v]
    rw [arrayAddressNat (vFp fp m divisorCount) 0 (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvFit
      omega)]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremDivisorRead : divisorResult.memory.readWithPadding remPtr 32 =
      (vMemory mem fp dividendPtr m divisorCount).readWithPadding remPtr 32 := by
    simpa only [divisorResult, positiveDivisorResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDivisorResult, stateAw, v,
      Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_frontier
        stateAw (UInt256.ofNat divisorPtr) v shift 0 divisorCount remPtr
        (vMemory mem fp dividendPtr m divisorCount) ⟨0⟩ hbase32
        (by simpa only [Nat.zero_add] using hfrontier) hremBelowV0
  have huWrite : ∀ j, j < m →
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat + 32 ≤
        divisorResult.memory.size := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
        unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
        omega), hdivisorResultSize, hvSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremBelowU : ∀ j, j < m → remPtr + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u j).toNat := by
    intro j hj
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) j (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hdivisor32 : 32 ≤ divisorResult.memory.size := by
    rw [hdivisorResultSize]
    omega
  have hremDividendRead : dividendResult.memory.readWithPadding remPtr 32 =
      divisorResult.memory.readWithPadding remPtr 32 := by
    simpa only [dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult, stateAw, u, Nat.zero_add] using
      MultiLimbBarrettContinuationExecutable.shiftDivisor_read_below_inBounds
        stateAw u u shift 0 m remPtr divisorResult.memory ⟨0⟩ hdivisor32
        (by simpa only [Nat.zero_add] using huWrite)
        (by simpa only [Nat.zero_add] using hremBelowU)
  have hdividendResultSize : dividendResult.memory.size = divisorResult.memory.size := by
    have hsize := MultiLimbSchoolbookNormalizationSemantic.shiftDivisor_size_eq_of_inBounds
      stateAw u u shift 0 m divisorResult.memory ⟨0⟩
      (by simpa only [Nat.zero_add] using huWrite)
    simpa only [stateAw, dividendResult, positiveDividendResult,
      MultiLimbSchoolbookNormalizationFunction.positiveDividendResult, divisorResult,
      positiveDivisorResult] using hsize
  have htopWrite : (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat + 32 ≤
      dividendResult.memory.size := by
    rw [hdividendResultSize, hdivisorResultSize, hvSize]
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremBelowTop : remPtr + 32 ≤
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat := by
    dsimp only [u]
    rw [arrayAddressNat (uFp fp m divisorCount) m (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at huFit
      omega)]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hfinal32 : 32 ≤ dividendResult.memory.size := by
    rw [hdividendResultSize]
    exact hdivisor32
  have hremTopRead :
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).readWithPadding
          remPtr 32 = dividendResult.memory.readWithPadding remPtr 32 := by
    change (dividendResult.carry.toByteArray.write 0 dividendResult.memory
      (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat 32).readWithPadding
        remPtr 32 = _
    exact toByteArray_write_read_below_padded_of_gap dividendResult.carry
      dividendResult.memory (MultiLimbSchoolbookNormalization.arrayAddress u m).toNat
      remPtr hfinal32 hremBelowTop (by
        have husize : 0 < USize.size := by native_decide
        have := htopWrite
        omega)
  have hdivHeader : MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory
      stateAw rem = MultiLimbSchoolbookNormalization.arrayHeader
        (vMemory mem fp dividendPtr m divisorCount) stateAw rem := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hremNat, hvSize]
      have := facts.remainderEndBeforeFp
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hdivisorResultSize]
      omega
    · simpa only [rem, hremNat] using hremDivisorRead
  have hdividendHeader : MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory
      stateAw rem = MultiLimbSchoolbookNormalization.arrayHeader divisorResult.memory
        stateAw rem := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hremNat, hdivisorResultSize, hvSize]
      have := facts.remainderEndBeforeFp
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hdividendResultSize]
    · simpa only [rem, hremNat] using hremDividendRead
  have hfinalHeader : MultiLimbSchoolbookNormalization.arrayHeader
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift) stateAw rem =
        MultiLimbSchoolbookNormalization.arrayHeader dividendResult.memory stateAw rem := by
    apply MultiLimbBarrettContinuationExecutable.arrayHeader_eq_of_readWithPadding_eq
    · rw [hremNat, hdividendResultSize, hdivisorResultSize, hvSize]
      have := facts.remainderEndBeforeFp
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    · rw [hfinalSize, hdividendResultSize, hdivisorResultSize, hvSize]
    · simpa only [rem, hremNat] using hremTopRead
  exact hfinalHeader.trans
    (hdividendHeader.trans (hdivHeader.trans layouts.remainder.header))

/-- A selected positive quotient trace determines the complete concrete denormalization
certificate for the original remainder allocation. -/
theorem positiveValidDenormalize
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (selected : MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat shift) ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨1⟩
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)) :
    MultiLimbSchoolbookDenormalization.ValidDenormalize selected.finalAw
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat remPtr)
      (m + 1) divisorCount shift 0 divisorCount selected.finalMem := by
  let geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hheaders := positiveMemory_headers facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound (shift := shift)
  have hremHeader := positiveMemory_remainderHeader facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound (shift := shift)
  have hsize := positiveMemory_size facts hmPos hmDividend hquotientBound huBound hvBound
    (shift := shift)
  have hremPtrFit : remPtr < UInt256.size := lt_trans (by
    have := facts.remainderEndBeforeFp
    have := hquotientBound
    omega : remPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
    have := huBound
    omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hqPtrFit : fp < UInt256.size := lt_trans (by
    have := hquotientBound
    omega : fp < 2 ^ 64) (by norm_num [UInt256.size])
  have hremNat := UInt256.toNat_ofNat_of_lt hremPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have hremMem : (UInt256.ofNat remPtr).toNat <
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift).size := by
    rw [hremNat, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremBelowU : (UInt256.ofNat remPtr).toNat + 32 ≤
      (UInt256.ofNat (uFp fp m divisorCount)).toNat + 32 := by
    rw [hremNat, huNat]
    have := facts.remainderEndBeforeFp
    unfold uFp
    omega
  have hremBelowQuotient : ∀ jj, jj < numQ m divisorCount →
      (UInt256.ofNat remPtr).toNat + 32 ≤
        (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat fp) jj).toNat := by
    intro jj hj
    have hb := hquotientBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    have hfit64 : fp + 32 * (jj + 1) < 2 ^ 64 := by omega
    have hqFit : fp + 32 * (jj + 1) < UInt256.size :=
      lt_trans hfit64 (by norm_num [UInt256.size])
    rw [hremNat, arrayAddressNat fp jj hqFit]
    have := facts.remainderEndBeforeFp
    omega
  have hquotBelowU : ∀ jj, jj < numQ m divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat fp) jj).toNat + 32 ≤
        (UInt256.ofNat (uFp fp m divisorCount)).toNat := by
    intro jj hj
    have hb := hquotientBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    have hfit64 : fp + 32 * (jj + 1) < 2 ^ 64 := by omega
    have hqFit : fp + 32 * (jj + 1) < UInt256.size :=
      lt_trans hfit64 (by norm_num [UInt256.size])
    rw [arrayAddressNat fp jj hqFit, huNat]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hreturn :=
    MultiLimbBarrettContinuationExecutable.semanticContinuations_returnHeaders
      selected.semantic hheaders.2.1 hremHeader hremMem hremBelowU
      hremBelowQuotient hquotBelowU
  have hremActive : remPtr + 32 + 32 * divisorCount ≤ 32 * selected.finalAw.toNat := by
    rw [hreturn.1]
    have hactive := geometry.hvActive
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
      have := hvBound
      omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
    have := facts.remainderEndBeforeFp
    exact le_trans (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hactive
  have huHeaderAw : MultiLimbSchoolbookNormalization.arrayAfterHeader selected.finalAw
      (UInt256.ofNat (uFp fp m divisorCount)) = selected.finalAw := by
    rw [hreturn.1]
    exact geometry.huHeaderAw
  have huWordAw : ∀ i, i < divisorCount →
      MultiLimbSchoolbookNormalization.arrayAfterWord selected.finalAw
        (UInt256.ofNat (uFp fp m divisorCount)) i = selected.finalAw := by
    intro i hi
    rw [hreturn.1]
    exact geometry.huWordAw i (by omega)
  have hremHeaderAw : MultiLimbSchoolbookNormalization.arrayAfterHeader selected.finalAw
      (UInt256.ofNat remPtr) = selected.finalAw := by
    apply MultiLimbSchoolbookContinuationExecutable.arrayAfterHeader_eq_of_active
    rw [hremNat]
    omega
  have hremWordAw : ∀ i, i < divisorCount →
      MultiLimbSchoolbookNormalization.arrayAfterWord selected.finalAw
        (UInt256.ofNat remPtr) i = selected.finalAw := by
    intro i hi
    apply MultiLimbSchoolbookContinuationExecutable.arrayAfterWord_eq_of_active
    change (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat remPtr) i).toNat +
      32 ≤ 32 * selected.finalAw.toNat
    rw [arrayAddressNat remPtr i (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega
  have hcountWord : divisorCount < UInt256.size :=
    lt_of_le_of_lt facts.divisorBound (by norm_num [UInt256.size])
  have huCountWord : m + 1 < UInt256.size := lt_of_le_of_lt (by
    have := facts.dividendBound
    omega : m + 1 ≤ 33) (by norm_num [UInt256.size])
  have hfinalAwFit : selected.finalAw.toNat * 32 < UInt256.size := by
    rw [hreturn.1]
    exact geometry.hawFit
  apply MultiLimbBarrettContinuationExecutable.validDenormalizeOfLayout
    (m + 1) divisorCount shift (by omega) hcountWord huCountWord hfinalAwFit
    hreturn.2.2.1 huHeaderAw huWordAw hreturn.2.2.2 hremHeaderAw hremWordAw
  · rw [huNat, hreturn.2.1, hsize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hremNat, hreturn.2.1, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      hreturn.2.1, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [arrayAddressNat remPtr i (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega
  · intro i hi
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])), huNat]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [hremNat, arrayAddressNat remPtr i (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega

/-- Execute the selected positive-CLZ branch from PC 5199 through the complete quotient loop,
denormalization, and the real `reduceBase` return at PC 1707. -/
theorem selectedPositiveExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {m zeroLimbs shift : Nat} {top : UInt256} {tail : List UInt256}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (htop : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
      (m - 1) = top)
    (htopNonzero : top ≠ ⟨0⟩)
    (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n)
    (selected : MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat shift) ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨1⟩
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 993)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    let denormalized := MultiLimbSchoolbookDenormalization.denormalizeRange
      selected.finalAw (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat remPtr)
      shift 0 divisorCount selected.finalMem
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat divisorPtr :: tail)
      denormalized.memory selected.finalAw rdata acc
      ((((((steps + 134 + 72 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalSteps mem aw fp
          (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr)) +
        MultiLimbSchoolbookNormalizationFunction.positiveSteps
          (vMemory mem fp dividendPtr m divisorCount)
          (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
          (UInt256.ofNat (uFp fp m divisorCount)) divisorCount m shift) +
        selected.steps + 5) + 23) + denormalized.steps + 6) + 5)
      ((((((gasUsed + 491 + 270 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalGas mem aw fp
          (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr)) +
        MultiLimbSchoolbookNormalizationFunction.positiveGas
          (setupMemory mem fp dividendPtr m divisorCount)
          (setupWords aw fp dividendPtr m divisorCount divisorPtr)
          (UInt256.ofNat divisorPtr) (UInt256.ofNat (vFp fp m divisorCount))
          (UInt256.ofNat (uFp fp m divisorCount)) (vFp fp m divisorCount)
          divisorCount m shift) + selected.gas + 13) + 73) + denormalized.gas + 26) + 17) := by
  have hmDividend : m ≤ dividendCount := by omega
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hsetupCoverage := setupWords_uCoverage facts hmPos hmDividend hquotientBound huBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsetupLe : (setupMemory mem fp dividendPtr m divisorCount).size ≤
      vFp fp m divisorCount := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsetupGap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  have hsetupAw3 : 3 ≤ (setupWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize at hsetupCoverage
    omega
  have hsetupAw64 : ¬ (⟨64⟩ : UInt256) ≥
      setupWords aw fp dividendPtr m divisorCount divisorPtr * ⟨32⟩ := by
    have hmul :
        (setupWords aw fp dividendPtr m divisorCount divisorPtr * (⟨32⟩ : UInt256)).toNat =
          (setupWords aw fp dividendPtr m divisorCount divisorPtr).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := setupWords aw fp dividendPtr m divisorCount divisorPtr)
          (b := (⟨32⟩ : UInt256)) hsetupCoverage.2
    intro hge
    have hnat :
        (setupWords aw fp dividendPtr m divisorCount divisorPtr * ⟨32⟩).toNat ≤ 64 := hge
    rw [hmul] at hnat
    omega
  have hfree := setupMemory_freeRead facts hmPos hmDividend
  have hdivisorValid := positiveDivisorValid facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound (shift := shift)
  have hdividendValid := positiveDividendValid facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound (shift := shift)
  have huHeader := positiveDividendResult_uHeader facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound (shift := shift)
  have hheaders := positiveMemory_headers facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound (shift := shift)
  have hdenormalize := positiveValidDenormalize facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound selected
  have hshiftBound : shift < 256 := by
    rw [hshift]
    exact setupClzShift_lt_256 mem aw fp dividendPtr divisorPtr m divisorCount
  have rd5368 := selectedSetupExact facts hmPos hcount hzero htop htopNonzero hknuth
    hquotientBound huBound hcalldata (by omega) h
  have hresultShift :
      (MultiLimbSchoolbookKnuthPrefix.clzResultOf mem aw fp
        (uFp fp m divisorCount) dividendPtr m divisorCount
        (UInt256.ofNat divisorPtr)).n = shift := by
    rw [setupClzResult_eq]
    exact hshift.symm
  dsimp only at rd5368
  rw [hresultShift] at rd5368
  let vTop := MultiLimbSchoolbookNormalization.arrayWord
    (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
    (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)
    (UInt256.ofNat (vFp fp m divisorCount)) (divisorCount - 1)
  have rd3010 := MultiLimbBarrettReduceBaseExecutable.positiveFromClzExact
    (fp := vFp fp m divisorCount) (kEff := divisorCount) (m := m)
    (numQ := numQ m divisorCount) (ret := 3010) (shift := shift)
    (rem := UInt256.ofNat remPtr) (quotient := UInt256.ofNat fp)
    (u := UInt256.ofNat (uFp fp m divisorCount))
    (divisor := UInt256.ofNat divisorPtr) (vTop := vTop)
    (tail := ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
    hshiftPos hshiftBound (by have := facts.divisorTwo; omega) facts.divisorBound
    (lt_of_le_of_lt facts.divisorBound (by norm_num [UInt256.size]))
    (lt_of_le_of_lt (by have := facts.dividendBound; omega : m ≤ 32)
      (by norm_num [UInt256.size]))
    (lt_of_le_of_lt (by have := facts.dividendBound; omega : m + 1 ≤ 33)
      (by norm_num [UInt256.size]))
    (by unfold vFp uFp; have := facts.fp96; omega) hvBound hsetup96 hsetupLe
    hsetupGap hsetupAw3 hsetupAw64 hfree hcalldata hdivisorValid hdividendValid
    huHeader geometry.huHeaderAw (geometry.huWordAw m (by omega)) hheaders.2.2
    geometry.hvHeaderAw (geometry.hvWordAw (divisorCount - 1) (by
      have := facts.divisorTwo
      omega)) rfl selected
    (by unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ; omega)
    hdenormalize (by native_decide) (by simp only [List.length_cons]; omega)
    (by simpa only [setupMemory, setupWords] using rd5368)
  have rd1707 := MultiLimbBarrettConstant.divisionReturnExact (tail := tail)
    (by omega) rd3010
  exact rd1707.withIndices
    (by simpa only [vMemory, normalizedWords])
    (by simpa only [normalizedWords])

/-- The concrete denormalization produced by `selectedPositiveExact` is the pure remainder of
the original trimmed dividend by the original divisor.  The exposed `selected` value is shared
with execution, so this theorem covers the same q-hat estimates and correction branches. -/
theorem selectedPositiveResult_eq_mod
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {m shift : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftPos : 0 < shift)
    (hshift : shift = (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n)
    (selected : MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat shift) ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨1⟩
      (positiveMemory mem aw fp dividendPtr divisorPtr m divisorCount shift)
      (normalizedWords aw fp dividendPtr m divisorCount divisorPtr)) :
    Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (MultiLimbSchoolbookDenormalization.denormalizeRange selected.finalAw
            (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat remPtr)
            shift 0 divisorCount selected.finalMem).memory
          selected.finalAw (UInt256.ofNat remPtr) 0 divisorCount) =
      Modexp.wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat dividendPtr) 0 m) %
        Modexp.wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  let geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
    selected.semantic
  have hsize := positiveMemory_size facts hmPos hmDividend hquotientBound huBound hvBound
    (shift := shift)
  have hshiftBound : shift < 256 := by
    rw [hshift]
    exact setupClzShift_lt_256 mem aw fp dividendPtr divisorPtr m divisorCount
  have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
    have := huBound
    omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hremPtrFit : remPtr < UInt256.size := lt_trans (by
    have := facts.remainderEndBeforeFp
    have := hquotientBound
    omega : remPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hremNat := UInt256.toNat_ofNat_of_lt hremPtrFit
  apply MultiLimbBarrettReduceBaseExecutable.KnuthSelection.positiveResult_eq_mod selected
  · unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  · rw [selected.topValue]
    exact positiveMemory_normalizedTop facts hmPos hmDividend hknuth hquotientBound
      huBound hvBound hshiftPos hshift
  · exact hshiftPos
  · exact hshiftBound
  · exact MultiLimbBarrettContinuationExecutable.quotientBelowU geometry
  · have hvalue := positiveDividend_value facts hmPos hmDividend hknuth hquotientBound
      huBound hvBound hshiftPos hshift
    have hlength : selected.inputs.length + divisorCount = m + 1 := by
      rw [selected.inputsLength]
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
      omega
    simpa only [hlength] using hvalue
  · exact positiveDivisor_final_value facts hmPos hmDividend hknuth hquotientBound
      huBound hvBound hshiftPos hshift
  · exact facts.divisorBound
  · rw [huNat]
    have hfit := geometry.huFit
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hfit
    omega
  · rw [hfinal.1]
    exact geometry.hawFit
  · intro j hj
    rw [arrayAddressNat remPtr j (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      hfinal.2, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro j hj
    rw [arrayAddressNat remPtr j (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      hfinal.1]
    have hactive := geometry.hvActive
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
      have := hvBound
      omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
    have := facts.remainderEndBeforeFp
    exact le_trans (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hactive
  · intro i j hi hj
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      arrayAddressNat (uFp fp m divisorCount) j (by
        exact lt_trans (by
          have := huBound
          unfold wordArrayAllocationSize wordArrayPayloadSize at huBound
          omega : uFp fp m divisorCount + 32 * (j + 1) < 2 ^ 64)
          (by norm_num [UInt256.size]))]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i j hij hj
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      arrayAddressNat remPtr j (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega

/-- A selected zero-CLZ quotient trace determines the complete concrete direct-copy certificate
for the original remainder allocation. -/
theorem zeroValidCopy
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (selected : MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) ⟨0⟩ ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨0⟩
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)) :
    MultiLimbSchoolbookZeroShiftRemainder.ValidCopy selected.finalAw
      (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat remPtr)
      (m + 1) divisorCount 0 divisorCount selected.finalMem := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have zeroGeometry : MultiLimbSchoolbookContinuationExecutable.ContinuationGeometry
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount))
      (UInt256.ofNat (vFp fp m divisorCount)) (UInt256.ofNat fp)
      divisorCount (m + 1) (numQ m divisorCount) := by
    rw [hawEq]
    exact geometry
  have layouts := zeroLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hsize := zeroMemory_size facts hmPos hmDividend hquotientBound
  have hremPtrFit : remPtr < UInt256.size := lt_trans (by
    have := facts.remainderEndBeforeFp
    have := hquotientBound
    omega : remPtr < 2 ^ 64) (by norm_num [UInt256.size])
  have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
    have := huBound
    omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have hqPtrFit : fp < UInt256.size := lt_trans (by
    have := hquotientBound
    omega : fp < 2 ^ 64) (by norm_num [UInt256.size])
  have hremNat := UInt256.toNat_ofNat_of_lt hremPtrFit
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  have hqNat := UInt256.toNat_ofNat_of_lt hqPtrFit
  have hremMem : (UInt256.ofNat remPtr).toNat <
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount).size := by
    rw [hremNat, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hremBelowU : (UInt256.ofNat remPtr).toNat + 32 ≤
      (UInt256.ofNat (uFp fp m divisorCount)).toNat + 32 := by
    rw [hremNat, huNat]
    have := facts.remainderEndBeforeFp
    unfold uFp
    omega
  have hremBelowQuotient : ∀ jj, jj < numQ m divisorCount →
      (UInt256.ofNat remPtr).toNat + 32 ≤
        (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat fp) jj).toNat := by
    intro jj hj
    have hb := hquotientBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    have hqFit : fp + 32 * (jj + 1) < UInt256.size := lt_trans (by
      omega : fp + 32 * (jj + 1) < 2 ^ 64) (by norm_num [UInt256.size])
    rw [hremNat, arrayAddressNat fp jj hqFit]
    have := facts.remainderEndBeforeFp
    omega
  have hquotBelowU : ∀ jj, jj < numQ m divisorCount →
      (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat fp) jj).toNat + 32 ≤
        (UInt256.ofNat (uFp fp m divisorCount)).toNat := by
    intro jj hj
    have hb := hquotientBound
    unfold wordArrayAllocationSize wordArrayPayloadSize at hb
    have hqFit : fp + 32 * (jj + 1) < UInt256.size := lt_trans (by
      omega : fp + 32 * (jj + 1) < 2 ^ 64) (by norm_num [UInt256.size])
    rw [arrayAddressNat fp jj hqFit, huNat]
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hreturn :=
    MultiLimbBarrettContinuationExecutable.semanticContinuations_returnHeaders
      selected.semantic layouts.dividend.header layouts.remainder.header hremMem hremBelowU
      hremBelowQuotient hquotBelowU
  have hremActive : remPtr + 32 + 32 * divisorCount ≤ 32 * selected.finalAw.toNat := by
    rw [hreturn.1]
    have hactive := zeroGeometry.hvActive
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
      have := hvBound
      omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
    have := facts.remainderEndBeforeFp
    exact le_trans (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hactive
  have huHeaderAw : MultiLimbSchoolbookNormalization.arrayAfterHeader selected.finalAw
      (UInt256.ofNat (uFp fp m divisorCount)) = selected.finalAw := by
    rw [hreturn.1]
    exact zeroGeometry.huHeaderAw
  have huWordAw : ∀ i, i < divisorCount →
      MultiLimbSchoolbookNormalization.arrayAfterWord selected.finalAw
        (UInt256.ofNat (uFp fp m divisorCount)) i = selected.finalAw := by
    intro i hi
    rw [hreturn.1]
    exact zeroGeometry.huWordAw i (by omega)
  have hremHeaderAw : MultiLimbSchoolbookNormalization.arrayAfterHeader selected.finalAw
      (UInt256.ofNat remPtr) = selected.finalAw := by
    apply MultiLimbSchoolbookContinuationExecutable.arrayAfterHeader_eq_of_active
    rw [hremNat]
    omega
  have hremWordAw : ∀ i, i < divisorCount →
      MultiLimbSchoolbookNormalization.arrayAfterWord selected.finalAw
        (UInt256.ofNat remPtr) i = selected.finalAw := by
    intro i hi
    apply MultiLimbSchoolbookContinuationExecutable.arrayAfterWord_eq_of_active
    change (MultiLimbSchoolbookNormalization.arrayAddress (UInt256.ofNat remPtr) i).toNat +
      32 ≤ 32 * selected.finalAw.toNat
    rw [arrayAddressNat remPtr i (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega
  have hcountWord : divisorCount < UInt256.size :=
    lt_of_le_of_lt facts.divisorBound (by norm_num [UInt256.size])
  have huCountWord : m + 1 < UInt256.size := lt_of_le_of_lt (by
    have := facts.dividendBound
    omega : m + 1 ≤ 33) (by norm_num [UInt256.size])
  apply MultiLimbBarrettContinuationExecutable.validCopyOfLayout
    (m + 1) divisorCount (by omega) hcountWord huCountWord hreturn.2.2.1
    huHeaderAw huWordAw hreturn.2.2.2 hremHeaderAw hremWordAw
  · rw [huNat, hreturn.2.1, hsize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hremNat, hreturn.2.1, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      hreturn.2.1, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])), huNat]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i hi
    rw [hremNat, arrayAddressNat remPtr i (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega

/-- Execute the selected zero-CLZ branch from PC 5199 through `MCOPY`, the complete quotient
loop, direct remainder copy, and the real `reduceBase` return at PC 1707. -/
theorem selectedZeroExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed dividendPtr divisorPtr remPtr dividendCount divisorCount fp : Nat}
    {m zeroLimbs : Nat} {top : UInt256} {tail : List UInt256}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hcount : dividendCount = m + zeroLimbs)
    (hzero : ∀ i, m ≤ i → i < m + zeroLimbs →
      MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr) i = ⟨0⟩)
    (htop : MultiLimbSchoolbookTrim.dividendWord mem aw (UInt256.ofNat dividendPtr)
      (m - 1) = top)
    (htopNonzero : top ≠ ⟨0⟩)
    (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftZero : (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n = 0)
    (selected : MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) ⟨0⟩ ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨0⟩
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 993)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat dividendCount ::
        UInt256.ofNat dividendPtr :: ⟨3010⟩ :: UInt256.ofNat divisorCount ::
        UInt256.ofNat divisorPtr :: ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
      mem aw rdata acc steps gasUsed) :
    let copied := MultiLimbSchoolbookZeroShiftRemainder.copyRange
      selected.finalAw (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat remPtr)
      0 divisorCount selected.finalMem
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1707⟩
      (UInt256.ofNat remPtr :: UInt256.ofNat divisorPtr :: tail)
      copied.memory selected.finalAw rdata acc
      ((steps + 134 + 72 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalSteps mem aw fp
          (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr) +
        152 + selected.steps + 5 + 58 * divisorCount + 30) + 5)
      ((gasUsed + 491 + 270 * zeroLimbs +
        MultiLimbSchoolbookKnuthPrefix.totalGas mem aw fp
          (uFp fp m divisorCount) dividendPtr m divisorCount (UInt256.ofNat divisorPtr) +
        MultiLimbSchoolbookNormalizationFunction.zeroGas
          (setupWords aw fp dividendPtr m divisorCount divisorPtr) divisorPtr
          (vFp fp m divisorCount) divisorCount + selected.gas + 13 +
        208 * divisorCount + 100) + 17) := by
  have hmDividend : m ≤ dividendCount := by omega
  have layouts := zeroLayouts facts hmPos hmDividend hknuth hquotientBound huBound hvBound
  have hsetupSize := setupMemory_size facts hmPos hmDividend hquotientBound
  have hsetupCoverage := setupWords_uCoverage facts hmPos hmDividend hquotientBound huBound
  have hsetup96 : 96 ≤ (setupMemory mem fp dividendPtr m divisorCount).size := by
    rw [hsetupSize]
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsetupLe : (setupMemory mem fp dividendPtr m divisorCount).size ≤
      vFp fp m divisorCount := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hsetupGap : vFp fp m divisorCount -
      (setupMemory mem fp dividendPtr m divisorCount).size < USize.size := by
    rw [hsetupSize]
    unfold vFp wordArrayAllocationSize wordArrayPayloadSize
    have : 32 < USize.size := by native_decide
    omega
  have hsetupAw3 : 3 ≤ (setupWords aw fp dividendPtr m divisorCount divisorPtr).toNat := by
    have := facts.fp96
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize at hsetupCoverage
    omega
  have hsetupAw64 : ¬ (⟨64⟩ : UInt256) ≥
      setupWords aw fp dividendPtr m divisorCount divisorPtr * ⟨32⟩ := by
    have hmul :
        (setupWords aw fp dividendPtr m divisorCount divisorPtr * (⟨32⟩ : UInt256)).toNat =
          (setupWords aw fp dividendPtr m divisorCount divisorPtr).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := setupWords aw fp dividendPtr m divisorCount divisorPtr)
          (b := (⟨32⟩ : UInt256)) hsetupCoverage.2
    intro hge
    have hnat :
        (setupWords aw fp dividendPtr m divisorCount divisorPtr * ⟨32⟩).toNat ≤ 64 := hge
    rw [hmul] at hnat
    omega
  have hfree := setupMemory_freeRead facts hmPos hmDividend
  have hcopy := zeroValidCopy facts hmPos hmDividend hknuth hquotientBound huBound
    hvBound selected
  have rd5368 := selectedSetupExact facts hmPos hcount hzero htop htopNonzero hknuth
    hquotientBound huBound hcalldata (by omega) h
  have hresultZero :
      (MultiLimbSchoolbookKnuthPrefix.clzResultOf mem aw fp
        (uFp fp m divisorCount) dividendPtr m divisorCount
        (UInt256.ofNat divisorPtr)).n = 0 := by
    rw [setupClzResult_eq]
    exact hshiftZero
  dsimp only at rd5368
  rw [hresultZero] at rd5368
  let vTop := MultiLimbSchoolbookNormalization.arrayWord
    (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
    (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
    (UInt256.ofNat (vFp fp m divisorCount)) (divisorCount - 1)
  have rd3010 := MultiLimbBarrettReduceBaseExecutable.zeroFromClzExact
    (fp := vFp fp m divisorCount) (kEff := divisorCount) (m := m)
    (numQ := numQ m divisorCount) (ret := 3010)
    (rem := UInt256.ofNat remPtr) (quotient := UInt256.ofNat fp)
    (u := UInt256.ofNat (uFp fp m divisorCount)) (vTop := vTop)
    (tail := ⟨1707⟩ :: UInt256.ofNat divisorPtr :: tail)
    (by have := facts.divisorTwo; omega) facts.divisorBound
    (lt_of_le_of_lt facts.divisorBound (by norm_num [UInt256.size]))
    (lt_of_le_of_lt (by have := facts.divisorBound; omega : 32 * divisorCount ≤ 1024)
      (by norm_num [UInt256.size]))
    (lt_trans (by
      have := facts.divisorEndBeforeDividend
      have := facts.dividendEndBeforeRemainder
      have := facts.remainderEndBeforeFp
      have := hquotientBound
      omega : divisorPtr + 32 < 2 ^ 64) (by norm_num [UInt256.size]))
    (lt_trans (by
      unfold wordArrayAllocationSize wordArrayPayloadSize at hvBound
      omega : vFp fp m divisorCount + 32 < 2 ^ 64)
      (by norm_num [UInt256.size]))
    (by have := facts.fp96; unfold vFp uFp; omega) hvBound hsetup96 hsetupLe
    hsetupGap hsetupAw3 hsetupAw64 hfree hcalldata layouts.normalizedDivisor.header
    layouts.normalizedDivisor.headerAw
    (layouts.normalizedDivisor.wordAw (divisorCount - 1) (by
      have := facts.divisorTwo
      omega)) rfl selected
    (by unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ; omega) hcopy
    (by native_decide) (by simp only [List.length_cons]; omega)
    (by simpa only [zeroMemory, zeroWords] using rd5368)
  have rd1707 := MultiLimbBarrettConstant.divisionReturnExact (tail := tail)
    (by omega) rd3010
  exact rd1707

/-- The concrete direct copy produced by `selectedZeroExact` is the pure remainder of the
original trimmed dividend by the original divisor, for the identical exposed selector. -/
theorem selectedZeroResult_eq_mod
    {mem : ByteArray} {aw : UInt256}
    {dividendPtr divisorPtr remPtr dividendCount divisorCount fp m : Nat}
    (facts : MultiLimbBarrettReduceBaseSelection.DivisionEntryFacts
      mem aw dividendPtr divisorPtr remPtr dividendCount divisorCount fp)
    (hmPos : 0 < m) (hmDividend : m ≤ dividendCount) (hknuth : divisorCount ≤ m)
    (hquotientBound : fp + wordArrayAllocationSize (numQ m divisorCount) < 2 ^ 64)
    (huBound : uFp fp m divisorCount + wordArrayAllocationSize (m + 1) < 2 ^ 64)
    (hvBound : vFp fp m divisorCount + wordArrayAllocationSize divisorCount < 2 ^ 64)
    (hshiftZero : (MultiLimbClz.clzResult
      (setupTop mem aw fp dividendPtr divisorPtr m divisorCount)).n = 0)
    (selected : MultiLimbBarrettReduceBaseExecutable.KnuthSelection
      divisorCount (m + 1) (numQ m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount)) ⟨0⟩ ⟨3010⟩
      (UInt256.ofNat remPtr) (UInt256.ofNat (vFp fp m divisorCount))
      (UInt256.ofNat fp) ⟨0⟩
      (zeroMemory mem fp dividendPtr divisorPtr m divisorCount)
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)) :
    Modexp.wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
          (MultiLimbSchoolbookZeroShiftRemainder.copyRange selected.finalAw
            (UInt256.ofNat (uFp fp m divisorCount)) (UInt256.ofNat remPtr)
            0 divisorCount selected.finalMem).memory
          selected.finalAw (UInt256.ofNat remPtr) 0 divisorCount) =
      Modexp.wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat dividendPtr) 0 m) %
        Modexp.wordLimbsToNat
          (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
            mem aw (UInt256.ofNat divisorPtr) 0 divisorCount) := by
  have geometry := continuationGeometry facts hmPos hmDividend hknuth hquotientBound
    huBound hvBound
  have hawEq := zeroWords_eq_normalizedWords facts hmPos hmDividend hknuth
    hquotientBound huBound hvBound
  have zeroGeometry : MultiLimbSchoolbookContinuationExecutable.ContinuationGeometry
      (zeroWords aw fp dividendPtr divisorPtr m divisorCount)
      (UInt256.ofNat (uFp fp m divisorCount))
      (UInt256.ofNat (vFp fp m divisorCount)) (UInt256.ofNat fp)
      divisorCount (m + 1) (numQ m divisorCount) := by
    rw [hawEq]
    exact geometry
  have hfinal := MultiLimbSchoolbookOuterComplete.semanticContinuations_final_geometry
    selected.semantic
  have hsize := zeroMemory_size facts hmPos hmDividend hquotientBound
  have huPtrFit : uFp fp m divisorCount < UInt256.size := lt_trans (by
    have := huBound
    omega : uFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
  have huNat := UInt256.toNat_ofNat_of_lt huPtrFit
  apply MultiLimbBarrettReduceBaseExecutable.KnuthSelection.zeroResult_eq_mod selected
  · unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
    omega
  · rw [selected.topValue]
    exact zeroMemory_normalizedTop facts hmPos hmDividend hknuth hquotientBound
      huBound hvBound hshiftZero
  · exact MultiLimbBarrettContinuationExecutable.quotientBelowU zeroGeometry
  · have hvalue := zeroDividend_value facts hmPos hmDividend hknuth hquotientBound
      huBound hvBound
    have hlength : selected.inputs.length + divisorCount = m + 1 := by
      rw [selected.inputsLength]
      unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ
      omega
    simpa only [hlength] using hvalue
  · exact congrArg Modexp.wordLimbsToNat
      (zeroDivisorWords_eq facts hmPos hmDividend hknuth hquotientBound huBound hvBound)
  · exact facts.divisorBound
  · rw [huNat]
    have hfit := zeroGeometry.huFit
    unfold numQ MultiLimbSchoolbookKnuthPrefix.numQ at hfit
    omega
  · rw [hfinal.1]
    exact zeroGeometry.hawFit
  · intro j hj
    rw [arrayAddressNat remPtr j (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      hfinal.2, hsize]
    have := facts.remainderEndBeforeFp
    unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro j hj
    rw [arrayAddressNat remPtr j (by
      exact lt_trans (by
        have := facts.remainderEndBeforeFp
        have := hquotientBound
        omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      hfinal.1]
    have hactive := zeroGeometry.hvActive
    have hvPtrFit : vFp fp m divisorCount < UInt256.size := lt_trans (by
      have := hvBound
      omega : vFp fp m divisorCount < 2 ^ 64) (by norm_num [UInt256.size])
    rw [UInt256.toNat_ofNat_of_lt hvPtrFit] at hactive
    have := facts.remainderEndBeforeFp
    exact le_trans (by
      unfold vFp uFp wordArrayAllocationSize wordArrayPayloadSize
      omega) hactive
  · intro i j hi hj
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      arrayAddressNat (uFp fp m divisorCount) j (by
        exact lt_trans (by
          unfold wordArrayAllocationSize wordArrayPayloadSize at huBound
          omega : uFp fp m divisorCount + 32 * (j + 1) < 2 ^ 64)
          (by norm_num [UInt256.size]))]
    have := facts.remainderEndBeforeFp
    unfold uFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · intro i j hij hj
    rw [arrayAddressNat remPtr i (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (i + 1) < 2 ^ 64) (by norm_num [UInt256.size])),
      arrayAddressNat remPtr j (by
        exact lt_trans (by
          have := facts.remainderEndBeforeFp
          have := hquotientBound
          omega : remPtr + 32 * (j + 1) < 2 ^ 64) (by norm_num [UInt256.size]))]
    omega

end Modexp.MultiLimbBarrettReduceBaseKnuth
