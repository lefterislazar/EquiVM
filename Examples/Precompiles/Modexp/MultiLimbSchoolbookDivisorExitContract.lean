import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisorTrimContract

/-!
# Nonzero divisor-trim exit

The generated divisor scan had exact zero-limb cycles and later dispatch contracts, but no
contract for its ordinary nonzero-top-limb exit.  Barrett's converted modulus is expected to take
this path.  This module exposes the missing PC 5237 to PC 5266 segment so the short-dividend and
Knuth branches can be composed without assuming away the scan.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookDivisorExit

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- A positive effective divisor with a nonzero top limb exits the trim loop. -/
theorem nonzeroExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C top count : Nat} {tail : List UInt256}
    {rem dividend ret m divisor value : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (htopPos : 0 < top) (htop : top < count) (hcountBound : count ≤ 32)
    (hheader : MultiLimbSchoolbookDivisorTrim.divisorHeader mem aw divisor =
      UInt256.ofNat count)
    (hheaderAw : MultiLimbSchoolbookDivisorTrim.divisorAfterHeader aw divisor = aw)
    (helementAw : MultiLimbSchoolbookDivisorTrim.divisorAfterWord aw divisor top = aw)
    (hvalue : MultiLimbSchoolbookDivisorTrim.divisorWord mem aw divisor top = value)
    (hvalueNonzero : value ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5237⟩
      (UInt256.ofNat (top + 1) :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5266⟩
      (UInt256.ofNat (top + 1) :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc (k + 55) (C + 202) := by
  have hsmall : count < UInt256.size := by
    have : 32 < UInt256.size := by decide
    omega
  have htopSucc : top + 1 < UInt256.size := by omega
  have hloop : (UInt256.ofNat (top + 1)).gt ⟨1⟩ ≠ ⟨0⟩ := by
    have heq : (UInt256.ofNat (top + 1)).gt ⟨1⟩ = ⟨1⟩ := by
      apply ugt_one
      rw [UInt256.toNat_ofNat_of_lt htopSucc]
      change 1 < top + 1
      omega
    rw [heq]
    native_decide
  have rd6383 := GeneratedTraces.trace_5237_taken
    (tail := rem :: dividend :: ret :: m :: divisor :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hloop (by native_decide)
  have hprev : MultiLimbOddCompare.previousIndex (UInt256.ofNat (top + 1)) =
      UInt256.ofNat top := by
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (top + 1)) = UInt256.ofNat top
    exact MultiLimbOddCompare.scanIndex_ofNat_succ top htopSucc
  have hdecIndex :
      UInt256.ofNat (top + 1) + (⟨0⟩ : UInt256).lnot = UInt256.ofNat top := by
    rw [u256_add_comm]
    exact hprev
  have hnoUnderflow :
      (UInt256.ofNat (top + 1) + (⟨0⟩ : UInt256).lnot).gt
        (UInt256.ofNat (top + 1)) = ⟨0⟩ := by
    rw [hdecIndex]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (by omega : top < UInt256.size),
      UInt256.toNat_ofNat_of_lt htopSucc]
    omega
  have rd1036 := GeneratedTraces.trace_6376_notTaken
    (by simp only [List.length_cons]; omega) rd6383 (by native_decide) hnoUnderflow
  have rd6396 := GeneratedTraces.trace_1036_jump
    (by simp only [List.length_cons]; omega) rd1036
    (by native_decide) (by native_decide)
  have harrayBound :
      (UInt256.ofNat top).lt
        (MultiLimbSchoolbookDivisorTrim.divisorHeader mem aw divisor) ≠ ⟨0⟩ := by
    rw [hheader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt (by omega : top < UInt256.size),
        UInt256.toNat_ofNat_of_lt hsmall]
      exact htop
  have harrayCondition :
      ((UInt256.ofNat (top + 1) + (⟨0⟩ : UInt256).lnot).lt
        (MultiLimbOddCompare.headerWord mem aw divisor)).isZero = ⟨0⟩ := by
    rw [hdecIndex]
    have harrayBound' :
        (UInt256.ofNat top).lt
          (MultiLimbOddCompare.headerWord mem aw divisor) ≠ ⟨0⟩ := harrayBound
    simp [UInt256.isZero, UInt256.eq0, harrayBound', Bool.toUInt256]
    native_decide
  have rd1539 := GeneratedTraces.trace_6389_notTaken
    (by omega) rd6396 (by native_decide) harrayCondition
  have hheaderAw' : MultiLimbOddCompare.afterHeader aw divisor = aw := hheaderAw
  rw [hdecIndex, ← MultiLimbOddCompare.afterHeader_generated, hheaderAw'] at rd1539
  have rd6402 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539
    (by native_decide) (by native_decide)
  have rd5252 := GeneratedTraces.trace_6395_body
    (by simp only [List.length_cons]; omega) rd6402
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd5252
  have hvalueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat top).shiftLeft ⟨5⟩ + divisor + ⟨32⟩) = value := by
    simpa only [MultiLimbSchoolbookDivisorTrim.divisorWord,
      MultiLimbOddCompare.loadedWord,
      MultiLimbSchoolbookDivisorTrim.divisorAddress,
      MultiLimbOddCompare.elementPtr] using hvalue
  have helementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat top).shiftLeft ⟨5⟩ + divisor + ⟨32⟩) = aw := by
    simpa only [MultiLimbSchoolbookDivisorTrim.divisorAfterWord,
      MultiLimbOddCompare.afterLoad,
      MultiLimbSchoolbookDivisorTrim.divisorAddress,
      MultiLimbOddCompare.elementPtr] using helementAw
  rw [hvalueRaw, helementAwRaw] at rd5252
  have hcondition : value.isZero.isZero ≠ ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hvalueNonzero, Bool.toUInt256]
    native_decide
  have rd5266 := rd5252.jumpiT (by native_decide) hcondition
    (by native_decide) (by simp only [List.length_cons]; omega)
  have normalized := rd5266.withIndices
    (k' := k + 55) (C' := C + 202) (by omega) (by omega)
  exact normalized

end Modexp.MultiLimbSchoolbookDivisorExit
