import Examples.Precompiles.Modexp.MultiLimbSchoolbookEstimateExecutable
import Examples.Precompiles.Modexp.MultiLimbSchoolbookIterationComplete

/-!
# Constructive schoolbook quotient-digit selection

This module selects the generated direct or corrected multiply-subtract result from the concrete
borrow flag. It proves the checked correction decrement is safe and reconstructs the quotient
array header facts from the actual below-window memory frame.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookDigitExecutable

open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookDivisionSemantic
open MultiLimbSchoolbookDigitFunction
open MultiLimbSchoolbookIterationFunction
open MultiLimbSchoolbookIterationSemantic
open MultiLimbSchoolbookNormalization
open MultiLimbSchoolbookSingle

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem windowReadSlice_length
    (mem : ByteArray) (aw u : UInt256) (current start count : Nat) :
    (windowReadSlice mem aw u current start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [windowReadSlice, ih]

private theorem divisorReadSlice_length
    (mem : ByteArray) (aw v : UInt256) (start count : Nat) :
    (divisorReadSlice mem aw v start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [divisorReadSlice, ih]

/-- A concrete negative top subtraction implies that the selected q-hat is nonzero, so the
bytecode's checked correction decrement cannot revert. -/
theorem qHat_ne_zero_of_topResult_negative
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hnegative : (topResult mem aw v u (UInt256.ofNat current) qHat count).negative ≠ ⟨0⟩) :
    qHat ≠ ⟨0⟩ := by
  let uLower := windowReadSlice mem aw u current 0 count
  let vDigits := divisorReadSlice mem aw v 0 count
  let uTop := MultiLimbDivisionTrace.readWord mem aw
    (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count))
  let pure := knuthSubtractWindow qHat uLower vDigits uTop
  have hnegativeEq := topResult_negative_eq_knuthSubtractWindow mem aw v u qHat current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive huBelowV
    hawFit
  have hpureNonzero : pure.negative ≠ ⟨0⟩ := by
    intro hpureZero
    apply hnegative
    exact hnegativeEq.symm.trans hpureZero
  have hnegativeBit := evmSubBorrow_borrow_bit uTop
    (knuthSubtractDigits qHat uLower vDigits ⟨0⟩ ⟨0⟩).carry
    (knuthSubtractDigits qHat uLower vDigits ⟨0⟩ ⟨0⟩).borrow
  change pure.negative = ⟨0⟩ ∨ pure.negative = ⟨1⟩ at hnegativeBit
  have hpureOne : pure.negative = ⟨1⟩ := by
    rcases hnegativeBit with hzero | hone
    · exact (hpureNonzero hzero).elim
    · exact hone
  have hlength : uLower.length = vDigits.length := by
    dsimp only [uLower, vDigits]
    rw [windowReadSlice_length, divisorReadSlice_length]
  have hpositive := knuthNegative_qHat_positive qHat uLower vDigits uTop hlength hpureOne
  intro hzero
  subst qHat
  norm_num at hpositive

/-- Every concrete multiply-subtract state satisfying the established allocator geometry has a
direct or corrected digit execution certificate with exact branch gas. -/
theorem validDigit_exists
    {mem : ByteArray} {aw v u qHat quotient : UInt256}
    {current count jj quotientCount : Nat}
    {shift ret rem vTop normalizationMarker : UInt256}
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hjj : jj < quotientCount)
    (hjjWord : jj < UInt256.size)
    (hquotientCountWord : quotientCount < UInt256.size)
    (hquotHeader : MultiLimbSchoolbookNormalization.arrayHeader mem aw quotient =
      UInt256.ofNat quotientCount)
    (hquotHeaderAw : MultiLimbSchoolbookNormalization.arrayAfterHeader aw quotient = aw)
    (hquotElementAw : MultiLimbSchoolbookNormalization.arrayAfterWord aw quotient jj = aw)
    (hquotBelowU : quotient.toNat + 32 ≤ u.toNat + 32 * current) :
    ∃ result, ValidDigit mem aw count jj quotientCount v u (UInt256.ofNat current) qHat
      shift ret rem quotient vTop normalizationMarker result := by
  let top := topResult mem aw v u (UInt256.ofNat current) qHat count
  have htopSemantic := topResult_eq_knuthSubtractWindow mem aw v u qHat current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have htopAw : top.activeWords = aw := by simpa only [top] using htopSemantic.2.2.2
  have htopPhase := topResult_preserves_divisor_and_size mem aw v u qHat current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have htopSize : top.memory.size = mem.size := by simpa only [top] using htopPhase.2
  have htopRead := topResult_read_below_eq mem aw v u qHat current count quotient.toNat
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    hquotBelowU
  have htopHeaderEq : MultiLimbSchoolbookNormalization.arrayHeader top.memory
      top.activeWords quotient =
      MultiLimbSchoolbookNormalization.arrayHeader mem aw quotient := by
    unfold MultiLimbSchoolbookNormalization.arrayHeader
      MultiLimbSchoolbookSingle.arrayHeader MultiLimbSchoolbookShort.arrayHeader
      MultiLimbOddCompare.headerWord
    rw [htopAw]
    exact readWord_eq_of_size_read_eq top.memory mem aw quotient htopSize
      (by simpa only using htopRead)
  by_cases hnegative : top.negative = ⟨0⟩
  · refine ⟨_, ValidDigit.direct hnegative hjj hjjWord hquotientCountWord ?_ ?_ ?_⟩
    · exact htopHeaderEq.trans hquotHeader
    · change MultiLimbSchoolbookNormalization.arrayAfterHeader top.activeWords quotient =
        top.activeWords
      rw [htopAw]
      exact hquotHeaderAw
    · change MultiLimbSchoolbookNormalization.arrayAfterWord top.activeWords quotient jj =
        top.activeWords
      rw [htopAw]
      exact hquotElementAw
  · have hqHat := qHat_ne_zero_of_topResult_negative mem aw v u qHat current count hcurrent
      hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive (by omega)
      hawFit (by simpa only [top] using hnegative)
    let corrected := correctionTop mem aw v u (UInt256.ofNat current) qHat count
    have hcorrectedSemantic := correctionTop_eq_knuthAddBack mem aw v u qHat current count
      hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
      htopActive htopBelowV hawFit
    have hcorrectedAw : corrected.activeWords = aw := by
      simpa only [corrected] using hcorrectedSemantic.2.2.1
    have hcorrectedSize : corrected.memory.size = mem.size := by
      simpa only [corrected] using hcorrectedSemantic.2.2.2
    have hcorrectedRead := correctionTop_read_below_eq mem aw v u qHat current count
      quotient.toNat hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive
      huActive htopMem htopActive htopBelowV hawFit hquotBelowU
    have hcorrectedHeaderEq : MultiLimbSchoolbookNormalization.arrayHeader corrected.memory
        corrected.activeWords quotient =
        MultiLimbSchoolbookNormalization.arrayHeader mem aw quotient := by
      unfold MultiLimbSchoolbookNormalization.arrayHeader
        MultiLimbSchoolbookSingle.arrayHeader MultiLimbSchoolbookShort.arrayHeader
        MultiLimbOddCompare.headerWord
      rw [hcorrectedAw]
      exact readWord_eq_of_size_read_eq corrected.memory mem aw quotient hcorrectedSize
        (by simpa only using hcorrectedRead)
    refine ⟨_, ValidDigit.corrected (by simpa only [top] using hnegative) hqHat hjj hjjWord
      hquotientCountWord ?_ ?_ ?_⟩
    · exact hcorrectedHeaderEq.trans hquotHeader
    · change MultiLimbSchoolbookNormalization.arrayAfterHeader corrected.activeWords quotient =
        corrected.activeWords
      rw [hcorrectedAw]
      exact hquotHeaderAw
    · change MultiLimbSchoolbookNormalization.arrayAfterWord corrected.activeWords quotient jj =
        corrected.activeWords
      rw [hcorrectedAw]
      exact hquotElementAw

end Modexp.MultiLimbSchoolbookDigitExecutable
