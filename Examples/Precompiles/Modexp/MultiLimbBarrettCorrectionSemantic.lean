import Examples.Precompiles.Modexp.MultiLimbBarrettCorrectionContract
import Examples.Precompiles.Modexp.MultiLimbBarrettSubtractSemantic
import Examples.Precompiles.Modexp.MultiLimbMontgomeryFinalize
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeLinks
import Examples.Precompiles.Modexp.MultiLimbBarrettModel

/-!
# Barrett correction semantics

This module identifies the exposed correction selectors with numeric limb comparison and the
pure subtraction model.  The first layer deliberately describes the words actually observed by
the evolving-memory loads; allocator geometry can then identify those collectors with the source
arrays without weakening the execution theorem.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbBarrettCorrectionSemantic

open Modexp.MultiLimbBarrettCompare
open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbSchoolbookMulTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbBarrettCorrection

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

/-- The comparison trace's literal pointer expression is the shared Solidity array-element
pointer. -/
theorem comparePtr_eq_elementPtr (array : UInt256) (iWords : Nat) :
    comparePtr array iWords = elementPtr array (compareIndex iWords) := by
  simp only [comparePtr, elementPtr]
  rw [u256_add_comm array]

/-- Complete candidate words observed by a descending comparison, returned in little-endian
order.  Active memory words evolve in exactly the same order as the deployed loads. -/
def compareCandidateWords (mem : ByteArray) (n r2 : UInt256) :
    UInt256 → Nat → List UInt256
  | _, 0 => []
  | aw, count + 1 =>
      compareCandidateWords mem n r2 (compareWords aw n r2 (count + 1)) count ++
        [compareLeft mem aw r2 (count + 1)]

/-- Complete modulus words observed alongside `compareCandidateWords`. -/
def compareModulusWords (mem : ByteArray) (n r2 : UInt256) :
    UInt256 → Nat → List UInt256
  | _, 0 => []
  | aw, count + 1 =>
      compareModulusWords mem n r2 (compareWords aw n r2 (count + 1)) count ++
        [compareRight mem aw n r2 (count + 1)]

@[simp] theorem compareCandidateWords_length
    (mem : ByteArray) (n r2 aw : UInt256) (count : Nat) :
    (compareCandidateWords mem n r2 aw count).length = count := by
  induction count generalizing aw with
  | zero => rfl
  | succ count ih => simp [compareCandidateWords, ih]

@[simp] theorem compareModulusWords_length
    (mem : ByteArray) (n r2 aw : UInt256) (count : Nat) :
    (compareModulusWords mem n r2 aw count).length = count := by
  induction count generalizing aw with
  | zero => rfl
  | succ count ih => simp [compareModulusWords, ih]

private theorem append_high_gt
    (leftLow rightLow : List UInt256) (leftHigh rightHigh : UInt256)
    (hlength : leftLow.length = rightLow.length)
    (hhigh : rightHigh.toNat < leftHigh.toNat) :
    Modexp.wordLimbsToNat (rightLow ++ [rightHigh]) <
      Modexp.wordLimbsToNat (leftLow ++ [leftHigh]) := by
  rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append, hlength]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
  have hleftBound := Modexp.wordLimbsToNat_lt_pow leftLow
  have hrightBound := Modexp.wordLimbsToNat_lt_pow rightLow
  have hpowPos : 0 < UInt256.size ^ rightLow.length :=
    Nat.pow_pos (by norm_num [UInt256.size])
  nlinarith

private theorem append_equal_high_le_iff
    (leftLow rightLow : List UInt256) (high : UInt256)
    (hlength : leftLow.length = rightLow.length) :
    Modexp.wordLimbsToNat (rightLow ++ [high]) ≤
        Modexp.wordLimbsToNat (leftLow ++ [high]) ↔
      Modexp.wordLimbsToNat rightLow ≤ Modexp.wordLimbsToNat leftLow := by
  rw [Modexp.wordLimbsToNat_append, Modexp.wordLimbsToNat_append, hlength]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
  omega

/-- A successful descending selector chooses subtraction exactly when its complete observed
candidate is greater than or equal to its complete observed modulus. -/
theorem selectedBarrettCompare_doSub_iff_words
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords iWords : Nat} {selected : BarrettCompareSelection}
    (hiPos : 0 < iWords)
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords iWords =
      some selected) :
    selected.doSub = true ↔
      Modexp.wordLimbsToNat (compareModulusWords mem n r2 aw iWords) ≤
        Modexp.wordLimbsToNat (compareCandidateWords mem n r2 aw iWords) := by
  induction fuel generalizing aw iWords selected with
  | zero => simp [selectBarrettCompare] at hselect
  | succ fuel ih =>
      simp only [selectBarrettCompare] at hselect
      let left := compareLeft mem aw r2 iWords
      let right := compareRight mem aw n r2 iWords
      let nextAw := compareWords aw n r2 iWords
      by_cases hgreater : right.toNat < left.toNat
      · rw [if_pos hgreater] at hselect
        injection hselect with heq
        subst selected
        cases iWords with
        | zero => omega
        | succ count =>
            simp only [compareCandidateWords, compareModulusWords]
            have hgt := append_high_gt
              (compareCandidateWords mem n r2 nextAw count)
              (compareModulusWords mem n r2 nextAw count) left right
              (by simp) hgreater
            simpa [nextAw, left, right] using hgt.le
      · rw [if_neg hgreater] at hselect
        by_cases hless : left.toNat < right.toNat
        · rw [if_pos hless] at hselect
          injection hselect with heq
          subst selected
          cases iWords with
          | zero => omega
          | succ count =>
              simp only [compareCandidateWords, compareModulusWords, Bool.false_eq_true]
              have hlt := append_high_gt
                (compareModulusWords mem n r2 nextAw count)
                (compareCandidateWords mem n r2 nextAw count) right left
                (by simp) hless
              constructor
              · intro hfalse
                contradiction
              · intro hle
                exact (not_le_of_gt (by simpa [nextAw, left, right] using hlt)) hle
        · rw [if_neg hless] at hselect
          have hequal : left = right := by
            apply u256_inj
            omega
          by_cases hiOne : iWords = 1
          · rw [if_pos hiOne] at hselect
            injection hselect with heq
            subst selected
            subst iWords
            simp [compareCandidateWords, compareModulusWords, left, right, hequal]
          · rw [if_neg hiOne] at hselect
            cases hrest : selectBarrettCompare fuel mem nextAw n r2 result kWords
                (iWords - 1) with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heqSelection
                subst selected
                have hiRest : 0 < iWords - 1 := by omega
                have ihRest := ih hiRest hrest
                cases iWords with
                | zero => omega
                | succ count =>
                    have hcount : count + 1 - 1 = count := by omega
                    simp only [compareCandidateWords, compareModulusWords]
                    change rest.doSub = true ↔
                      Modexp.wordLimbsToNat
                          (compareModulusWords mem n r2 nextAw count ++ [right]) ≤
                        Modexp.wordLimbsToNat
                          (compareCandidateWords mem n r2 nextAw count ++ [left])
                    rw [hequal, append_equal_high_le_iff (hlength := by simp)]
                    simpa only [hcount] using ihRest

/-- Under ordinary covered Solidity-array geometry, the evolving descending loads observe the
complete r2 and modulus payloads. -/
theorem compareCollectors_eq_memoryWordsFrom
    (count : Nat) (mem : ByteArray) (aw n r2 : UInt256)
    (hr2Fit : r2.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (count + 1) ≤ mem.size)
    (hnMem : n.toNat + 32 * (count + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    compareCandidateWords mem n r2 aw count =
        memoryWordsFrom mem (r2.toNat + 32) count ∧
      compareModulusWords mem n r2 aw count =
        memoryWordsFrom mem (n.toNat + 32) count := by
  induction count generalizing aw with
  | zero => simp [compareCandidateWords, compareModulusWords, memoryWordsFrom]
  | succ count ih =>
      have hindex : compareIndex (count + 1) = UInt256.ofNat count := by
        simp [compareIndex]
      have hr2Address : (comparePtr r2 (count + 1)).toNat =
          r2.toNat + 32 * (count + 1) := by
        rw [comparePtr_eq_elementPtr, hindex]
        change (Modexp.MultiLimbOddCompare.elementPtr r2
          (UInt256.ofNat count)).toNat = _
        exact Modexp.MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit r2 count
          (by omega)
      have hnAddress : (comparePtr n (count + 1)).toNat =
          n.toNat + 32 * (count + 1) := by
        rw [comparePtr_eq_elementPtr, hindex]
        change (Modexp.MultiLimbOddCompare.elementPtr n
          (UInt256.ofNat count)).toNat = _
        exact Modexp.MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit n count
          (by omega)
      have hleftCoverage := readWords1_coverage mem aw (comparePtr r2 (count + 1))
        hcovered hawFit (by rw [hr2Address]; omega)
      have hrightCoverage := readWords1_coverage mem
        (compareAfterLeft aw r2 (count + 1)) (comparePtr n (count + 1))
        (by simpa [compareAfterLeft] using hleftCoverage.1)
        (by simpa [compareAfterLeft] using hleftCoverage.2)
        (by rw [hnAddress]; omega)
      have hleftWord : compareLeft mem aw r2 (count + 1) =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
            (r2.toNat + 32 * (count + 1))) := by
        have hread := readWord_eq_memoryWordOf_covered mem aw
          (comparePtr r2 (count + 1)) hcovered hawFit (by rw [hr2Address]; omega)
        simpa [compareLeft, hr2Address] using hread
      have hrightWord : compareRight mem aw n r2 (count + 1) =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
            (n.toNat + 32 * (count + 1))) := by
        have hread := readWord_eq_memoryWordOf_covered mem
          (compareAfterLeft aw r2 (count + 1)) (comparePtr n (count + 1))
          (by simpa [compareAfterLeft] using hleftCoverage.1)
          (by simpa [compareAfterLeft] using hleftCoverage.2)
          (by rw [hnAddress]; omega)
        simpa [compareRight, hnAddress] using hread
      have hrest := ih (compareWords aw n r2 (count + 1))
        (by omega) (by omega) (by omega) (by omega)
        (by simpa [compareWords, compareAfterLeft] using hrightCoverage.1)
        (by simpa [compareWords, compareAfterLeft] using hrightCoverage.2)
      constructor
      · simp only [compareCandidateWords]
        rw [hrest.1, hleftWord, memoryWordsFrom_succ_eq_append]
        have hoff : r2.toNat + 32 + 32 * count =
            r2.toNat + 32 * (count + 1) := by omega
        rw [hoff]
      · simp only [compareModulusWords]
        rw [hrest.2, hrightWord, memoryWordsFrom_succ_eq_append]
        have hoff : n.toNat + 32 + 32 * count =
            n.toNat + 32 * (count + 1) := by omega
        rw [hoff]

/-- With covered array geometry, the exposed selector is ordinary comparison of the concrete
Solidity payload values. -/
theorem selectedBarrettCompare_doSub_iff_memoryWords
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords)
    (hr2Fit : r2.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords kWords =
      some selected) :
    selected.doSub = true ↔
      Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords) ≤
        Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) := by
  have hwords := compareCollectors_eq_memoryWordsFrom kWords mem aw n r2
    hr2Fit hnFit hr2Mem hnMem hcovered hawFit
  rw [← hwords.1, ← hwords.2]
  exact selectedBarrettCompare_doSub_iff_words hkPos hselect

/-- The final Barrett `MCOPY` preserves covered representable memory and the concrete allocated
size when both its source and target payloads are already materialized. -/
theorem barrettFinal_coverage_size
    (count : Nat) (mem : ByteArray) (aw r2 result : UInt256)
    (hcount : 0 < count) (hcountFit : count < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hsource : r2.toNat + 32 + 32 * count <= mem.size)
    (htarget : result.toNat + 32 + 32 * count <= mem.size)
    (hr2AccessFit : r2.toNat + 32 + 32 * count + 31 < UInt256.size)
    (hresultAccessFit : result.toNat + 32 + 32 * count + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MemoryCovered (barrettFinalMemory mem r2 result count)
        (barrettFinalWords aw r2 result count) /\
      (barrettFinalWords aw r2 result count).toNat * 32 < UInt256.size /\
      (barrettFinalMemory mem r2 result count).size = mem.size := by
  have hbytes : (barrettCopyBytes count).toNat = 32 * count := by
    unfold barrettCopyBytes
    exact ushl5_ofNat_toNat count hcountFit
  have hsrc : (barrettCopySource r2).toNat = r2.toNat + 32 := by
    unfold barrettCopySource
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hr2Fit]
  have hdest : (barrettCopyTarget result).toNat = result.toNat + 32 := by
    unfold barrettCopyTarget
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hresultFit]
  have haccess : max (barrettCopyTarget result).toNat
        (barrettCopySource r2).toNat + (barrettCopyBytes count).toNat + 31 <
      UInt256.size := by
    rw [hsrc, hdest, hbytes]
    omega
  have hgeometry := finalCopy_coverage mem aw (barrettCopySource r2)
    (barrettCopyTarget result) (barrettCopyBytes count)
    (by rw [hbytes]; omega) (by rw [hsrc, hbytes]; omega)
    (by rw [hdest, hbytes]; omega) hcovered hawFit haccess
  have hsize := finalCopyMemory_size mem (barrettCopySource r2)
    (barrettCopyTarget result) (barrettCopyBytes count)
    (by rw [hbytes]; omega) (by rw [hsrc, hbytes]; omega)
    (by rw [hdest, hbytes]; omega)
  simpa [barrettFinalMemory, barrettFinalWords, finalCopyMemory, finalCopyAw] using
    And.intro hgeometry.1 (And.intro hgeometry.2 hsize)

/-- The first Barrett call may have materialized only the result header.  Its final copy extends
concrete memory through the result payload while retaining exact active-word coverage. -/
theorem barrettFinal_coverage_size_from_start
    (count : Nat) (mem : ByteArray) (aw r2 result : UInt256)
    (hcount : 0 < count) (hcountFit : count < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hsource : r2.toNat + 32 + 32 * count ≤ mem.size)
    (htarget : result.toNat + 32 ≤ mem.size)
    (hr2AccessFit : r2.toNat + 32 + 32 * count + 31 < UInt256.size)
    (hresultAccessFit : result.toNat + 32 + 32 * count + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MemoryCovered (barrettFinalMemory mem r2 result count)
        (barrettFinalWords aw r2 result count) ∧
      (barrettFinalWords aw r2 result count).toNat * 32 < UInt256.size ∧
      (barrettFinalMemory mem r2 result count).size =
        max mem.size (result.toNat + 32 + 32 * count) := by
  have hbytes : (barrettCopyBytes count).toNat = 32 * count := by
    unfold barrettCopyBytes
    exact ushl5_ofNat_toNat count hcountFit
  have hsrc : (barrettCopySource r2).toNat = r2.toNat + 32 := by
    unfold barrettCopySource
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hr2Fit]
  have hdest : (barrettCopyTarget result).toNat = result.toNat + 32 := by
    unfold barrettCopyTarget
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hresultFit]
  have haccess : max (barrettCopyTarget result).toNat
        (barrettCopySource r2).toNat + (barrettCopyBytes count).toNat + 31 <
      UInt256.size := by
    rw [hsrc, hdest, hbytes]
    omega
  have hgeometry := finalCopy_coverage_from_start mem aw (barrettCopySource r2)
    (barrettCopyTarget result) (barrettCopyBytes count)
    (by rw [hbytes]; omega) (by rw [hsrc, hbytes]; omega)
    (by rw [hdest]; omega) hcovered hawFit haccess
  have hsize := finalCopyMemory_size_from_start mem (barrettCopySource r2)
    (barrettCopyTarget result) (barrettCopyBytes count)
    (by rw [hbytes]; omega) (by rw [hsrc, hbytes]; omega) (by rw [hdest]; omega)
  refine ⟨by simpa [barrettFinalMemory, barrettFinalWords, finalCopyMemory, finalCopyAw]
      using hgeometry.1,
    by simpa [barrettFinalWords, finalCopyAw] using hgeometry.2, ?_⟩
  change (finalCopyMemory mem (barrettCopySource r2) (barrettCopyTarget result)
    (barrettCopyBytes count)).size = _
  simpa [hdest, hbytes, Nat.add_assoc] using hsize

/-- The final correction copy does not change a complete word range below its target payload. -/
theorem barrettFinalMemory_words_below
    (count : Nat) (mem : ByteArray) (r2 result : UInt256) (ptr words : Nat)
    (hcount : 0 < count) (hcountFit : count < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hsource : r2.toNat + 32 + 32 * count <= mem.size)
    (htarget : result.toNat + 32 <= mem.size)
    (hread : ptr + 32 * words <= mem.size)
    (hbelow : ptr + 32 * words <= result.toNat + 32) :
    memoryWordsFrom (barrettFinalMemory mem r2 result count) ptr words =
      memoryWordsFrom mem ptr words := by
  have hbytes : (barrettCopyBytes count).toNat = 32 * count := by
    unfold barrettCopyBytes
    exact ushl5_ofNat_toNat count hcountFit
  have hsrc : (barrettCopySource r2).toNat = r2.toNat + 32 := by
    unfold barrettCopySource
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hr2Fit]
  have hdest : (barrettCopyTarget result).toNat = result.toNat + 32 := by
    unfold barrettCopyTarget
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hresultFit]
  have hframe := memoryWordsFrom_finalCopy_below words mem (barrettCopySource r2)
    (barrettCopyTarget result) (barrettCopyBytes count) ptr
    (by rw [hbytes]; omega) (by rw [hsrc, hbytes]; omega)
    (by rw [hdest]; omega) hread (by rw [hdest]; omega)
  simpa [barrettFinalMemory, finalCopyMemory] using hframe

theorem elementPtr_ofNat_toNat_of_fit (array : UInt256) (i : Nat)
    (hfit : array.toNat + 32 * (i + 1) < UInt256.size) :
    (elementPtr array (UInt256.ofNat i)).toNat = array.toNat + 32 * (i + 1) := by
  change (Modexp.MultiLimbOddCompare.elementPtr array (UInt256.ofNat i)).toNat = _
  exact Modexp.MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit array i hfit

/-- A successful comparison that selects subtraction has only read memory.  Its returned active
word count therefore covers the unchanged memory and remains representable. -/
theorem selectedBarrettCompare_true_geometry
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords iWords : Nat} {selected : BarrettCompareSelection}
    (hiPos : 0 < iWords)
    (hr2Fit : r2.toNat + 32 * (iWords + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (iWords + 1) + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords iWords =
      some selected)
    (htrue : selected.doSub = true) :
    selected.memory = mem ∧ MemoryCovered mem selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size := by
  induction fuel generalizing aw iWords selected with
  | zero => simp [selectBarrettCompare] at hselect
  | succ fuel ih =>
      cases iWords with
      | zero => omega
      | succ count =>
          simp only [selectBarrettCompare] at hselect
          let left := compareLeft mem aw r2 (count + 1)
          let right := compareRight mem aw n r2 (count + 1)
          let nextAw := compareWords aw n r2 (count + 1)
          have hindex : compareIndex (count + 1) = UInt256.ofNat count := by
            simp [compareIndex]
          have hr2Address : (comparePtr r2 (count + 1)).toNat =
              r2.toNat + 32 * (count + 1) := by
            rw [comparePtr_eq_elementPtr, hindex]
            exact elementPtr_ofNat_toNat_of_fit r2 count (by omega)
          have hnAddress : (comparePtr n (count + 1)).toNat =
              n.toNat + 32 * (count + 1) := by
            rw [comparePtr_eq_elementPtr, hindex]
            exact elementPtr_ofNat_toNat_of_fit n count (by omega)
          have hleftCoverage := readWords1_coverage mem aw
            (comparePtr r2 (count + 1)) hcovered hawFit (by
              rw [hr2Address]
              omega)
          have hrightCoverage := readWords1_coverage mem
            (compareAfterLeft aw r2 (count + 1)) (comparePtr n (count + 1))
            (by simpa [compareAfterLeft] using hleftCoverage.1)
            (by simpa [compareAfterLeft] using hleftCoverage.2)
            (by rw [hnAddress]; omega)
          by_cases hgreater : right.toNat < left.toNat
          · rw [if_pos hgreater] at hselect
            injection hselect with heq
            subst selected
            exact ⟨rfl, by simpa [nextAw, compareWords] using hrightCoverage.1,
              by simpa [nextAw, compareWords] using hrightCoverage.2⟩
          · rw [if_neg hgreater] at hselect
            by_cases hless : left.toNat < right.toNat
            · rw [if_pos hless] at hselect
              injection hselect with heq
              subst selected
              contradiction
            · rw [if_neg hless] at hselect
              by_cases hiOne : count + 1 = 1
              · rw [if_pos hiOne] at hselect
                injection hselect with heq
                subst selected
                exact ⟨rfl, by simpa [nextAw, compareWords] using hrightCoverage.1,
                  by simpa [nextAw, compareWords] using hrightCoverage.2⟩
              · rw [if_neg hiOne] at hselect
                cases hrest : selectBarrettCompare fuel mem nextAw n r2 result kWords
                    (count + 1 - 1) with
                | none => rw [hrest] at hselect; contradiction
                | some rest =>
                    rw [hrest] at hselect
                    injection hselect with heq
                    subst selected
                    have hrestTrue : rest.doSub = true := by simpa using htrue
                    exact ih (aw := nextAw) (iWords := count + 1 - 1)
                      (selected := rest) (by omega) (by omega) (by omega)
                      (by simpa [nextAw, compareWords] using hrightCoverage.1)
                      (by simpa [nextAw, compareWords] using hrightCoverage.2)
                      hrest hrestTrue

/-- The complete top-word decision preserves valid read geometry whenever it requests a
subtraction pass. -/
theorem selectedBarrettDecision_true_geometry
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (htrue : selected.doSub = true) :
    selected.memory = mem ∧ MemoryCovered mem selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size := by
  let topPtr := correctionTopPtr r2 kWords
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  have htopAddress : topPtr.toNat = r2.toNat + 32 * (kWords + 1) := by
    simpa [topPtr, correctionTopPtr] using
      elementPtr_ofNat_toNat_of_fit r2 kWords (by omega)
  have htopCoverage := readWords1_coverage mem aw topPtr hcovered hawFit
    (by rw [htopAddress]; omega)
  simp only [selectBarrettDecision] at hselect
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop] at hselect
    injection hselect with heq
    subst selected
    exact ⟨rfl,
      by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr] using htopCoverage.1,
      by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr] using htopCoverage.2⟩
  · rw [if_neg htop] at hselect
    cases hcompare : selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => rw [hcompare] at hselect; contradiction
    | some rest =>
        rw [hcompare] at hselect
        injection hselect with heq
        subst selected
        have hrestTrue : rest.doSub = true := by simpa using htrue
        have hgeometry := selectedBarrettCompare_true_geometry
          (fuel := fuel) (mem := mem) (aw := topAw) (n := n) (r2 := r2)
          (result := result) (kWords := kWords) (iWords := kWords)
          (selected := rest) hkPos (by omega) hnFit
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.1)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.2)
          hcompare hrestTrue
        simpa using hgeometry

/-- A descending comparison that exits through the final copy preserves covered memory and its
concrete size. -/
theorem selectedBarrettCompare_false_geometry
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords iWords : Nat} {selected : BarrettCompareSelection}
    (hiPos : 0 < iWords)
    (hr2Fit : r2.toNat + 32 * (iWords + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (iWords + 1) + 31 < UInt256.size)
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2CopyFit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hsource : r2.toNat + 32 + 32 * kWords <= mem.size)
    (htarget : result.toNat + 32 + 32 * kWords <= mem.size)
    (hr2AccessFit : r2.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hresultAccessFit : result.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords iWords =
      some selected)
    (hfalse : selected.doSub = false) :
    MemoryCovered selected.memory selected.activeWords /\
      selected.activeWords.toNat * 32 < UInt256.size /\
      selected.memory.size = mem.size := by
  induction fuel generalizing aw iWords selected with
  | zero => simp [selectBarrettCompare] at hselect
  | succ fuel ih =>
      cases iWords with
      | zero => omega
      | succ count =>
          simp only [selectBarrettCompare] at hselect
          let left := compareLeft mem aw r2 (count + 1)
          let right := compareRight mem aw n r2 (count + 1)
          let nextAw := compareWords aw n r2 (count + 1)
          have hindex : compareIndex (count + 1) = UInt256.ofNat count := by
            simp [compareIndex]
          have hr2Address : (comparePtr r2 (count + 1)).toNat =
              r2.toNat + 32 * (count + 1) := by
            rw [comparePtr_eq_elementPtr, hindex]
            exact elementPtr_ofNat_toNat_of_fit r2 count (by omega)
          have hnAddress : (comparePtr n (count + 1)).toNat =
              n.toNat + 32 * (count + 1) := by
            rw [comparePtr_eq_elementPtr, hindex]
            exact elementPtr_ofNat_toNat_of_fit n count (by omega)
          have hleftCoverage := readWords1_coverage mem aw
            (comparePtr r2 (count + 1)) hcovered hawFit (by
              rw [hr2Address]
              omega)
          have hrightCoverage := readWords1_coverage mem
            (compareAfterLeft aw r2 (count + 1)) (comparePtr n (count + 1))
            (by simpa [compareAfterLeft] using hleftCoverage.1)
            (by simpa [compareAfterLeft] using hleftCoverage.2)
            (by rw [hnAddress]; omega)
          have hnextCovered : MemoryCovered mem nextAw := by
            simpa [nextAw, compareWords] using hrightCoverage.1
          have hnextFit : nextAw.toNat * 32 < UInt256.size := by
            simpa [nextAw, compareWords] using hrightCoverage.2
          by_cases hgreater : right.toNat < left.toNat
          · rw [if_pos hgreater] at hselect
            injection hselect with heq
            subst selected
            contradiction
          · rw [if_neg hgreater] at hselect
            by_cases hless : left.toNat < right.toNat
            · rw [if_pos hless] at hselect
              injection hselect with heq
              subst selected
              simpa using barrettFinal_coverage_size kWords mem nextAw r2 result
                hkPos hkShift hr2CopyFit hresultFit hsource htarget hr2AccessFit
                hresultAccessFit hnextCovered hnextFit
            · rw [if_neg hless] at hselect
              by_cases hiOne : count + 1 = 1
              · rw [if_pos hiOne] at hselect
                injection hselect with heq
                subst selected
                contradiction
              · rw [if_neg hiOne] at hselect
                cases hrest : selectBarrettCompare fuel mem nextAw n r2 result kWords
                    (count + 1 - 1) with
                | none => rw [hrest] at hselect; contradiction
                | some rest =>
                    rw [hrest] at hselect
                    injection hselect with heq
                    subst selected
                    have hrestFalse : rest.doSub = false := by simpa using hfalse
                    exact ih (aw := nextAw) (iWords := count + 1 - 1)
                      (selected := rest) (by omega) (by omega) (by omega) hnextCovered
                      hnextFit hrest hrestFalse

/-- A complete top-word decision that declines subtraction has executed a covered in-bounds final
copy and preserves the concrete memory size. -/
theorem selectedBarrettDecision_false_geometry
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) <= mem.size)
    (hresultMem : result.toNat + 32 + 32 * kWords <= mem.size)
    (hresultAccessFit : result.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (hfalse : selected.doSub = false) :
    MemoryCovered selected.memory selected.activeWords /\
      selected.activeWords.toNat * 32 < UInt256.size /\
      selected.memory.size = mem.size := by
  let topPtr := correctionTopPtr r2 kWords
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  have htopAddress : topPtr.toNat = r2.toNat + 32 * (kWords + 1) := by
    simpa [topPtr, correctionTopPtr] using
      elementPtr_ofNat_toNat_of_fit r2 kWords (by omega)
  have htopCoverage := readWords1_coverage mem aw topPtr hcovered hawFit
    (by rw [htopAddress]; omega)
  simp only [selectBarrettDecision] at hselect
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop] at hselect
    injection hselect with heq
    subst selected
    contradiction
  · rw [if_neg htop] at hselect
    cases hcompare : selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => rw [hcompare] at hselect; contradiction
    | some rest =>
        rw [hcompare] at hselect
        injection hselect with heq
        subst selected
        have hrestFalse : rest.doSub = false := by simpa using hfalse
        exact selectedBarrettCompare_false_geometry
          (mem := mem) (aw := topAw) (n := n) (r2 := r2) (result := result)
          (kWords := kWords) (iWords := kWords) (selected := rest)
          hkPos (by omega) hnFit hkPos hkShift
          (hr2CopyFit := by omega) (hresultFit := hresultFit)
          (hsource := by omega) (htarget := hresultMem)
          (hr2AccessFit := by omega) (hresultAccessFit := hresultAccessFit)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.1)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.2)
          hcompare hrestFalse

/-- A descending comparison may finish by extending a header-only result allocation. -/
theorem selectedBarrettCompare_false_geometry_from_start
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords iWords : Nat} {selected : BarrettCompareSelection}
    (hiPos : 0 < iWords)
    (hr2Fit : r2.toNat + 32 * (iWords + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (iWords + 1) + 31 < UInt256.size)
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2CopyFit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hsource : r2.toNat + 32 + 32 * kWords ≤ mem.size)
    (htarget : result.toNat + 32 ≤ mem.size)
    (hr2AccessFit : r2.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hresultAccessFit : result.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords iWords =
      some selected)
    (hfalse : selected.doSub = false) :
    MemoryCovered selected.memory selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size ∧
      selected.memory.size = max mem.size (result.toNat + 32 + 32 * kWords) := by
  induction fuel generalizing aw iWords selected with
  | zero => simp [selectBarrettCompare] at hselect
  | succ fuel ih =>
      cases iWords with
      | zero => omega
      | succ count =>
          simp only [selectBarrettCompare] at hselect
          let left := compareLeft mem aw r2 (count + 1)
          let right := compareRight mem aw n r2 (count + 1)
          let nextAw := compareWords aw n r2 (count + 1)
          have hindex : compareIndex (count + 1) = UInt256.ofNat count := by
            simp [compareIndex]
          have hr2Address : (comparePtr r2 (count + 1)).toNat =
              r2.toNat + 32 * (count + 1) := by
            rw [comparePtr_eq_elementPtr, hindex]
            exact elementPtr_ofNat_toNat_of_fit r2 count (by omega)
          have hnAddress : (comparePtr n (count + 1)).toNat =
              n.toNat + 32 * (count + 1) := by
            rw [comparePtr_eq_elementPtr, hindex]
            exact elementPtr_ofNat_toNat_of_fit n count (by omega)
          have hleftCoverage := readWords1_coverage mem aw
            (comparePtr r2 (count + 1)) hcovered hawFit (by rw [hr2Address]; omega)
          have hrightCoverage := readWords1_coverage mem
            (compareAfterLeft aw r2 (count + 1)) (comparePtr n (count + 1))
            (by simpa [compareAfterLeft] using hleftCoverage.1)
            (by simpa [compareAfterLeft] using hleftCoverage.2)
            (by rw [hnAddress]; omega)
          have hnextCovered : MemoryCovered mem nextAw := by
            simpa [nextAw, compareWords] using hrightCoverage.1
          have hnextFit : nextAw.toNat * 32 < UInt256.size := by
            simpa [nextAw, compareWords] using hrightCoverage.2
          by_cases hgreater : right.toNat < left.toNat
          · rw [if_pos hgreater] at hselect
            injection hselect with heq
            subst selected
            contradiction
          · rw [if_neg hgreater] at hselect
            by_cases hless : left.toNat < right.toNat
            · rw [if_pos hless] at hselect
              injection hselect with heq
              subst selected
              simpa using barrettFinal_coverage_size_from_start kWords mem nextAw r2 result
                hkPos hkShift hr2CopyFit hresultFit hsource htarget hr2AccessFit
                hresultAccessFit hnextCovered hnextFit
            · rw [if_neg hless] at hselect
              by_cases hiOne : count + 1 = 1
              · rw [if_pos hiOne] at hselect
                injection hselect with heq
                subst selected
                contradiction
              · rw [if_neg hiOne] at hselect
                cases hrest : selectBarrettCompare fuel mem nextAw n r2 result kWords
                    (count + 1 - 1) with
                | none => rw [hrest] at hselect; contradiction
                | some rest =>
                    rw [hrest] at hselect
                    injection hselect with heq
                    subst selected
                    have hrestFalse : rest.doSub = false := by simpa using hfalse
                    exact ih (aw := nextAw) (iWords := count + 1 - 1)
                      (selected := rest) (by omega) (by omega) (by omega) hnextCovered
                      hnextFit hrest hrestFalse

/-- A complete false decision supports the same extending-copy geometry. -/
theorem selectedBarrettDecision_false_geometry_from_start
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hresultMem : result.toNat + 32 ≤ mem.size)
    (hresultAccessFit : result.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (hfalse : selected.doSub = false) :
    MemoryCovered selected.memory selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size ∧
      selected.memory.size = max mem.size (result.toNat + 32 + 32 * kWords) := by
  let topPtr := correctionTopPtr r2 kWords
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  have htopAddress : topPtr.toNat = r2.toNat + 32 * (kWords + 1) := by
    simpa [topPtr, correctionTopPtr] using
      elementPtr_ofNat_toNat_of_fit r2 kWords (by omega)
  have htopCoverage := readWords1_coverage mem aw topPtr hcovered hawFit
    (by rw [htopAddress]; omega)
  simp only [selectBarrettDecision] at hselect
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop] at hselect
    injection hselect with heq
    subst selected
    contradiction
  · rw [if_neg htop] at hselect
    cases hcompare : selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => rw [hcompare] at hselect; contradiction
    | some rest =>
        rw [hcompare] at hselect
        injection hselect with heq
        subst selected
        have hrestFalse : rest.doSub = false := by simpa using hfalse
        exact selectedBarrettCompare_false_geometry_from_start
          (mem := mem) (aw := topAw) (n := n) (r2 := r2) (result := result)
          (kWords := kWords) (iWords := kWords) (selected := rest)
          hkPos (by omega) hnFit hkPos hkShift (hr2CopyFit := by omega)
          (hresultFit := hresultFit) (hsource := by omega) (htarget := hresultMem)
          (hr2AccessFit := by omega) (hresultAccessFit := hresultAccessFit)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.1)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.2)
          hcompare hrestFalse

/-- One ordinary correction column preserves covered representable memory and does not resize an
already allocated r2 buffer. -/
theorem correctionAdvance_coverage_size
    (n r2 : UInt256) (state : CorrectionSubtractionState)
    (hr2Fit : (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 + 31 < UInt256.size)
    (hnFit : (elementPtr n (UInt256.ofNat state.i)).toNat + 32 + 31 < UInt256.size)
    (hr2Mem : (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size)
    (_hnMem : (elementPtr n (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (correctionAdvance n r2 state).memory
        (correctionAdvance n r2 state).activeWords ∧
      (correctionAdvance n r2 state).activeWords.toNat * 32 < UInt256.size ∧
      (correctionAdvance n r2 state).memory.size = state.memory.size := by
  let r2Ptr := elementPtr r2 (UInt256.ofNat state.i)
  let nPtr := elementPtr n (UInt256.ofNat state.i)
  have hleft := readWords1_coverage state.memory state.activeWords r2Ptr
    hcovered hawFit (by simpa [r2Ptr] using hr2Fit)
  have hright := readWords1_coverage state.memory (afterLoad state.activeWords r2Ptr) nPtr
    (by simpa [afterLoad] using hleft.1) (by simpa [afterLoad] using hleft.2)
    (by simpa [nPtr] using hnFit)
  have hgap : r2Ptr.toNat - state.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by
      have hword : r2Ptr.toNat + 32 ≤ state.memory.size := by
        simpa [r2Ptr] using hr2Mem
      omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite := write32_coverage
    (correctionStep state.memory state.activeWords n r2
      (UInt256.ofNat state.i) state.borrow).1
    state.memory (afterLoad (afterLoad state.activeWords r2Ptr) nPtr) r2Ptr
    (by simpa [afterLoad] using hright.1) (by simpa [afterLoad] using hright.2)
    (by simpa [r2Ptr] using hr2Fit) hgap
  have hsize : (correctionAdvance n r2 state).memory.size = state.memory.size := by
    unfold correctionAdvance correctionMemory
    exact write_size_of_inBounds_from _ _ 0 r2Ptr.toNat 32
      (by decide) (by rw [toByteArray_size]) (by simpa [r2Ptr] using hr2Mem)
  refine ⟨?_, ?_, hsize⟩
  · simpa [correctionAdvance, correctionMemory, correctionWords, r2Ptr, nPtr,
      afterLoad] using hwrite.1
  · simpa [correctionAdvance, correctionWords, r2Ptr, nPtr, afterLoad] using hwrite.2

/-- Ordinary correction collectors are the original contiguous r2 and modulus slices.  Sequential
r2 writes lie below future r2 reads and above the disjoint modulus allocation. -/
theorem correctionCollectors_eq_memoryWordsFrom
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState)
    (hr2Fit : r2.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hnMem : n.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hdisjoint : n.toNat + 32 * (state.i + count + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    correctionLeftWords n r2 count state =
        memoryWordsFrom state.memory (r2.toNat + 32 * (state.i + 1)) count ∧
      correctionRightWords n r2 count state =
        memoryWordsFrom state.memory (n.toNat + 32 * (state.i + 1)) count := by
  induction count generalizing state with
  | zero => simp [correctionLeftWords, correctionRightWords, memoryWordsFrom]
  | succ count ih =>
      have hr2Address : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        elementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hnAddress : (elementPtr n (UInt256.ofNat state.i)).toNat =
          n.toNat + 32 * (state.i + 1) :=
        elementPtr_ofNat_toNat_of_fit n state.i (by omega)
      have hadvance := correctionAdvance_coverage_size n r2 state
        (by rw [hr2Address]; omega) (by rw [hnAddress]; omega)
        (by rw [hr2Address]; omega) (by rw [hnAddress]; omega)
        hcovered hawFit
      let next := correctionAdvance n r2 state
      have hnextI : next.i = state.i + 1 := by rfl
      have hrest := ih next
        (by rw [hnextI]; omega) (by rw [hnextI]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI]; omega) hadvance.1 hadvance.2.1
      have hleftWord :
          (correctionOperands state.memory state.activeWords n r2
            (UInt256.ofNat state.i)).1 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              (r2.toNat + 32 * (state.i + 1))) := by
        have hread := readWord_eq_memoryWordOf_covered state.memory state.activeWords
          (elementPtr r2 (UInt256.ofNat state.i)) hcovered hawFit
          (by rw [hr2Address]; omega)
        simpa [correctionOperands, hr2Address] using hread
      have hleftCoverage := readWords1_coverage state.memory state.activeWords
        (elementPtr r2 (UInt256.ofNat state.i)) hcovered hawFit
        (by rw [hr2Address]; omega)
      have hrightWord :
          (correctionOperands state.memory state.activeWords n r2
            (UInt256.ofNat state.i)).2 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
              (n.toNat + 32 * (state.i + 1))) := by
        have hread := readWord_eq_memoryWordOf_covered state.memory
          (afterLoad state.activeWords (elementPtr r2 (UInt256.ofNat state.i)))
          (elementPtr n (UInt256.ofNat state.i))
          (by simpa [afterLoad] using hleftCoverage.1)
          (by simpa [afterLoad] using hleftCoverage.2)
          (by rw [hnAddress]; omega)
        simpa [correctionOperands, hnAddress] using hread
      have hleftFrame :
          memoryWordsFrom next.memory
              (r2.toNat + 32 * (next.i + 1)) count =
            memoryWordsFrom state.memory
              (r2.toNat + 32 * (state.i + 2)) count := by
        have hframe := memoryWordsFrom_write_below
          (correctionStep state.memory state.activeWords n r2
            (UInt256.ofNat state.i) state.borrow).1.toByteArray
          state.memory (elementPtr r2 (UInt256.ofNat state.i)).toNat
          (r2.toNat + 32 * (state.i + 2)) count
          (by rw [toByteArray_size]) (by rw [hr2Address]; omega)
          (by rw [hr2Address]; omega)
        simpa [next, correctionAdvance, correctionMemory, hnextI] using hframe
      have hrightFrame :
          memoryWordsFrom next.memory
              (n.toNat + 32 * (next.i + 1)) count =
            memoryWordsFrom state.memory
              (n.toNat + 32 * (state.i + 2)) count := by
        have hframe := memoryWordsFrom_write_above
          (correctionStep state.memory state.activeWords n r2
            (UInt256.ofNat state.i) state.borrow).1.toByteArray
          state.memory (elementPtr r2 (UInt256.ofNat state.i)).toNat
          (n.toNat + 32 * (state.i + 2)) count
          (by rw [toByteArray_size]) (by rw [hr2Address]; omega)
          (by rw [hr2Address]; omega)
        simpa [next, correctionAdvance, correctionMemory, hnextI] using hframe
      constructor
      · simp only [correctionLeftWords]
        rw [hrest.1, hleftFrame, hleftWord]
        simp only [memoryWordsFrom]
        have hoff : r2.toNat + 32 * (state.i + 2) =
            r2.toNat + 32 * (state.i + 1) + 32 := by omega
        rw [hoff]
      · simp only [correctionRightWords]
        rw [hrest.2, hrightFrame, hrightWord]
        simp only [memoryWordsFrom]
        have hoff : n.toNat + 32 * (state.i + 2) =
            n.toNat + 32 * (state.i + 1) + 32 := by omega
        rw [hoff]

/-- Later correction writes preserve a complete earlier word below every write address. -/
theorem correctionIterate_read_below
    (count : Nat) (n r2 : UInt256) (state : CorrectionSubtractionState) (read : Nat)
    (hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size ∧
        read + 32 ≤ (elementPtr r2 (UInt256.ofNat current.i)).toNat) :
    (correctionIterate n r2 count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := correctionAdvance n r2 state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count →
          let current := correctionIterate n r2 j next
          (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size ∧
            read + 32 ≤ (elementPtr r2 (UInt256.ofNat current.i)).toNat := by
        intro j hj
        simpa only [next, correctionIterate_advance] using hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstInBounds :
          (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size := by
        simpa only [correctionIterate] using hfirst.1
      rw [correctionIterate, hrest]
      unfold next correctionAdvance correctionMemory
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirst.2

/-- One in-bounds correction store records exactly the arithmetic output word. -/
theorem correctionMemory_word
    (mem : ByteArray) (aw n r2 i borrow : UInt256)
    (hgap : (elementPtr r2 i).toNat - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (correctionMemory mem aw n r2 i borrow) (elementPtr r2 i).toNat =
      (correctionStep mem aw n r2 i borrow).1.toNat := by
  unfold correctionMemory Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- The ordinary correction output collector is exactly the final contiguous r2 range written by
the loop. -/
theorem correctionOutputWords_eq_finalMemoryWords
    (count : Nat) (n r2 : UInt256) (state : CorrectionSubtractionState)
    (hfit : r2.toNat + 32 * (state.i + count + 1) < UInt256.size)
    (hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size) :
    correctionOutputWords n r2 count state =
      memoryWordsFrom (correctionIterate n r2 count state).memory
        (r2.toNat + 32 * (state.i + 1)) count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := correctionAdvance n r2 state
      have hfirstWrite :
          (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size := by
        simpa only [correctionIterate] using hwrites 0 (by omega)
      have haddress : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        elementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hnextI : next.i = state.i + 1 := by rfl
      have hnextWrites : ∀ j, j < count →
          let current := correctionIterate n r2 j next
          (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size := by
        intro j hj
        simpa only [next, correctionIterate_advance] using hwrites (j + 1) (by omega)
      have htail := ih next (by rw [hnextI]; omega) hnextWrites
      have hgap : (elementPtr r2 (UInt256.ofNat state.i)).toNat -
          state.memory.size < USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega)]
        exact lt_usize 0 (by norm_num)
      have hstored :
          Modexp.MultiLimbMemoryModel.memoryWordNat next.memory
              (r2.toNat + 32 * (state.i + 1)) =
            (correctionStep state.memory state.activeWords n r2
              (UInt256.ofNat state.i) state.borrow).1.toNat := by
        simpa [next, correctionAdvance, haddress] using
          correctionMemory_word state.memory state.activeWords n r2
            (UInt256.ofNat state.i) state.borrow hgap
      have hlater :
          (correctionIterate n r2 count next).memory.readWithPadding
              (r2.toNat + 32 * (state.i + 1)) 32 =
            next.memory.readWithPadding (r2.toNat + 32 * (state.i + 1)) 32 := by
        apply correctionIterate_read_below count n r2 next
        intro j hj
        let current := correctionIterate n r2 j next
        have hwrite := hnextWrites j hj
        have hi : current.i = state.i + 1 + j := by
          change (correctionIterate n r2 j next).i = _
          rw [correctionIterate_i, hnextI]
        have hcurrentAddress :
            (elementPtr r2 (UInt256.ofNat current.i)).toNat =
              r2.toNat + 32 * (current.i + 1) :=
          elementPtr_ofNat_toNat_of_fit r2 current.i (by rw [hi]; omega)
        refine ⟨hwrite, ?_⟩
        rw [hcurrentAddress, hi]
        omega
      have hhead :
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              (correctionIterate n r2 count next).memory
              (r2.toNat + 32 * (state.i + 1))) =
            (correctionStep state.memory state.activeWords n r2
              (UInt256.ofNat state.i) state.borrow).1 := by
        apply u256_inj
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [hlater]
        exact hstored
      simp only [correctionOutputWords, correctionIterate, memoryWordsFrom]
      rw [← hhead, htail]
      have hoff : r2.toNat + 32 * (next.i + 1) =
          r2.toNat + 32 * (state.i + 1) + 32 := by rw [hnextI]; omega
      rw [hoff]

theorem correctionTerminalMemory_word
    (mem : ByteArray) (aw r2 i borrow : UInt256)
    (hgap : (elementPtr r2 i).toNat - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat
        (correctionTerminalMemory mem aw r2 i borrow) (elementPtr r2 i).toNat =
      (correctionTerminalStep mem aw r2 i borrow).1.toNat := by
  unfold correctionTerminalMemory Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write_read_back_of_gap _ _ _ hgap]
  exact fromByteArrayBigEndian_toByteArray _

/-- Including the terminal zero-modulus column, the complete correction output collector is the
final `k+1`-word r2 memory window. -/
theorem correctionPassOutputWords_eq_finalMemoryWords
    (count : Nat) (n r2 : UInt256) (state : CorrectionSubtractionState)
    (hfit : r2.toNat + 32 * (state.i + count + 2) < UInt256.size)
    (hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size)
    (hterminalWrite :
      let beforeFinal := correctionIterate n r2 count state
      (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat + 32 ≤
        beforeFinal.memory.size) :
    let beforeFinal := correctionIterate n r2 count state
    let finalMemory := correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat beforeFinal.i) beforeFinal.borrow
    correctionPassOutputWords n r2 count state =
      memoryWordsFrom finalMemory (r2.toNat + 32 * (state.i + 1)) (count + 1) := by
  let beforeFinal := correctionIterate n r2 count state
  let finalMemory := correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
    (UInt256.ofNat beforeFinal.i) beforeFinal.borrow
  have hbeforeI : beforeFinal.i = state.i + count := by
    simpa [beforeFinal] using correctionIterate_i n r2 count state
  have htopFit : r2.toNat + 32 * (beforeFinal.i + 1) < UInt256.size := by
    rw [hbeforeI]
    omega
  have htopAddress : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat =
      r2.toNat + 32 * (state.i + count + 1) := by
    rw [elementPtr_ofNat_toNat_of_fit r2 beforeFinal.i htopFit, hbeforeI]
  have hterminalWrite' :
      (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat + 32 ≤
        beforeFinal.memory.size := by
    simpa [beforeFinal] using hterminalWrite
  have hordinary := correctionOutputWords_eq_finalMemoryWords count n r2 state
    (by omega) hwrites
  have hlowFrame :
      memoryWordsFrom finalMemory (r2.toNat + 32 * (state.i + 1)) count =
        memoryWordsFrom beforeFinal.memory (r2.toNat + 32 * (state.i + 1)) count := by
    have hframe := memoryWordsFrom_write_above
      (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
        (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1.toByteArray
      beforeFinal.memory (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat
      (r2.toNat + 32 * (state.i + 1)) count
      (by rw [toByteArray_size]) (by omega)
      (by rw [htopAddress]; omega)
    simpa [finalMemory, correctionTerminalMemory] using hframe
  have hgap : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat -
      beforeFinal.memory.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by norm_num)
  have htopStored :
      Modexp.MultiLimbMemoryModel.memoryWordNat finalMemory
          (r2.toNat + 32 * (state.i + count + 1)) =
        (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
          (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1.toNat := by
    simpa [finalMemory, htopAddress] using
      correctionTerminalMemory_word beforeFinal.memory beforeFinal.activeWords r2
        (UInt256.ofNat beforeFinal.i) beforeFinal.borrow hgap
  change correctionPassOutputWords n r2 count state =
    memoryWordsFrom finalMemory (r2.toNat + 32 * (state.i + 1)) (count + 1)
  have hoff : r2.toNat + 32 * (state.i + 1) + 32 * count =
      r2.toNat + 32 * (state.i + count + 1) := by omega
  have htopWord :
      UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat finalMemory
        (r2.toNat + 32 * (state.i + 1) + 32 * count)) =
        (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
          (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1 := by
    apply u256_inj
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _), hoff, htopStored]
  rw [memoryWordsFrom_succ_eq_append, hlowFrame, ← hordinary]
  simp only [correctionPassOutputWords]
  rw [htopWord]

/-- Coverage, representability, and fixed allocated size propagate through all ordinary
correction columns. -/
theorem correctionIterate_coverage_size
    (count : Nat) (n r2 : UInt256) (state : CorrectionSubtractionState)
    (hr2Fit : r2.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (state.i + count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hnMem : n.toNat + 32 * (state.i + count + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size) :
    MemoryCovered (correctionIterate n r2 count state).memory
        (correctionIterate n r2 count state).activeWords ∧
      (correctionIterate n r2 count state).activeWords.toNat * 32 < UInt256.size ∧
      (correctionIterate n r2 count state).memory.size = state.memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, rfl⟩
  | succ count ih =>
      have hr2Address : (elementPtr r2 (UInt256.ofNat state.i)).toNat =
          r2.toNat + 32 * (state.i + 1) :=
        elementPtr_ofNat_toNat_of_fit r2 state.i (by omega)
      have hnAddress : (elementPtr n (UInt256.ofNat state.i)).toNat =
          n.toNat + 32 * (state.i + 1) :=
        elementPtr_ofNat_toNat_of_fit n state.i (by omega)
      have hadvance := correctionAdvance_coverage_size n r2 state
        (by rw [hr2Address]; omega) (by rw [hnAddress]; omega)
        (by rw [hr2Address]; omega) (by rw [hnAddress]; omega)
        hcovered hawFit
      let next := correctionAdvance n r2 state
      have hnextI : next.i = state.i + 1 := by rfl
      have hrest := ih next
        (by rw [hnextI]; omega) (by rw [hnextI]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        (by rw [hnextI, hadvance.2.2]; omega)
        hadvance.1 hadvance.2.1
      simpa only [next, correctionIterate] using
        And.intro hrest.1 (And.intro hrest.2.1 (hrest.2.2.trans hadvance.2.2))

/-- Ordinary lower-index correction writes preserve a later complete top word. -/
theorem correctionIterate_read_above
    (count : Nat) (n r2 : UInt256) (state : CorrectionSubtractionState) (read : Nat)
    (hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size ∧
        (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ read) :
    (correctionIterate n r2 count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := correctionAdvance n r2 state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count →
          let current := correctionIterate n r2 j next
          (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size ∧
            (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ read := by
        intro j hj
        simpa only [next, correctionIterate_advance] using hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstInBounds :
          (elementPtr r2 (UInt256.ofNat state.i)).toNat + 32 ≤ state.memory.size := by
        simpa only [correctionIterate] using hfirst.1
      rw [correctionIterate, hrest]
      unfold next correctionAdvance correctionMemory
      exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
        hfirstInBounds hfirst.2

/-- A complete correction pass reads the original r2 payload including its unchanged top word,
and the original modulus payload extended by zero. -/
theorem correctionPassCollectors_eq_initialMemoryWords
    (count : Nat) (mem : ByteArray) (aw n r2 : UInt256)
    (hr2Fit : r2.toNat + 32 * (count + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (count + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (count + 1) ≤ mem.size)
    (hdisjoint : n.toNat + 32 * (count + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let initial := correctionInitialState mem aw
    correctionPassLeftWords n r2 count initial =
        memoryWordsFrom mem (r2.toNat + 32) (count + 1) ∧
      correctionPassRightWords n r2 count initial =
        memoryWordsFrom mem (n.toNat + 32) count ++ [⟨0⟩] := by
  let initial := correctionInitialState mem aw
  let beforeFinal := correctionIterate n r2 count initial
  have hordinary := correctionCollectors_eq_memoryWordsFrom n r2 count initial
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simpa [initial, correctionInitialState] using hdisjoint)
    (by simpa [initial, correctionInitialState] using hcovered)
    (by simpa [initial, correctionInitialState] using hawFit)
  have hcoverage := correctionIterate_coverage_size count n r2 initial
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simpa [initial, correctionInitialState] using hcovered)
    (by simpa [initial, correctionInitialState] using hawFit)
  have hbeforeI : beforeFinal.i = count := by
    simpa [beforeFinal, initial, correctionInitialState] using
      correctionIterate_i n r2 count initial
  have htopAddress : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat =
      r2.toNat + 32 * (count + 1) := by
    have htopFit : r2.toNat + 32 * (beforeFinal.i + 1) < UInt256.size := by
      rw [hbeforeI]
      omega
    rw [elementPtr_ofNat_toNat_of_fit r2 beforeFinal.i htopFit, hbeforeI]
  have htopRead :
      readWord beforeFinal.memory beforeFinal.activeWords
          (elementPtr r2 (UInt256.ofNat beforeFinal.i)) =
        UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat beforeFinal.memory
          (r2.toNat + 32 * (count + 1))) := by
    have hread := readWord_eq_memoryWordOf_covered beforeFinal.memory beforeFinal.activeWords
      (elementPtr r2 (UInt256.ofNat beforeFinal.i))
      (by simpa [beforeFinal] using hcoverage.1)
      (by simpa [beforeFinal] using hcoverage.2.1)
      (by
        rw [htopAddress]
        have hsize : beforeFinal.memory.size = mem.size := by
          simpa [beforeFinal, initial, correctionInitialState] using hcoverage.2.2
        rw [hsize]
        omega)
    simpa [htopAddress] using hread
  have htopFrame : beforeFinal.memory.readWithPadding
        (r2.toNat + 32 * (count + 1)) 32 =
      mem.readWithPadding (r2.toNat + 32 * (count + 1)) 32 := by
    apply correctionIterate_read_above count n r2 initial
    intro j hj
    let current := correctionIterate n r2 j initial
    have hi : current.i = j := by
      simpa [current, initial, correctionInitialState] using
        correctionIterate_i n r2 j initial
    have haddr : (elementPtr r2 (UInt256.ofNat current.i)).toNat =
        r2.toNat + 32 * (j + 1) := by
      have hcurrentFit : r2.toNat + 32 * (current.i + 1) < UInt256.size := by
        rw [hi]
        omega
      rw [elementPtr_ofNat_toNat_of_fit r2 current.i hcurrentFit, hi]
    have hcurrentCoverage := correctionIterate_coverage_size j n r2 initial
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simpa [initial, correctionInitialState] using hcovered)
      (by simpa [initial, correctionInitialState] using hawFit)
    constructor
    · rw [haddr]
      have hsize : current.memory.size = mem.size := by
        simpa [current, initial, correctionInitialState] using hcurrentCoverage.2.2
      rw [hsize]
      omega
    · rw [haddr]
      omega
  have htopNat : Modexp.MultiLimbMemoryModel.memoryWordNat beforeFinal.memory
        (r2.toNat + 32 * (count + 1)) =
      Modexp.MultiLimbMemoryModel.memoryWordNat mem
        (r2.toNat + 32 * (count + 1)) := by
    unfold Modexp.MultiLimbMemoryModel.memoryWordNat
    exact congrArg fromByteArrayBigEndian htopFrame
  constructor
  · simp only [correctionPassLeftWords]
    change correctionLeftWords n r2 count initial ++
        [readWord beforeFinal.memory beforeFinal.activeWords
          (elementPtr r2 (UInt256.ofNat beforeFinal.i))] =
      memoryWordsFrom mem (r2.toNat + 32) (count + 1)
    rw [hordinary.1, htopRead, htopNat,
      memoryWordsFrom_succ_eq_append]
    simp only [initial, correctionInitialState, Nat.zero_add]
    have hoff : r2.toNat + 32 + 32 * count =
        r2.toNat + 32 * (count + 1) := by omega
    rw [hoff]
  · simp only [correctionPassRightWords]
    simpa [initial, correctionInitialState] using congrArg (fun words => words ++ [⟨0⟩])
      hordinary.2

/-- One selected correction pass changes the actual `k+1`-word r2 memory value by ordinary
subtraction of the concrete `k`-word modulus. -/
theorem correctionPass_finalMemory_value_eq_sub
    (count : Nat) (mem : ByteArray) (aw n r2 : UInt256)
    (hr2Fit : r2.toNat + 32 * (count + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (count + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (count + 1) ≤ mem.size)
    (hdisjoint : n.toNat + 32 * (count + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hge : Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) count) ≤
      Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) (count + 1))) :
    let initial := correctionInitialState mem aw
    let beforeFinal := correctionIterate n r2 count initial
    let finalMemory := correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat beforeFinal.i) beforeFinal.borrow
    Modexp.wordLimbsToNat
        (memoryWordsFrom finalMemory (r2.toNat + 32) (count + 1)) =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) (count + 1)) -
        Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) count) := by
  let initial := correctionInitialState mem aw
  let beforeFinal := correctionIterate n r2 count initial
  let finalMemory := correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
    (UInt256.ofNat beforeFinal.i) beforeFinal.borrow
  have hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j initial
      (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size := by
    intro j hj
    let current := correctionIterate n r2 j initial
    have hi : current.i = j := by
      simpa [current, initial, correctionInitialState] using
        correctionIterate_i n r2 j initial
    have haddr : (elementPtr r2 (UInt256.ofNat current.i)).toNat =
        r2.toNat + 32 * (j + 1) := by
      have hfit : r2.toNat + 32 * (current.i + 1) < UInt256.size := by
        rw [hi]
        omega
      rw [elementPtr_ofNat_toNat_of_fit r2 current.i hfit, hi]
    have hcoverage := correctionIterate_coverage_size j n r2 initial
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simpa [initial, correctionInitialState] using hcovered)
      (by simpa [initial, correctionInitialState] using hawFit)
    have hsize : current.memory.size = mem.size := by
      simpa [current, initial, correctionInitialState] using hcoverage.2.2
    change (elementPtr r2 (UInt256.ofNat current.i)).toNat + 32 ≤ current.memory.size
    rw [haddr, hsize]
    omega
  have hbeforeI : beforeFinal.i = count := by
    simpa [beforeFinal, initial, correctionInitialState] using
      correctionIterate_i n r2 count initial
  have hterminalWrite :
      (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat + 32 ≤
        beforeFinal.memory.size := by
    have hfit : r2.toNat + 32 * (beforeFinal.i + 1) < UInt256.size := by
      rw [hbeforeI]
      omega
    have haddr := elementPtr_ofNat_toNat_of_fit r2 beforeFinal.i hfit
    have hcoverage := correctionIterate_coverage_size count n r2 initial
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simp [initial, correctionInitialState]; omega)
      (by simpa [initial, correctionInitialState] using hcovered)
      (by simpa [initial, correctionInitialState] using hawFit)
    have hsize : beforeFinal.memory.size = mem.size := by
      simpa [beforeFinal, initial, correctionInitialState] using hcoverage.2.2
    rw [haddr, hbeforeI, hsize]
    omega
  have hinputs := correctionPassCollectors_eq_initialMemoryWords count mem aw n r2
    hr2Fit hnFit hr2Mem hnMem hdisjoint hcovered hawFit
  have hgeCollectors : Modexp.wordLimbsToNat
        (correctionPassRightWords n r2 count initial) ≤
      Modexp.wordLimbsToNat (correctionPassLeftWords n r2 count initial) := by
    rw [hinputs.1, hinputs.2, Modexp.wordLimbsToNat_append]
    simp only [memoryWordsFrom_length, Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero,
      Nat.add_zero]
    exact hge
  have hsub := correctionPassCollectors_fromZero_eq_sub n r2 count mem aw hgeCollectors
  have houtputs := correctionPassOutputWords_eq_finalMemoryWords count n r2 initial
    (by simp [initial, correctionInitialState]; omega) hwrites
    (by simpa [beforeFinal] using hterminalWrite)
  rw [houtputs, hinputs.1, hinputs.2, Modexp.wordLimbsToNat_append] at hsub
  simp only [memoryWordsFrom_length, Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero,
    Nat.add_zero] at hsub
  simpa [initial, beforeFinal, finalMemory, correctionInitialState] using hsub

def correctionCandidateValue (mem : ByteArray) (r2 : UInt256) (kWords : Nat) : Nat :=
  Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) (kWords + 1))

def correctionModulusValue (mem : ByteArray) (n : UInt256) (kWords : Nat) : Nat :=
  Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords)

/-- The combined top-word shortcut and descending selector requests subtraction exactly when the
full `k+1`-word candidate is at least the concrete modulus. -/
theorem selectedBarrettDecision_doSub_iff_memoryValue
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected) :
    selected.doSub = true ↔
      correctionModulusValue mem n kWords ≤ correctionCandidateValue mem r2 kWords := by
  let topPtr := correctionTopPtr r2 kWords
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  have htopAddress : topPtr.toNat = r2.toNat + 32 * (kWords + 1) := by
    simpa [topPtr, correctionTopPtr] using
      elementPtr_ofNat_toNat_of_fit r2 kWords (by omega)
  have htopCoverage := readWords1_coverage mem aw topPtr hcovered hawFit
    (by rw [htopAddress]; omega)
  have htopRead : top = UInt256.ofNat
      (Modexp.MultiLimbMemoryModel.memoryWordNat mem
        (r2.toNat + 32 * (kWords + 1))) := by
    have hread := readWord_eq_memoryWordOf_covered mem aw topPtr hcovered hawFit
      (by rw [htopAddress]; omega)
    rw [htopAddress] at hread
    simpa [top, correctionTopWord, correctionTopPtr, topPtr] using hread
  have hr2Split := memoryWordsFrom_succ_eq_append mem (r2.toNat + 32) kWords
  have hr2Value : correctionCandidateValue mem r2 kWords =
      Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) +
        UInt256.size ^ kWords * top.toNat := by
    unfold correctionCandidateValue
    rw [hr2Split, Modexp.wordLimbsToNat_append, memoryWordsFrom_length]
    simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
    have hoff : r2.toNat + 32 + 32 * kWords =
        r2.toNat + 32 * (kWords + 1) := by omega
    rw [hoff]
    have htopNatRead := congrArg UInt256.toNat htopRead
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] at htopNatRead
    rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
    rw [htopNatRead]
  simp only [selectBarrettDecision] at hselect
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop] at hselect
    injection hselect with heq
    subst selected
    have htopNat : 1 ≤ top.toNat := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hz
      apply htop
      apply u256_inj
      simpa using hz
    have hnBound := Modexp.wordLimbsToNat_lt_pow
      (memoryWordsFrom mem (n.toNat + 32) kWords)
    rw [memoryWordsFrom_length] at hnBound
    unfold correctionModulusValue
    rw [hr2Value]
    have hscaled : UInt256.size ^ kWords ≤ UInt256.size ^ kWords * top.toNat := by
      simpa using Nat.mul_le_mul_left (UInt256.size ^ kWords) htopNat
    have hvalue : Modexp.wordLimbsToNat
          (memoryWordsFrom mem (n.toNat + 32) kWords) ≤
        Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) +
          UInt256.size ^ kWords * top.toNat := by
      calc
      Modexp.wordLimbsToNat (memoryWordsFrom mem (n.toNat + 32) kWords) ≤
          UInt256.size ^ kWords := hnBound.le
      _ ≤ UInt256.size ^ kWords * top.toNat := hscaled
      _ ≤ Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords) +
          UInt256.size ^ kWords * top.toNat := by omega
    simpa using hvalue
  · rw [if_neg htop] at hselect
    cases hcompare : selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => rw [hcompare] at hselect; contradiction
    | some rest =>
        rw [hcompare] at hselect
        injection hselect with heq
        subst selected
        have hcompareSem := selectedBarrettCompare_doSub_iff_memoryWords hkPos
          (by omega) (by omega) (by omega) (by omega)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.1)
          (by simpa [topAw, correctionTopWords, topPtr, correctionTopPtr]
            using htopCoverage.2)
          hcompare
        have htopZero : top.toNat = 0 := by
          have hz : top = ⟨0⟩ := by simpa using htop
          rw [hz]
          decide
        unfold correctionModulusValue at hcompareSem ⊢
        rw [hr2Value, htopZero, Nat.mul_zero, Nat.add_zero]
        exact hcompareSem

/-- A complete correction pass preserves covered representable allocator memory and its concrete
size, so a second decision reads a valid evolving state. -/
theorem runBarrettPass_coverage_size
    (count : Nat) (mem : ByteArray) (aw n r2 : UInt256)
    (hr2Fit : r2.toNat + 32 * (count + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (count + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (count + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let pass := runBarrettPass mem aw n r2 count
    MemoryCovered pass.memory pass.activeWords ∧
      pass.activeWords.toNat * 32 < UInt256.size ∧ pass.memory.size = mem.size := by
  let initial := correctionInitialState mem aw
  let beforeFinal := correctionIterate n r2 count initial
  let pass := runBarrettPass mem aw n r2 count
  have hbefore := correctionIterate_coverage_size count n r2 initial
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simpa [initial, correctionInitialState] using hcovered)
    (by simpa [initial, correctionInitialState] using hawFit)
  have hbeforeI : beforeFinal.i = count := by
    simpa [beforeFinal, initial, correctionInitialState] using
      correctionIterate_i n r2 count initial
  have htopAddress : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat =
      r2.toNat + 32 * (count + 1) := by
    have hfit : r2.toNat + 32 * (beforeFinal.i + 1) < UInt256.size := by
      rw [hbeforeI]
      omega
    rw [elementPtr_ofNat_toNat_of_fit r2 beforeFinal.i hfit, hbeforeI]
  have hbeforeCovered : MemoryCovered beforeFinal.memory beforeFinal.activeWords := by
    simpa [beforeFinal] using hbefore.1
  have hbeforeAw : beforeFinal.activeWords.toNat * 32 < UInt256.size := by
    simpa [beforeFinal] using hbefore.2.1
  have hload := readWords1_coverage beforeFinal.memory beforeFinal.activeWords
    (elementPtr r2 (UInt256.ofNat beforeFinal.i)) hbeforeCovered hbeforeAw
    (by rw [htopAddress]; omega)
  have hgap : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat -
      beforeFinal.memory.size < USize.size := by
    have hsize : beforeFinal.memory.size = mem.size := by
      simpa [beforeFinal, initial, correctionInitialState] using hbefore.2.2
    rw [Nat.sub_eq_zero_of_le (by rw [htopAddress, hsize]; omega)]
    exact lt_usize 0 (by norm_num)
  have hwrite := write32_coverage
    (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1
    beforeFinal.memory
    (afterLoad beforeFinal.activeWords (elementPtr r2 (UInt256.ofNat beforeFinal.i)))
    (elementPtr r2 (UInt256.ofNat beforeFinal.i))
    (by simpa [afterLoad] using hload.1) (by simpa [afterLoad] using hload.2)
    (by rw [htopAddress]; omega) hgap
  have hsizeFinal :
      (correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
        (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).size = beforeFinal.memory.size := by
    unfold correctionTerminalMemory
    exact write_size_of_inBounds_from _ _ 0
      (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat 32
      (by decide) (by rw [toByteArray_size]) (by
        have hsize : beforeFinal.memory.size = mem.size := by
          simpa [beforeFinal, initial, correctionInitialState] using hbefore.2.2
        rw [htopAddress, hsize]
        omega)
  rw [hbeforeI] at hwrite hsizeFinal
  refine ⟨?_, ?_, ?_⟩
  · simpa [pass, runBarrettPass, beforeFinal, initial, correctionTerminalMemory,
      correctionTerminalWords, afterLoad] using hwrite.1
  · simpa [pass, runBarrettPass, beforeFinal, initial, correctionTerminalWords,
      afterLoad] using hwrite.2
  · simpa [pass, runBarrettPass, beforeFinal, initial, correctionInitialState]
      using hsizeFinal.trans hbefore.2.2

/-- The deployed final `MCOPY` puts exactly the low corrected r2 words in the result payload. -/
theorem barrettFinalMemory_resultWords
    (count : Nat) (mem : ByteArray) (r2 result : UInt256)
    (hcount : 0 < count)
    (hcountFit : count < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hsource : r2.toNat + 32 + 32 * count ≤ mem.size)
    (htarget : result.toNat + 32 ≤ mem.size) :
    memoryWordsFrom (barrettFinalMemory mem r2 result count)
        (result.toNat + 32) count =
      memoryWordsFrom mem (r2.toNat + 32) count := by
  have hbytes : (barrettCopyBytes count).toNat = 32 * count := by
    unfold barrettCopyBytes
    exact ushl5_ofNat_toNat count hcountFit
  have hsrc : (barrettCopySource r2).toNat = r2.toNat + 32 := by
    unfold barrettCopySource
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hr2Fit]
  have hdest : (barrettCopyTarget result).toNat = result.toNat + 32 := by
    unfold barrettCopyTarget
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide,
      Nat.mod_eq_of_lt hresultFit]
  unfold barrettFinalMemory
  rw [hsrc, hdest, hbytes]
  simpa only [Nat.zero_add, Nat.mul_zero] using
    memoryWordsFrom_write_copy_window mem mem (r2.toNat + 32) (result.toNat + 32)
      count 0 count hcount hsource htarget (by omega)

/-- A complete memory-word range below every correction write is unchanged by the ordinary
iteration. -/
theorem correctionIterate_memoryWords_below
    (count : Nat) (n r2 : UInt256) (state : CorrectionSubtractionState)
    (ptr words : Nat)
    (hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j state
      (elementPtr r2 (UInt256.ofNat current.i)).toNat ≤ current.memory.size ∧
        ptr + 32 * words ≤ (elementPtr r2 (UInt256.ofNat current.i)).toNat) :
    memoryWordsFrom (correctionIterate n r2 count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := correctionAdvance n r2 state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count →
          let current := correctionIterate n r2 j next
          (elementPtr r2 (UInt256.ofNat current.i)).toNat ≤ current.memory.size ∧
            ptr + 32 * words ≤ (elementPtr r2 (UInt256.ofNat current.i)).toNat := by
        intro j hj
        simpa only [next, correctionIterate_advance] using hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hframe := memoryWordsFrom_write_above
        (correctionStep state.memory state.activeWords n r2
          (UInt256.ofNat state.i) state.borrow).1.toByteArray
        state.memory (elementPtr r2 (UInt256.ofNat state.i)).toNat ptr words
        (by rw [toByteArray_size]) (by simpa only [correctionIterate] using hfirst.1)
        (by simpa only [correctionIterate] using hfirst.2)
      rw [correctionIterate, hrest]
      simpa [next, correctionAdvance, correctionMemory] using hframe

/-- A complete pass leaves the disjoint concrete modulus payload unchanged. -/
theorem runBarrettPass_modulusWords
    (count : Nat) (mem : ByteArray) (aw n r2 : UInt256)
    (hr2Fit : r2.toNat + 32 * (count + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (count + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (count + 1) ≤ mem.size)
    (hdisjoint : n.toNat + 32 * (count + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let pass := runBarrettPass mem aw n r2 count
    memoryWordsFrom pass.memory (n.toNat + 32) count =
      memoryWordsFrom mem (n.toNat + 32) count := by
  let initial := correctionInitialState mem aw
  let beforeFinal := correctionIterate n r2 count initial
  let pass := runBarrettPass mem aw n r2 count
  have hbeforeCoverage := correctionIterate_coverage_size count n r2 initial
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simpa [initial, correctionInitialState] using hcovered)
    (by simpa [initial, correctionInitialState] using hawFit)
  have hwrites : ∀ j, j < count →
      let current := correctionIterate n r2 j initial
      (elementPtr r2 (UInt256.ofNat current.i)).toNat ≤ current.memory.size ∧
        n.toNat + 32 + 32 * count ≤
          (elementPtr r2 (UInt256.ofNat current.i)).toNat := by
    intro j hj
    let current := correctionIterate n r2 j initial
    have hi : current.i = j := by
      simpa [current, initial, correctionInitialState] using
        correctionIterate_i n r2 j initial
    have haddr : (elementPtr r2 (UInt256.ofNat current.i)).toNat =
        r2.toNat + 32 * (j + 1) := by
      have hfit : r2.toNat + 32 * (current.i + 1) < UInt256.size := by
        rw [hi]
        omega
      rw [elementPtr_ofNat_toNat_of_fit r2 current.i hfit, hi]
    constructor
    · rw [haddr]
      have hsize : current.memory.size = mem.size := by
        have hcurrentCoverage := correctionIterate_coverage_size j n r2 initial
          (by simp [initial, correctionInitialState]; omega)
          (by simp [initial, correctionInitialState]; omega)
          (by simp [initial, correctionInitialState]; omega)
          (by simp [initial, correctionInitialState]; omega)
          (by simpa [initial, correctionInitialState] using hcovered)
          (by simpa [initial, correctionInitialState] using hawFit)
        simpa [current, initial, correctionInitialState] using hcurrentCoverage.2.2
      rw [hsize]
      omega
    · rw [haddr]
      omega
  have hordinary := correctionIterate_memoryWords_below count n r2 initial
    (n.toNat + 32) count hwrites
  have hbeforeI : beforeFinal.i = count := by
    simpa [beforeFinal, initial, correctionInitialState] using
      correctionIterate_i n r2 count initial
  have htopAddress : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat =
      r2.toNat + 32 * (count + 1) := by
    have hfit : r2.toNat + 32 * (beforeFinal.i + 1) < UInt256.size := by
      rw [hbeforeI]
      omega
    rw [elementPtr_ofNat_toNat_of_fit r2 beforeFinal.i hfit, hbeforeI]
  have hterminalFrame := memoryWordsFrom_write_above
    (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1.toByteArray
    beforeFinal.memory (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat
    (n.toNat + 32) count (by rw [toByteArray_size])
    (by
      rw [htopAddress]
      have hsize : beforeFinal.memory.size = mem.size := by
        simpa [beforeFinal, initial, correctionInitialState] using hbeforeCoverage.2.2
      rw [hsize]
      omega)
    (by rw [htopAddress]; omega)
  change memoryWordsFrom pass.memory (n.toNat + 32) count =
    memoryWordsFrom mem (n.toNat + 32) count
  have hpass : pass.memory =
      correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
        (UInt256.ofNat beforeFinal.i) beforeFinal.borrow := by
    rw [hbeforeI]
    rfl
  rw [hpass]
  unfold correctionTerminalMemory
  rw [hterminalFrame]
  simpa [beforeFinal, initial, correctionInitialState] using hordinary

/-- A complete correction pass leaves every concrete word range ending at or below the r2
header unchanged.  This is the frame property used for persistent exponent-loop arrays. -/
theorem runBarrettPass_memoryWords_below
    (count : Nat) (mem : ByteArray) (aw n r2 : UInt256) (ptr words : Nat)
    (hr2Fit : r2.toNat + 32 * (count + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (count + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (count + 2) <= mem.size)
    (hnMem : n.toNat + 32 * (count + 1) <= mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbelow : ptr + 32 * words <= r2.toNat) :
    let pass := runBarrettPass mem aw n r2 count
    memoryWordsFrom pass.memory ptr words = memoryWordsFrom mem ptr words := by
  let initial := correctionInitialState mem aw
  let beforeFinal := correctionIterate n r2 count initial
  let pass := runBarrettPass mem aw n r2 count
  have hbeforeCoverage := correctionIterate_coverage_size count n r2 initial
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simp [initial, correctionInitialState]; omega)
    (by simpa [initial, correctionInitialState] using hcovered)
    (by simpa [initial, correctionInitialState] using hawFit)
  have hwrites : forall j, j < count ->
      let current := correctionIterate n r2 j initial
      (elementPtr r2 (UInt256.ofNat current.i)).toNat <= current.memory.size /\
        ptr + 32 * words <=
          (elementPtr r2 (UInt256.ofNat current.i)).toNat := by
    intro j hj
    let current := correctionIterate n r2 j initial
    have hi : current.i = j := by
      simpa [current, initial, correctionInitialState] using
        correctionIterate_i n r2 j initial
    have haddr : (elementPtr r2 (UInt256.ofNat current.i)).toNat =
        r2.toNat + 32 * (j + 1) := by
      have hfit : r2.toNat + 32 * (current.i + 1) < UInt256.size := by
        rw [hi]
        omega
      rw [elementPtr_ofNat_toNat_of_fit r2 current.i hfit, hi]
    constructor
    · rw [haddr]
      have hsize : current.memory.size = mem.size := by
        have hcurrentCoverage := correctionIterate_coverage_size j n r2 initial
          (by simp [initial, correctionInitialState]; omega)
          (by simp [initial, correctionInitialState]; omega)
          (by simp [initial, correctionInitialState]; omega)
          (by simp [initial, correctionInitialState]; omega)
          (by simpa [initial, correctionInitialState] using hcovered)
          (by simpa [initial, correctionInitialState] using hawFit)
        simpa [current, initial, correctionInitialState] using hcurrentCoverage.2.2
      rw [hsize]
      omega
    · rw [haddr]
      omega
  have hordinary := correctionIterate_memoryWords_below count n r2 initial ptr words hwrites
  have hbeforeI : beforeFinal.i = count := by
    simpa [beforeFinal, initial, correctionInitialState] using
      correctionIterate_i n r2 count initial
  have htopAddress : (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat =
      r2.toNat + 32 * (count + 1) := by
    have hfit : r2.toNat + 32 * (beforeFinal.i + 1) < UInt256.size := by
      rw [hbeforeI]
      omega
    rw [elementPtr_ofNat_toNat_of_fit r2 beforeFinal.i hfit, hbeforeI]
  have hterminalFrame := memoryWordsFrom_write_above
    (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat beforeFinal.i) beforeFinal.borrow).1.toByteArray
    beforeFinal.memory (elementPtr r2 (UInt256.ofNat beforeFinal.i)).toNat
    ptr words (by rw [toByteArray_size])
    (by
      rw [htopAddress]
      have hsize : beforeFinal.memory.size = mem.size := by
        simpa [beforeFinal, initial, correctionInitialState] using hbeforeCoverage.2.2
      rw [hsize]
      omega)
    (by rw [htopAddress]; omega)
  change memoryWordsFrom pass.memory ptr words = memoryWordsFrom mem ptr words
  have hpass : pass.memory =
      correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
        (UInt256.ofNat beforeFinal.i) beforeFinal.borrow := by
    rw [hbeforeI]
    rfl
  rw [hpass]
  unfold correctionTerminalMemory
  rw [hterminalFrame]
  simpa [beforeFinal, initial, correctionInitialState] using hordinary

/-- A true correction decision followed by its concrete pass subtracts one modulus while
preserving the geometry needed by a possible second decision. -/
theorem selectedBarrettDecision_true_pass
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hdisjoint : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (htrue : selected.doSub = true) :
    let pass := runBarrettPass selected.memory selected.activeWords n r2 kWords
    correctionCandidateValue pass.memory r2 kWords =
        correctionCandidateValue mem r2 kWords - correctionModulusValue mem n kWords ∧
      MemoryCovered pass.memory pass.activeWords ∧
      pass.activeWords.toNat * 32 < UInt256.size ∧
      pass.memory.size = mem.size ∧
      correctionModulusValue pass.memory n kWords = correctionModulusValue mem n kWords := by
  have hgeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit hnFit
    hcovered hawFit hselect htrue
  have hge := (selectedBarrettDecision_doSub_iff_memoryValue hkPos hr2Fit hnFit
    hr2Mem hnMem hcovered hawFit hselect).mp htrue
  let pass := runBarrettPass selected.memory selected.activeWords n r2 kWords
  rw [hgeometry.1]
  have hvalue := correctionPass_finalMemory_value_eq_sub kWords mem
    selected.activeWords n r2 hr2Fit hnFit hr2Mem hnMem hdisjoint
    hgeometry.2.1 hgeometry.2.2 hge
  have hpassCoverage := runBarrettPass_coverage_size kWords mem selected.activeWords n r2
    hr2Fit hnFit hr2Mem hnMem hgeometry.2.1 hgeometry.2.2
  have hmodulus := runBarrettPass_modulusWords kWords mem selected.activeWords n r2
    hr2Fit hnFit hr2Mem hnMem hdisjoint hgeometry.2.1 hgeometry.2.2
  have hbeforeI :
      (correctionIterate n r2 kWords
        (correctionInitialState mem selected.activeWords)).i = kWords := by
    simpa [correctionInitialState] using
      correctionIterate_i n r2 kWords (correctionInitialState mem selected.activeWords)
  dsimp only at hvalue
  rw [hbeforeI] at hvalue
  refine ⟨?_, hpassCoverage.1, hpassCoverage.2.1, hpassCoverage.2.2, ?_⟩
  · simpa [correctionCandidateValue, runBarrettPass] using hvalue
  · exact congrArg Modexp.wordLimbsToNat hmodulus

/-- A descending selector that declines subtraction has exactly the deployed final-copy memory. -/
theorem selectedBarrettCompare_memory_of_false
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords iWords : Nat} {selected : BarrettCompareSelection}
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords iWords = some selected)
    (hfalse : selected.doSub = false) :
    selected.memory = barrettFinalMemory mem r2 result kWords := by
  induction fuel generalizing aw iWords selected with
  | zero => simp [selectBarrettCompare] at hselect
  | succ fuel ih =>
      simp only [selectBarrettCompare] at hselect
      let left := compareLeft mem aw r2 iWords
      let right := compareRight mem aw n r2 iWords
      let nextAw := compareWords aw n r2 iWords
      by_cases hgreater : right.toNat < left.toNat
      · rw [if_pos hgreater] at hselect
        injection hselect with heq
        subst selected
        contradiction
      · rw [if_neg hgreater] at hselect
        by_cases hless : left.toNat < right.toNat
        · rw [if_pos hless] at hselect
          injection hselect with heq
          subst selected
          rfl
        · rw [if_neg hless] at hselect
          by_cases hiOne : iWords = 1
          · rw [if_pos hiOne] at hselect
            injection hselect with heq
            subst selected
            contradiction
          · rw [if_neg hiOne] at hselect
            cases hrest : selectBarrettCompare fuel mem nextAw n r2 result kWords
                (iWords - 1) with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have hrestFalse : rest.doSub = false := by simpa using hfalse
                exact ih (aw := nextAw) (iWords := iWords - 1) (selected := rest)
                  hrest hrestFalse

/-- A complete decision that declines subtraction has already copied the current r2 low words. -/
theorem selectedBarrettDecision_memory_of_false
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (hfalse : selected.doSub = false) :
    selected.memory = barrettFinalMemory mem r2 result kWords := by
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  simp only [selectBarrettDecision] at hselect
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop] at hselect
    injection hselect with heq
    subst selected
    contradiction
  · rw [if_neg htop] at hselect
    cases hcompare : selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => rw [hcompare] at hselect; contradiction
    | some rest =>
        rw [hcompare] at hselect
        injection hselect with heq
        subst selected
        have hrestFalse : rest.doSub = false := by simpa using hfalse
        exact selectedBarrettCompare_memory_of_false
          (selected := rest) hcompare hrestFalse

/-- Every successful zero/one/two-pass correction selector preserves covered representable
memory and its already-materialized concrete size. -/
theorem selectedBarrettCorrection_coverage_size
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) <= mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) <= mem.size)
    (hresultMem : result.toNat + 32 + 32 * kWords <= mem.size)
    (hresultAccessFit : result.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettCorrection fuel mem aw n r2 result kWords = some selected) :
    MemoryCovered selected.memory selected.activeWords /\
      selected.activeWords.toNat * 32 < UInt256.size /\
      selected.memory.size = mem.size := by
  simp only [selectBarrettCorrection] at hselect
  cases hfirst : selectBarrettDecision fuel mem aw n r2 result kWords with
  | none => rw [hfirst] at hselect; contradiction
  | some first =>
      rw [hfirst] at hselect
      cases hdoFirst : first.doSub with
      | false =>
          simp only [hdoFirst, Bool.false_eq_true, ↓reduceIte] at hselect
          injection hselect with hselected
          subst selected
          exact selectedBarrettDecision_false_geometry hkPos hkShift hr2Fit hnFit
            hresultFit hr2Mem hresultMem hresultAccessFit hcovered hawFit hfirst hdoFirst
      | true =>
          simp only [hdoFirst, ↓reduceIte] at hselect
          have hfirstGeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit hnFit
            hcovered hawFit hfirst hdoFirst
          let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
          have hpass1 := runBarrettPass_coverage_size kWords first.memory first.activeWords n r2
            hr2Fit hnFit (by rw [hfirstGeometry.1]; exact hr2Mem)
            (by rw [hfirstGeometry.1]; exact hnMem)
            (by rw [hfirstGeometry.1]; exact hfirstGeometry.2.1)
            hfirstGeometry.2.2
          have hpass1Size : pass1.memory.size = mem.size := by
            calc
              pass1.memory.size = first.memory.size := by simpa [pass1] using hpass1.2.2
              _ = mem.size := congrArg ByteArray.size hfirstGeometry.1
          cases hsecond : selectBarrettDecision fuel pass1.memory pass1.activeWords n r2 result
              kWords with
          | none => rw [hsecond] at hselect; contradiction
          | some second =>
              rw [hsecond] at hselect
              cases hdoSecond : second.doSub with
              | false =>
                  simp only [hdoSecond, Bool.false_eq_true, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  have hsecondGeometry := selectedBarrettDecision_false_geometry hkPos hkShift
                    hr2Fit hnFit hresultFit
                    (by rw [hpass1Size]; exact hr2Mem)
                    (by rw [hpass1Size]; exact hresultMem)
                    hresultAccessFit
                    (by simpa [pass1] using hpass1.1)
                    (by simpa [pass1] using hpass1.2.1) hsecond hdoSecond
                  refine ⟨hsecondGeometry.1, hsecondGeometry.2.1, ?_⟩
                  exact hsecondGeometry.2.2.trans hpass1Size
              | true =>
                  simp only [hdoSecond, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  have hsecondGeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit
                    hnFit (by simpa [pass1] using hpass1.1)
                    (by simpa [pass1] using hpass1.2.1) hsecond hdoSecond
                  let pass2 := runBarrettPass second.memory second.activeWords n r2 kWords
                  have hpass2 := runBarrettPass_coverage_size kWords second.memory
                    second.activeWords n r2 hr2Fit hnFit
                    (by
                      rw [hsecondGeometry.1, hpass1Size]
                      exact hr2Mem)
                    (by
                      rw [hsecondGeometry.1, hpass1Size]
                      exact hnMem)
                    (by rw [hsecondGeometry.1]; exact hsecondGeometry.2.1)
                    hsecondGeometry.2.2
                  have hpass2Size : pass2.memory.size = mem.size := by
                    calc
                      pass2.memory.size = second.memory.size := by
                        simpa [pass2] using hpass2.2.2
                      _ = pass1.memory.size := congrArg ByteArray.size hsecondGeometry.1
                      _ = mem.size := hpass1Size
                  have hfinal := barrettFinal_coverage_size kWords pass2.memory
                    pass2.activeWords r2 result hkPos hkShift (by omega) hresultFit
                    (by rw [hpass2Size]; omega)
                    (by rw [hpass2Size]; exact hresultMem)
                    (by omega) hresultAccessFit
                    (by simpa [pass2] using hpass2.1)
                    (by simpa [pass2] using hpass2.2.1)
                  refine ⟨hfinal.1, hfinal.2.1, ?_⟩
                  exact hfinal.2.2.trans hpass2Size

/-- Every successful correction selector also supports a header-only result allocation, with the
selected final copy materializing the complete payload. -/
theorem selectedBarrettCorrection_coverage_size_from_start
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hresultMem : result.toNat + 32 ≤ mem.size)
    (hresultAccessFit : result.toNat + 32 + 32 * kWords + 31 < UInt256.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hselect : selectBarrettCorrection fuel mem aw n r2 result kWords = some selected) :
    MemoryCovered selected.memory selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size ∧
      selected.memory.size = max mem.size (result.toNat + 32 + 32 * kWords) := by
  simp only [selectBarrettCorrection] at hselect
  cases hfirst : selectBarrettDecision fuel mem aw n r2 result kWords with
  | none => rw [hfirst] at hselect; contradiction
  | some first =>
      rw [hfirst] at hselect
      cases hdoFirst : first.doSub with
      | false =>
          simp only [hdoFirst, Bool.false_eq_true, ↓reduceIte] at hselect
          injection hselect with hselected
          subst selected
          exact selectedBarrettDecision_false_geometry_from_start hkPos hkShift hr2Fit hnFit
            hresultFit hr2Mem hresultMem hresultAccessFit hcovered hawFit hfirst hdoFirst
      | true =>
          simp only [hdoFirst, ↓reduceIte] at hselect
          have hfirstGeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit hnFit
            hcovered hawFit hfirst hdoFirst
          let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
          have hpass1 := runBarrettPass_coverage_size kWords first.memory first.activeWords n r2
            hr2Fit hnFit (by rw [hfirstGeometry.1]; exact hr2Mem)
            (by rw [hfirstGeometry.1]; exact hnMem)
            (by rw [hfirstGeometry.1]; exact hfirstGeometry.2.1)
            hfirstGeometry.2.2
          have hpass1Size : pass1.memory.size = mem.size := by
            calc
              pass1.memory.size = first.memory.size := by simpa [pass1] using hpass1.2.2
              _ = mem.size := congrArg ByteArray.size hfirstGeometry.1
          cases hsecond : selectBarrettDecision fuel pass1.memory pass1.activeWords n r2 result
              kWords with
          | none => rw [hsecond] at hselect; contradiction
          | some second =>
              rw [hsecond] at hselect
              cases hdoSecond : second.doSub with
              | false =>
                  simp only [hdoSecond, Bool.false_eq_true, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  have hsecondGeometry := selectedBarrettDecision_false_geometry_from_start
                    hkPos hkShift hr2Fit hnFit hresultFit
                    (by rw [hpass1Size]; exact hr2Mem)
                    (by rw [hpass1Size]; exact hresultMem)
                    hresultAccessFit (by simpa [pass1] using hpass1.1)
                    (by simpa [pass1] using hpass1.2.1) hsecond hdoSecond
                  refine ⟨hsecondGeometry.1, hsecondGeometry.2.1, ?_⟩
                  rw [hsecondGeometry.2.2, hpass1Size]
              | true =>
                  simp only [hdoSecond, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  have hsecondGeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit
                    hnFit (by simpa [pass1] using hpass1.1)
                    (by simpa [pass1] using hpass1.2.1) hsecond hdoSecond
                  let pass2 := runBarrettPass second.memory second.activeWords n r2 kWords
                  have hpass2 := runBarrettPass_coverage_size kWords second.memory
                    second.activeWords n r2 hr2Fit hnFit
                    (by rw [hsecondGeometry.1, hpass1Size]; exact hr2Mem)
                    (by rw [hsecondGeometry.1, hpass1Size]; exact hnMem)
                    (by rw [hsecondGeometry.1]; exact hsecondGeometry.2.1)
                    hsecondGeometry.2.2
                  have hpass2Size : pass2.memory.size = mem.size := by
                    calc
                      pass2.memory.size = second.memory.size := by
                        simpa [pass2] using hpass2.2.2
                      _ = pass1.memory.size := congrArg ByteArray.size hsecondGeometry.1
                      _ = mem.size := hpass1Size
                  have hfinal := barrettFinal_coverage_size_from_start kWords pass2.memory
                    pass2.activeWords r2 result hkPos hkShift (by omega) hresultFit
                    (by rw [hpass2Size]; omega)
                    (by rw [hpass2Size]; exact hresultMem)
                    (by omega) hresultAccessFit
                    (by simpa [pass2] using hpass2.1)
                    (by simpa [pass2] using hpass2.2.1)
                  refine ⟨hfinal.1, hfinal.2.1, ?_⟩
                  rw [hfinal.2.2, hpass2Size]

/-- Every selected correction path preserves a complete persistent word range ending at or below
the r2 header.  Comparisons only read, subtraction passes write r2, and the final copy writes the
later result payload. -/
theorem selectedBarrettCorrection_memoryWords_below
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords ptr words : Nat} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) <= mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) <= mem.size)
    (hresultMem : result.toNat + 32 <= mem.size)
    (hresultAfterR2 : r2.toNat <= result.toNat + 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hbelow : ptr + 32 * words <= r2.toNat)
    (hselect : selectBarrettCorrection fuel mem aw n r2 result kWords = some selected) :
    memoryWordsFrom selected.memory ptr words = memoryWordsFrom mem ptr words := by
  have hread : ptr + 32 * words <= mem.size := by omega
  simp only [selectBarrettCorrection] at hselect
  cases hfirst : selectBarrettDecision fuel mem aw n r2 result kWords with
  | none => rw [hfirst] at hselect; contradiction
  | some first =>
      rw [hfirst] at hselect
      cases hdoFirst : first.doSub with
      | false =>
          simp only [hdoFirst, Bool.false_eq_true, ↓reduceIte] at hselect
          injection hselect with hselected
          subst selected
          rw [selectedBarrettDecision_memory_of_false hfirst hdoFirst]
          exact barrettFinalMemory_words_below kWords mem r2 result ptr words hkPos hkShift
            (by omega) hresultFit (by omega) (by omega) hread (by omega)
      | true =>
          simp only [hdoFirst, ↓reduceIte] at hselect
          have hfirstGeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit hnFit
            hcovered hawFit hfirst hdoFirst
          let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
          have hpass1Coverage := runBarrettPass_coverage_size kWords first.memory
            first.activeWords n r2 hr2Fit hnFit
            (by rw [hfirstGeometry.1]; exact hr2Mem)
            (by rw [hfirstGeometry.1]; exact hnMem)
            (by rw [hfirstGeometry.1]; exact hfirstGeometry.2.1)
            hfirstGeometry.2.2
          have hpass1Size : pass1.memory.size = mem.size := by
            calc
              pass1.memory.size = first.memory.size := by
                simpa [pass1] using hpass1Coverage.2.2
              _ = mem.size := congrArg ByteArray.size hfirstGeometry.1
          have hpass1Frame : memoryWordsFrom pass1.memory ptr words =
              memoryWordsFrom mem ptr words := by
            have hframe := runBarrettPass_memoryWords_below kWords first.memory
              first.activeWords n r2 ptr words hr2Fit hnFit
              (by rw [hfirstGeometry.1]; exact hr2Mem)
              (by rw [hfirstGeometry.1]; exact hnMem)
              (by rw [hfirstGeometry.1]; exact hfirstGeometry.2.1)
              hfirstGeometry.2.2 hbelow
            rw [show memoryWordsFrom first.memory ptr words = memoryWordsFrom mem ptr words by
              rw [hfirstGeometry.1]] at hframe
            simpa [pass1] using hframe
          cases hsecond : selectBarrettDecision fuel pass1.memory pass1.activeWords n r2 result
              kWords with
          | none => rw [hsecond] at hselect; contradiction
          | some second =>
              rw [hsecond] at hselect
              cases hdoSecond : second.doSub with
              | false =>
                  simp only [hdoSecond, Bool.false_eq_true, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  rw [selectedBarrettDecision_memory_of_false hsecond hdoSecond]
                  have hfinal := barrettFinalMemory_words_below kWords pass1.memory r2
                    result ptr words hkPos hkShift (by omega) hresultFit
                    (by rw [hpass1Size]; omega) (by rw [hpass1Size]; omega)
                    (by rw [hpass1Size]; exact hread) (by omega)
                  exact hfinal.trans hpass1Frame
              | true =>
                  simp only [hdoSecond, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  have hsecondGeometry := selectedBarrettDecision_true_geometry hkPos hr2Fit
                    hnFit (by simpa [pass1] using hpass1Coverage.1)
                    (by simpa [pass1] using hpass1Coverage.2.1) hsecond hdoSecond
                  let pass2 := runBarrettPass second.memory second.activeWords n r2 kWords
                  have hpass2Coverage := runBarrettPass_coverage_size kWords second.memory
                    second.activeWords n r2 hr2Fit hnFit
                    (by rw [hsecondGeometry.1, hpass1Size]; exact hr2Mem)
                    (by rw [hsecondGeometry.1, hpass1Size]; exact hnMem)
                    (by rw [hsecondGeometry.1]; exact hsecondGeometry.2.1)
                    hsecondGeometry.2.2
                  have hpass2Size : pass2.memory.size = mem.size := by
                    calc
                      pass2.memory.size = second.memory.size := by
                        simpa [pass2] using hpass2Coverage.2.2
                      _ = pass1.memory.size := congrArg ByteArray.size hsecondGeometry.1
                      _ = mem.size := hpass1Size
                  have hpass2Frame : memoryWordsFrom pass2.memory ptr words =
                      memoryWordsFrom mem ptr words := by
                    have hframe := runBarrettPass_memoryWords_below kWords second.memory
                      second.activeWords n r2 ptr words hr2Fit hnFit
                      (by rw [hsecondGeometry.1, hpass1Size]; exact hr2Mem)
                      (by rw [hsecondGeometry.1, hpass1Size]; exact hnMem)
                      (by rw [hsecondGeometry.1]; exact hsecondGeometry.2.1)
                      hsecondGeometry.2.2 hbelow
                    have hsecondFrame : memoryWordsFrom second.memory ptr words =
                        memoryWordsFrom mem ptr words := by
                      rw [hsecondGeometry.1]
                      exact hpass1Frame
                    rw [hsecondFrame] at hframe
                    simpa [pass2] using hframe
                  have hfinal := barrettFinalMemory_words_below kWords pass2.memory r2
                    result ptr words hkPos hkShift (by omega) hresultFit
                    (by rw [hpass2Size]; omega) (by rw [hpass2Size]; omega)
                    (by rw [hpass2Size]; exact hread) (by omega)
                  exact hfinal.trans hpass2Frame

def correctionLowValue (mem : ByteArray) (r2 : UInt256) (kWords : Nat) : Nat :=
  Modexp.wordLimbsToNat (memoryWordsFrom mem (r2.toNat + 32) kWords)

/-- Split the full candidate into low words and its top radix digit. -/
theorem correctionCandidateValue_split
    (mem : ByteArray) (r2 : UInt256) (kWords : Nat) :
    correctionCandidateValue mem r2 kWords =
      correctionLowValue mem r2 kWords + UInt256.size ^ kWords *
        (UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
          (r2.toNat + 32 + 32 * kWords))).toNat := by
  unfold correctionCandidateValue correctionLowValue
  rw [memoryWordsFrom_succ_eq_append, Modexp.wordLimbsToNat_append,
    memoryWordsFrom_length]
  simp [Modexp.wordLimbsToNat]

/-- Below any concrete `k`-word modulus, the full candidate has zero top digit and therefore
equals its low `k`-word value. -/
theorem correctionLowValue_eq_candidate_of_lt_modulus
    (mem : ByteArray) (n r2 : UInt256) (kWords : Nat)
    (hlt : correctionCandidateValue mem r2 kWords <
      correctionModulusValue mem n kWords) :
    correctionLowValue mem r2 kWords = correctionCandidateValue mem r2 kWords := by
  have hnBound := Modexp.wordLimbsToNat_lt_pow
    (memoryWordsFrom mem (n.toNat + 32) kWords)
  rw [memoryWordsFrom_length] at hnBound
  have hcandidateBound : correctionCandidateValue mem r2 kWords <
      UInt256.size ^ kWords := lt_trans hlt (by
        simpa [correctionModulusValue] using hnBound)
  rw [correctionCandidateValue_split] at hcandidateBound ⊢
  let top := UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat mem
    (r2.toNat + 32 + 32 * kWords))
  by_cases htop : top.toNat = 0
  · simp [top, htop]
  · have htopPos : 1 ≤ top.toNat := Nat.one_le_iff_ne_zero.mpr htop
    have hscaled : UInt256.size ^ kWords ≤ UInt256.size ^ kWords * top.toNat := by
      simpa using Nat.mul_le_mul_left (UInt256.size ^ kWords) htopPos
    dsimp only [top] at hscaled
    omega

/-- A false correction decision has already copied exactly its below-modulus candidate into the
result payload. -/
theorem selectedBarrettDecision_false_resultValue
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCompareSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 + 32 * kWords ≤ mem.size)
    (hresultMem : result.toNat + 32 ≤ mem.size)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (hfalse : selected.doSub = false)
    (hlt : correctionCandidateValue mem r2 kWords <
      correctionModulusValue mem n kWords) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory (result.toNat + 32) kWords) =
      correctionCandidateValue mem r2 kWords := by
  have hmemory := selectedBarrettDecision_memory_of_false hselect hfalse
  have hcopy := barrettFinalMemory_resultWords kWords mem r2 result hkPos hkShift
    hr2Fit hresultFit hr2Mem hresultMem
  have hlow := correctionLowValue_eq_candidate_of_lt_modulus mem n r2 kWords hlt
  rw [hmemory, hcopy]
  exact hlow

/-- The complete zero/one/two-pass selector stores exactly the pure two-correction value in the
result payload.  The `candidate < 3*n` premise is discharged by the pure Barrett quotient bound. -/
theorem selectedBarrettCorrection_resultValue
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords : Nat} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hresultMem : result.toNat + 32 ≤ mem.size)
    (hdisjoint : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hnValue : 0 < correctionModulusValue mem n kWords)
    (hcandidateBound : correctionCandidateValue mem r2 kWords <
      3 * correctionModulusValue mem n kWords)
    (hselect : selectBarrettCorrection fuel mem aw n r2 result kWords = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory (result.toNat + 32) kWords) =
      Modexp.barrettCorrectTwice (correctionModulusValue mem n kWords)
        (correctionCandidateValue mem r2 kWords) := by
  let nValue := correctionModulusValue mem n kWords
  let candidate0 := correctionCandidateValue mem r2 kWords
  simp only [selectBarrettCorrection] at hselect
  cases hfirst : selectBarrettDecision fuel mem aw n r2 result kWords with
  | none => rw [hfirst] at hselect; contradiction
  | some first =>
      rw [hfirst] at hselect
      have hfirstSem := selectedBarrettDecision_doSub_iff_memoryValue hkPos
        hr2Fit hnFit hr2Mem hnMem hcovered hawFit hfirst
      cases hdoFirst : first.doSub with
      | false =>
          simp only [hdoFirst, Bool.false_eq_true, ↓reduceIte] at hselect
          injection hselect with hselected
          subst selected
          have hlt0 : candidate0 < nValue := by
            have hnotGe : ¬correctionModulusValue mem n kWords ≤
                correctionCandidateValue mem r2 kWords := by
              intro hge
              have htrue := hfirstSem.mpr hge
              rw [hdoFirst] at htrue
              contradiction
            simpa [candidate0, nValue] using Nat.lt_of_not_ge hnotGe
          have hresult := selectedBarrettDecision_false_resultValue
            (fuel := fuel) (mem := mem) (aw := aw) (n := n) (r2 := r2)
            (result := result) (kWords := kWords) (selected := first)
            hkPos hkShift (by omega) hresultFit (by omega) hresultMem
            hfirst hdoFirst (by simpa [candidate0, nValue] using hlt0)
          rw [hresult]
          change candidate0 = Modexp.barrettCorrectTwice nValue candidate0
          have hnot : ¬nValue ≤ candidate0 := Nat.not_le_of_lt hlt0
          simp [Modexp.barrettCorrectTwice, hnot]
      | true =>
          simp only [hdoFirst, ↓reduceIte] at hselect
          let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
          have hge0 : nValue ≤ candidate0 := by
            simpa [nValue, candidate0] using hfirstSem.mp hdoFirst
          have hpass1 := selectedBarrettDecision_true_pass hkPos hr2Fit hnFit
            hr2Mem hnMem hdisjoint hcovered hawFit hfirst hdoFirst
          have hr2Mem1 : r2.toNat + 32 * (kWords + 2) ≤ pass1.memory.size := by
            rw [hpass1.2.2.2.1]
            exact hr2Mem
          have hnMem1 : n.toNat + 32 * (kWords + 1) ≤ pass1.memory.size := by
            rw [hpass1.2.2.2.1]
            exact hnMem
          have hresultMem1 : result.toNat + 32 ≤ pass1.memory.size := by
            rw [hpass1.2.2.2.1]
            exact hresultMem
          cases hsecond : selectBarrettDecision fuel pass1.memory pass1.activeWords n r2
              result kWords with
          | none => rw [hsecond] at hselect; contradiction
          | some second =>
              rw [hsecond] at hselect
              have hsecondSem := selectedBarrettDecision_doSub_iff_memoryValue hkPos
                hr2Fit hnFit hr2Mem1 hnMem1 hpass1.2.1 hpass1.2.2.1 hsecond
              cases hdoSecond : second.doSub with
              | false =>
                  simp only [hdoSecond, Bool.false_eq_true, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  have hlt1 : correctionCandidateValue pass1.memory r2 kWords <
                      correctionModulusValue pass1.memory n kWords := by
                    have hnotGe : ¬correctionModulusValue pass1.memory n kWords ≤
                        correctionCandidateValue pass1.memory r2 kWords := by
                      intro hge
                      have htrue := hsecondSem.mpr hge
                      rw [hdoSecond] at htrue
                      contradiction
                    exact Nat.lt_of_not_ge hnotGe
                  have hltOnce : candidate0 - nValue < nValue := by
                    calc
                      candidate0 - nValue =
                          correctionCandidateValue pass1.memory r2 kWords := by
                        simpa only [candidate0, nValue] using hpass1.1.symm
                      _ < correctionModulusValue pass1.memory n kWords := hlt1
                      _ = nValue := by
                        simpa only [nValue] using hpass1.2.2.2.2
                  have hresult := selectedBarrettDecision_false_resultValue
                    (fuel := fuel) (mem := pass1.memory) (aw := pass1.activeWords)
                    (n := n) (r2 := r2) (result := result) (kWords := kWords)
                    (selected := second) hkPos hkShift (by omega) hresultFit
                    (by omega) hresultMem1 hsecond hdoSecond hlt1
                  rw [hresult, hpass1.1]
                  simp [Modexp.barrettCorrectTwice, nValue, candidate0,
                    if_pos hge0, if_neg (Nat.not_le_of_lt hltOnce)]
              | true =>
                  simp only [hdoSecond, ↓reduceIte] at hselect
                  let pass2 := runBarrettPass second.memory second.activeWords n r2 kWords
                  have hge1 : correctionModulusValue pass1.memory n kWords ≤
                      correctionCandidateValue pass1.memory r2 kWords :=
                    hsecondSem.mp hdoSecond
                  have hgeOnce : nValue ≤ candidate0 - nValue := by
                    calc
                      nValue = correctionModulusValue pass1.memory n kWords := by
                        simpa only [nValue] using hpass1.2.2.2.2.symm
                      _ ≤ correctionCandidateValue pass1.memory r2 kWords := hge1
                      _ = candidate0 - nValue := by
                        simpa only [candidate0, nValue] using hpass1.1
                  have hpass2 := selectedBarrettDecision_true_pass hkPos hr2Fit hnFit
                    hr2Mem1 hnMem1 hdisjoint hpass1.2.1 hpass1.2.2.1
                    hsecond hdoSecond
                  have hcandidate2Lt : correctionCandidateValue pass2.memory r2 kWords <
                      correctionModulusValue pass2.memory n kWords := by
                    rw [hpass2.1, hpass2.2.2.2.2, hpass1.1,
                      hpass1.2.2.2.2]
                    omega
                  have hpass2Mem : pass2.memory.size = mem.size := by
                    exact hpass2.2.2.2.1.trans hpass1.2.2.2.1
                  have hcopy := barrettFinalMemory_resultWords kWords pass2.memory r2 result
                    hkPos hkShift (by omega) hresultFit (by rw [hpass2Mem]; omega)
                    (by rw [hpass2Mem]; exact hresultMem)
                  have hlow := correctionLowValue_eq_candidate_of_lt_modulus
                    pass2.memory n r2 kWords hcandidate2Lt
                  injection hselect with hselected
                  subst selected
                  rw [hcopy]
                  change correctionLowValue pass2.memory r2 kWords =
                    Modexp.barrettCorrectTwice nValue candidate0
                  rw [hlow, hpass2.1, hpass1.1, hpass1.2.2.2.2]
                  simp [Modexp.barrettCorrectTwice, if_pos hge0, if_pos hgeOnce,
                    candidate0, nValue]

/-- If the concrete modulus and candidate windows have been connected to the deployed Barrett
estimate, the exposed correction selector's result payload is the ordinary remainder. -/
theorem selectedBarrettCorrection_resultValue_eq_mod
    {fuel : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    {kWords nValue x : Nat} {selected : BarrettCorrectionSelection}
    (hkPos : 0 < kWords) (hkShift : kWords < 2 ^ 251)
    (hr2Fit : r2.toNat + 32 * (kWords + 2) + 31 < UInt256.size)
    (hnFit : n.toNat + 32 * (kWords + 1) + 31 < UInt256.size)
    (hresultFit : result.toNat + 32 < UInt256.size)
    (hr2Mem : r2.toNat + 32 * (kWords + 2) ≤ mem.size)
    (hnMem : n.toNat + 32 * (kWords + 1) ≤ mem.size)
    (hresultMem : result.toNat + 32 ≤ mem.size)
    (hdisjoint : n.toNat + 32 * (kWords + 1) ≤ r2.toNat)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hnPos : 0 < nValue)
    (hnNormalized : UInt256.size ^ (kWords - 1) ≤ nValue)
    (hx : x < UInt256.size ^ (2 * kWords))
    (hnValue : correctionModulusValue mem n kWords = nValue)
    (hcandidate : correctionCandidateValue mem r2 kWords =
      Modexp.deployedBarrettCandidate kWords nValue x)
    (hselect : selectBarrettCorrection fuel mem aw n r2 result kWords = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory (result.toNat + 32) kWords) =
      x % nValue := by
  have hbounds := Modexp.barrettQ3_bounds kWords nValue x hkPos hnPos hnNormalized hx
  have hcandidateBound : correctionCandidateValue mem r2 kWords <
      3 * correctionModulusValue mem n kWords := by
    rw [hnValue, hcandidate]
    unfold Modexp.deployedBarrettCandidate
    omega
  have hresult := selectedBarrettCorrection_resultValue hkPos hkShift hr2Fit hnFit
    hresultFit hr2Mem hnMem hresultMem hdisjoint hcovered hawFit
    (by rw [hnValue]; exact hnPos) hcandidateBound hselect
  rw [hnValue, hcandidate] at hresult
  exact hresult.trans
    (Modexp.deployedBarrettCorrect_eq_mod
      kWords nValue x hkPos hnPos hnNormalized hx)

end Modexp.MultiLimbBarrettCorrectionSemantic
