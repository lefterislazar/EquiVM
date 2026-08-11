import Examples.Precompiles.Modexp.MultiLimbSchoolbookNonzeroPrefix
import Examples.Precompiles.Modexp.MultiLimbArrayReadSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortSemantic

/-!
# Constructive dividend-trim selector

The deployed division scans allocated dividend limbs from high to low.  This finite selector
constructs exactly the all-zero or first-nonzero case selected by that scan, including the number
of charged zero-limb cycles.
-/

open Ethereum

namespace Modexp.MultiLimbSchoolbookTrimSelection

open MultiLimbSchoolbookTrim

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

/-- Exposed result of the high-to-low dividend trim. -/
inductive Selection (mem : ByteArray) (aw dividend : UInt256) (count : Nat) : Prop
  | allZero
      (zero : ∀ i, i < count → dividendWord mem aw dividend i = ⟨0⟩) : Selection mem aw dividend count
  | nonzero
      (m zeroLimbs : Nat) (top : UInt256)
      (mPos : 0 < m)
      (countEq : count = m + zeroLimbs)
      (zero : ∀ i, m ≤ i → i < m + zeroLimbs → dividendWord mem aw dividend i = ⟨0⟩)
      (topEq : dividendWord mem aw dividend (m - 1) = top)
      (topNe : top ≠ ⟨0⟩) : Selection mem aw dividend count

/-- Every finite concrete payload has a constructive trim selection. -/
theorem selection_exists (mem : ByteArray) (aw dividend : UInt256) (count : Nat) :
    Selection mem aw dividend count := by
  induction count with
  | zero =>
      exact Selection.allZero (by intro i hi; omega)
  | succ count ih =>
      let current := dividendWord mem aw dividend count
      by_cases hcurrent : current = ⟨0⟩
      · cases ih with
        | allZero hzero =>
            apply Selection.allZero
            intro i hi
            by_cases hlt : i < count
            · exact hzero i hlt
            · have hiEq : i = count := by omega
              subst i
              exact hcurrent
        | nonzero m zeroLimbs top hmPos hcountEq hzero htop htopNe =>
            apply Selection.nonzero m (zeroLimbs + 1) top hmPos
            · omega
            · intro i hmi hi
              by_cases hlt : i < count
              · apply hzero i hmi
                omega
              · have hiEq : i = count := by omega
                subst i
                exact hcurrent
            · exact htop
            · exact htopNe
      · apply Selection.nonzero (count + 1) 0 current (by omega)
        · omega
        · intro i hmi hi
          omega
        · have hindex : count + 1 - 1 = count := by omega
          rw [hindex]
        · exact hcurrent

/-- The numeric payload selected by the all-zero scan is exactly zero. -/
theorem allZero_value
    (mem : ByteArray) (aw dividend : UInt256) (count : Nat)
    (hzero : ∀ i, i < count → dividendWord mem aw dividend i = ⟨0⟩) :
    wordLimbsToNat
      (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords
        mem aw dividend 0 count) = 0 := by
  apply MultiLimbSchoolbookShortSemantic.arrayReadWords_toNat_eq_zero
  intro i hi
  simpa only [Nat.zero_add, dividendWord, MultiLimbSchoolbookNormalization.arrayWord,
    MultiLimbSchoolbookSingle.arrayWord] using hzero i hi

/-- A `count`-word value reaching the radix weight of its top limb has a nonzero top word. -/
theorem top_nonzero_of_value_lower
    (mem : ByteArray) (aw array : UInt256) (count : Nat)
    (hcountPos : 0 < count)
    (hlower : UInt256.size ^ (count - 1) ≤
      wordLimbsToNat
        (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw array 0 count)) :
    MultiLimbSchoolbookNormalization.arrayWord mem aw array (count - 1) ≠ ⟨0⟩ := by
  intro htop
  have hsplit := MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_succ_append
    mem aw array 0 (count - 1)
  have hcount : count - 1 + 1 = count := by omega
  rw [hcount] at hsplit
  simp only [Nat.zero_add] at hsplit
  rw [hsplit, wordLimbsToNat_append, htop] at hlower
  simp only [wordLimbsToNat, show (⟨0⟩ : UInt256).toNat = 0 by decide,
    Nat.add_zero, Nat.mul_zero] at hlower
  have hupper := wordLimbsToNat_lt_pow
    (MultiLimbSchoolbookNormalizationSemantic.arrayReadWords mem aw array 0 (count - 1))
  rw [MultiLimbSchoolbookNormalizationSemantic.arrayReadWords_length] at hupper
  omega

end Modexp.MultiLimbSchoolbookTrimSelection
