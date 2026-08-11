import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeLinks

/-! # Selected CIOS comparison coverage -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbMontgomeryCIOSCall
open Modexp.MultiLimbMontgomeryCompareTrace

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Every successful selected comparison returns an active-word count covering the unchanged
memory after all concrete descending loads. -/
theorem selectedCIOSCompare_coverage
    (columns : Nat) {fuel : Nat} {mem : ByteArray} {tP : UInt256}
    {state : CompareState} {prevTOff : UInt256} {selected : CIOSCompareSelection}
    (candidateBase modulusBase : Nat)
    (hcolumns : 0 < columns)
    (htOff : state.tOff.toNat = candidateBase + 32 * columns)
    (hnOff : state.nOff.toNat = modulusBase + 32 * columns)
    (htBase : candidateBase = tP.toNat)
    (htFit : candidateBase + 32 * columns + 31 < UInt256.size)
    (hnFit : modulusBase + 32 * columns + 31 < UInt256.size)
    (hcovered : MemoryCovered mem state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hprev : prevTOff = comparePrev state.tOff)
    (hselect : selectCIOSCompare fuel mem tP state.activeWords state.tOff state.nOff
      prevTOff = some selected) :
    MemoryCovered mem selected.activeWords ∧
      selected.activeWords.toNat * 32 < UInt256.size := by
  induction columns generalizing fuel state prevTOff selected with
  | zero => omega
  | succ columns ih =>
      cases fuel with
      | zero => simp [selectCIOSCompare] at hselect
      | succ fuel =>
          simp only [selectCIOSCompare] at hselect
          have htLo : 32 ≤ state.tOff.toNat := by rw [htOff]; omega
          have hnLo : 32 ≤ state.nOff.toNat := by rw [hnOff]; omega
          have htPrev : (comparePrev state.tOff).toNat =
              candidateBase + 32 * columns := by
            rw [comparePrev_toNat state.tOff htLo, htOff]
            omega
          have hnPrev : (comparePrev state.nOff).toNat =
              modulusBase + 32 * columns := by
            rw [comparePrev_toNat state.nOff hnLo, hnOff]
            omega
          have hnextCoverage := compareAdvance_coverage mem state hcovered hawFit
            (by rw [htPrev]; omega) (by rw [hnPrev]; omega)
          by_cases hgreater :
              (compareNWord mem state.activeWords state.tOff state.nOff).toNat <
                (compareTWord mem state.activeWords state.tOff).toNat
          · rw [if_pos hgreater] at hselect
            injection hselect with heq
            subst selected
            simpa [compareAdvance] using hnextCoverage
          · rw [if_neg hgreater] at hselect
            by_cases hless :
                (compareTWord mem state.activeWords state.tOff).toNat <
                  (compareNWord mem state.activeWords state.tOff state.nOff).toNat
            · rw [if_pos hless] at hselect
              injection hselect with heq
              subst selected
              simpa [compareAdvance] using hnextCoverage
            · rw [if_neg hless] at hselect
              by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
              · rw [if_pos hguard] at hselect
                have hcolumnsPos : 0 < columns := by
                  by_contra hzero
                  have hcolumnsZero : columns = 0 := by omega
                  subst columns
                  apply hguard
                  apply ugt_zero
                  have hprevNat : prevTOff.toNat = tP.toNat := by
                    rw [hprev, comparePrev_toNat state.tOff htLo, htOff, htBase]
                    omega
                  omega
                let next := compareAdvance state
                cases hrest : selectCIOSCompare fuel mem tP next.activeWords next.tOff
                    next.nOff (comparePrev prevTOff) with
                | none =>
                    have hrest' : selectCIOSCompare fuel mem tP
                        (compareAw state.activeWords state.tOff state.nOff) prevTOff
                        (comparePrev state.nOff) (comparePrev prevTOff) = none := by
                      simpa [next, compareAdvance, hprev] using hrest
                    rw [hrest'] at hselect
                    contradiction
                | some rest =>
                    have hrest' : selectCIOSCompare fuel mem tP
                        (compareAw state.activeWords state.tOff state.nOff) prevTOff
                        (comparePrev state.nOff) (comparePrev prevTOff) = some rest := by
                      simpa [next, compareAdvance, hprev] using hrest
                    rw [hrest'] at hselect
                    injection hselect with heq
                    subst selected
                    apply ih (fuel := fuel) (state := next)
                      (prevTOff := comparePrev prevTOff) (selected := rest) hcolumnsPos
                    · simpa [next, compareAdvance] using htPrev
                    · simpa [next, compareAdvance] using hnPrev
                    · omega
                    · omega
                    · exact hnextCoverage.1
                    · exact hnextCoverage.2
                    · simp [next, compareAdvance, hprev]
                    · exact hrest
              · rw [if_neg hguard] at hselect
                injection hselect with heq
                subst selected
                simpa [compareAdvance] using hnextCoverage

end Modexp.MultiLimbMontgomeryCIOSSemantic
