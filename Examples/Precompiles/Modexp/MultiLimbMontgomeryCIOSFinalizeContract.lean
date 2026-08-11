import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeZero
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeNonzero

/-! # Pure contract of selected CIOS finalization -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomeryCIOSSemantic

open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCompareTrace
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 2000
set_option maxHeartbeats 500000

/-- The selected CIOS finalizer stores the pure Montgomery finalization of the complete
`columns + 1` word scratch value. -/
theorem selectedCIOSFinalize_value
    (columns : Nat) {compareFuel subFuel : Nat} (mem : ByteArray)
    (aw nBefore tP bytes tEnd nP resultPtr resultBase : UInt256)
    (selected : CIOSFinalizeSelection)
    (geometry : CIOSFinalizeGeometry columns mem aw nBefore tP bytes tEnd nP
      resultPtr resultBase)
    (hselect : selectCIOSFinalize compareFuel subFuel mem aw nBefore tP bytes tEnd
      nP resultPtr resultBase = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.memory resultPtr.toNat columns) =
      Modexp.montgomeryFinalize
        (limbsWithTop (memoryWordsFrom mem tP.toNat columns)
          (finalTopWord mem aw tEnd))
        (Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat columns)) := by
  unfold selectCIOSFinalize at hselect
  dsimp only at hselect
  by_cases htop : finalTopWord mem aw tEnd = ⟨0⟩
  · rw [if_pos htop] at hselect
    have hguard : tEnd.gt tP ≠ ⟨0⟩ := by
      intro hzero
      rw [if_pos hzero] at hselect
      contradiction
    rw [if_neg hguard] at hselect
    cases hcomparison : selectCIOSCompare compareFuel mem tP (finalTopAw aw tEnd)
        tEnd (⟨32⟩ + (bytes + nBefore)) (comparePrev tEnd) with
    | none =>
        rw [hcomparison] at hselect
        contradiction
    | some comparison =>
        rw [hcomparison] at hselect
        simp only at hselect
        cases hcopy : selectCIOSCopy subFuel mem comparison.activeWords tP bytes
            comparison.doSub resultPtr nP resultBase with
        | none =>
            rw [hcopy] at hselect
            contradiction
        | some copy =>
            rw [hcopy] at hselect
            injection hselect with heq
            subst selected
            exact selectedCIOSFinalizeZero_value columns mem aw nBefore tP bytes
              tEnd nP resultPtr resultBase comparison copy geometry htop hcomparison
              hcopy
  · rw [if_neg htop] at hselect
    cases hcopy : selectCIOSCopy subFuel mem (finalTopAw aw tEnd) tP bytes ⟨1⟩
        resultPtr nP resultBase with
    | none =>
        rw [hcopy] at hselect
        contradiction
    | some copy =>
        rw [hcopy] at hselect
        injection hselect with heq
        subst selected
        exact selectedCIOSFinalizeNonzero_value columns mem aw nBefore tP bytes
          tEnd nP resultPtr resultBase copy geometry htop hcopy

end Modexp.MultiLimbMontgomeryCIOSSemantic
