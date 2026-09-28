import Benchmarks.ActAmm.Common
import Reasoning.Stepping

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem ammX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ammBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 10 → (ammSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat ammBytecode (nthArmPc ammBytecode ammLowFirstArmPc j))
        (ammSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [ammLowArmEq I hsz j hj, hnm j (by omega)]
    rfl
  have heqHigh0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat ammBytecode (nthArmPc ammBytecode ammHighFirstArmPc j))
        (ammSelWord I) = ⟨0⟩ := by
    intro j hj
    rw [ammHighArmEq I hsz j hj, hnm (j + 5) (by omega)]
    rfl
  obtain ⟨kS, CS, hsplit⟩ := ammReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat ammBytecode ammSplitPc) (ammSelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit ammSplitWellFormed hpivot (by simp)
    have h96 := h41
      |>.selectorArmNotTakenAuto (ammHighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammHighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammHighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammHighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammHighArmsWellFormed 4 (by omega))
          (heqHigh0 4 (by omega)) (by simp)
    have h96' : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨96⟩
        [ammSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [ammHighFirstArmPc, ammSplitPc, nthArmPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h96
    obtain ⟨_, _, h96rd⟩ := h96'
    exact evm_run h96rd with [
      push2 ⟨156⟩, jump (by jump_dest), jumpdest,
      raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]
  · have h100 := RD.selectorSplitTakenAuto hsplit ammSplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h101 := h100.jumpdest (by native_decide) (by simp)
    have h156 := h101
      |>.selectorArmNotTakenAuto (ammLowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammLowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammLowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammLowArmsWellFormed 3 (by omega))
          (heqLow0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (ammLowArmsWellFormed 4 (by omega))
          (heqLow0 4 (by omega)) (by simp)
    have h156' : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨156⟩
        [ammSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5 + 5,
        CS + 22 + 1 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [ammLowFirstArmPc, ammLowJumpdestPc, ammSplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
        selArmPush4Pc] using h156
    obtain ⟨_, _, h156rd⟩ := h156'
    exact evm_run h156rd with [
      jumpdest, raw revertStub (by native_decide) (by native_decide)
        (by native_decide) (by evm_ov) ]

end Benchmarks.ActAmm
