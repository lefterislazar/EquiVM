import Benchmarks.ActAmm4.Common
import Reasoning.Stepping

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000000 in
theorem amm4X_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = amm4Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 9 → (amm4SelBytes i == I.calldata.extract 0 4) = false) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLow0 : ∀ j, j < 4 →
      UInt256.eq
        (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4LowFirstArmPc j))
        (amm4SelWord I) = ⟨0⟩ := by
    intro j hj
    rw [amm4LowArmEq I hsz j hj, hnm j (by omega)]
    rfl
  have heqHigh0 : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat amm4Bytecode (nthArmPc amm4Bytecode amm4HighFirstArmPc j))
        (amm4SelWord I) = ⟨0⟩ := by
    intro j hj
    rw [amm4HighArmEq I hsz j hj, hnm (j + 4) (by omega)]
    rfl
  obtain ⟨kS, CS, hsplit⟩ := amm4ReachSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  by_cases hpivot : UInt256.gt (armSelNat amm4Bytecode amm4SplitPc) (amm4SelWord I) = ⟨0⟩
  · have h41 := RD.selectorSplitNotTakenAuto hsplit amm4SplitWellFormed hpivot (by simp)
    have h96 := h41
      |>.selectorArmNotTakenAuto (amm4HighArmsWellFormed 0 (by omega))
          (heqHigh0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4HighArmsWellFormed 1 (by omega))
          (heqHigh0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4HighArmsWellFormed 2 (by omega))
          (heqHigh0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4HighArmsWellFormed 3 (by omega))
          (heqHigh0 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4HighArmsWellFormed 4 (by omega))
          (heqHigh0 4 (by omega)) (by simp)
    have h96' : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨96⟩
        [amm4SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 5 + 5 + 5 + 5 + 5, CS + 22 + 22 + 22 + 22 + 22 + 22, ?_⟩
      simpa [amm4HighFirstArmPc, amm4SplitPc, nthArmPc, selArmNextPc, armTgtWidth,
        selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using h96
    obtain ⟨_, _, h96rd⟩ := h96'
    exact evm_run h96rd with [
      push2 ⟨145⟩, jump (by jump_dest), jumpdest,
      raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov) ]
  · have h100 := RD.selectorSplitTakenAuto hsplit amm4SplitWellFormed hpivot
      (by jump_dest) (by simp)
    have h101 := h100.jumpdest (by native_decide) (by simp)
    have h145 := h101
      |>.selectorArmNotTakenAuto (amm4LowArmsWellFormed 0 (by omega))
          (heqLow0 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4LowArmsWellFormed 1 (by omega))
          (heqLow0 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4LowArmsWellFormed 2 (by omega))
          (heqLow0 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (amm4LowArmsWellFormed 3 (by omega))
          (heqLow0 3 (by omega)) (by simp)
    have h145' : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨145⟩
        [amm4SelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      refine ⟨kS + 5 + 1 + 5 + 5 + 5 + 5,
        CS + 22 + 1 + 22 + 22 + 22 + 22, ?_⟩
      simpa [amm4LowFirstArmPc, amm4LowJumpdestPc, amm4SplitPc, nthArmPc, selArmNextPc,
        armTgtWidth, armTgt, pushAt, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
        selArmPush4Pc] using h145
    obtain ⟨_, _, h145rd⟩ := h145'
    exact evm_run h145rd with [
      jumpdest, raw revertStub (by native_decide) (by native_decide)
        (by native_decide) (by evm_ov) ]

end Benchmarks.ActAmm4
