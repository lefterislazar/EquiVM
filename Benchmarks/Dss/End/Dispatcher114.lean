import Benchmarks.Dss.End.Dispatcher65

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

theorem endArms114WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨114⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

def endArm114Index : Nat → Nat
  | 0 => 20
  | 1 => 14
  | 2 => 23
  | _ => 9

theorem endArm114Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm114Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm114Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endReachFirstArm114 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp43 : UInt256.gt (armSelNat endBytecode ⟨43⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp54 : UInt256.gt (armSelNat endBytecode ⟨54⟩) (endRuntimeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 := RD.selectorSplitNotTakenAuto h32 endSplit32WellFormed hp32 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h43
  have h54 := RD.selectorSplitNotTakenAuto h43 endSplit43WellFormed hp43 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h54
  have h113 := RD.selectorSplitTakenAuto h54 endSplit54WellFormed hp54 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h113
  have h114 := h113.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, by simpa using h114⟩

theorem endReachWhen {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 9)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1200⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 9 (by omega) hsel
  obtain ⟨_, _, h114⟩ := endReachFirstArm114 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm114Eq I hsz 0 (by omega))
        (by simpa [endArm114Index] using
          endSelectorMiss_of_match 20 9 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm114Eq I hsz 1 (by omega))
        (by simpa [endArm114Index] using
          endSelectorMiss_of_match 14 9 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm114Eq I hsz 2 (by omega))
        (by simpa [endArm114Index] using
          endSelectorMiss_of_match 23 9 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm114Eq I hsz 3 (by omega))
      (by simpa [endArm114Index] using hsel)
  exact RD.dispatchTo ⟨1200⟩ 3 h114
    (fun j hj => endArms114WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachCageIlk {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 23)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1171⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 23 (by omega) hsel
  obtain ⟨_, _, h114⟩ := endReachFirstArm114 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm114Eq I hsz 0 (by omega))
        (by simpa [endArm114Index] using
          endSelectorMiss_of_match 20 23 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm114Eq I hsz 1 (by omega))
        (by simpa [endArm114Index] using
          endSelectorMiss_of_match 14 23 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm114Eq I hsz 2 (by omega))
      (by simpa [endArm114Index] using hsel)
  exact RD.dispatchTo ⟨1171⟩ 2 h114
    (fun j hj => endArms114WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

end Benchmarks.Dss.End
