import Benchmarks.Dss.End.Dispatcher

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

theorem endSplit43WellFormed : selectorSplitWellFormed endBytecode ⟨43⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endSplit54WellFormed : selectorSplitWellFormed endBytecode ⟨54⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endArms65WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨65⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

def endArm65Index : Nat → Nat
  | 0 => 2
  | 1 => 13
  | 2 => 12
  | _ => 31

theorem endArm65Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm65Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm65Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endReachFirstArm65 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp43 : UInt256.gt (armSelNat endBytecode ⟨43⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp54 : UInt256.gt (armSelNat endBytecode ⟨54⟩) (endRuntimeSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨65⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 := RD.selectorSplitNotTakenAuto h32 endSplit32WellFormed hp32 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h43
  have h54 := RD.selectorSplitNotTakenAuto h43 endSplit43WellFormed hp43 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h54
  have h65 := RD.selectorSplitNotTakenAuto h54 endSplit54WellFormed hp54 (by simp)
  exact ⟨_, _, by simpa using h65⟩

theorem endReachCat {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 2)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1208⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 2 (by omega) hsel
  obtain ⟨_, _, h65⟩ := endReachFirstArm65 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm65Eq I hsz 0 (by omega))
      (by simpa [endArm65Index] using hsel)
  exact RD.dispatchTo ⟨1208⟩ 0 h65
    (fun j hj => endArms65WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachCash {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 31)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1274⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 31 (by omega) hsel
  obtain ⟨_, _, h65⟩ := endReachFirstArm65 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm65Eq I hsz 0 (by omega))
        (by simpa [endArm65Index] using
          endSelectorMiss_of_match 2 31 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm65Eq I hsz 1 (by omega))
        (by simpa [endArm65Index] using
          endSelectorMiss_of_match 13 31 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm65Eq I hsz 2 (by omega))
        (by simpa [endArm65Index] using
          endSelectorMiss_of_match 12 31 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm65Eq I hsz 3 (by omega))
      (by simpa [endArm65Index] using hsel)
  exact RD.dispatchTo ⟨1274⟩ 3 h65
    (fun j hj => endArms65WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

end Benchmarks.Dss.End
