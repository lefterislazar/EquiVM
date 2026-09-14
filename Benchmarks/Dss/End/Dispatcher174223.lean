import Benchmarks.Dss.End.Dispatcher65

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

theorem endSplit163WellFormed : selectorSplitWellFormed endBytecode ⟨163⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endArms174WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨174⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem endArms223WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨223⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

def endArm174Index : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 27
  | _ => 17

def endArm223Index : Nat → Nat
  | 0 => 26
  | 1 => 16
  | 2 => 8
  | _ => 19

theorem endArm174Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm174Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm174Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endArm223Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm223Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm223Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endReachFirstArm174 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp43 : UInt256.gt (armSelNat endBytecode ⟨43⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp163 : UInt256.gt (armSelNat endBytecode ⟨163⟩) (endRuntimeSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨174⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 := RD.selectorSplitNotTakenAuto h32 endSplit32WellFormed hp32 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h43
  have h162 := RD.selectorSplitTakenAuto h43 endSplit43WellFormed hp43 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h162
  have h163 := h162.jumpdest (by native_decide) (by simp)
  have h174 := RD.selectorSplitNotTakenAuto h163 endSplit163WellFormed hp163 (by simp)
  exact ⟨_, _, by simpa using h174⟩

theorem endReachFirstArm223 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp43 : UInt256.gt (armSelNat endBytecode ⟨43⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp163 : UInt256.gt (armSelNat endBytecode ⟨163⟩) (endRuntimeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨223⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 := RD.selectorSplitNotTakenAuto h32 endSplit32WellFormed hp32 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h43
  have h162 := RD.selectorSplitTakenAuto h43 endSplit43WellFormed hp43 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨162⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h162
  have h163 := h162.jumpdest (by native_decide) (by simp)
  have h222 := RD.selectorSplitTakenAuto h163 endSplit163WellFormed hp163 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨222⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h222
  have h223 := h222.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, by simpa using h223⟩

theorem endReachDog {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 3)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1017⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 3 (by omega) hsel
  obtain ⟨_, _, h174⟩ := endReachFirstArm174 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm174Eq I hsz 0 (by omega))
      (by simpa [endArm174Index] using
        endSelectorMiss_of_match 0 3 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm174Eq I hsz 1 (by omega))
      (by simpa [endArm174Index] using hsel)
  exact RD.dispatchTo ⟨1017⟩ 1 h174
    (fun j hj => endArms174WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachLive {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 8)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨933⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 8 (by omega) hsel
  obtain ⟨_, _, h223⟩ := endReachFirstArm223 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm223Eq I hsz 0 (by omega))
        (by simpa [endArm223Index] using
          endSelectorMiss_of_match 26 8 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm223Eq I hsz 1 (by omega))
        (by simpa [endArm223Index] using
          endSelectorMiss_of_match 16 8 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm223Eq I hsz 2 (by omega))
      (by simpa [endArm223Index] using hsel)
  exact RD.dispatchTo ⟨933⟩ 2 h223
    (fun j hj => endArms223WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachFree {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 27)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1025⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 27 (by omega) hsel
  obtain ⟨_, _, h174⟩ := endReachFirstArm174 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm174Eq I hsz 0 (by omega))
        (by simpa [endArm174Index] using
          endSelectorMiss_of_match 0 27 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm174Eq I hsz 1 (by omega))
        (by simpa [endArm174Index] using
          endSelectorMiss_of_match 3 27 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm174Eq I hsz 2 (by omega))
      (by simpa [endArm174Index] using hsel)
  exact RD.dispatchTo ⟨1025⟩ 2 h174
    (fun j hj => endArms174WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachSkim {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 26)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 26 (by omega) hsel
  obtain ⟨_, _, h223⟩ := endReachFirstArm223 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm223Eq I hsz 0 (by omega))
      (by simpa [endArm223Index] using hsel)
  exact RD.dispatchTo ⟨851⟩ 0 h223
    (fun j hj => endArms223WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

end Benchmarks.Dss.End
