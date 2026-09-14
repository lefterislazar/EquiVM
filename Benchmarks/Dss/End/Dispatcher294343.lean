import Benchmarks.Dss.End.Dispatcher

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

theorem endSplit283WellFormed : selectorSplitWellFormed endBytecode ⟨283⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endArms294WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨294⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

theorem endArms343WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨343⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

def endArm294Index : Nat → Nat
  | 0 => 22
  | 1 => 30
  | 2 => 6
  | _ => 7

def endArm343Index : Nat → Nat
  | 0 => 4
  | 1 => 15
  | 2 => 10
  | _ => 18

theorem endArm294Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm294Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm294Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endArm343Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm343Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm343Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endReachFirstArm294 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp272 : UInt256.gt (armSelNat endBytecode ⟨272⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp283 : UInt256.gt (armSelNat endBytecode ⟨283⟩) (endRuntimeSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨294⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 := RD.selectorSplitTakenAuto h32 endSplit32WellFormed hp32 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨271⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h271
  have h272 := h271.jumpdest (by native_decide) (by simp)
  have h283 := RD.selectorSplitNotTakenAuto h272 endSplit272WellFormed hp272 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨283⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h283
  have h294 := RD.selectorSplitNotTakenAuto h283 endSplit283WellFormed hp283 (by simp)
  exact ⟨_, _, by simpa using h294⟩

theorem endReachFirstArm343 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp272 : UInt256.gt (armSelNat endBytecode ⟨272⟩) (endRuntimeSelWord I) = ⟨0⟩)
    (hp283 : UInt256.gt (armSelNat endBytecode ⟨283⟩) (endRuntimeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨343⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 := RD.selectorSplitTakenAuto h32 endSplit32WellFormed hp32 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨271⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h271
  have h272 := h271.jumpdest (by native_decide) (by simp)
  have h283 := RD.selectorSplitNotTakenAuto h272 endSplit272WellFormed hp272 (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨283⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h283
  have h342 := RD.selectorSplitTakenAuto h283 endSplit283WellFormed hp283 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨342⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h342
  have h343 := h342.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, by simpa using h343⟩

theorem endReachVow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 4)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨715⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 4 (by omega) hsel
  obtain ⟨_, _, h343⟩ := endReachFirstArm343 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm343Eq I hsz 0 (by omega))
      (by simpa [endArm343Index] using hsel)
  exact RD.dispatchTo ⟨715⟩ 0 h343
    (fun j hj => endArms343WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachSpot {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 6)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨835⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 6 (by omega) hsel
  obtain ⟨_, _, h294⟩ := endReachFirstArm294 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm294Eq I hsz 0 (by omega))
        (by simpa [endArm294Index] using
          endSelectorMiss_of_match 22 6 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm294Eq I hsz 1 (by omega))
        (by simpa [endArm294Index] using
          endSelectorMiss_of_match 30 6 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm294Eq I hsz 2 (by omega))
      (by simpa [endArm294Index] using hsel)
  exact RD.dispatchTo ⟨835⟩ 2 h294
    (fun j hj => endArms294WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachCure {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 7)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨843⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 7 (by omega) hsel
  obtain ⟨_, _, h294⟩ := endReachFirstArm294 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm294Eq I hsz 0 (by omega))
        (by simpa [endArm294Index] using
          endSelectorMiss_of_match 22 7 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm294Eq I hsz 1 (by omega))
        (by simpa [endArm294Index] using
          endSelectorMiss_of_match 30 7 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm294Eq I hsz 2 (by omega))
        (by simpa [endArm294Index] using
          endSelectorMiss_of_match 6 7 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm294Eq I hsz 3 (by omega))
      (by simpa [endArm294Index] using hsel)
  exact RD.dispatchTo ⟨843⟩ 3 h294
    (fun j hj => endArms294WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachWait {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 10)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨752⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 10 (by omega) hsel
  obtain ⟨_, _, h343⟩ := endReachFirstArm343 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm343Eq I hsz 0 (by omega))
        (by simpa [endArm343Index] using
          endSelectorMiss_of_match 4 10 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm343Eq I hsz 1 (by omega))
        (by simpa [endArm343Index] using
          endSelectorMiss_of_match 15 10 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm343Eq I hsz 2 (by omega))
      (by simpa [endArm343Index] using hsel)
  exact RD.dispatchTo ⟨752⟩ 2 h343
    (fun j hj => endArms343WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachCage {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 22)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨798⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 22 (by omega) hsel
  obtain ⟨_, _, h294⟩ := endReachFirstArm294 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm294Eq I hsz 0 (by omega))
      (by simpa [endArm294Index] using hsel)
  exact RD.dispatchTo ⟨798⟩ 0 h294
    (fun j hj => endArms294WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachPack {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 30)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 30 (by omega) hsel
  obtain ⟨_, _, h294⟩ := endReachFirstArm294 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm294Eq I hsz 0 (by omega))
      (by simpa [endArm294Index] using
        endSelectorMiss_of_match 22 30 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm294Eq I hsz 1 (by omega))
      (by simpa [endArm294Index] using hsel)
  exact RD.dispatchTo ⟨806⟩ 1 h294
    (fun j hj => endArms294WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

end Benchmarks.Dss.End
