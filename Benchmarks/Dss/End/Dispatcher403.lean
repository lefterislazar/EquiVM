import Benchmarks.Dss.End.Dispatcher

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

theorem endArms403WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨403⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

def endArm403Index : Nat → Nat
  | 0 => 29
  | 1 => 5
  | 2 => 25
  | _ => 28

theorem endArm403Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm403Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm403Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endReachFirstArm403 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp272 : UInt256.gt (armSelNat endBytecode ⟨272⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp392 : UInt256.gt (armSelNat endBytecode ⟨392⟩) (endRuntimeSelWord I) = ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨403⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := endReachTopSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h271 := RD.selectorSplitTakenAuto h32 endSplit32WellFormed hp32 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨271⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h271
  have h272 := h271.jumpdest (by native_decide) (by simp)
  have h391 := RD.selectorSplitTakenAuto h272 endSplit272WellFormed hp272 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨391⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h391
  have h392 := h391.jumpdest (by native_decide) (by simp)
  have h403 := RD.selectorSplitNotTakenAuto h392 endSplit392WellFormed hp392 (by simp)
  exact ⟨_, _, by simpa using h403⟩

theorem endReachPot {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 5)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨664⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 5 (by omega) hsel
  obtain ⟨_, _, h403⟩ := endReachFirstArm403 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    exact endEqIfZero (endArm403Eq I hsz 0 (by omega))
      (by simpa [endArm403Index] using
        endSelectorMiss_of_match 29 5 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ 1))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm403Eq I hsz 1 (by omega))
      (by simpa [endArm403Index] using hsel)
  exact RD.dispatchTo ⟨664⟩ 1 h403
    (fun j hj => endArms403WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachFlow {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 29)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨635⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 29 (by omega) hsel
  obtain ⟨_, _, h403⟩ := endReachFirstArm403 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm403Eq I hsz 0 (by omega))
      (by simpa [endArm403Index] using hsel)
  exact RD.dispatchTo ⟨635⟩ 0 h403
    (fun j hj => endArms403WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachSkip {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 25)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨672⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 25 (by omega) hsel
  obtain ⟨_, _, h403⟩ := endReachFirstArm403 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm403Eq I hsz 0 (by omega))
        (by simpa [endArm403Index] using
          endSelectorMiss_of_match 29 25 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm403Eq I hsz 1 (by omega))
        (by simpa [endArm403Index] using
          endSelectorMiss_of_match 5 25 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm403Eq I hsz 2 (by omega))
      (by simpa [endArm403Index] using hsel)
  exact RD.dispatchTo ⟨672⟩ 2 h403
    (fun j hj => endArms403WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachThaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 28)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨707⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 28 (by omega) hsel
  obtain ⟨_, _, h403⟩ := endReachFirstArm403 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm403Eq I hsz 0 (by omega))
        (by simpa [endArm403Index] using
          endSelectorMiss_of_match 29 28 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm403Eq I hsz 1 (by omega))
        (by simpa [endArm403Index] using
          endSelectorMiss_of_match 5 28 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm403Eq I hsz 2 (by omega))
        (by simpa [endArm403Index] using
          endSelectorMiss_of_match 25 28 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm403Eq I hsz 3 (by omega))
      (by simpa [endArm403Index] using hsel)
  exact RD.dispatchTo ⟨707⟩ 3 h403
    (fun j hj => endArms403WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

end Benchmarks.Dss.End
