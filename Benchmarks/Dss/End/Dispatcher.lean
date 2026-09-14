import Benchmarks.Dss.End.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## Concrete nested dispatcher route for the low/low/low arm chain -/

theorem endSplit32WellFormed : selectorSplitWellFormed endBytecode ⟨32⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endSplit272WellFormed : selectorSplitWellFormed endBytecode ⟨272⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endSplit392WellFormed : selectorSplitWellFormed endBytecode ⟨392⟩ := by
  exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

theorem endArms452WellFormed :
    ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode ⟨452⟩ j) := by
  intro j hj
  interval_cases j <;>
    exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
      by native_decide, by native_decide⟩

def endArm452Index : Nat → Nat
  | 0 => 11
  | 1 => 21
  | 2 => 1
  | _ => 24

theorem endArm452Eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : Nat) (hj : j < 4) :
    UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ j))
        (endRuntimeSelWord I)
      = if (endSelBytes (endArm452Index j) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;>
    simpa [endArm452Index, endSelBytes, endRuntimeSelWord, solcSelectorWord] using
      (evmSelectorDecode (cd := I.calldata) hsz _ _ _ _ _ (by native_decide))

theorem endEqIfZero {x : UInt256} {b : Bool}
    (h : x = if b then (⟨1⟩ : UInt256) else ⟨0⟩) (hb : b = false) :
    x = ⟨0⟩ := by
  rw [h, hb]
  decide

theorem endEqIfNeZero {x : UInt256} {b : Bool}
    (h : x = if b then (⟨1⟩ : UInt256) else ⟨0⟩) (hb : b = true) :
    x ≠ ⟨0⟩ := by
  rw [h, hb]
  decide

theorem endReachFirstArm452 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp272 : UInt256.gt (armSelNat endBytecode ⟨272⟩) (endRuntimeSelWord I) ≠ ⟨0⟩)
    (hp392 : UInt256.gt (armSelNat endBytecode ⟨392⟩) (endRuntimeSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨452⟩
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
  have h451 := RD.selectorSplitTakenAuto h392 endSplit392WellFormed hp392 (by jump_dest) (by simp)
  change RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨451⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) _ _ at h451
  have h452 := h451.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, by simpa using h452⟩

theorem endReachDebt {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 11)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨501⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 11 (by omega) hsel
  obtain ⟨_, _, h452⟩ := endReachFirstArm452 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ 0))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm452Eq I hsz 0 (by omega))
      (by simpa [endArm452Index] using hsel)
  exact RD.dispatchTo ⟨501⟩ 0 h452
    (fun j hj => endArms452WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachVat {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 1)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨564⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 1 (by omega) hsel
  obtain ⟨_, _, h452⟩ := endReachFirstArm452 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm452Eq I hsz 0 (by omega))
        (by simpa [endArm452Index] using
          endSelectorMiss_of_match 11 1 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm452Eq I hsz 1 (by omega))
        (by simpa [endArm452Index] using
          endSelectorMiss_of_match 21 1 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ 2))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm452Eq I hsz 2 (by omega))
      (by simpa [endArm452Index] using hsel)
  exact RD.dispatchTo ⟨564⟩ 2 h452
    (fun j hj => endArms452WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endReachSnip {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 24)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨600⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 24 (by omega) hsel
  obtain ⟨_, _, h452⟩ := endReachFirstArm452 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm452Eq I hsz 0 (by omega))
        (by simpa [endArm452Index] using
          endSelectorMiss_of_match 11 24 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm452Eq I hsz 1 (by omega))
        (by simpa [endArm452Index] using
          endSelectorMiss_of_match 21 24 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm452Eq I hsz 2 (by omega))
        (by simpa [endArm452Index] using
          endSelectorMiss_of_match 1 24 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm452Eq I hsz 3 (by omega))
      (by simpa [endArm452Index] using hsel)
  exact RD.dispatchTo ⟨600⟩ 3 h452
    (fun j hj => endArms452WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

end Benchmarks.Dss.End
