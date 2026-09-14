import Benchmarks.Dss.End.Dispatcher114
import Benchmarks.Dss.End.Dispatcher174223
import Benchmarks.Dss.End.Dispatcher294343
import Benchmarks.Dss.End.Dispatcher403

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## Nested dispatcher no-match path -/

theorem endSelectorMiss_of_not_match {I : ExecutionEnv} {sel : ByteArray}
    (h : ¬ endSelectorMatches I sel) :
    (sel == I.calldata.extract 0 4) = false := by
  unfold endSelectorMatches at h
  cases hb : (sel == I.calldata.extract 0 4) <;> simp [hb] at h ⊢

theorem endDispatchMiss4 {cA gh bl σ σ₀ A I} {g : Sat256} {start : UInt256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {R : List UInt256}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) start
      (endRuntimeSelWord I :: R) mem aw rdata (cA, σ) k C)
    (hwf : ∀ j, j ≤ 3 → armWellFormed endBytecode (nthArmPc endBytecode start j))
    (heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode start j))
        (endRuntimeSelWord I) = ⟨0⟩)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      (nthArmPc endBytecode start 4) (endRuntimeSelWord I :: R) mem aw rdata (cA, σ)
      k' C' := by
  have h1 := RD.selectorArmNotTakenAuto h (hwf 0 (by omega)) (heq0 0 (by omega)) hov
  have h2 := RD.selectorArmNotTakenAuto h1
    (by simpa [nthArmPc] using hwf 1 (by omega))
    (by simpa [nthArmPc] using heq0 1 (by omega)) hov
  have h3 := RD.selectorArmNotTakenAuto h2
    (by simpa [nthArmPc] using hwf 2 (by omega))
    (by simpa [nthArmPc] using heq0 2 (by omega)) hov
  have h4 := RD.selectorArmNotTakenAuto h3
    (by simpa [nthArmPc] using hwf 3 (by omega))
    (by simpa [nthArmPc] using heq0 3 (by omega)) hov
  exact ⟨_, _, by simpa [nthArmPc] using h4⟩

theorem endNthArm65_4 : nthArmPc endBytecode (⟨65⟩ : UInt256) 4 = ⟨109⟩ := by
  native_decide

theorem endNthArm114_4 : nthArmPc endBytecode (⟨114⟩ : UInt256) 4 = ⟨158⟩ := by
  native_decide

theorem endNthArm174_4 : nthArmPc endBytecode (⟨174⟩ : UInt256) 4 = ⟨218⟩ := by
  native_decide

theorem endNthArm223_4 : nthArmPc endBytecode (⟨223⟩ : UInt256) 4 = ⟨267⟩ := by
  native_decide

theorem endNthArm294_4 : nthArmPc endBytecode (⟨294⟩ : UInt256) 4 = ⟨338⟩ := by
  native_decide

theorem endNthArm343_4 : nthArmPc endBytecode (⟨343⟩ : UInt256) 4 = ⟨387⟩ := by
  native_decide

theorem endNthArm403_4 : nthArmPc endBytecode (⟨403⟩ : UInt256) 4 = ⟨447⟩ := by
  native_decide

theorem endNthArm452_4 : nthArmPc endBytecode (⟨452⟩ : UInt256) 4 = ⟨496⟩ := by
  native_decide

theorem endNoMatchLeaf65 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨65⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨65⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm65Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm65Index] using hnm 2 (by omega)
        · simpa [endArm65Index] using hnm 13 (by omega)
        · simpa [endArm65Index] using hnm 12 (by omega)
        · simpa [endArm65Index] using hnm 31 (by omega))
  obtain ⟨k109, C109, h109⟩ := endDispatchMiss4 (start := (⟨65⟩ : UInt256)) h
    (fun j hj => endArms65WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm65_4] at h109
  have h496 := endRuntimeBlocks.endRuntime_block_109
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h109
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf114 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨114⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm114Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm114Index] using hnm 20 (by omega)
        · simpa [endArm114Index] using hnm 14 (by omega)
        · simpa [endArm114Index] using hnm 23 (by omega)
        · simpa [endArm114Index] using hnm 9 (by omega))
  obtain ⟨k158, C158, h158⟩ := endDispatchMiss4 (start := (⟨114⟩ : UInt256)) h
    (fun j hj => endArms114WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm114_4] at h158
  have h496 := endRuntimeBlocks.endRuntime_block_158
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h158
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf174 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨174⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨174⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm174Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm174Index] using hnm 0 (by omega)
        · simpa [endArm174Index] using hnm 3 (by omega)
        · simpa [endArm174Index] using hnm 27 (by omega)
        · simpa [endArm174Index] using hnm 17 (by omega))
  obtain ⟨k218, C218, h218⟩ := endDispatchMiss4 (start := (⟨174⟩ : UInt256)) h
    (fun j hj => endArms174WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm174_4] at h218
  have h496 := endRuntimeBlocks.endRuntime_block_218
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h218
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf223 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨223⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm223Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm223Index] using hnm 26 (by omega)
        · simpa [endArm223Index] using hnm 16 (by omega)
        · simpa [endArm223Index] using hnm 8 (by omega)
        · simpa [endArm223Index] using hnm 19 (by omega))
  obtain ⟨k267, C267, h267⟩ := endDispatchMiss4 (start := (⟨223⟩ : UInt256)) h
    (fun j hj => endArms223WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm223_4] at h267
  have h496 := endRuntimeBlocks.endRuntime_block_267
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h267
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf294 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨294⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨294⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm294Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm294Index] using hnm 22 (by omega)
        · simpa [endArm294Index] using hnm 30 (by omega)
        · simpa [endArm294Index] using hnm 6 (by omega)
        · simpa [endArm294Index] using hnm 7 (by omega))
  obtain ⟨k338, C338, h338⟩ := endDispatchMiss4 (start := (⟨294⟩ : UInt256)) h
    (fun j hj => endArms294WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm294_4] at h338
  have h496 := endRuntimeBlocks.endRuntime_block_338
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h338
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf343 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨343⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm343Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm343Index] using hnm 4 (by omega)
        · simpa [endArm343Index] using hnm 15 (by omega)
        · simpa [endArm343Index] using hnm 10 (by omega)
        · simpa [endArm343Index] using hnm 18 (by omega))
  obtain ⟨k387, C387, h387⟩ := endDispatchMiss4 (start := (⟨343⟩ : UInt256)) h
    (fun j hj => endArms343WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm343_4] at h387
  have h496 := endRuntimeBlocks.endRuntime_block_387
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h387
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf403 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨403⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨403⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm403Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm403Index] using hnm 29 (by omega)
        · simpa [endArm403Index] using hnm 5 (by omega)
        · simpa [endArm403Index] using hnm 25 (by omega)
        · simpa [endArm403Index] using hnm 28 (by omega))
  obtain ⟨k447, C447, h447⟩ := endDispatchMiss4 (start := (⟨403⟩ : UInt256)) h
    (fun j hj => endArms403WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm403_4] at h447
  have h496 := endRuntimeBlocks.endRuntime_block_447
    (R := [endRuntimeSelWord I]) (by simp) (by native_decide) h447
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endNoMatchLeaf452 {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨452⟩
      [endRuntimeSelWord I] mem aw rdata (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : ∀ j, j < 4 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨452⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    exact endEqIfZero (endArm452Eq I hsz j hj)
      (by
        interval_cases j
        · simpa [endArm452Index] using hnm 11 (by omega)
        · simpa [endArm452Index] using hnm 21 (by omega)
        · simpa [endArm452Index] using hnm 1 (by omega)
        · simpa [endArm452Index] using hnm 24 (by omega))
  obtain ⟨k496, C496, h496⟩ := endDispatchMiss4 (start := (⟨452⟩ : UInt256)) h
    (fun j hj => endArms452WellFormed j (by omega)) heq0 (by simp)
  rw [endNthArm452_4] at h496
  exact endRuntimeBlocks.endRuntime_block_496 (R := [endRuntimeSelWord I]) (by simp) h496

theorem endX_nomatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  by_cases hp32 : UInt256.gt (armSelNat endBytecode ⟨32⟩) (endRuntimeSelWord I) = ⟨0⟩
  · by_cases hp43 : UInt256.gt (armSelNat endBytecode ⟨43⟩) (endRuntimeSelWord I) = ⟨0⟩
    · by_cases hp54 : UInt256.gt (armSelNat endBytecode ⟨54⟩) (endRuntimeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h65⟩ := endReachFirstArm65 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp43 hp54
        exact endNoMatchLeaf65 hsz hnm h65
      · obtain ⟨_, _, h114⟩ := endReachFirstArm114 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp43 hp54
        exact endNoMatchLeaf114 hsz hnm h114
    · by_cases hp163 : UInt256.gt (armSelNat endBytecode ⟨163⟩) (endRuntimeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h174⟩ := endReachFirstArm174 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp43 hp163
        exact endNoMatchLeaf174 hsz hnm h174
      · obtain ⟨_, _, h223⟩ := endReachFirstArm223 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp43 hp163
        exact endNoMatchLeaf223 hsz hnm h223
  · by_cases hp272 : UInt256.gt (armSelNat endBytecode ⟨272⟩) (endRuntimeSelWord I) = ⟨0⟩
    · by_cases hp283 : UInt256.gt (armSelNat endBytecode ⟨283⟩) (endRuntimeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h294⟩ := endReachFirstArm294 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp272 hp283
        exact endNoMatchLeaf294 hsz hnm h294
      · obtain ⟨_, _, h343⟩ := endReachFirstArm343 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp272 hp283
        exact endNoMatchLeaf343 hsz hnm h343
    · by_cases hp392 : UInt256.gt (armSelNat endBytecode ⟨392⟩) (endRuntimeSelWord I) = ⟨0⟩
      · obtain ⟨_, _, h403⟩ := endReachFirstArm403 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp272 hp392
        exact endNoMatchLeaf403 hsz hnm h403
      · obtain ⟨_, _, h452⟩ := endReachFirstArm452 (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hwv hsz hsize hp32 hp272 hp392
        exact endNoMatchLeaf452 hsz hnm h452

theorem endNoMatchRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 32 → (endSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endX_nomatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm).reEquivNoDispatch
    hcode (endDispatch_none_nomatch hnm)

end Benchmarks.Dss.End
