import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulTrace

/-!
# Standalone schoolbook-multiplication outer loop

This module composes the exact zero/nonzero row selector across every source limb. The recursion
starts and ends at the deployed outer guard at PC 5046 and retains the branch-sensitive row gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def rowsIterate (aPtr bPtr resultPtr : UInt256) (bCount : Nat) :
    Nat → OuterState → OuterState
  | 0, state => state
  | n + 1, state =>
      rowsIterate aPtr bPtr resultPtr bCount n
        (rowAdvance aPtr bPtr resultPtr bCount state)

def rowsSteps (aPtr bPtr resultPtr : UInt256) (bCount : Nat) :
    Nat → OuterState → Nat
  | 0, _ => 0
  | n + 1, state =>
      1 + rowSteps aPtr bCount state +
        rowsSteps aPtr bPtr resultPtr bCount n
          (rowAdvance aPtr bPtr resultPtr bCount state)

def rowsGas (aPtr bPtr resultPtr : UInt256) (bCount : Nat) :
    Nat → OuterState → Nat
  | 0, _ => 0
  | n + 1, state =>
      10 + rowGas aPtr bPtr resultPtr bCount state +
        rowsGas aPtr bPtr resultPtr bCount n
          (rowAdvance aPtr bPtr resultPtr bCount state)

theorem rowsIterate_advance
    (aPtr bPtr resultPtr : UInt256) (bCount n : Nat) (state : OuterState) :
    rowsIterate aPtr bPtr resultPtr bCount n
        (rowAdvance aPtr bPtr resultPtr bCount state) =
      rowsIterate aPtr bPtr resultPtr bCount (n + 1) state := by
  rfl

/-- The same recurrence may be exposed at its final row rather than its first row. -/
theorem rowsIterate_succ_last
    (aPtr bPtr resultPtr : UInt256) (bCount n : Nat) (state : OuterState) :
    rowsIterate aPtr bPtr resultPtr bCount (n + 1) state =
      rowAdvance aPtr bPtr resultPtr bCount
        (rowsIterate aPtr bPtr resultPtr bCount n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [show rowsIterate aPtr bPtr resultPtr bCount (n + 1 + 1) state =
        rowsIterate aPtr bPtr resultPtr bCount (n + 1)
          (rowAdvance aPtr bPtr resultPtr bCount state) by rfl]
      rw [ih]
      rw [rowsIterate_advance]

/-- Execute any number of outer rows. Each row is selected from the source word loaded in its
current memory, and each preceding taken outer guard contributes one instruction and ten gas. -/
theorem rowsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C bCount n : Nat} {tail : List UInt256}
    {aPtr aLen bPtr ret resultPtr : UInt256}
    (state : OuterState)
    (hbPos : 0 < bCount) (hbWord : bCount < UInt256.size)
    (hdepth : tail.length + 10 ≤ 1016)
    (hcontinue : ∀ q, q < n →
      (rowsIterate aPtr bPtr resultPtr bCount q state).i.lt aLen ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack state aPtr bCount aLen bPtr ret resultPtr tail)
      state.memory state.activeWords rdata acc k C) :
    let final := rowsIterate aPtr bPtr resultPtr bCount n state
    RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack final aPtr bCount aLen bPtr ret resultPtr tail)
      final.memory final.activeWords rdata acc
      (k + rowsSteps aPtr bPtr resultPtr bCount n state)
      (C + rowsGas aPtr bPtr resultPtr bCount n state) := by
  induction n generalizing state k C with
  | zero => simpa [rowsIterate, rowsSteps, rowsGas]
  | succ n ih =>
      have rd5053 := h.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have rdRow := rowExact state hbPos hbWord hdepth
        (by simpa [outerGuardStack] using rd5053)
      have hcontinue' : ∀ q, q < n →
          (rowsIterate aPtr bPtr resultPtr bCount q
            (rowAdvance aPtr bPtr resultPtr bCount state)).i.lt aLen ≠ ⟨0⟩ := by
        intro q hq
        simpa [rowsIterate_advance] using hcontinue (q + 1) (by omega)
      have rdRest := ih (state := rowAdvance aPtr bPtr resultPtr bCount state)
        hcontinue' rdRow
      have normalized := rdRest.withIndices
        (k' := k + rowsSteps aPtr bPtr resultPtr bCount (n + 1) state) (by
          simp only [rowsSteps]
          omega)
        (C' := C + rowsGas aPtr bPtr resultPtr bCount (n + 1) state) (by
          simp only [rowsGas]
          omega)
      simpa only [rowsIterate] using normalized

theorem rowAdvance_i
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState) :
    (rowAdvance aPtr bPtr resultPtr bCount state).i = state.i + ⟨1⟩ := by
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · simp [rowAdvance, hzero]
  · simp [rowAdvance, hzero]

theorem rowAdvance_i_toNat
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState)
    (hbound : state.i.toNat + 1 < UInt256.size) :
    (rowAdvance aPtr bPtr resultPtr bCount state).i.toNat = state.i.toNat + 1 := by
  rw [rowAdvance_i, uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
    Nat.mod_eq_of_lt hbound]

theorem rowsIterate_i_toNat
    (aPtr bPtr resultPtr : UInt256) (bCount n : Nat) (state : OuterState)
    (hbound : state.i.toNat + n < UInt256.size) :
    (rowsIterate aPtr bPtr resultPtr bCount n state).i.toNat = state.i.toNat + n := by
  induction n generalizing state with
  | zero => simp [rowsIterate]
  | succ n ih =>
      rw [show rowsIterate aPtr bPtr resultPtr bCount (n + 1) state =
        rowsIterate aPtr bPtr resultPtr bCount n
          (rowAdvance aPtr bPtr resultPtr bCount state) by rfl]
      have hstep := rowAdvance_i_toNat aPtr bPtr resultPtr bCount state (by omega)
      rw [ih]
      · omega
      · rw [hstep]
        omega

/-- Execute all `aCount` source rows from the assembly loop's concrete `i = 0` initialization.
Every taken outer guard is derived from its natural index. -/
theorem rowsFromZeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr ret resultPtr : UInt256}
    (haWord : aCount < UInt256.size)
    (hbPos : 0 < bCount) (hbWord : bCount < UInt256.size)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack { i := ⟨0⟩, memory := mem, activeWords := aw }
        aPtr bCount (UInt256.ofNat aCount) bPtr ret resultPtr tail)
      mem aw rdata acc k C) :
    let initial : OuterState := { i := ⟨0⟩, memory := mem, activeWords := aw }
    let final := rowsIterate aPtr bPtr resultPtr bCount aCount initial
    RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack final aPtr bCount (UInt256.ofNat aCount) bPtr ret resultPtr tail)
      final.memory final.activeWords rdata acc
      (k + rowsSteps aPtr bPtr resultPtr bCount aCount initial)
      (C + rowsGas aPtr bPtr resultPtr bCount aCount initial) := by
  let initial : OuterState := { i := ⟨0⟩, memory := mem, activeWords := aw }
  have hi (q : Nat) (hq : q < aCount) :
      (rowsIterate aPtr bPtr resultPtr bCount q initial).i.toNat = q := by
    have hbound : initial.i.toNat + q < UInt256.size := by
      dsimp only [initial]
      rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
      omega
    simpa [initial] using
      rowsIterate_i_toNat aPtr bPtr resultPtr bCount q initial hbound
  have hcontinue : ∀ q, q < aCount →
      (rowsIterate aPtr bPtr resultPtr bCount q initial).i.lt
        (UInt256.ofNat aCount) ≠ ⟨0⟩ := by
    intro q hq
    have hlt : (rowsIterate aPtr bPtr resultPtr bCount q initial).i.toNat <
        (UInt256.ofNat aCount).toNat := by
      rw [hi q hq, UInt256.toNat_ofNat_of_lt haWord]
      exact hq
    rw [ult_one hlt]
    decide
  exact rowsExact initial hbPos hbWord hdepth hcontinue (by simpa [initial] using h)

/-- Select the false terminal outer guard, remove all loop locals, and dynamically return the
result pointer to the standalone multiplier's caller. -/
theorem rowsReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C bCount : Nat} {tail : List UInt256}
    {aPtr aLen bPtr returnPc resultPtr i : UInt256}
    (hguard : i.lt aLen = ⟨0⟩)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hdepth : tail.length + 10 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack { i := i, memory := mem, activeWords := aw }
        aPtr bCount aLen bPtr returnPc resultPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 returnPc (resultPtr :: tail)
      mem aw rdata acc (k + 7) (C + 28) := by
  have rd5047 := h.jumpiNT (by native_decide) hguard
    (by simp only [List.length_cons]; omega)
  have rd5052 := GeneratedTraces.trace_5047_body
    (by simp only [List.length_cons]; omega) rd5047
  have rdReturn := rd5052.jump (by native_decide) hreturn
    (by simp only [List.length_cons]; omega)
  simpa [outerGuardStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

/-- Execute exactly `aCount` rows from `i = 0`, prove the terminal guard false, and return the
same concrete result array produced by those rows. -/
theorem rowsFromZeroReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr returnPc resultPtr : UInt256}
    (haWord : aCount < UInt256.size)
    (hbPos : 0 < bCount) (hbWord : bCount < UInt256.size)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack { i := ⟨0⟩, memory := mem, activeWords := aw }
        aPtr bCount (UInt256.ofNat aCount) bPtr returnPc resultPtr tail)
      mem aw rdata acc k C) :
    let initial : OuterState := { i := ⟨0⟩, memory := mem, activeWords := aw }
    let final := rowsIterate aPtr bPtr resultPtr bCount aCount initial
    RDx runtimeBytecode ee g s0 returnPc (resultPtr :: tail)
      final.memory final.activeWords rdata acc
      (k + rowsSteps aPtr bPtr resultPtr bCount aCount initial + 7)
      (C + rowsGas aPtr bPtr resultPtr bCount aCount initial + 28) := by
  let initial : OuterState := { i := ⟨0⟩, memory := mem, activeWords := aw }
  let final := rowsIterate aPtr bPtr resultPtr bCount aCount initial
  have rdRows := rowsFromZeroExact haWord hbPos hbWord hdepth h
  have hindex : final.i.toNat = aCount := by
    have hbound : initial.i.toNat + aCount < UInt256.size := by
      dsimp only [initial]
      rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
      omega
    simpa [final, initial] using
      rowsIterate_i_toNat aPtr bPtr resultPtr bCount aCount initial hbound
  have hguard : final.i.lt (UInt256.ofNat aCount) = ⟨0⟩ := by
    apply ult_zero
    rw [hindex, UInt256.toNat_ofNat_of_lt haWord]
  have rdReturn := rowsReturnExact (tail := tail) hguard hreturn (by omega)
    (by simpa [final, initial] using rdRows)
  have normalized := rdReturn.withIndices
    (k' := k + rowsSteps aPtr bPtr resultPtr bCount aCount initial + 7) (by
      dsimp only [initial])
    (C' := C + rowsGas aPtr bPtr resultPtr bCount aCount initial + 28) (by
      dsimp only [initial])
  simpa [final, initial] using normalized

end Modexp.MultiLimbSchoolbookMulTrace
