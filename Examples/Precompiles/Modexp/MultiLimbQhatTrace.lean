import Examples.Precompiles.Modexp.MultiLimbDivisionTrace

/-!
# Generated q-hat refinement cycle

This module packages the decrement, overflow guard, and product recomputation generated traces as
one exact loop-state transition.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem lnotZero_eq_max_qhat :
    UInt256.lnot ⟨0⟩ = UInt256.ofNat (UInt256.size - 1) := by
  native_decide

structure QhatState where
  qHat : UInt256
  rHat : UInt256

def qhatAdvance (vTop : UInt256) (s : QhatState) : QhatState where
  qHat := s.qHat + UInt256.lnot ⟨0⟩
  rHat := s.rHat + vTop

private theorem lnotZero_toNat_qhat :
    (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 := by
  rw [lnotZero_eq_max_qhat]
  exact ulit_toNat' _ (by norm_num [UInt256.size])

/-- The generated all-ones addition is an ordinary decrement when q-hat is positive. -/
theorem qhatAdvance_qHat_toNat (vTop : UInt256) (s : QhatState)
    (hpos : 0 < s.qHat.toNat) :
    (qhatAdvance vTop s).qHat.toNat = s.qHat.toNat - 1 := by
  unfold qhatAdvance
  rw [uadd_toNat, lnotZero_toNat_qhat]
  have hq : s.qHat.toNat < UInt256.size := s.qHat.val.isLt
  have hge : UInt256.size ≤ s.qHat.toNat + (UInt256.size - 1) := by omega
  rw [Nat.mod_eq_sub_mod hge]
  have hsub : s.qHat.toNat + (UInt256.size - 1) - UInt256.size =
      s.qHat.toNat - 1 := by omega
  rw [hsub, Nat.mod_eq_of_lt (by omega)]

/-- A non-overflowing generated r-hat update is ordinary natural-number addition. -/
theorem qhatAdvance_rHat_toNat (vTop : UInt256) (s : QhatState)
    (hnoOverflow : (qhatAdvance vTop s).rHat.lt vTop = ⟨0⟩) :
    (qhatAdvance vTop s).rHat.toNat = s.rHat.toNat + vTop.toNat := by
  have hrec := Modexp.evmAddCarry_recompose vTop s.rHat
  have hzero : UInt256.lt (vTop + s.rHat) vTop = ⟨0⟩ := by
    simpa [qhatAdvance, u256_add_comm] using hnoOverflow
  rw [hzero] at hrec
  simpa [qhatAdvance, u256_add_comm, Nat.add_comm] using hrec

/-- A taken q-hat condition implies that q-hat is nonzero, so the generated decrement does not
underflow as an unbounded natural subtraction. -/
theorem qhatRefinement_qHat_positive
    (qHat rHat vSecond uSecond : UInt256)
    (hrefine : qhatNeedsRefinement qHat rHat vSecond uSecond ≠ ⟨0⟩) :
    0 < qHat.toNat := by
  have hineq := (qhatNeedsRefinement_iff qHat rHat vSecond uSecond).mp hrefine
  nlinarith

def qhatLoopStack (s : QhatState) (vTop vSecond uSecond : UInt256)
    (tail : List UInt256) : List UInt256 :=
  ⟨8519⟩ :: qhatNeedsRefinement s.qHat s.rHat vSecond uSecond ::
    vTop :: vSecond :: uSecond :: s.rHat :: s.qHat :: tail

/-- Recompute the full q-hat product after one decrement and return to the generated loop guard. -/
theorem qhatRecomputeBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {qHat rHat vTop vSecond uSecond : UInt256}
    (hdepth : tail.length + 5 ≤ 1018)
    (h : RDx runtimeBytecode ee g s0 ⟨8538⟩
      (uSecond :: vTop :: vSecond :: rHat :: qHat :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack { qHat := qHat, rHat := rHat } vTop vSecond uSecond tail)
      mem aw rdata acc (k + 37) (C + 120) := by
  have rd := GeneratedTraces.trace_8538_body hdepth h
  simpa [qhatLoopStack, qhatNeedsRefinement, evmMulHigh, lnotZero_eq_max_qhat,
    Nat.add_comm] using rd

/-- Decrement q-hat, add the normalized divisor top to r-hat, and expose the overflow guard. -/
theorem qhatDecrementBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {qHat rHat vTop vSecond uSecond : UInt256}
    (hdepth : tail.length + 5 ≤ 1022)
    (h : RDx runtimeBytecode ee g s0 ⟨8519⟩
      (vTop :: vSecond :: uSecond :: rHat :: qHat :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8537⟩
      (⟨8567⟩ :: (rHat + vTop).lt vTop ::
        uSecond :: vTop :: vSecond :: (rHat + vTop) ::
        (qHat + UInt256.lnot ⟨0⟩) :: tail)
      mem aw rdata acc (k + 16) (C + 45) := by
  have rd := GeneratedTraces.trace_8519_body hdepth h
  simpa only [Nat.add_comm] using rd

/-- One non-overflowing generated q-hat decrement cycle, including both conditional jumps. -/
theorem qhatRefinementCycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {vTop vSecond uSecond : UInt256}
    (state : QhatState)
    (hdepth : tail.length + 7 ≤ 1020)
    (hrefine : qhatNeedsRefinement state.qHat state.rHat vSecond uSecond ≠ ⟨0⟩)
    (hnoOverflow : (qhatAdvance vTop state).rHat.lt vTop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack state vTop vSecond uSecond tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨8511⟩
      (qhatLoopStack (qhatAdvance vTop state) vTop vSecond uSecond tail)
      mem aw rdata acc (k + 55) (C + 185) := by
  have rd8526 := h.jumpiT (by native_decide) hrefine
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd8544 := qhatDecrementBody (by omega) rd8526
  have rd8545 := rd8544.jumpiNT (by native_decide) hnoOverflow
    (by simp only [List.length_cons]; omega)
  have rdNext := qhatRecomputeBody (by omega) rd8545
  exact rdNext.withIndices (by omega) (by omega)

end Modexp.MultiLimbDivisionTrace
