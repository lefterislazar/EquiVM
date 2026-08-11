import Examples.Precompiles.Modexp.GeneratedTraces

/-!
# Generated multi-limb loop steps

This file turns the generic SymCheck-generated traces into bytecode-specific loop rules.  The
generated declarations remain untrusted inputs until Lean replays them; the theorems below are
ordinary kernel-checked compositions over the concrete ModExp runtime.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace MultiLimbGenerated

def fullWordLoopStack (i full dataPtr dataLen ret limbsPtr : UInt256)
    (tail : List UInt256) : List UInt256 :=
  i :: full :: dataPtr :: dataLen :: ret :: limbsPtr :: tail

def fullWordReadOffset (i dataLen : UInt256) : UInt256 :=
  dataLen - ((i + ⟨1⟩).shiftLeft ⟨5⟩)

def fullWordReadAddress (i dataPtr dataLen : UInt256) : UInt256 :=
  dataPtr + fullWordReadOffset i dataLen + ⟨32⟩

def fullWordWriteAddress (i limbsPtr : UInt256) : UInt256 :=
  limbsPtr + i.shiftLeft ⟨5⟩ + ⟨32⟩

def fullWordReadValue (mem : ByteArray) (aw i dataPtr dataLen : UInt256) : UInt256 :=
  let addr := fullWordReadAddress i dataPtr dataLen
  if addr.toNat ≥ mem.size ∨ addr ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding addr.toNat 32))

def fullWordIterationMemory (mem : ByteArray) (aw i dataPtr dataLen limbsPtr : UInt256) :
    ByteArray :=
  (fullWordReadValue mem aw i dataPtr dataLen).toByteArray.write
    0 mem (fullWordWriteAddress i limbsPtr).toNat 32

def fullWordReadActiveWords (aw i dataPtr dataLen : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (fullWordReadAddress i dataPtr dataLen).toNat 32)

def fullWordIterationActiveWords (aw i dataPtr dataLen limbsPtr : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (fullWordReadActiveWords aw i dataPtr dataLen).toNat
      (fullWordWriteAddress i limbsPtr).toNat 32)

def fullWordIterationGas (aw i dataPtr dataLen limbsPtr : UInt256) : Nat :=
  286 +
    (Cₘ (fullWordReadActiveWords aw i dataPtr dataLen) - Cₘ aw) +
    (Cₘ (fullWordIterationActiveWords aw i dataPtr dataLen limbsPtr) -
      Cₘ (fullWordReadActiveWords aw i dataPtr dataLen))

/-- Enter the full-word copy body when the loop guard succeeds. -/
theorem fullWordLoopEnter
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hcontinue : i.lt full ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨2857⟩
      (fullWordLoopStack i full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack i full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc (k + 6) (C + 23) := by
  simpa [fullWordLoopStack, Nat.add_comm] using
    (GeneratedTraces.trace_2857_taken
      (tail := dataPtr :: dataLen :: ret :: limbsPtr :: tail)
      (by simp only [List.length_cons]; omega) h (by native_decide) hcontinue (by native_decide))

/-- Skip the full-word copy body when there are no full limbs left. -/
theorem fullWordLoopEmpty
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hfinished : i.lt full = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨2857⟩
      (fullWordLoopStack i full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack i full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc (k + 6) (C + 23) := by
  have rd := GeneratedTraces.trace_2857_notTaken
      (tail := dataPtr :: dataLen :: ret :: limbsPtr :: tail)
      (by simp only [List.length_cons]; omega) h (by native_decide) hfinished
  simpa [fullWordLoopStack, Nat.add_comm] using
    (rd.withPC (pc' := ⟨2865⟩) (by native_decide))

/-- One complete full-word `bytesToLimbs` iteration, from the body entry after a successful loop
guard to the next body entry.  This composes six generated maximal traces and their checked branch
edges.  The side conditions are the three Solidity checked-arithmetic guards and the loop's
continue condition. -/
theorem fullWordIterationContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hadd : i.gt (i + ⟨1⟩) = ⟨0⟩)
    (hshift :
      ((i + ⟨1⟩).isZero.lor
        ((⟨32⟩ : UInt256).eq (((i + ⟨1⟩).shiftLeft ⟨5⟩).div (i + ⟨1⟩)))).isZero = ⟨0⟩)
    (hsub : (fullWordReadOffset i dataLen).gt dataLen = ⟨0⟩)
    (hcontinue : (i + ⟨1⟩).lt full ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack i full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack (i + ⟨1⟩) full dataPtr dataLen ret limbsPtr tail)
      (fullWordIterationMemory mem aw i dataPtr dataLen limbsPtr)
      (fullWordIterationActiveWords aw i dataPtr dataLen limbsPtr)
      rdata acc (k + 79) (C + fullWordIterationGas aw i dataPtr dataLen limbsPtr) := by
  have rd1336 := GeneratedTraces.trace_2906_notTaken
    (tail := full :: dataPtr :: dataLen :: ret :: limbsPtr :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hadd
  have rd2926 := GeneratedTraces.trace_1336_jump
    (by simp only [List.length_cons]; omega) rd1336 (by native_decide) (by native_decide)
  have rd1924 := GeneratedTraces.trace_2926_notTaken
    (by simp only [List.length_cons]; omega) rd2926 (by native_decide) hshift
  have rd2931 := GeneratedTraces.trace_1924_jump
    (by simp only [List.length_cons]; omega) rd1924 (by native_decide) (by native_decide)
  have rd1115 := GeneratedTraces.trace_2931_notTaken
    (by simp only [List.length_cons]; omega) rd2931 (by native_decide) hsub
  have rd2937 := GeneratedTraces.trace_1115_jump
    (by simp only [List.length_cons]; omega) rd1115 (by native_decide) (by native_decide)
  have rd2906 := GeneratedTraces.trace_2937_taken
    (by omega) rd2937 (by native_decide) hcontinue
      (by native_decide)
  simpa [fullWordLoopStack, fullWordIterationMemory, fullWordIterationActiveWords,
    fullWordReadValue, fullWordReadActiveWords, fullWordReadAddress, fullWordReadOffset,
    fullWordWriteAddress, fullWordIterationGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using rd2906

/-- The final full-word `bytesToLimbs` iteration.  It performs the same checked arithmetic and
memory transfer as `fullWordIterationContinue`, then exits to the partial-word suffix. -/
theorem fullWordIterationExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hadd : i.gt (i + ⟨1⟩) = ⟨0⟩)
    (hshift :
      ((i + ⟨1⟩).isZero.lor
        ((⟨32⟩ : UInt256).eq (((i + ⟨1⟩).shiftLeft ⟨5⟩).div (i + ⟨1⟩)))).isZero = ⟨0⟩)
    (hsub : (fullWordReadOffset i dataLen).gt dataLen = ⟨0⟩)
    (hfinished : (i + ⟨1⟩).lt full = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack i full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack (i + ⟨1⟩) full dataPtr dataLen ret limbsPtr tail)
      (fullWordIterationMemory mem aw i dataPtr dataLen limbsPtr)
      (fullWordIterationActiveWords aw i dataPtr dataLen limbsPtr)
      rdata acc (k + 79) (C + fullWordIterationGas aw i dataPtr dataLen limbsPtr) := by
  have rd1336 := GeneratedTraces.trace_2906_notTaken
    (tail := full :: dataPtr :: dataLen :: ret :: limbsPtr :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hadd
  have rd2926 := GeneratedTraces.trace_1336_jump
    (by simp only [List.length_cons]; omega) rd1336 (by native_decide) (by native_decide)
  have rd1924 := GeneratedTraces.trace_2926_notTaken
    (by simp only [List.length_cons]; omega) rd2926 (by native_decide) hshift
  have rd2931 := GeneratedTraces.trace_1924_jump
    (by simp only [List.length_cons]; omega) rd1924 (by native_decide) (by native_decide)
  have rd1115 := GeneratedTraces.trace_2931_notTaken
    (by simp only [List.length_cons]; omega) rd2931 (by native_decide) hsub
  have rd2937 := GeneratedTraces.trace_1115_jump
    (by simp only [List.length_cons]; omega) rd1115 (by native_decide) (by native_decide)
  have rd2865 := GeneratedTraces.trace_2937_notTaken
    (by omega) rd2937 (by native_decide) hfinished
  simpa [fullWordLoopStack, fullWordIterationMemory, fullWordIterationActiveWords,
    fullWordReadValue, fullWordReadActiveWords, fullWordReadAddress, fullWordReadOffset,
    fullWordWriteAddress, fullWordIterationGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using rd2865

structure FullWordState where
  index : UInt256
  memory : ByteArray
  activeWords : UInt256

def fullWordAdvance (dataPtr dataLen limbsPtr : UInt256) (s : FullWordState) :
    FullWordState where
  index := s.index + ⟨1⟩
  memory := fullWordIterationMemory s.memory s.activeWords s.index dataPtr dataLen limbsPtr
  activeWords := fullWordIterationActiveWords s.activeWords s.index dataPtr dataLen limbsPtr

def fullWordIterate (dataPtr dataLen limbsPtr : UInt256) : Nat → FullWordState → FullWordState
  | 0, s => s
  | n + 1, s => fullWordIterate dataPtr dataLen limbsPtr n
      (fullWordAdvance dataPtr dataLen limbsPtr s)

def fullWordIterationsGas (dataPtr dataLen limbsPtr : UInt256) :
    Nat → FullWordState → Nat
  | 0, _ => 0
  | n + 1, s =>
      fullWordIterationGas s.activeWords s.index dataPtr dataLen limbsPtr +
        fullWordIterationsGas dataPtr dataLen limbsPtr n
          (fullWordAdvance dataPtr dataLen limbsPtr s)

def fullWordStepSafe (dataLen : UInt256) (i : UInt256) : Prop :=
  i.gt (i + ⟨1⟩) = ⟨0⟩ ∧
  ((i + ⟨1⟩).isZero.lor
    ((⟨32⟩ : UInt256).eq (((i + ⟨1⟩).shiftLeft ⟨5⟩).div (i + ⟨1⟩)))).isZero = ⟨0⟩ ∧
  (fullWordReadOffset i dataLen).gt dataLen = ⟨0⟩

@[simp] theorem fullWordIterate_advance (dataPtr dataLen limbsPtr : UInt256)
    (n : Nat) (s : FullWordState) :
    fullWordIterate dataPtr dataLen limbsPtr n
        (fullWordAdvance dataPtr dataLen limbsPtr s) =
      fullWordIterate dataPtr dataLen limbsPtr (n + 1) s := by
  rfl

/-- Execute any positive number of full-word copies.  The hypotheses expose every checked
arithmetic and control-flow obligation at its concrete iteration; no functional result or gas is
existentially hidden. -/
theorem fullWordIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {full dataPtr dataLen ret limbsPtr : UInt256}
    (state : FullWordState)
    (hdepth : tail.length + 6 ≤ 1016)
    (hn : 0 < n)
    (hsafe : ∀ j, j < n →
      fullWordStepSafe dataLen (fullWordIterate dataPtr dataLen limbsPtr j state).index)
    (hcontinue : ∀ j, j + 1 < n →
      ((fullWordIterate dataPtr dataLen limbsPtr j state).index + ⟨1⟩).lt full ≠ ⟨0⟩)
    (hfinished :
      (fullWordIterate dataPtr dataLen limbsPtr n state).index.lt full = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack state.index full dataPtr dataLen ret limbsPtr tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack
        (fullWordIterate dataPtr dataLen limbsPtr n state).index
        full dataPtr dataLen ret limbsPtr tail)
      (fullWordIterate dataPtr dataLen limbsPtr n state).memory
      (fullWordIterate dataPtr dataLen limbsPtr n state).activeWords
      rdata acc (k + 79 * n)
      (C + fullWordIterationsGas dataPtr dataLen limbsPtr n state) := by
  induction n generalizing state k C with
  | zero => omega
  | succ n ih =>
    rcases hsafe 0 (by omega) with ⟨hadd, hshift, hsub⟩
    cases n with
    | zero =>
      have hexit := fullWordIterationExit hdepth hadd hshift hsub
        (by simpa [fullWordIterate, fullWordAdvance] using hfinished) h
      simpa [fullWordIterate, fullWordIterationsGas, fullWordAdvance, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hexit
    | succ n =>
      have hnext := fullWordIterationContinue hdepth hadd hshift hsub
        (hcontinue 0 (by omega)) h
      have hsafe' : ∀ j, j < n + 1 →
          fullWordStepSafe dataLen
            (fullWordIterate dataPtr dataLen limbsPtr j
              (fullWordAdvance dataPtr dataLen limbsPtr state)).index := by
        intro j hj
        simpa [fullWordIterate_advance] using hsafe (j + 1) (by omega)
      have hcontinue' : ∀ j, j + 1 < n + 1 →
          ((fullWordIterate dataPtr dataLen limbsPtr j
            (fullWordAdvance dataPtr dataLen limbsPtr state)).index + ⟨1⟩).lt full ≠ ⟨0⟩ := by
        intro j hj
        simpa [fullWordIterate_advance] using hcontinue (j + 1) (by omega)
      have hfinished' :
          (fullWordIterate dataPtr dataLen limbsPtr (n + 1)
            (fullWordAdvance dataPtr dataLen limbsPtr state)).index.lt full = ⟨0⟩ := by
        simpa [fullWordIterate_advance, Nat.add_assoc] using hfinished
      have hrest := ih (state := fullWordAdvance dataPtr dataLen limbsPtr state)
        (by omega) hsafe' hcontinue' hfinished' hnext
      have hrest' := hrest.withIndices (k' := k + 79 * (n + 2)) (by omega) rfl
      simpa [fullWordIterate, fullWordIterationsGas, fullWordAdvance, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest'

theorem fullWordStepSafe_ofNat {i dataLen : Nat}
    (hi : i < 32) (hlen : dataLen ≤ 1024) (hword : 32 * (i + 1) ≤ dataLen) :
    fullWordStepSafe (UInt256.ofNat dataLen) (UInt256.ofNat i) := by
  have hiSucc : i + 1 < UInt256.size := by
    apply lt_of_le_of_lt (show i + 1 ≤ 32 by omega)
    decide
  have hdata : dataLen < UInt256.size := by
    apply lt_of_le_of_lt hlen
    decide
  have hshiftBound : 32 * (i + 1) < UInt256.size := by
    apply lt_of_le_of_lt hword hdata
  have hadd : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) := by
    rw [u256_add_comm]
    exact u256_one_add_ofNat i
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (i + 1)) ⟨5⟩ =
        UInt256.ofNat (32 * (i + 1)) :=
    shiftLeft5_ofNat_eq hshiftBound
  have hdiv :
      UInt256.div (UInt256.ofNat (32 * (i + 1))) (UInt256.ofNat (i + 1)) =
        UInt256.ofNat 32 := by
    apply u256_inj
    rw [udiv_toNat, UInt256.toNat_ofNat_of_lt hshiftBound,
      UInt256.toNat_ofNat_of_lt hiSucc,
      UInt256.toNat_ofNat_of_lt (show 32 < UInt256.size by decide)]
    simpa only [Nat.mul_comm] using
      Nat.mul_div_right 32 (show 0 < i + 1 from Nat.zero_lt_succ i)
  have hsuccNe : UInt256.ofNat (i + 1) ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hiSucc] at hzNat
    simp only [UInt256.zero_toNat] at hzNat
    omega
  have hsuccIsZero : UInt256.isZero (UInt256.ofNat (i + 1)) = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hsuccNe, Bool.toUInt256]
    apply u256_inj
    rfl
  have heq : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat 32) = ⟨1⟩ := by
    native_decide
  have hcheckedShift :
      (UInt256.lor (UInt256.isZero (UInt256.ofNat (i + 1)))
        (UInt256.eq (UInt256.ofNat 32)
          (UInt256.div
            (UInt256.shiftLeft (UInt256.ofNat (i + 1)) ⟨5⟩)
            (UInt256.ofNat (i + 1))))).isZero = ⟨0⟩ := by
    rw [hshift, hdiv, hsuccIsZero, heq]
    native_decide
  have hsub :
      fullWordReadOffset (UInt256.ofNat i) (UInt256.ofNat dataLen) =
        UInt256.ofNat (dataLen - 32 * (i + 1)) := by
    unfold fullWordReadOffset
    rw [hadd, hshift]
    apply u256_inj
    change (UInt256.sub (UInt256.ofNat dataLen)
      (UInt256.ofNat (32 * (i + 1)))).toNat =
        (UInt256.ofNat (dataLen - 32 * (i + 1))).toNat
    rw [usub_ofNat_lit_toNat hword hdata,
      UInt256.toNat_ofNat_of_lt
        (lt_of_le_of_lt (Nat.sub_le dataLen (32 * (i + 1))) hdata)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hadd]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (show i < UInt256.size by omega),
      UInt256.toNat_ofNat_of_lt hiSucc]
    omega
  · simpa [hadd] using hcheckedShift
  · rw [hsub]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt
        (lt_of_le_of_lt (Nat.sub_le dataLen (32 * (i + 1))) hdata),
      UInt256.toNat_ofNat_of_lt hdata]
    omega

theorem fullWordIterate_index (dataPtr dataLen limbsPtr : UInt256)
    (n : Nat) (state : FullWordState) :
    (fullWordIterate dataPtr dataLen limbsPtr n state).index =
      state.index + UInt256.ofNat n := by
  induction n generalizing state with
  | zero =>
    simp only [fullWordIterate]
    rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by
      apply u256_inj
      rfl]
    rw [u256_add_comm, u256_zero_add]
  | succ n ih =>
    rw [show n + 1 = Nat.succ n by omega]
    simp only [fullWordIterate]
    rw [ih]
    change (state.index + ⟨1⟩) + UInt256.ofNat n =
      state.index + UInt256.ofNat (Nat.succ n)
    rw [u256_add_assoc, u256_one_add_ofNat]

def fullWordInitialState (mem : ByteArray) (aw : UInt256) : FullWordState where
  index := ⟨0⟩
  memory := mem
  activeWords := aw

/-- Execute the complete full-word phase of `bytesToLimbs` for an Osaka-bounded byte string.  The
only remaining input-side condition is positivity of `dataLen / 32`; the zero-full-word case uses
`fullWordLoopEmpty` directly. -/
theorem fullWordLoopOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {dataPtr ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hfull : 0 < dataLen / 32)
    (h : RDx runtimeBytecode ee g s0 ⟨2857⟩
      (fullWordLoopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32)) dataPtr
        (UInt256.ofNat dataLen) ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack (UInt256.ofNat (dataLen / 32))
        (UInt256.ofNat (dataLen / 32)) dataPtr (UInt256.ofNat dataLen) ret limbsPtr tail)
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
        (fullWordInitialState mem aw)).memory
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
        (fullWordInitialState mem aw)).activeWords
      rdata acc (k + 6 + 79 * (dataLen / 32))
      (C + 23 + fullWordIterationsGas dataPtr (UInt256.ofNat dataLen) limbsPtr
        (dataLen / 32) (fullWordInitialState mem aw)) := by
  have hfullLe : dataLen / 32 ≤ 32 := by omega
  have hfullBound : dataLen / 32 < UInt256.size := by
    apply lt_of_le_of_lt hfullLe
    decide
  have henter := fullWordLoopEnter (tail := tail) (i := (⟨0⟩ : UInt256))
    (full := UInt256.ofNat (dataLen / 32)) (dataPtr := dataPtr)
    (dataLen := UInt256.ofNat dataLen) (ret := ret) (limbsPtr := limbsPtr)
    (by omega) (by
      have hlt := ult_one (a := (⟨0⟩ : UInt256))
        (b := UInt256.ofNat (dataLen / 32)) (by
          rw [UInt256.zero_toNat, UInt256.toNat_ofNat_of_lt hfullBound]
          exact hfull)
      rw [hlt]
      decide) h
  have hindex (j : Nat) :
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
        (fullWordInitialState mem aw)).index = UInt256.ofNat j := by
    rw [fullWordIterate_index]
    change (⟨0⟩ : UInt256) + UInt256.ofNat j = UInt256.ofNat j
    exact u256_zero_add _
  have hsafe : ∀ j, j < dataLen / 32 →
      fullWordStepSafe (UInt256.ofNat dataLen)
        (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
          (fullWordInitialState mem aw)).index := by
    intro j hj
    rw [hindex]
    apply fullWordStepSafe_ofNat
    · omega
    · exact hlen
    · have hmul := Nat.mul_div_le dataLen 32
      omega
  have hcontinue : ∀ j, j + 1 < dataLen / 32 →
      ((fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
        (fullWordInitialState mem aw)).index + ⟨1⟩).lt
          (UInt256.ofNat (dataLen / 32)) ≠ ⟨0⟩ := by
    intro j hj
    rw [hindex, u256_add_comm, u256_one_add_ofNat]
    have hjBound : j + 1 < UInt256.size := by omega
    have hlt := ult_one (a := UInt256.ofNat (j + 1))
      (b := UInt256.ofNat (dataLen / 32)) (by
        rw [UInt256.toNat_ofNat_of_lt hjBound,
          UInt256.toNat_ofNat_of_lt hfullBound]
        exact hj)
    rw [hlt]
    decide
  have hfinished :
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
        (fullWordInitialState mem aw)).index.lt
          (UInt256.ofNat (dataLen / 32)) = ⟨0⟩ := by
    rw [hindex]
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hfullBound]
  have hrun := fullWordIterations
    (state := fullWordInitialState mem aw) (n := dataLen / 32) hdepth hfull
    hsafe hcontinue hfinished henter
  have hrun' := hrun.withIndices
    (k' := k + 6 + 79 * (dataLen / 32)) (by omega)
    (C' := C + 23 + fullWordIterationsGas dataPtr (UInt256.ofNat dataLen) limbsPtr
      (dataLen / 32) (fullWordInitialState mem aw)) (by omega)
  simpa [hindex] using hrun'

/-- Execute the complete positive full-word phase when the caller has already taken the initial
loop guard and reached the body entry. -/
theorem fullWordBodyOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {dataPtr ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hfull : 0 < dataLen / 32)
    (h : RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32)) dataPtr
        (UInt256.ofNat dataLen) ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack (UInt256.ofNat (dataLen / 32))
        (UInt256.ofNat (dataLen / 32)) dataPtr (UInt256.ofNat dataLen) ret limbsPtr tail)
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
        (fullWordInitialState mem aw)).memory
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
        (fullWordInitialState mem aw)).activeWords
      rdata acc (k + 79 * (dataLen / 32))
      (C + fullWordIterationsGas dataPtr (UInt256.ofNat dataLen) limbsPtr
        (dataLen / 32) (fullWordInitialState mem aw)) := by
  have hfullLe : dataLen / 32 ≤ 32 := by omega
  have hfullBound : dataLen / 32 < UInt256.size := by
    apply lt_of_le_of_lt hfullLe
    decide
  have hindex (j : Nat) :
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
        (fullWordInitialState mem aw)).index = UInt256.ofNat j := by
    rw [fullWordIterate_index]
    change (⟨0⟩ : UInt256) + UInt256.ofNat j = UInt256.ofNat j
    exact u256_zero_add _
  have hsafe : ∀ j, j < dataLen / 32 →
      fullWordStepSafe (UInt256.ofNat dataLen)
        (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
          (fullWordInitialState mem aw)).index := by
    intro j hj
    rw [hindex]
    apply fullWordStepSafe_ofNat
    · omega
    · exact hlen
    · have hmul := Nat.mul_div_le dataLen 32
      omega
  have hcontinue : ∀ j, j + 1 < dataLen / 32 →
      ((fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr j
        (fullWordInitialState mem aw)).index + ⟨1⟩).lt
          (UInt256.ofNat (dataLen / 32)) ≠ ⟨0⟩ := by
    intro j hj
    rw [hindex, u256_add_comm, u256_one_add_ofNat]
    have hjBound : j + 1 < UInt256.size := by omega
    have hlt := ult_one (a := UInt256.ofNat (j + 1))
      (b := UInt256.ofNat (dataLen / 32)) (by
        rw [UInt256.toNat_ofNat_of_lt hjBound,
          UInt256.toNat_ofNat_of_lt hfullBound]
        exact hj)
    rw [hlt]
    decide
  have hfinished :
      (fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
        (fullWordInitialState mem aw)).index.lt
          (UInt256.ofNat (dataLen / 32)) = ⟨0⟩ := by
    rw [hindex]
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hfullBound]
  have hrun := fullWordIterations
    (state := fullWordInitialState mem aw) (n := dataLen / 32) hdepth hfull
    hsafe hcontinue hfinished h
  simpa [hindex] using hrun

/-- Finish `bytesToLimbs` without a partial limb. -/
theorem bytesToLimbsNoRemainder
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1021)
    (hrem : UInt256.land dataLen ⟨31⟩ = ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack index full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (limbsPtr :: tail)
      mem aw rdata acc (k + 13) (C + 46) := by
  have rd2877 := GeneratedTraces.trace_2865_notTaken
    (tail := ret :: limbsPtr :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hrem
  have rdret := GeneratedTraces.trace_2877_jump
    (tail := limbsPtr :: tail)
    (by simp only [List.length_cons]; omega) rd2877 (by native_decide) hret
  simpa [fullWordLoopStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdret

def partialWordReadAddress (dataPtr : UInt256) : UInt256 := dataPtr + ⟨32⟩

def partialWordWriteAddress (dataLen limbsPtr : UInt256) : UInt256 :=
  limbsPtr + UInt256.land dataLen (UInt256.lnot ⟨31⟩) + ⟨32⟩

def partialWordReadValue (mem : ByteArray) (aw dataPtr : UInt256) : UInt256 :=
  let addr := partialWordReadAddress dataPtr
  if addr.toNat ≥ mem.size ∨ addr ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding addr.toNat 32))

def partialWordValue (mem : ByteArray) (aw dataPtr rem : UInt256) : UInt256 :=
  UInt256.shiftRight (partialWordReadValue mem aw dataPtr)
    (UInt256.shiftLeft (⟨32⟩ - rem) ⟨3⟩)

def partialWordReadActiveWords (aw dataPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (partialWordReadAddress dataPtr).toNat 32)

def partialWordActiveWords (aw dataPtr dataLen limbsPtr : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (partialWordReadActiveWords aw dataPtr).toNat
      (partialWordWriteAddress dataLen limbsPtr).toNat 32)

def partialWordMemory (mem : ByteArray) (aw dataPtr dataLen rem limbsPtr : UInt256) :
    ByteArray :=
  (partialWordValue mem aw dataPtr rem).toByteArray.write
    0 mem (partialWordWriteAddress dataLen limbsPtr).toNat 32

def partialWordGas (aw dataPtr dataLen limbsPtr : UInt256) : Nat :=
  101 + (Cₘ (partialWordReadActiveWords aw dataPtr) - Cₘ aw) +
    (Cₘ (partialWordActiveWords aw dataPtr dataLen limbsPtr) -
      Cₘ (partialWordReadActiveWords aw dataPtr))

/- Raw generated composition for the partial most-significant limb.  Its inferred result is kept
opaque before the byte-level normalization theorem, avoiding expansion of the 256-bit mask during
trace replay. -/
evm_theorem bytesToLimbsPartialRaw
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hrem : UInt256.land dataLen ⟨31⟩ ≠ ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack index full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) := by
  have rd2881 := GeneratedTraces.trace_2865_taken
    (tail := ret :: limbsPtr :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hrem (by native_decide)
  have rdret := GeneratedTraces.trace_2881_jump
    (tail := tail) (by omega) rd2881 (by native_decide) hret
  exact rdret

/-- Finish `bytesToLimbs` by loading and right-aligning its partial most-significant limb. -/
theorem bytesToLimbsPartial
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index full dataPtr dataLen ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hrem : UInt256.land dataLen ⟨31⟩ ≠ ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack index full dataPtr dataLen ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (limbsPtr :: tail)
      (partialWordMemory mem aw dataPtr dataLen (UInt256.land dataLen ⟨31⟩) limbsPtr)
      (partialWordActiveWords aw dataPtr dataLen limbsPtr)
      rdata acc (k + 31) (C + partialWordGas aw dataPtr dataLen limbsPtr) := by
  have rdRaw := bytesToLimbsPartialRaw hdepth hrem hret h
  have normalized := rdRaw.withIndices (k' := k + 31) (by omega)
    (C' := C + partialWordGas aw dataPtr dataLen limbsPtr) (by
      unfold partialWordGas partialWordActiveWords partialWordReadActiveWords
        partialWordReadAddress partialWordWriteAddress
      omega)
  simpa only [partialWordMemory, partialWordValue, partialWordReadValue,
    partialWordReadAddress, partialWordWriteAddress, partialWordActiveWords,
    partialWordReadActiveWords] using normalized

theorem wordRemainder_eq {dataLen : Nat} (hlen : dataLen ≤ 1024) :
    UInt256.land (UInt256.ofNat dataLen) ⟨31⟩ = UInt256.ofNat (dataLen % 32) := by
  apply u256_inj
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hlen (by decide)),
    show (⟨31⟩ : UInt256).toNat = 31 from by decide,
    UInt256.toNat_ofNat_of_lt
      (lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 32)) (by decide))]
  simpa using nat_land_mask_eq_mod dataLen 5

theorem wordClearedRemainder_eq {dataLen : Nat} (hlen : dataLen ≤ 1024) :
    UInt256.land (UInt256.ofNat dataLen) (UInt256.lnot ⟨31⟩) =
      UInt256.ofNat (32 * (dataLen / 32)) := by
  apply u256_inj
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hlen (by decide)),
    lnot31_toNat,
    UInt256.toNat_ofNat_of_lt (show 32 * (dataLen / 32) < UInt256.size by
      exact lt_of_le_of_lt (Nat.mul_div_le dataLen 32)
        (lt_of_le_of_lt hlen (by decide)))]
  exact nat_land_mask dataLen (by
    apply lt_of_le_of_lt hlen
    norm_num [UInt256.size])

def bytesToLimbsSuffixMemory (mem : ByteArray) (aw dataPtr limbsPtr : UInt256)
    (dataLen : Nat) : ByteArray :=
  if dataLen % 32 = 0 then mem
  else partialWordMemory mem aw dataPtr (UInt256.ofNat dataLen)
    (UInt256.ofNat (dataLen % 32)) limbsPtr

def bytesToLimbsSuffixActiveWords (aw dataPtr limbsPtr : UInt256) (dataLen : Nat) :
    UInt256 :=
  if dataLen % 32 = 0 then aw
  else partialWordActiveWords aw dataPtr (UInt256.ofNat dataLen) limbsPtr

def bytesToLimbsSuffixSteps (dataLen : Nat) : Nat :=
  if dataLen % 32 = 0 then 13 else 31

def bytesToLimbsSuffixGas (aw dataPtr limbsPtr : UInt256) (dataLen : Nat) : Nat :=
  if dataLen % 32 = 0 then 46
  else partialWordGas aw dataPtr (UInt256.ofNat dataLen) limbsPtr

/-- Total executable selector for the remainder phase, covering both the aligned and partial-word
paths with exact memory, active-word, step, and gas results. -/
theorem bytesToLimbsSuffixOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {index full dataPtr ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2865⟩
      (fullWordLoopStack index full dataPtr (UInt256.ofNat dataLen) ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (limbsPtr :: tail)
      (bytesToLimbsSuffixMemory mem aw dataPtr limbsPtr dataLen)
      (bytesToLimbsSuffixActiveWords aw dataPtr limbsPtr dataLen)
      rdata acc (k + bytesToLimbsSuffixSteps dataLen)
      (C + bytesToLimbsSuffixGas aw dataPtr limbsPtr dataLen) := by
  have hremEq := wordRemainder_eq hlen
  by_cases hrem : dataLen % 32 = 0
  · have hwordZero : UInt256.land (UInt256.ofNat dataLen) ⟨31⟩ = ⟨0⟩ := by
      rw [hremEq, hrem]
      apply u256_inj
      rfl
    have rd := bytesToLimbsNoRemainder (by omega) hwordZero hret h
    simpa [bytesToLimbsSuffixMemory, bytesToLimbsSuffixActiveWords,
      bytesToLimbsSuffixSteps, bytesToLimbsSuffixGas, hrem] using rd
  · have hwordNonzero : UInt256.land (UInt256.ofNat dataLen) ⟨31⟩ ≠ ⟨0⟩ := by
      rw [hremEq]
      intro hz
      have hzNat := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt
        (lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 32)) (by decide))] at hzNat
      simp only [UInt256.zero_toNat] at hzNat
      exact hrem hzNat
    have rd := bytesToLimbsPartial hdepth hwordNonzero hret h
    simpa [bytesToLimbsSuffixMemory, bytesToLimbsSuffixActiveWords,
      bytesToLimbsSuffixSteps, bytesToLimbsSuffixGas, hrem, hremEq] using rd

def bytesToLimbsFullState (mem : ByteArray) (aw dataPtr limbsPtr : UInt256)
    (dataLen : Nat) : FullWordState :=
  fullWordIterate dataPtr (UInt256.ofNat dataLen) limbsPtr (dataLen / 32)
    (fullWordInitialState mem aw)

def bytesToLimbsMemory (mem : ByteArray) (aw dataPtr limbsPtr : UInt256)
    (dataLen : Nat) : ByteArray :=
  let s := bytesToLimbsFullState mem aw dataPtr limbsPtr dataLen
  bytesToLimbsSuffixMemory s.memory s.activeWords dataPtr limbsPtr dataLen

def bytesToLimbsActiveWords (mem : ByteArray) (aw dataPtr limbsPtr : UInt256)
    (dataLen : Nat) : UInt256 :=
  let s := bytesToLimbsFullState mem aw dataPtr limbsPtr dataLen
  bytesToLimbsSuffixActiveWords s.activeWords dataPtr limbsPtr dataLen

def bytesToLimbsSteps (dataLen : Nat) : Nat :=
  6 + 79 * (dataLen / 32) + bytesToLimbsSuffixSteps dataLen

def bytesToLimbsGas (mem : ByteArray) (aw dataPtr limbsPtr : UInt256)
    (dataLen : Nat) : Nat :=
  let s := bytesToLimbsFullState mem aw dataPtr limbsPtr dataLen
  23 + fullWordIterationsGas dataPtr (UInt256.ofNat dataLen) limbsPtr
      (dataLen / 32) (fullWordInitialState mem aw) +
    bytesToLimbsSuffixGas s.activeWords dataPtr limbsPtr dataLen

def bytesToLimbsBodySteps (dataLen : Nat) : Nat :=
  79 * (dataLen / 32) + bytesToLimbsSuffixSteps dataLen

def bytesToLimbsBodyGas (mem : ByteArray) (aw dataPtr limbsPtr : UInt256)
    (dataLen : Nat) : Nat :=
  let s := bytesToLimbsFullState mem aw dataPtr limbsPtr dataLen
  fullWordIterationsGas dataPtr (UInt256.ofNat dataLen) limbsPtr
      (dataLen / 32) (fullWordInitialState mem aw) +
    bytesToLimbsSuffixGas s.activeWords dataPtr limbsPtr dataLen

/-- Complete arbitrary `bytesToLimbs` execution after the initial positive loop guard has already
entered the full-word body. -/
theorem bytesToLimbsFromBodyOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {dataPtr ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hfull : 0 < dataLen / 32)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2906⟩
      (fullWordLoopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32)) dataPtr
        (UInt256.ofNat dataLen) ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (limbsPtr :: tail)
      (bytesToLimbsMemory mem aw dataPtr limbsPtr dataLen)
      (bytesToLimbsActiveWords mem aw dataPtr limbsPtr dataLen)
      rdata acc (k + bytesToLimbsBodySteps dataLen)
      (C + bytesToLimbsBodyGas mem aw dataPtr limbsPtr dataLen) := by
  have rd2865 := fullWordBodyOfNat hdepth hlen hfull h
  let state := bytesToLimbsFullState mem aw dataPtr limbsPtr dataLen
  have rdone := bytesToLimbsSuffixOfNat
    (mem := state.memory) (aw := state.activeWords)
    (index := UInt256.ofNat (dataLen / 32))
    (full := UInt256.ofNat (dataLen / 32)) (dataPtr := dataPtr)
    (ret := ret) (limbsPtr := limbsPtr) (tail := tail)
    hdepth hlen hret (by
      simpa [state, bytesToLimbsFullState] using rd2865)
  have normalized := rdone.withIndices
    (k' := k + bytesToLimbsBodySteps dataLen) (by
      unfold bytesToLimbsBodySteps
      omega)
    (C' := C + bytesToLimbsBodyGas mem aw dataPtr limbsPtr dataLen) (by
      unfold bytesToLimbsBodyGas
      dsimp only [state]
      omega)
  simpa [bytesToLimbsMemory, bytesToLimbsActiveWords, state] using normalized

/-- Complete arbitrary multi-limb `bytesToLimbs` execution, including every full-word iteration,
the optional partial limb, its dynamic return, and an executable exact gas expression. -/
theorem bytesToLimbsOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {dataPtr ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hfull : 0 < dataLen / 32)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2857⟩
      (fullWordLoopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32)) dataPtr
        (UInt256.ofNat dataLen) ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (limbsPtr :: tail)
      (bytesToLimbsMemory mem aw dataPtr limbsPtr dataLen)
      (bytesToLimbsActiveWords mem aw dataPtr limbsPtr dataLen)
      rdata acc (k + bytesToLimbsSteps dataLen)
      (C + bytesToLimbsGas mem aw dataPtr limbsPtr dataLen) := by
  have rd2865 := fullWordLoopOfNat hdepth hlen hfull h
  let state := bytesToLimbsFullState mem aw dataPtr limbsPtr dataLen
  have rdone := bytesToLimbsSuffixOfNat
    (mem := state.memory) (aw := state.activeWords)
    (index := UInt256.ofNat (dataLen / 32))
    (full := UInt256.ofNat (dataLen / 32)) (dataPtr := dataPtr)
    (ret := ret) (limbsPtr := limbsPtr) (tail := tail)
    hdepth hlen hret (by
      simpa [state, bytesToLimbsFullState] using rd2865)
  have normalized := rdone.withIndices
    (k' := k + bytesToLimbsSteps dataLen) (by
      unfold bytesToLimbsSteps
      omega)
    (C' := C + bytesToLimbsGas mem aw dataPtr limbsPtr dataLen) (by
      unfold bytesToLimbsGas
      dsimp only [state]
      omega)
  simpa [bytesToLimbsMemory, bytesToLimbsActiveWords, state] using normalized

/-- Total `bytesToLimbs` execution for every Osaka-valid byte length.  The zero-full-limb case
executes the generated false loop edge and then shares the same executable remainder selector. -/
theorem bytesToLimbsTotalOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {dataPtr ret limbsPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2857⟩
      (fullWordLoopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32)) dataPtr
        (UInt256.ofNat dataLen) ret limbsPtr tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (limbsPtr :: tail)
      (bytesToLimbsMemory mem aw dataPtr limbsPtr dataLen)
      (bytesToLimbsActiveWords mem aw dataPtr limbsPtr dataLen)
      rdata acc (k + bytesToLimbsSteps dataLen)
      (C + bytesToLimbsGas mem aw dataPtr limbsPtr dataLen) := by
  by_cases hfull : 0 < dataLen / 32
  · exact bytesToLimbsOfNat hdepth hlen hfull hret h
  · have hdiv : dataLen / 32 = 0 := by omega
    have hfinished :
        UInt256.lt (⟨0⟩ : UInt256) (UInt256.ofNat (dataLen / 32)) = ⟨0⟩ := by
      rw [hdiv]
      native_decide
    have rd2865 := fullWordLoopEmpty (by omega) hfinished h
    have rdone := bytesToLimbsSuffixOfNat hdepth hlen hret rd2865
    have normalized := rdone.withIndices
      (k' := k + bytesToLimbsSteps dataLen) (by
        unfold bytesToLimbsSteps
        rw [hdiv]
        omega)
      (C' := C + bytesToLimbsGas mem aw dataPtr limbsPtr dataLen) (by
        unfold bytesToLimbsGas bytesToLimbsFullState
        rw [hdiv]
        simp [fullWordIterate, fullWordIterationsGas, fullWordInitialState]
        omega)
    simpa [bytesToLimbsMemory, bytesToLimbsActiveWords, bytesToLimbsFullState,
      hdiv, fullWordIterate, fullWordInitialState] using normalized

end MultiLimbGenerated

end Modexp
