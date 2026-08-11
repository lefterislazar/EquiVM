import Examples.Precompiles.Modexp.MultiLimbArithmeticTrace
import Examples.Precompiles.Modexp.MultiLimbGenerated

/-!
# Exact `limbsToBytes` execution

This module turns the generated traces for the deployed helper at PC 3559 into an arbitrary-length
recursive execution theorem. The model follows every checked arithmetic helper, array bounds
check, `MLOAD`, and `MSTORE`; in particular, the optional partial word is the masked merge from the
Solidity assembly rather than a replacement numeric serialization.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbLimbsToBytes

open Modexp.MultiLimbArithmeticTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def loopStack (i full limbs dataLen out ret : UInt256) (tail : List UInt256) :
    List UInt256 :=
  i :: full :: limbs :: dataLen :: out :: ret :: tail

def sourceAddress (i limbs : UInt256) : UInt256 :=
  i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩

def outputOffset (i dataLen : UInt256) : UInt256 :=
  dataLen.sub ((i + ⟨1⟩).shiftLeft ⟨5⟩)

def outputAddress (i dataLen out : UInt256) : UInt256 :=
  out + outputOffset i dataLen + ⟨32⟩

def headerActiveWords (aw limbs : UInt256) : UInt256 :=
  readWords1 aw limbs

def sourceActiveWords (aw i limbs : UInt256) : UInt256 :=
  readWords1 (headerActiveWords aw limbs) (sourceAddress i limbs)

def iterationActiveWords (aw i limbs dataLen out : UInt256) : UInt256 :=
  readWords1 (sourceActiveWords aw i limbs) (outputAddress i dataLen out)

def headerValue (mem : ByteArray) (aw limbs : UInt256) : UInt256 :=
  readWord mem aw limbs

def sourceValue (mem : ByteArray) (aw i limbs : UInt256) : UInt256 :=
  readWord mem (headerActiveWords aw limbs) (sourceAddress i limbs)

def iterationMemory (mem : ByteArray) (aw i limbs dataLen out : UInt256) : ByteArray :=
  (sourceValue mem aw i limbs).toByteArray.write
    0 mem (outputAddress i dataLen out).toNat 32

def iterationGas (aw i limbs dataLen out : UInt256) : Nat :=
  let aw1 := headerActiveWords aw limbs
  let aw2 := sourceActiveWords aw i limbs
  let aw3 := iterationActiveWords aw i limbs dataLen out
  29 + (56 + (262 +
    ((Cₘ aw1 - Cₘ aw) + ((Cₘ aw2 - Cₘ aw1) + (Cₘ aw3 - Cₘ aw2)))))

def stepSafe (mem : ByteArray) (aw i limbs dataLen : UInt256) : Prop :=
  i.gt (i + ⟨1⟩) = ⟨0⟩ ∧
  ((i + ⟨1⟩).isZero.lor
    ((⟨32⟩ : UInt256).eq (((i + ⟨1⟩).shiftLeft ⟨5⟩).div (i + ⟨1⟩)))).isZero = ⟨0⟩ ∧
  (outputOffset i dataLen).gt dataLen = ⟨0⟩ ∧
  (i.lt (headerValue mem aw limbs)).isZero = ⟨0⟩

/-- The initial helper frame and successful first loop guard. -/
theorem enterLoop
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {limbs out dataLen ret full : UInt256}
    (hdepth : tail.length + 4 ≤ 1016)
    (hfull : dataLen.shiftRight ⟨5⟩ = full)
    (hcontinue : (⟨0⟩ : UInt256).lt full ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3559⟩
      (limbs :: out :: dataLen :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3644⟩
      (loopStack ⟨0⟩ full limbs dataLen out ret tail)
      mem aw rdata acc (k + 14) (C + 44) := by
  have rd := GeneratedTraces.trace_3559_taken (tail := ret :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) (by
      simpa [hfull] using hcontinue) (by native_decide)
  simpa [loopStack, hfull, Nat.add_comm] using rd

/-- The initial helper frame when there are no complete limbs. -/
theorem skipLoop
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {limbs out dataLen ret full : UInt256}
    (hdepth : tail.length + 4 ≤ 1016)
    (hfull : dataLen.shiftRight ⟨5⟩ = full)
    (hfinished : (⟨0⟩ : UInt256).lt full = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3559⟩
      (limbs :: out :: dataLen :: ret :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack ⟨0⟩ full limbs dataLen out ret tail)
      mem aw rdata acc (k + 14) (C + 44) := by
  have rd := GeneratedTraces.trace_3559_notTaken (tail := ret :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) (by
      simpa [hfull] using hfinished)
  simpa [loopStack, hfull, Nat.add_comm] using
    (rd.withPC (pc' := ⟨3576⟩) (by native_decide))

/-- One full-limb iteration whose following guard enters another iteration. -/
theorem iterationContinue
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i full limbs dataLen out ret limb : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hsafe : stepSafe mem aw i limbs dataLen)
    (hheaderAw : headerActiveWords aw limbs = aw)
    (hsourceAw : sourceActiveWords aw i limbs = aw)
    (houtputAw : iterationActiveWords aw i limbs dataLen out = aw)
    (hsource : sourceValue mem aw i limbs = limb)
    (hcontinue : (i + ⟨1⟩).lt full ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3644⟩
      (loopStack i full limbs dataLen out ret tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3644⟩
      (loopStack (i + ⟨1⟩) full limbs dataLen out ret tail)
      (limb.toByteArray.write 0 mem (outputAddress i dataLen out).toNat 32)
      aw rdata acc (k + 95) (C + 347) := by
  rcases hsafe with ⟨hadd, hshift, hsub, hindex⟩
  have rd1336 := GeneratedTraces.trace_3644_notTaken
    (tail := full :: limbs :: dataLen :: out :: ret :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hadd
  have rd2926 := GeneratedTraces.trace_1336_jump
    (by simp only [List.length_cons]; omega) rd1336 (by native_decide) (by native_decide)
  have rd1924 := GeneratedTraces.trace_2926_notTaken
    (by simp only [List.length_cons]; omega) rd2926 (by native_decide) hshift
  have rd3662 := GeneratedTraces.trace_1924_jump
    (by simp only [List.length_cons]; omega) rd1924 (by native_decide) (by native_decide)
  have rd1115 := GeneratedTraces.trace_3662_notTaken
    (by simp only [List.length_cons]; omega) rd3662 (by native_decide) hsub
  have rd3668 := GeneratedTraces.trace_1115_jump
    (by simp only [List.length_cons]; omega) rd1115 (by native_decide) (by native_decide)
  have rd1539 := GeneratedTraces.trace_3668_notTaken
    (by simp only [List.length_cons]; omega) rd3668 (by native_decide) (by
      simpa [headerValue] using hindex)
  have rd3680 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have rd3644 := GeneratedTraces.trace_3680_taken
    (by simp only [List.length_cons]; omega) rd3680 (by native_decide) hcontinue
      (by native_decide)
  have hheaderAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat limbs.toNat 32) = aw := by
    simpa [headerActiveWords, readWords1] using hheaderAw
  have hsourceAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat
        (i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩).toNat 32) = aw := by
    simpa [sourceActiveWords, headerActiveWords, readWords1, hheaderAwRaw] using hsourceAw
  have houtputAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat
        (out + dataLen.sub ((i + ⟨1⟩).shiftLeft ⟨5⟩) + ⟨32⟩).toNat 32) = aw := by
    simpa only [iterationActiveWords, hsourceAw, outputAddress, outputOffset, readWords1]
      using houtputAw
  have hsourceRaw :
      (if (i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩).toNat ≥ mem.size ∨
          i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩ ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding (i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩).toNat 32))) = limb := by
    simpa [sourceValue, readWord, hheaderAw] using hsource
  have normalized := rd3644.withIndices (k' := k + 95) (by omega)
    (C' := C + 347) (by
      simp only [hheaderAwRaw,
        hsourceAwRaw, houtputAwRaw, Nat.sub_self, Nat.add_zero]
      omega)
  simpa only [loopStack, sourceAddress, outputAddress, outputOffset,
    hheaderAwRaw, hsourceAwRaw, houtputAwRaw, hsourceRaw] using normalized

/-- The final full-limb iteration, ending at the remainder suffix. -/
theorem iterationExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i full limbs dataLen out ret limb : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hsafe : stepSafe mem aw i limbs dataLen)
    (hheaderAw : headerActiveWords aw limbs = aw)
    (hsourceAw : sourceActiveWords aw i limbs = aw)
    (houtputAw : iterationActiveWords aw i limbs dataLen out = aw)
    (hsource : sourceValue mem aw i limbs = limb)
    (hfinished : (i + ⟨1⟩).lt full = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3644⟩
      (loopStack i full limbs dataLen out ret tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack (i + ⟨1⟩) full limbs dataLen out ret tail)
      (limb.toByteArray.write 0 mem (outputAddress i dataLen out).toNat 32)
      aw rdata acc (k + 95) (C + 347) := by
  rcases hsafe with ⟨hadd, hshift, hsub, hindex⟩
  have rd1336 := GeneratedTraces.trace_3644_notTaken
    (tail := full :: limbs :: dataLen :: out :: ret :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hadd
  have rd2926 := GeneratedTraces.trace_1336_jump
    (by simp only [List.length_cons]; omega) rd1336 (by native_decide) (by native_decide)
  have rd1924 := GeneratedTraces.trace_2926_notTaken
    (by simp only [List.length_cons]; omega) rd2926 (by native_decide) hshift
  have rd3662 := GeneratedTraces.trace_1924_jump
    (by simp only [List.length_cons]; omega) rd1924 (by native_decide) (by native_decide)
  have rd1115 := GeneratedTraces.trace_3662_notTaken
    (by simp only [List.length_cons]; omega) rd3662 (by native_decide) hsub
  have rd3668 := GeneratedTraces.trace_1115_jump
    (by simp only [List.length_cons]; omega) rd1115 (by native_decide) (by native_decide)
  have rd1539 := GeneratedTraces.trace_3668_notTaken
    (by simp only [List.length_cons]; omega) rd3668 (by native_decide) (by
      simpa [headerValue] using hindex)
  have rd3680 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have rd3576 := GeneratedTraces.trace_3680_notTaken
    (by simp only [List.length_cons]; omega) rd3680 (by native_decide) hfinished
  have hheaderAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat limbs.toNat 32) = aw := by
    simpa [headerActiveWords, readWords1] using hheaderAw
  have hsourceAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat
        (i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩).toNat 32) = aw := by
    simpa [sourceActiveWords, headerActiveWords, readWords1, hheaderAwRaw] using hsourceAw
  have houtputAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat
        (out + dataLen.sub ((i + ⟨1⟩).shiftLeft ⟨5⟩) + ⟨32⟩).toNat 32) = aw := by
    simpa only [iterationActiveWords, hsourceAw, outputAddress, outputOffset, readWords1]
      using houtputAw
  have hsourceRaw :
      (if (i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩).toNat ≥ mem.size ∨
          i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩ ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding (i.shiftLeft ⟨5⟩ + limbs + ⟨32⟩).toNat 32))) = limb := by
    simpa [sourceValue, readWord, hheaderAw] using hsource
  have rd3576' := rd3576.withPC (pc' := ⟨3576⟩) (by native_decide)
  have normalized := rd3576'.withIndices (k' := k + 95) (by omega)
    (C' := C + 347) (by
      simp only [hheaderAwRaw,
        hsourceAwRaw, houtputAwRaw, Nat.sub_self, Nat.add_zero]
      omega)
  simpa only [loopStack, sourceAddress, outputAddress, outputOffset,
    hheaderAwRaw, hsourceAwRaw, houtputAwRaw, hsourceRaw] using normalized

structure FullState where
  index : UInt256
  memory : ByteArray

def advance (aw limbs dataLen out : UInt256) (s : FullState) : FullState where
  index := s.index + ⟨1⟩
  memory := (sourceValue s.memory aw s.index limbs).toByteArray.write
    0 s.memory (outputAddress s.index dataLen out).toNat 32

def iterate (aw limbs dataLen out : UInt256) : Nat → FullState → FullState
  | 0, s => s
  | n + 1, s => iterate aw limbs dataLen out n (advance aw limbs dataLen out s)

def initialState (mem : ByteArray) : FullState where
  index := ⟨0⟩
  memory := mem

def ValidStep (aw limbs dataLen out : UInt256) (s : FullState) : Prop :=
  stepSafe s.memory aw s.index limbs dataLen ∧
  headerActiveWords aw limbs = aw ∧
  sourceActiveWords aw s.index limbs = aw ∧
  iterationActiveWords aw s.index limbs dataLen out = aw

@[simp] theorem iterate_advance (aw limbs dataLen out : UInt256)
    (n : Nat) (s : FullState) :
    iterate aw limbs dataLen out n (advance aw limbs dataLen out s) =
      iterate aw limbs dataLen out (n + 1) s := by
  rfl

theorem iterate_index (aw limbs dataLen out : UInt256) (n : Nat) (s : FullState) :
    (iterate aw limbs dataLen out n s).index = s.index + UInt256.ofNat n := by
  induction n generalizing s with
  | zero =>
      simp only [iterate]
      rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by apply u256_inj; rfl]
      rw [u256_add_comm]
      exact (u256_zero_add s.index).symm
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega]
      simp only [iterate]
      rw [ih]
      change (s.index + ⟨1⟩) + UInt256.ofNat n =
        s.index + UInt256.ofNat (Nat.succ n)
      rw [u256_add_assoc, u256_one_add_ofNat]

/-- Execute a positive selected sequence of full-limb writes. Every checked-arithmetic, array
bounds, and active-memory fact is supplied at the state where the bytecode observes it. -/
theorem iterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {full limbs dataLen out ret : UInt256}
    (state : FullState)
    (hdepth : tail.length + 6 ≤ 1014)
    (hcount : 0 < count)
    (hvalid : ∀ j, j < count →
      ValidStep aw limbs dataLen out (iterate aw limbs dataLen out j state))
    (hcontinue : ∀ j, j + 1 < count →
      ((iterate aw limbs dataLen out j state).index + ⟨1⟩).lt full ≠ ⟨0⟩)
    (hfinished : (iterate aw limbs dataLen out count state).index.lt full = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3644⟩
      (loopStack state.index full limbs dataLen out ret tail)
      state.memory aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack (iterate aw limbs dataLen out count state).index
        full limbs dataLen out ret tail)
      (iterate aw limbs dataLen out count state).memory aw rdata acc
      (k + 95 * count) (C + 347 * count) := by
  induction count generalizing state k C with
  | zero => omega
  | succ count ih =>
      rcases hvalid 0 (by omega) with ⟨hsafe, hheaderAw, hsourceAw, houtputAw⟩
      cases count with
      | zero =>
          have hexit := iterationExit hdepth hsafe hheaderAw hsourceAw houtputAw rfl
            (by simpa [iterate, advance] using hfinished) h
          simpa [iterate, advance, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
            using hexit
      | succ count =>
          have hnext := iterationContinue hdepth hsafe hheaderAw hsourceAw houtputAw rfl
            (hcontinue 0 (by omega)) h
          have hvalid' : ∀ j, j < count + 1 →
              ValidStep aw limbs dataLen out
                (iterate aw limbs dataLen out j (advance aw limbs dataLen out state)) := by
            intro j hj
            simpa [iterate_advance] using hvalid (j + 1) (by omega)
          have hcontinue' : ∀ j, j + 1 < count + 1 →
              ((iterate aw limbs dataLen out j (advance aw limbs dataLen out state)).index +
                ⟨1⟩).lt full ≠ ⟨0⟩ := by
            intro j hj
            simpa [iterate_advance] using hcontinue (j + 1) (by omega)
          have hfinished' :
              (iterate aw limbs dataLen out (count + 1)
                (advance aw limbs dataLen out state)).index.lt full = ⟨0⟩ := by
            simpa [iterate_advance, Nat.add_assoc] using hfinished
          have hrest := ih (state := advance aw limbs dataLen out state)
            (by omega) hvalid' hcontinue' hfinished' hnext
          have normalized := hrest.withIndices
            (k' := k + 95 * (count + 2)) (by omega)
            (C' := C + 347 * (count + 2)) (by omega)
          simpa [iterate, advance, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using normalized

private theorem shiftRight_div32 {n : Nat} (hn : n ≤ 1024) :
    UInt256.shiftRight (UInt256.ofNat n) ⟨5⟩ = UInt256.ofNat (n / 32) := by
  have hnWord : n < UInt256.size := lt_of_le_of_lt hn (by decide)
  have hdivWord : n / 32 < UInt256.size :=
    lt_of_le_of_lt (Nat.div_le_self n 32) hnWord
  apply u256_inj
  rw [shiftRight_toNat_of_lt256 _ _ (by decide),
    UInt256.toNat_ofNat_of_lt hnWord,
    show (⟨5⟩ : UInt256).toNat = 5 by decide,
    UInt256.toNat_ofNat_of_lt hdivWord]
  norm_num

theorem initial_index (aw limbs dataLen out : UInt256) (j : Nat) (mem : ByteArray) :
    (iterate aw limbs dataLen out j (initialState mem)).index = UInt256.ofNat j := by
  rw [iterate_index]
  change (⟨0⟩ : UInt256) + UInt256.ofNat j = UInt256.ofNat j
  exact u256_zero_add _

/-- Complete the positive full-limb phase for an arbitrary Osaka-valid byte length. -/
theorem fullPhaseOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {limbs out ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hlen : dataLen ≤ 1024)
    (hfull : 0 < dataLen / 32)
    (hvalid : ∀ j, j < dataLen / 32 →
      ValidStep aw limbs (UInt256.ofNat dataLen) out
        (iterate aw limbs (UInt256.ofNat dataLen) out j (initialState mem)))
    (h : RDx runtimeBytecode ee g s0 ⟨3644⟩
      (loopStack ⟨0⟩ (UInt256.ofNat (dataLen / 32)) limbs
        (UInt256.ofNat dataLen) out ret tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack (UInt256.ofNat (dataLen / 32)) (UInt256.ofNat (dataLen / 32))
        limbs (UInt256.ofNat dataLen) out ret tail)
      (iterate aw limbs (UInt256.ofNat dataLen) out (dataLen / 32)
        (initialState mem)).memory aw rdata acc
      (k + 95 * (dataLen / 32)) (C + 347 * (dataLen / 32)) := by
  have hqBound : dataLen / 32 < UInt256.size := by
    apply lt_of_le_of_lt (show dataLen / 32 ≤ 32 by omega)
    decide
  have hcontinue : ∀ j, j + 1 < dataLen / 32 →
      ((iterate aw limbs (UInt256.ofNat dataLen) out j (initialState mem)).index +
        ⟨1⟩).lt (UInt256.ofNat (dataLen / 32)) ≠ ⟨0⟩ := by
    intro j hj
    rw [initial_index, u256_add_comm, u256_one_add_ofNat]
    have hjBound : j + 1 < UInt256.size := by omega
    have hlt := ult_one (a := UInt256.ofNat (j + 1))
      (b := UInt256.ofNat (dataLen / 32)) (by
        rw [UInt256.toNat_ofNat_of_lt hjBound, UInt256.toNat_ofNat_of_lt hqBound]
        exact hj)
    rw [hlt]
    decide
  have hfinished :
      (iterate aw limbs (UInt256.ofNat dataLen) out (dataLen / 32)
        (initialState mem)).index.lt (UInt256.ofNat (dataLen / 32)) = ⟨0⟩ := by
    rw [initial_index]
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hqBound]
  have rd := iterations (state := initialState mem) hdepth hfull hvalid
    hcontinue hfinished h
  simpa [initial_index] using rd

/-- Return directly after an aligned byte length. -/
theorem noRemainder
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index full limbs dataLen out ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (hrem : UInt256.land dataLen ⟨31⟩ = ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack index full limbs dataLen out ret tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret tail mem aw rdata acc (k + 14) (C + 48) := by
  have rd3588 := GeneratedTraces.trace_3576_notTaken
    (tail := out :: ret :: tail) (by simp only [List.length_cons]; omega)
    h (by native_decide) hrem
  have rdret := GeneratedTraces.trace_3588_jump
    (tail := tail) (by omega) rd3588 (by native_decide) hret
  simpa [loopStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdret

/- The generated partial-word trace includes both source/output loads, the exact mask expression,
the output store, and the shared four-word cleanup at PC 2334. Its inferred state is normalized by
`partialRemainder` below after the concrete in-bounds equalities are supplied. -/
evm_theorem partialRaw
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index full limbs dataLen out ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hrem : UInt256.land dataLen ⟨31⟩ ≠ ⟨0⟩)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack index full limbs dataLen out ret tail)
      mem aw rdata acc k C) := by
  have rd3593 := GeneratedTraces.trace_3576_taken
    (tail := out :: ret :: tail) (by simp only [List.length_cons]; omega)
    h (by native_decide) hrem (by native_decide)
  have rdret := GeneratedTraces.trace_3593_jump
    (tail := tail) (by omega) rd3593 (by native_decide) hret
  exact rdret

def partialSourceAddress (limbs dataLen : UInt256) : UInt256 :=
  dataLen.land (UInt256.lnot ⟨31⟩) + limbs + ⟨32⟩

def partialOutputAddress (out : UInt256) : UInt256 :=
  out + ⟨32⟩

def partialSourceActiveWords (aw limbs dataLen : UInt256) : UInt256 :=
  readWords1 aw (partialSourceAddress limbs dataLen)

def partialOutputActiveWords (aw limbs dataLen out : UInt256) : UInt256 :=
  readWords1 (partialSourceActiveWords aw limbs dataLen) (partialOutputAddress out)

def partialStoreActiveWords (aw limbs dataLen out : UInt256) : UInt256 :=
  readWords1 (partialOutputActiveWords aw limbs dataLen out) (partialOutputAddress out)

def partialSourceValue (mem : ByteArray) (aw limbs dataLen : UInt256) : UInt256 :=
  readWord mem aw (partialSourceAddress limbs dataLen)

def partialExistingValue
    (mem : ByteArray) (aw limbs dataLen out : UInt256) : UInt256 :=
  readWord mem (partialSourceActiveWords aw limbs dataLen) (partialOutputAddress out)

def partialShift (dataLen : UInt256) : UInt256 :=
  ((⟨32⟩ : UInt256).sub (dataLen.land ⟨31⟩)).shiftLeft ⟨3⟩

def partialLowMask (dataLen : UInt256) : UInt256 :=
  (⟨1⟩ : UInt256).shiftLeft (partialShift dataLen) + UInt256.lnot ⟨0⟩

def partialMergedValue (source existing dataLen : UInt256) : UInt256 :=
  ((source.shiftLeft (partialShift dataLen)).land (partialLowMask dataLen).lnot).lor
    (existing.land (partialLowMask dataLen))

def partialMemory
    (mem : ByteArray) (source existing dataLen out : UInt256) : ByteArray :=
  (partialMergedValue source existing dataLen).toByteArray.write
    0 mem (partialOutputAddress out).toNat 32

/-- Execute the non-aligned suffix, including both loads and the Solidity masked merge. -/
theorem partialRemainder
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {index full limbs dataLen out ret source existing : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hrem : UInt256.land dataLen ⟨31⟩ ≠ ⟨0⟩)
    (hsourceAw : partialSourceActiveWords aw limbs dataLen = aw)
    (houtputAw : partialOutputActiveWords aw limbs dataLen out = aw)
    (hstoreAw : partialStoreActiveWords aw limbs dataLen out = aw)
    (hsource : partialSourceValue mem aw limbs dataLen = source)
    (hexisting : partialExistingValue mem aw limbs dataLen out = existing)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack index full limbs dataLen out ret tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret tail
      (partialMemory mem source existing dataLen out)
      aw rdata acc (k + 60) (C + 185) := by
  have rd := partialRaw hdepth hrem hret h
  have hsourceAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat
        (dataLen.land (UInt256.lnot ⟨31⟩) + limbs + ⟨32⟩).toNat 32) = aw := by
    simpa [partialSourceActiveWords, partialSourceAddress, readWords1] using hsourceAw
  have houtputAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat (out + ⟨32⟩).toNat 32) = aw := by
    simpa [partialOutputActiveWords, partialOutputAddress, readWords1, hsourceAw] using houtputAw
  have hstoreAwRaw :
      UInt256.ofNat (MachineState.M aw.toNat (out + ⟨32⟩).toNat 32) = aw := by
    simpa [partialStoreActiveWords, partialOutputAddress, readWords1, houtputAw] using hstoreAw
  have hsourceRaw :
      (if (dataLen.land (UInt256.lnot ⟨31⟩) + limbs + ⟨32⟩).toNat ≥ mem.size ∨
          dataLen.land (UInt256.lnot ⟨31⟩) + limbs + ⟨32⟩ ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding
            (dataLen.land (UInt256.lnot ⟨31⟩) + limbs + ⟨32⟩).toNat 32))) = source := by
    simpa [partialSourceValue, partialSourceAddress, readWord] using hsource
  have hexistingRaw :
      (if (out + ⟨32⟩).toNat ≥ mem.size ∨ out + ⟨32⟩ ≥ aw * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          (mem.readWithPadding (out + ⟨32⟩).toNat 32))) = existing := by
    simpa [partialExistingValue, partialOutputAddress, readWord, hsourceAw] using hexisting
  have normalized := rd.withIndices (k' := k + 60) (by omega)
    (C' := C + 185) (by
      simp only [hsourceAwRaw, houtputAwRaw, Nat.sub_self, Nat.add_zero]
      omega)
  simpa only [partialMemory, partialMergedValue, partialLowMask, partialShift,
    partialOutputAddress, hsourceAwRaw, houtputAwRaw, hstoreAwRaw,
    hsourceRaw, hexistingRaw] using normalized

def PartialValid
    (_mem : ByteArray) (aw limbs dataLen out : UInt256) : Prop :=
  partialSourceActiveWords aw limbs dataLen = aw ∧
  partialOutputActiveWords aw limbs dataLen out = aw ∧
  partialStoreActiveWords aw limbs dataLen out = aw

def limbsToBytesSuffixMemory
    (mem : ByteArray) (aw limbs out : UInt256) (dataLen : Nat) : ByteArray :=
  if dataLen % 32 = 0 then mem
  else partialMemory mem
    (partialSourceValue mem aw limbs (UInt256.ofNat dataLen))
    (partialExistingValue mem aw limbs (UInt256.ofNat dataLen) out)
    (UInt256.ofNat dataLen) out

def limbsToBytesSuffixSteps (dataLen : Nat) : Nat :=
  if dataLen % 32 = 0 then 14 else 60

def limbsToBytesSuffixGas (dataLen : Nat) : Nat :=
  if dataLen % 32 = 0 then 48 else 185

/-- Executable aligned/partial selector for the helper suffix. -/
theorem suffixOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {index full limbs out ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (hlen : dataLen ≤ 1024)
    (hpartial : dataLen % 32 ≠ 0 →
      PartialValid mem aw limbs (UInt256.ofNat dataLen) out)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3576⟩
      (loopStack index full limbs (UInt256.ofNat dataLen) out ret tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret tail
      (limbsToBytesSuffixMemory mem aw limbs out dataLen)
      aw rdata acc (k + limbsToBytesSuffixSteps dataLen)
      (C + limbsToBytesSuffixGas dataLen) := by
  have hremEq := MultiLimbGenerated.wordRemainder_eq hlen
  by_cases hrem : dataLen % 32 = 0
  · have hwordZero : UInt256.land (UInt256.ofNat dataLen) ⟨31⟩ = ⟨0⟩ := by
      rw [hremEq, hrem]
      apply u256_inj
      rfl
    have rd := noRemainder (by omega) hwordZero hret h
    simpa [limbsToBytesSuffixMemory, limbsToBytesSuffixSteps,
      limbsToBytesSuffixGas, hrem] using rd
  · have hwordNonzero : UInt256.land (UInt256.ofNat dataLen) ⟨31⟩ ≠ ⟨0⟩ := by
      rw [hremEq]
      intro hz
      have hzNat := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt
        (lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 32)) (by decide))] at hzNat
      simp only [UInt256.zero_toNat] at hzNat
      exact hrem hzNat
    rcases hpartial hrem with ⟨hsourceAw, houtputAw, hstoreAw⟩
    have rd := partialRemainder hdepth hwordNonzero hsourceAw houtputAw hstoreAw
      (source := partialSourceValue mem aw limbs (UInt256.ofNat dataLen))
      (existing := partialExistingValue mem aw limbs (UInt256.ofNat dataLen) out)
      rfl rfl hret h
    simpa [limbsToBytesSuffixMemory, limbsToBytesSuffixSteps,
      limbsToBytesSuffixGas, hrem] using rd

def limbsToBytesFullState
    (mem : ByteArray) (aw limbs out : UInt256) (dataLen : Nat) : FullState :=
  iterate aw limbs (UInt256.ofNat dataLen) out (dataLen / 32) (initialState mem)

def limbsToBytesMemory
    (mem : ByteArray) (aw limbs out : UInt256) (dataLen : Nat) : ByteArray :=
  let s := limbsToBytesFullState mem aw limbs out dataLen
  limbsToBytesSuffixMemory s.memory aw limbs out dataLen

def limbsToBytesSteps (dataLen : Nat) : Nat :=
  14 + 95 * (dataLen / 32) + limbsToBytesSuffixSteps dataLen

def limbsToBytesGas (dataLen : Nat) : Nat :=
  44 + 347 * (dataLen / 32) + limbsToBytesSuffixGas dataLen

/-- Complete arbitrary-length execution of `limbsToBytes` from its deployed entry at PC 3559.
The theorem executes every full-limb iteration and selects the real aligned or masked-partial
suffix, with exact path-sensitive step and gas totals. -/
theorem totalOfNat
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C dataLen : Nat} {tail : List UInt256}
    {limbs out ret : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hlen : dataLen ≤ 1024)
    (hvalid : ∀ j, j < dataLen / 32 →
      ValidStep aw limbs (UInt256.ofNat dataLen) out
        (iterate aw limbs (UInt256.ofNat dataLen) out j (initialState mem)))
    (hpartial : dataLen % 32 ≠ 0 → PartialValid
      (limbsToBytesFullState mem aw limbs out dataLen).memory
      aw limbs (UInt256.ofNat dataLen) out)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3559⟩
      (limbs :: out :: UInt256.ofNat dataLen :: ret :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret tail
      (limbsToBytesMemory mem aw limbs out dataLen)
      aw rdata acc (k + limbsToBytesSteps dataLen)
      (C + limbsToBytesGas dataLen) := by
  have hshift := shiftRight_div32 hlen
  by_cases hfull : 0 < dataLen / 32
  · have hqBound : dataLen / 32 < UInt256.size := by
      apply lt_of_le_of_lt (show dataLen / 32 ≤ 32 by omega)
      decide
    have hcontinue :
        (UInt256.lt ⟨0⟩ (UInt256.ofNat (dataLen / 32))) ≠ ⟨0⟩ := by
      have hlt := ult_one (a := (⟨0⟩ : UInt256))
        (b := UInt256.ofNat (dataLen / 32)) (by
          rw [UInt256.zero_toNat, UInt256.toNat_ofNat_of_lt hqBound]
          exact hfull)
      rw [hlt]
      decide
    have rd3644 := enterLoop (by omega) hshift hcontinue h
    have rd3576 := fullPhaseOfNat hdepth hlen hfull hvalid rd3644
    have rdone := suffixOfNat (tail := tail) (by omega) hlen hpartial hret (by
      simpa [limbsToBytesFullState] using rd3576)
    have normalized := rdone.withIndices
      (k' := k + limbsToBytesSteps dataLen) (by
        unfold limbsToBytesSteps
        omega)
      (C' := C + limbsToBytesGas dataLen) (by
        unfold limbsToBytesGas
        omega)
    simpa [limbsToBytesMemory, limbsToBytesFullState] using normalized
  · have hdiv : dataLen / 32 = 0 := by omega
    have hfinished :
        UInt256.lt (⟨0⟩ : UInt256) (UInt256.ofNat (dataLen / 32)) = ⟨0⟩ := by
      rw [hdiv]
      native_decide
    have rd3576 := skipLoop (by omega) hshift hfinished h
    have rdone := suffixOfNat (tail := tail) (by omega) hlen (by
      intro hrem
      simpa [limbsToBytesFullState, hdiv, iterate, initialState] using hpartial hrem)
      hret rd3576
    have normalized := rdone.withIndices
      (k' := k + limbsToBytesSteps dataLen) (by
        unfold limbsToBytesSteps
        rw [hdiv]
        omega)
      (C' := C + limbsToBytesGas dataLen) (by
        unfold limbsToBytesGas
        rw [hdiv]
        omega)
    simpa [limbsToBytesMemory, limbsToBytesFullState, hdiv, iterate, initialState]
      using normalized

end Modexp.MultiLimbLimbsToBytes
