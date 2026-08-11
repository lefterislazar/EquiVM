import Examples.Precompiles.Modexp.MultiLimbMontgomeryTrace
import Examples.Precompiles.Modexp.MultiLimbDivisionTrace

/-!
# Generated CIOS final comparison and subtraction

The conditional subtraction in `_montMul` uses the same word subtraction model as the division
routine.  This file connects its distinct PC 4202 trace to that model and iterates it exactly.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomeryFinalize

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Strict comparison in the order used by the bytecode: highest limb first, despite the
little-endian in-memory representation. -/
def limbsLtMSB : List UInt256 → List UInt256 → Prop
  | [], [] => False
  | left :: lefts, right :: rights =>
      if Modexp.wordLimbsToNat lefts = Modexp.wordLimbsToNat rights then
        left.toNat < right.toNat
      else
        limbsLtMSB lefts rights
  | [], _ :: _ => True
  | _ :: _, [] => False

/-- The source's descending lexicographic comparison is ordinary natural-number comparison for
equal-length limb vectors. -/
theorem limbsLtMSB_iff
    (left right : List UInt256) (hlength : left.length = right.length) :
    limbsLtMSB left right ↔
      Modexp.wordLimbsToNat left < Modexp.wordLimbsToNat right := by
  induction left generalizing right with
  | nil =>
      have hright : right = [] := List.eq_nil_of_length_eq_zero hlength.symm
      subst right
      simp [limbsLtMSB, Modexp.wordLimbsToNat]
  | cons left lefts ih =>
      cases right with
      | nil => simp at hlength
      | cons right rights =>
          have htailLength : lefts.length = rights.length := by
            simpa using hlength
          have ih' := ih rights htailLength
          simp only [limbsLtMSB, Modexp.wordLimbsToNat]
          by_cases heq : Modexp.wordLimbsToNat lefts =
              Modexp.wordLimbsToNat rights
          · rw [if_pos heq, heq]
            omega
          · rw [if_neg heq, ih']
            have hleftBound : left.toNat < UInt256.size := left.val.isLt
            have hrightBound : right.toNat < UInt256.size := right.val.isLt
            have headTail_lt {a b highLeft highRight : Nat}
                (ha : a < UInt256.size) (hhigh : highLeft < highRight) :
                a + UInt256.size * highLeft <
                  b + UInt256.size * highRight := by
              calc
                a + UInt256.size * highLeft <
                    UInt256.size + UInt256.size * highLeft := by omega
                _ = UInt256.size * (highLeft + 1) := by ring
                _ ≤ UInt256.size * highRight := by
                  exact Nat.mul_le_mul_left UInt256.size (by omega)
                _ ≤ b + UInt256.size * highRight := by omega
            by_cases htail : Modexp.wordLimbsToNat lefts <
                Modexp.wordLimbsToNat rights
            · constructor
              · intro _
                exact headTail_lt hleftBound htail
              · intro _
                exact htail
            · have htailReverse : Modexp.wordLimbsToNat rights <
                  Modexp.wordLimbsToNat lefts := by omega
              constructor
              · intro hfalse
                exact (htail hfalse).elim
              · intro hfalse
                exact ((Nat.not_lt_of_ge
                  (Nat.le_of_lt (headTail_lt hrightBound htailReverse))) hfalse).elim

theorem limbsGeMSB_iff
    (left right : List UInt256) (hlength : left.length = right.length) :
    ¬ limbsLtMSB left right ↔
      Modexp.wordLimbsToNat right ≤ Modexp.wordLimbsToNat left := by
  rw [limbsLtMSB_iff left right hlength]
  omega

/-- The limb result selected by the source's descending comparison. -/
noncomputable def finalizeLimbs (value modulus : List UInt256) : List UInt256 :=
  by
    classical
    exact if limbsLtMSB value modulus then
      value
    else
      (Modexp.evmSubLimbs value modulus ⟨0⟩).1

theorem finalizeLimbs_length
    (value modulus : List UInt256) (hlength : value.length = modulus.length) :
    (finalizeLimbs value modulus).length = value.length := by
  classical
  unfold finalizeLimbs
  split
  · rfl
  · exact Modexp.evmSubLimbs_result_length value modulus ⟨0⟩ hlength

/-- The descending comparison and conditional limb subtraction implement the pure Montgomery
finalizer exactly. -/
theorem finalizeLimbs_value
    (value modulus : List UInt256) (hlength : value.length = modulus.length) :
    Modexp.wordLimbsToNat (finalizeLimbs value modulus) =
      Modexp.montgomeryFinalize
        (Modexp.wordLimbsToNat value) (Modexp.wordLimbsToNat modulus) := by
  classical
  by_cases hlt : limbsLtMSB value modulus
  · have hnat := (limbsLtMSB_iff value modulus hlength).mp hlt
    rw [finalizeLimbs, if_pos hlt]
    unfold Modexp.montgomeryFinalize
    rw [if_neg (by omega)]
  · have hge := (limbsGeMSB_iff value modulus hlength).mp hlt
    rw [finalizeLimbs, if_neg hlt]
    rw [(Modexp.evmSubLimbs_eq_sub value modulus hlength hge).2]
    unfold Modexp.montgomeryFinalize
    rw [if_pos hge]

def limbsWithTop (value : List UInt256) (top : UInt256) : Nat :=
  Modexp.wordLimbsToNat value +
    UInt256.size ^ value.length * top.toNat

/-- Under the CIOS `< 2n` bound, any nonzero extra word is exactly one. -/
theorem extraTop_eq_one
    (value modulus : List UInt256) (top : UInt256)
    (hlength : value.length = modulus.length)
    (htop : top ≠ ⟨0⟩)
    (hbound : limbsWithTop value top < 2 * Modexp.wordLimbsToNat modulus) :
    top = ⟨1⟩ := by
  have htopPos : 0 < top.toNat := by
    have hne : top.toNat ≠ 0 := by
      intro hzero
      apply htop
      exact uint256_toNat_eq_zero hzero
    omega
  have hmodBound := Modexp.wordLimbsToNat_lt_pow modulus
  rw [← hlength] at hmodBound
  have htopLt : top.toNat < 2 := by
    unfold limbsWithTop at hbound
    have hpowPos : 0 < UInt256.size ^ value.length := by
      exact Nat.pow_pos (by norm_num [UInt256.size])
    nlinarith
  have htopNat : top.toNat = 1 := by omega
  apply u256_inj
  rw [htopNat]
  decide

/-- With a nonzero extra CIOS word, subtracting the modulus from only the low vector correctly
borrows through that word and equals finalization of the complete `(k+1)`-word value. -/
theorem finalizeNonzeroTop_value
    (value modulus : List UInt256) (top : UInt256)
    (hlength : value.length = modulus.length)
    (htop : top ≠ ⟨0⟩)
    (hbound : limbsWithTop value top < 2 * Modexp.wordLimbsToNat modulus) :
    Modexp.wordLimbsToNat (Modexp.evmSubLimbs value modulus ⟨0⟩).1 =
      Modexp.montgomeryFinalize (limbsWithTop value top)
        (Modexp.wordLimbsToNat modulus) := by
  have htopOne := extraTop_eq_one value modulus top hlength htop hbound
  have hmodBound := Modexp.wordLimbsToNat_lt_pow modulus
  rw [← hlength] at hmodBound
  have hvalueLt : Modexp.wordLimbsToNat value < Modexp.wordLimbsToNat modulus := by
    unfold limbsWithTop at hbound
    rw [htopOne, show (⟨1⟩ : UInt256).toNat = 1 by decide] at hbound
    omega
  rw [(Modexp.evmSubLimbs_eq_add_pow_sub value modulus hlength hvalueLt).2]
  unfold Modexp.montgomeryFinalize limbsWithTop
  rw [htopOne, show (⟨1⟩ : UInt256).toNat = 1 by decide]
  rw [if_pos]
  · ring_nf
  · omega

def finalTopWord (mem : ByteArray) (aw tEnd : UInt256) : UInt256 :=
  readWord mem aw tEnd

def finalTopAw (aw tEnd : UInt256) : UInt256 :=
  readWords1 aw tEnd

def finalTopGasAfter (C : Nat) (aw tEnd : UInt256) : Nat :=
  38 + C + (Cₘ (finalTopAw aw tEnd) - Cₘ aw)

/-- Drop the completed CIOS loop frame and split on the extra top word. -/
theorem finalTopCheckBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 drop3 drop4 drop5 drop6 s7 s8 s9 tEnd : UInt256}
    (hdepth : tail.length + 11 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨4147⟩
      (drop0 :: drop1 :: drop2 :: drop3 :: drop4 :: drop5 :: drop6 ::
        s7 :: s8 :: s9 :: tEnd :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4164⟩
      (⟨4234⟩ :: (finalTopWord mem aw tEnd).isZero :: tEnd :: s7 :: s8 :: s9 ::
        (finalTopWord mem aw tEnd).isZero.isZero :: tail)
      mem (finalTopAw aw tEnd) rdata acc (15 + k) (finalTopGasAfter C aw tEnd) := by
  have rd := GeneratedTraces.trace_4147_body hdepth h
  simpa only [finalTopWord, finalTopAw, finalTopGasAfter, readWord, readWords1]
    using rd

/-- A nonzero extra word forces subtraction and skips the limb comparison. -/
theorem finalTopNonzeroToCopy
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 drop3 drop4 drop5 drop6 s7 s8 s9 tEnd : UInt256}
    (hdepth : tail.length + 11 ≤ 1024)
    (htop : finalTopWord mem aw tEnd ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4147⟩
      (drop0 :: drop1 :: drop2 :: drop3 :: drop4 :: drop5 :: drop6 ::
        s7 :: s8 :: s9 :: tEnd :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tEnd :: s7 :: s8 :: s9 :: ⟨1⟩ :: tail)
      mem (finalTopAw aw tEnd) rdata acc (16 + k)
      (finalTopGasAfter C aw tEnd + 10) := by
  have rdCheck := finalTopCheckBody hdepth h
  have hiszero : (finalTopWord mem aw tEnd).isZero = ⟨0⟩ :=
    isZero_eq_zero_of_ne htop
  have hnonzeroFlag : (finalTopWord mem aw tEnd).isZero.isZero = ⟨1⟩ := by
    rw [hiszero]
    native_decide
  have rd := rdCheck.jumpiNT (by native_decide) hiszero
    (by simp only [List.length_cons]; omega)
  simpa only [hnonzeroFlag,
    show (⟨4164⟩ : UInt256) + ⟨1⟩ = ⟨4165⟩ by native_decide,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- A zero extra word enters the descending limb comparison with `doSub` still unset. -/
theorem finalTopZeroToCompare
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 drop3 drop4 drop5 drop6 s7 s8 s9 tEnd : UInt256}
    (hdepth : tail.length + 11 ≤ 1024)
    (htop : finalTopWord mem aw tEnd = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4147⟩
      (drop0 :: drop1 :: drop2 :: drop3 :: drop4 :: drop5 :: drop6 ::
        s7 :: s8 :: s9 :: tEnd :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4234⟩
      (tEnd :: s7 :: s8 :: s9 :: ⟨0⟩ :: tail)
      mem (finalTopAw aw tEnd) rdata acc (16 + k)
      (finalTopGasAfter C aw tEnd + 10) := by
  have rdCheck := finalTopCheckBody hdepth h
  have hiszero : (finalTopWord mem aw tEnd).isZero = ⟨1⟩ := by
    rw [htop]
    native_decide
  have hflag : (finalTopWord mem aw tEnd).isZero.isZero = ⟨0⟩ := by
    rw [hiszero]
    native_decide
  have rd := rdCheck.jumpiT (by native_decide) (by rw [hiszero]; decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  simpa only [hflag, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

def finalCopyMemory
    (mem : ByteArray) (source result bytes : UInt256) : ByteArray :=
  mem.write source.toNat mem result.toNat bytes.toNat

def finalCopyAw
    (aw source result bytes : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (max result.toNat source.toNat) bytes.toNat)

def finalCopyGas
    (aw source result bytes : UInt256) : Nat :=
  11 + (Cₘ (finalCopyAw aw source result bytes) - Cₘ aw) +
    GasConstants.Gverylow + GasConstants.Gcopy * ((bytes.toNat + 31) / 32)

/-- Copy the low candidate limbs to the result buffer and stop at the conditional branch. -/
theorem finalCopyBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff source bytes doSub rightPtr resultPtr : UInt256}
    (hdepth : tail.length + 7 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tOff :: nOff :: source :: bytes :: doSub :: rightPtr :: resultPtr :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4173⟩
      (⟨4178⟩ :: doSub :: rightPtr :: resultPtr :: tail)
      (finalCopyMemory mem source resultPtr bytes)
      (finalCopyAw aw source resultPtr bytes) rdata acc (k + 6)
      (C + finalCopyGas aw source resultPtr bytes) := by
  have rd := GeneratedTraces.trace_4165_body hdepth h
  simpa [finalCopyMemory, finalCopyAw, finalCopyGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- A false `doSub` branch returns immediately after the exact low-limb copy. -/
theorem finalCopyNoSubReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff source bytes rightPtr resultPtr resultBase returnPc keep : UInt256}
    (hdepth : tail.length + 10 ≤ 1024)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tOff :: nOff :: source :: bytes :: ⟨0⟩ :: rightPtr :: resultPtr ::
        resultBase :: returnPc :: keep :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 returnPc
      (keep :: tail)
      (finalCopyMemory mem source resultPtr bytes)
      (finalCopyAw aw source resultPtr bytes) rdata acc (k + 11)
      (C + finalCopyGas aw source resultPtr bytes + 24) := by
  have rdBody := finalCopyBody (by simpa using hdepth) h
  have rd4174 := rdBody.jumpiNT (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4177 := GeneratedTraces.trace_4174_body
    (by simp only [List.length_cons]; omega) rd4174
  have rdReturn := rd4177.jump (by native_decide) hreturn
    (by simp only [List.length_cons]; omega)
  have normalized := rdReturn.withIndices
    (k' := k + 11) (C' := C + finalCopyGas aw source resultPtr bytes + 24)
    (by ring) (by ring)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

/-- A true `doSub` branch enters the shared arbitrary-width subtraction loop with exact pointers,
copied memory, and gas. -/
theorem finalCopyToSubtraction
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff source bytes doSub rightPtr resultPtr resultBase returnPc bytesAgain : UInt256}
    (hdepth : tail.length + 10 ≤ 1021)
    (hdoSub : doSub ≠ ⟨0⟩)
    (hcolumns : resultPtr.lt (⟨32⟩ + (bytesAgain + resultBase)) ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tOff :: nOff :: source :: bytes :: doSub :: rightPtr :: resultPtr ::
        resultBase :: returnPc :: bytesAgain :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4202⟩
      (resultPtr :: ⟨0⟩ :: rightPtr ::
        (⟨32⟩ + (bytesAgain + resultBase)) :: returnPc :: bytesAgain :: tail)
      (finalCopyMemory mem source resultPtr bytes)
      (finalCopyAw aw source resultPtr bytes) rdata acc (k + 23)
      (C + finalCopyGas aw source resultPtr bytes + 60) := by
  have rdBody := finalCopyBody (by simp only [List.length_cons]; omega) h
  have rd4178 := rdBody.jumpiT (by native_decide) hdoSub
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd4196 := GeneratedTraces.trace_4178_body (by omega) rd4178
  have rd4202 := rd4196.jumpiT (by native_decide) hcolumns
    (by native_decide) (by simp only [List.length_cons]; omega)
  have normalized := rd4202.withIndices
    (k' := k + 23) (C' := C + finalCopyGas aw source resultPtr bytes + 60)
    (by ring) (by ring)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

/-- One final-subtraction column, including both loads, borrow propagation, result write, pointer
updates, loop backedge, next guard, and exact gas. -/
theorem finalSubtractionBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {leftPtr borrow rightPtr stop : UInt256}
    (hdepth : tail.length + 4 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨4202⟩
      (leftPtr :: borrow :: rightPtr :: stop :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4196⟩
      (⟨4202⟩ :: (leftPtr + ⟨32⟩).lt stop :: (leftPtr + ⟨32⟩) ::
        (subtractionStep mem aw leftPtr rightPtr borrow).2 ::
        (rightPtr + ⟨32⟩) :: stop :: tail)
      (subtractionMemory mem aw leftPtr rightPtr borrow)
      (subtractionAw aw leftPtr rightPtr) rdata acc
      (k + 34) (C + subtractionGas aw leftPtr rightPtr) := by
  have rd := GeneratedTraces.trace_4202_body hdepth h
  simpa [subtractionStep, subtractionMemory, subtractionAw, subtractionGas,
    readWord, readWords1, Modexp.evmSubBorrow,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

def finalSubtractionIterationsGas : Nat → SubtractionState → Nat
  | 0, _ => 0
  | n + 1, state => subtractionGas state.activeWords state.leftPtr state.rightPtr + 10 +
      finalSubtractionIterationsGas n (subtractionAdvance state)

/-- Execute any number of final-subtraction columns whose guard continues. -/
theorem finalSubtractionIterations
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256} {stop : UInt256}
    (state : SubtractionState)
    (hdepth : tail.length + 4 ≤ 1017)
    (hcontinue : ∀ j, j < n →
      (subtractionAdvance (subtractionIterate j state)).leftPtr.lt stop ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4202⟩
      (subtractionLoopStack state stop tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4202⟩
      (subtractionLoopStack (subtractionIterate n state) stop tail)
      (subtractionIterate n state).memory
      (subtractionIterate n state).activeWords rdata acc
      (k + 35 * n) (C + finalSubtractionIterationsGas n state) := by
  induction n generalizing state k C with
  | zero => simpa [subtractionIterate, finalSubtractionIterationsGas]
  | succ n ih =>
      have rd4196 := finalSubtractionBody hdepth h
      have rdNext := rd4196.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ j, j < n →
          (subtractionAdvance
            (subtractionIterate j (subtractionAdvance state))).leftPtr.lt stop ≠ ⟨0⟩ := by
        intro j hj
        simpa [subtractionIterate_advance] using hcontinue (j + 1) (by omega)
      have rdRest := ih (state := subtractionAdvance state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 35 * (n + 1)) (by omega) rfl
      simpa [subtractionLoopStack, subtractionIterate, subtractionAdvance,
        finalSubtractionIterationsGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.mul_add] using normalized

def finalSubtractionThroughExitGas (n : Nat) (state : SubtractionState) : Nat :=
  finalSubtractionIterationsGas n state +
    subtractionGas (subtractionIterate n state).activeWords
      (subtractionIterate n state).leftPtr (subtractionIterate n state).rightPtr + 10

/-- Execute the continuing subtraction columns and the final column, exiting at PC 4197. -/
theorem finalSubtractionThroughExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256} {stop : UInt256}
    (state : SubtractionState)
    (hdepth : tail.length + 4 ≤ 1017)
    (hcontinue : ∀ j, j < n →
      (subtractionAdvance (subtractionIterate j state)).leftPtr.lt stop ≠ ⟨0⟩)
    (hexit :
      (subtractionAdvance (subtractionIterate n state)).leftPtr.lt stop = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4202⟩
      (subtractionLoopStack state stop tail)
      state.memory state.activeWords rdata acc k C) :
    let final := subtractionAdvance (subtractionIterate n state)
    RDx runtimeBytecode ee g s0 ⟨4197⟩
      (subtractionLoopStack final stop tail)
      final.memory final.activeWords rdata acc
      (k + 35 * (n + 1)) (C + finalSubtractionThroughExitGas n state) := by
  have rdIterations := finalSubtractionIterations state hdepth hcontinue h
  have rdBody := finalSubtractionBody hdepth rdIterations
  have rdExit := rdBody.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rdExit.withIndices (k' := k + 35 * (n + 1)) (by omega) rfl
  simpa [subtractionLoopStack, subtractionAdvance, finalSubtractionThroughExitGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

def finalSubtractionInitialState
    (mem : ByteArray) (aw resultPtr rightPtr : UInt256) : SubtractionState where
  leftPtr := resultPtr
  rightPtr := rightPtr
  borrow := ⟨0⟩
  memory := mem
  activeWords := aw

/-- Complete the true finalization branch: copy, execute every subtraction column, clean the loop
frame, and return to the caller with exact gas. -/
theorem finalCopySubtractionReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {tOff nOff source bytes doSub rightPtr resultPtr resultBase returnPc bytesAgain : UInt256}
    (hdepth : tail.length + 10 ≤ 1021)
    (hdoSub : doSub ≠ ⟨0⟩)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hcolumns : resultPtr.lt (⟨32⟩ + (bytesAgain + resultBase)) ≠ ⟨0⟩)
    (hcontinue : ∀ j, j < n →
      (subtractionAdvance (subtractionIterate j
        (finalSubtractionInitialState
          (finalCopyMemory mem source resultPtr bytes)
          (finalCopyAw aw source resultPtr bytes) resultPtr rightPtr))).leftPtr.lt
          (⟨32⟩ + (bytesAgain + resultBase)) ≠ ⟨0⟩)
    (hexit :
      (subtractionAdvance (subtractionIterate n
        (finalSubtractionInitialState
          (finalCopyMemory mem source resultPtr bytes)
          (finalCopyAw aw source resultPtr bytes) resultPtr rightPtr))).leftPtr.lt
          (⟨32⟩ + (bytesAgain + resultBase)) = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tOff :: nOff :: source :: bytes :: doSub :: rightPtr :: resultPtr ::
        resultBase :: returnPc :: bytesAgain :: tail)
      mem aw rdata acc k C) :
    let initial := finalSubtractionInitialState
      (finalCopyMemory mem source resultPtr bytes)
      (finalCopyAw aw source resultPtr bytes) resultPtr rightPtr
    let final := subtractionAdvance (subtractionIterate n initial)
    RDx runtimeBytecode ee g s0 returnPc
      (bytesAgain :: tail) final.memory final.activeWords rdata acc
      (k + 28 + 35 * (n + 1))
      (C + finalCopyGas aw source resultPtr bytes + 76 +
        finalSubtractionThroughExitGas n initial) := by
  let initial := finalSubtractionInitialState
    (finalCopyMemory mem source resultPtr bytes)
    (finalCopyAw aw source resultPtr bytes) resultPtr rightPtr
  let stop := ⟨32⟩ + (bytesAgain + resultBase)
  have rd4202 := finalCopyToSubtraction hdepth hdoSub hcolumns h
  have rdInitial : RDx runtimeBytecode ee g s0 ⟨4202⟩
      (subtractionLoopStack initial stop (returnPc :: bytesAgain :: tail))
      initial.memory initial.activeWords rdata acc (k + 23)
      (C + finalCopyGas aw source resultPtr bytes + 60) := by
    simpa [initial, stop, finalSubtractionInitialState, subtractionLoopStack] using rd4202
  have rd4197 := finalSubtractionThroughExit initial
    (by simp only [List.length_cons]; omega) hcontinue hexit rdInitial
  have rd4201 := GeneratedTraces.trace_4197_body
    (by simp only [List.length_cons]; omega) rd4197
  have rdReturn := rd4201.jump (by native_decide) hreturn
    (by simp only [List.length_cons]; omega)
  have normalized := rdReturn.withIndices
    (k' := k + 28 + 35 * (n + 1))
    (C' := C + finalCopyGas aw source resultPtr bytes + 76 +
      finalSubtractionThroughExitGas n initial)
    (by ring) (by ring)
  simpa [initial, stop, subtractionLoopStack,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

end Modexp.MultiLimbMontgomeryFinalize
