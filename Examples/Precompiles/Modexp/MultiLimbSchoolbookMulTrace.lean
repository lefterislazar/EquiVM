import Examples.Precompiles.Modexp.MultiLimbMultiplicationTraceBridge
import Examples.Precompiles.Modexp.MultiLimbDivisionTrace

/-!
# Standalone schoolbook-multiplication trace

`LimbMath.schoolbookMul` has a second generated multiplication loop, distinct from the CIOS
column at PC 4440. This module gives its PC 5117 inner body a compact transition. The body reads
`b[j]` and `result[i+j]`, performs the same full-width product-plus-carry step as the pure model,
stores the low word, and returns to the inner guard at PC 5083/5090 with exact gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookMulTrace

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def elementPtr (array index : UInt256) : UInt256 :=
  index.shiftLeft ⟨5⟩ + array + ⟨32⟩

def afterLoad (aw ptr : UInt256) : UInt256 :=
  readWords1 aw ptr

def operands (mem : ByteArray) (aw bPtr resultPtr i j carry : UInt256) :
    UInt256 × UInt256 × UInt256 :=
  let bAddress := elementPtr bPtr j
  let resultAddress := elementPtr resultPtr (i + j)
  let b := readWord mem aw bAddress
  let prior := readWord mem (afterLoad aw bAddress) resultAddress
  (b, prior, carry)

def step (mem : ByteArray) (aw a bPtr resultPtr i j carry : UInt256) :
    UInt256 × UInt256 :=
  let input := operands mem aw bPtr resultPtr i j carry
  Modexp.evmSchoolbookStep a input.1 input.2.1 input.2.2

def nextMemory (mem : ByteArray) (aw a bPtr resultPtr i j carry : UInt256) : ByteArray :=
  let output := step mem aw a bPtr resultPtr i j carry
  output.1.toByteArray.write 0 mem (elementPtr resultPtr (i + j)).toNat 32

def nextWords (aw bPtr resultPtr i j : UInt256) : UInt256 :=
  let bWords := afterLoad aw (elementPtr bPtr j)
  let resultWords := afterLoad bWords (elementPtr resultPtr (i + j))
  afterLoad resultWords (elementPtr resultPtr (i + j))

def bodyGas (aw bPtr resultPtr i j : UInt256) : Nat :=
  let bWords := afterLoad aw (elementPtr bPtr j)
  let resultWords := afterLoad bWords (elementPtr resultPtr (i + j))
  let storedWords := afterLoad resultWords (elementPtr resultPtr (i + j))
  208 + (Cₘ bWords - Cₘ aw) + (Cₘ resultWords - Cₘ bWords) +
    (Cₘ storedWords - Cₘ resultWords)

/-- One exact standalone schoolbook inner-body execution, stopping on the generated next-`j`
guard before its `JUMPI`. -/
theorem bodyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {a j carry i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5117⟩
      (a :: j :: carry :: i :: aPtr :: bLen :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem aw rdata acc k C) :
    let output := step mem aw a bPtr resultPtr i j carry
    let nextJ := j + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨5090⟩
      (⟨5117⟩ :: nextJ.lt bLen :: a :: nextJ :: output.2 :: i :: aPtr :: bLen ::
        aLen :: bPtr :: ret :: resultPtr :: tail)
      (nextMemory mem aw a bPtr resultPtr i j carry)
      (nextWords aw bPtr resultPtr i j) rdata acc
      (k + 67) (C + bodyGas aw bPtr resultPtr i j) := by
  have rd := GeneratedTraces.trace_5117_body hdepth h
  simpa [step, operands, nextMemory, nextWords, bodyGas, elementPtr, afterLoad,
    readWord, readWords1, Modexp.evmSchoolbookStep, Modexp.evmMulHigh,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, u256_add_comm] using rd

/-- The exact stored low word and propagated carry satisfy the unbounded radix equation for the
two words loaded by `bodyExact`. -/
theorem stepRecompose
    (mem : ByteArray) (aw a bPtr resultPtr i j carry : UInt256) :
    let input := operands mem aw bPtr resultPtr i j carry
    let output := step mem aw a bPtr resultPtr i j carry
    output.1.toNat + UInt256.size * output.2.toNat =
      a.toNat * input.1.toNat + input.2.1.toNat + input.2.2.toNat := by
  dsimp only [step, operands]
  exact Modexp.evmSchoolbookStep_recompose _ _ _ _

structure InnerState where
  j : UInt256
  carry : UInt256
  memory : ByteArray
  activeWords : UInt256

def advance (a bPtr resultPtr i : UInt256) (state : InnerState) : InnerState where
  j := state.j + ⟨1⟩
  carry := (step state.memory state.activeWords a bPtr resultPtr i state.j state.carry).2
  memory := nextMemory state.memory state.activeWords a bPtr resultPtr i state.j state.carry
  activeWords := nextWords state.activeWords bPtr resultPtr i state.j

def iterate (a bPtr resultPtr i : UInt256) : Nat → InnerState → InnerState
  | 0, state => state
  | n + 1, state => iterate a bPtr resultPtr i n (advance a bPtr resultPtr i state)

def iterationsGas (a bPtr resultPtr i : UInt256) : Nat → InnerState → Nat
  | 0, _ => 0
  | n + 1, state => bodyGas state.activeWords bPtr resultPtr i state.j + 10 +
      iterationsGas a bPtr resultPtr i n (advance a bPtr resultPtr i state)

def loopStack (state : InnerState) (a i aPtr bLen aLen bPtr ret resultPtr : UInt256)
    (tail : List UInt256) : List UInt256 :=
  a :: state.j :: state.carry :: i :: aPtr :: bLen :: aLen :: bPtr :: ret ::
    resultPtr :: tail

@[simp] theorem iterate_advance (a bPtr resultPtr i : UInt256)
    (n : Nat) (state : InnerState) :
    iterate a bPtr resultPtr i n (advance a bPtr resultPtr i state) =
      iterate a bPtr resultPtr i (n + 1) state := by
  rfl

/-- Execute any number of continuing standalone inner columns. Each selected body includes the
67-instruction arithmetic trace and its 10-gas taken guard. -/
theorem iterationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (state : InnerState)
    (hdepth : tail.length + 10 ≤ 1016)
    (hcontinue : ∀ q, q < n →
      (advance a bPtr resultPtr i (iterate a bPtr resultPtr i q state)).j.lt bLen ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5117⟩
      (loopStack state a i aPtr bLen aLen bPtr ret resultPtr tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5117⟩
      (loopStack (iterate a bPtr resultPtr i n state)
        a i aPtr bLen aLen bPtr ret resultPtr tail)
      (iterate a bPtr resultPtr i n state).memory
      (iterate a bPtr resultPtr i n state).activeWords rdata acc
      (k + 68 * n) (C + iterationsGas a bPtr resultPtr i n state) := by
  induction n generalizing state k C with
  | zero => simpa [iterate, iterationsGas]
  | succ n ih =>
      have rd5090 := bodyExact hdepth h
      have rdNext := rd5090.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ q, q < n →
          (advance a bPtr resultPtr i
            (iterate a bPtr resultPtr i q (advance a bPtr resultPtr i state))).j.lt bLen ≠
            ⟨0⟩ := by
        intro q hq
        simpa [iterate_advance] using hcontinue (q + 1) (by omega)
      have rdRest := ih (state := advance a bPtr resultPtr i state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := k + 68 * (n + 1)) (by omega) rfl
      simpa [loopStack, iterate, advance, iterationsGas, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.mul_add] using normalized

def throughExitGas (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) : Nat :=
  iterationsGas a bPtr resultPtr i n state +
    bodyGas (iterate a bPtr resultPtr i n state).activeWords bPtr resultPtr i
      (iterate a bPtr resultPtr i n state).j + 10

/-- Execute the continuing columns and the final column whose next-`j` guard exits to PC 5091. -/
theorem throughExitExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n : Nat} {tail : List UInt256}
    {a i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (state : InnerState)
    (hdepth : tail.length + 10 ≤ 1016)
    (hcontinue : ∀ q, q < n →
      (advance a bPtr resultPtr i (iterate a bPtr resultPtr i q state)).j.lt bLen ≠ ⟨0⟩)
    (hexit :
      (advance a bPtr resultPtr i (iterate a bPtr resultPtr i n state)).j.lt bLen = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5117⟩
      (loopStack state a i aPtr bLen aLen bPtr ret resultPtr tail)
      state.memory state.activeWords rdata acc k C) :
    let final := advance a bPtr resultPtr i (iterate a bPtr resultPtr i n state)
    RDx runtimeBytecode ee g s0 ⟨5091⟩
      (loopStack final a i aPtr bLen aLen bPtr ret resultPtr tail)
      final.memory final.activeWords rdata acc
      (k + 68 * (n + 1)) (C + throughExitGas a bPtr resultPtr i n state) := by
  have rdIterations := iterationsExact state hdepth hcontinue h
  have rd5090 := bodyExact hdepth rdIterations
  have rd5091 := rd5090.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rd5091.withIndices (k' := k + 68 * (n + 1)) (by omega) rfl
  simpa [loopStack, advance, throughExitGas, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.mul_add] using normalized

def carryPtr (resultPtr i bLen : UInt256) : UInt256 :=
  elementPtr resultPtr (i + bLen)

def carryMemory (mem : ByteArray) (aw resultPtr i bLen carry : UInt256) : ByteArray :=
  let ptr := carryPtr resultPtr i bLen
  let prior := readWord mem aw ptr
  (prior + carry).toByteArray.write 0 mem ptr.toNat 32

def carryWords (aw resultPtr i bLen : UInt256) : UInt256 :=
  let ptr := carryPtr resultPtr i bLen
  afterLoad (afterLoad aw ptr) ptr

def carryGas (aw resultPtr i bLen : UInt256) : Nat :=
  let ptr := carryPtr resultPtr i bLen
  let loaded := afterLoad aw ptr
  let stored := afterLoad loaded ptr
  99 + (Cₘ loaded - Cₘ aw) + (Cₘ stored - Cₘ loaded)

/-- Store the final row carry and reach the next outer-loop guard at PC 5046. -/
theorem carryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {a j carry i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (hdepth : tail.length + 10 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨5091⟩
      (a :: j :: carry :: i :: aPtr :: bLen :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem aw rdata acc k C) :
    let nextI := i + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨5046⟩
      (⟨5053⟩ :: nextI.lt aLen :: nextI :: aPtr :: bLen :: aLen :: bPtr :: ret ::
        resultPtr :: tail)
      (carryMemory mem aw resultPtr i bLen carry) (carryWords aw resultPtr i bLen)
      rdata acc (k + 32) (C + carryGas aw resultPtr i bLen) := by
  have rd := GeneratedTraces.trace_5091_body hdepth h
  simpa [carryPtr, carryMemory, carryWords, carryGas, elementPtr, afterLoad,
    readWord, readWords1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    u256_add_comm] using rd

def sourcePtr (aPtr i : UInt256) : UInt256 :=
  elementPtr aPtr i

def sourceWord (mem : ByteArray) (aw aPtr i : UInt256) : UInt256 :=
  readWord mem aw (sourcePtr aPtr i)

def sourceWords (aw aPtr i : UInt256) : UInt256 :=
  afterLoad aw (sourcePtr aPtr i)

def sourceGas (aw aPtr i : UInt256) : Nat :=
  31 + (Cₘ (sourceWords aw aPtr i) - Cₘ aw)

/-- Load one outer multiplier word and stop at its zero/nonzero branch. -/
theorem sourceExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨5053⟩
      (i :: aPtr :: bLen :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem aw rdata acc k C) :
    let a := sourceWord mem aw aPtr i
    RDx runtimeBytecode ee g s0 ⟨5068⟩
      (⟨5078⟩ :: a :: a :: i :: aPtr :: bLen :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem (sourceWords aw aPtr i) rdata acc (k + 11) (C + sourceGas aw aPtr i) := by
  have rd := GeneratedTraces.trace_5053_body
    (by simp only [List.length_cons]; omega) h
  simpa [sourceWord, sourceWords, sourceGas, sourcePtr, elementPtr, afterLoad,
    readWord, readWords1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    u256_add_comm] using rd

/-- A zero multiplier limb skips the inner loop and reaches the next outer guard exactly. -/
theorem zeroRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (hzero : sourceWord mem aw aPtr i = ⟨0⟩)
    (hdepth : tail.length + 7 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨5053⟩
      (i :: aPtr :: bLen :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem aw rdata acc k C) :
    let nextI := i + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨5046⟩
      (⟨5053⟩ :: nextI.lt aLen :: nextI :: aPtr :: bLen :: aLen :: bPtr :: ret ::
        resultPtr :: tail)
      mem (sourceWords aw aPtr i) rdata acc (k + 23) (C + sourceGas aw aPtr i + 43) := by
  have rd5068 := sourceExact hdepth h
  have rd5069 := rd5068.jumpiNT (by native_decide) (by simpa [hzero])
    (by simp only [List.length_cons]; omega)
  have rd5046 := GeneratedTraces.trace_5069_body
    (by simp only [List.length_cons]; omega) rd5069
  have normalized := rd5046.withIndices (k' := k + 23) (by omega)
    (C' := C + sourceGas aw aPtr i + 43) (by omega)
  simpa [u256_add_comm] using normalized

/-- A nonzero multiplier limb initializes `j = 0`, `carry = 0` and enters PC 5117 when `bLen`
is positive. -/
theorem nonzeroRowEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {i aPtr bLen aLen bPtr ret resultPtr : UInt256}
    (hnonzero : sourceWord mem aw aPtr i ≠ ⟨0⟩)
    (hbLen : ⟨0⟩ < bLen)
    (hdepth : tail.length + 7 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5053⟩
      (i :: aPtr :: bLen :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem aw rdata acc k C) :
    let a := sourceWord mem aw aPtr i
    let state : InnerState := {
      j := ⟨0⟩
      carry := ⟨0⟩
      memory := mem
      activeWords := sourceWords aw aPtr i }
    RDx runtimeBytecode ee g s0 ⟨5117⟩
      (loopStack state a i aPtr bLen aLen bPtr ret resultPtr tail)
      state.memory state.activeWords rdata acc (k + 23) (C + sourceGas aw aPtr i + 44) := by
  have rd5068 := sourceExact (by omega) h
  have rd5078 := rd5068.jumpiT (by native_decide) hnonzero
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd5090 := GeneratedTraces.trace_5078_body
    (by simp only [List.length_cons]; omega) rd5078
  have hbGuard : (⟨0⟩ : UInt256).lt bLen ≠ ⟨0⟩ := by
    rw [ult_one hbLen]
    decide
  have rd5117 := rd5090.jumpiT (by native_decide) hbGuard
    (by native_decide) (by simp only [List.length_cons]; omega)
  have normalized := rd5117.withIndices (k' := k + 23) (by omega)
    (C' := C + sourceGas aw aPtr i + 44) (by omega)
  simpa [loopStack] using normalized

theorem advance_j_toNat
    (a bPtr resultPtr i : UInt256) (state : InnerState)
    (hbound : state.j.toNat + 1 < UInt256.size) :
    (advance a bPtr resultPtr i state).j.toNat = state.j.toNat + 1 := by
  simp only [advance]
  rw [uadd_toNat, show (⟨1⟩ : UInt256).toNat = 1 by decide,
    Nat.mod_eq_of_lt hbound]

theorem iterate_j_toNat
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState)
    (hbound : state.j.toNat + n < UInt256.size) :
    (iterate a bPtr resultPtr i n state).j.toNat = state.j.toNat + n := by
  induction n generalizing state with
  | zero => simp [iterate]
  | succ n ih =>
      rw [show iterate a bPtr resultPtr i (n + 1) state =
        iterate a bPtr resultPtr i n (advance a bPtr resultPtr i state) by rfl]
      have hstep := advance_j_toNat a bPtr resultPtr i state (by omega)
      rw [ih]
      · omega
      · rw [hstep]
        omega

theorem advance_iterate
    (a bPtr resultPtr i : UInt256) (n : Nat) (state : InnerState) :
    advance a bPtr resultPtr i (iterate a bPtr resultPtr i n state) =
      iterate a bPtr resultPtr i (n + 1) state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      change advance a bPtr resultPtr i
          (iterate a bPtr resultPtr i n (advance a bPtr resultPtr i state)) =
        iterate a bPtr resultPtr i (n + 1) (advance a bPtr resultPtr i state)
      exact ih (advance a bPtr resultPtr i state)

def initialInnerState
    (mem : ByteArray) (aw aPtr i : UInt256) : InnerState where
  j := ⟨0⟩
  carry := ⟨0⟩
  memory := mem
  activeWords := sourceWords aw aPtr i

def completedInnerState
    (mem : ByteArray) (aw a aPtr bPtr resultPtr i : UInt256) (bCount : Nat) : InnerState :=
  iterate a bPtr resultPtr i bCount (initialInnerState mem aw aPtr i)

def nonzeroRowMemory
    (mem : ByteArray) (aw aPtr bPtr resultPtr i : UInt256) (bCount : Nat) : ByteArray :=
  let a := sourceWord mem aw aPtr i
  let final := completedInnerState mem aw a aPtr bPtr resultPtr i bCount
  carryMemory final.memory final.activeWords resultPtr i (UInt256.ofNat bCount) final.carry

def nonzeroRowWords
    (mem : ByteArray) (aw aPtr bPtr resultPtr i : UInt256) (bCount : Nat) : UInt256 :=
  let a := sourceWord mem aw aPtr i
  let final := completedInnerState mem aw a aPtr bPtr resultPtr i bCount
  carryWords final.activeWords resultPtr i (UInt256.ofNat bCount)

def nonzeroRowGas
    (mem : ByteArray) (aw aPtr bPtr resultPtr i : UInt256) (bCount : Nat) : Nat :=
  let a := sourceWord mem aw aPtr i
  let initial := initialInnerState mem aw aPtr i
  let final := completedInnerState mem aw a aPtr bPtr resultPtr i bCount
  sourceGas aw aPtr i + 44 +
    throughExitGas a bPtr resultPtr i (bCount - 1) initial +
    carryGas final.activeWords resultPtr i (UInt256.ofNat bCount)

/-- Execute one complete nonzero schoolbook row of arbitrary positive width, including all inner
columns and the final carry store. The theorem stops at the outer guard so the caller can select
either the next row or the function return. -/
theorem nonzeroRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C bCount : Nat} {tail : List UInt256}
    {i aPtr aLen bPtr ret resultPtr : UInt256}
    (hbPos : 0 < bCount) (hbWord : bCount < UInt256.size)
    (hnonzero : sourceWord mem aw aPtr i ≠ ⟨0⟩)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5053⟩
      (i :: aPtr :: UInt256.ofNat bCount :: aLen :: bPtr :: ret :: resultPtr :: tail)
      mem aw rdata acc k C) :
    let nextI := i + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨5046⟩
      (⟨5053⟩ :: nextI.lt aLen :: nextI :: aPtr :: UInt256.ofNat bCount :: aLen ::
        bPtr :: ret :: resultPtr :: tail)
      (nonzeroRowMemory mem aw aPtr bPtr resultPtr i bCount)
      (nonzeroRowWords mem aw aPtr bPtr resultPtr i bCount)
      rdata acc (k + 55 + 68 * bCount)
      (C + nonzeroRowGas mem aw aPtr bPtr resultPtr i bCount) := by
  let a := sourceWord mem aw aPtr i
  let initial := initialInnerState mem aw aPtr i
  have hbLen : (⟨0⟩ : UInt256) < UInt256.ofNat bCount := by
    change (⟨0⟩ : UInt256).toNat < (UInt256.ofNat bCount).toNat
    rw [UInt256.toNat_ofNat_of_lt hbWord]
    norm_num
    exact hbPos
  have rd5117 := nonzeroRowEntryExact hnonzero hbLen (by omega) h
  have hj (q : Nat) (hq : q < bCount) :
      (iterate a bPtr resultPtr i q initial).j.toNat = q := by
    have hbound : initial.j.toNat + q < UInt256.size := by
      dsimp only [initial, initialInnerState]
      rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
      omega
    simpa [initial, initialInnerState] using
      iterate_j_toNat a bPtr resultPtr i q initial hbound
  have hcontinue : ∀ q, q < bCount - 1 →
      (advance a bPtr resultPtr i (iterate a bPtr resultPtr i q initial)).j.lt
        (UInt256.ofNat bCount) ≠ ⟨0⟩ := by
    intro q hq
    have hnext :
        (advance a bPtr resultPtr i (iterate a bPtr resultPtr i q initial)).j.toNat =
          q + 1 := by
      rw [advance_j_toNat]
      · rw [hj q (by omega)]
      · rw [hj q (by omega)]
        omega
    have hlt :
        (advance a bPtr resultPtr i (iterate a bPtr resultPtr i q initial)).j.toNat <
          (UInt256.ofNat bCount).toNat := by
      rw [hnext, UInt256.toNat_ofNat_of_lt hbWord]
      omega
    rw [ult_one hlt]
    decide
  have hexit :
      (advance a bPtr resultPtr i
        (iterate a bPtr resultPtr i (bCount - 1) initial)).j.lt
          (UInt256.ofNat bCount) = ⟨0⟩ := by
    have hbefore :
        (iterate a bPtr resultPtr i (bCount - 1) initial).j.toNat = bCount - 1 :=
      hj (bCount - 1) (by omega)
    have hnext :
        (advance a bPtr resultPtr i
          (iterate a bPtr resultPtr i (bCount - 1) initial)).j.toNat = bCount := by
      rw [advance_j_toNat]
      · omega
      · rw [hbefore]
        omega
    apply ult_zero
    rw [hnext, UInt256.toNat_ofNat_of_lt hbWord]
  have rd5091 := throughExitExact initial hdepth hcontinue hexit
    (by simpa [a, initial, initialInnerState, loopStack] using rd5117)
  let final := completedInnerState mem aw a aPtr bPtr resultPtr i bCount
  have hfinal :
      advance a bPtr resultPtr i (iterate a bPtr resultPtr i (bCount - 1) initial) =
        final := by
    rw [advance_iterate]
    have hcount : bCount - 1 + 1 = bCount := by omega
    simpa [final, completedInnerState, initial] using congrArg
      (fun n => iterate a bPtr resultPtr i n initial) hcount
  rw [hfinal] at rd5091
  have rd5046 := carryExact (by omega) rd5091
  have normalized := rd5046.withIndices (k' := k + 55 + 68 * bCount) (by omega)
    (C' := C + nonzeroRowGas mem aw aPtr bPtr resultPtr i bCount) (by
      unfold nonzeroRowGas
      dsimp only [a, initial, final]
      omega)
  simpa [nonzeroRowMemory, nonzeroRowWords, a, final, completedInnerState] using normalized

structure OuterState where
  i : UInt256
  memory : ByteArray
  activeWords : UInt256

def rowAdvance
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState) : OuterState :=
  if sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩ then
    { i := state.i + ⟨1⟩
      memory := state.memory
      activeWords := sourceWords state.activeWords aPtr state.i }
  else
    { i := state.i + ⟨1⟩
      memory := nonzeroRowMemory state.memory state.activeWords aPtr bPtr resultPtr
        state.i bCount
      activeWords := nonzeroRowWords state.memory state.activeWords aPtr bPtr resultPtr
        state.i bCount }

def rowSteps
    (aPtr : UInt256) (bCount : Nat) (state : OuterState) : Nat :=
  if sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩ then 23
  else 55 + 68 * bCount

def rowGas
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState) : Nat :=
  if sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩ then
    sourceGas state.activeWords aPtr state.i + 43
  else
    nonzeroRowGas state.memory state.activeWords aPtr bPtr resultPtr state.i bCount

def outerGuardStack
    (state : OuterState) (aPtr : UInt256) (bCount : Nat) (aLen bPtr ret resultPtr : UInt256)
    (tail : List UInt256) : List UInt256 :=
  ⟨5053⟩ :: state.i.lt aLen :: state.i :: aPtr :: UInt256.ofNat bCount :: aLen ::
    bPtr :: ret :: resultPtr :: tail

/-- Select and execute one complete standalone multiplication row from the actual source word.
The result retains the bytecode's next outer-loop guard and exact branch-sensitive cost. -/
theorem rowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C bCount : Nat} {tail : List UInt256}
    {aPtr aLen bPtr ret resultPtr : UInt256}
    (state : OuterState)
    (hbPos : 0 < bCount) (hbWord : bCount < UInt256.size)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨5053⟩
      (state.i :: aPtr :: UInt256.ofNat bCount :: aLen :: bPtr :: ret :: resultPtr :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5046⟩
      (outerGuardStack (rowAdvance aPtr bPtr resultPtr bCount state)
        aPtr bCount aLen bPtr ret resultPtr tail)
      (rowAdvance aPtr bPtr resultPtr bCount state).memory
      (rowAdvance aPtr bPtr resultPtr bCount state).activeWords rdata acc
      (k + rowSteps aPtr bCount state)
      (C + rowGas aPtr bPtr resultPtr bCount state) := by
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · have rd := zeroRowExact hzero (by omega) h
    simpa [outerGuardStack, rowAdvance, rowSteps, rowGas, hzero] using rd
  · have rd := nonzeroRowExact hbPos hbWord hzero hdepth h
    simpa [outerGuardStack, rowAdvance, rowSteps, rowGas, hzero, Nat.add_assoc] using rd

end Modexp.MultiLimbSchoolbookMulTrace
