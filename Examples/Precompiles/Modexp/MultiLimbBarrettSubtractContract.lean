import Examples.Precompiles.Modexp.MultiLimbBarrettTruncatedMulContract
import Examples.Precompiles.Modexp.MultiLimbSubtractionModel

/-!
# Barrett subtraction execution contract

This module continues `_barrettMulMod` at PC 6685, allocates the final `k`-limb result array,
and executes the in-place `product-r2` subtraction setup.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettSubtract

open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

/-- Remove the completed truncated-multiply locals and call the concrete allocator for the
`k`-limb result. -/
theorem resultAllocationEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {i q3 q3Cap rLen n kWord r2 returnPc product : UInt256}
    (hdepth : tail.length + 9 ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨6685⟩
      (i :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (kWord :: ⟨6696⟩ :: rLen :: n :: kWord :: r2 :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 7) (gasUsed + 23) := by
  have rd := evm_run h with [
    pop,
    pop,
    pop,
    pushCanonical 2 .PUSH2 ⟨6696⟩ (by decide),
    dup4,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)
  ]
  exact rd.withIndices (by omega) (by omega)

def resultAllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize kWords)) fp kWords

def resultAllocatedWords (aw : UInt256) (fp kWords : Nat) : UInt256 :=
  newWordArrayWords aw fp kWords

/-- Allocate the deployed zeroed result array and return to PC 6696 with all Barrett locals. -/
theorem resultAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {i q3 q3Cap rLen n r2 returnPc product : UInt256}
    (hkBound : kWords ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kWords < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6685⟩
      (i :: q3 :: q3Cap :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6696⟩
      (UInt256.ofNat fp :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: product :: tail)
      (resultAllocatedMemory mem fp kWords) (resultAllocatedWords aw fp kWords)
      rdata acc (steps + 85) (gasUsed + 23 + newWordArrayGas aw fp kWords) := by
  have rd1487 := resultAllocationEntryExact (by omega) h
  have rd6696 := newWordArrayExact68 hkBound hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd6696.withIndices (k' := steps + 85) (by omega)
    (C' := gasUsed + 23 + newWordArrayGas aw fp kWords) (by omega)
  simpa [resultAllocatedMemory, resultAllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

/-- Initialize `borrow=0` and `i=0`, prove `0<rLen=k+1`, and enter the subtraction body. -/
theorem subtractionEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {result n r2 returnPc product : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 7 ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨6696⟩
      (result :: UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords ::
        r2 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6940⟩
      (⟨0⟩ :: ⟨0⟩ :: product :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc (steps + 10) (gasUsed + 31) := by
  have hcondition : (⟨0⟩ : UInt256).lt
      (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    rw [ult_one (by
      change (⟨0⟩ : UInt256).toNat < (UInt256.ofNat (kWords + 1)).toNat
      rw [UInt256.toNat_ofNat_of_lt hkWord]
      norm_num)]
    native_decide
  have rd6940 := GeneratedTraces.trace_6696_taken
    hdepth h (by native_decide)
    hcondition (by native_decide)
  exact rd6940.withIndices (by omega) (by omega)

def subtractionPtr (array index : UInt256) : UInt256 := elementPtr array index

def subtractionOperands
    (mem : ByteArray) (aw product r2 i : UInt256) : UInt256 × UInt256 :=
  let productPtr := subtractionPtr product i
  let r2Ptr := subtractionPtr r2 i
  let left := readWord mem aw productPtr
  let right := readWord mem (afterLoad aw productPtr) r2Ptr
  (left, right)

def subtractionStep
    (mem : ByteArray) (aw product r2 i borrow : UInt256) : UInt256 × UInt256 :=
  let input := subtractionOperands mem aw product r2 i
  Modexp.evmSubBorrow input.1 input.2 borrow

def subtractionMemory
    (mem : ByteArray) (aw product r2 i borrow : UInt256) : ByteArray :=
  let output := subtractionStep mem aw product r2 i borrow
  output.1.toByteArray.write 0 mem (subtractionPtr r2 i).toNat 32

def subtractionWords (aw product r2 i : UInt256) : UInt256 :=
  let productWords := afterLoad aw (subtractionPtr product i)
  let r2Words := afterLoad productWords (subtractionPtr r2 i)
  afterLoad r2Words (subtractionPtr r2 i)

def subtractionBodyGas (aw product r2 i : UInt256) : Nat :=
  let productWords := afterLoad aw (subtractionPtr product i)
  let r2Words := afterLoad productWords (subtractionPtr r2 i)
  let storedWords := afterLoad r2Words (subtractionPtr r2 i)
  130 + (Cₘ productWords - Cₘ aw) + (Cₘ r2Words - Cₘ productWords) +
    (Cₘ storedWords - Cₘ r2Words)

/-- Execute one deployed `product[i]-r2[i]-borrow` column and stop at its next-index guard. -/
theorem subtractionBodyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {i borrow product rLen n kWord r2 returnPc result : UInt256}
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6940⟩
      (i :: borrow :: product :: rLen :: n :: kWord :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let output := subtractionStep mem aw product r2 i borrow
    let nextI := i + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨6707⟩
      (⟨6940⟩ :: nextI.lt rLen :: nextI :: output.2 :: product :: rLen :: n ::
        kWord :: r2 :: returnPc :: result :: tail)
      (subtractionMemory mem aw product r2 i borrow)
      (subtractionWords aw product r2 i) rdata acc
      (steps + 43) (gasUsed + subtractionBodyGas aw product r2 i) := by
  have rd := GeneratedTraces.trace_6940_body
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h
  rw [u256_add_comm product (i.shiftLeft ⟨5⟩),
    u256_add_comm r2 (i.shiftLeft ⟨5⟩)] at rd
  have normalized := rd.withIndices (k' := steps + 43) (by omega)
    (C' := gasUsed + subtractionBodyGas aw product r2 i) (by
      simp only [subtractionBodyGas, subtractionPtr, elementPtr, afterLoad, readWords1]
      omega)
  exact normalized

structure BarrettSubtractionState where
  i : Nat
  borrow : UInt256
  memory : ByteArray
  activeWords : UInt256

def subtractionAdvance (product r2 : UInt256) (state : BarrettSubtractionState) :
    BarrettSubtractionState :=
  let output := subtractionStep state.memory state.activeWords product r2
    (UInt256.ofNat state.i) state.borrow
  { i := state.i + 1
    borrow := output.2
    memory := subtractionMemory state.memory state.activeWords product r2
      (UInt256.ofNat state.i) state.borrow
    activeWords := subtractionWords state.activeWords product r2 (UInt256.ofNat state.i) }

def subtractionIterate (product r2 : UInt256) :
    Nat → BarrettSubtractionState → BarrettSubtractionState
  | 0, state => state
  | count + 1, state =>
      subtractionIterate product r2 count (subtractionAdvance product r2 state)

def subtractionIterationsGas (product r2 : UInt256) :
    Nat → BarrettSubtractionState → Nat
  | 0, _ => 0
  | count + 1, state =>
      subtractionBodyGas state.activeWords product r2 (UInt256.ofNat state.i) + 10 +
        subtractionIterationsGas product r2 count (subtractionAdvance product r2 state)

def subtractionLoopStack (state : BarrettSubtractionState)
    (product rLen n kWord r2 returnPc result : UInt256) (tail : List UInt256) :
    List UInt256 :=
  UInt256.ofNat state.i :: state.borrow :: product :: rLen :: n :: kWord :: r2 ::
    returnPc :: result :: tail

@[simp] theorem subtractionIterate_advance
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    subtractionIterate product r2 count (subtractionAdvance product r2 state) =
      subtractionIterate product r2 (count + 1) state := by
  rfl

theorem subtractionAdvance_iterate
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    subtractionAdvance product r2 (subtractionIterate product r2 count state) =
      subtractionIterate product r2 (count + 1) state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      change subtractionAdvance product r2
          (subtractionIterate product r2 count (subtractionAdvance product r2 state)) =
        subtractionIterate product r2 (count + 2) state
      rw [ih]
      rfl

theorem subtractionAdvance_i (product r2 : UInt256) (state : BarrettSubtractionState) :
    (subtractionAdvance product r2 state).i = state.i + 1 := by
  rfl

theorem subtractionIterate_i
    (product r2 : UInt256) (count : Nat) (state : BarrettSubtractionState) :
    (subtractionIterate product r2 count state).i = state.i + count := by
  induction count generalizing state with
  | zero => simp [subtractionIterate]
  | succ count ih =>
      rw [show subtractionIterate product r2 (count + 1) state =
        subtractionIterate product r2 count (subtractionAdvance product r2 state) by rfl,
        ih, subtractionAdvance_i]
      omega

/-- Execute one column whose incremented index remains below `rLen=k+1`. -/
theorem subtractionContinuingColumnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {product n r2 returnPc result : UInt256}
    (state : BarrettSubtractionState)
    (hi : state.i = iWords) (hiLt : iWords < kWords)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6940⟩
      (subtractionLoopStack state product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let next := subtractionAdvance product r2 state
    RDx runtimeBytecode ee g s0 ⟨6940⟩
      (subtractionLoopStack next product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      next.memory next.activeWords rdata acc (steps + 44)
      (gasUsed + subtractionBodyGas state.activeWords product r2
        (UInt256.ofNat state.i) + 10) := by
  have hiWord : state.i + 1 < UInt256.size := by omega
  have hnext : UInt256.ofNat state.i + ⟨1⟩ = UInt256.ofNat (state.i + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : state.i < UInt256.size),
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mod_eq_of_lt hiWord,
      UInt256.toNat_ofNat_of_lt hiWord]
  have hcondition : (UInt256.ofNat (state.i + 1)).lt
      (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    rw [ult_one (by
      rw [UInt256.toNat_ofNat_of_lt hiWord, UInt256.toNat_ofNat_of_lt hkWord]
      omega)]
    native_decide
  have rd6707 := subtractionBodyExact hdepth
    (by simpa [subtractionLoopStack] using h)
  have rd6940 := rd6707.jumpiT (by native_decide)
    (by simpa only [hnext] using hcondition) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have normalized := rd6940.withIndices (k' := steps + 44) (by omega)
    (C' := gasUsed + subtractionBodyGas state.activeWords product r2
      (UInt256.ofNat state.i) + 10) (by omega)
  simpa [subtractionLoopStack, subtractionAdvance, hnext] using normalized

/-- Execute the final `i=k` column and take the false guard to correction setup at PC 6708. -/
theorem subtractionTerminalColumnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {product n r2 returnPc result : UInt256}
    (state : BarrettSubtractionState)
    (hi : state.i = kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6940⟩
      (subtractionLoopStack state product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let next := subtractionAdvance product r2 state
    RDx runtimeBytecode ee g s0 ⟨6708⟩
      (subtractionLoopStack next product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      next.memory next.activeWords rdata acc (steps + 44)
      (gasUsed + subtractionBodyGas state.activeWords product r2
        (UInt256.ofNat state.i) + 10) := by
  have hiWord : state.i + 1 < UInt256.size := by omega
  have hnext : UInt256.ofNat state.i + ⟨1⟩ = UInt256.ofNat (state.i + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : state.i < UInt256.size),
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mod_eq_of_lt hiWord,
      UInt256.toNat_ofNat_of_lt hiWord]
  have hcondition : (UInt256.ofNat (state.i + 1)).lt
      (UInt256.ofNat (kWords + 1)) = ⟨0⟩ := by
    apply ult_zero
    rw [hi, UInt256.toNat_ofNat_of_lt hkWord]
  have rd6707 := subtractionBodyExact hdepth
    (by simpa [subtractionLoopStack] using h)
  have rd6708 := rd6707.jumpiNT (by native_decide)
    (by simpa only [hnext] using hcondition)
    (by simp only [List.length_cons]; omega)
  have rd6708' := rd6708.withPC (pc' := ⟨6708⟩) (by native_decide)
  have normalized := rd6708'.withIndices (k' := steps + 44) (by omega)
    (C' := gasUsed + subtractionBodyGas state.activeWords product r2
      (UInt256.ofNat state.i) + 10) (by omega)
  simpa [subtractionLoopStack, subtractionAdvance, hnext] using normalized

/-- Execute an arbitrary number of subtraction columns whose incremented indices stay below
`rLen=k+1`. -/
theorem subtractionContinuingIterationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed count kWords : Nat} {tail : List UInt256}
    {product n r2 returnPc result : UInt256}
    (state : BarrettSubtractionState)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (hindices : ∀ q, q < count →
      (subtractionIterate product r2 q state).i < kWords)
    (h : RDx runtimeBytecode ee g s0 ⟨6940⟩
      (subtractionLoopStack state product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let final := subtractionIterate product r2 count state
    RDx runtimeBytecode ee g s0 ⟨6940⟩
      (subtractionLoopStack final product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      final.memory final.activeWords rdata acc (steps + 44 * count)
      (gasUsed + subtractionIterationsGas product r2 count state) := by
  induction count generalizing state steps gasUsed with
  | zero => simpa [subtractionIterate, subtractionIterationsGas]
  | succ count ih =>
      have rdNext := subtractionContinuingColumnExact state rfl
        (hindices 0 (by omega)) hkWord hdepth h
      have hindices' : ∀ q, q < count →
          (subtractionIterate product r2 q
            (subtractionAdvance product r2 state)).i < kWords := by
        intro q hq
        simpa [subtractionIterate_advance] using hindices (q + 1) (by omega)
      have rdRest := ih (state := subtractionAdvance product r2 state) hindices' rdNext
      have normalized := rdRest.withIndices (k' := steps + 44 * (count + 1))
        (by omega)
        (C' := gasUsed + subtractionIterationsGas product r2 (count + 1) state) (by
          simp only [subtractionIterationsGas]
          omega)
      simpa only [subtractionIterate] using normalized

def subtractionInitialState (mem : ByteArray) (aw : UInt256) : BarrettSubtractionState where
  i := 0
  borrow := ⟨0⟩
  memory := mem
  activeWords := aw

def subtractionThroughExitGas
    (product r2 : UInt256) (kWords : Nat) (state : BarrettSubtractionState) : Nat :=
  let beforeFinal := subtractionIterate product r2 kWords state
  subtractionIterationsGas product r2 kWords state +
    subtractionBodyGas beforeFinal.activeWords product r2 (UInt256.ofNat beforeFinal.i) + 10

/-- Execute all `k+1` deployed subtraction columns from `i=0,borrow=0`, including the terminal
false guard, and expose the concrete in-place r2 result at PC 6708. -/
theorem subtractionFromZeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {product n r2 returnPc result : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6940⟩
      (⟨0⟩ :: ⟨0⟩ :: product :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial := subtractionInitialState mem aw
    let final := subtractionIterate product r2 (kWords + 1) initial
    RDx runtimeBytecode ee g s0 ⟨6708⟩
      (subtractionLoopStack final product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      final.memory final.activeWords rdata acc (steps + 44 * (kWords + 1))
      (gasUsed + subtractionThroughExitGas product r2 kWords initial) := by
  let initial := subtractionInitialState mem aw
  have hindex (q : Nat) :
      (subtractionIterate product r2 q initial).i = q := by
    simpa [initial, subtractionInitialState] using
      subtractionIterate_i product r2 q initial
  have hindices : ∀ q, q < kWords →
      (subtractionIterate product r2 q initial).i < kWords := by
    intro q hq
    rw [hindex q]
    exact hq
  have hInitial : RDx runtimeBytecode ee g s0 ⟨6940⟩
      (subtractionLoopStack initial product (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      initial.memory initial.activeWords rdata acc steps gasUsed := by
    simpa [initial, subtractionInitialState, subtractionLoopStack] using h
  have rdBeforeFinal := subtractionContinuingIterationsExact initial hkWord hdepth
    hindices hInitial
  let beforeFinal := subtractionIterate product r2 kWords initial
  have hbeforeFinal : beforeFinal.i = kWords := by
    simpa [beforeFinal] using hindex kWords
  have rdFinal := subtractionTerminalColumnExact beforeFinal hbeforeFinal hkWord hdepth
    (by simpa [beforeFinal] using rdBeforeFinal)
  have hfinal : subtractionAdvance product r2 beforeFinal =
      subtractionIterate product r2 (kWords + 1) initial := by
    simpa [beforeFinal] using subtractionAdvance_iterate product r2 kWords initial
  rw [hfinal] at rdFinal
  have normalized := rdFinal.withIndices (k' := steps + 44 * (kWords + 1))
    (by omega)
    (C' := gasUsed + subtractionThroughExitGas product r2 kWords initial) (by
      unfold subtractionThroughExitGas
      dsimp only [beforeFinal]
      omega)
  simpa [initial] using normalized

def correctionTopPtr (r2 : UInt256) (kWords : Nat) : UInt256 :=
  elementPtr r2 (UInt256.ofNat kWords)

def correctionTopWord
    (mem : ByteArray) (aw r2 : UInt256) (kWords : Nat) : UInt256 :=
  readWord mem aw (correctionTopPtr r2 kWords)

def correctionTopWords (aw r2 : UInt256) (kWords : Nat) : UInt256 :=
  afterLoad aw (correctionTopPtr r2 kWords)

def correctionSetupGas (aw r2 : UInt256) (kWords : Nat) : Nat :=
  71 + (Cₘ (correctionTopWords aw r2 kWords) - Cₘ aw)

/-- Remove the completed subtraction locals, initialize correction iteration zero, execute its
`iter<2` guard, and load the actual extra r2 limb that selects the comparison path. -/
theorem correctionSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {i borrow product n r2 returnPc result : UInt256}
    (hdepth : tail.length + 9 ≤ 1023)
    (h : RDx runtimeBytecode ee g s0 ⟨6708⟩
      (i :: borrow :: product :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let top := correctionTopWord mem aw r2 kWords
    RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: top.isZero :: top.isZero.isZero :: ⟨0⟩ ::
        UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem (correctionTopWords aw r2 kWords) rdata acc
      (steps + 24) (gasUsed + correctionSetupGas aw r2 kWords) := by
  have rd := GeneratedTraces.trace_6708_body
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h
  rw [u256_add_comm r2 ((UInt256.ofNat kWords).shiftLeft ⟨5⟩)] at rd
  have normalized := rd.withIndices (k' := steps + 24) (by omega)
    (C' := gasUsed + correctionSetupGas aw r2 kWords) (by
      simp only [correctionSetupGas, correctionTopWords, correctionTopPtr, elementPtr,
        afterLoad, readWords1]
      omega)
  exact normalized

/-- A nonzero extra r2 limb makes `geq` true immediately and enters the correction subtraction
loop with zero index and borrow. -/
theorem correctionTopNonzeroEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {top n r2 returnPc result : UInt256}
    (htop : top ≠ ⟨0⟩)
    (hdepth : tail.length + 7 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: top.isZero :: top.isZero.isZero :: ⟨0⟩ ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6780⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc (steps + 12) (gasUsed + 49) := by
  have hzero : top.isZero = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne htop
  have hone : top.isZero.isZero = ⟨1⟩ := by rw [hzero]; native_decide
  have hzero2 : top.isZero.isZero.isZero = ⟨0⟩ := by rw [hone]; native_decide
  have rd6757 := h.jumpiNT (by native_decide) hzero
    (by simp only [List.length_cons]; omega)
  have rd6764 := GeneratedTraces.trace_6757_notTaken
    (by simp only [List.length_cons]; omega) rd6757 (by native_decide)
    (by simpa only [hzero2])
  have rd6777 := GeneratedTraces.trace_6764_taken
    (by simp only [List.length_cons]; omega) rd6764 (by native_decide)
    (by rw [hone]; native_decide) (by native_decide)
  have rd6780 := evm_run rd6777 with [
    jumpdest,
    push0,
    push0
  ]
  have normalized := rd6780.withIndices (k' := steps + 12) (by omega)
    (C' := gasUsed + 49) (by omega)
  simpa [hzero, hone] using normalized

def correctionOperands
    (mem : ByteArray) (aw n r2 i : UInt256) : UInt256 × UInt256 :=
  let r2Ptr := elementPtr r2 i
  let nPtr := elementPtr n i
  let left := readWord mem aw r2Ptr
  let right := readWord mem (afterLoad aw r2Ptr) nPtr
  (left, right)

def correctionStep
    (mem : ByteArray) (aw n r2 i borrow : UInt256) : UInt256 × UInt256 :=
  let input := correctionOperands mem aw n r2 i
  Modexp.evmSubBorrow input.1 input.2 borrow

def correctionMemory
    (mem : ByteArray) (aw n r2 i borrow : UInt256) : ByteArray :=
  let output := correctionStep mem aw n r2 i borrow
  output.1.toByteArray.write 0 mem (elementPtr r2 i).toNat 32

def correctionWords (aw n r2 i : UInt256) : UInt256 :=
  let r2Words := afterLoad aw (elementPtr r2 i)
  let nWords := afterLoad r2Words (elementPtr n i)
  afterLoad nWords (elementPtr r2 i)

def correctionBodyGas (aw n r2 i : UInt256) : Nat :=
  let r2Words := afterLoad aw (elementPtr r2 i)
  let nWords := afterLoad r2Words (elementPtr n i)
  let storedWords := afterLoad nWords (elementPtr r2 i)
  189 + (Cₘ r2Words - Cₘ aw) + (Cₘ nWords - Cₘ r2Words) +
    (Cₘ storedWords - Cₘ nWords)

def correctionTerminalStep
    (mem : ByteArray) (aw r2 i borrow : UInt256) : UInt256 × UInt256 :=
  let left := readWord mem aw (elementPtr r2 i)
  Modexp.evmSubBorrow left ⟨0⟩ borrow

def correctionTerminalMemory
    (mem : ByteArray) (aw r2 i borrow : UInt256) : ByteArray :=
  let output := correctionTerminalStep mem aw r2 i borrow
  output.1.toByteArray.write 0 mem (elementPtr r2 i).toNat 32

def correctionTerminalWords (aw r2 i : UInt256) : UInt256 :=
  let loaded := afterLoad aw (elementPtr r2 i)
  afterLoad loaded (elementPtr r2 i)

def correctionTerminalGas (aw r2 i : UInt256) : Nat :=
  let loaded := afterLoad aw (elementPtr r2 i)
  let stored := afterLoad loaded (elementPtr r2 i)
  155 + (Cₘ loaded - Cₘ aw) + (Cₘ stored - Cₘ loaded)

/-- One ordinary correction-subtraction column (`i<k`), including its next true guard. -/
theorem correctionOrdinaryColumnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {borrow iter n r2 returnPc result : UInt256}
    (hiLt : iWords < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6794⟩
      (UInt256.ofNat iWords :: borrow :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let output := correctionStep mem aw n r2 (UInt256.ofNat iWords) borrow
    RDx runtimeBytecode ee g s0 ⟨6794⟩
      (UInt256.ofNat (iWords + 1) :: output.2 :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      (correctionMemory mem aw n r2 (UInt256.ofNat iWords) borrow)
      (correctionWords aw n r2 (UInt256.ofNat iWords)) rdata acc
      (steps + 59) (gasUsed + correctionBodyGas aw n r2 (UInt256.ofNat iWords)) := by
  have hiWord : iWords + 1 < UInt256.size := by omega
  have hbranch : (UInt256.ofNat iWords).lt (UInt256.ofNat kWords) ≠ ⟨0⟩ := by
    rw [ult_one (by
      rw [UInt256.toNat_ofNat_of_lt (by omega : iWords < UInt256.size),
        UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size)]
      exact hiLt)]
    native_decide
  have hnextGuard : (UInt256.ofNat (iWords + 1)).lt
      (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    rw [ult_one (by
      rw [UInt256.toNat_ofNat_of_lt hiWord, UInt256.toNat_ofNat_of_lt hkWord]
      omega)]
    native_decide
  have hnext : UInt256.ofNat iWords + ⟨1⟩ = UInt256.ofNat (iWords + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : iWords < UInt256.size),
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mod_eq_of_lt hiWord,
      UInt256.toNat_ofNat_of_lt hiWord]
  have rd6843 := GeneratedTraces.trace_6794_taken
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hbranch
    (by native_decide)
  have rd6794 := GeneratedTraces.trace_6843_taken
    (by simp only [List.length_cons]; omega) rd6843 (by native_decide)
    (by simpa only [hnext] using hnextGuard) (by native_decide)
  rw [u256_add_comm r2 ((UInt256.ofNat iWords).shiftLeft ⟨5⟩),
    u256_add_comm n ((UInt256.ofNat iWords).shiftLeft ⟨5⟩)] at rd6794
  rw [hnext] at rd6794
  have normalized := rd6794.withIndices (k' := steps + 59) (by omega)
    (C' := gasUsed + correctionBodyGas aw n r2 (UInt256.ofNat iWords)) (by
      simp only [correctionBodyGas, elementPtr, afterLoad, readWords1]
      omega)
  simpa [correctionStep, correctionOperands, correctionMemory, correctionWords,
    elementPtr, afterLoad, readWord, readWords1, Modexp.evmSubBorrow,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

/-- The `i=k` correction column uses a zero right limb and includes the final false guard. -/
theorem correctionTerminalColumnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {borrow iter n r2 returnPc result : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6794⟩
      (UInt256.ofNat kWords :: borrow :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let output := correctionTerminalStep mem aw r2 (UInt256.ofNat kWords) borrow
    RDx runtimeBytecode ee g s0 ⟨6788⟩
      (UInt256.ofNat (kWords + 1) :: output.2 :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      (correctionTerminalMemory mem aw r2 (UInt256.ofNat kWords) borrow)
      (correctionTerminalWords aw r2 (UInt256.ofNat kWords)) rdata acc
      (steps + 48) (gasUsed + correctionTerminalGas aw r2 (UInt256.ofNat kWords)) := by
  have hbranch : (UInt256.ofNat kWords).lt (UInt256.ofNat kWords) = ⟨0⟩ :=
    ult_zero (by omega)
  have hnextGuard : (UInt256.ofNat (kWords + 1)).lt
      (UInt256.ofNat (kWords + 1)) = ⟨0⟩ := ult_zero (by omega)
  have hnext : UInt256.ofNat kWords + ⟨1⟩ = UInt256.ofNat (kWords + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size),
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mod_eq_of_lt hkWord,
      UInt256.toNat_ofNat_of_lt hkWord]
  have rd6822 := GeneratedTraces.trace_6794_notTaken
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hbranch
  have rd6788 := GeneratedTraces.trace_6822_notTaken
    (by simp only [List.length_cons]; omega) rd6822 (by native_decide)
    (by simpa only [hnext] using hnextGuard)
  have rd6788' := rd6788.withPC (pc' := ⟨6788⟩) (by native_decide)
  rw [u256_add_comm r2 ((UInt256.ofNat kWords).shiftLeft ⟨5⟩)] at rd6788'
  rw [hnext] at rd6788'
  have normalized := rd6788'.withIndices (k' := steps + 48) (by omega)
    (C' := gasUsed + correctionTerminalGas aw r2 (UInt256.ofNat kWords)) (by
      simp only [correctionTerminalGas, elementPtr, afterLoad, readWords1]
      omega)
  simpa [correctionTerminalStep, correctionTerminalMemory, correctionTerminalWords,
    elementPtr, afterLoad, readWord, readWords1, Modexp.evmSubBorrow,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

structure CorrectionSubtractionState where
  i : Nat
  borrow : UInt256
  memory : ByteArray
  activeWords : UInt256

def correctionAdvance (n r2 : UInt256) (state : CorrectionSubtractionState) :
    CorrectionSubtractionState :=
  let output := correctionStep state.memory state.activeWords n r2
    (UInt256.ofNat state.i) state.borrow
  { i := state.i + 1
    borrow := output.2
    memory := correctionMemory state.memory state.activeWords n r2
      (UInt256.ofNat state.i) state.borrow
    activeWords := correctionWords state.activeWords n r2 (UInt256.ofNat state.i) }

def correctionIterate (n r2 : UInt256) :
    Nat → CorrectionSubtractionState → CorrectionSubtractionState
  | 0, state => state
  | count + 1, state => correctionIterate n r2 count (correctionAdvance n r2 state)

def correctionIterationsGas (n r2 : UInt256) :
    Nat → CorrectionSubtractionState → Nat
  | 0, _ => 0
  | count + 1, state =>
      correctionBodyGas state.activeWords n r2 (UInt256.ofNat state.i) +
        correctionIterationsGas n r2 count (correctionAdvance n r2 state)

def correctionLoopStack (state : CorrectionSubtractionState) (iter rLen n kWord r2 returnPc
    result : UInt256) (tail : List UInt256) : List UInt256 :=
  UInt256.ofNat state.i :: state.borrow :: iter :: rLen :: n :: kWord :: r2 ::
    returnPc :: result :: tail

@[simp] theorem correctionIterate_advance
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    correctionIterate n r2 count (correctionAdvance n r2 state) =
      correctionIterate n r2 (count + 1) state := by rfl

theorem correctionIterate_i
    (n r2 : UInt256) (count : Nat) (state : CorrectionSubtractionState) :
    (correctionIterate n r2 count state).i = state.i + count := by
  induction count generalizing state with
  | zero => simp [correctionIterate]
  | succ count ih =>
      rw [show correctionIterate n r2 (count + 1) state =
        correctionIterate n r2 count (correctionAdvance n r2 state) by rfl, ih]
      change state.i + 1 + count = state.i + (count + 1)
      omega

theorem correctionIterationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed count kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (state : CorrectionSubtractionState)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (hindices : ∀ q, q < count → (correctionIterate n r2 q state).i < kWords)
    (h : RDx runtimeBytecode ee g s0 ⟨6794⟩
      (correctionLoopStack state iter (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let final := correctionIterate n r2 count state
    RDx runtimeBytecode ee g s0 ⟨6794⟩
      (correctionLoopStack final iter (UInt256.ofNat (kWords + 1)) n
        (UInt256.ofNat kWords) r2 returnPc result tail)
      final.memory final.activeWords rdata acc (steps + 59 * count)
      (gasUsed + correctionIterationsGas n r2 count state) := by
  induction count generalizing state steps gasUsed with
  | zero => simpa [correctionIterate, correctionIterationsGas]
  | succ count ih =>
      have rdNext := correctionOrdinaryColumnExact
        (hindices 0 (by omega)) hkWord hdepth
        (by simpa [correctionLoopStack] using h)
      have hindices' : ∀ q, q < count →
          (correctionIterate n r2 q (correctionAdvance n r2 state)).i < kWords := by
        intro q hq
        simpa [correctionIterate_advance] using hindices (q + 1) (by omega)
      have rdRest := ih (state := correctionAdvance n r2 state) hindices'
        (by simpa [correctionLoopStack, correctionAdvance] using rdNext)
      have normalized := rdRest.withIndices (k' := steps + 59 * (count + 1))
        (by omega)
        (C' := gasUsed + correctionIterationsGas n r2 (count + 1) state) (by
          simp only [correctionIterationsGas, correctionIterate]
          omega)
      simpa only [correctionIterate] using normalized

def correctionInitialState (mem : ByteArray) (aw : UInt256) : CorrectionSubtractionState where
  i := 0
  borrow := ⟨0⟩
  memory := mem
  activeWords := aw

def correctionPassGas
    (n r2 : UInt256) (kWords : Nat) (state : CorrectionSubtractionState) : Nat :=
  let beforeFinal := correctionIterate n r2 kWords state
  correctionIterationsGas n r2 kWords state +
    correctionTerminalGas beforeFinal.activeWords r2 (UInt256.ofNat kWords)

/-- Execute one complete selected correction subtraction over `n` extended by a zero limb. -/
theorem correctionPassFromZeroExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨6794⟩
      (⟨0⟩ :: ⟨0⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial := correctionInitialState mem aw
    let beforeFinal := correctionIterate n r2 kWords initial
    let finalMemory := correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat kWords) beforeFinal.borrow
    let finalWords := correctionTerminalWords beforeFinal.activeWords r2
      (UInt256.ofNat kWords)
    let finalBorrow := (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat kWords) beforeFinal.borrow).2
    RDx runtimeBytecode ee g s0 ⟨6788⟩
      (UInt256.ofNat (kWords + 1) :: finalBorrow :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      finalMemory finalWords rdata acc (steps + 59 * kWords + 48)
      (gasUsed + correctionPassGas n r2 kWords initial) := by
  let initial := correctionInitialState mem aw
  have hindex (q : Nat) : (correctionIterate n r2 q initial).i = q := by
    simpa [initial, correctionInitialState] using correctionIterate_i n r2 q initial
  have hindices : ∀ q, q < kWords → (correctionIterate n r2 q initial).i < kWords := by
    intro q hq
    rw [hindex q]
    exact hq
  have rdBefore := correctionIterationsExact initial hkWord hdepth hindices
    (by simpa [initial, correctionInitialState, correctionLoopStack] using h)
  let beforeFinal := correctionIterate n r2 kWords initial
  have hbeforeFinal : beforeFinal.i = kWords := by
    simpa [beforeFinal] using hindex kWords
  have rdFinal := correctionTerminalColumnExact hkWord hdepth
    (by simpa [beforeFinal, correctionLoopStack, hbeforeFinal] using rdBefore)
  have normalized := rdFinal.withIndices (k' := steps + 59 * kWords + 48) (by omega)
    (C' := gasUsed + correctionPassGas n r2 kWords initial) (by
      unfold correctionPassGas
      dsimp only [beforeFinal]
      omega)
  simpa [initial, beforeFinal] using normalized

end Modexp.MultiLimbBarrettSubtract
