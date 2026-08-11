import Examples.Precompiles.Modexp.MultiLimbBarrettMulContract

/-!
# Barrett truncated multiplication execution contract

This module continues `_barrettMulMod` at PC 6666 and executes the assembly computation of
`r2 = (q3 * n) mod B^(k+1)` from the concrete arrays allocated by the caller.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettTruncatedMul

open Modexp.MultiLimbSchoolbookMulTrace
open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

/-- The deployed defensive cap replaces q3's `k+3` length by the output width `k+1` before
entering the truncated-product outer loop. -/
theorem capExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 r2 n returnPc product : UInt256}
    (hkBound : kWords + 3 < UInt256.size)
    (hdepth : tail.length + 8 ≤ 1018)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6666⟩
      (r2 :: UInt256.ofNat (kWords + 3) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6675⟩
      (q3 :: UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 13) (gasUsed + 46) := by
  have hq3 : UInt256.gt (UInt256.ofNat (kWords + 3))
      (UInt256.ofNat (kWords + 1)) = ⟨1⟩ := by
    apply ugt_one
    rw [UInt256.toNat_ofNat_of_lt hkBound,
      UInt256.toNat_ofNat_of_lt (by omega : kWords + 1 < UInt256.size)]
    omega
  have hcondition : UInt256.gt (UInt256.ofNat (kWords + 3))
      (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    rw [hq3]
    native_decide
  have rd7156 := GeneratedTraces.trace_6666_taken
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hcondition (by native_decide)
  have rd6675 := evm_run rd7156 with [
    jumpdest,
    dup3,
    swap2,
    pop,
    pushCanonical 2 .PUSH2 ⟨6675⟩ (by decide),
    jump (by native_decide)
  ]
  exact rd6675.withIndices (by omega) (by omega)

/-- Apply the defensive cap, initialize outer index zero, and stop at the real outer guard. -/
theorem truncatedEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 r2 n returnPc product : UInt256}
    (hkBound : kWords + 3 < UInt256.size)
    (hdepth : tail.length + 13 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6666⟩
      (r2 :: UInt256.ofNat (kWords + 3) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6677⟩
      (⟨0⟩ :: q3 :: UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 15) (gasUsed + 49) := by
  have rd6675 := capExact hkBound (by omega) h
  have rd6677 := evm_run rd6675 with [jumpdest, push0]
  have normalized := rd6677.withIndices (k' := steps + 15) (by omega)
    (C' := gasUsed + 49) (by omega)
  exact normalized

def q3ElementPtr (q3 i : UInt256) : UInt256 := elementPtr q3 i

def q3Word (mem : ByteArray) (aw q3 i : UInt256) : UInt256 :=
  readWord mem aw (q3ElementPtr q3 i)

def q3Words (aw q3 i : UInt256) : UInt256 :=
  afterLoad aw (q3ElementPtr q3 i)

def q3LoadGas (aw q3 i : UInt256) : Nat :=
  31 + (Cₘ (q3Words aw q3 i) - Cₘ aw)

/-- Load the actual q3 limb selected by the outer index and stop at its zero/nonzero branch. -/
theorem q3LoadExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {i q3 q3Cap rLen n kWord r2 : UInt256}
    (hdepth : tail.length + 7 ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨6983⟩
      (i :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    let qi := q3Word mem aw q3 i
    RDx runtimeBytecode ee g s0 ⟨6998⟩
      (⟨7008⟩ :: qi :: qi :: i :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      mem (q3Words aw q3 i) rdata acc (steps + 11) (gasUsed + q3LoadGas aw q3 i) := by
  have rd := GeneratedTraces.trace_6983_body
    (by simp only [List.length_cons]; omega) h
  simpa [q3Word, q3Words, q3LoadGas, q3ElementPtr, elementPtr, afterLoad,
    readWord, readWords1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    u256_add_comm] using rd

/-- A zero q3 limb skips its multiplication row and increments the concrete outer index. -/
theorem zeroRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {i q3 q3Cap rLen n kWord r2 : UInt256}
    (hzero : q3Word mem aw q3 i = ⟨0⟩)
    (hdepth : tail.length + 7 ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨6983⟩
      (i :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    let nextI := i + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (nextI :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      mem (q3Words aw q3 i) rdata acc (steps + 18)
      (gasUsed + q3LoadGas aw q3 i + 30) := by
  have rd6998 := q3LoadExact hdepth h
  have rd6999 := rd6998.jumpiNT (by native_decide) (by simpa [hzero])
    (by simp only [List.length_cons]; omega)
  have rd6677 := evm_run rd6999 with [
    jumpdest,
    pop,
    pushCanonical 1 .PUSH1 ⟨1⟩ (by decide),
    add,
    pushCanonical 2 .PUSH2 ⟨6677⟩ (by decide),
    jump (by native_decide)
  ]
  have normalized := rd6677.withIndices (k' := steps + 18) (by omega)
    (C' := gasUsed + q3LoadGas aw q3 i + 30) (by omega)
  simpa [u256_add_comm] using normalized

/-- One concrete truncated-product inner column. This is the deployed full-width
product-plus-carry recurrence, writing only the selected `r2[i+j]` limb. -/
theorem innerBodyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {qi j jMax carry i q3 q3Cap rLen n kWord r2 : UInt256}
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7079⟩
      (qi :: j :: jMax :: carry :: i :: q3 :: q3Cap :: rLen :: n :: kWord ::
        r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    let output := MultiLimbSchoolbookMulTrace.step mem aw qi n r2 i j carry
    let nextJ := j + ⟨1⟩
    RDx runtimeBytecode ee g s0 ⟨7032⟩
      (⟨7079⟩ :: nextJ.lt jMax :: qi :: nextJ :: jMax :: output.2 :: i :: q3 ::
        q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      (nextMemory mem aw qi n r2 i j carry) (nextWords aw n r2 i j)
      rdata acc (steps + 67) (gasUsed + bodyGas aw n r2 i j) := by
  have rd := GeneratedTraces.trace_7079_body hdepth h
  rw [u256_add_comm n (j.shiftLeft ⟨5⟩)] at rd
  have normalized := rd.withIndices (k' := steps + 67) (by omega)
    (C' := gasUsed + bodyGas aw n r2 i j) (by
      simp only [bodyGas, afterLoad, readWords1, elementPtr]
      omega)
  exact normalized

def truncatedLoopStack (state : InnerState) (qi jMax i q3 q3Cap rLen n kWord r2 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  qi :: state.j :: jMax :: state.carry :: i :: q3 :: q3Cap :: rLen :: n :: kWord ::
    r2 :: tail

/-- Execute any number of continuing truncated-product columns. -/
theorem innerIterationsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed count : Nat} {tail : List UInt256}
    {qi jMax i q3 q3Cap rLen n kWord r2 : UInt256}
    (state : InnerState)
    (hdepth : tail.length + 11 ≤ 1016)
    (hcontinue : ∀ q, q < count →
      (advance qi n r2 i (iterate qi n r2 i q state)).j.lt jMax ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7079⟩
      (truncatedLoopStack state qi jMax i q3 q3Cap rLen n kWord r2 tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨7079⟩
      (truncatedLoopStack (iterate qi n r2 i count state)
        qi jMax i q3 q3Cap rLen n kWord r2 tail)
      (iterate qi n r2 i count state).memory
      (iterate qi n r2 i count state).activeWords rdata acc
      (steps + 68 * count) (gasUsed + iterationsGas qi n r2 i count state) := by
  induction count generalizing state steps gasUsed with
  | zero => simpa [iterate, iterationsGas]
  | succ count ih =>
      have rd7032 := innerBodyExact hdepth h
      have rdNext := rd7032.jumpiT (by native_decide) (hcontinue 0 (by omega))
        (by native_decide) (by simp only [List.length_cons]; omega)
      have hcontinue' : ∀ q, q < count →
          (advance qi n r2 i
            (iterate qi n r2 i q (advance qi n r2 i state))).j.lt jMax ≠ ⟨0⟩ := by
        intro q hq
        simpa [iterate_advance] using hcontinue (q + 1) (by omega)
      have rdRest := ih (state := advance qi n r2 i state) hcontinue' rdNext
      have normalized := rdRest.withIndices (k' := steps + 68 * (count + 1))
        (by omega) rfl
      simpa [truncatedLoopStack, iterate, advance, iterationsGas, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm, Nat.mul_add] using normalized

/-- Execute all continuing columns and the final column, whose guard exits to PC 7033. -/
theorem innerThroughExitExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed count : Nat} {tail : List UInt256}
    {qi jMax i q3 q3Cap rLen n kWord r2 : UInt256}
    (state : InnerState)
    (hdepth : tail.length + 11 ≤ 1016)
    (hcontinue : ∀ q, q < count →
      (advance qi n r2 i (iterate qi n r2 i q state)).j.lt jMax ≠ ⟨0⟩)
    (hexit :
      (advance qi n r2 i (iterate qi n r2 i count state)).j.lt jMax = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨7079⟩
      (truncatedLoopStack state qi jMax i q3 q3Cap rLen n kWord r2 tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let final := advance qi n r2 i (iterate qi n r2 i count state)
    RDx runtimeBytecode ee g s0 ⟨7033⟩
      (truncatedLoopStack final qi jMax i q3 q3Cap rLen n kWord r2 tail)
      final.memory final.activeWords rdata acc
      (steps + 68 * (count + 1))
      (gasUsed + throughExitGas qi n r2 i count state) := by
  have rdIterations := innerIterationsExact state hdepth hcontinue h
  have rd7032 := innerBodyExact hdepth rdIterations
  have rd7033 := rd7032.jumpiNT (by native_decide) hexit
    (by simp only [List.length_cons]; omega)
  have normalized := rd7033.withIndices (k' := steps + 68 * (count + 1))
    (by omega) rfl
  simpa [truncatedLoopStack, advance, throughExitGas, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm, Nat.mul_add] using normalized

/-- At `i=0`, the raw bound `rLen-i=k+1` exceeds `k`, so the deployed cap sets
`jMax=k` before entering the first inner column. -/
theorem firstInnerEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {qi q3 n r2 : UInt256}
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7008⟩
      (qi :: ⟨0⟩ :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨7079⟩
      (qi :: ⟨0⟩ :: UInt256.ofNat kWords :: ⟨0⟩ :: ⟨0⟩ :: q3 ::
        UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc (steps + 27) (gasUsed + 89) := by
  have hkSmall : kWords < UInt256.size := by omega
  have hcap : UInt256.gt (UInt256.ofNat (kWords + 1))
      (UInt256.ofNat kWords) ≠ ⟨0⟩ := by
    rw [ugt_one (by
      rw [UInt256.toNat_ofNat_of_lt hkWord, UInt256.toNat_ofNat_of_lt hkSmall]
      omega)]
    native_decide
  have rd7148 := GeneratedTraces.trace_7008_taken
    (by simp only [List.length_cons]; omega) h (by native_decide)
    (by
      have hsubzero : UInt256.sub (UInt256.ofNat (kWords + 1)) ⟨0⟩ =
          UInt256.ofNat (kWords + 1) := by
        apply u256_inj
        rw [usub_toNat (by simp)]
        simp
      simpa only [hsubzero] using hcap) (by native_decide)
  have hinner : (⟨0⟩ : UInt256).lt (UInt256.ofNat kWords) ≠ ⟨0⟩ := by
    rw [ult_one (by
      change (⟨0⟩ : UInt256).toNat < (UInt256.ofNat kWords).toNat
      rw [UInt256.toNat_ofNat_of_lt hkSmall]
      norm_num
      exact hkPos)]
    native_decide
  have rd7079 := GeneratedTraces.trace_7148_taken
    (by simp only [List.length_cons]; omega) rd7148 (by native_decide)
    hinner (by native_decide)
  have normalized := rd7079.withIndices (k' := steps + 27) (by omega)
    (C' := gasUsed + 89) (by omega)
  simpa using normalized

/-- At every later outer index `1 ≤ i ≤ k`, `rLen-i` is already at most `k`, so the
deployed cap is not taken and `jMax=k+1-i` remains positive. -/
theorem laterInnerEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {qi q3 n r2 : UInt256}
    (hiPos : 0 < iWords) (hiLe : iWords ≤ kWords)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7008⟩
      (qi :: UInt256.ofNat iWords :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨7079⟩
      (qi :: ⟨0⟩ :: UInt256.ofNat (kWords + 1 - iWords) :: ⟨0⟩ ::
        UInt256.ofNat iWords :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc (steps + 21) (gasUsed + 69) := by
  have hiWord : iWords < UInt256.size := by omega
  have hkSmall : kWords < UInt256.size := by omega
  have hsub : UInt256.sub (UInt256.ofNat (kWords + 1)) (UInt256.ofNat iWords) =
      UInt256.ofNat (kWords + 1 - iWords) :=
    Modexp.ofNat_sub_bounded (by omega) hkWord
  have hcap : UInt256.gt (UInt256.ofNat (kWords + 1 - iWords))
      (UInt256.ofNat kWords) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (by omega : kWords + 1 - iWords < UInt256.size),
      UInt256.toNat_ofNat_of_lt hkSmall]
    omega
  have rd7022 := GeneratedTraces.trace_7008_notTaken
    (by simp only [List.length_cons]; omega) h (by native_decide) (by simpa [hsub, hcap])
  have hjPos : 0 < kWords + 1 - iWords := by omega
  have hjWord : kWords + 1 - iWords < UInt256.size := by omega
  have hinner : (⟨0⟩ : UInt256).lt
      (UInt256.ofNat (kWords + 1 - iWords)) ≠ ⟨0⟩ := by
    rw [ult_one (by
      change (⟨0⟩ : UInt256).toNat <
        (UInt256.ofNat (kWords + 1 - iWords)).toNat
      rw [UInt256.toNat_ofNat_of_lt hjWord]
      norm_num
      exact hiLe)]
    native_decide
  rw [hsub] at rd7022
  have rd7079 := GeneratedTraces.trace_7022_taken
    (by simp only [List.length_cons]; omega) rd7022 (by native_decide)
    hinner (by native_decide)
  have normalized := rd7079.withIndices (k' := steps + 21) (by omega)
    (C' := gasUsed + 69) (by omega)
  simpa [hsub] using normalized

def truncatedCarryPtr (r2 finalIdx : UInt256) : UInt256 := elementPtr r2 finalIdx

def truncatedCarryMemory
    (mem : ByteArray) (aw r2 finalIdx carry : UInt256) : ByteArray :=
  let ptr := truncatedCarryPtr r2 finalIdx
  let prior := readWord mem aw ptr
  (prior + carry).toByteArray.write 0 mem ptr.toNat 32

def truncatedCarryWords (aw r2 finalIdx : UInt256) : UInt256 :=
  let ptr := truncatedCarryPtr r2 finalIdx
  afterLoad (afterLoad aw ptr) ptr

def truncatedCarryCleanupGas (aw r2 finalIdx : UInt256) : Nat :=
  let ptr := truncatedCarryPtr r2 finalIdx
  let loaded := afterLoad aw ptr
  let stored := afterLoad loaded ptr
  95 + (Cₘ loaded - Cₘ aw) + (Cₘ stored - Cₘ loaded)

/-- Store the first row's final carry and remove all row locals before returning to the outer
guard. -/
theorem carryCleanupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {finalIdx carry i q3 q3Cap rLen n kWord r2 : UInt256}
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7057⟩
      (finalIdx :: carry :: i :: ⟨1⟩ :: q3 :: q3Cap :: rLen :: n :: kWord ::
        r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      ((i + ⟨1⟩) :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      (truncatedCarryMemory mem aw r2 finalIdx carry)
      (truncatedCarryWords aw r2 finalIdx) rdata acc
      (steps + 30) (gasUsed + truncatedCarryCleanupGas aw r2 finalIdx) := by
  have rd := evm_run h with [
    jumpdest,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    swap1,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    dup11,
    add,
    add,
    swap1,
    dup2,
    mloadCanonical,
    add,
    swap1,
    mstoreCanonical,
    push0,
    dup1,
    pushCanonical 2 .PUSH2 ⟨7049⟩ (by decide),
    jump (by native_decide),
    jumpdest,
    pop,
    pop,
    swap1,
    pushCanonical 2 .PUSH2 ⟨6999⟩ (by decide),
    jump (by native_decide),
    jumpdest,
    pop,
    pushCanonical 1 .PUSH1 ⟨1⟩ (by decide),
    add,
    pushCanonical 2 .PUSH2 ⟨6677⟩ (by decide),
    jump (by native_decide)
  ]
  rw [u256_add_comm r2 (finalIdx.shiftLeft ⟨5⟩)] at rd
  have normalized := rd.withIndices (k' := steps + 30) (by omega)
    (C' := gasUsed + truncatedCarryCleanupGas aw r2 finalIdx) (by
      simp only [truncatedCarryCleanupGas, truncatedCarryPtr, elementPtr, afterLoad,
        readWords1]
      omega)
  simpa only [u256_add_comm, truncatedCarryMemory, truncatedCarryWords,
    truncatedCarryPtr, elementPtr, afterLoad, readWord, readWords1] using normalized

/-- When `finalIdx=rLen`, skip the final-carry store and remove the row locals. -/
theorem noCarryCleanupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {finalIdx carry i q3 q3Cap rLen n kWord r2 : UInt256}
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨7049⟩
      (finalIdx :: carry :: i :: ⟨1⟩ :: q3 :: q3Cap :: rLen :: n :: kWord ::
        r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      ((i + ⟨1⟩) :: q3 :: q3Cap :: rLen :: n :: kWord :: r2 :: tail)
      mem aw rdata acc (steps + 12) (gasUsed + 39) := by
  have rd := evm_run h with [
    jumpdest,
    pop,
    pop,
    swap1,
    pushCanonical 2 .PUSH2 ⟨6999⟩ (by decide),
    jump (by native_decide),
    jumpdest,
    pop,
    pushCanonical 1 .PUSH1 ⟨1⟩ (by decide),
    add,
    pushCanonical 2 .PUSH2 ⟨6677⟩ (by decide),
    jump (by native_decide)
  ]
  have normalized := rd.withIndices (k' := steps + 12) (by omega)
    (C' := gasUsed + 39) (by omega)
  simpa only [u256_add_comm] using normalized

/-- Finish the `i=0` row. Its final index is `k<k+1`, so the carry store is selected. -/
theorem firstRowFinishExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {qi carry q3 n r2 : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7033⟩
      (qi :: UInt256.ofNat kWords :: UInt256.ofNat kWords :: carry :: ⟨0⟩ :: q3 ::
        UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (⟨1⟩ :: q3 :: UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: tail)
      (truncatedCarryMemory mem aw r2 (UInt256.ofNat kWords) carry)
      (truncatedCarryWords aw r2 (UInt256.ofNat kWords)) rdata acc
      (steps + 43) (gasUsed + 44 + truncatedCarryCleanupGas aw r2 (UInt256.ofNat kWords)) := by
  have hkSmall : kWords < UInt256.size := by omega
  have hcondition : (UInt256.ofNat kWords).lt
      (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    rw [ult_one (by
      rw [UInt256.toNat_ofNat_of_lt hkSmall, UInt256.toNat_ofNat_of_lt hkWord]
      omega)]
    native_decide
  have rd7057 := GeneratedTraces.trace_7033_taken
    (by simp only [List.length_cons]; omega) h (by native_decide)
    (by simpa only [u256_zero_add] using hcondition) (by native_decide)
  have rd6677 := carryCleanupExact (by omega) rd7057
  rw [u256_zero_add] at rd6677
  have normalized := rd6677.withIndices (k' := steps + 43) (by omega)
    (C' := gasUsed + 44 +
      truncatedCarryCleanupGas aw r2 (⟨0⟩ + UInt256.ofNat kWords))
    (by omega)
  simpa only [u256_zero_add] using normalized

/-- Finish a later row. Here `i+jMax=k+1=rLen`, so the carry-store branch is not taken. -/
theorem laterRowFinishExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {qi carry q3 n r2 : UInt256}
    (hiPos : 0 < iWords) (hiLe : iWords ≤ kWords)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨7033⟩
      (qi :: UInt256.ofNat (kWords + 1 - iWords) ::
        UInt256.ofNat (kWords + 1 - iWords) :: carry :: UInt256.ofNat iWords :: q3 ::
        UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (UInt256.ofNat (iWords + 1) :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc (steps + 25) (gasUsed + 83) := by
  have hiWord : iWords < UInt256.size := by omega
  have hnextWord : iWords + 1 < UInt256.size := by omega
  have hjWord : kWords + 1 - iWords < UInt256.size := by omega
  have hfinal : UInt256.ofNat iWords + UInt256.ofNat (kWords + 1 - iWords) =
      UInt256.ofNat (kWords + 1) := by
    rw [Modexp.ofNat_add_bounded (by omega : iWords + (kWords + 1 - iWords) < UInt256.size)]
    congr 1
    omega
  have hcondition : (UInt256.ofNat (kWords + 1)).lt
      (UInt256.ofNat (kWords + 1)) = ⟨0⟩ := ult_zero (by omega)
  have rd7049 := GeneratedTraces.trace_7033_notTaken
    (by simp only [List.length_cons]; omega) h (by native_decide)
    (by simpa [hfinal] using hcondition)
  have rd6677 := noCarryCleanupExact (by omega) rd7049
  have hnext : UInt256.ofNat iWords + ⟨1⟩ = UInt256.ofNat (iWords + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hiWord,
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mod_eq_of_lt hnextWord,
      UInt256.toNat_ofNat_of_lt hnextWord]
  have normalized := rd6677.withIndices (k' := steps + 25) (by omega)
    (C' := gasUsed + 83) (by omega)
  simpa [hfinal, hnext] using normalized

def truncatedInitialState (mem : ByteArray) (aw q3 i : UInt256) : InnerState where
  j := ⟨0⟩
  carry := ⟨0⟩
  memory := mem
  activeWords := q3Words aw q3 i

def truncatedCompletedState
    (mem : ByteArray) (aw qi q3 n r2 i : UInt256) (width : Nat) : InnerState :=
  iterate qi n r2 i width (truncatedInitialState mem aw q3 i)

def firstNonzeroRowMemory
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat) : ByteArray :=
  let qi := q3Word mem aw q3 ⟨0⟩
  let final := truncatedCompletedState mem aw qi q3 n r2 ⟨0⟩ kWords
  truncatedCarryMemory final.memory final.activeWords r2 (UInt256.ofNat kWords) final.carry

def firstNonzeroRowWords
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat) : UInt256 :=
  let qi := q3Word mem aw q3 ⟨0⟩
  let final := truncatedCompletedState mem aw qi q3 n r2 ⟨0⟩ kWords
  truncatedCarryWords final.activeWords r2 (UInt256.ofNat kWords)

def firstNonzeroRowGas
    (mem : ByteArray) (aw q3 n r2 : UInt256) (kWords : Nat) : Nat :=
  let qi := q3Word mem aw q3 ⟨0⟩
  let initial := truncatedInitialState mem aw q3 ⟨0⟩
  let final := truncatedCompletedState mem aw qi q3 n r2 ⟨0⟩ kWords
  q3LoadGas aw q3 ⟨0⟩ + 143 + throughExitGas qi n r2 ⟨0⟩ (kWords - 1) initial +
    truncatedCarryCleanupGas final.activeWords r2 (UInt256.ofNat kWords)

/-- Execute the complete nonzero `i=0` row, including its capped width and final-carry store. -/
theorem firstNonzeroRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 n r2 : UInt256}
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hnonzero : q3Word mem aw q3 ⟨0⟩ ≠ ⟨0⟩)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨6983⟩
      (⟨0⟩ :: q3 :: UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (⟨1⟩ :: q3 :: UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: tail)
      (firstNonzeroRowMemory mem aw q3 n r2 kWords)
      (firstNonzeroRowWords mem aw q3 n r2 kWords) rdata acc
      (steps + 82 + 68 * kWords)
      (gasUsed + firstNonzeroRowGas mem aw q3 n r2 kWords) := by
  let qi := q3Word mem aw q3 ⟨0⟩
  let initial := truncatedInitialState mem aw q3 ⟨0⟩
  have rd6998 := q3LoadExact (by omega) h
  have rd7008 := rd6998.jumpiT (by native_decide) hnonzero
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd7079 := firstInnerEntryExact hkPos hkWord hdepth rd7008
  have hj (q : Nat) (hq : q < kWords) :
      (iterate qi n r2 ⟨0⟩ q initial).j.toNat = q := by
    have hbound : initial.j.toNat + q < UInt256.size := by
      dsimp only [initial, truncatedInitialState]
      rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
      omega
    simpa [initial, truncatedInitialState] using
      iterate_j_toNat qi n r2 ⟨0⟩ q initial hbound
  have hcontinue : ∀ q, q < kWords - 1 →
      (advance qi n r2 ⟨0⟩ (iterate qi n r2 ⟨0⟩ q initial)).j.lt
        (UInt256.ofNat kWords) ≠ ⟨0⟩ := by
    intro q hq
    have hnext :
        (advance qi n r2 ⟨0⟩ (iterate qi n r2 ⟨0⟩ q initial)).j.toNat = q + 1 := by
      rw [advance_j_toNat]
      · rw [hj q (by omega)]
      · rw [hj q (by omega)]
        omega
    rw [ult_one (by
      rw [hnext, UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size)]
      omega)]
    native_decide
  have hexit :
      (advance qi n r2 ⟨0⟩
        (iterate qi n r2 ⟨0⟩ (kWords - 1) initial)).j.lt
          (UInt256.ofNat kWords) = ⟨0⟩ := by
    have hbefore := hj (kWords - 1) (by omega)
    have hnext :
        (advance qi n r2 ⟨0⟩
          (iterate qi n r2 ⟨0⟩ (kWords - 1) initial)).j.toNat = kWords := by
      rw [advance_j_toNat]
      · omega
      · rw [hbefore]
        omega
    apply ult_zero
    rw [hnext, UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size)]
  have rd7033 := innerThroughExitExact initial hdepth hcontinue hexit
    (by simpa [qi, initial, truncatedInitialState, truncatedLoopStack] using rd7079)
  let final := truncatedCompletedState mem aw qi q3 n r2 ⟨0⟩ kWords
  have hfinal :
      advance qi n r2 ⟨0⟩ (iterate qi n r2 ⟨0⟩ (kWords - 1) initial) = final := by
    rw [advance_iterate]
    have hcount : kWords - 1 + 1 = kWords := by omega
    simpa [final, truncatedCompletedState, initial] using congrArg
      (fun width => iterate qi n r2 ⟨0⟩ width initial) hcount
  rw [hfinal] at rd7033
  have hfinalJ : final.j = UInt256.ofNat kWords := by
    apply u256_inj
    rw [UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size)]
    simpa [final, truncatedCompletedState, initial, truncatedInitialState] using
      iterate_j_toNat qi n r2 ⟨0⟩ kWords initial (by
        dsimp only [initial, truncatedInitialState]
        rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
        omega)
  simp only [truncatedLoopStack] at rd7033
  rw [hfinalJ] at rd7033
  have rd6677 := firstRowFinishExact hkWord hdepth rd7033
  have normalized := rd6677.withIndices (k' := steps + 82 + 68 * kWords) (by omega)
    (C' := gasUsed + firstNonzeroRowGas mem aw q3 n r2 kWords) (by
      unfold firstNonzeroRowGas
      dsimp only [qi, initial, final]
      omega)
  simpa [firstNonzeroRowMemory, firstNonzeroRowWords, qi, final,
    truncatedCompletedState] using normalized

def laterNonzeroRowMemory
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords kWords : Nat) : ByteArray :=
  let i := UInt256.ofNat iWords
  let qi := q3Word mem aw q3 i
  (truncatedCompletedState mem aw qi q3 n r2 i (kWords + 1 - iWords)).memory

def laterNonzeroRowWords
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords kWords : Nat) : UInt256 :=
  let i := UInt256.ofNat iWords
  let qi := q3Word mem aw q3 i
  (truncatedCompletedState mem aw qi q3 n r2 i (kWords + 1 - iWords)).activeWords

def laterNonzeroRowGas
    (mem : ByteArray) (aw q3 n r2 : UInt256) (iWords kWords : Nat) : Nat :=
  let i := UInt256.ofNat iWords
  let qi := q3Word mem aw q3 i
  let initial := truncatedInitialState mem aw q3 i
  q3LoadGas aw q3 i + 162 +
    throughExitGas qi n r2 i (kWords - iWords) initial

/-- Execute a complete nonzero row for `1≤i≤k`; truncation omits its out-of-range carry. -/
theorem laterNonzeroRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {q3 n r2 : UInt256}
    (hiPos : 0 < iWords) (hiLe : iWords ≤ kWords)
    (hkWord : kWords + 1 < UInt256.size)
    (hnonzero : q3Word mem aw q3 (UInt256.ofNat iWords) ≠ ⟨0⟩)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨6983⟩
      (UInt256.ofNat iWords :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (UInt256.ofNat (iWords + 1) :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: tail)
      (laterNonzeroRowMemory mem aw q3 n r2 iWords kWords)
      (laterNonzeroRowWords mem aw q3 n r2 iWords kWords) rdata acc
      (steps + 58 + 68 * (kWords + 1 - iWords))
      (gasUsed + laterNonzeroRowGas mem aw q3 n r2 iWords kWords) := by
  let i := UInt256.ofNat iWords
  let width := kWords + 1 - iWords
  let qi := q3Word mem aw q3 i
  let initial := truncatedInitialState mem aw q3 i
  have hwidthPos : 0 < width := by omega
  have hwidthWord : width < UInt256.size := by omega
  have rd6998 := q3LoadExact (by omega) h
  have rd7008 := rd6998.jumpiT (by native_decide) hnonzero
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd7079 := laterInnerEntryExact hiPos hiLe hkWord hdepth rd7008
  have hj (q : Nat) (hq : q < width) :
      (iterate qi n r2 i q initial).j.toNat = q := by
    have hbound : initial.j.toNat + q < UInt256.size := by
      dsimp only [initial, truncatedInitialState]
      rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
      omega
    simpa [initial, truncatedInitialState] using
      iterate_j_toNat qi n r2 i q initial hbound
  have hcontinue : ∀ q, q < width - 1 →
      (advance qi n r2 i (iterate qi n r2 i q initial)).j.lt
        (UInt256.ofNat width) ≠ ⟨0⟩ := by
    intro q hq
    have hnext :
        (advance qi n r2 i (iterate qi n r2 i q initial)).j.toNat = q + 1 := by
      rw [advance_j_toNat]
      · rw [hj q (by omega)]
      · rw [hj q (by omega)]
        omega
    rw [ult_one (by
      rw [hnext, UInt256.toNat_ofNat_of_lt hwidthWord]
      omega)]
    native_decide
  have hexit :
      (advance qi n r2 i (iterate qi n r2 i (width - 1) initial)).j.lt
        (UInt256.ofNat width) = ⟨0⟩ := by
    have hbefore := hj (width - 1) (by omega)
    have hnext :
        (advance qi n r2 i (iterate qi n r2 i (width - 1) initial)).j.toNat = width := by
      rw [advance_j_toNat]
      · omega
      · rw [hbefore]
        omega
    apply ult_zero
    rw [hnext, UInt256.toNat_ofNat_of_lt hwidthWord]
  have rd7033 := innerThroughExitExact initial hdepth hcontinue hexit
    (by simpa [i, width, qi, initial, truncatedInitialState, truncatedLoopStack] using rd7079)
  let final := truncatedCompletedState mem aw qi q3 n r2 i width
  have hfinal :
      advance qi n r2 i (iterate qi n r2 i (width - 1) initial) = final := by
    rw [advance_iterate]
    have hcount : width - 1 + 1 = width := by omega
    simpa [final, truncatedCompletedState, initial] using congrArg
      (fun count => iterate qi n r2 i count initial) hcount
  rw [hfinal] at rd7033
  have hwidthPred : width - 1 = kWords - iWords := by
    dsimp only [width]
    omega
  rw [hwidthPred] at rd7033
  have hfinalJ : final.j = UInt256.ofNat width := by
    apply u256_inj
    rw [UInt256.toNat_ofNat_of_lt hwidthWord]
    simpa [final, truncatedCompletedState, initial, truncatedInitialState] using
      iterate_j_toNat qi n r2 i width initial (by
        dsimp only [initial, truncatedInitialState]
        rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
        omega)
  simp only [truncatedLoopStack] at rd7033
  rw [hfinalJ] at rd7033
  have rd6677 := laterRowFinishExact hiPos hiLe hkWord hdepth rd7033
  have normalized := rd6677.withIndices
    (k' := steps + 58 + 68 * (kWords + 1 - iWords)) (by omega)
    (C' := gasUsed + laterNonzeroRowGas mem aw q3 n r2 iWords kWords) (by
      unfold laterNonzeroRowGas
      dsimp only [i, width, qi, initial]
      omega)
  simpa [laterNonzeroRowMemory, laterNonzeroRowWords, i, width, qi, final,
    truncatedCompletedState] using normalized

structure TruncatedOuterState where
  i : Nat
  memory : ByteArray
  activeWords : UInt256

def truncatedRowAdvance
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState) :
    TruncatedOuterState :=
  let i := UInt256.ofNat state.i
  if q3Word state.memory state.activeWords q3 i = ⟨0⟩ then
    { i := state.i + 1
      memory := state.memory
      activeWords := q3Words state.activeWords q3 i }
  else if state.i = 0 then
    { i := 1
      memory := firstNonzeroRowMemory state.memory state.activeWords q3 n r2 kWords
      activeWords := firstNonzeroRowWords state.memory state.activeWords q3 n r2 kWords }
  else
    { i := state.i + 1
      memory := laterNonzeroRowMemory state.memory state.activeWords q3 n r2 state.i kWords
      activeWords := laterNonzeroRowWords state.memory state.activeWords q3 n r2 state.i kWords }

def truncatedRowSteps (q3 : UInt256) (kWords : Nat) (state : TruncatedOuterState) : Nat :=
  let i := UInt256.ofNat state.i
  if q3Word state.memory state.activeWords q3 i = ⟨0⟩ then 18
  else if state.i = 0 then 82 + 68 * kWords
  else 58 + 68 * (kWords + 1 - state.i)

def truncatedRowGas
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState) : Nat :=
  let i := UInt256.ofNat state.i
  if q3Word state.memory state.activeWords q3 i = ⟨0⟩ then
    q3LoadGas state.activeWords q3 i + 30
  else if state.i = 0 then
    firstNonzeroRowGas state.memory state.activeWords q3 n r2 kWords
  else
    laterNonzeroRowGas state.memory state.activeWords q3 n r2 state.i kWords

def truncatedOuterStack (state : TruncatedOuterState)
    (q3 n r2 returnPc product : UInt256) (kWords : Nat) (tail : List UInt256) :
    List UInt256 :=
  UInt256.ofNat state.i :: q3 :: UInt256.ofNat (kWords + 1) ::
    UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: returnPc ::
    product :: tail

/-- Select one complete truncated-product row from the q3 limb actually loaded from memory. -/
theorem truncatedRowExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 n r2 returnPc product : UInt256}
    (state : TruncatedOuterState)
    (hkPos : 0 < kWords) (hiLe : state.i ≤ kWords)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 13 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨6983⟩
      (UInt256.ofNat state.i :: q3 :: UInt256.ofNat (kWords + 1) ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 :: returnPc ::
        product :: tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let next := truncatedRowAdvance q3 n r2 kWords state
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (truncatedOuterStack next q3 n r2 returnPc product kWords tail)
      next.memory next.activeWords rdata acc
      (steps + truncatedRowSteps q3 kWords state)
      (gasUsed + truncatedRowGas q3 n r2 kWords state) := by
  let i := UInt256.ofNat state.i
  have hiWord : state.i + 1 < UInt256.size := by omega
  have hnext : UInt256.ofNat state.i + ⟨1⟩ = UInt256.ofNat (state.i + 1) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : state.i < UInt256.size),
      show (⟨1⟩ : UInt256).toNat = 1 by decide, Nat.mod_eq_of_lt hiWord,
      UInt256.toNat_ofNat_of_lt hiWord]
  by_cases hzero : q3Word state.memory state.activeWords q3 i = ⟨0⟩
  · have rd := zeroRowExact (tail := returnPc :: product :: tail) hzero
      (by simp only [List.length_cons]; omega) h
    simpa [truncatedOuterStack, truncatedRowAdvance, truncatedRowSteps,
      truncatedRowGas, i, hzero, hnext] using rd
  · by_cases hiZero : state.i = 0
    · have hzero0 : q3Word state.memory state.activeWords q3
          (UInt256.ofNat 0) ≠ ⟨0⟩ := by
        simpa [i, hiZero] using hzero
      have rd := firstNonzeroRowExact (tail := returnPc :: product :: tail) hkPos hkWord
        hzero0
        (by simp only [List.length_cons]; omega)
        (by simpa [hiZero] using h)
      simpa [truncatedOuterStack, truncatedRowAdvance, truncatedRowSteps,
        truncatedRowGas, i, hzero, hzero0, hiZero, Nat.add_assoc,
        show UInt256.ofNat 1 = (⟨1⟩ : UInt256) by decide] using rd
    · have hiPos : 0 < state.i := Nat.pos_of_ne_zero hiZero
      have rd := laterNonzeroRowExact (tail := returnPc :: product :: tail)
        hiPos hiLe hkWord hzero
        (by simp only [List.length_cons]; omega) h
      simpa [truncatedOuterStack, truncatedRowAdvance, truncatedRowSteps,
        truncatedRowGas, i, hzero, hiZero, hnext, Nat.add_assoc] using rd

def truncatedRowsIterate (q3 n r2 : UInt256) (kWords : Nat) :
    Nat → TruncatedOuterState → TruncatedOuterState
  | 0, state => state
  | count + 1, state =>
      truncatedRowsIterate q3 n r2 kWords count
        (truncatedRowAdvance q3 n r2 kWords state)

def truncatedRowsSteps (q3 n r2 : UInt256) (kWords : Nat) :
    Nat → TruncatedOuterState → Nat
  | 0, _ => 0
  | count + 1, state =>
      6 + truncatedRowSteps q3 kWords state +
        truncatedRowsSteps q3 n r2 kWords count
          (truncatedRowAdvance q3 n r2 kWords state)

def truncatedRowsGas (q3 n r2 : UInt256) (kWords : Nat) :
    Nat → TruncatedOuterState → Nat
  | 0, _ => 0
  | count + 1, state =>
      23 + truncatedRowGas q3 n r2 kWords state +
        truncatedRowsGas q3 n r2 kWords count
          (truncatedRowAdvance q3 n r2 kWords state)

@[simp] theorem truncatedRowsIterate_advance
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState) :
    truncatedRowsIterate q3 n r2 kWords count
        (truncatedRowAdvance q3 n r2 kWords state) =
      truncatedRowsIterate q3 n r2 kWords (count + 1) state := by
  rfl

/-- The truncated outer recurrence may equivalently expose its final selected row. -/
theorem truncatedRowsIterate_succ_last
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState) :
    truncatedRowsIterate q3 n r2 kWords (count + 1) state =
      truncatedRowAdvance q3 n r2 kWords
        (truncatedRowsIterate q3 n r2 kWords count state) := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [show truncatedRowsIterate q3 n r2 kWords (count + 1 + 1) state =
        truncatedRowsIterate q3 n r2 kWords (count + 1)
          (truncatedRowAdvance q3 n r2 kWords state) by rfl]
      rw [ih, truncatedRowsIterate_advance]

theorem truncatedRowAdvance_i
    (q3 n r2 : UInt256) (kWords : Nat) (state : TruncatedOuterState) :
    (truncatedRowAdvance q3 n r2 kWords state).i = state.i + 1 := by
  by_cases hzero : q3Word state.memory state.activeWords q3
      (UInt256.ofNat state.i) = ⟨0⟩
  · simp [truncatedRowAdvance, hzero]
  · by_cases hiZero : state.i = 0
    · have hzero0 : q3Word state.memory state.activeWords q3
          (UInt256.ofNat 0) ≠ ⟨0⟩ := by simpa [hiZero] using hzero
      simp [truncatedRowAdvance, hiZero, hzero0]
    · simp [truncatedRowAdvance, hzero, hiZero]

theorem truncatedRowsIterate_i
    (q3 n r2 : UInt256) (kWords count : Nat) (state : TruncatedOuterState) :
    (truncatedRowsIterate q3 n r2 kWords count state).i = state.i + count := by
  induction count generalizing state with
  | zero => simp [truncatedRowsIterate]
  | succ count ih =>
      rw [show truncatedRowsIterate q3 n r2 kWords (count + 1) state =
        truncatedRowsIterate q3 n r2 kWords count
          (truncatedRowAdvance q3 n r2 kWords state) by rfl, ih,
        truncatedRowAdvance_i]
      omega

/-- Execute any number of selected outer rows from the deployed PC 6677 guard. -/
theorem truncatedRowsExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords count : Nat} {tail : List UInt256}
    {q3 n r2 returnPc product : UInt256}
    (state : TruncatedOuterState)
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 13 ≤ 1016)
    (hindices : ∀ q, q < count →
      (truncatedRowsIterate q3 n r2 kWords q state).i ≤ kWords)
    (hcontinue : ∀ q, q < count →
      (UInt256.ofNat (truncatedRowsIterate q3 n r2 kWords q state).i).lt
        (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨6677⟩
      (truncatedOuterStack state q3 n r2 returnPc product kWords tail)
      state.memory state.activeWords rdata acc steps gasUsed) :
    let final := truncatedRowsIterate q3 n r2 kWords count state
    RDx runtimeBytecode ee g s0 ⟨6677⟩
      (truncatedOuterStack final q3 n r2 returnPc product kWords tail)
      final.memory final.activeWords rdata acc
      (steps + truncatedRowsSteps q3 n r2 kWords count state)
      (gasUsed + truncatedRowsGas q3 n r2 kWords count state) := by
  induction count generalizing state steps gasUsed with
  | zero => simpa [truncatedRowsIterate, truncatedRowsSteps, truncatedRowsGas]
  | succ count ih =>
      have rd6983 := GeneratedTraces.trace_6677_taken
        (by simp only [truncatedOuterStack, List.length_cons]; omega) h
        (by native_decide) (hcontinue 0 (by omega)) (by native_decide)
      have rdRow := truncatedRowExact state hkPos (hindices 0 (by omega)) hkWord hdepth
        (by simpa [truncatedOuterStack] using rd6983)
      have hindices' : ∀ q, q < count →
          (truncatedRowsIterate q3 n r2 kWords q
            (truncatedRowAdvance q3 n r2 kWords state)).i ≤ kWords := by
        intro q hq
        simpa [truncatedRowsIterate_advance] using hindices (q + 1) (by omega)
      have hcontinue' : ∀ q, q < count →
          (UInt256.ofNat (truncatedRowsIterate q3 n r2 kWords q
            (truncatedRowAdvance q3 n r2 kWords state)).i).lt
              (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
        intro q hq
        simpa [truncatedRowsIterate_advance] using hcontinue (q + 1) (by omega)
      have rdRest := ih (state := truncatedRowAdvance q3 n r2 kWords state)
        hindices' hcontinue' rdRow
      have normalized := rdRest.withIndices
        (k' := steps + truncatedRowsSteps q3 n r2 kWords (count + 1) state) (by
          simp only [truncatedRowsSteps]
          omega)
        (C' := gasUsed + truncatedRowsGas q3 n r2 kWords (count + 1) state) (by
          simp only [truncatedRowsGas]
          omega)
      simpa only [truncatedRowsIterate] using normalized

/-- Execute all `k+1` rows from `i=0`, prove the terminal guard false, and enter the result
allocation continuation at PC 6685 with the computed r2 memory. -/
theorem truncatedRowsFromZeroExitExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 n r2 returnPc product : UInt256}
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 13 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨6677⟩
      (truncatedOuterStack { i := 0, memory := mem, activeWords := aw }
        q3 n r2 returnPc product kWords tail)
      mem aw rdata acc steps gasUsed) :
    let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    RDx runtimeBytecode ee g s0 ⟨6685⟩
      (truncatedOuterStack final q3 n r2 returnPc product kWords tail)
      final.memory final.activeWords rdata acc
      (steps + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial + 6)
      (gasUsed + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial + 23) := by
  let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  have hindex (q : Nat) :
      (truncatedRowsIterate q3 n r2 kWords q initial).i = q := by
    simpa [initial] using truncatedRowsIterate_i q3 n r2 kWords q initial
  have hindices : ∀ q, q < kWords + 1 →
      (truncatedRowsIterate q3 n r2 kWords q initial).i ≤ kWords := by
    intro q hq
    rw [hindex q]
    omega
  have hcontinue : ∀ q, q < kWords + 1 →
      (UInt256.ofNat (truncatedRowsIterate q3 n r2 kWords q initial).i).lt
        (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    intro q hq
    rw [hindex q, ult_one (by
      rw [UInt256.toNat_ofNat_of_lt (by omega : q < UInt256.size),
        UInt256.toNat_ofNat_of_lt hkWord]
      omega)]
    native_decide
  have hInitial : RDx runtimeBytecode ee g s0 ⟨6677⟩
      (truncatedOuterStack initial q3 n r2 returnPc product kWords tail)
      initial.memory initial.activeWords rdata acc steps gasUsed := by
    simpa only [initial] using h
  have rdRows := truncatedRowsExact initial hkPos hkWord hdepth hindices hcontinue hInitial
  have hfinalIndex : final.i = kWords + 1 := by
    simpa [final] using hindex (kWords + 1)
  have hguard : (UInt256.ofNat final.i).lt
      (UInt256.ofNat (kWords + 1)) = ⟨0⟩ := by
    rw [hfinalIndex]
    exact ult_zero (by omega)
  have rdRows' : RDx runtimeBytecode ee g s0 ⟨6677⟩
      (truncatedOuterStack final q3 n r2 returnPc product kWords tail)
      final.memory final.activeWords rdata acc
      (steps + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial)
      (gasUsed + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial) := by
    simpa only [final] using rdRows
  have rd6685 := GeneratedTraces.trace_6677_notTaken
    (tail := UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
      returnPc :: product :: tail)
    (by simp only [List.length_cons]; omega)
    rdRows' (by native_decide) hguard
  have normalized := rd6685.withIndices
    (k' := steps + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial + 6)
    (by omega)
    (C' := gasUsed + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial + 23)
    (by omega)
  simpa [final, initial] using normalized

end Modexp.MultiLimbBarrettTruncatedMul
