import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFinalizeTop

/-! # Exact SOS copy and conditional subtraction -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSFinalize

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryFinalize

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

structure SOSSubtractionSelection where
  leftPtr : UInt256
  borrow : UInt256
  rightPtr : UInt256
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

@[irreducible] def SOSSubtractionExitPost
    (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (leftPtr borrow rightPtr stop returnPc resultBase : UInt256)
    (tail : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : Nat) : Prop :=
  RDx runtimeBytecode ee g s0 ⟨7378⟩
    (leftPtr :: borrow :: rightPtr :: stop ::
      returnPc :: resultBase :: tail)
    mem aw rdata acc k C

/-- Follow every deployed subtraction guard with explicit fuel. -/
def selectSOSSubtraction (fuel : Nat) (stop : UInt256)
    (mem : ByteArray) (aw leftPtr borrow rightPtr : UInt256) :
    Option SOSSubtractionSelection :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let step := subtractionStep mem aw leftPtr rightPtr borrow
      let nextLeft := leftPtr + ⟨32⟩
      let nextRight := rightPtr + ⟨32⟩
      let nextMem := subtractionMemory mem aw leftPtr rightPtr borrow
      let nextAw := subtractionAw aw leftPtr rightPtr
      let columnGas := subtractionGas aw leftPtr rightPtr + 10
      if nextLeft.lt stop ≠ ⟨0⟩ then
        match selectSOSSubtraction fuel stop nextMem nextAw nextLeft step.2 nextRight with
        | none => none
        | some rest => some {
            leftPtr := rest.leftPtr
            borrow := rest.borrow
            rightPtr := rest.rightPtr
            memory := rest.memory
            activeWords := rest.activeWords
            steps := 35 + rest.steps
            gas := columnGas + rest.gas }
      else
        some {
          leftPtr := nextLeft
          borrow := step.2
          rightPtr := nextRight
          memory := nextMem
          activeWords := nextAw
          steps := 35
          gas := columnGas }

/-- The subtraction selector reaches the cleanup block with exact memory, steps, and gas. -/
theorem selectedSOSSubtractionExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {stop returnPc resultBase : UInt256}
    {mem : ByteArray} {aw leftPtr borrow rightPtr : UInt256}
    (selected : SOSSubtractionSelection)
    (hdepth : tail.length + 6 ≤ 1017)
    (hselect : selectSOSSubtraction fuel stop mem aw leftPtr borrow rightPtr =
      some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7383⟩
      (leftPtr :: borrow :: rightPtr :: stop :: returnPc :: resultBase :: tail)
      mem aw rdata acc k C) :
    SOSSubtractionExitPost ee g s0 selected.leftPtr selected.borrow selected.rightPtr
      stop returnPc resultBase tail selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing mem aw leftPtr borrow rightPtr selected k C with
  | zero => simp [selectSOSSubtraction] at hselect
  | succ fuel ih =>
      simp only [selectSOSSubtraction] at hselect
      let step := subtractionStep mem aw leftPtr rightPtr borrow
      let nextLeft := leftPtr + ⟨32⟩
      let nextRight := rightPtr + ⟨32⟩
      let nextMem := subtractionMemory mem aw leftPtr rightPtr borrow
      let nextAw := subtractionAw aw leftPtr rightPtr
      let columnGas := subtractionGas aw leftPtr rightPtr + 10
      by_cases hcontinue : nextLeft.lt stop ≠ ⟨0⟩
      · rw [if_pos hcontinue] at hselect
        cases hrest : selectSOSSubtraction fuel stop nextMem nextAw nextLeft step.2
            nextRight with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            cases hselect
            have rd7384 := subtractionBody (by simpa using hdepth) h
            have rd7390 := rd7384.jumpiT (by native_decide) hcontinue
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdFinal := ih rest hrest (by
              simpa [nextMem, nextAw, nextLeft, nextRight, step] using rd7390)
            have normalized : SOSSubtractionExitPost ee g s0
                rest.leftPtr rest.borrow rest.rightPtr stop returnPc resultBase tail
                rest.memory rest.activeWords rdata acc
                (k + (35 + rest.steps)) (C + (columnGas + rest.gas)) := by
              simpa [columnGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using rdFinal
            exact normalized
      · rw [if_neg hcontinue] at hselect
        cases hselect
        have rd7384 := subtractionBody (by simpa using hdepth) h
        have hexit : nextLeft.lt stop = ⟨0⟩ := by
          by_contra hne
          exact hcontinue hne
        have rd7385 := rd7384.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        have normalized := rd7385.withIndices
          (k' := k + 35) (C' := C + columnGas) (by ring) (by
            simp [columnGas]
            ring)
        simpa [SOSSubtractionExitPost, nextLeft, nextRight, nextMem, nextAw, step]
          using normalized

structure SOSCopySelection where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

/-- False subtraction decisions return after copy; true decisions select every subtraction
column.  The initial empty-range branch is included for totality. -/
def selectSOSCopy (fuel : Nat) (mem : ByteArray)
    (aw source bytes doSub resultPtr nP resultBase : UInt256) :
    Option SOSCopySelection :=
  let copied := finalCopyMemory mem source resultPtr bytes
  let copiedAw := finalCopyAw aw source resultPtr bytes
  let copyGas := finalCopyGas aw source resultPtr bytes
  let stop := ⟨32⟩ + (resultBase + bytes)
  if doSub = ⟨0⟩ then
    some {
      memory := copied
      activeWords := copiedAw
      steps := 11
      gas := copyGas + 24 }
  else if resultPtr.lt stop = ⟨0⟩ then
    some {
      memory := copied
      activeWords := copiedAw
      steps := 27
      gas := copyGas + 73 }
  else
    match selectSOSSubtraction fuel stop copied copiedAw resultPtr ⟨0⟩ nP with
    | none => none
    | some sub => some {
        memory := sub.memory
        activeWords := sub.activeWords
        steps := 27 + sub.steps
        gas := copyGas + 73 + sub.gas }

@[irreducible] def SOSCopyReturnPost
    (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (returnPc resultBase : UInt256) (tail : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : Nat) : Prop :=
  RDx runtimeBytecode ee g s0 returnPc (resultBase :: tail) mem aw rdata acc k C

theorem sosCopyBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {tOff nOff source bytes doSub resultPtr : UInt256}
    (hdepth : tail.length + 6 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨7347⟩
      (tOff :: nOff :: source :: bytes :: doSub :: resultPtr :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7355⟩
      (⟨7360⟩ :: doSub :: resultPtr :: tail)
      (finalCopyMemory mem source resultPtr bytes)
      (finalCopyAw aw source resultPtr bytes) rdata acc (k + 6)
      (C + finalCopyGas aw source resultPtr bytes) := by
  have rd := GeneratedTraces.trace_7347_body hdepth h
  simpa [finalCopyMemory, finalCopyAw, finalCopyGas,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- Every successful copy/subtraction selection returns to the caller exactly. -/
theorem selectedSOSCopyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {tOff nOff source bytes doSub resultPtr nP returnPc resultBase : UInt256}
    (selected : SOSCopySelection)
    (hdepth : tail.length + 10 ≤ 1021)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectSOSCopy fuel mem aw source bytes doSub resultPtr nP resultBase =
      some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7347⟩
      (tOff :: nOff :: source :: bytes :: doSub :: resultPtr :: nP :: bytes ::
        returnPc :: resultBase :: tail)
      mem aw rdata acc k C) :
    SOSCopyReturnPost ee g s0 returnPc resultBase tail selected.memory
      selected.activeWords rdata acc (k + selected.steps) (C + selected.gas) := by
  let copied := finalCopyMemory mem source resultPtr bytes
  let copiedAw := finalCopyAw aw source resultPtr bytes
  let copyGas := finalCopyGas aw source resultPtr bytes
  let stop := ⟨32⟩ + (resultBase + bytes)
  unfold selectSOSCopy at hselect
  dsimp only at hselect
  have rd7362 := sosCopyBody (tail := nP :: bytes :: returnPc :: resultBase :: tail)
    (by simp only [List.length_cons]; omega) h
  by_cases hdoSub : doSub = ⟨0⟩
  · rw [if_pos hdoSub] at hselect
    cases hselect
    have rd7363 := rd7362.jumpiNT (by native_decide) hdoSub
      (by simp only [List.length_cons]; omega)
    have rd7366 := GeneratedTraces.trace_7356_body
      (tail := resultBase :: tail) (by simp only [List.length_cons]; omega) (by
        simpa using rd7363)
    have rdReturn := rd7366.jump (by native_decide) hreturn
      (by simp only [List.length_cons]; omega)
    have normalized := rdReturn.withIndices
      (k' := k + 11) (C' := C + (copyGas + 24)) (by ring) (by
        simp [copyGas]
        ring)
    simpa [SOSCopyReturnPost, copied, copiedAw, copyGas] using normalized
  · rw [if_neg hdoSub] at hselect
    have hdoSubNZ : doSub ≠ ⟨0⟩ := hdoSub
    have rd7367 := rd7362.jumpiT (by native_decide) hdoSubNZ
      (by native_decide) (by simp only [List.length_cons]; omega)
    have rd7384 := GeneratedTraces.trace_7360_body
      (tail := tail) (by omega) (by
        simpa [stop] using rd7367)
    by_cases hempty : resultPtr.lt stop = ⟨0⟩
    · rw [if_pos hempty] at hselect
      cases hselect
      have rd7385 := rd7384.jumpiNT (by native_decide) hempty
        (by simp only [List.length_cons]; omega)
      have rd7389 := GeneratedTraces.trace_7378_body
        (tail := resultBase :: tail) (by simp only [List.length_cons]; omega) (by
          simpa [stop] using rd7385)
      have rdReturn := rd7389.jump (by native_decide) hreturn
        (by simp only [List.length_cons]; omega)
      have normalized := rdReturn.withIndices
        (k' := k + 27) (C' := C + (copyGas + 73)) (by ring) (by
          simp [copyGas]
          ring)
      simpa [SOSCopyReturnPost, copied, copiedAw, copyGas] using normalized
    · rw [if_neg hempty] at hselect
      cases hsub : selectSOSSubtraction fuel stop copied copiedAw resultPtr ⟨0⟩ nP with
      | none => rw [hsub] at hselect; contradiction
      | some sub =>
          rw [hsub] at hselect
          cases hselect
          have rd7390 := rd7384.jumpiT (by native_decide) hempty
            (by native_decide) (by simp only [List.length_cons]; omega)
          have rd7385 := selectedSOSSubtractionExact
            (tail := tail) (stop := stop) (returnPc := returnPc)
            (resultBase := resultBase) sub (by omega) hsub (by
            simpa [SOSSubtractionExitPost, copied, copiedAw, stop] using rd7390)
          have rd7389 := GeneratedTraces.trace_7378_body
            (tail := resultBase :: tail) (by simp only [List.length_cons]; omega) (by
              simpa [SOSSubtractionExitPost, stop] using rd7385)
          have rdReturn := rd7389.jump (by native_decide) hreturn
            (by simp only [List.length_cons]; omega)
          have normalized := rdReturn.withIndices
            (k' := k + (27 + sub.steps))
            (C' := C + (copyGas + 73 + sub.gas)) (by ring) (by ring)
          simpa [SOSCopyReturnPost, copyGas, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using normalized

end Modexp.MultiLimbMontgomerySOSFinalize
