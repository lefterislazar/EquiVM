import Examples.Precompiles.Modexp.MultiLimbBarrettCompareContract

/-!
# Complete Barrett correction execution

This module composes the deployed at-most-two correction passes and final copy.  Both decisions are
computed from the evolving r2 memory, and every selected path retains its exact gas.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettCorrection

open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbBarrettCompare

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

structure BarrettPassResult where
  memory : ByteArray
  activeWords : UInt256
  borrow : UInt256
  steps : Nat
  gas : Nat

def runBarrettPass (mem : ByteArray) (aw n r2 : UInt256) (kWords : Nat) :
    BarrettPassResult :=
  let initial := correctionInitialState mem aw
  let beforeFinal := correctionIterate n r2 kWords initial
  {
    memory := correctionTerminalMemory beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat kWords) beforeFinal.borrow
    activeWords := correctionTerminalWords beforeFinal.activeWords r2
      (UInt256.ofNat kWords)
    borrow := (correctionTerminalStep beforeFinal.memory beforeFinal.activeWords r2
      (UInt256.ofNat kWords) beforeFinal.borrow).2
    steps := 59 * kWords + 48
    gas := correctionPassGas n r2 kWords initial }

/-- The pure pass record is exactly the concrete PC6794--PC6788 execution. -/
theorem runBarrettPassExact
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
    let pass := runBarrettPass mem aw n r2 kWords
    RDx runtimeBytecode ee g s0 ⟨6788⟩
      (UInt256.ofNat (kWords + 1) :: pass.borrow :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      pass.memory pass.activeWords rdata acc
      (steps + pass.steps) (gasUsed + pass.gas) := by
  have rd := correctionPassFromZeroExact hkWord hdepth h
  simpa [runBarrettPass] using rd

def correctionIterationSetupGas (aw r2 : UInt256) (kWords : Nat) : Nat :=
  40 + (Cₘ (correctionTopWords aw r2 kWords) - Cₘ aw)

structure BarrettCorrectionSelection where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

/-- Execute at most two selected subtractions, with both decisions exposed by computation. -/
def selectBarrettCorrection (fuel : Nat) (mem : ByteArray) (aw n r2 result : UInt256)
    (kWords : Nat) : Option BarrettCorrectionSelection :=
  let initialSetupGas := correctionSetupGas aw r2 kWords
  match selectBarrettDecision fuel mem aw n r2 result kWords with
  | none => none
  | some first =>
      if first.doSub then
        let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
        let secondSetupGas := correctionIterationSetupGas pass1.activeWords r2 kWords
        match selectBarrettDecision fuel pass1.memory pass1.activeWords n r2 result kWords with
        | none => none
        | some second =>
            if second.doSub then
              let pass2 := runBarrettPass second.memory second.activeWords n r2 kWords
              some {
                memory := barrettFinalMemory pass2.memory r2 result kWords
                activeWords := barrettFinalWords pass2.activeWords r2 result kWords
                steps := 24 + first.steps + pass1.steps + 15 + 14 + second.steps +
                  pass2.steps + 28
                gas := initialSetupGas + first.gas + pass1.gas + 56 + secondSetupGas +
                  second.gas + pass2.gas + 89 +
                    barrettCopyOpcodeGas pass2.activeWords r2 result kWords }
            else
              some {
                memory := second.memory
                activeWords := second.activeWords
                steps := 24 + first.steps + pass1.steps + 15 + 14 + second.steps
                gas := initialSetupGas + first.gas + pass1.gas + 56 + secondSetupGas +
                  second.gas }
      else
        some {
          memory := first.memory
          activeWords := first.activeWords
          steps := 24 + first.steps
          gas := initialSetupGas + first.gas }

/-- Both correction decisions are total when the descending comparison has one fuel unit per
modulus limb. The same bound suffices for the optional second pass. -/
theorem selectBarrettCorrection_exists
    {fuel kWords : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected, selectBarrettCorrection fuel mem aw n r2 result kWords = some selected := by
  rcases selectBarrettDecision_exists (mem := mem) (aw := aw) (n := n) (r2 := r2)
    (result := result) hkPos hfuel with ⟨first, hfirst⟩
  cases hdoFirst : first.doSub with
  | false =>
      simp [selectBarrettCorrection, hfirst, hdoFirst]
  | true =>
      let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
      rcases selectBarrettDecision_exists (mem := pass1.memory) (aw := pass1.activeWords)
        (n := n) (r2 := r2) (result := result) hkPos hfuel with ⟨second, hsecond⟩
      cases hdoSecond : second.doSub <;>
        simp [selectBarrettCorrection, hfirst, hdoFirst, pass1, hsecond, hdoSecond]

/-- Every successful two-pass selection executes from correction setup through the concrete copy. -/
theorem selectedBarrettCorrectionExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel kWords : Nat} {tail : List UInt256}
    {i borrow product n r2 returnPc result : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1017)
    (hselect : selectBarrettCorrection fuel mem aw n r2 result kWords = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨6708⟩
      (i :: borrow :: product :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6737⟩
      (returnPc :: result :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + selected.steps) (gasUsed + selected.gas) := by
  let initialSetupGas := correctionSetupGas aw r2 kWords
  simp only [selectBarrettCorrection] at hselect
  cases hfirst : selectBarrettDecision fuel mem aw n r2 result kWords with
  | none => rw [hfirst] at hselect; contradiction
  | some first =>
      rw [hfirst] at hselect
      have rd6756 := correctionSetupExact
        (tail := tail) (kWords := kWords) (by omega) h
      have rdFirst := selectedBarrettDecisionExact (fuel := fuel) (mem := mem) (aw := aw)
        (n := n) (r2 := r2) (result := result) (iter := ⟨0⟩)
        (returnPc := returnPc) (tail := tail) first hkPos hkWord
        (by omega) hfirst (by
          simpa [initialSetupGas, correctionSetupGas] using rd6756)
      cases hdoFirst : first.doSub with
      | false =>
          simp only [hdoFirst, Bool.false_eq_true, ↓reduceIte] at hselect
          injection hselect with hselected
          subst selected
          simp only [BarrettComparePost, hdoFirst, Bool.false_eq_true, ↓reduceIte] at rdFirst
          have normalized := rdFirst.withIndices
            (k' := steps + (24 + first.steps)) (by omega)
            (C' := gasUsed + (initialSetupGas + first.gas)) (by
              simp [initialSetupGas, correctionSetupGas, Nat.add_assoc])
          exact normalized
      | true =>
          simp only [hdoFirst, ↓reduceIte] at hselect
          simp only [BarrettComparePost, hdoFirst, ↓reduceIte] at rdFirst
          let pass1 := runBarrettPass first.memory first.activeWords n r2 kWords
          have rdPass1 := runBarrettPassExact hkWord (by omega) (by
            simpa [pass1] using rdFirst)
          have rd6738 := correctionFirstPassContinueExact
            (tail := tail) (kWords := kWords) (by omega) (by
              simpa [pass1] using rdPass1)
          have rd6756Second := correctionIterationSetupExact
            (tail := tail) (kWords := kWords) (by omega) (by
              simpa [pass1] using rd6738)
          let secondSetupGas := correctionIterationSetupGas pass1.activeWords r2 kWords
          cases hsecond : selectBarrettDecision fuel pass1.memory pass1.activeWords n r2
              result kWords with
          | none => rw [hsecond] at hselect; contradiction
          | some second =>
              rw [hsecond] at hselect
              have rdSecond := selectedBarrettDecisionExact (fuel := fuel)
                (mem := pass1.memory) (aw := pass1.activeWords) (n := n) (r2 := r2)
                (result := result) (iter := ⟨1⟩) (returnPc := returnPc) (tail := tail) second
                hkPos hkWord (by omega) hsecond (by
                  simpa [pass1, secondSetupGas, correctionIterationSetupGas,
                    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd6756Second)
              cases hdoSecond : second.doSub with
              | false =>
                  simp only [hdoSecond, Bool.false_eq_true, ↓reduceIte] at hselect
                  injection hselect with hselected
                  subst selected
                  simp only [BarrettComparePost, hdoSecond, Bool.false_eq_true,
                    ↓reduceIte] at rdSecond
                  have normalized := rdSecond.withIndices
                    (k' := steps +
                      (24 + first.steps + pass1.steps + 15 + 14 + second.steps))
                    (by simp only [pass1]; omega)
                    (C' := gasUsed +
                      (initialSetupGas + first.gas + pass1.gas + 56 + secondSetupGas +
                        second.gas)) (by
                      simp only [initialSetupGas, secondSetupGas, pass1,
                        correctionSetupGas, correctionIterationSetupGas]
                      omega)
                  exact normalized
              | true =>
                  simp only [hdoSecond, ↓reduceIte] at hselect
                  simp only [BarrettComparePost, hdoSecond, ↓reduceIte] at rdSecond
                  let pass2 := runBarrettPass second.memory second.activeWords n r2 kWords
                  have rdPass2 := runBarrettPassExact hkWord (by omega) (by
                    simpa [pass2] using rdSecond)
                  have rd6737 := correctionSecondPassCopyExact
                    (tail := tail) (kWords := kWords) (by omega) (by
                      simpa [pass2] using rdPass2)
                  injection hselect with hselected
                  subst selected
                  have normalized := rd6737.withIndices
                    (k' := steps +
                      (24 + first.steps + pass1.steps + 15 + 14 + second.steps +
                        pass2.steps + 28)) (by
                      simp only [pass1, pass2]
                      omega)
                    (C' := gasUsed +
                      (initialSetupGas + first.gas + pass1.gas + 56 + secondSetupGas +
                        second.gas + pass2.gas + 89 +
                          barrettCopyOpcodeGas pass2.activeWords r2 result kWords)) (by
                      simp only [initialSetupGas, secondSetupGas, pass1, pass2,
                        correctionSetupGas, correctionIterationSetupGas]
                      omega)
                  exact normalized

end Modexp.MultiLimbBarrettCorrection
