import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFinalizeSelector

/-! # Total exact SOS top-word and comparison selector -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSFinalize

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryCompareTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def sosFinalTopPtr (sBase bytes : UInt256) : UInt256 := sBase + bytes

def sosFinalTopWord (mem : ByteArray) (aw sBase bytes : UInt256) : UInt256 :=
  readWord mem aw (sosFinalTopPtr sBase bytes)

def sosFinalTopAw (aw sBase bytes : UInt256) : UInt256 :=
  readWords1 aw (sosFinalTopPtr sBase bytes)

def sosFinalTopGas (aw sBase bytes : UInt256) : Nat :=
  42 + (Cₘ (sosFinalTopAw aw sBase bytes) - Cₘ aw)

structure SOSFinalCompareSelection where
  tOff : UInt256
  nOff : UInt256
  activeWords : UInt256
  doSub : UInt256
  steps : Nat
  gas : Nat

/-- Select top-word, empty-width, or descending-comparison finalization. -/
def selectSOSFinalCompare (fuel : Nat) (mem : ByteArray)
    (aw sBase bytes nEnd : UInt256) : Option SOSFinalCompareSelection :=
  let topPtr := sosFinalTopPtr sBase bytes
  let topAw := sosFinalTopAw aw sBase bytes
  let topGas := sosFinalTopGas aw sBase bytes
  if sosFinalTopWord mem aw sBase bytes ≠ ⟨0⟩ then
    some {
      tOff := topPtr
      nOff := nEnd
      activeWords := topAw
      doSub := ⟨1⟩
      steps := 16
      gas := topGas + 10 }
  else if topPtr.gt sBase = ⟨0⟩ then
    some {
      tOff := topPtr
      nOff := nEnd
      activeWords := topAw
      doSub := ⟨1⟩
      steps := 27
      gas := 10 + (25 + (topGas + 10)) }
  else
    match selectSOSCompare fuel mem sBase topAw topPtr nEnd (comparePrev topPtr) with
    | none => none
    | some compared => some {
        tOff := compared.tOff
        nOff := compared.nOff
        activeWords := compared.activeWords
        doSub := compared.doSub
        steps := 27 + compared.steps
        gas := compared.gas + (10 + (10 + (25 + topGas))) }

/-- A successful top/comparison selection reaches the common copy block exactly. -/
theorem selectedSOSFinalCompareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 sBase bytes nEnd resultPtr nP : UInt256}
    (selected : SOSFinalCompareSelection)
    (hdepth : tail.length + 9 ≤ 1018)
    (hselect : selectSOSFinalCompare fuel mem aw sBase bytes nEnd = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7329⟩
      (drop0 :: drop1 :: drop2 :: sBase :: bytes :: nEnd ::
        resultPtr :: nP :: bytes :: tail)
      mem aw rdata acc k C) :
    SOSComparePost ee g s0 selected.tOff selected.nOff sBase bytes
      selected.doSub resultPtr nP tail mem selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  let topPtr := sosFinalTopPtr sBase bytes
  let topAw := sosFinalTopAw aw sBase bytes
  let topGas := sosFinalTopGas aw sBase bytes
  unfold selectSOSFinalCompare at hselect
  dsimp only at hselect
  have rd7353 := GeneratedTraces.trace_7329_body
    (tail := resultPtr :: nP :: bytes :: tail)
    (by simp only [List.length_cons]; omega) h
  by_cases htop : sosFinalTopWord mem aw sBase bytes ≠ ⟨0⟩
  · rw [if_pos htop] at hselect
    cases hselect
    have hiszero : (sosFinalTopWord mem aw sBase bytes).isZero = ⟨0⟩ :=
      isZero_eq_zero_of_ne htop
    have hflag : (sosFinalTopWord mem aw sBase bytes).isZero.isZero = ⟨1⟩ := by
      rw [hiszero]
      native_decide
    have hiszeroRaw := hiszero
    simp only [sosFinalTopWord, sosFinalTopPtr, readWord] at hiszeroRaw
    have hflagRaw := hflag
    simp only [sosFinalTopWord, sosFinalTopPtr, readWord] at hflagRaw
    have rd7354 := rd7353.jumpiNT (by native_decide) hiszeroRaw
      (by simp only [List.length_cons]; omega)
    rw [hflagRaw] at rd7354
    have normalized := rd7354.withIndices
      (k' := k + 16) (C' := C + (topGas + 10)) (by ring) (by
        simp [topGas, sosFinalTopGas, sosFinalTopAw, sosFinalTopPtr,
          readWords1]
        ring)
    simpa [SOSComparePost, topPtr, topAw,
      show (⟨7346⟩ : UInt256) + ⟨1⟩ = ⟨7347⟩ by native_decide,
      sosFinalTopWord, sosFinalTopPtr, readWord] using normalized
  · rw [if_neg htop] at hselect
    have htopZero : sosFinalTopWord mem aw sBase bytes = ⟨0⟩ := by
      by_contra hne
      exact htop hne
    have hiszero : (sosFinalTopWord mem aw sBase bytes).isZero = ⟨1⟩ := by
      rw [htopZero]
      native_decide
    have hflag : (sosFinalTopWord mem aw sBase bytes).isZero.isZero = ⟨0⟩ := by
      rw [hiszero]
      native_decide
    have hiszeroRaw := hiszero
    simp only [sosFinalTopWord, sosFinalTopPtr, readWord] at hiszeroRaw
    have hflagRaw := hflag
    simp only [sosFinalTopWord, sosFinalTopPtr, readWord] at hflagRaw
    have rd7422 := rd7353.jumpiT (by native_decide) (by
        rw [hiszeroRaw]
        native_decide)
      (by native_decide) (by simp only [List.length_cons]; omega)
    rw [hflagRaw] at rd7422
    have rd7435 := GeneratedTraces.trace_7415_body
      (tail := resultPtr :: nP :: bytes :: tail)
      (by simp only [List.length_cons]; omega) (by
        simpa [topPtr, sosFinalTopPtr] using rd7422)
    by_cases hempty : topPtr.gt sBase = ⟨0⟩
    · rw [if_pos hempty] at hselect
      cases hselect
      have rd7354 := rd7435.jumpiT (by native_decide) (by
          have hemptyRaw : (sBase + bytes).gt sBase = ⟨0⟩ := by
            simpa [topPtr, sosFinalTopPtr] using hempty
          rw [hemptyRaw]
          native_decide)
        (by native_decide) (by simp only [List.length_cons]; omega)
      have normalized := rd7354.withIndices
        (k' := k + 27) (C' := C + (10 + (25 + (topGas + 10)))) (by ring) (by
          simp [topGas, sosFinalTopGas, sosFinalTopAw, sosFinalTopPtr,
            readWords1]
          ring)
      simpa [SOSComparePost, topPtr, topAw, sosFinalTopPtr] using normalized
    · rw [if_neg hempty] at hselect
      cases hcompare : selectSOSCompare fuel mem sBase topAw topPtr nEnd
          (comparePrev topPtr) with
      | none => rw [hcompare] at hselect; contradiction
      | some compared =>
          rw [hcompare] at hselect
          cases hselect
          have rd7436 := rd7435.jumpiNT (by native_decide) (by
              have hnonzero : (sBase + bytes).gt sBase ≠ ⟨0⟩ := by
                simpa [topPtr, sosFinalTopPtr] using hempty
              rw [isZero_eq_zero_of_ne hnonzero])
            (by simp only [List.length_cons]; omega)
          have rd7354 := selectedSOSCompareExact
            (fuel := fuel) (activeWords := topAw) (tOff := topPtr)
            (nOff := nEnd) (prevTOff := comparePrev topPtr)
            (selected := compared) (tP := sBase) (junk := bytes)
            (resultPtr := resultPtr) (nP := nP) (bytes := bytes)
            (tail := tail) (by omega) rfl hcompare (by
              simpa [SOSComparePost, topPtr] using rd7436)
          simpa [topGas, sosFinalTopGas, sosFinalTopAw, sosFinalTopPtr,
            readWords1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7354

end Modexp.MultiLimbMontgomerySOSFinalize
