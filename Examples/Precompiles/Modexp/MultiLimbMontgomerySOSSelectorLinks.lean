import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSFinalizeContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSSemantic

/-! # Shared CIOS/SOS final-selector semantics -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryCompareTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 10000
set_option maxHeartbeats 500000

structure SOSCIOSCompareRelation
    (sos : SOSCompareSelection) (cios : CIOSCompareSelection) : Prop where
  tOff : cios.tOff = sos.tOff
  nOff : cios.nOff = sos.nOff
  activeWords : cios.activeWords = sos.activeWords
  doSub : cios.doSub = sos.doSub

/-- The SOS and CIOS descending-comparison selectors follow the same memory observations and
return the same semantic fields.  Their step/gas metadata remains backend-specific. -/
theorem selectedSOSCompare_to_CIOS
    {fuel : Nat} {mem : ByteArray} {tP activeWords tOff nOff prevTOff : UInt256}
    {selected : SOSCompareSelection}
    (hselect : selectSOSCompare fuel mem tP activeWords tOff nOff prevTOff =
      some selected) :
    ∃ cios, selectCIOSCompare fuel mem tP activeWords tOff nOff prevTOff =
        some cios ∧ SOSCIOSCompareRelation selected cios := by
  induction fuel generalizing activeWords tOff nOff prevTOff selected with
  | zero => simp [selectSOSCompare] at hselect
  | succ fuel ih =>
      simp only [selectSOSCompare] at hselect
      by_cases hgreater :
          (compareNWord mem activeWords tOff nOff).toNat <
            (compareTWord mem activeWords tOff).toNat
      · rw [if_pos hgreater] at hselect
        injection hselect with heq
        subst selected
        refine ⟨{
          tOff := tP
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨1⟩
          iterations := 1
          steps := 45
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 97 }, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
        simp [selectCIOSCompare, hgreater]
      · rw [if_neg hgreater] at hselect
        by_cases hless :
            (compareTWord mem activeWords tOff).toNat <
              (compareNWord mem activeWords tOff nOff).toNat
        · rw [if_pos hless] at hselect
          injection hselect with heq
          subst selected
          refine ⟨{
            tOff := tP
            nOff := comparePrev nOff
            activeWords := compareAw activeWords tOff nOff
            doSub := ⟨0⟩
            iterations := 1
            steps := 47
            gas := compareLoadGasAfter 0 activeWords tOff nOff + 101 }, ?_,
            ⟨rfl, rfl, rfl, rfl⟩⟩
          simp [selectCIOSCompare, hgreater, hless]
        · rw [if_neg hless] at hselect
          by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
          · rw [if_pos hguard] at hselect
            cases hrest : selectSOSCompare fuel mem tP
                (compareAw activeWords tOff nOff) prevTOff (comparePrev nOff)
                (comparePrev prevTOff) with
            | none =>
                rw [hrest] at hselect
                contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                obtain ⟨ciosRest, hciosRest, relation⟩ := ih hrest
                refine ⟨{
                  tOff := ciosRest.tOff
                  nOff := ciosRest.nOff
                  activeWords := ciosRest.activeWords
                  doSub := ciosRest.doSub
                  iterations := ciosRest.iterations + 1
                  steps := 39 + ciosRest.steps
                  gas := compareLoadGasAfter 0 activeWords tOff nOff + 77 +
                    ciosRest.gas }, ?_, ?_⟩
                · simp [selectCIOSCompare, hgreater, hless, hguard, hciosRest]
                · exact ⟨relation.tOff, relation.nOff, relation.activeWords,
                    relation.doSub⟩
          · rw [if_neg hguard] at hselect
            injection hselect with heq
            subst selected
            refine ⟨{
              tOff := prevTOff
              nOff := comparePrev nOff
              activeWords := compareAw activeWords tOff nOff
              doSub := ⟨1⟩
              iterations := 1
              steps := 39
              gas := compareLoadGasAfter 0 activeWords tOff nOff + 77 }, ?_,
              ⟨rfl, rfl, rfl, rfl⟩⟩
            simp [selectCIOSCompare, hgreater, hless, hguard]

def sosSubtractionState (selected : SOSSubtractionSelection) : SubtractionState := {
  leftPtr := selected.leftPtr
  rightPtr := selected.rightPtr
  borrow := selected.borrow
  memory := selected.memory
  activeWords := selected.activeWords }

/-- The SOS subtraction selector is the CIOS subtraction selector over the same pure transition;
only backend-specific step/gas totals differ. -/
theorem selectedSOSSubtraction_to_CIOS
    {fuel : Nat} {stop : UInt256} {mem : ByteArray}
    {aw leftPtr borrow rightPtr : UInt256} {selected : SOSSubtractionSelection}
    (hselect : selectSOSSubtraction fuel stop mem aw leftPtr borrow rightPtr =
      some selected) :
    ∃ cios, selectCIOSSubtraction fuel stop {
          leftPtr := leftPtr
          rightPtr := rightPtr
          borrow := borrow
          memory := mem
          activeWords := aw } = some cios ∧
        cios.final = sosSubtractionState selected := by
  induction fuel generalizing mem aw leftPtr borrow rightPtr selected with
  | zero => simp [selectSOSSubtraction] at hselect
  | succ fuel ih =>
      simp only [selectSOSSubtraction] at hselect
      let step := subtractionStep mem aw leftPtr rightPtr borrow
      let nextLeft := leftPtr + ⟨32⟩
      let nextRight := rightPtr + ⟨32⟩
      let nextMem := subtractionMemory mem aw leftPtr rightPtr borrow
      let nextAw := subtractionAw aw leftPtr rightPtr
      let next : SubtractionState := {
        leftPtr := nextLeft
        rightPtr := nextRight
        borrow := step.2
        memory := nextMem
        activeWords := nextAw }
      by_cases hcontinue : nextLeft.lt stop ≠ ⟨0⟩
      · rw [if_pos hcontinue] at hselect
        cases hrest : selectSOSSubtraction fuel stop nextMem nextAw nextLeft step.2
            nextRight with
        | none =>
            rw [hrest] at hselect
            contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            obtain ⟨ciosRest, hciosRest, hfinal⟩ := ih hrest
            refine ⟨{
              final := ciosRest.final
              iterations := ciosRest.iterations + 1
              steps := 35 + ciosRest.steps
              gas := subtractionGas aw leftPtr rightPtr + 10 + ciosRest.gas }, ?_, hfinal⟩
            simpa [selectCIOSSubtraction, subtractionAdvance, next, nextLeft,
              nextRight, nextMem, nextAw, step, hcontinue, hciosRest]
      · rw [if_neg hcontinue] at hselect
        injection hselect with heq
        subst selected
        refine ⟨{
          final := next
          iterations := 1
          steps := 35
          gas := subtractionGas aw leftPtr rightPtr + 10 }, ?_, rfl⟩
        simp [selectCIOSSubtraction, subtractionAdvance, next, nextLeft,
          nextRight, nextMem, nextAw, step, hcontinue]

/-- On a nonempty result range, the SOS copy/subtract selector and CIOS copy/subtract selector
produce identical memory and active-word states. -/
theorem selectedSOSCopy_to_CIOS
    (columns : Nat) {fuel : Nat} {mem : ByteArray}
    {aw source bytes doSub resultPtr nP resultBase : UInt256}
    {selected : SOSCopySelection}
    (hcolumns : 0 < columns)
    (hbytes : bytes.toNat = 32 * columns)
    (hstop : (⟨32⟩ + (bytes + resultBase)).toNat =
      resultPtr.toNat + 32 * columns)
    (hselect : selectSOSCopy fuel mem aw source bytes doSub resultPtr nP resultBase =
      some selected) :
    ∃ cios, selectCIOSCopy fuel mem aw source bytes doSub resultPtr nP resultBase =
        some cios ∧ cios.memory = selected.memory ∧
        cios.activeWords = selected.activeWords := by
  let copied := finalCopyMemory mem source resultPtr bytes
  let copiedAw := finalCopyAw aw source resultPtr bytes
  let copyGas := finalCopyGas aw source resultPtr bytes
  let sosStop := ⟨32⟩ + (resultBase + bytes)
  let ciosStop := ⟨32⟩ + (bytes + resultBase)
  have hstopEq : sosStop = ciosStop := by
    simp only [sosStop, ciosStop]
    rw [u256_add_comm resultBase bytes]
  unfold selectSOSCopy at hselect
  dsimp only at hselect
  by_cases hdoSub : doSub = ⟨0⟩
  · rw [if_pos hdoSub] at hselect
    injection hselect with heq
    subst selected
    refine ⟨{
      memory := copied
      activeWords := copiedAw
      steps := 11
      gas := copyGas + 24 }, ?_, rfl, rfl⟩
    simp [selectCIOSCopy, copied, copiedAw, copyGas, hdoSub]
  · rw [if_neg hdoSub] at hselect
    have hnonemptyNat : resultPtr.toNat < ciosStop.toNat := by
      rw [hstop]
      omega
    have hnonempty : resultPtr.lt sosStop ≠ ⟨0⟩ := by
      rw [hstopEq, ult_one hnonemptyNat]
      decide
    rw [if_neg hnonempty] at hselect
    cases hsub : selectSOSSubtraction fuel sosStop copied copiedAw resultPtr ⟨0⟩ nP with
    | none =>
        rw [hsub] at hselect
        contradiction
    | some sub =>
        rw [hsub] at hselect
        injection hselect with heq
        subst selected
        have hsub' : selectSOSSubtraction fuel ciosStop copied copiedAw resultPtr ⟨0⟩
            nP = some sub := by
          simpa only [hstopEq] using hsub
        obtain ⟨ciosSub, hciosSub, hfinal⟩ := selectedSOSSubtraction_to_CIOS hsub'
        refine ⟨{
          memory := ciosSub.final.memory
          activeWords := ciosSub.final.activeWords
          steps := 28 + ciosSub.steps
          gas := copyGas + 76 + ciosSub.gas }, ?_, ?_, ?_⟩
        · have hnonemptyCIOS : resultPtr.lt ciosStop ≠ ⟨0⟩ := by
            rw [ult_one hnonemptyNat]
            decide
          unfold selectCIOSCopy
          dsimp only
          rw [if_neg hdoSub, if_neg hnonemptyCIOS]
          change (match selectCIOSSubtraction fuel ciosStop {
              leftPtr := resultPtr
              rightPtr := nP
              borrow := ⟨0⟩
              memory := copied
              activeWords := copiedAw } with
            | none => (none : Option CIOSCopySelection)
            | some sub => some {
                memory := sub.final.memory
                activeWords := sub.final.activeWords
                steps := 28 + sub.steps
                gas := copyGas + 76 + sub.gas }) = _
          rw [hciosSub]
        · rw [hfinal]
          rfl
        · rw [hfinal]
          rfl

end Modexp.MultiLimbMontgomerySOSSemantic
