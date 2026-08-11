import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSReductionLoopContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFinalizeContract
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFull
import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSOffDiagonalLoopContract

/-! # End-to-end SOS Montgomery arithmetic contract -/

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Modexp.MultiLimbMontgomerySOSSemantic

open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbMontgomerySOSTrace
open Modexp.MultiLimbMontgomerySOSExecutable
open Modexp.MultiLimbMontgomerySOSFull
open Modexp.MultiLimbMontgomerySOSCall

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem square_lt_modulus_mul_radix_add_one
    {operand modulus radix words : Nat}
    (hoperand : operand < modulus) (hmodulus : modulus < radix ^ words) :
    operand ^ 2 < modulus * (radix ^ words + 1) := by
  have hleft : operand * operand < modulus * modulus := by
    exact Nat.mul_self_lt_mul_self hoperand
  have hright : modulus * modulus < modulus * (radix ^ words + 1) := by
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  simpa [pow_two] using hleft.trans hright

/-- A successful exposed square selector supplies the exact square and all invariants required
by the complete selected reduction-loop theorem. -/
theorem selectedSOSSquare_reduction_facts
    (words : Nat) {doubleFuel diagonalFuel reductionFuel columnFuel carryFuel : Nat}
    {mem : ByteArray} {aw sEnd aP aEnd sP n0inv kWords nBefore nP : UInt256}
    {selected : SOSSquareSelection}
    (modulus operand : Nat)
    (hwords : 0 < words)
    (hsEnd : sEnd.toNat = sP.toNat + 32 * (2 * words + 1))
    (haEnd : aEnd.toNat = aP.toNat + 32 * words)
    (haFit : aP.toNat + 32 * words + 31 < UInt256.size)
    (hsFit : sP.toNat + 32 * (2 * words + 1) + 31 < UInt256.size)
    (haSeparate : aEnd.toNat ≤ sP.toNat)
    (hsRange : sP.toNat + 32 * (2 * words + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hoffDiagonal : Modexp.wordLimbsToNat
          (memoryWordsFrom mem sP.toNat (2 * words + 1)) =
        Modexp.sosOffDiagonal UInt256.size
          ((memoryWordsFrom mem aP.toNat words).map UInt256.toNat))
    (hsKEnd : (sP + kWords).toNat = sP.toNat + 32 * words)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : (nBefore + kWords + ⟨32⟩).toNat = nP.toNat + 32 * words)
    (hnFit : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) + 31 < UInt256.size)
    (hnRange : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ mem.size)
    (hnSeparate : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ sP.toNat + 32)
    (hnScratchSeparate : nP.toNat + 32 * words ≤ sP.toNat)
    (hmodulus : Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat words) = modulus)
    (hinv : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hoperand : Modexp.wordLimbsToNat (memoryWordsFrom mem aP.toNat words) = operand)
    (hoperandReduced : operand < modulus)
    (hselect : selectSOSSquare doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      mem aw sEnd aP aEnd sP n0inv kWords nBefore nP = some selected) :
    let reductionState : SOSReductionLoopState := {
      sBase := sP
      memory := selected.diagonal.final.memory
      activeWords := selected.diagonal.final.activeWords }
    SOSReductionLoopFacts words words reductionState.memory reductionState nP n0inv modulus
        selected.reduction ∧
      Modexp.wordLimbsToNat (memoryWordsFrom reductionState.memory nP.toNat words) =
        modulus ∧
      Modexp.wordLimbsToNat
          (memoryWordsFrom reductionState.memory reductionState.sBase.toNat
            (words + words + 1)) = operand ^ 2 := by
  let doubleState : SOSDoubleState := {
    carry := ⟨0⟩
    ptr := sP
    memory := mem
    activeWords := aw }
  unfold selectSOSSquare at hselect
  dsimp only at hselect
  cases hdouble : selectSOSDoublePhase doubleFuel sEnd doubleState with
  | none => rw [hdouble] at hselect; contradiction
  | some double =>
      rw [hdouble] at hselect
      dsimp only at hselect
      let diagonalState : SOSDiagonalLoopState := {
        sOff := sP
        aOff := aP
        memory := double.final.memory
        activeWords := double.final.activeWords }
      cases hdiagonal : selectSOSDiagonalLoop diagonalFuel carryFuel aEnd kWords kWords
          diagonalState with
      | none => rw [hdiagonal] at hselect; contradiction
      | some diagonal =>
          rw [hdiagonal] at hselect
          dsimp only at hselect
          let reductionState : SOSReductionLoopState := {
            sBase := sP
            memory := diagonal.final.memory
            activeWords := diagonal.final.activeWords }
          cases hreduction : selectSOSReductionLoop reductionFuel columnFuel carryFuel nP
              n0inv nBefore (nBefore + kWords + ⟨32⟩) (sP + kWords) reductionState with
          | none => rw [hreduction] at hselect; contradiction
          | some reduction =>
              rw [hreduction] at hselect
              injection hselect with heq
              subst selected
              have hsquare := selectedSOSSquarePhases_value words hsEnd haEnd haFit hsFit
                haSeparate hsRange hcovered hawFit hoffDiagonal
                (by simpa only [doubleState] using hdouble)
                (by simpa only [diagonalState] using hdiagonal)
              have hmodulusDiagonal : Modexp.wordLimbsToNat
                  (memoryWordsFrom diagonal.final.memory nP.toNat words) = modulus := by
                rw [hsquare.2.2.2.2 nP.toNat words hnScratchSeparate, hmodulus]
              have hmodulusLt : modulus < UInt256.size ^ words := by
                rw [← hmodulus]
                have hbound := Modexp.wordLimbsToNat_lt_pow
                  (memoryWordsFrom mem nP.toNat words)
                simpa only [memoryWordsFrom_length] using hbound
              have hsquareBound : Modexp.wordLimbsToNat
                    (memoryWordsFrom diagonal.final.memory sP.toNat (2 * words + 1)) <
                  modulus * (UInt256.size ^ words + 1) := by
                rw [hsquare.1, hoperand]
                exact square_lt_modulus_mul_radix_add_one hoperandReduced hmodulusLt
              have hreductionFacts : SOSReductionLoopFacts words words
                  reductionState.memory reductionState nP n0inv modulus reduction :=
                selectedSOSReductionLoop_facts_of_coverage words words modulus hwords
                hnNext hnBefore hnEnd hsKEnd hsquare.2.1 hsquare.2.2.1
                (by change sP.toNat + 32 * (words + words + 1) + 31 < _; omega)
                (by
                  change sP.toNat + 32 * (words + words + 1) ≤ diagonal.final.memory.size
                  rw [hsquare.2.2.2.1]
                  omega) hnFit
                (by rw [hsquare.2.2.2.1]; exact hnRange) hnSeparate hmodulusDiagonal hinv
                (by
                  rw [show words + words + 1 = 2 * words + 1 by omega]
                  exact hsquareBound) hreduction
              have hsquareInitial : Modexp.wordLimbsToNat
                    (memoryWordsFrom diagonal.final.memory sP.toNat
                      (words + words + 1)) = operand ^ 2 := by
                rw [show words + words + 1 = 2 * words + 1 by omega,
                  hsquare.1, hoperand]
              exact ⟨hreductionFacts, hmodulusDiagonal, hsquareInitial⟩

/-- The exposed executable selector, including its final compare/copy branches, computes the
pure Montgomery square.  Exact execution and gas for the same selector are provided by
`selectedSOSExecutableExact`. -/
theorem selectedSOSExecutable_value
    (words : Nat)
    {doubleFuel diagonalFuel reductionFuel columnFuel carryFuel compareFuel subFuel : Nat}
    {mem : ByteArray} {aw sEnd aP aEnd sP n0inv kWords nBefore nP resultPtr
      resultBase : UInt256}
    {selected : SOSExecutableSelection}
    (modulus rInv operand : Nat)
    (hwords : 0 < words)
    (hsEnd : sEnd.toNat = sP.toNat + 32 * (2 * words + 1))
    (haEnd : aEnd.toNat = aP.toNat + 32 * words)
    (haFit : aP.toNat + 32 * words + 31 < UInt256.size)
    (hsFit : sP.toNat + 32 * (2 * words + 1) + 31 < UInt256.size)
    (haSeparate : aEnd.toNat ≤ sP.toNat)
    (hsRange : sP.toNat + 32 * (2 * words + 1) ≤ mem.size)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hoffDiagonal : Modexp.wordLimbsToNat
          (memoryWordsFrom mem sP.toNat (2 * words + 1)) =
        Modexp.sosOffDiagonal UInt256.size
          ((memoryWordsFrom mem aP.toNat words).map UInt256.toNat))
    (hsKEnd : (sP + kWords).toNat = sP.toNat + 32 * words)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : (nBefore + kWords + ⟨32⟩).toNat = nP.toNat + 32 * words)
    (hnFit : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) + 31 < UInt256.size)
    (hnRange : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ mem.size)
    (hnSeparate : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ sP.toNat + 32)
    (hnScratchSeparate : nP.toNat + 32 * words ≤ sP.toNat)
    (hmodulus : Modexp.wordLimbsToNat (memoryWordsFrom mem nP.toNat words) = modulus)
    (hmodulusPos : 0 < modulus)
    (hinv : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hoperand : Modexp.wordLimbsToNat (memoryWordsFrom mem aP.toNat words) = operand)
    (hoperandReduced : operand < modulus)
    (hinvR : UInt256.size ^ words * rInv % modulus = 1 % modulus)
    (geometry : SOSFinalizeGeometry words selected.square.reduction.final.memory
      selected.square.reduction.final.activeWords nBefore
      selected.square.reduction.final.sBase kWords (nBefore + kWords + ⟨32⟩) nP
      resultPtr resultBase)
    (hselect : selectSOSExecutable doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel mem aw sEnd aP aEnd sP n0inv kWords nBefore nP
      resultPtr resultBase = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.copy.memory resultPtr.toNat words) =
      (operand * operand * rInv) % modulus := by
  unfold selectSOSExecutable at hselect
  cases hsquare : selectSOSSquare doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel mem aw sEnd aP aEnd sP n0inv kWords nBefore nP with
  | none => rw [hsquare] at hselect; contradiction
  | some square =>
      rw [hsquare] at hselect
      dsimp only at hselect
      cases hcompare : selectSOSFinalCompare compareFuel square.reduction.final.memory
          square.reduction.final.activeWords square.reduction.final.sBase kWords
          (nBefore + kWords + ⟨32⟩) with
      | none => rw [hcompare] at hselect; contradiction
      | some compared =>
          rw [hcompare] at hselect
          dsimp only at hselect
          cases hcopy : selectSOSCopy subFuel square.reduction.final.memory
              compared.activeWords square.reduction.final.sBase kWords compared.doSub
              resultPtr nP resultBase with
          | none => rw [hcopy] at hselect; contradiction
          | some copy =>
              rw [hcopy] at hselect
              injection hselect with heq
              subst selected
              have hsquareFacts := selectedSOSSquare_reduction_facts words modulus operand
                hwords hsEnd haEnd haFit hsFit haSeparate hsRange hcovered hawFit
                hoffDiagonal hsKEnd hnNext hnBefore hnEnd hnFit hnRange hnSeparate
                hnScratchSeparate hmodulus hinv hoperand hoperandReduced hsquare
              let reductionState : SOSReductionLoopState := {
                sBase := sP
                memory := square.diagonal.final.memory
                activeWords := square.diagonal.final.activeWords }
              have hfinal := selectedSOSFinalize_value words square.reduction.final.memory
                square.reduction.final.activeWords nBefore square.reduction.final.sBase
                kWords (nBefore + kWords + ⟨32⟩) nP resultPtr resultBase compared copy
                geometry hcompare hcopy
              have hcandidate := geometry.candidate_eq_memoryWords
              have hfinalModulus : Modexp.wordLimbsToNat
                  (memoryWordsFrom square.reduction.final.memory nP.toNat words) =
                  modulus := by
                rw [hsquareFacts.1.modulusFrame, hsquareFacts.2.1]
              rw [hcandidate, hsquareFacts.1.value, hfinalModulus] at hfinal
              rw [hfinal]
              have hscanBound : Modexp.montgomerySOSScan UInt256.size modulus
                    n0inv.toNat
                    (Modexp.wordLimbsToNat
                      (memoryWordsFrom reductionState.memory reductionState.sBase.toNat
                        (words + words + 1))) words <
                  2 * modulus := by
                rw [← hsquareFacts.1.value]
                exact hsquareFacts.1.bound
              exact Modexp.montgomerySOS_contract (by decide) hmodulusPos hinv
                hsquareFacts.2.2 hinvR hscanBound

/-- The exposed full selector computes the pure Montgomery square from zeroed scratch memory.
Together with `selectedSOSFullExact`, this gives semantic output and exact gas for one and the
same complete selector. -/
theorem selectedSOSFull_value
    (words : Nat)
    {rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      compareFuel subFuel : Nat}
    {state : SOSOffDiagonalLoopState}
    {sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase : UInt256}
    {selected : SOSFullSelection}
    (modulus rInv operand : Nat)
    (hwords : 0 < words)
    (haStart : state.aOff = aP)
    (hsStart : state.sRow.toNat = sP.toNat + 32)
    (hsEnd : sEnd.toNat = sP.toNat + 32 * (2 * words + 1))
    (haEnd : aEnd.toNat = aP.toNat + 32 * words)
    (haFit : aP.toNat + 32 * words + 31 < UInt256.size)
    (hsFit : sP.toNat + 32 * (2 * words + 1) + 31 < UInt256.size)
    (haSeparate : aEnd.toNat ≤ sP.toNat)
    (hsRange : sP.toNat + 32 * (2 * words + 1) ≤ state.memory.size)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hzero : memoryWordsFrom state.memory sP.toNat (2 * words + 1) =
      List.replicate (2 * words + 1) (⟨0⟩ : UInt256))
    (hsKEnd : (sP + kWords).toNat = sP.toNat + 32 * words)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : (nBefore + kWords + ⟨32⟩).toNat = nP.toNat + 32 * words)
    (hnFit : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) + 31 < UInt256.size)
    (hnRange : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ state.memory.size)
    (hnSeparate : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ sP.toNat + 32)
    (hnScratchSeparate : nP.toNat + 32 * words ≤ sP.toNat)
    (hmodulus : Modexp.wordLimbsToNat
      (memoryWordsFrom state.memory nP.toNat words) = modulus)
    (hmodulusPos : 0 < modulus)
    (hinv : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hoperand : Modexp.wordLimbsToNat
      (memoryWordsFrom state.memory aP.toNat words) = operand)
    (hoperandReduced : operand < modulus)
    (hinvR : UInt256.size ^ words * rInv % modulus = 1 % modulus)
    (geometry : SOSFinalizeGeometry words selected.suffix.square.reduction.final.memory
      selected.suffix.square.reduction.final.activeWords nBefore
      selected.suffix.square.reduction.final.sBase kWords (nBefore + kWords + ⟨32⟩) nP
      resultPtr resultBase)
    (hselect : selectSOSFull rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel state sEnd aP aEnd sP n0inv kWords
      nBefore resultPtr nP resultBase = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.suffix.copy.memory resultPtr.toNat words) =
      (operand * operand * rInv) % modulus := by
  unfold selectSOSFull at hselect
  cases hoff : selectSOSOffDiagonalLoop rowFuel productFuel aEnd kWords kWords state with
  | none => rw [hoff] at hselect; contradiction
  | some offDiagonal =>
      rw [hoff] at hselect
      cases hsuffix : selectSOSExecutable doubleFuel diagonalFuel reductionFuel columnFuel
          carryFuel compareFuel subFuel offDiagonal.final.memory
          offDiagonal.final.activeWords sEnd aP aEnd sP n0inv kWords nBefore nP resultPtr
          resultBase with
      | none => simp [hsuffix] at hselect
      | some suffix =>
          have hselected : selected = {
              offDiagonal := offDiagonal
              suffix := suffix
              steps := offDiagonal.steps + suffix.steps
              gas := offDiagonal.gas + suffix.gas } := by
            simpa [hsuffix] using hselect.symm
          subst selected
          have hoffValue := selectedSOSOffDiagonalLoop_value_from_zero words
            (state := state) (selected := offDiagonal) (scratchBase := sP.toNat)
            (by rw [haStart, haEnd]) (by simpa only [haStart] using haFit) hsStart hsFit
            (by rw [hsStart]; omega) hsRange hcovered hawFit hzero hoff
          have hoffCoverage := selectedSOSOffDiagonalLoop_coverage words 1
            (state := state) (selected := offDiagonal) (scratchBase := sP.toNat)
            (by rw [haStart, haEnd]) (by simpa only [haStart] using haFit) hsStart
            (by omega)
            (by rw [hsStart]; omega) (by omega) hcovered hawFit hoff
          have hoffOperand := selectedSOSOffDiagonalLoop_frame_below words 1 aP.toNat words
            (state := state) (selected := offDiagonal) (scratchBase := sP.toNat)
            (by rw [haStart, haEnd]) (by simpa only [haStart] using haFit) hsStart
            (by omega)
            (by rw [hsStart]; omega) (by omega) hcovered hawFit
            (by rw [← haEnd]; exact haSeparate) hoff
          have hoffModulus := selectedSOSOffDiagonalLoop_frame_below words 1 nP.toNat words
            (state := state) (selected := offDiagonal) (scratchBase := sP.toNat)
            (by rw [haStart, haEnd]) (by simpa only [haStart] using haFit) hsStart
            (by omega)
            (by rw [hsStart]; omega) (by omega) hcovered hawFit
            hnScratchSeparate hoff
          have hoffDiagonal : Modexp.wordLimbsToNat
                (memoryWordsFrom offDiagonal.final.memory sP.toNat (2 * words + 1)) =
              Modexp.sosOffDiagonal UInt256.size
                ((memoryWordsFrom offDiagonal.final.memory aP.toNat words).map
                  UInt256.toNat) := by
            rw [hoffOperand]
            simpa only [haStart] using hoffValue
          have hmodulusFinal : Modexp.wordLimbsToNat
                (memoryWordsFrom offDiagonal.final.memory nP.toNat words) = modulus := by
            rw [hoffModulus, hmodulus]
          have hoperandFinal : Modexp.wordLimbsToNat
                (memoryWordsFrom offDiagonal.final.memory aP.toNat words) = operand := by
            rw [hoffOperand, hoperand]
          exact selectedSOSExecutable_value words modulus rInv operand hwords hsEnd haEnd
            haFit hsFit haSeparate
            (by rw [hoffCoverage.2.2]; exact hsRange)
            hoffCoverage.1 hoffCoverage.2.1 hoffDiagonal hsKEnd hnNext hnBefore hnEnd hnFit
            (by rw [hoffCoverage.2.2]; exact hnRange) hnSeparate hnScratchSeparate
            hmodulusFinal hmodulusPos hinv hoperandFinal hoperandReduced hinvR geometry hsuffix

/-- Scratch initialization followed by the exposed full selector computes the pure Montgomery
square.  The zero-loop selector itself supplies coverage, exact scratch size, zero contents, and
operand/modulus framing. -/
theorem selectedSOSInitialized_value
    (words : Nat)
    {zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel carryFuel
      compareFuel subFuel : Nat}
    {zeroState : SOSZeroState}
    {sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase : UInt256}
    {selected : SOSInitializedSelection}
    (modulus rInv operand : Nat)
    (hwords : 0 < words)
    (hzeroPtr : zeroState.ptr = sP)
    (hsEnd : sEnd.toNat = sP.toNat + 32 * (2 * words + 1))
    (haEnd : aEnd.toNat = aP.toNat + 32 * words)
    (haFit : aP.toNat + 32 * words + 31 < UInt256.size)
    (hsFit : sP.toNat + 32 * (2 * words + 1) + 31 < UInt256.size)
    (haSeparate : aEnd.toNat ≤ sP.toNat)
    (hcovered : MemoryCovered zeroState.memory zeroState.activeWords)
    (hawFit : zeroState.activeWords.toNat * 32 < UInt256.size)
    (hmem32 : 32 ≤ zeroState.memory.size)
    (hmemory : zeroState.memory.size ≤ zeroState.ptr.toNat)
    (hgap : zeroState.ptr.toNat - zeroState.memory.size < USize.size)
    (hsKEnd : (sP + kWords).toNat = sP.toNat + 32 * words)
    (hnNext : (nP + ⟨32⟩).toNat = nP.toNat + 32)
    (hnBefore : (nBefore + ⟨64⟩).toNat = (nP + ⟨32⟩).toNat)
    (hnEnd : (nBefore + kWords + ⟨32⟩).toNat = nP.toNat + 32 * words)
    (hnFit : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) + 31 < UInt256.size)
    (hnSeparate : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ sP.toNat + 32)
    (hnScratchSeparate : nP.toNat + 32 * words ≤ sP.toNat)
    (hmodulus : Modexp.wordLimbsToNat
      (memoryWordsFrom zeroState.memory nP.toNat words) = modulus)
    (hmodulusPos : 0 < modulus)
    (hinv : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hoperand : Modexp.wordLimbsToNat
      (memoryWordsFrom zeroState.memory aP.toNat words) = operand)
    (hoperandReduced : operand < modulus)
    (hinvR : UInt256.size ^ words * rInv % modulus = 1 % modulus)
    (geometry : SOSFinalizeGeometry words
      selected.arithmetic.suffix.square.reduction.final.memory
      selected.arithmetic.suffix.square.reduction.final.activeWords nBefore
      selected.arithmetic.suffix.square.reduction.final.sBase kWords
      (nBefore + kWords + ⟨32⟩) nP resultPtr resultBase)
    (hselect : selectSOSInitialized zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel zeroState
      sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase = some selected) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom selected.arithmetic.suffix.copy.memory resultPtr.toNat words) =
      (operand * operand * rInv) % modulus := by
  unfold selectSOSInitialized at hselect
  cases hz : selectSOSZeroLoop zeroFuel sEnd zeroState with
  | none => rw [hz] at hselect; contradiction
  | some zero =>
      rw [hz] at hselect
      let arithmeticState : SOSOffDiagonalLoopState := {
        sRow := sP + ⟨32⟩
        aOff := aP
        memory := zero.final.memory
        activeWords := zero.final.activeWords }
      cases ha : selectSOSFull rowFuel productFuel doubleFuel diagonalFuel reductionFuel
          columnFuel carryFuel compareFuel subFuel arithmeticState sEnd aP aEnd sP n0inv
          kWords nBefore resultPtr nP resultBase with
      | none => simp [arithmeticState, ha] at hselect
      | some arithmetic =>
          have hselected : selected = {
              zero := zero
              arithmetic := arithmetic
              steps := zero.steps + 10 + arithmetic.steps
              gas := zero.gas + 27 + arithmetic.gas } := by
            simpa [arithmeticState, ha] using hselect.symm
          subst selected
          have hzeroFit : zeroState.ptr.toNat + 32 * (2 * words + 1) < UInt256.size := by
            rw [hzeroPtr]
            omega
          have hzeroStop : sEnd.toNat = zeroState.ptr.toNat + 32 * (2 * words + 1) := by
            rw [hzeroPtr]
            exact hsEnd
          have hzeroCoverage := selectedSOSZeroLoop_coverage_geometry (2 * words + 1)
            zeroState zero hz hcovered hawFit hmemory hgap (by omega) hzeroStop
          have hzeroWords := selectedSOSZeroLoop_words_zero (2 * words + 1)
            zeroState zero hz hzeroFit hmemory hgap hzeroStop
          have hzeroSize := selectedSOSZeroLoop_succ_memory_size (2 * words)
            zeroState zero hz hmemory hzeroFit hgap hzeroStop
          have hoperandFrame := selectedSOSZeroLoop_memoryWords_below
            (2 * words + 1) zeroState zero aP.toNat words hz hzeroFit hmem32 hgap
            hzeroStop (by rw [hzeroPtr, ← haEnd]; exact haSeparate)
          have hmodulusFrame := selectedSOSZeroLoop_memoryWords_below
            (2 * words + 1) zeroState zero nP.toNat words hz hzeroFit hmem32 hgap
            hzeroStop (by rw [hzeroPtr]; exact hnScratchSeparate)
          have hoperandFinal : Modexp.wordLimbsToNat
                (memoryWordsFrom zero.final.memory aP.toNat words) = operand := by
            rw [hoperandFrame, hoperand]
          have hmodulusFinal : Modexp.wordLimbsToNat
                (memoryWordsFrom zero.final.memory nP.toNat words) = modulus := by
            rw [hmodulusFrame, hmodulus]
          have hsStartState : arithmeticState.sRow.toNat = sP.toNat + 32 := by
            change (sP + ⟨32⟩).toNat = sP.toNat + 32
            exact uadd_word_lit32_toNat sP (by omega)
          have hsRangeState : sP.toNat + 32 * (2 * words + 1) ≤
              arithmeticState.memory.size := by
            change sP.toNat + 32 * (2 * words + 1) ≤ zero.final.memory.size
            rw [hzeroSize, hzeroPtr]
          have hcoveredState : MemoryCovered arithmeticState.memory
              arithmeticState.activeWords := by
            exact hzeroCoverage.2.1
          have hawFitState : arithmeticState.activeWords.toNat * 32 < UInt256.size := by
            exact hzeroCoverage.2.2
          have hzeroState : memoryWordsFrom arithmeticState.memory sP.toNat
                (2 * words + 1) = List.replicate (2 * words + 1) (⟨0⟩ : UInt256) := by
            change memoryWordsFrom zero.final.memory sP.toNat (2 * words + 1) = _
            simpa only [hzeroPtr] using hzeroWords
          have hnRangeState : (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤
              arithmeticState.memory.size := by
            change (nBefore + ⟨64⟩).toNat + 32 * (words - 1) ≤ zero.final.memory.size
            rw [hzeroSize, hzeroPtr]
            omega
          exact selectedSOSFull_value (state := arithmeticState) (selected := arithmetic)
            words modulus rInv operand hwords rfl hsStartState hsEnd haEnd haFit hsFit
            haSeparate hsRangeState hcoveredState hawFitState hzeroState
            hsKEnd hnNext hnBefore hnEnd hnFit hnRangeState
            hnSeparate hnScratchSeparate hmodulusFinal hmodulusPos hinv hoperandFinal
            hoperandReduced hinvR geometry ha

/-- The selected reduction loop and selected finalizer compute the pure Montgomery square.
The selector remains explicit, while the result is stated only in terms of the initial operand,
modulus, and Montgomery inverse. -/
theorem selectedSOSReductionFinalize_value
    (columns passes : Nat) {compareFuel subFuel : Nat}
    {initial : SOSReductionLoopState} {reduction : SOSReductionLoopSelection}
    {nP n0inv nBefore bytes nEnd resultPtr resultBase : UInt256}
    {compared : SOSFinalCompareSelection} {copy : SOSCopySelection}
    (modulus rInv operand : Nat)
    (facts : SOSReductionLoopFacts columns passes initial.memory initial nP n0inv
      modulus reduction)
    (geometry : SOSFinalizeGeometry columns reduction.final.memory
      reduction.final.activeWords nBefore reduction.final.sBase bytes nEnd nP
      resultPtr resultBase)
    (hcompare : selectSOSFinalCompare compareFuel reduction.final.memory
      reduction.final.activeWords reduction.final.sBase bytes nEnd = some compared)
    (hcopy : selectSOSCopy subFuel reduction.final.memory compared.activeWords
      reduction.final.sBase bytes compared.doSub resultPtr nP resultBase = some copy)
    (hmodulus : Modexp.wordLimbsToNat
      (memoryWordsFrom initial.memory nP.toNat columns) = modulus)
    (hmodulusPos : 0 < modulus)
    (hinv0 : modulus * n0inv.toNat % UInt256.size = UInt256.size - 1)
    (hsquare : Modexp.wordLimbsToNat
        (memoryWordsFrom initial.memory initial.sBase.toNat (columns + passes + 1)) =
      operand ^ 2)
    (hinvR : UInt256.size ^ passes * rInv % modulus = 1 % modulus) :
    Modexp.wordLimbsToNat (memoryWordsFrom copy.memory resultPtr.toNat columns) =
      (operand * operand * rInv) % modulus := by
  have hfinal := selectedSOSFinalize_value columns reduction.final.memory
    reduction.final.activeWords nBefore reduction.final.sBase bytes nEnd nP resultPtr
    resultBase compared copy geometry hcompare hcopy
  have hcandidate := geometry.candidate_eq_memoryWords
  have hfinalModulus : Modexp.wordLimbsToNat
      (memoryWordsFrom reduction.final.memory nP.toNat columns) = modulus := by
    rw [facts.modulusFrame, hmodulus]
  rw [hcandidate, facts.value, hfinalModulus] at hfinal
  rw [hfinal]
  have hscanBound : Modexp.montgomerySOSScan UInt256.size modulus n0inv.toNat
        (Modexp.wordLimbsToNat
          (memoryWordsFrom initial.memory initial.sBase.toNat
            (columns + passes + 1))) passes <
      2 * modulus := by
    rw [← facts.value]
    exact facts.bound
  exact Modexp.montgomerySOS_contract (by decide) hmodulusPos hinv0 hsquare hinvR
    hscanBound

end Modexp.MultiLimbMontgomerySOSSemantic
