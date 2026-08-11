import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulInputSemantic

/-! # Complete standalone schoolbook row semantics -/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookMulTrace

open Modexp.MultiLimbMontgomeryCIOSSemantic

/-- Once the concrete collector-to-memory premises are discharged, every inner store plus the
fresh zero-top carry store is exactly one pure schoolbook row. -/
theorem completeInnerRow_memory_eq_pure
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (operandWords priorWords : List UInt256) (ptr : Nat)
    (hcarryZero : state.carry = ⟨0⟩)
    (hoperand : innerOperandWords a bPtr resultPtr i count state = operandWords)
    (hprior : innerPriorWords a bPtr resultPtr i count state = priorWords)
    (houtput : innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr count)
    (hcarryAddress :
      (carryPtr resultPtr i (UInt256.ofNat count)).toNat = ptr + 32 * count)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate a bPtr resultPtr i count state).memory
      (iterate a bPtr resultPtr i count state).activeWords
      (carryPtr resultPtr i (UInt256.ofNat count)) = ⟨0⟩)
    (hcarryWrite : (carryPtr resultPtr i (UInt256.ofNat count)).toNat + 32 ≤
      (iterate a bPtr resultPtr i count state).memory.size) :
    let final := iterate a bPtr resultPtr i count state
    let row := Modexp.evmSchoolbookRow a operandWords priorWords ⟨0⟩
    memoryWordsFrom
        (carryMemory final.memory final.activeWords resultPtr i
          (UInt256.ofNat count) final.carry)
        ptr (count + 1) = row.1 ++ [row.2] := by
  let final := iterate a bPtr resultPtr i count state
  let row := Modexp.evmSchoolbookRow a operandWords priorWords ⟨0⟩
  have hrow := innerCollectors_eq_row a bPtr resultPtr i count state
  rw [hcarryZero, hoperand, hprior] at hrow
  have hrowOutput := congrArg Prod.fst hrow
  have hrowCarry := congrArg Prod.snd hrow
  have hstored := carryMemory_words_of_read_zero final.memory final.activeWords
    resultPtr i (UInt256.ofNat count) final.carry ptr count
    (by simpa [final] using hcarryAddress)
    (by simpa [final] using hcarryReadZero)
    (by simpa [final] using hcarryWrite)
  dsimp only
  rw [hstored]
  rw [← houtput]
  simpa [row, final] using congrArg₂ (fun left right => left ++ [right])
    hrowOutput.symm hrowCarry.symm

/-- The represented value of the complete concrete row is the prior segment plus the exact
single-limb-by-vector product. -/
theorem completeInnerRow_memory_value
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (operandWords priorWords : List UInt256) (ptr : Nat)
    (hcarryZero : state.carry = ⟨0⟩)
    (hoperandLength : operandWords.length = count)
    (hpriorLength : priorWords.length = count)
    (hoperand : innerOperandWords a bPtr resultPtr i count state = operandWords)
    (hprior : innerPriorWords a bPtr resultPtr i count state = priorWords)
    (houtput : innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr count)
    (hcarryAddress :
      (carryPtr resultPtr i (UInt256.ofNat count)).toNat = ptr + 32 * count)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate a bPtr resultPtr i count state).memory
      (iterate a bPtr resultPtr i count state).activeWords
      (carryPtr resultPtr i (UInt256.ofNat count)) = ⟨0⟩)
    (hcarryWrite : (carryPtr resultPtr i (UInt256.ofNat count)).toNat + 32 ≤
      (iterate a bPtr resultPtr i count state).memory.size) :
    let final := iterate a bPtr resultPtr i count state
    Modexp.wordLimbsToNat
        (memoryWordsFrom
          (carryMemory final.memory final.activeWords resultPtr i
            (UInt256.ofNat count) final.carry)
          ptr (count + 1)) =
      Modexp.wordLimbsToNat priorWords +
        a.toNat * Modexp.wordLimbsToNat operandWords := by
  have hmemory := completeInnerRow_memory_eq_pure a bPtr resultPtr i count state
    operandWords priorWords ptr hcarryZero hoperand hprior houtput hcarryAddress
    hcarryReadZero hcarryWrite
  dsimp only at hmemory ⊢
  rw [hmemory, Modexp.wordLimbsToNat_append]
  have hrowLength := Modexp.evmSchoolbookRow_result_length a operandWords
    priorWords ⟨0⟩ (by omega)
  have hrow := Modexp.evmSchoolbookRow_recompose a operandWords priorWords ⟨0⟩
    (by omega)
  rw [hrowLength, hoperandLength]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
  simpa [hoperandLength] using hrow

/-- The complete standalone row equals the pure schoolbook row when its destination stores and
final carry store materialize an implicit-zero allocator payload. -/
theorem completeInnerRow_memory_eq_pure_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (operandWords priorWords : List UInt256) (ptr : Nat)
    (hcarryZero : state.carry = ⟨0⟩)
    (hoperand : innerOperandWords a bPtr resultPtr i count state = operandWords)
    (hprior : innerPriorWords a bPtr resultPtr i count state = priorWords)
    (houtput : innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr count)
    (hcarryAddress :
      (carryPtr resultPtr i (UInt256.ofNat count)).toNat = ptr + 32 * count)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate a bPtr resultPtr i count state).memory
      (iterate a bPtr resultPtr i count state).activeWords
      (carryPtr resultPtr i (UInt256.ofNat count)) = ⟨0⟩)
    (hcarryWriteStart : (carryPtr resultPtr i (UInt256.ofNat count)).toNat ≤
      (iterate a bPtr resultPtr i count state).memory.size) :
    let final := iterate a bPtr resultPtr i count state
    let row := Modexp.evmSchoolbookRow a operandWords priorWords ⟨0⟩
    memoryWordsFrom
        (carryMemory final.memory final.activeWords resultPtr i
          (UInt256.ofNat count) final.carry)
        ptr (count + 1) = row.1 ++ [row.2] := by
  let final := iterate a bPtr resultPtr i count state
  let row := Modexp.evmSchoolbookRow a operandWords priorWords ⟨0⟩
  have hrow := innerCollectors_eq_row a bPtr resultPtr i count state
  rw [hcarryZero, hoperand, hprior] at hrow
  have hrowOutput := congrArg Prod.fst hrow
  have hrowCarry := congrArg Prod.snd hrow
  have hstored := carryMemory_words_of_read_zero_extending final.memory final.activeWords
    resultPtr i (UInt256.ofNat count) final.carry ptr count
    (by simpa [final] using hcarryAddress)
    (by simpa [final] using hcarryReadZero)
    (by simpa [final] using hcarryWriteStart)
  dsimp only
  rw [hstored, ← houtput]
  simpa [row, final] using congrArg₂ (fun left right => left ++ [right])
    hrowOutput.symm hrowCarry.symm

/-- The represented value of a complete frontier-extending concrete row is the exact prior value
plus its single-limb-by-vector product. -/
theorem completeInnerRow_memory_value_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (operandWords priorWords : List UInt256) (ptr : Nat)
    (hcarryZero : state.carry = ⟨0⟩)
    (hoperandLength : operandWords.length = count)
    (hpriorLength : priorWords.length = count)
    (hoperand : innerOperandWords a bPtr resultPtr i count state = operandWords)
    (hprior : innerPriorWords a bPtr resultPtr i count state = priorWords)
    (houtput : innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr count)
    (hcarryAddress :
      (carryPtr resultPtr i (UInt256.ofNat count)).toNat = ptr + 32 * count)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate a bPtr resultPtr i count state).memory
      (iterate a bPtr resultPtr i count state).activeWords
      (carryPtr resultPtr i (UInt256.ofNat count)) = ⟨0⟩)
    (hcarryWriteStart : (carryPtr resultPtr i (UInt256.ofNat count)).toNat ≤
      (iterate a bPtr resultPtr i count state).memory.size) :
    let final := iterate a bPtr resultPtr i count state
    Modexp.wordLimbsToNat
        (memoryWordsFrom
          (carryMemory final.memory final.activeWords resultPtr i
            (UInt256.ofNat count) final.carry)
          ptr (count + 1)) =
      Modexp.wordLimbsToNat priorWords +
        a.toNat * Modexp.wordLimbsToNat operandWords := by
  have hmemory := completeInnerRow_memory_eq_pure_extending a bPtr resultPtr i count state
    operandWords priorWords ptr hcarryZero hoperand hprior houtput hcarryAddress
    hcarryReadZero hcarryWriteStart
  dsimp only at hmemory ⊢
  rw [hmemory, Modexp.wordLimbsToNat_append]
  have hrowLength := Modexp.evmSchoolbookRow_result_length a operandWords
    priorWords ⟨0⟩ (by omega)
  have hrow := Modexp.evmSchoolbookRow_recompose a operandWords priorWords ⟨0⟩
    (by omega)
  rw [hrowLength, hoperandLength]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
  simpa [hoperandLength] using hrow

/-- A complete standalone row equals the pure schoolbook row when its final carry store may cross
a bounded implicit-zero gap. -/
theorem completeInnerRow_memory_eq_pure_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (operandWords priorWords : List UInt256) (ptr : Nat)
    (hcarryZero : state.carry = ⟨0⟩)
    (hoperand : innerOperandWords a bPtr resultPtr i count state = operandWords)
    (hprior : innerPriorWords a bPtr resultPtr i count state = priorWords)
    (houtput : innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr count)
    (hcarryAddress :
      (carryPtr resultPtr i (UInt256.ofNat count)).toNat = ptr + 32 * count)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate a bPtr resultPtr i count state).memory
      (iterate a bPtr resultPtr i count state).activeWords
      (carryPtr resultPtr i (UInt256.ofNat count)) = ⟨0⟩)
    (hfinalBase : 32 ≤ (iterate a bPtr resultPtr i count state).memory.size)
    (hcarryGap : (carryPtr resultPtr i (UInt256.ofNat count)).toNat -
      (iterate a bPtr resultPtr i count state).memory.size < USize.size) :
    let final := iterate a bPtr resultPtr i count state
    let row := Modexp.evmSchoolbookRow a operandWords priorWords ⟨0⟩
    memoryWordsFrom
        (carryMemory final.memory final.activeWords resultPtr i
          (UInt256.ofNat count) final.carry)
        ptr (count + 1) = row.1 ++ [row.2] := by
  let final := iterate a bPtr resultPtr i count state
  let row := Modexp.evmSchoolbookRow a operandWords priorWords ⟨0⟩
  have hrow := innerCollectors_eq_row a bPtr resultPtr i count state
  rw [hcarryZero, hoperand, hprior] at hrow
  have hrowOutput := congrArg Prod.fst hrow
  have hrowCarry := congrArg Prod.snd hrow
  have hstored := carryMemory_words_of_read_zero_of_gap final.memory final.activeWords
    resultPtr i (UInt256.ofNat count) final.carry ptr count
    (by simpa [final] using hcarryAddress)
    (by simpa [final] using hcarryReadZero)
    (by simpa [final] using hfinalBase)
    (by simpa [final] using hcarryGap)
  dsimp only
  rw [hstored, ← houtput]
  simpa [row, final] using congrArg₂ (fun left right => left ++ [right])
    hrowOutput.symm hrowCarry.symm

/-- The represented value of a complete bounded-gap row is the exact prior value plus its
single-limb-by-vector product. -/
theorem completeInnerRow_memory_value_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (operandWords priorWords : List UInt256) (ptr : Nat)
    (hcarryZero : state.carry = ⟨0⟩)
    (hoperandLength : operandWords.length = count)
    (hpriorLength : priorWords.length = count)
    (hoperand : innerOperandWords a bPtr resultPtr i count state = operandWords)
    (hprior : innerPriorWords a bPtr resultPtr i count state = priorWords)
    (houtput : innerOutputWords a bPtr resultPtr i count state =
      memoryWordsFrom (iterate a bPtr resultPtr i count state).memory ptr count)
    (hcarryAddress :
      (carryPtr resultPtr i (UInt256.ofNat count)).toNat = ptr + 32 * count)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate a bPtr resultPtr i count state).memory
      (iterate a bPtr resultPtr i count state).activeWords
      (carryPtr resultPtr i (UInt256.ofNat count)) = ⟨0⟩)
    (hfinalBase : 32 ≤ (iterate a bPtr resultPtr i count state).memory.size)
    (hcarryGap : (carryPtr resultPtr i (UInt256.ofNat count)).toNat -
      (iterate a bPtr resultPtr i count state).memory.size < USize.size) :
    let final := iterate a bPtr resultPtr i count state
    Modexp.wordLimbsToNat
        (memoryWordsFrom
          (carryMemory final.memory final.activeWords resultPtr i
            (UInt256.ofNat count) final.carry)
          ptr (count + 1)) =
      Modexp.wordLimbsToNat priorWords +
        a.toNat * Modexp.wordLimbsToNat operandWords := by
  have hmemory := completeInnerRow_memory_eq_pure_of_gap a bPtr resultPtr i count state
    operandWords priorWords ptr hcarryZero hoperand hprior houtput hcarryAddress
    hcarryReadZero hfinalBase hcarryGap
  dsimp only at hmemory ⊢
  rw [hmemory, Modexp.wordLimbsToNat_append]
  have hrowLength := Modexp.evmSchoolbookRow_result_length a operandWords
    priorWords ⟨0⟩ (by omega)
  have hrow := Modexp.evmSchoolbookRow_recompose a operandWords priorWords ⟨0⟩
    (by omega)
  rw [hrowLength, hoperandLength]
  simp only [Modexp.wordLimbsToNat, Nat.add_zero, Nat.mul_zero]
  simpa [hoperandLength] using hrow

end Modexp.MultiLimbSchoolbookMulTrace
