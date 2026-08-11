import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulRowSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulOuter
import Examples.Precompiles.Modexp.MultiLimbMultiplicationRowsModel

/-! # Standalone schoolbook outer-loop semantics -/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookMulTrace

open Modexp.MultiLimbMontgomeryCIOSSemantic

/-- Source words observed by the exact zero/nonzero outer-row selector. -/
def outerSourceWords (aPtr bPtr resultPtr : UInt256) (bCount : Nat) :
    Nat → OuterState → List UInt256
  | 0, _ => []
  | count + 1, state =>
      sourceWord state.memory state.activeWords aPtr state.i ::
        outerSourceWords aPtr bPtr resultPtr bCount count
          (rowAdvance aPtr bPtr resultPtr bCount state)

@[simp] theorem outerSourceWords_length
    (aPtr bPtr resultPtr : UInt256) (bCount count : Nat) (state : OuterState) :
    (outerSourceWords aPtr bPtr resultPtr bCount count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp [outerSourceWords, ih]

/-- The source-word collector can expose its final observed row. -/
theorem outerSourceWords_succ_last
    (aPtr bPtr resultPtr : UInt256) (bCount count : Nat) (state : OuterState) :
    outerSourceWords aPtr bPtr resultPtr bCount (count + 1) state =
      outerSourceWords aPtr bPtr resultPtr bCount count state ++
        [sourceWord
          (rowsIterate aPtr bPtr resultPtr bCount count state).memory
          (rowsIterate aPtr bPtr resultPtr bCount count state).activeWords
          aPtr (rowsIterate aPtr bPtr resultPtr bCount count state).i] := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      change sourceWord state.memory state.activeWords aPtr state.i ::
          outerSourceWords aPtr bPtr resultPtr bCount (count + 1) next =
        sourceWord state.memory state.activeWords aPtr state.i ::
          (outerSourceWords aPtr bPtr resultPtr bCount count next ++
            [sourceWord
              (rowsIterate aPtr bPtr resultPtr bCount (count + 1) state).memory
              (rowsIterate aPtr bPtr resultPtr bCount (count + 1) state).activeWords
              aPtr (rowsIterate aPtr bPtr resultPtr bCount (count + 1) state).i])
      congr 1
      rw [ih]
      simp only [next, rowsIterate_advance]

/-- The exact zero-source branch of `rowAdvance` is the pure identity row update on a destination
whose selected segment is followed by its fresh zero carry word. -/
theorem rowAdvance_zero_schoolbookRowUpdate
    (aPtr bPtr resultPtr : UInt256) (bCount shift resultLength : Nat)
    (state : OuterState) (operandWords pre segment suffix : List UInt256)
    (hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩)
    (hpre : pre.length = shift) (hsegment : segment.length = operandWords.length)
    (hbefore : memoryWordsFrom state.memory (resultPtr.toNat + 32) resultLength =
      pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix) :
    Modexp.SchoolbookRowUpdate
      (sourceWord state.memory state.activeWords aPtr state.i)
      operandWords shift
      (memoryWordsFrom state.memory (resultPtr.toNat + 32) resultLength)
      (memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount state).memory
        (resultPtr.toNat + 32) resultLength) := by
  rw [hzero]
  have hupdate := Modexp.schoolbookRowUpdate_zero operandWords pre segment suffix shift
    hpre hsegment
  simpa only [hbefore, rowAdvance, hzero, if_pos] using hupdate

/-- A consecutive word range splits at an arbitrary word boundary. -/
theorem memoryWordsFrom_split_at (mem : ByteArray) (ptr left right : Nat) :
    memoryWordsFrom mem ptr (left + right) =
      memoryWordsFrom mem ptr left ++ memoryWordsFrom mem (ptr + 32 * left) right := by
  induction left generalizing ptr with
  | zero => simp [memoryWordsFrom]
  | succ left ih =>
      rw [show left + 1 + right = (left + right) + 1 by omega]
      simp only [memoryWordsFrom, List.cons_append]
      rw [ih]
      rw [show ptr + 32 + 32 * left = ptr + 32 * (left + 1) by omega]

/-- A zero limb exposed by a full padded-range decomposition is the corresponding concrete
memory word. -/
theorem memoryWordNat_of_words_zero
    (mem : ByteArray) (base index : Nat) (front suffix : List UInt256)
    (hfront : front.length = index)
    (hwords : memoryWordsFrom mem base (index + 1 + suffix.length) =
      front ++ (⟨0⟩ : UInt256) :: suffix) :
    Modexp.MultiLimbMemoryModel.memoryWordNat mem (base + 32 * index) = 0 := by
  have hsplit := memoryWordsFrom_split_at mem base index (1 + suffix.length)
  rw [show index + (1 + suffix.length) = index + 1 + suffix.length by omega,
    hwords] at hsplit
  have hprefixLength : (memoryWordsFrom mem base index).length = front.length := by
    rw [memoryWordsFrom_length, hfront]
  have htail : memoryWordsFrom mem (base + 32 * index) (1 + suffix.length) =
      (⟨0⟩ : UInt256) :: suffix :=
    (List.append_inj hsplit hprefixLength.symm).2.symm
  rw [show 1 + suffix.length = suffix.length + 1 by omega] at htail
  simp only [memoryWordsFrom] at htail
  have hword := (List.cons.inj htail).1
  have hnat := congrArg UInt256.toNat hword
  simpa only [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)] using hnat

/-- Under the concrete standalone-loop address and frame facts, the selected nonzero bytecode row
is exactly one shifted pure schoolbook row update on the full result payload. -/
theorem rowAdvance_nonzero_schoolbookRowUpdate
    (aPtr bPtr resultPtr : UInt256) (bCount shift suffixLength : Nat)
    (state : OuterState) (operandWords : List UInt256)
    (hnonzero : sourceWord state.memory state.activeWords aPtr state.i ≠ ⟨0⟩)
    (hbaseMemory : 32 ≤ state.memory.size)
    (hoperandLength : operandWords.length = bCount)
    (hrowPtr : (elementPtr resultPtr (state.i + ⟨0⟩)).toNat =
      resultPtr.toNat + 32 + 32 * shift)
    (hcarryAddress :
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat =
        resultPtr.toNat + 32 + 32 * shift + 32 * bCount)
    (htopZero : Modexp.MultiLimbMemoryModel.memoryWordNat state.memory
      (resultPtr.toNat + 32 + 32 * shift + 32 * bCount) = 0)
    (hoperand : innerOperandWords
      (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr state.i bCount
      (initialInnerState state.memory state.activeWords aPtr state.i) = operandWords)
    (hprior : innerPriorWords
      (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr state.i bCount
      (initialInnerState state.memory state.activeWords aPtr state.i) =
        memoryWordsFrom state.memory (resultPtr.toNat + 32 + 32 * shift) bCount)
    (houtput : innerOutputWords
      (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr state.i bCount
      (initialInnerState state.memory state.activeWords aPtr state.i) =
        memoryWordsFrom
          (iterate (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr
            state.i bCount (initialInnerState state.memory state.activeWords aPtr state.i)).memory
          (resultPtr.toNat + 32 + 32 * shift) bCount)
    (hcarryReadZero : Modexp.MultiLimbDivisionTrace.readWord
      (iterate (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr
        state.i bCount (initialInnerState state.memory state.activeWords aPtr state.i)).memory
      (iterate (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr
        state.i bCount (initialInnerState state.memory state.activeWords aPtr state.i)).activeWords
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)) = ⟨0⟩)
    (hfinalBase : 32 ≤
      (iterate (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr
        state.i bCount (initialInnerState state.memory state.activeWords aPtr state.i)).memory.size)
    (hcarryGap : (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat -
      (iterate (sourceWord state.memory state.activeWords aPtr state.i) bPtr resultPtr
        state.i bCount (initialInnerState state.memory state.activeWords aPtr state.i)).memory.size <
        USize.size)
    (hgaps : ∀ q, q < bCount →
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q
          (initialInnerState state.memory state.activeWords aPtr state.i)
      (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size)
    (hprefixBelow : ∀ q, q < bCount →
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q
          (initialInnerState state.memory state.activeWords aPtr state.i)
      resultPtr.toNat + 32 + 32 * shift ≤
        (elementPtr resultPtr (state.i + current.j)).toNat)
    (hsuffixAbove : ∀ q, q < bCount →
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q
          (initialInnerState state.memory state.activeWords aPtr state.i)
      (elementPtr resultPtr (state.i + current.j)).toNat + 32 ≤
        resultPtr.toNat + 32 + 32 * (shift + bCount + 1)) :
    Modexp.SchoolbookRowUpdate
      (sourceWord state.memory state.activeWords aPtr state.i) operandWords shift
      (memoryWordsFrom state.memory (resultPtr.toNat + 32)
        (shift + bCount + 1 + suffixLength))
      (memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount state).memory
        (resultPtr.toNat + 32) (shift + bCount + 1 + suffixLength)) := by
  let a := sourceWord state.memory state.activeWords aPtr state.i
  let initial := initialInnerState state.memory state.activeWords aPtr state.i
  let final := iterate a bPtr resultPtr state.i bCount initial
  let rowMemory := carryMemory final.memory final.activeWords resultPtr state.i
    (UInt256.ofNat bCount) final.carry
  let base := resultPtr.toNat + 32
  let rowPtr := base + 32 * shift
  let suffixPtr := base + 32 * (shift + bCount + 1)
  let pre := memoryWordsFrom state.memory base shift
  let segment := memoryWordsFrom state.memory rowPtr bCount
  let suffix := memoryWordsFrom state.memory suffixPtr suffixLength
  have hrowPtr' : (elementPtr resultPtr (state.i + initial.j)).toNat = rowPtr := by
    simpa only [initial, initialInnerState, u256_zero_add, rowPtr, base, Nat.add_assoc]
      using hrowPtr
  have hcarryAddress' : (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat =
      rowPtr + 32 * bCount := by
    simpa only [rowPtr, base, Nat.add_assoc] using hcarryAddress
  have hrow := completeInnerRow_memory_eq_pure_of_gap a bPtr resultPtr state.i bCount initial
    operandWords segment rowPtr (by rfl)
    (by simpa only [a, initial] using hoperand)
    (by simpa only [a, initial, segment, rowPtr] using hprior)
    (by simpa only [a, initial, final, rowPtr] using houtput)
    hcarryAddress'
    (by simpa only [a, initial, final] using hcarryReadZero)
    (by simpa only [a, initial, final] using hfinalBase)
    (by simpa only [a, initial, final] using hcarryGap)
  have hprefixInner := iterate_memoryWords_below_of_gap a bPtr resultPtr state.i bCount initial
    base shift (by simpa only [initial, initialInnerState] using hbaseMemory)
    (by simpa only [a, initial] using hgaps)
    (by simpa only [a, initial, base] using hprefixBelow)
  have hprefixCarry := carryMemory_words_below_of_gap final.memory final.activeWords resultPtr
    state.i (UInt256.ofNat bCount) final.carry base shift
    (by simpa only [a, initial, final] using hfinalBase)
    (by simpa only [a, initial, final] using hcarryGap) (by
      rw [hcarryAddress']
      dsimp only [rowPtr, base]
      omega)
  have hprefix : memoryWordsFrom rowMemory base shift = pre := by
    rw [show memoryWordsFrom rowMemory base shift = memoryWordsFrom final.memory base shift by
      simpa only [rowMemory] using hprefixCarry]
    rw [hprefixInner]
    rfl
  have hsuffixInner := iterate_memoryWords_above_of_gap a bPtr resultPtr state.i bCount initial
    suffixPtr suffixLength (by simpa only [a, initial] using hgaps)
    (by simpa only [a, initial, suffixPtr, base, Nat.add_assoc] using hsuffixAbove)
  have hsuffixCarry := carryMemory_words_above_of_gap final.memory final.activeWords resultPtr
    state.i (UInt256.ofNat bCount) final.carry suffixPtr suffixLength
    (by simpa only [a, initial, final] using hcarryGap) (by
      rw [hcarryAddress']
      dsimp only [suffixPtr, rowPtr, base]
      omega)
  have hsuffix : memoryWordsFrom rowMemory suffixPtr suffixLength = suffix := by
    rw [show memoryWordsFrom rowMemory suffixPtr suffixLength =
        memoryWordsFrom final.memory suffixPtr suffixLength by
      simpa only [rowMemory] using hsuffixCarry]
    rw [hsuffixInner]
    rfl
  have hbeforeSplit : memoryWordsFrom state.memory base
      (shift + bCount + 1 + suffixLength) =
        pre ++ segment ++ (⟨0⟩ : UInt256) :: suffix := by
    rw [show shift + bCount + 1 + suffixLength = shift + (bCount + 1 + suffixLength) by omega]
    rw [memoryWordsFrom_split_at]
    rw [show base + 32 * shift = rowPtr by rfl]
    rw [show bCount + 1 + suffixLength = (bCount + 1) + suffixLength by omega]
    rw [memoryWordsFrom_split_at]
    rw [Modexp.MultiLimbMontgomeryCIOSSemantic.memoryWordsFrom_succ_eq_append]
    rw [show rowPtr + 32 * (bCount + 1) = suffixPtr by
      dsimp only [suffixPtr, rowPtr, base]; omega]
    rw [show UInt256.ofNat
        (Modexp.MultiLimbMemoryModel.memoryWordNat state.memory (rowPtr + 32 * bCount)) =
          (⟨0⟩ : UInt256) by
      apply u256_inj
      rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      simpa only [rowPtr, base, Nat.add_assoc] using htopZero]
    simp only [pre, segment, suffix, List.singleton_append, List.append_assoc]
  have hafterSplit : memoryWordsFrom rowMemory base
      (shift + bCount + 1 + suffixLength) =
        pre ++ (Modexp.evmSchoolbookRow a operandWords segment ⟨0⟩).1 ++
          (Modexp.evmSchoolbookRow a operandWords segment ⟨0⟩).2 :: suffix := by
    rw [show shift + bCount + 1 + suffixLength = shift + (bCount + 1 + suffixLength) by omega]
    rw [memoryWordsFrom_split_at, hprefix]
    rw [show base + 32 * shift = rowPtr by rfl]
    rw [show bCount + 1 + suffixLength = (bCount + 1) + suffixLength by omega]
    rw [memoryWordsFrom_split_at]
    rw [show rowPtr + 32 * (bCount + 1) = suffixPtr by
      dsimp only [suffixPtr, rowPtr, base]; omega]
    rw [hsuffix]
    rw [show memoryWordsFrom rowMemory rowPtr (bCount + 1) =
        (Modexp.evmSchoolbookRow a operandWords segment ⟨0⟩).1 ++
          [(Modexp.evmSchoolbookRow a operandWords segment ⟨0⟩).2] by
      simpa only [rowMemory, final] using hrow]
    simp only [List.singleton_append, List.append_assoc]
  refine ⟨pre, segment, suffix, ?_, ?_, ?_, ?_⟩
  · exact memoryWordsFrom_length _ _ _
  · rw [memoryWordsFrom_length, hoperandLength]
  · simpa only [base, a, initial, final, rowMemory, rowAdvance, hnonzero, if_neg]
      using hbeforeSplit
  · simpa only [base, a, initial, final, rowMemory, nonzeroRowMemory,
      completedInnerState, rowAdvance, hnonzero, if_neg] using hafterSplit

/-- One selected outer row preserves covered representable memory and its concrete byte-array size.
The nonzero case includes every inner load/store and the final carry load/store. -/
theorem rowAdvance_coverage_size
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsourceFit : (sourcePtr aPtr state.i).toNat + 32 + 31 < UInt256.size)
    (hinner : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (state.i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (state.i + current.j)).toNat + 32 ≤ current.memory.size)
    (hcarryFit : (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 + 31 <
      UInt256.size)
    (hcarryWrite :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 ≤ final.memory.size) :
    MemoryCovered (rowAdvance aPtr bPtr resultPtr bCount state).memory
        (rowAdvance aPtr bPtr resultPtr bCount state).activeWords ∧
      (rowAdvance aPtr bPtr resultPtr bCount state).activeWords.toNat * 32 < UInt256.size ∧
      (rowAdvance aPtr bPtr resultPtr bCount state).memory.size = state.memory.size := by
  have hsource := readWords1_coverage state.memory state.activeWords (sourcePtr aPtr state.i)
    hcovered hawFit hsourceFit
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [rowAdvance, hzero, if_pos, sourceWords, afterLoad] using hsource.1
    · simpa only [rowAdvance, hzero, if_pos, sourceWords, afterLoad] using hsource.2
    · simp only [rowAdvance, hzero, if_pos]
  · let a := sourceWord state.memory state.activeWords aPtr state.i
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let final := iterate a bPtr resultPtr state.i bCount initial
    have hinitialCovered : MemoryCovered initial.memory initial.activeWords := by
      simpa only [initial, initialInnerState, sourceWords, afterLoad] using hsource.1
    have hinitialFit : initial.activeWords.toNat * 32 < UInt256.size := by
      simpa only [initial, initialInnerState, sourceWords, afterLoad] using hsource.2
    have hiter := iterate_coverage_size a bPtr resultPtr state.i bCount initial
      hinitialCovered hinitialFit (by simpa only [a, initial] using hinner)
    have hcarry := carryMemory_coverage_size final.memory final.activeWords resultPtr state.i
      (UInt256.ofNat bCount) final.carry
      (by simpa only [a, initial, final] using hcarryFit)
      (by simpa only [a, initial, final] using hcarryWrite)
      (by simpa only [final] using hiter.1)
      (by simpa only [final] using hiter.2.1)
    simpa only [rowAdvance, hzero, if_neg, nonzeroRowMemory, nonzeroRowWords,
      completedInnerState, a, initial, final] using
        And.intro hcarry.1 (And.intro hcarry.2.1 (hcarry.2.2.trans hiter.2.2))

/-- Concrete address-safety obligations for one complete selected standalone row. -/
def RowAccessSafe
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState) : Prop :=
  (sourcePtr aPtr state.i).toNat + 32 + 31 < UInt256.size ∧
  (∀ q, q < bCount →
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
      bPtr resultPtr state.i q initial
    (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
      (elementPtr resultPtr (state.i + current.j)).toNat + 32 + 31 < UInt256.size ∧
      (elementPtr resultPtr (state.i + current.j)).toNat + 32 ≤ current.memory.size) ∧
  (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 + 31 < UInt256.size ∧
  (let initial := initialInnerState state.memory state.activeWords aPtr state.i
   let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
     bPtr resultPtr state.i bCount initial
   (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 ≤ final.memory.size)

/-- Covered representable memory and fixed byte-array size propagate across any finite sequence of
outer rows whose concrete accesses satisfy `RowAccessSafe`. -/
theorem rowsIterate_coverage_size
    (aPtr bPtr resultPtr : UInt256) (bCount count : Nat) (state : OuterState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsafe : ∀ q, q < count →
      RowAccessSafe aPtr bPtr resultPtr bCount
        (rowsIterate aPtr bPtr resultPtr bCount q state)) :
    MemoryCovered (rowsIterate aPtr bPtr resultPtr bCount count state).memory
        (rowsIterate aPtr bPtr resultPtr bCount count state).activeWords ∧
      (rowsIterate aPtr bPtr resultPtr bCount count state).activeWords.toNat * 32 <
        UInt256.size ∧
      (rowsIterate aPtr bPtr resultPtr bCount count state).memory.size = state.memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, rfl⟩
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      have hfirst : RowAccessSafe aPtr bPtr resultPtr bCount state := by
        simpa only [rowsIterate] using hsafe 0 (by omega)
      have hnext := rowAdvance_coverage_size aPtr bPtr resultPtr bCount state hcovered hawFit
        hfirst.1 hfirst.2.1 hfirst.2.2.1 hfirst.2.2.2
      have htailSafe : ∀ q, q < count →
          RowAccessSafe aPtr bPtr resultPtr bCount
            (rowsIterate aPtr bPtr resultPtr bCount q next) := by
        intro q hq
        simpa only [next, rowsIterate_advance] using hsafe (q + 1) (by omega)
      have htail := ih next hnext.1 hnext.2.1 htailSafe
      simpa only [next, rowsIterate] using
        And.intro htail.1 (And.intro htail.2.1 (htail.2.2.trans hnext.2.2))

/-- One selected row preserves coverage when its destination stores may cross bounded
implicit-zero gaps. -/
theorem rowAdvance_coverage_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsourceFit : (sourcePtr aPtr state.i).toNat + 32 + 31 < UInt256.size)
    (hinner : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (state.i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size)
    (hcarryFit : (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 + 31 <
      UInt256.size)
    (hcarryGap :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size < USize.size) :
    MemoryCovered (rowAdvance aPtr bPtr resultPtr bCount state).memory
        (rowAdvance aPtr bPtr resultPtr bCount state).activeWords ∧
      (rowAdvance aPtr bPtr resultPtr bCount state).activeWords.toNat * 32 < UInt256.size ∧
      state.memory.size ≤ (rowAdvance aPtr bPtr resultPtr bCount state).memory.size := by
  have hsource := readWords1_coverage state.memory state.activeWords (sourcePtr aPtr state.i)
    hcovered hawFit hsourceFit
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [rowAdvance, hzero, if_pos, sourceWords, afterLoad] using hsource.1
    · simpa only [rowAdvance, hzero, if_pos, sourceWords, afterLoad] using hsource.2
    · simp only [rowAdvance, hzero, if_pos]
      exact Nat.le_refl state.memory.size
  · let a := sourceWord state.memory state.activeWords aPtr state.i
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let final := iterate a bPtr resultPtr state.i bCount initial
    have hinitialCovered : MemoryCovered initial.memory initial.activeWords := by
      simpa only [initial, initialInnerState, sourceWords, afterLoad] using hsource.1
    have hinitialFit : initial.activeWords.toNat * 32 < UInt256.size := by
      simpa only [initial, initialInnerState, sourceWords, afterLoad] using hsource.2
    have hiter := iterate_coverage_of_gap a bPtr resultPtr state.i bCount initial
      hinitialCovered hinitialFit (by simpa only [a, initial] using hinner)
    have hcarry := carryMemory_coverage_of_gap final.memory final.activeWords resultPtr state.i
      (UInt256.ofNat bCount) final.carry hcarryFit
      (by simpa only [a, initial, final] using hcarryGap)
      (by simpa only [final] using hiter.1)
      (by simpa only [final] using hiter.2.1)
    have hfinalLeRow : final.memory.size ≤
        (carryMemory final.memory final.activeWords resultPtr state.i
          (UInt256.ofNat bCount) final.carry).size := by
      rw [hcarry.2.2]
      exact Nat.le_max_left _ _
    simpa only [rowAdvance, hzero, if_neg, nonzeroRowMemory, nonzeroRowWords,
      completedInnerState, a, initial, final] using
        And.intro hcarry.1
          (And.intro hcarry.2.1 (hiter.2.2.trans hfinalLeRow))

/-- Address-safety obligations for a row whose stores may cross bounded implicit-zero gaps. -/
def RowAccessSafeGap
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState) : Prop :=
  (sourcePtr aPtr state.i).toNat + 32 + 31 < UInt256.size ∧
  (∀ q, q < bCount →
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
      bPtr resultPtr state.i q initial
    (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
      (elementPtr resultPtr (state.i + current.j)).toNat + 32 + 31 < UInt256.size ∧
      (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size) ∧
  (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 + 31 < UInt256.size ∧
  (let initial := initialInnerState state.memory state.activeWords aPtr state.i
   let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
     bPtr resultPtr state.i bCount initial
   (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size < USize.size)

/-- One selected row stays below a common logical allocation end when all inner destinations and
the final carry destination lie below it. -/
theorem rowAdvance_memory_size_le_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState) (bound : Nat)
    (hstate : state.memory.size ≤ bound)
    (hinner : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      (elementPtr resultPtr (state.i + current.j)).toNat + 32 ≤ bound ∧
        (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size <
          USize.size)
    (hcarryEnd : (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32 ≤ bound)
    (hcarryGap :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size <
        USize.size) :
    (rowAdvance aPtr bPtr resultPtr bCount state).memory.size ≤ bound := by
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · simpa only [rowAdvance, hzero, if_pos] using hstate
  · let a := sourceWord state.memory state.activeWords aPtr state.i
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let final := iterate a bPtr resultPtr state.i bCount initial
    have hfinalLe : final.memory.size ≤ bound := by
      apply iterate_memory_size_le_of_gap a bPtr resultPtr state.i bCount initial bound
      · simpa only [initial, initialInnerState] using hstate
      · simpa only [a, initial] using hinner
    have hcarrySize :
        (carryMemory final.memory final.activeWords resultPtr state.i
          (UInt256.ofNat bCount) final.carry).size =
          max final.memory.size
            ((carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32) := by
      unfold carryMemory
      exact toByteArray_write_size_eq_max _ _ _ (by simpa only [a, initial, final] using hcarryGap)
    rw [rowAdvance, if_neg hzero]
    change (nonzeroRowMemory state.memory state.activeWords aPtr bPtr resultPtr state.i
      bCount).size ≤ bound
    change (carryMemory final.memory final.activeWords resultPtr state.i
      (UInt256.ofNat bCount) final.carry).size ≤ bound
    rw [hcarrySize]
    exact max_le hfinalLe hcarryEnd

/-- A selected row cannot shrink concrete memory, including across bounded implicit-zero gaps. -/
theorem rowAdvance_memory_size_mono_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState)
    (hgaps : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size)
    (hcarryGap :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size <
        USize.size) :
    state.memory.size ≤ (rowAdvance aPtr bPtr resultPtr bCount state).memory.size := by
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · simpa only [rowAdvance, hzero, if_pos] using (le_rfl : state.memory.size ≤ state.memory.size)
  · let a := sourceWord state.memory state.activeWords aPtr state.i
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let final := iterate a bPtr resultPtr state.i bCount initial
    have hinner := iterate_memory_size_mono_of_gap a bPtr resultPtr state.i bCount initial
      (by simpa only [a, initial] using hgaps)
    have hcarrySize :
        (carryMemory final.memory final.activeWords resultPtr state.i
          (UInt256.ofNat bCount) final.carry).size =
          max final.memory.size
            ((carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat + 32) := by
      unfold carryMemory
      exact toByteArray_write_size_eq_max _ _ _ (by simpa only [a, initial, final] using hcarryGap)
    rw [rowAdvance, if_neg hzero]
    change state.memory.size ≤
      (carryMemory final.memory final.activeWords resultPtr state.i
        (UInt256.ofNat bCount) final.carry).size
    rw [hcarrySize]
    exact hinner.trans (Nat.le_max_left _ _)

/-- A complete 32-byte word below every selected destination is unchanged by one outer row. -/
theorem rowAdvance_read32_below_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount read : Nat) (state : OuterState)
    (hread : read + 32 ≤ state.memory.size)
    (hgaps : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size)
    (hbelow : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      read + 32 ≤ (elementPtr resultPtr (state.i + current.j)).toNat)
    (hcarryGap :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size <
        USize.size)
    (hcarryBelow : read + 32 ≤
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat) :
    (rowAdvance aPtr bPtr resultPtr bCount state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · simp only [rowAdvance, hzero, if_pos]
  · let a := sourceWord state.memory state.activeWords aPtr state.i
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let final := iterate a bPtr resultPtr state.i bCount initial
    have hinner := iterate_read32_below_of_gap a bPtr resultPtr state.i bCount read initial
      (by simpa only [initial, initialInnerState] using hread)
      (by simpa only [a, initial] using hgaps)
      (by simpa only [a, initial] using hbelow)
    have hmono := iterate_memory_size_mono_of_gap a bPtr resultPtr state.i bCount initial
      (by simpa only [a, initial] using hgaps)
    have hfinalRead : read + 32 ≤ final.memory.size :=
      hread.trans (by simpa only [initial, initialInnerState, final] using hmono)
    have hcarry :
        (carryMemory final.memory final.activeWords resultPtr state.i
          (UInt256.ofNat bCount) final.carry).readWithPadding read 32 =
          final.memory.readWithPadding read 32 := by
      unfold carryMemory
      exact toByteArray_write_read_below_of_gap _ _ _ _ hfinalRead hcarryBelow
        (by simpa only [a, initial, final] using hcarryGap)
    rw [rowAdvance, if_neg hzero]
    change (carryMemory final.memory final.activeWords resultPtr state.i
      (UInt256.ofNat bCount) final.carry).readWithPadding read 32 = _
    exact hcarry.trans hinner

/-- The row-wise allocation upper bound composes across every selected outer prefix. -/
theorem rowsIterate_memory_size_le_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount count : Nat) (state : OuterState) (bound : Nat)
    (hstate : state.memory.size ≤ bound)
    (hsafe : ∀ q, q < count →
      RowAccessSafeGap aPtr bPtr resultPtr bCount
        (rowsIterate aPtr bPtr resultPtr bCount q state))
    (hends : ∀ q, q < count →
      let outer := rowsIterate aPtr bPtr resultPtr bCount q state
      (∀ p, p < bCount →
        let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
        let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
          bPtr resultPtr outer.i p initial
        (elementPtr resultPtr (outer.i + current.j)).toNat + 32 ≤ bound) ∧
      (carryPtr resultPtr outer.i (UInt256.ofNat bCount)).toNat + 32 ≤ bound) :
    (rowsIterate aPtr bPtr resultPtr bCount count state).memory.size ≤ bound := by
  induction count generalizing state with
  | zero => exact hstate
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      have hfirstSafe : RowAccessSafeGap aPtr bPtr resultPtr bCount state := by
        simpa only [rowsIterate] using hsafe 0 (by omega)
      have hfirstEnds := hends 0 (by omega)
      have hnextLe := rowAdvance_memory_size_le_of_gap aPtr bPtr resultPtr bCount state bound
        hstate
        (by
          intro p hp
          exact ⟨by simpa only [rowsIterate] using hfirstEnds.1 p hp,
            hfirstSafe.2.1 p hp |>.2.2⟩)
        (by simpa only [rowsIterate] using hfirstEnds.2)
        hfirstSafe.2.2.2
      have htailSafe : ∀ q, q < count →
          RowAccessSafeGap aPtr bPtr resultPtr bCount
            (rowsIterate aPtr bPtr resultPtr bCount q next) := by
        intro q hq
        simpa only [next, rowsIterate_advance] using hsafe (q + 1) (by omega)
      have htailEnds : ∀ q, q < count →
          let outer := rowsIterate aPtr bPtr resultPtr bCount q next
          (∀ p, p < bCount →
            let initial := initialInnerState outer.memory outer.activeWords aPtr outer.i
            let current := iterate (sourceWord outer.memory outer.activeWords aPtr outer.i)
              bPtr resultPtr outer.i p initial
            (elementPtr resultPtr (outer.i + current.j)).toNat + 32 ≤ bound) ∧
          (carryPtr resultPtr outer.i (UInt256.ofNat bCount)).toNat + 32 ≤ bound := by
        intro q hq
        simpa only [next, rowsIterate_advance] using hends (q + 1) (by omega)
      simpa only [next, rowsIterate] using ih next hnextLe htailSafe htailEnds

/-- Bounded-gap row coverage and monotone concrete memory growth compose across the full outer
loop. -/
theorem rowsIterate_coverage_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount count : Nat) (state : OuterState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hsafe : ∀ q, q < count →
      RowAccessSafeGap aPtr bPtr resultPtr bCount
        (rowsIterate aPtr bPtr resultPtr bCount q state)) :
    MemoryCovered (rowsIterate aPtr bPtr resultPtr bCount count state).memory
        (rowsIterate aPtr bPtr resultPtr bCount count state).activeWords ∧
      (rowsIterate aPtr bPtr resultPtr bCount count state).activeWords.toNat * 32 <
        UInt256.size ∧
      state.memory.size ≤
        (rowsIterate aPtr bPtr resultPtr bCount count state).memory.size := by
  induction count generalizing state with
  | zero => exact ⟨hcovered, hawFit, le_rfl⟩
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      have hfirst : RowAccessSafeGap aPtr bPtr resultPtr bCount state := by
        simpa only [rowsIterate] using hsafe 0 (by omega)
      have hnext := rowAdvance_coverage_of_gap aPtr bPtr resultPtr bCount state
        hcovered hawFit hfirst.1 hfirst.2.1 hfirst.2.2.1 hfirst.2.2.2
      have htailSafe : ∀ q, q < count →
          RowAccessSafeGap aPtr bPtr resultPtr bCount
            (rowsIterate aPtr bPtr resultPtr bCount q next) := by
        intro q hq
        simpa only [next, rowsIterate_advance] using hsafe (q + 1) (by omega)
      have htail := ih next hnext.1 hnext.2.1 htailSafe
      simpa only [next, rowsIterate] using
        And.intro htail.1 (And.intro htail.2.1 (hnext.2.2.trans htail.2.2))

/-- A selected outer row preserves every complete padded range below all of its result writes,
including when those writes cross bounded implicit-zero gaps. -/
theorem rowAdvance_memoryWords_below_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount : Nat) (state : OuterState)
    (ptr words : Nat)
    (hbase : 32 ≤ state.memory.size)
    (hgaps : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size)
    (hinnerBelow : ∀ q, q < bCount →
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i q initial
      ptr + 32 * words ≤ (elementPtr resultPtr (state.i + current.j)).toNat)
    (hfinalBase :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      32 ≤ final.memory.size)
    (hcarryGap :
      let initial := initialInnerState state.memory state.activeWords aPtr state.i
      let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
        bPtr resultPtr state.i bCount initial
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size <
        USize.size)
    (hcarryBelow : ptr + 32 * words ≤
      (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat) :
    memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  by_cases hzero : sourceWord state.memory state.activeWords aPtr state.i = ⟨0⟩
  · simp only [rowAdvance, hzero, if_pos]
  · let a := sourceWord state.memory state.activeWords aPtr state.i
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let final := iterate a bPtr resultPtr state.i bCount initial
    have hinner := iterate_memoryWords_below_of_gap a bPtr resultPtr state.i bCount initial
      ptr words (by simpa only [initial, initialInnerState] using hbase)
      (by simpa only [a, initial] using hgaps)
      (by simpa only [a, initial] using hinnerBelow)
    have hcarry := carryMemory_words_below_of_gap final.memory final.activeWords resultPtr
      state.i (UInt256.ofNat bCount) final.carry ptr words
      (by simpa only [a, initial, final] using hfinalBase)
      (by simpa only [a, initial, final] using hcarryGap) hcarryBelow
    rw [show memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount state).memory ptr words =
        memoryWordsFrom
          (carryMemory final.memory final.activeWords resultPtr state.i
            (UInt256.ofNat bCount) final.carry) ptr words by
      simp [rowAdvance, hzero, nonzeroRowMemory, a, final,
        completedInnerState, initial]]
    rw [hcarry, hinner]
    rfl

/-- Bundled premises for preserving one complete padded range below a selected outer row. -/
def RowBelowFrameSafeGap
    (aPtr bPtr resultPtr : UInt256) (bCount ptr words : Nat) (state : OuterState) : Prop :=
  32 ≤ state.memory.size ∧
  (∀ q, q < bCount →
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
      bPtr resultPtr state.i q initial
    (elementPtr resultPtr (state.i + current.j)).toNat - current.memory.size < USize.size) ∧
  (∀ q, q < bCount →
    let initial := initialInnerState state.memory state.activeWords aPtr state.i
    let current := iterate (sourceWord state.memory state.activeWords aPtr state.i)
      bPtr resultPtr state.i q initial
    ptr + 32 * words ≤ (elementPtr resultPtr (state.i + current.j)).toNat) ∧
  (let initial := initialInnerState state.memory state.activeWords aPtr state.i
   let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
     bPtr resultPtr state.i bCount initial
   32 ≤ final.memory.size) ∧
  (let initial := initialInnerState state.memory state.activeWords aPtr state.i
   let final := iterate (sourceWord state.memory state.activeWords aPtr state.i)
     bPtr resultPtr state.i bCount initial
   (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat - final.memory.size <
     USize.size) ∧
  ptr + 32 * words ≤ (carryPtr resultPtr state.i (UInt256.ofNat bCount)).toNat

/-- A complete outer-loop prefix preserves a padded range below every row destination. -/
theorem rowsIterate_memoryWords_below_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount count : Nat) (state : OuterState)
    (ptr words : Nat)
    (hsafe : ∀ q, q < count →
      RowBelowFrameSafeGap aPtr bPtr resultPtr bCount ptr words
        (rowsIterate aPtr bPtr resultPtr bCount q state)) :
    memoryWordsFrom (rowsIterate aPtr bPtr resultPtr bCount count state).memory ptr words =
      memoryWordsFrom state.memory ptr words := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      have hfirst : RowBelowFrameSafeGap aPtr bPtr resultPtr bCount ptr words state := by
        simpa only [rowsIterate] using hsafe 0 (by omega)
      have hhead := rowAdvance_memoryWords_below_of_gap aPtr bPtr resultPtr bCount state
        ptr words hfirst.1 hfirst.2.1 hfirst.2.2.1 hfirst.2.2.2.1
        hfirst.2.2.2.2.1 hfirst.2.2.2.2.2
      have htailSafe : ∀ q, q < count →
          RowBelowFrameSafeGap aPtr bPtr resultPtr bCount ptr words
            (rowsIterate aPtr bPtr resultPtr bCount q next) := by
        intro q hq
        simpa only [next, rowsIterate_advance] using hsafe (q + 1) (by omega)
      have htail := ih next htailSafe
      calc
        memoryWordsFrom (rowsIterate aPtr bPtr resultPtr bCount (count + 1) state).memory
            ptr words =
          memoryWordsFrom (rowsIterate aPtr bPtr resultPtr bCount count next).memory
            ptr words := by rfl
        _ = memoryWordsFrom next.memory ptr words := htail
        _ = memoryWordsFrom state.memory ptr words := hhead

/-- A complete outer-loop prefix preserves a raw 32-byte word below every row destination. -/
theorem rowsIterate_read32_below_of_gap
    (aPtr bPtr resultPtr : UInt256) (bCount count read : Nat) (state : OuterState)
    (hread : read + 32 ≤ state.memory.size)
    (hsafe : ∀ q, q < count →
      RowBelowFrameSafeGap aPtr bPtr resultPtr bCount read 1
        (rowsIterate aPtr bPtr resultPtr bCount q state)) :
    (rowsIterate aPtr bPtr resultPtr bCount count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      have hfirst : RowBelowFrameSafeGap aPtr bPtr resultPtr bCount read 1 state := by
        simpa only [rowsIterate] using hsafe 0 (by omega)
      have hhead := rowAdvance_read32_below_of_gap aPtr bPtr resultPtr bCount read state
        hread hfirst.2.1 (by simpa only [Nat.mul_one] using hfirst.2.2.1)
        hfirst.2.2.2.2.1 (by simpa only [Nat.mul_one] using hfirst.2.2.2.2.2)
      have hmono := rowAdvance_memory_size_mono_of_gap aPtr bPtr resultPtr bCount state
        hfirst.2.1 hfirst.2.2.2.2.1
      have hnextRead : read + 32 ≤ next.memory.size := by
        exact hread.trans (by simpa only [next] using hmono)
      have htailSafe : ∀ q, q < count →
          RowBelowFrameSafeGap aPtr bPtr resultPtr bCount read 1
            (rowsIterate aPtr bPtr resultPtr bCount q next) := by
        intro q hq
        simpa only [next, rowsIterate_advance] using hsafe (q + 1) (by omega)
      have htail := ih next hnextRead htailSafe
      simpa only [next, rowsIterate] using htail.trans hhead

/-- If each concrete selected row satisfies `SchoolbookRowUpdate` on the same result range, the
exact outer recurrence composes to the pure `SchoolbookRows` relation. -/
theorem rowsIterate_schoolbookRows
    (aPtr bPtr resultPtr : UInt256) (bCount count shift resultLength : Nat)
    (state : OuterState) (operandWords : List UInt256)
    (hupdates : ∀ q, q < count →
      let current := rowsIterate aPtr bPtr resultPtr bCount q state
      Modexp.SchoolbookRowUpdate
        (sourceWord current.memory current.activeWords aPtr current.i)
        operandWords (shift + q)
        (memoryWordsFrom current.memory (resultPtr.toNat + 32) resultLength)
        (memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount current).memory
          (resultPtr.toNat + 32) resultLength)) :
    Modexp.SchoolbookRows operandWords shift
      (outerSourceWords aPtr bPtr resultPtr bCount count state)
      (memoryWordsFrom state.memory (resultPtr.toNat + 32) resultLength)
      (memoryWordsFrom (rowsIterate aPtr bPtr resultPtr bCount count state).memory
        (resultPtr.toNat + 32) resultLength) := by
  induction count generalizing state shift with
  | zero => exact Modexp.SchoolbookRows.nil shift _
  | succ count ih =>
      let next := rowAdvance aPtr bPtr resultPtr bCount state
      have hhead : Modexp.SchoolbookRowUpdate
          (sourceWord state.memory state.activeWords aPtr state.i)
          operandWords shift
          (memoryWordsFrom state.memory (resultPtr.toNat + 32) resultLength)
          (memoryWordsFrom next.memory (resultPtr.toNat + 32) resultLength) := by
        simpa only [Nat.add_zero, rowsIterate] using hupdates 0 (by omega)
      have htailUpdates : ∀ q, q < count →
          let current := rowsIterate aPtr bPtr resultPtr bCount q next
          Modexp.SchoolbookRowUpdate
            (sourceWord current.memory current.activeWords aPtr current.i)
            operandWords (shift + 1 + q)
            (memoryWordsFrom current.memory (resultPtr.toNat + 32) resultLength)
            (memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount current).memory
              (resultPtr.toNat + 32) resultLength) := by
        intro q hq
        have h := hupdates (q + 1) (by omega)
        simpa only [next, rowsIterate_advance, Nat.add_assoc,
          show shift + (q + 1) = shift + 1 + q by omega] using h
      have htail := ih (state := next) (shift := shift + 1) htailUpdates
      apply Modexp.SchoolbookRows.cons shift
        (sourceWord state.memory state.activeWords aPtr state.i)
        (outerSourceWords aPtr bPtr resultPtr bCount count next)
        (memoryWordsFrom state.memory (resultPtr.toNat + 32) resultLength)
        (memoryWordsFrom next.memory (resultPtr.toNat + 32) resultLength)
        (memoryWordsFrom (rowsIterate aPtr bPtr resultPtr bCount count next).memory
          (resultPtr.toNat + 32) resultLength)
        hhead
      simpa only [next] using htail

/-- A concrete zero-initialized outer execution satisfying the per-row memory relation returns
the exact product of its observed source vector and fixed operand vector. -/
theorem rowsIterate_from_zero_value
    (aPtr bPtr resultPtr : UInt256) (bCount count resultLength : Nat)
    (state : OuterState) (operandWords : List UInt256)
    (hzero : memoryWordsFrom state.memory (resultPtr.toNat + 32) resultLength =
      List.replicate resultLength (⟨0⟩ : UInt256))
    (hupdates : ∀ q, q < count →
      let current := rowsIterate aPtr bPtr resultPtr bCount q state
      Modexp.SchoolbookRowUpdate
        (sourceWord current.memory current.activeWords aPtr current.i)
        operandWords q
        (memoryWordsFrom current.memory (resultPtr.toNat + 32) resultLength)
        (memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount current).memory
          (resultPtr.toNat + 32) resultLength)) :
    Modexp.wordLimbsToNat
        (memoryWordsFrom (rowsIterate aPtr bPtr resultPtr bCount count state).memory
          (resultPtr.toNat + 32) resultLength) =
      Modexp.wordLimbsToNat
          (outerSourceWords aPtr bPtr resultPtr bCount count state) *
        Modexp.wordLimbsToNat operandWords := by
  have hupdatesZero : ∀ q, q < count →
      let current := rowsIterate aPtr bPtr resultPtr bCount q state
      Modexp.SchoolbookRowUpdate
        (sourceWord current.memory current.activeWords aPtr current.i)
        operandWords (0 + q)
        (memoryWordsFrom current.memory (resultPtr.toNat + 32) resultLength)
        (memoryWordsFrom (rowAdvance aPtr bPtr resultPtr bCount current).memory
          (resultPtr.toNat + 32) resultLength) := by
    simpa only [Nat.zero_add] using hupdates
  have hrows := rowsIterate_schoolbookRows aPtr bPtr resultPtr bCount count 0
    resultLength state operandWords hupdatesZero
  rw [hzero] at hrows
  exact Modexp.schoolbookRows_from_zero hrows

end Modexp.MultiLimbSchoolbookMulTrace
