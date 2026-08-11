import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulMemorySemantic
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSOperandLinks
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSLayoutLinks

/-! # Standalone schoolbook input collector semantics -/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookMulTrace

open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbArithmeticTrace

/-- A generic multiply-pass operand collector remains its initial immutable range when result
writes may extend concrete memory at its frontier. -/
theorem multiplyPassOperandWords_eq_initialMemory_extending
    (a : UInt256) (count : Nat) (state : MultiplyPassState)
    (hoperandFit : state.operandPtr.toNat + 32 * count < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * count < UInt256.size)
    (hseparate : state.operandPtr.toNat + 32 * count ≤ state.resultPtr.toNat)
    (hloads : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat)
    (hstarts : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat ≤ current.memory.size) :
    multiplyPassOperandWords a count state =
      memoryWordsFrom state.memory state.operandPtr.toNat count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hoperandStep : next.operandPtr.toNat = state.operandPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.operandPtr (by omega)
      have hresultStep : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextLoads : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hloads (q + 1) (by omega)
      have hnextStarts : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hstarts (q + 1) (by omega)
      have htail := ih next (by rw [hoperandStep]; omega)
        (by rw [hresultStep]; omega) (by rw [hoperandStep, hresultStep]; omega)
        hnextLoads hnextStarts
      have hheadNat := hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              state.memory state.operandPtr.toNat) := by
        apply u256_inj
        rw [show (schoolbookOperands state.memory state.activeWords state.operandPtr
          state.resultPtr state.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.operandPtr.toNat by
          simpa only [multiplyPassIterate] using hheadNat]
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      have hfirstStart : state.resultPtr.toNat ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hstarts 0 (by omega)
      have hframeRaw := memoryWordsFrom_write_above
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1.toByteArray state.memory state.resultPtr.toNat
        next.operandPtr.toNat count (by rw [toByteArray_size]) hfirstStart
        (by rw [hoperandStep]; omega)
      have hframe : memoryWordsFrom next.memory next.operandPtr.toNat count =
          memoryWordsFrom state.memory next.operandPtr.toNat count := by
        simpa only [next, multiplyPassAdvance, multiplyPassMemory] using hframeRaw
      simp only [multiplyPassOperandWords, memoryWordsFrom]
      change
        (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 :: multiplyPassOperandWords a count next =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              state.memory state.operandPtr.toNat) ::
            memoryWordsFrom state.memory (state.operandPtr.toNat + 32) count
      rw [hhead, htail, hframe, hoperandStep]

/-- A generic multiply-pass prior-result collector is its initial padded destination range even
when the first write materializes an implicit-zero word. -/
theorem multiplyPassPriorWords_eq_memoryWordsFrom_extending
    (a : UInt256) (count : Nat) (state : MultiplyPassState)
    (hresultFit : state.resultPtr.toNat + 32 * count < UInt256.size)
    (hloads : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hstarts : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat ≤ current.memory.size) :
    multiplyPassPriorWords a count state =
      memoryWordsFrom state.memory state.resultPtr.toNat count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hptr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hnextLoads : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).2.1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hloads (q + 1) (by omega)
      have hnextStarts : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat ≤ current.memory.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hstarts (q + 1) (by omega)
      have htail := ih next (by rw [hptr]; omega) hnextLoads hnextStarts
      have hheadNat := hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).2.1 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              state.memory state.resultPtr.toNat) := by
        apply u256_inj
        rw [show (schoolbookOperands state.memory state.activeWords state.operandPtr
          state.resultPtr state.carry).2.1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.resultPtr.toNat by
          simpa only [multiplyPassIterate] using hheadNat]
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      have hfirstStart : state.resultPtr.toNat ≤ state.memory.size := by
        simpa only [multiplyPassIterate] using hstarts 0 (by omega)
      have hframe := memoryWordsFrom_write_below_extending
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1 state.memory state.resultPtr.toNat
        (state.resultPtr.toNat + 32) count hfirstStart (by omega)
      simp only [multiplyPassPriorWords, memoryWordsFrom]
      rw [hhead]
      congr 1
      rw [← hframe]
      have hadd : (state.resultPtr + ⟨32⟩).toNat = state.resultPtr.toNat + 32 := by
        simpa only [next, multiplyPassAdvance] using hptr
      simpa only [next, multiplyPassAdvance, multiplyPassMemory, hadd] using htail

/-- A generic multiply-pass operand collector remains its initial immutable range when result
writes may cross bounded implicit-zero gaps. -/
theorem multiplyPassOperandWords_eq_initialMemory_of_gap
    (a : UInt256) (count : Nat) (state : MultiplyPassState)
    (hoperandFit : state.operandPtr.toNat + 32 * count < UInt256.size)
    (hresultFit : state.resultPtr.toNat + 32 * count < UInt256.size)
    (hseparate : state.operandPtr.toNat + 32 * count ≤ state.resultPtr.toNat)
    (hbase : 32 ≤ state.memory.size)
    (hloads : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat)
    (hgaps : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat - current.memory.size < USize.size) :
    multiplyPassOperandWords a count state =
      memoryWordsFrom state.memory state.operandPtr.toNat count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hoperandStep : next.operandPtr.toNat = state.operandPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.operandPtr (by omega)
      have hresultStep : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hfirstGap : state.resultPtr.toNat - state.memory.size < USize.size := by
        simpa only [multiplyPassIterate] using hgaps 0 (by omega)
      have hnextBase : 32 ≤ next.memory.size := by
        have hsize : next.memory.size =
            max state.memory.size (state.resultPtr.toNat + 32) := by
          dsimp only [next, multiplyPassAdvance, multiplyPassMemory]
          exact toByteArray_write_size_eq_max _ _ _ hfirstGap
        rw [hsize]
        exact hbase.trans (Nat.le_max_left _ _)
      have hnextLoads : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hloads (q + 1) (by omega)
      have hnextGaps : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hgaps (q + 1) (by omega)
      have htail := ih next (by rw [hoperandStep]; omega)
        (by rw [hresultStep]; omega) (by rw [hoperandStep, hresultStep]; omega)
        hnextBase hnextLoads hnextGaps
      have hheadNat := hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              state.memory state.operandPtr.toNat) := by
        apply u256_inj
        rw [show (schoolbookOperands state.memory state.activeWords state.operandPtr
          state.resultPtr state.carry).1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.operandPtr.toNat by
          simpa only [multiplyPassIterate] using hheadNat]
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      have hframeRaw := memoryWordsFrom_write_above_padded_of_gap
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1 state.memory state.resultPtr.toNat
        next.operandPtr.toNat count hbase (by rw [hoperandStep]; omega) hfirstGap
      have hframe : memoryWordsFrom next.memory next.operandPtr.toNat count =
          memoryWordsFrom state.memory next.operandPtr.toNat count := by
        simpa only [next, multiplyPassAdvance, multiplyPassMemory] using hframeRaw
      simp only [multiplyPassOperandWords, memoryWordsFrom]
      change
        (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).1 :: multiplyPassOperandWords a count next =
          UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              state.memory state.operandPtr.toNat) ::
            memoryWordsFrom state.memory (state.operandPtr.toNat + 32) count
      rw [hhead, htail, hframe, hoperandStep]

/-- A generic multiply-pass prior-result collector is its initial padded destination range when
writes may cross bounded implicit-zero gaps. -/
theorem multiplyPassPriorWords_eq_memoryWordsFrom_of_gap
    (a : UInt256) (count : Nat) (state : MultiplyPassState)
    (hresultFit : state.resultPtr.toNat + 32 * count < UInt256.size)
    (hloads : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat)
    (hgaps : ∀ q, q < count →
      let current := multiplyPassIterate a q state
      current.resultPtr.toNat - current.memory.size < USize.size) :
    multiplyPassPriorWords a count state =
      memoryWordsFrom state.memory state.resultPtr.toNat count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplyPassAdvance a state
      have hptr : next.resultPtr.toNat = state.resultPtr.toNat + 32 := by
        dsimp only [next, multiplyPassAdvance]
        exact uadd_word_lit32_toNat state.resultPtr (by omega)
      have hfirstGap : state.resultPtr.toNat - state.memory.size < USize.size := by
        simpa only [multiplyPassIterate] using hgaps 0 (by omega)
      have hnextLoads : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          (schoolbookOperands current.memory current.activeWords current.operandPtr
            current.resultPtr current.carry).2.1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hloads (q + 1) (by omega)
      have hnextGaps : ∀ q, q < count →
          let current := multiplyPassIterate a q next
          current.resultPtr.toNat - current.memory.size < USize.size := by
        intro q hq
        simpa only [next, multiplyPassIterate_advance] using hgaps (q + 1) (by omega)
      have htail := ih next (by rw [hptr]; omega) hnextLoads hnextGaps
      have hheadNat := hloads 0 (by omega)
      have hhead :
          (schoolbookOperands state.memory state.activeWords state.operandPtr
            state.resultPtr state.carry).2.1 =
            UInt256.ofNat (Modexp.MultiLimbMemoryModel.memoryWordNat
              state.memory state.resultPtr.toNat) := by
        apply u256_inj
        rw [show (schoolbookOperands state.memory state.activeWords state.operandPtr
          state.resultPtr state.carry).2.1.toNat =
            Modexp.MultiLimbMemoryModel.memoryWordNat state.memory state.resultPtr.toNat by
          simpa only [multiplyPassIterate] using hheadNat]
        rw [UInt256.toNat_ofNat_of_lt (memoryWordNat_lt_size _ _)]
      have hframe := memoryWordsFrom_write_below_of_gap
        (schoolbookStep state.memory state.activeWords state.operandPtr state.resultPtr
          a state.carry).1 state.memory state.resultPtr.toNat
        (state.resultPtr.toNat + 32) count hfirstGap (by omega)
      simp only [multiplyPassPriorWords, memoryWordsFrom]
      rw [hhead]
      congr 1
      rw [← hframe]
      have hadd : (state.resultPtr + ⟨32⟩).toNat = state.resultPtr.toNat + 32 := by
        simpa only [next, multiplyPassAdvance] using hptr
      simpa only [next, multiplyPassAdvance, multiplyPassMemory, hadd] using htail

/-- The standalone inner operand and prior-result collectors are their initial contiguous memory
ranges when the immutable operand range lies below the destination writes. -/
theorem innerInputWords_eq_initialMemory
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 3) < UInt256.size)
    (hbMem : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr bPtr current.j).toNat + 32 ≤ current.memory.size)
    (hresultMem : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size)
    (hoperandRange : (elementPtr bPtr state.j).toNat + 32 * count < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * count <
      UInt256.size)
    (hseparate : (elementPtr bPtr state.j).toNat + 32 * count ≤
      (elementPtr resultPtr (i + state.j)).toNat) :
    innerOperandWords a bPtr resultPtr i count state =
        memoryWordsFrom state.memory (elementPtr bPtr state.j).toNat count ∧
      innerPriorWords a bPtr resultPtr i count state =
        memoryWordsFrom state.memory (elementPtr resultPtr (i + state.j)).toNat count := by
  have hbFits2 : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size := by
    intro q hq
    have h := hbFits q hq
    omega
  have hresultFits2 : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size := by
    intro q hq
    have h := hresultFits q hq
    omega
  have hmap (q : Nat) (hq : q ≤ count) :
      asMultiplyPassState bPtr resultPtr i (iterate a bPtr resultPtr i q state) =
        multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state) := by
    apply asMultiplyPassState_iterate
    · intro p hp
      have h := hbFits p (by omega)
      omega
    · intro p hp
      have h := hresultFits p (by omega)
      omega
  have hcoverageAt (q : Nat) (hq : q < count) :
      MemoryCovered (iterate a bPtr resultPtr i q state).memory
          (iterate a bPtr resultPtr i q state).activeWords ∧
        (iterate a bPtr resultPtr i q state).activeWords.toNat * 32 < UInt256.size := by
    have hsteps : ∀ p, p < q →
        let current := iterate a bPtr resultPtr i p state
        (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
          (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 <
            UInt256.size ∧
          (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size := by
      intro p hp
      let current := iterate a bPtr resultPtr i p state
      have hbBase : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
        simpa only [current] using hbFits p (by omega)
      have hresultBase : resultPtr.toNat + 32 * ((i + current.j).toNat + 3) <
          UInt256.size := by
        simpa only [current] using hresultFits p (by omega)
      have hbAddress : (elementPtr bPtr current.j).toNat =
          bPtr.toNat + 32 * (current.j.toNat + 1) :=
        elementPtr_toNat_of_fit bPtr current.j (by omega)
      have hresultAddress : (elementPtr resultPtr (i + current.j)).toNat =
          resultPtr.toNat + 32 * ((i + current.j).toNat + 1) :=
        elementPtr_toNat_of_fit resultPtr (i + current.j) (by omega)
      change (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
        (elementPtr resultPtr (i + current.j)).toNat + 32 ≤ current.memory.size
      refine ⟨by rw [hbAddress]; omega, by rw [hresultAddress]; omega, ?_⟩
      simpa only [current] using hresultMem p (by omega)
    have hiter := iterate_coverage_size a bPtr resultPtr i q state
      hcovered hawFit hsteps
    exact ⟨hiter.1, hiter.2.1⟩
  have hgenericWrites : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      current.resultPtr.toNat + 32 ≤ current.memory.size := by
    intro q hq
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState] using hresultMem q hq
  have hgenericOperandLoads : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.operandPtr.toNat := by
    intro q hq
    let current := iterate a bPtr resultPtr i q state
    have hcov := hcoverageAt q hq
    have hbBase : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
      simpa only [current] using hbFits q hq
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (current.j.toNat + 1) :=
      elementPtr_toNat_of_fit bPtr current.j (by omega)
    have hbPtrFit : (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size := by
      rw [hbAddress]
      omega
    have hloads := operands_toNat_eq_memoryWords current.memory current.activeWords
      bPtr resultPtr i current.j current.carry hbPtrFit
      (by simpa only [current] using hbMem q hq)
      (by simpa only [current] using hresultMem q hq) hcov.1 hcov.2
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState, operands] using hloads.1
  have hgenericPriorLoads : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory
          current.resultPtr.toNat := by
    intro q hq
    let current := iterate a bPtr resultPtr i q state
    have hcov := hcoverageAt q hq
    have hbBase : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
      simpa only [current] using hbFits q hq
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (current.j.toNat + 1) :=
      elementPtr_toNat_of_fit bPtr current.j (by omega)
    have hbPtrFit : (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size := by
      rw [hbAddress]
      omega
    have hloads := operands_toNat_eq_memoryWords current.memory current.activeWords
      bPtr resultPtr i current.j current.carry hbPtrFit
      (by simpa only [current] using hbMem q hq)
      (by simpa only [current] using hresultMem q hq) hcov.1 hcov.2
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState, operands] using hloads.2
  have hoperand := multiplyPassOperandWords_eq_initialMemory a count
    (asMultiplyPassState bPtr resultPtr i state) hoperandRange hresultRange hseparate
    hgenericOperandLoads hgenericWrites
  have hprior := multiplyPassPriorWords_eq_memoryWordsFrom a count
    (asMultiplyPassState bPtr resultPtr i state) hresultRange
    hgenericPriorLoads hgenericWrites
  have hcollectors := innerCollectors_eq_multiplyPassCollectors
    a bPtr resultPtr i count state hbFits2 hresultFits2
  constructor
  · rw [hcollectors.1]
    simpa only [asMultiplyPassState] using hoperand
  · rw [hcollectors.2.1]
    simpa only [asMultiplyPassState] using hprior

/-- The standalone operand and prior-result collectors equal their initial padded memory ranges
when destination stores begin at or within the concrete allocator frontier. -/
theorem innerInputWords_eq_initialMemory_extending
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 3) < UInt256.size)
    (hstarts : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size)
    (hoperandRange : (elementPtr bPtr state.j).toNat + 32 * count < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * count <
      UInt256.size)
    (hseparate : (elementPtr bPtr state.j).toNat + 32 * count ≤
      (elementPtr resultPtr (i + state.j)).toNat) :
    innerOperandWords a bPtr resultPtr i count state =
        memoryWordsFrom state.memory (elementPtr bPtr state.j).toNat count ∧
      innerPriorWords a bPtr resultPtr i count state =
        memoryWordsFrom state.memory (elementPtr resultPtr (i + state.j)).toNat count := by
  have hbFits2 : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size := by
    intro q hq
    have h := hbFits q hq
    omega
  have hresultFits2 : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size := by
    intro q hq
    have h := hresultFits q hq
    omega
  have hmap (q : Nat) (hq : q ≤ count) :
      asMultiplyPassState bPtr resultPtr i (iterate a bPtr resultPtr i q state) =
        multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state) := by
    apply asMultiplyPassState_iterate
    · intro p hp
      exact hbFits2 p (by omega)
    · intro p hp
      exact hresultFits2 p (by omega)
  have hcoverageAt (q : Nat) (hq : q < count) :
      MemoryCovered (iterate a bPtr resultPtr i q state).memory
          (iterate a bPtr resultPtr i q state).activeWords ∧
        (iterate a bPtr resultPtr i q state).activeWords.toNat * 32 < UInt256.size := by
    have hsteps : ∀ p, p < q →
        let current := iterate a bPtr resultPtr i p state
        (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
          (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
          (elementPtr resultPtr (i + current.j)).toNat ≤ current.memory.size := by
      intro p hp
      let current := iterate a bPtr resultPtr i p state
      have hbBase := hbFits p (by omega)
      have hresultBase := hresultFits p (by omega)
      have hbBase' : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
        simpa only [current] using hbBase
      have hresultBase' : resultPtr.toNat + 32 * ((i + current.j).toNat + 3) <
          UInt256.size := by
        simpa only [current] using hresultBase
      have hbAddress := elementPtr_toNat_of_fit bPtr current.j (by
        omega)
      have hresultAddress := elementPtr_toNat_of_fit resultPtr (i + current.j) (by
        omega)
      refine ⟨by rw [hbAddress]; omega, by rw [hresultAddress]; omega, ?_⟩
      simpa only [current] using hstarts p (by omega)
    have hiter := iterate_coverage_extending a bPtr resultPtr i q state
      hcovered hawFit hsteps
    exact ⟨hiter.1, hiter.2.1⟩
  have hgenericStarts : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      current.resultPtr.toNat ≤ current.memory.size := by
    intro q hq
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState] using hstarts q hq
  have hgenericOperandLoads : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat := by
    intro q hq
    let current := iterate a bPtr resultPtr i q state
    have hcov := hcoverageAt q hq
    have hbBase := hbFits q hq
    have hbBase' : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
      simpa only [current] using hbBase
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (current.j.toNat + 1) :=
      elementPtr_toNat_of_fit bPtr current.j (by omega)
    have hloads := operands_toNat_eq_memoryWords_padded current.memory current.activeWords
      bPtr resultPtr i current.j current.carry (by rw [hbAddress]; omega) hcov.1 hcov.2
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState, operands] using hloads.1
  have hgenericPriorLoads : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
    intro q hq
    let current := iterate a bPtr resultPtr i q state
    have hcov := hcoverageAt q hq
    have hbBase := hbFits q hq
    have hbBase' : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
      simpa only [current] using hbBase
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (current.j.toNat + 1) :=
      elementPtr_toNat_of_fit bPtr current.j (by omega)
    have hloads := operands_toNat_eq_memoryWords_padded current.memory current.activeWords
      bPtr resultPtr i current.j current.carry (by rw [hbAddress]; omega) hcov.1 hcov.2
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState, operands] using hloads.2
  have hoperand := multiplyPassOperandWords_eq_initialMemory_extending a count
    (asMultiplyPassState bPtr resultPtr i state) hoperandRange hresultRange hseparate
    hgenericOperandLoads hgenericStarts
  have hprior := multiplyPassPriorWords_eq_memoryWordsFrom_extending a count
    (asMultiplyPassState bPtr resultPtr i state) hresultRange hgenericPriorLoads hgenericStarts
  have hcollectors := innerCollectors_eq_multiplyPassCollectors
    a bPtr resultPtr i count state hbFits2 hresultFits2
  constructor
  · rw [hcollectors.1]
    simpa only [asMultiplyPassState] using hoperand
  · rw [hcollectors.2.1]
    simpa only [asMultiplyPassState] using hprior

/-- The standalone operand and prior-result collectors equal their initial padded ranges when
destination stores may cross bounded implicit-zero gaps. -/
theorem innerInputWords_eq_initialMemory_of_gap
    (a bPtr resultPtr i : UInt256) (count : Nat) (state : InnerState)
    (hcovered : MemoryCovered state.memory state.activeWords)
    (hawFit : state.activeWords.toNat * 32 < UInt256.size)
    (hbase : 32 ≤ state.memory.size)
    (hbFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size)
    (hresultFits : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 3) < UInt256.size)
    (hgaps : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size)
    (hoperandRange : (elementPtr bPtr state.j).toNat + 32 * count < UInt256.size)
    (hresultRange : (elementPtr resultPtr (i + state.j)).toNat + 32 * count <
      UInt256.size)
    (hseparate : (elementPtr bPtr state.j).toNat + 32 * count ≤
      (elementPtr resultPtr (i + state.j)).toNat) :
    innerOperandWords a bPtr resultPtr i count state =
        memoryWordsFrom state.memory (elementPtr bPtr state.j).toNat count ∧
      innerPriorWords a bPtr resultPtr i count state =
        memoryWordsFrom state.memory (elementPtr resultPtr (i + state.j)).toNat count := by
  have hbFits2 : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      bPtr.toNat + 32 * (current.j.toNat + 2) < UInt256.size := by
    intro q hq
    have h := hbFits q hq
    omega
  have hresultFits2 : ∀ q, q < count →
      let current := iterate a bPtr resultPtr i q state
      resultPtr.toNat + 32 * ((i + current.j).toNat + 2) < UInt256.size := by
    intro q hq
    have h := hresultFits q hq
    omega
  have hmap (q : Nat) (hq : q ≤ count) :
      asMultiplyPassState bPtr resultPtr i (iterate a bPtr resultPtr i q state) =
        multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state) := by
    apply asMultiplyPassState_iterate
    · intro p hp
      exact hbFits2 p (by omega)
    · intro p hp
      exact hresultFits2 p (by omega)
  have hcoverageAt (q : Nat) (hq : q < count) :
      MemoryCovered (iterate a bPtr resultPtr i q state).memory
          (iterate a bPtr resultPtr i q state).activeWords ∧
        (iterate a bPtr resultPtr i q state).activeWords.toNat * 32 < UInt256.size := by
    have hsteps : ∀ p, p < q →
        let current := iterate a bPtr resultPtr i p state
        (elementPtr bPtr current.j).toNat + 32 + 31 < UInt256.size ∧
          (elementPtr resultPtr (i + current.j)).toNat + 32 + 31 < UInt256.size ∧
          (elementPtr resultPtr (i + current.j)).toNat - current.memory.size < USize.size := by
      intro p hp
      let current := iterate a bPtr resultPtr i p state
      have hbBase := hbFits p (by omega)
      have hresultBase := hresultFits p (by omega)
      have hbBase' : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
        simpa only [current] using hbBase
      have hresultBase' : resultPtr.toNat + 32 * ((i + current.j).toNat + 3) <
          UInt256.size := by
        simpa only [current] using hresultBase
      have hbAddress := elementPtr_toNat_of_fit bPtr current.j (by omega)
      have hresultAddress := elementPtr_toNat_of_fit resultPtr (i + current.j) (by omega)
      refine ⟨by rw [hbAddress]; omega, by rw [hresultAddress]; omega, ?_⟩
      simpa only [current] using hgaps p (by omega)
    have hiter := iterate_coverage_of_gap a bPtr resultPtr i q state
      hcovered hawFit hsteps
    exact ⟨hiter.1, hiter.2.1⟩
  have hgenericGaps : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      current.resultPtr.toNat - current.memory.size < USize.size := by
    intro q hq
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState] using hgaps q hq
  have hgenericOperandLoads : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.operandPtr.toNat := by
    intro q hq
    let current := iterate a bPtr resultPtr i q state
    have hcov := hcoverageAt q hq
    have hbBase := hbFits q hq
    have hbBase' : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
      simpa only [current] using hbBase
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (current.j.toNat + 1) :=
      elementPtr_toNat_of_fit bPtr current.j (by omega)
    have hloads := operands_toNat_eq_memoryWords_padded current.memory current.activeWords
      bPtr resultPtr i current.j current.carry (by rw [hbAddress]; omega) hcov.1 hcov.2
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState, operands] using hloads.1
  have hgenericPriorLoads : ∀ q, q < count →
      let current := multiplyPassIterate a q (asMultiplyPassState bPtr resultPtr i state)
      (schoolbookOperands current.memory current.activeWords current.operandPtr
        current.resultPtr current.carry).2.1.toNat =
        Modexp.MultiLimbMemoryModel.memoryWordNat current.memory current.resultPtr.toNat := by
    intro q hq
    let current := iterate a bPtr resultPtr i q state
    have hcov := hcoverageAt q hq
    have hbBase := hbFits q hq
    have hbBase' : bPtr.toNat + 32 * (current.j.toNat + 3) < UInt256.size := by
      simpa only [current] using hbBase
    have hbAddress : (elementPtr bPtr current.j).toNat =
        bPtr.toNat + 32 * (current.j.toNat + 1) :=
      elementPtr_toNat_of_fit bPtr current.j (by omega)
    have hloads := operands_toNat_eq_memoryWords_padded current.memory current.activeWords
      bPtr resultPtr i current.j current.carry (by rw [hbAddress]; omega) hcov.1 hcov.2
    rw [← hmap q (by omega)]
    simpa only [asMultiplyPassState, operands] using hloads.2
  have hoperand := multiplyPassOperandWords_eq_initialMemory_of_gap a count
    (asMultiplyPassState bPtr resultPtr i state) hoperandRange hresultRange hseparate hbase
    hgenericOperandLoads hgenericGaps
  have hprior := multiplyPassPriorWords_eq_memoryWordsFrom_of_gap a count
    (asMultiplyPassState bPtr resultPtr i state) hresultRange hgenericPriorLoads hgenericGaps
  have hcollectors := innerCollectors_eq_multiplyPassCollectors
    a bPtr resultPtr i count state hbFits2 hresultFits2
  constructor
  · rw [hcollectors.1]
    simpa only [asMultiplyPassState] using hoperand
  · rw [hcollectors.2.1]
    simpa only [asMultiplyPassState] using hprior

end Modexp.MultiLimbSchoolbookMulTrace
