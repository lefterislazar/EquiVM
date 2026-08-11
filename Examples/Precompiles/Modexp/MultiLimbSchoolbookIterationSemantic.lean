import Examples.Precompiles.Modexp.MultiLimbSchoolbookDigitFunction
import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisionSemantic

/-!
# Concrete-memory semantics of one schoolbook quotient digit

The execution contracts expose the in-place multiply-subtract and add-back loops as recursive
state machines. This file first relates those state machines to the pure Algorithm D list
operations over the exact words read at each concrete iteration. Keeping this bridge separate
from the address-layout lemmas makes explicit that no arithmetic result is supplied as a callback:
the result is derived from the bytecode recurrence itself.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookIterationSemantic

open MultiLimbSchoolbookDivision
open MultiLimbSchoolbookDivisionSemantic

set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Concrete divisor accesses are ordinary Solidity payload addresses when the bounded index and
pointer arithmetic do not wrap. -/
theorem multiplySubtractVAddress_ofNat_toNat
    (v : UInt256) (i : Nat)
    (hi : i ≤ 32)
    (hfit : v.toNat + 32 * (i + 1) < UInt256.size) :
    (multiplySubtractVAddress v (UInt256.ofNat i)).toNat =
      v.toNat + 32 * (i + 1) := by
  exact MultiLimbOddCompare.elementPtr_ofNat_toNat v i hi hfit

/-- The bytecode spells `u[current - 1 + i]` as the wrapped word expression
`current + i + ~0`; under the loop bounds this is the expected natural payload address. -/
theorem multiplySubtractUAddress_ofNat_toNat
    (u : UInt256) (current i : Nat)
    (hcurrent : 0 < current)
    (hsumWord : current + i < UInt256.size)
    (hindex : current + i - 1 ≤ 65)
    (hfit : u.toNat + 32 * (current + i) < UInt256.size) :
    (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)).toNat =
      u.toNat + 32 * (current + i) := by
  have hcurrentWord : current < UInt256.size := by omega
  have hiWord : i < UInt256.size := by omega
  have hadd :
      UInt256.ofNat current + UInt256.ofNat i = UInt256.ofNat (current + i) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hcurrentWord,
      UInt256.toNat_ofNat_of_lt hiWord, UInt256.toNat_ofNat_of_lt hsumWord,
      Nat.mod_eq_of_lt hsumWord]
  have hsumPos : 0 < current + i := by omega
  have hpred :
      UInt256.ofNat (current + i) + (⟨0⟩ : UInt256).lnot =
        UInt256.ofNat (current + i - 1) := by
    rw [show current + i = (current + i - 1) + 1 by omega, u256_add_comm]
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat ((current + i - 1) + 1)) =
      UInt256.ofNat (current + i - 1)
    exact MultiLimbOddCompare.scanIndex_ofNat_succ (current + i - 1) (by omega)
  rw [multiplySubtractUAddress, hadd, hpred]
  change (MultiLimbOddCompare.elementPtr u (UInt256.ofNat (current + i - 1))).toNat = _
  rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit u (current + i - 1) (by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ current + i)] using hfit)]
  omega

/-- Under the allocated-array geometry, every multiply-subtract read and write stays inside the
existing active memory. Consequently the generated active-word counter and byte-array size remain
constant while the loop index advances without wrap. -/
theorem multiplySubtractIterate_preserves_geometry
    (v u qHat : UInt256) (current start count memSize : Nat)
    (aw : UInt256) (state : MultiplySubtractState)
    (hcurrent : 0 < current)
    (hrange : start + count ≤ 32)
    (hwindowRange : current + start + count ≤ 66)
    (hsumWord : current + start + count < UInt256.size)
    (hvFit : v.toNat + 32 * (start + count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + start + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (start + count + 1) ≤ memSize)
    (huMem : u.toNat + 32 * (current + start + count) ≤ memSize)
    (hvActive : v.toNat + 32 * (start + count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + start + count) ≤ 32 * aw.toNat)
    (hindex : state.index = UInt256.ofNat start)
    (hactive : state.activeWords = aw)
    (hsize : state.memory.size = memSize) :
    let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count state
    final.index = UInt256.ofNat (start + count) ∧
      final.activeWords = aw ∧ final.memory.size = memSize := by
  induction count generalizing start state with
  | zero => simpa [multiplySubtractIterate] using And.intro hindex (And.intro hactive hsize)
  | succ count ih =>
      have hstartLt : start < 32 := by omega
      have hsumStart : current + start < UInt256.size := by omega
      have hvAddress := multiplySubtractVAddress_ofNat_toNat v start (by omega) (by omega)
      have huAddress := multiplySubtractUAddress_ofNat_toNat u current start hcurrent
        hsumStart (by omega) (by omega)
      have hvAccess :
          (multiplySubtractVAddress v (UInt256.ofNat start)).toNat + 32 ≤
            32 * aw.toNat := by rw [hvAddress]; omega
      have huAccess :
          (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
        rw [huAddress]
        omega
      have hvAw : multiplySubtractAw1 aw v (UInt256.ofNat start) = aw := by
        exact MultiLimbOddCompare.afterHeader_eq_of_access aw
          (multiplySubtractVAddress v (UInt256.ofNat start)) hvAccess
      have huAw :
          MultiLimbDivisionTrace.readWords1 aw
            (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)) = aw := by
        exact MultiLimbOddCompare.afterHeader_eq_of_access aw
          (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) huAccess
      have hwrite :
          (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ state.memory.size := by
        rw [huAddress, hsize]
        omega
      let next := multiplySubtractAdvance v u (UInt256.ofNat current) qHat state
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next]
        rw [multiplySubtractAdvance_index, hindex]
        apply u256_inj
        rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : start < UInt256.size),
          show (⟨1⟩ : UInt256).toNat = 1 by decide,
          UInt256.toNat_ofNat_of_lt (by omega : start + 1 < UInt256.size),
          Nat.mod_eq_of_lt (by omega : start + 1 < UInt256.size)]
      have hnextActive : next.activeWords = aw := by
        dsimp only [next]
        simp only [multiplySubtractAdvance, multiplySubtractStep,
          multiplySubtractAw2, hactive, hindex, hvAw, huAw]
      have hnextSize : next.memory.size = memSize := by
        dsimp only [next]
        simp only [multiplySubtractAdvance, multiplySubtractStep, hactive, hindex]
        apply (toByteArray_write32_size_of_le state.memory _
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat state.memory.size state.memory.size rfl (by omega)
          (max_eq_left hwrite)).trans
        exact hsize
      have hrest := ih (start := start + 1) (state := next)
        (hrange := by omega) (hwindowRange := by omega) (hsumWord := by omega)
        (hvFit := by omega) (huFit := by omega) (hvMem := by omega) (huMem := by omega)
        (hvActive := by omega) (huActive := by omega) hnextIndex hnextActive hnextSize
      simpa only [multiplySubtractIterate, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hrest

@[simp] theorem multiplySubtractIterate_advance
    (v u current qHat : UInt256) (count : Nat) (state : MultiplySubtractState) :
    multiplySubtractIterate v u current qHat count
        (multiplySubtractAdvance v u current qHat state) =
      multiplySubtractIterate v u current qHat (count + 1) state := by
  rfl

/-- Any number of concrete multiply-subtract writes preserves a padded word above every
destination. -/
theorem multiplySubtractIterate_read_above
    (v u current qHat : UInt256) (count : Nat) (state : MultiplySubtractState)
    (read : Nat)
    (hwrites : ∀ j, j < count ->
      let step := multiplySubtractIterate v u current qHat j state
      (multiplySubtractUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
        (multiplySubtractUAddress u current step.index).toNat + 32 ≤ read) :
    (multiplySubtractIterate v u current qHat count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplySubtractAdvance v u current qHat state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count ->
          let step := multiplySubtractIterate v u current qHat j next
          (multiplySubtractUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
            (multiplySubtractUAddress u current step.index).toNat + 32 ≤ read := by
        intro j hj
        have heq : multiplySubtractIterate v u current qHat j next =
            multiplySubtractIterate v u current qHat (j + 1) state := by
          simpa only [next] using multiplySubtractIterate_advance v u current qHat j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      rw [multiplySubtractIterate, hrest]
      exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
        hfirst.1 hfirst.2

/-- Any number of concrete multiply-subtract writes also preserves a padded word below every
destination. -/
theorem multiplySubtractIterate_read_below
    (v u current qHat : UInt256) (count : Nat) (state : MultiplySubtractState)
    (read : Nat)
    (hwrites : ∀ j, j < count ->
      let step := multiplySubtractIterate v u current qHat j state
      (multiplySubtractUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
        read + 32 ≤ (multiplySubtractUAddress u current step.index).toNat) :
    (multiplySubtractIterate v u current qHat count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := multiplySubtractAdvance v u current qHat state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count ->
          let step := multiplySubtractIterate v u current qHat j next
          (multiplySubtractUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
            read + 32 ≤ (multiplySubtractUAddress u current step.index).toNat := by
        intro j hj
        have heq : multiplySubtractIterate v u current qHat j next =
            multiplySubtractIterate v u current qHat (j + 1) state := by
          simpa only [next] using multiplySubtractIterate_advance v u current qHat j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstInBounds :
          (multiplySubtractUAddress u current state.index).toNat + 32 ≤ state.memory.size := by
        simpa only [multiplySubtractIterate] using hfirst.1
      rw [multiplySubtractIterate, hrest]
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirst.2

/-- An in-bounds concrete word write preserves a generated guarded load at a wholly higher
address. -/
theorem readWord_wordWrite_below
    (mem : ByteArray) (aw ptr : UInt256) (word : UInt256) (dest : Nat)
    (hwrite : dest + 32 ≤ mem.size)
    (hbelow : dest + 32 ≤ ptr.toNat) :
    MultiLimbDivisionTrace.readWord (word.toByteArray.write 0 mem dest 32) aw ptr =
      MultiLimbDivisionTrace.readWord mem aw ptr := by
  have hsize : (word.toByteArray.write 0 mem dest 32).size = mem.size := by
    exact toByteArray_write32_size_of_le mem word dest mem.size mem.size rfl (by omega)
      (max_eq_left hwrite)
  unfold MultiLimbDivisionTrace.readWord
  rw [hsize]
  by_cases hguard : ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩
  · simp only [hguard, if_true]
  · simp only [hguard, if_false]
    rw [write32_read_above_padded word.toByteArray mem dest ptr.toNat
      (by rw [toByteArray_size]) hwrite hbelow]

/-- An in-bounds concrete word write also preserves a generated guarded load wholly below it. -/
theorem readWord_wordWrite_above
    (mem : ByteArray) (aw ptr : UInt256) (word : UInt256) (dest : Nat)
    (hwrite : dest + 32 ≤ mem.size)
    (habove : ptr.toNat + 32 ≤ dest) :
    MultiLimbDivisionTrace.readWord (word.toByteArray.write 0 mem dest 32) aw ptr =
      MultiLimbDivisionTrace.readWord mem aw ptr := by
  have hsize : (word.toByteArray.write 0 mem dest 32).size = mem.size := by
    exact toByteArray_write32_size_of_le mem word dest mem.size mem.size rfl (by omega)
      (max_eq_left hwrite)
  unfold MultiLimbDivisionTrace.readWord
  rw [hsize]
  by_cases hguard : ptr.toNat ≥ mem.size ∨ ptr ≥ aw * ⟨32⟩
  · simp only [hguard, if_true]
  · simp only [hguard, if_false]
    rw [write32_read_below word.toByteArray mem dest ptr.toNat
      (by rw [toByteArray_size]) (by omega) habove]

/-- A guarded load returns a word just written at the same in-bounds, active address. -/
theorem readWord_wordWrite_self
    (mem : ByteArray) (aw ptr word : UInt256) (dest : Nat)
    (hptr : ptr.toNat = dest)
    (hwrite : dest + 32 ≤ mem.size)
    (hactive : dest + 32 ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    MultiLimbDivisionTrace.readWord (word.toByteArray.write 0 mem dest 32) aw ptr = word := by
  have hsize : (word.toByteArray.write 0 mem dest 32).size = mem.size :=
    toByteArray_write32_size_of_le mem word dest mem.size mem.size rfl (by omega)
      (max_eq_left hwrite)
  have hawMul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
      umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
  have hnotActive : ¬ ptr ≥ aw * ⟨32⟩ := by
    intro hge
    have hgeNat : (aw * ⟨32⟩).toNat ≤ ptr.toNat := hge
    rw [hawMul, hptr] at hgeNat
    omega
  unfold MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by rw [hsize, hptr]; omega, hnotActive⟩)]
  rw [hptr, toByteArray_write32_read_back mem word dest (by omega),
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- Guarded loads agree when memory size and the selected padded word agree. -/
theorem readWord_eq_of_size_read_eq
    (left right : ByteArray) (aw ptr : UInt256)
    (hsize : left.size = right.size)
    (hread : left.readWithPadding ptr.toNat 32 = right.readWithPadding ptr.toNat 32) :
    MultiLimbDivisionTrace.readWord left aw ptr =
      MultiLimbDivisionTrace.readWord right aw ptr := by
  unfold MultiLimbDivisionTrace.readWord
  rw [hsize, hread]

/-- Divisor words actually loaded by successive multiply-subtract iterations. -/
def multiplySubtractVDigits (v u current qHat : UInt256) :
    Nat -> MultiplySubtractState -> List UInt256
  | 0, _ => []
  | count + 1, state =>
      multiplySubtractVi state.memory state.activeWords v state.index ::
        multiplySubtractVDigits v u current qHat count
          (multiplySubtractAdvance v u current qHat state)

/-- Dividend-window words actually loaded before their in-place replacement. -/
def multiplySubtractUDigits (v u current qHat : UInt256) :
    Nat -> MultiplySubtractState -> List UInt256
  | 0, _ => []
  | count + 1, state =>
      multiplySubtractUVal state.memory state.activeWords v state.index u current ::
        multiplySubtractUDigits v u current qHat count
          (multiplySubtractAdvance v u current qHat state)

/-- Consecutive divisor loads in the same low-to-high order as the loop. -/
def divisorReadSlice (mem : ByteArray) (aw v : UInt256) : Nat -> Nat -> List UInt256
  | _, 0 => []
  | start, count + 1 =>
      multiplySubtractVi mem aw v (UInt256.ofNat start) ::
        divisorReadSlice mem aw v (start + 1) count

/-- Consecutive current-window loads in the same low-to-high order as the loop. -/
def windowReadSlice (mem : ByteArray) (aw u : UInt256) (current : Nat) :
    Nat -> Nat -> List UInt256
  | _, 0 => []
  | start, count + 1 =>
      MultiLimbDivisionTrace.readWord mem aw
          (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) ::
        windowReadSlice mem aw u current (start + 1) count

/-- A write above every address in a current-window slice preserves the whole slice. -/
theorem windowReadSlice_wordWrite_above
    (mem : ByteArray) (aw u word : UInt256) (current start count dest : Nat)
    (hwrite : dest + 32 ≤ mem.size)
    (habove : ∀ i, start ≤ i -> i < start + count ->
      (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)).toNat + 32 ≤
        dest) :
    windowReadSlice (word.toByteArray.write 0 mem dest 32) aw u current start count =
      windowReadSlice mem aw u current start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [windowReadSlice]
      rw [readWord_wordWrite_above mem aw
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start))
        word dest hwrite (habove start (by omega) (by omega))]
      rw [ih (start := start + 1) (by
        intro i hiLo hiHi
        exact habove i (by omega) (by omega))]

/-- A write below every address in a current-window slice preserves the whole slice. -/
theorem windowReadSlice_wordWrite_below
    (mem : ByteArray) (aw u word : UInt256) (current start count dest : Nat)
    (hwrite : dest + 32 ≤ mem.size)
    (hbelow : ∀ i, start ≤ i -> i < start + count ->
      dest + 32 ≤
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)).toNat) :
    windowReadSlice (word.toByteArray.write 0 mem dest 32) aw u current start count =
      windowReadSlice mem aw u current start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [windowReadSlice]
      rw [readWord_wordWrite_below mem aw
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start))
        word dest hwrite (hbelow start (by omega) (by omega))]
      rw [ih (start := start + 1) (by
        intro i hiLo hiHi
        exact hbelow i (by omega) (by omega))]

/-- If the current state's remaining loads still agree with a fixed pre-digit memory, one
concrete write preserves that agreement for the tail. Induction therefore identifies all
observed loop operands with consecutive pre-digit slices. -/
theorem multiplySubtractObservedInputs_eq_slices
    (base : ByteArray) (v u qHat : UInt256) (current start count memSize : Nat)
    (aw : UInt256) (state : MultiplySubtractState)
    (hcurrent : 0 < current)
    (hrange : start + count ≤ 32)
    (hwindowRange : current + start + count ≤ 66)
    (hsumWord : current + start + count < UInt256.size)
    (hvFit : v.toNat + 32 * (start + count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + start + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (start + count + 1) ≤ memSize)
    (huMem : u.toNat + 32 * (current + start + count) ≤ memSize)
    (hvActive : v.toNat + 32 * (start + count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + start + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + start + count) ≤ v.toNat)
    (hindex : state.index = UInt256.ofNat start)
    (hactive : state.activeWords = aw)
    (hsize : state.memory.size = memSize)
    (hvReads : ∀ i, start ≤ i -> i < start + count ->
      multiplySubtractVi state.memory state.activeWords v (UInt256.ofNat i) =
        multiplySubtractVi base aw v (UInt256.ofNat i))
    (huReads : ∀ i, start ≤ i -> i < start + count ->
      multiplySubtractUVal state.memory state.activeWords v (UInt256.ofNat i) u
          (UInt256.ofNat current) =
        MultiLimbDivisionTrace.readWord base aw
          (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i))) :
    multiplySubtractVDigits v u (UInt256.ofNat current) qHat count state =
        divisorReadSlice base aw v start count ∧
      multiplySubtractUDigits v u (UInt256.ofNat current) qHat count state =
        windowReadSlice base aw u current start count := by
  induction count generalizing start state with
  | zero => simp [multiplySubtractVDigits, multiplySubtractUDigits,
      divisorReadSlice, windowReadSlice]
  | succ count ih =>
      have hsumStart : current + start < UInt256.size := by omega
      have hvAddress := multiplySubtractVAddress_ofNat_toNat v start (by omega) (by omega)
      have huAddress := multiplySubtractUAddress_ofNat_toNat u current start hcurrent
        hsumStart (by omega) (by omega)
      have hvAccess :
          (multiplySubtractVAddress v (UInt256.ofNat start)).toNat + 32 ≤
            32 * aw.toNat := by rw [hvAddress]; omega
      have huAccess :
          (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
        rw [huAddress]
        omega
      have hvAw : multiplySubtractAw1 aw v (UInt256.ofNat start) = aw :=
        MultiLimbOddCompare.afterHeader_eq_of_access aw
          (multiplySubtractVAddress v (UInt256.ofNat start)) hvAccess
      have hwrite :
          (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ state.memory.size := by
        rw [huAddress, hsize]
        omega
      let next := multiplySubtractAdvance v u (UInt256.ofNat current) qHat state
      have hstep := multiplySubtractIterate_preserves_geometry v u qHat current start 1
        memSize aw state hcurrent (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hindex hactive hsize
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        simpa only [next, multiplySubtractIterate] using hstep.1
      have hnextActive : next.activeWords = aw := by
        simpa only [next, multiplySubtractIterate] using hstep.2.1
      have hnextSize : next.memory.size = memSize := by
        simpa only [next, multiplySubtractIterate] using hstep.2.2
      have hnextVReads : ∀ i, start + 1 ≤ i -> i < start + 1 + count ->
          multiplySubtractVi next.memory next.activeWords v (UInt256.ofNat i) =
            multiplySubtractVi base aw v (UInt256.ofNat i) := by
        intro i hiLo hiHi
        have hiWord : current + i < UInt256.size := by omega
        have hvI := multiplySubtractVAddress_ofNat_toNat v i (by omega) (by omega)
        have hbelow :
            (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)).toNat + 32 ≤
              (multiplySubtractVAddress v (UInt256.ofNat i)).toNat := by
          rw [huAddress, hvI]
          omega
        let written := evmSubBorrow
          (multiplySubtractUVal state.memory state.activeWords v state.index u
            (UInt256.ofNat current))
          (qHat * multiplySubtractVi state.memory state.activeWords v state.index + state.carry)
          state.borrow
        have hframe := readWord_wordWrite_below state.memory aw
          (multiplySubtractVAddress v (UInt256.ofNat i)) written.1
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat hwrite hbelow
        calc
          multiplySubtractVi next.memory next.activeWords v (UInt256.ofNat i) =
              MultiLimbDivisionTrace.readWord next.memory aw
                (multiplySubtractVAddress v (UInt256.ofNat i)) := by
            simp [multiplySubtractVi, hnextActive]
          _ = MultiLimbDivisionTrace.readWord state.memory aw
                (multiplySubtractVAddress v (UInt256.ofNat i)) := by
            simpa only [next, multiplySubtractAdvance, multiplySubtractStep, written,
              hactive, hindex] using hframe
          _ = multiplySubtractVi state.memory state.activeWords v (UInt256.ofNat i) := by
            simp [multiplySubtractVi, hactive]
          _ = multiplySubtractVi base aw v (UInt256.ofNat i) :=
            hvReads i (by omega) (by omega)
      have hnextUReads : ∀ i, start + 1 ≤ i -> i < start + 1 + count ->
          multiplySubtractUVal next.memory next.activeWords v (UInt256.ofNat i) u
              (UInt256.ofNat current) =
            MultiLimbDivisionTrace.readWord base aw
              (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)) := by
        intro i hiLo hiHi
        have hiWord : current + i < UInt256.size := by omega
        have huI := multiplySubtractUAddress_ofNat_toNat u current i hcurrent hiWord
          (by omega) (by omega)
        have hvI := multiplySubtractVAddress_ofNat_toNat v i (by omega) (by omega)
        have hvIAccess :
            (multiplySubtractVAddress v (UInt256.ofNat i)).toNat + 32 ≤
              32 * aw.toNat := by rw [hvI]; omega
        have hvIAw : multiplySubtractAw1 aw v (UInt256.ofNat i) = aw :=
          MultiLimbOddCompare.afterHeader_eq_of_access aw
            (multiplySubtractVAddress v (UInt256.ofNat i)) hvIAccess
        have hbelow :
            (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)).toNat + 32 ≤
              (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat i)).toNat := by
          rw [huAddress, huI]
          omega
        let written := evmSubBorrow
          (multiplySubtractUVal state.memory state.activeWords v state.index u
            (UInt256.ofNat current))
          (qHat * multiplySubtractVi state.memory state.activeWords v state.index + state.carry)
          state.borrow
        have hframe := readWord_wordWrite_below state.memory aw
          (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat i)) written.1
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat hwrite hbelow
        calc
          multiplySubtractUVal next.memory next.activeWords v (UInt256.ofNat i) u
              (UInt256.ofNat current) =
              MultiLimbDivisionTrace.readWord next.memory aw
                (multiplySubtractUAddress u (UInt256.ofNat current)
                  (UInt256.ofNat i)) := by
            unfold multiplySubtractUVal
            rw [hnextActive, hvIAw]
          _ = MultiLimbDivisionTrace.readWord state.memory aw
                (multiplySubtractUAddress u (UInt256.ofNat current)
                  (UInt256.ofNat i)) := by
            simpa only [next, multiplySubtractAdvance, multiplySubtractStep, written,
              hactive, hindex] using hframe
          _ = multiplySubtractUVal state.memory state.activeWords v (UInt256.ofNat i) u
                (UInt256.ofNat current) := by
            unfold multiplySubtractUVal
            rw [hactive, hvIAw]
          _ = MultiLimbDivisionTrace.readWord base aw
                (multiplySubtractUAddress u (UInt256.ofNat current)
                  (UInt256.ofNat i)) := huReads i (by omega) (by omega)
      have hrest := ih (start := start + 1) (state := next)
        (hrange := by omega) (hwindowRange := by omega) (hsumWord := by omega)
        (hvFit := by omega) (huFit := by omega) (hvMem := by omega) (huMem := by omega)
        (hvActive := by omega) (huActive := by omega) (huBelowV := by omega)
        hnextIndex hnextActive hnextSize hnextVReads hnextUReads
      constructor
      · simp only [multiplySubtractVDigits, divisorReadSlice, hindex]
        rw [hvReads start (by omega) (by omega), hrest.1]
      · simp only [multiplySubtractUDigits, windowReadSlice, hindex]
        rw [huReads start (by omega) (by omega), hrest.2]

/-- Specialization of the evolving-memory slice induction to the actual zero-index loop entry. -/
theorem multiplyInitialObservedInputs_eq_slices
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat) :
    multiplySubtractVDigits v u (UInt256.ofNat current) qHat count
        (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw) =
          divisorReadSlice mem aw v 0 count ∧
      multiplySubtractUDigits v u (UInt256.ofNat current) qHat count
        (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw) =
          windowReadSlice mem aw u current 0 count := by
  apply multiplySubtractObservedInputs_eq_slices mem v u qHat current 0 count mem.size aw
    (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw) hcurrent
    (by simpa using hrange) (by simpa using hwindowRange) (by simpa using hsumWord)
    (by simpa using hvFit) (by simpa using huFit) (by simpa using hvMem)
    (by simpa using huMem) (by simpa using hvActive) (by simpa using huActive)
    (by simpa using huBelowV)
  · rfl
  · rfl
  · rfl
  · intro i hiLo hiHi
    rfl
  · intro i hiLo hiHi
    have hvI := multiplySubtractVAddress_ofNat_toNat v i (by omega) (by omega)
    have hvIAccess :
        (multiplySubtractVAddress v (UInt256.ofNat i)).toNat + 32 ≤
          32 * aw.toNat := by rw [hvI]; omega
    have hvIAw : multiplySubtractAw1 aw v (UInt256.ofNat i) = aw :=
      MultiLimbOddCompare.afterHeader_eq_of_access aw
        (multiplySubtractVAddress v (UInt256.ofNat i)) hvIAccess
    simp [MultiLimbSchoolbookDigitFunction.multiplyInitial, multiplySubtractUVal, hvIAw]

/-- Low result words produced by successive concrete multiply-subtract iterations. -/
def multiplySubtractResultDigits (v u current qHat : UInt256) :
    Nat -> MultiplySubtractState -> List UInt256
  | 0, _ => []
  | count + 1, state =>
      let subtraction := evmSubBorrow
        (multiplySubtractUVal state.memory state.activeWords v state.index u current)
        (qHat * multiplySubtractVi state.memory state.activeWords v state.index + state.carry)
        state.borrow
      subtraction.1 :: multiplySubtractResultDigits v u current qHat count
        (multiplySubtractAdvance v u current qHat state)

/-- Every produced multiply-subtract word occupies its expected position in the final evolving
memory. Later iterations write strictly higher words and therefore preserve each earlier result. -/
theorem multiplySubtractResultDigits_eq_finalSlice
    (v u qHat : UInt256) (current start count memSize : Nat)
    (aw : UInt256) (state : MultiplySubtractState)
    (hcurrent : 0 < current)
    (hrange : start + count ≤ 32)
    (hwindowRange : current + start + count ≤ 66)
    (hsumWord : current + start + count < UInt256.size)
    (hvFit : v.toNat + 32 * (start + count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + start + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (start + count + 1) ≤ memSize)
    (huMem : u.toNat + 32 * (current + start + count) ≤ memSize)
    (hvActive : v.toNat + 32 * (start + count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + start + count) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hindex : state.index = UInt256.ofNat start)
    (hactive : state.activeWords = aw)
    (hsize : state.memory.size = memSize) :
    let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count state
    multiplySubtractResultDigits v u (UInt256.ofNat current) qHat count state =
      windowReadSlice final.memory aw u current start count := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih =>
      have hsumStart : current + start < UInt256.size := by omega
      have hvAddress := multiplySubtractVAddress_ofNat_toNat v start (by omega) (by omega)
      have huAddress := multiplySubtractUAddress_ofNat_toNat u current start hcurrent
        hsumStart (by omega) (by omega)
      have hwrite :
          (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ state.memory.size := by
        rw [huAddress, hsize]
        omega
      let written := evmSubBorrow
        (multiplySubtractUVal state.memory state.activeWords v state.index u
          (UInt256.ofNat current))
        (qHat * multiplySubtractVi state.memory state.activeWords v state.index + state.carry)
        state.borrow
      let next := multiplySubtractAdvance v u (UInt256.ofNat current) qHat state
      have hstep := multiplySubtractIterate_preserves_geometry v u qHat current start 1
        memSize aw state hcurrent (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hindex hactive hsize
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        simpa only [next, multiplySubtractIterate] using hstep.1
      have hnextActive : next.activeWords = aw := by
        simpa only [next, multiplySubtractIterate] using hstep.2.1
      have hnextSize : next.memory.size = memSize := by
        simpa only [next, multiplySubtractIterate] using hstep.2.2
      have hrest := ih (start := start + 1) (state := next)
        (hrange := by omega) (hwindowRange := by omega) (hsumWord := by omega)
        (hvFit := by omega) (huFit := by omega) (hvMem := by omega) (huMem := by omega)
        (hvActive := by omega) (huActive := by omega) hnextIndex hnextActive hnextSize
      let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count next
      have hfinalGeometry := multiplySubtractIterate_preserves_geometry v u qHat current
        (start + 1) count memSize aw next hcurrent (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hnextIndex hnextActive hnextSize
      have htailRead : final.memory.readWithPadding
            (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat 32 =
          next.memory.readWithPadding
            (multiplySubtractUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat 32 := by
        apply multiplySubtractIterate_read_below v u (UInt256.ofNat current) qHat count next
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat
        intro j hj
        let step := multiplySubtractIterate v u (UInt256.ofNat current) qHat j next
        have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current
          (start + 1) j memSize aw next hcurrent (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          hnextIndex hnextActive hnextSize
        have hstepIndex : step.index = UInt256.ofNat (start + 1 + j) := by
          simpa only [step] using hgeometry.1
        have hstepSize : step.memory.size = memSize := by
          simpa only [step] using hgeometry.2.2
        have huJ := multiplySubtractUAddress_ofNat_toNat u current (start + 1 + j)
          hcurrent (by omega) (by omega) (by omega)
        constructor
        · rw [hstepIndex, huJ, hstepSize]
          omega
        · rw [hstepIndex, huJ, huAddress]
          omega
      have hreadFrame :
          MultiLimbDivisionTrace.readWord final.memory aw
              (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)) =
            MultiLimbDivisionTrace.readWord next.memory aw
              (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)) := by
        apply readWord_eq_of_size_read_eq
        · rw [hfinalGeometry.2.2, hnextSize]
        · exact htailRead
      have hself :
          MultiLimbDivisionTrace.readWord next.memory aw
              (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)) = written.1 := by
        have hactiveAddress :
            (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
          rw [huAddress]
          omega
        have hreadBack := readWord_wordWrite_self state.memory aw
          (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start))
          written.1
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat rfl hwrite hactiveAddress hawFit
        simpa only [next, multiplySubtractAdvance, multiplySubtractStep, written,
          hactive, hindex] using hreadBack
      simp only [multiplySubtractResultDigits, windowReadSlice]
      change written.1 :: multiplySubtractResultDigits v u (UInt256.ofNat current) qHat
          count next = _
      rw [hrest]
      change written.1 :: windowReadSlice final.memory aw u current (start + 1) count = _
      have hfinalEq :
          multiplySubtractIterate v u (UInt256.ofNat current) qHat (count + 1) state =
            final := by rfl
      rw [hfinalEq]
      rw [hreadFrame, hself]

@[simp] theorem multiplySubtractVDigits_length
    (v u current qHat : UInt256) (count : Nat) (state : MultiplySubtractState) :
    (multiplySubtractVDigits v u current qHat count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      simp only [multiplySubtractVDigits, List.length_cons, ih]

@[simp] theorem multiplySubtractUDigits_length
    (v u current qHat : UInt256) (count : Nat) (state : MultiplySubtractState) :
    (multiplySubtractUDigits v u current qHat count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      simp only [multiplySubtractUDigits, List.length_cons, ih]

/-- The concrete multiply-subtract state machine is the pure Algorithm D digit recurrence over
the exact words it reads. -/
theorem multiplySubtractIterate_eq_knuthSubtractDigits
    (v u current qHat : UInt256) (count : Nat) (state : MultiplySubtractState) :
    let pure := knuthSubtractDigits qHat
      (multiplySubtractUDigits v u current qHat count state)
      (multiplySubtractVDigits v u current qHat count state)
      state.carry state.borrow
    let final := multiplySubtractIterate v u current qHat count state
    pure.digits = multiplySubtractResultDigits v u current qHat count state /\
      pure.carry = final.carry /\ pure.borrow = final.borrow := by
  induction count generalizing state with
  | zero => simp [knuthSubtractDigits, multiplySubtractUDigits,
      multiplySubtractVDigits, multiplySubtractResultDigits, multiplySubtractIterate]
  | succ count ih =>
      let vi := multiplySubtractVi state.memory state.activeWords v state.index
      let uVal := multiplySubtractUVal state.memory state.activeWords v state.index u current
      let next := multiplySubtractAdvance v u current qHat state
      have hcarry := multiplySubtractCarry_eq_schoolbook qHat vi state.carry
      have hlow := multiplySubtractLow_eq_schoolbook qHat vi state.carry
      have hrest := ih next
      have hcarry' := hcarry
      dsimp only at hcarry'
      rw [hlow] at hcarry'
      have hcombined := And.intro
        (congrArg (fun tail => (evmSubBorrow uVal
          (evmSchoolbookStep qHat vi ⟨0⟩ state.carry).1 state.borrow).1 :: tail) hrest.1)
        (And.intro hrest.2.1 hrest.2.2)
      simp only [multiplySubtractUDigits, multiplySubtractVDigits, knuthSubtractDigits,
        multiplySubtractResultDigits, multiplySubtractIterate]
      dsimp only [vi, uVal] at hcarry hcarry' hlow ⊢
      rw [hlow]
      simpa only [next, multiplySubtractAdvance, multiplySubtractStep, hcarry', hlow] using
        hcombined

/-- The complete concrete multiply-subtract loop computes the pure Algorithm D recurrence over
the pre-digit memory slices. -/
theorem multiplyFinal_eq_knuthSubtractDigits_slices
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat) :
    let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
    let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
    let pure := knuthSubtractDigits qHat
      (windowReadSlice mem aw u current 0 count)
      (divisorReadSlice mem aw v 0 count) ⟨0⟩ ⟨0⟩
    pure.digits = multiplySubtractResultDigits v u (UInt256.ofNat current) qHat count initial ∧
      pure.carry = final.carry ∧ pure.borrow = final.borrow := by
  have hinputs := multiplyInitialObservedInputs_eq_slices mem aw v u qHat current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive huBelowV
  have harithmetic := multiplySubtractIterate_eq_knuthSubtractDigits v u
    (UInt256.ofNat current) qHat count
    (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw)
  rw [hinputs.1, hinputs.2] at harithmetic
  simpa only [MultiLimbSchoolbookDigitFunction.multiplyInitial] using harithmetic

/-- Collector-free form: the pure result digits are the words present in final concrete memory. -/
theorem multiplyFinalMemory_eq_knuthSubtractDigits_slices
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
    let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
    let pure := knuthSubtractDigits qHat
      (windowReadSlice mem aw u current 0 count)
      (divisorReadSlice mem aw v 0 count) ⟨0⟩ ⟨0⟩
    pure.digits = windowReadSlice final.memory aw u current 0 count ∧
      pure.carry = final.carry ∧ pure.borrow = final.borrow := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  have harithmetic := multiplyFinal_eq_knuthSubtractDigits_slices mem aw v u qHat current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive huBelowV
  have hmemory := multiplySubtractResultDigits_eq_finalSlice v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) hawFit rfl rfl rfl
  dsimp only [initial, final] at harithmetic hmemory ⊢
  exact ⟨harithmetic.1.trans hmemory, harithmetic.2.1, harithmetic.2.2⟩

/-- All lower multiply-subtract writes are below the saved top limb, so the post-loop top load is
the same word present in pre-digit memory. -/
theorem multiplyFinal_topRead_eq
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat) :
    let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
    let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
    MultiLimbDivisionTrace.readWord final.memory final.activeWords
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)) =
      MultiLimbDivisionTrace.readWord mem aw
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)) := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  have huTop := multiplySubtractUAddress_ofNat_toNat u current count hcurrent hsumWord
    (by omega) huFit
  have hread : final.memory.readWithPadding
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat count)).toNat 32 =
        mem.readWithPadding
          (multiplySubtractUAddress u (UInt256.ofNat current)
            (UInt256.ofNat count)).toNat 32 := by
    apply multiplySubtractIterate_read_above v u (UInt256.ofNat current) qHat count initial
      (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)).toNat
    intro j hj
    let step := multiplySubtractIterate v u (UInt256.ofNat current) qHat j initial
    have hstepGeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 j
      mem.size aw initial hcurrent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
    have hstepIndex : step.index = UInt256.ofNat j := by
      simpa only [step, Nat.zero_add] using hstepGeometry.1
    have hstepSize : step.memory.size = mem.size := by
      simpa only [step] using hstepGeometry.2.2
    have huJ := multiplySubtractUAddress_ofNat_toNat u current j hcurrent (by omega)
      (by omega) (by omega)
    constructor
    · rw [hstepIndex, huJ, hstepSize]
      omega
    · rw [hstepIndex, huJ, huTop]
      omega
  have hguarded := readWord_eq_of_size_read_eq final.memory mem aw
    (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count))
    (by simpa only [final] using hgeometry.2.2) hread
  dsimp only at hgeometry ⊢
  rw [hgeometry.2.1]
  exact hguarded

/-- The concrete top-subtraction flag is exactly the pure Algorithm D window-underflow flag. -/
theorem topResult_negative_eq_knuthSubtractWindow
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let pure := knuthSubtractWindow qHat
      (windowReadSlice mem aw u current 0 count)
      (divisorReadSlice mem aw v 0 count)
      (MultiLimbDivisionTrace.readWord mem aw
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)))
    pure.negative =
      (MultiLimbSchoolbookDigitFunction.topResult mem aw v u (UInt256.ofNat current)
        qHat count).negative := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  have hsemantic := multiplyFinalMemory_eq_knuthSubtractDigits_slices mem aw v u qHat
    current count hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive
    huActive huBelowV hawFit
  have htopRead := multiplyFinal_topRead_eq mem aw v u qHat current count hcurrent hrange
    hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
  dsimp only [initial, final] at hsemantic htopRead
  have hsemantic' := hsemantic
  simp only [MultiLimbSchoolbookDigitFunction.multiplyInitial] at hsemantic'
  have htopRead' := htopRead
  simp only [MultiLimbSchoolbookDigitFunction.multiplyInitial] at htopRead'
  simp only [knuthSubtractWindow, MultiLimbSchoolbookDigitFunction.topResult,
    MultiLimbSchoolbookDigitFunction.multiplyFinal,
    MultiLimbSchoolbookDigitFunction.multiplyInitial, topSubtractStep]
  rw [hsemantic'.2.1, hsemantic'.2.2, htopRead']

/-- The complete concrete top subtraction stores the pure lower and top words and exposes the
same negative flag, while remaining inside the existing active memory. -/
theorem topResult_eq_knuthSubtractWindow
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let pure := knuthSubtractWindow qHat
      (windowReadSlice mem aw u current 0 count)
      (divisorReadSlice mem aw v 0 count)
      (MultiLimbDivisionTrace.readWord mem aw
        (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)))
    let concrete := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
      (UInt256.ofNat current) qHat count
    pure.lower = windowReadSlice concrete.memory aw u current 0 count ∧
      pure.top = MultiLimbDivisionTrace.readWord concrete.memory concrete.activeWords
        concrete.address ∧
      pure.negative = concrete.negative ∧ concrete.activeWords = aw := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let uTop := MultiLimbDivisionTrace.readWord mem aw topAddr
  let pure := knuthSubtractWindow qHat (windowReadSlice mem aw u current 0 count)
    (divisorReadSlice mem aw v 0 count) uTop
  let concrete := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  have hsemantic := multiplyFinalMemory_eq_knuthSubtractDigits_slices mem aw v u qHat
    current count hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive
    huActive (by omega) hawFit
  have hnegative := topResult_negative_eq_knuthSubtractWindow mem aw v u qHat current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
    (by omega) hawFit
  have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  have huTopAddress := multiplySubtractUAddress_ofNat_toNat u current count hcurrent
    hsumWord (by omega) (by omega)
  have htopAccess : topAddr.toNat + 32 ≤ 32 * aw.toNat := by
    dsimp only [topAddr]
    rw [huTopAddress]
    omega
  have htopAw : MultiLimbDivisionTrace.readWords1 aw topAddr = aw :=
    MultiLimbOddCompare.afterHeader_eq_of_access aw topAddr htopAccess
  have hfinalActive : final.activeWords = aw := by
    simpa only [final] using hgeometry.2.1
  have hfinalSize : final.memory.size = mem.size := by
    simpa only [final] using hgeometry.2.2
  have hconcreteActive : concrete.activeWords = aw := by
    dsimp only [concrete, MultiLimbSchoolbookDigitFunction.topResult,
      MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial]
    change topSubtractAw2
      (multiplySubtractIterate v u (UInt256.ofNat current) qHat count
        (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw)).activeWords
      u (UInt256.ofNat current) (UInt256.ofNat count) = aw
    rw [show (multiplySubtractIterate v u (UInt256.ofNat current) qHat count
        (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw)).activeWords = aw by
      simpa only [final, initial] using hfinalActive]
    unfold topSubtractAw2 topSubtractAw1
    change MultiLimbDivisionTrace.readWords1
      (MultiLimbDivisionTrace.readWords1 aw topAddr) topAddr = aw
    rw [htopAw, htopAw]
  let subtraction := evmSubBorrow
    (MultiLimbDivisionTrace.readWord final.memory final.activeWords topAddr)
    final.carry final.borrow
  have htopWrite : topAddr.toNat + 32 ≤ final.memory.size := by
    rw [huTopAddress, hfinalSize]
    omega
  have hlowerPreserved :
      windowReadSlice concrete.memory aw u current 0 count =
        windowReadSlice final.memory aw u current 0 count := by
    have hpreserve := windowReadSlice_wordWrite_above final.memory aw u subtraction.1
      current 0 count topAddr.toNat htopWrite (by
        intro i hiLo hiHi
        have huI := multiplySubtractUAddress_ofNat_toNat u current i hcurrent
          (by omega) (by omega) (by omega)
        rw [huI, huTopAddress]
        omega)
    simpa only [concrete, MultiLimbSchoolbookDigitFunction.topResult,
      MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial,
      topSubtractStep, topAddr, subtraction] using hpreserve
  have htopStored :
      MultiLimbDivisionTrace.readWord concrete.memory concrete.activeWords concrete.address =
        subtraction.1 := by
    have hreadBack := readWord_wordWrite_self final.memory aw topAddr subtraction.1
      topAddr.toNat rfl htopWrite htopAccess hawFit
    rw [hconcreteActive]
    simpa only [concrete, MultiLimbSchoolbookDigitFunction.topResult,
      MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial,
      topSubtractStep, topAddr, subtraction] using hreadBack
  have hpureLower : pure.lower = windowReadSlice final.memory aw u current 0 count := by
    dsimp only [pure, knuthSubtractWindow]
    simpa only [initial, final] using hsemantic.1
  have hpureTop : pure.top = subtraction.1 := by
    have htopRead := multiplyFinal_topRead_eq mem aw v u qHat current count hcurrent
      hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive
    have hsemantic' := hsemantic
    simp only [MultiLimbSchoolbookDigitFunction.multiplyInitial] at hsemantic'
    dsimp only [pure, knuthSubtractWindow, subtraction, uTop, topAddr, initial, final]
    rw [hsemantic'.2.1, hsemantic'.2.2]
    simpa only [MultiLimbSchoolbookDigitFunction.multiplyInitial] using congrArg
      (fun loaded => (evmSubBorrow loaded
        (multiplySubtractIterate v u (UInt256.ofNat current) qHat count
          (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw)).carry
        (multiplySubtractIterate v u (UInt256.ofNat current) qHat count
          (MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw)).borrow).1) htopRead.symm
  dsimp only
  exact ⟨hpureLower.trans hlowerPreserved.symm,
    hpureTop.trans htopStored.symm, hnegative, hconcreteActive⟩

/-- Divisor words actually loaded by successive add-back iterations. -/
def addBackVDigits (v u current : UInt256) : Nat -> AddBackState -> List UInt256
  | 0, _ => []
  | count + 1, state =>
      MultiLimbDivisionTrace.readWord state.memory state.activeWords
          (addBackVAddress v state.index) ::
        addBackVDigits v u current count (addBackAdvance v u current state)

/-- Subtracted window words actually loaded by successive add-back iterations. -/
def addBackUDigits (v u current : UInt256) : Nat -> AddBackState -> List UInt256
  | 0, _ => []
  | count + 1, state =>
      MultiLimbDivisionTrace.readWord state.memory (addBackAw1 state.activeWords v state.index)
          (addBackUAddress u current state.index) ::
        addBackUDigits v u current count (addBackAdvance v u current state)

/-- Low result words produced by successive concrete add-back iterations. -/
def addBackResultDigits (v u current : UInt256) : Nat -> AddBackState -> List UInt256
  | 0, _ => []
  | count + 1, state =>
      let vDigit := MultiLimbDivisionTrace.readWord state.memory state.activeWords
        (addBackVAddress v state.index)
      let uDigit := MultiLimbDivisionTrace.readWord state.memory
        (addBackAw1 state.activeWords v state.index) (addBackUAddress u current state.index)
      (evmAddCarryStep uDigit vDigit state.carry).1 ::
        addBackResultDigits v u current count (addBackAdvance v u current state)

@[simp] theorem addBackVDigits_length
    (v u current : UInt256) (count : Nat) (state : AddBackState) :
    (addBackVDigits v u current count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp only [addBackVDigits, List.length_cons, ih]

@[simp] theorem addBackUDigits_length
    (v u current : UInt256) (count : Nat) (state : AddBackState) :
    (addBackUDigits v u current count state).length = count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => simp only [addBackUDigits, List.length_cons, ih]

/-- The concrete add-back state machine is the pure multi-limb addition recurrence over the exact
words it reads. -/
theorem addBackIterate_eq_evmAddLimbs
    (v u current : UInt256) (count : Nat) (state : AddBackState) :
    let pure := evmAddLimbs
      (addBackUDigits v u current count state)
      (addBackVDigits v u current count state) state.carry
    let final := addBackIterate v u current count state
    pure.1 = addBackResultDigits v u current count state /\ pure.2 = final.carry := by
  induction count generalizing state with
  | zero => simp [evmAddLimbs, addBackUDigits, addBackVDigits,
      addBackResultDigits, addBackIterate]
  | succ count ih =>
      let vDigit := MultiLimbDivisionTrace.readWord state.memory state.activeWords
        (addBackVAddress v state.index)
      let uDigit := MultiLimbDivisionTrace.readWord state.memory
        (addBackAw1 state.activeWords v state.index) (addBackUAddress u current state.index)
      let next := addBackAdvance v u current state
      have hrest := ih next
      simp only [addBackUDigits, addBackVDigits, evmAddLimbs,
        addBackResultDigits, addBackIterate]
      dsimp only [vDigit, uDigit, next] at hrest ⊢
      simp only [addBackAdvance, addBackStep]
      exact ⟨congrArg (fun tail => (evmAddCarryStep uDigit vDigit state.carry).1 :: tail)
        hrest.1, hrest.2⟩

/-- Add-back uses the same divisor payload address as multiply-subtract. -/
theorem addBackVAddress_ofNat_toNat
    (v : UInt256) (i : Nat)
    (hi : i ≤ 32)
    (hfit : v.toNat + 32 * (i + 1) < UInt256.size) :
    (addBackVAddress v (UInt256.ofNat i)).toNat =
      v.toNat + 32 * (i + 1) := by
  simpa only [addBackVAddress] using multiplySubtractVAddress_ofNat_toNat v i hi hfit

/-- Add-back uses the same wrapped current-window address as multiply-subtract. -/
theorem addBackUAddress_ofNat_toNat
    (u : UInt256) (current i : Nat)
    (hcurrent : 0 < current)
    (hsumWord : current + i < UInt256.size)
    (hindex : current + i - 1 ≤ 65)
    (hfit : u.toNat + 32 * (current + i) < UInt256.size) :
    (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat i)).toNat =
      u.toNat + 32 * (current + i) := by
  simpa only [addBackUAddress] using
    multiplySubtractUAddress_ofNat_toNat u current i hcurrent hsumWord hindex hfit

/-- Every add-back read and write remains in the existing active memory, so only the index and
carry evolve. -/
theorem addBackIterate_preserves_geometry
    (v u : UInt256) (current start count memSize : Nat)
    (aw : UInt256) (state : AddBackState)
    (hcurrent : 0 < current)
    (hrange : start + count ≤ 32)
    (hwindowRange : current + start + count ≤ 66)
    (hsumWord : current + start + count < UInt256.size)
    (hvFit : v.toNat + 32 * (start + count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + start + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (start + count + 1) ≤ memSize)
    (huMem : u.toNat + 32 * (current + start + count) ≤ memSize)
    (hvActive : v.toNat + 32 * (start + count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + start + count) ≤ 32 * aw.toNat)
    (hindex : state.index = UInt256.ofNat start)
    (hactive : state.activeWords = aw)
    (hsize : state.memory.size = memSize) :
    let final := addBackIterate v u (UInt256.ofNat current) count state
    final.index = UInt256.ofNat (start + count) ∧
      final.activeWords = aw ∧ final.memory.size = memSize := by
  induction count generalizing start state with
  | zero => simpa [addBackIterate] using And.intro hindex (And.intro hactive hsize)
  | succ count ih =>
      have hvAddress := addBackVAddress_ofNat_toNat v start (by omega) (by omega)
      have huAddress := addBackUAddress_ofNat_toNat u current start hcurrent
        (by omega) (by omega) (by omega)
      have hvAccess :
          (addBackVAddress v (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
        rw [hvAddress]
        omega
      have huAccess :
          (addBackUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
        rw [huAddress]
        omega
      have hvAw : addBackAw1 aw v (UInt256.ofNat start) = aw :=
        MultiLimbOddCompare.afterHeader_eq_of_access aw
          (addBackVAddress v (UInt256.ofNat start)) hvAccess
      have huAw2 :
          addBackAw2 aw v (UInt256.ofNat start) u (UInt256.ofNat current) = aw := by
        simp only [addBackAw2, hvAw]
        exact MultiLimbOddCompare.afterHeader_eq_of_access aw
          (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) huAccess
      have huAw3 :
          addBackAw3 aw v (UInt256.ofNat start) u (UInt256.ofNat current) = aw := by
        simp only [addBackAw3, huAw2]
        exact MultiLimbOddCompare.afterHeader_eq_of_access aw
          (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) huAccess
      have hwrite :
          (addBackUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ state.memory.size := by
        rw [huAddress, hsize]
        omega
      let next := addBackAdvance v u (UInt256.ofNat current) state
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        dsimp only [next]
        rw [addBackAdvance]
        dsimp only
        rw [hindex]
        apply u256_inj
        rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : start < UInt256.size),
          show (⟨1⟩ : UInt256).toNat = 1 by decide,
          UInt256.toNat_ofNat_of_lt (by omega : start + 1 < UInt256.size),
          Nat.mod_eq_of_lt (by omega : start + 1 < UInt256.size)]
      have hnextActive : next.activeWords = aw := by
        dsimp only [next]
        simp only [addBackAdvance, addBackStep, hactive, hindex, huAw3]
      have hnextSize : next.memory.size = memSize := by
        dsimp only [next]
        simp only [addBackAdvance, addBackStep, hactive, hindex]
        apply (toByteArray_write32_size_of_le state.memory _
          (addBackUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat state.memory.size state.memory.size rfl (by omega)
          (max_eq_left hwrite)).trans
        exact hsize
      have hrest := ih (start := start + 1) (state := next)
        (hrange := by omega) (hwindowRange := by omega) (hsumWord := by omega)
        (hvFit := by omega) (huFit := by omega) (hvMem := by omega) (huMem := by omega)
        (hvActive := by omega) (huActive := by omega) hnextIndex hnextActive hnextSize
      simpa only [addBackIterate, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hrest

@[simp] theorem addBackIterate_advance
    (v u current : UInt256) (count : Nat) (state : AddBackState) :
    addBackIterate v u current count (addBackAdvance v u current state) =
      addBackIterate v u current (count + 1) state := by
  rfl

/-- Advancing after an iteration prefix is the same as extending that prefix by one step. -/
theorem addBackAdvance_iterate
    (v u current : UInt256) (count : Nat) (state : AddBackState) :
    addBackAdvance v u current (addBackIterate v u current count state) =
      addBackIterate v u current (count + 1) state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      simp only [addBackIterate]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (addBackAdvance v u current state)

/-- Add-back writes preserve every padded word above their destinations. -/
theorem addBackIterate_read_above
    (v u current : UInt256) (count : Nat) (state : AddBackState)
    (read : Nat)
    (hwrites : ∀ j, j < count ->
      let step := addBackIterate v u current j state
      (addBackUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
        (addBackUAddress u current step.index).toNat + 32 ≤ read) :
    (addBackIterate v u current count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := addBackAdvance v u current state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count ->
          let step := addBackIterate v u current j next
          (addBackUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
            (addBackUAddress u current step.index).toNat + 32 ≤ read := by
        intro j hj
        have heq : addBackIterate v u current j next =
            addBackIterate v u current (j + 1) state := by
          simpa only [next] using addBackIterate_advance v u current j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      rw [addBackIterate, hrest]
      exact write32_read_above_padded _ _ _ _ (by rw [toByteArray_size])
        hfirst.1 hfirst.2

/-- Later add-back writes preserve every padded word below their destinations. -/
theorem addBackIterate_read_below
    (v u current : UInt256) (count : Nat) (state : AddBackState)
    (read : Nat)
    (hwrites : ∀ j, j < count ->
      let step := addBackIterate v u current j state
      (addBackUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
        read + 32 ≤ (addBackUAddress u current step.index).toNat) :
    (addBackIterate v u current count state).memory.readWithPadding read 32 =
      state.memory.readWithPadding read 32 := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      let next := addBackAdvance v u current state
      have hfirst := hwrites 0 (by omega)
      have htail : ∀ j, j < count ->
          let step := addBackIterate v u current j next
          (addBackUAddress u current step.index).toNat + 32 ≤ step.memory.size ∧
            read + 32 ≤ (addBackUAddress u current step.index).toNat := by
        intro j hj
        have heq : addBackIterate v u current j next =
            addBackIterate v u current (j + 1) state := by
          simpa only [next] using addBackIterate_advance v u current j state
        rw [heq]
        exact hwrites (j + 1) (by omega)
      have hrest := ih next htail
      have hfirstInBounds :
          (addBackUAddress u current state.index).toNat + 32 ≤ state.memory.size := by
        simpa only [addBackIterate] using hfirst.1
      rw [addBackIterate, hrest]
      exact write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by omega) hfirst.2

/-- Starting from a fixed correction-entry memory, ascending in-place writes preserve every
future divisor and window operand. Thus the concrete add-back loop reads exactly the entry
slices. -/
theorem addBackInitialObservedInputs_eq_slices
    (mem : ByteArray) (aw v u : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat) :
    let initial := MultiLimbSchoolbookDigitFunction.addBackInitial mem aw
    addBackVDigits v u (UInt256.ofNat current) count initial =
        divisorReadSlice mem aw v 0 count ∧
      addBackUDigits v u (UInt256.ofNat current) count initial =
        windowReadSlice mem aw u current 0 count := by
  let initial := MultiLimbSchoolbookDigitFunction.addBackInitial mem aw
  have hgeometry : ∀ j, j ≤ count ->
      let state := addBackIterate v u (UInt256.ofNat current) j initial
      state.index = UInt256.ofNat j ∧ state.activeWords = aw ∧
        state.memory.size = mem.size := by
    intro j hj
    simpa only [Nat.zero_add] using
      addBackIterate_preserves_geometry v u current 0 j mem.size aw initial hcurrent
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) rfl rfl rfl
  have hstates : ∀ start remaining, start + remaining = count ->
      let state := addBackIterate v u (UInt256.ofNat current) start initial
      addBackVDigits v u (UInt256.ofNat current) remaining state =
          divisorReadSlice mem aw v start remaining ∧
        addBackUDigits v u (UInt256.ofNat current) remaining state =
          windowReadSlice mem aw u current start remaining := by
    intro start remaining htotal
    induction remaining generalizing start with
    | zero => simp [addBackVDigits, addBackUDigits, divisorReadSlice, windowReadSlice]
    | succ remaining ih =>
        let state := addBackIterate v u (UInt256.ofNat current) start initial
        let next := addBackAdvance v u (UInt256.ofNat current) state
        have hstate := hgeometry start (by omega)
        have hstateIndex : state.index = UInt256.ofNat start := by
          simpa only [state] using hstate.1
        have hstateActive : state.activeWords = aw := by
          simpa only [state] using hstate.2.1
        have hstateSize : state.memory.size = mem.size := by
          simpa only [state] using hstate.2.2
        have hvAddress := addBackVAddress_ofNat_toNat v start (by omega) (by omega)
        have huAddress := addBackUAddress_ofNat_toNat u current start hcurrent
          (by omega) (by omega) (by omega)
        have hvAccess :
            (addBackVAddress v (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
          rw [hvAddress]
          omega
        have hvAw : addBackAw1 aw v (UInt256.ofNat start) = aw :=
          MultiLimbOddCompare.afterHeader_eq_of_access aw
            (addBackVAddress v (UInt256.ofNat start)) hvAccess
        have hwrite :
            (addBackUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)).toNat + 32 ≤ state.memory.size := by
          rw [huAddress, hstateSize]
          omega
        have hnextEq : next =
            addBackIterate v u (UInt256.ofNat current) (start + 1) initial := by
          dsimp only [next, state]
          exact addBackAdvance_iterate v u (UInt256.ofNat current) start initial
        have hrest := ih (start := start + 1) (by omega)
        have hcurrentV :
            MultiLimbDivisionTrace.readWord state.memory state.activeWords
                (addBackVAddress v state.index) =
              multiplySubtractVi mem aw v (UInt256.ofNat start) := by
          change MultiLimbDivisionTrace.readWord state.memory state.activeWords
              (addBackVAddress v state.index) =
            MultiLimbDivisionTrace.readWord mem aw
              (multiplySubtractVAddress v (UInt256.ofNat start))
          rw [hstateIndex, hstateActive]
          apply readWord_eq_of_size_read_eq
          · exact hstateSize
          · apply addBackIterate_read_above v u (UInt256.ofNat current) start initial
              (addBackVAddress v (UInt256.ofNat start)).toNat
            intro j hj
            let step := addBackIterate v u (UInt256.ofNat current) j initial
            have hstep := hgeometry j (by omega)
            have huJ := addBackUAddress_ofNat_toNat u current j hcurrent
              (by omega) (by omega) (by omega)
            constructor
            · rw [show step.index = UInt256.ofNat j by simpa only [step] using hstep.1,
                huJ, show step.memory.size = mem.size by
                  simpa only [step] using hstep.2.2]
              omega
            · rw [show step.index = UInt256.ofNat j by simpa only [step] using hstep.1,
                huJ, hvAddress]
              omega
        have hcurrentU :
            MultiLimbDivisionTrace.readWord state.memory
                (addBackAw1 state.activeWords v state.index)
                (addBackUAddress u (UInt256.ofNat current) state.index) =
              MultiLimbDivisionTrace.readWord mem aw
                (multiplySubtractUAddress u (UInt256.ofNat current)
                  (UInt256.ofNat start)) := by
          rw [hstateIndex, hstateActive, hvAw]
          apply readWord_eq_of_size_read_eq
          · exact hstateSize
          · apply addBackIterate_read_above v u (UInt256.ofNat current) start initial
              (addBackUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)).toNat
            intro j hj
            let step := addBackIterate v u (UInt256.ofNat current) j initial
            have hstep := hgeometry j (by omega)
            have huJ := addBackUAddress_ofNat_toNat u current j hcurrent
              (by omega) (by omega) (by omega)
            constructor
            · rw [show step.index = UInt256.ofNat j by simpa only [step] using hstep.1,
                huJ, show step.memory.size = mem.size by
                  simpa only [step] using hstep.2.2]
              omega
            · rw [show step.index = UInt256.ofNat j by simpa only [step] using hstep.1,
                huJ, huAddress]
              omega
        simp only [addBackVDigits, addBackUDigits, divisorReadSlice, windowReadSlice]
        change _ :: addBackVDigits v u (UInt256.ofNat current) remaining next = _ ∧
          _ :: addBackUDigits v u (UInt256.ofNat current) remaining next = _
        constructor
        · rw [hnextEq, hcurrentV, hrest.1]
        · rw [hnextEq, hcurrentU, hrest.2]
  simpa only [initial, addBackIterate] using hstates 0 count (by omega)

/-- Every add-back result word remains at its expected current-window address in final memory;
subsequent iterations write only strictly higher words. -/
theorem addBackResultDigits_eq_finalSlice
    (v u : UInt256) (current start count memSize : Nat)
    (aw : UInt256) (state : AddBackState)
    (hcurrent : 0 < current)
    (hrange : start + count ≤ 32)
    (hwindowRange : current + start + count ≤ 66)
    (hsumWord : current + start + count < UInt256.size)
    (hvFit : v.toNat + 32 * (start + count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + start + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (start + count + 1) ≤ memSize)
    (huMem : u.toNat + 32 * (current + start + count) ≤ memSize)
    (hvActive : v.toNat + 32 * (start + count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + start + count) ≤ 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hindex : state.index = UInt256.ofNat start)
    (hactive : state.activeWords = aw)
    (hsize : state.memory.size = memSize) :
    let final := addBackIterate v u (UInt256.ofNat current) count state
    addBackResultDigits v u (UInt256.ofNat current) count state =
      windowReadSlice final.memory aw u current start count := by
  induction count generalizing start state with
  | zero => rfl
  | succ count ih =>
      have hvAddress := addBackVAddress_ofNat_toNat v start (by omega) (by omega)
      have huAddress := addBackUAddress_ofNat_toNat u current start hcurrent
        (by omega) (by omega) (by omega)
      have hvAccess :
          (addBackVAddress v (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
        rw [hvAddress]
        omega
      have hvAw : addBackAw1 aw v (UInt256.ofNat start) = aw :=
        MultiLimbOddCompare.afterHeader_eq_of_access aw
          (addBackVAddress v (UInt256.ofNat start)) hvAccess
      have hwrite :
          (addBackUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat + 32 ≤ state.memory.size := by
        rw [huAddress, hsize]
        omega
      let vDigit := MultiLimbDivisionTrace.readWord state.memory state.activeWords
        (addBackVAddress v state.index)
      let uDigit := MultiLimbDivisionTrace.readWord state.memory
        (addBackAw1 state.activeWords v state.index)
        (addBackUAddress u (UInt256.ofNat current) state.index)
      let written := evmAddCarryStep uDigit vDigit state.carry
      let next := addBackAdvance v u (UInt256.ofNat current) state
      have hstep := addBackIterate_preserves_geometry v u current start 1 memSize aw state
        hcurrent (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hindex hactive hsize
      have hnextIndex : next.index = UInt256.ofNat (start + 1) := by
        simpa only [next, addBackIterate] using hstep.1
      have hnextActive : next.activeWords = aw := by
        simpa only [next, addBackIterate] using hstep.2.1
      have hnextSize : next.memory.size = memSize := by
        simpa only [next, addBackIterate] using hstep.2.2
      have hrest := ih (start := start + 1) (state := next)
        (hrange := by omega) (hwindowRange := by omega) (hsumWord := by omega)
        (hvFit := by omega) (huFit := by omega) (hvMem := by omega) (huMem := by omega)
        (hvActive := by omega) (huActive := by omega) hnextIndex hnextActive hnextSize
      let final := addBackIterate v u (UInt256.ofNat current) count next
      have hfinalGeometry := addBackIterate_preserves_geometry v u current
        (start + 1) count memSize aw next hcurrent (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hnextIndex hnextActive hnextSize
      have htailRead : final.memory.readWithPadding
            (addBackUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat 32 =
          next.memory.readWithPadding
            (addBackUAddress u (UInt256.ofNat current)
              (UInt256.ofNat start)).toNat 32 := by
        apply addBackIterate_read_below v u (UInt256.ofNat current) count next
          (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)).toNat
        intro j hj
        let step := addBackIterate v u (UInt256.ofNat current) j next
        have hgeometry := addBackIterate_preserves_geometry v u current
          (start + 1) j memSize aw next hcurrent (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          hnextIndex hnextActive hnextSize
        have huJ := addBackUAddress_ofNat_toNat u current (start + 1 + j)
          hcurrent (by omega) (by omega) (by omega)
        constructor
        · rw [show step.index = UInt256.ofNat (start + 1 + j) by
              simpa only [step] using hgeometry.1,
            huJ, show step.memory.size = memSize by
              simpa only [step] using hgeometry.2.2]
          omega
        · rw [show step.index = UInt256.ofNat (start + 1 + j) by
              simpa only [step] using hgeometry.1, huJ, huAddress]
          omega
      have hreadFrame :
          MultiLimbDivisionTrace.readWord final.memory aw
              (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) =
            MultiLimbDivisionTrace.readWord next.memory aw
              (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) := by
        apply readWord_eq_of_size_read_eq
        · rw [hfinalGeometry.2.2, hnextSize]
        · exact htailRead
      have hself :
          MultiLimbDivisionTrace.readWord next.memory aw
              (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) =
            written.1 := by
        have hactiveAddress :
            (addBackUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)).toNat + 32 ≤ 32 * aw.toNat := by
          rw [huAddress]
          omega
        have hreadBack := readWord_wordWrite_self state.memory aw
          (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) written.1
          (addBackUAddress u (UInt256.ofNat current)
            (UInt256.ofNat start)).toNat rfl hwrite hactiveAddress hawFit
        simpa only [next, addBackAdvance, addBackStep, written, vDigit, uDigit,
          hactive, hindex, hvAw] using hreadBack
      simp only [addBackResultDigits, windowReadSlice]
      change written.1 :: addBackResultDigits v u (UInt256.ofNat current) count next = _
      rw [hrest]
      change written.1 :: windowReadSlice final.memory aw u current (start + 1) count = _
      have hfinalEq :
          addBackIterate v u (UInt256.ofNat current) (count + 1) state = final := by rfl
      have hreadFrame' :
          MultiLimbDivisionTrace.readWord final.memory aw
              (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) =
            MultiLimbDivisionTrace.readWord next.memory aw
              (multiplySubtractUAddress u (UInt256.ofNat current)
                (UInt256.ofNat start)) := by
        simpa only [addBackUAddress] using hreadFrame
      have hself' :
          MultiLimbDivisionTrace.readWord next.memory aw
              (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat start)) =
            written.1 := by
        simpa only [addBackUAddress] using hself
      rw [hfinalEq, hreadFrame', hself']

/-- Collector-free add-back theorem: pure limb addition is exactly the final concrete lower
window and carry. -/
theorem addBackFinalMemory_eq_evmAddLimbs_slices
    (mem : ByteArray) (aw v u : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let initial := MultiLimbSchoolbookDigitFunction.addBackInitial mem aw
    let final := addBackIterate v u (UInt256.ofNat current) count initial
    let pure := evmAddLimbs
      (windowReadSlice mem aw u current 0 count)
      (divisorReadSlice mem aw v 0 count) ⟨0⟩
    pure.1 = windowReadSlice final.memory aw u current 0 count ∧
      pure.2 = final.carry := by
  let initial := MultiLimbSchoolbookDigitFunction.addBackInitial mem aw
  let final := addBackIterate v u (UInt256.ofNat current) count initial
  have hinputs := addBackInitialObservedInputs_eq_slices mem aw v u current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive huBelowV
  have harithmetic := addBackIterate_eq_evmAddLimbs v u (UInt256.ofNat current) count initial
  rw [hinputs.1, hinputs.2] at harithmetic
  have hmemory := addBackResultDigits_eq_finalSlice v u current 0 count mem.size aw initial
    hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) hawFit rfl rfl rfl
  dsimp only [initial, final] at harithmetic hmemory ⊢
  exact ⟨harithmetic.1.trans hmemory, harithmetic.2⟩

/-- Pointwise equality of guarded divisor loads lifts to equality of divisor slices. -/
theorem divisorReadSlice_eq_of_reads
    (left right : ByteArray) (leftAw rightAw v : UInt256) (start count : Nat)
    (hreads : ∀ i, start ≤ i -> i < start + count ->
      multiplySubtractVi left leftAw v (UInt256.ofNat i) =
        multiplySubtractVi right rightAw v (UInt256.ofNat i)) :
    divisorReadSlice left leftAw v start count =
      divisorReadSlice right rightAw v start count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [divisorReadSlice]
      rw [hreads start (by omega) (by omega)]
      rw [ih (start := start + 1) (by
        intro i hiLo hiHi
        exact hreads i (by omega) (by omega))]

/-- A write wholly below the divisor allocation preserves every divisor word in a slice. -/
theorem divisorReadSlice_wordWrite_below
    (mem : ByteArray) (aw v word : UInt256) (start count dest : Nat)
    (hwrite : dest + 32 ≤ mem.size)
    (hbelow : ∀ i, start ≤ i -> i < start + count ->
      dest + 32 ≤ (multiplySubtractVAddress v (UInt256.ofNat i)).toNat) :
    divisorReadSlice (word.toByteArray.write 0 mem dest 32) aw v start count =
      divisorReadSlice mem aw v start count := by
  apply divisorReadSlice_eq_of_reads
  intro i hiLo hiHi
  unfold multiplySubtractVi
  exact readWord_wordWrite_below mem aw
    (multiplySubtractVAddress v (UInt256.ofNat i)) word dest hwrite
    (hbelow i hiLo hiHi)

/-- The complete multiply-subtract loop writes only below `v`, hence leaves the divisor slice
unchanged for a possible correction pass. -/
theorem multiplyFinal_divisorSlice_eq
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (huBelowV : u.toNat + 32 * (current + count) ≤ v.toNat) :
    let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
    let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
    divisorReadSlice final.memory final.activeWords v 0 count =
      divisorReadSlice mem aw v 0 count := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  apply divisorReadSlice_eq_of_reads
  intro i hiLo hiHi
  have hvI := multiplySubtractVAddress_ofNat_toNat v i (by omega) (by omega)
  have hread : final.memory.readWithPadding
          (multiplySubtractVAddress v (UInt256.ofNat i)).toNat 32 =
        mem.readWithPadding
          (multiplySubtractVAddress v (UInt256.ofNat i)).toNat 32 := by
    apply multiplySubtractIterate_read_above v u (UInt256.ofNat current) qHat count initial
      (multiplySubtractVAddress v (UInt256.ofNat i)).toNat
    intro j hj
    let step := multiplySubtractIterate v u (UInt256.ofNat current) qHat j initial
    have hstep := multiplySubtractIterate_preserves_geometry v u qHat current 0 j mem.size aw
      initial hcurrent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
    have huJ := multiplySubtractUAddress_ofNat_toNat u current j hcurrent
      (by omega) (by omega) (by omega)
    constructor
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1,
        huJ, show step.memory.size = mem.size by simpa only [step] using hstep.2.2]
      omega
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1, huJ, hvI]
      omega
  have hguarded := readWord_eq_of_size_read_eq final.memory mem aw
    (multiplySubtractVAddress v (UInt256.ofNat i))
    (by simpa only [final] using hgeometry.2.2) hread
  unfold multiplySubtractVi
  rw [show final.activeWords = aw by simpa only [final] using hgeometry.2.1]
  exact hguarded

/-- The saved-top subtraction is also below `v`. The complete subtraction phase therefore
preserves the divisor and the byte-array size used by correction. -/
theorem topResult_preserves_divisor_and_size
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let concrete := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
      (UInt256.ofNat current) qHat count
    divisorReadSlice concrete.memory concrete.activeWords v 0 count =
        divisorReadSlice mem aw v 0 count ∧
      concrete.memory.size = mem.size := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  let concrete := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let subtraction := evmSubBorrow
    (MultiLimbDivisionTrace.readWord final.memory final.activeWords topAddr)
    final.carry final.borrow
  have htop := topResult_eq_knuthSubtractWindow mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  have huTopAddress := multiplySubtractUAddress_ofNat_toNat u current count hcurrent
    hsumWord (by omega) (by omega)
  have htopWrite : topAddr.toNat + 32 ≤ final.memory.size := by
    dsimp only [topAddr]
    rw [huTopAddress, show final.memory.size = mem.size by
      simpa only [final] using hgeometry.2.2]
    omega
  have hdivFinal := multiplyFinal_divisorSlice_eq mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive (by omega)
  have hdivWrite := divisorReadSlice_wordWrite_below final.memory aw v subtraction.1 0 count
    topAddr.toNat htopWrite (by
      intro i hiLo hiHi
      have hvI := multiplySubtractVAddress_ofNat_toNat v i (by omega) (by omega)
      dsimp only [topAddr]
      rw [huTopAddress, hvI]
      omega)
  have hconcreteActive : concrete.activeWords = aw := by
    simpa only [concrete] using htop.2.2.2
  have hdivConcrete :
      divisorReadSlice concrete.memory aw v 0 count =
        divisorReadSlice final.memory aw v 0 count := by
    simpa only [concrete, MultiLimbSchoolbookDigitFunction.topResult,
      MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial,
      topSubtractStep, topAddr, subtraction] using hdivWrite
  have hsizeConcrete : concrete.memory.size = mem.size := by
    have hwriteSize := toByteArray_write32_size_of_le final.memory subtraction.1
      topAddr.toNat final.memory.size final.memory.size rfl (by omega)
      (max_eq_left htopWrite)
    calc
      concrete.memory.size = final.memory.size := by
        simpa only [concrete, MultiLimbSchoolbookDigitFunction.topResult,
          MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial,
          topSubtractStep, topAddr, subtraction] using hwriteSize
      _ = mem.size := by simpa only [final] using hgeometry.2.2
  have hdivFinal' :
      divisorReadSlice final.memory aw v 0 count = divisorReadSlice mem aw v 0 count := by
    calc
      divisorReadSlice final.memory aw v 0 count =
          divisorReadSlice final.memory final.activeWords v 0 count := by
        rw [show final.activeWords = aw by simpa only [final] using hgeometry.2.1]
      _ = divisorReadSlice mem aw v 0 count := by
        simpa only [initial, final] using hdivFinal
  dsimp only
  rw [hconcreteActive]
  exact ⟨hdivConcrete.trans hdivFinal', hsizeConcrete⟩

/-- The correction loop writes the lower `count` words only, so its final state still reads the
saved top word from correction-entry memory. -/
theorem addBackFinal_topRead_eq
    (mem : ByteArray) (aw v u : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat) :
    let initial := MultiLimbSchoolbookDigitFunction.addBackInitial mem aw
    let final := addBackIterate v u (UInt256.ofNat current) count initial
    let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
    MultiLimbDivisionTrace.readWord final.memory final.activeWords topAddr =
      MultiLimbDivisionTrace.readWord mem aw topAddr := by
  let initial := MultiLimbSchoolbookDigitFunction.addBackInitial mem aw
  let final := addBackIterate v u (UInt256.ofNat current) count initial
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  have hgeometry := addBackIterate_preserves_geometry v u current 0 count mem.size aw initial
    hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  have huTop := addBackUAddress_ofNat_toNat u current count hcurrent hsumWord
    (by omega) huFit
  have hread : final.memory.readWithPadding topAddr.toNat 32 =
      mem.readWithPadding topAddr.toNat 32 := by
    apply addBackIterate_read_above v u (UInt256.ofNat current) count initial topAddr.toNat
    intro j hj
    let step := addBackIterate v u (UInt256.ofNat current) j initial
    have hstep := addBackIterate_preserves_geometry v u current 0 j mem.size aw initial
      hcurrent (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) rfl rfl rfl
    have huJ := addBackUAddress_ofNat_toNat u current j hcurrent
      (by omega) (by omega) (by omega)
    constructor
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1,
        huJ, show step.memory.size = mem.size by simpa only [step] using hstep.2.2]
      omega
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1]
      change (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat j)).toNat + 32 ≤
        (addBackUAddress u (UInt256.ofNat current) (UInt256.ofNat count)).toNat
      rw [huJ, huTop]
      omega
  have hguarded := readWord_eq_of_size_read_eq final.memory mem aw topAddr
    (by simpa only [final] using hgeometry.2.2) hread
  dsimp only [topAddr]
  rw [show final.activeWords = aw by simpa only [final] using hgeometry.2.1]
  exact hguarded

/-- The complete concrete correction, including the explicit saved-top carry write, stores the
same lower and top words as pure `knuthAddBack`. -/
theorem correctionTop_eq_knuthAddBack
    (mem : ByteArray) (aw v u qHat : UInt256) (current count : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    let uLower := windowReadSlice mem aw u current 0 count
    let vDigits := divisorReadSlice mem aw v 0 count
    let uTop := MultiLimbDivisionTrace.readWord mem aw
      (multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count))
    let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
    let pure := knuthAddBack subtracted.lower vDigits subtracted.top
    let concrete := MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
      (UInt256.ofNat current) qHat count
    let topAddress := multiplySubtractUAddress u (UInt256.ofNat current)
      (UInt256.ofNat count)
    pure.lower = windowReadSlice concrete.memory aw u current 0 count ∧
      pure.top = MultiLimbDivisionTrace.readWord concrete.memory concrete.activeWords
        topAddress ∧
      concrete.activeWords = aw ∧ concrete.memory.size = mem.size := by
  let uLower := windowReadSlice mem aw u current 0 count
  let vDigits := divisorReadSlice mem aw v 0 count
  let topAddress := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let uTop := MultiLimbDivisionTrace.readWord mem aw topAddress
  let subtracted := knuthSubtractWindow qHat uLower vDigits uTop
  let pure := knuthAddBack subtracted.lower vDigits subtracted.top
  let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  let addInitial := MultiLimbSchoolbookDigitFunction.addBackInitial top.memory aw
  let added := addBackIterate v u (UInt256.ofNat current) count addInitial
  let concrete := topAddStep added.memory added.activeWords topAddress added.carry
  have htop := topResult_eq_knuthSubtractWindow mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have htopActiveEq : top.activeWords = aw := by
    simpa only [top] using htop.2.2.2
  have htopSize : top.memory.size = mem.size := by
    simpa only [top] using hphase.2
  have hdivisorTop : divisorReadSlice top.memory aw v 0 count = vDigits := by
    have hdiv := hphase.1
    rw [show top.activeWords = aw by exact htopActiveEq] at hdiv
    simpa only [top, vDigits] using hdiv
  have hadd := addBackFinalMemory_eq_evmAddLimbs_slices top.memory aw v u current count
    hcurrent hrange hwindowRange hsumWord hvFit huFit
    (by rw [htopSize]; exact hvMem) (by rw [htopSize]; exact huMem)
    hvActive huActive (by omega) hawFit
  have hadd' := hadd
  dsimp only [addInitial, added] at hadd'
  rw [← show subtracted.lower = windowReadSlice top.memory aw u current 0 count by
      simpa only [subtracted, uLower, vDigits, uTop, top, topAddress] using htop.1,
    hdivisorTop] at hadd'
  have htopRead := addBackFinal_topRead_eq top.memory aw v u current count hcurrent hrange
    hwindowRange hsumWord hvFit huFit (by rw [htopSize]; exact hvMem)
    (by rw [htopSize]; exact huMem) hvActive huActive
  have haddedGeometry := addBackIterate_preserves_geometry v u current 0 count
    top.memory.size aw addInitial hcurrent (by simpa using hrange)
    (by simpa using hwindowRange) (by simpa using hsumWord) (by simpa using hvFit)
    (by simpa using huFit) (by rw [htopSize]; simpa only [Nat.zero_add] using hvMem)
    (by rw [htopSize]; simpa only [Nat.zero_add] using huMem)
    (by simpa only [Nat.zero_add] using hvActive)
    (by simpa only [Nat.zero_add] using huActive) rfl rfl rfl
  have haddedActive : added.activeWords = aw := by
    simpa only [added, addInitial] using haddedGeometry.2.1
  have haddedSize : added.memory.size = mem.size := by
    calc
      added.memory.size = top.memory.size := by
        simpa only [added, addInitial] using haddedGeometry.2.2
      _ = mem.size := htopSize
  have htopRead' :
      MultiLimbDivisionTrace.readWord added.memory added.activeWords topAddress =
        subtracted.top := by
    have hentryTop :
        MultiLimbDivisionTrace.readWord top.memory aw topAddress = subtracted.top := by
      calc
        MultiLimbDivisionTrace.readWord top.memory aw topAddress =
            MultiLimbDivisionTrace.readWord top.memory top.activeWords top.address := by
          rw [htopActiveEq]
          rfl
        _ = subtracted.top := by
          simpa only [subtracted, uLower, vDigits, uTop, top, topAddress] using
            htop.2.1.symm
    calc
      MultiLimbDivisionTrace.readWord added.memory added.activeWords topAddress =
          MultiLimbDivisionTrace.readWord top.memory aw topAddress := by
        simpa only [added, addInitial, topAddress] using htopRead
      _ = subtracted.top := hentryTop
  let value := MultiLimbDivisionTrace.readWord added.memory added.activeWords topAddress +
    added.carry
  have huTopAddress := multiplySubtractUAddress_ofNat_toNat u current count hcurrent
    hsumWord (by omega) (by omega)
  have htopWrite : topAddress.toNat + 32 ≤ added.memory.size := by
    dsimp only [topAddress]
    rw [huTopAddress, haddedSize]
    omega
  have htopAccess : topAddress.toNat + 32 ≤ 32 * aw.toNat := by
    dsimp only [topAddress]
    rw [huTopAddress]
    omega
  have htopAw : MultiLimbDivisionTrace.readWords1 aw topAddress = aw :=
    MultiLimbOddCompare.afterHeader_eq_of_access aw topAddress htopAccess
  have hconcreteActive : concrete.activeWords = aw := by
    dsimp only [concrete, topAddStep, topAddAw2, topAddAw1]
    rw [haddedActive, htopAw, htopAw]
  have hlowerPreserved :
      windowReadSlice concrete.memory aw u current 0 count =
        windowReadSlice added.memory aw u current 0 count := by
    have hpreserve := windowReadSlice_wordWrite_above added.memory aw u value current 0 count
      topAddress.toNat htopWrite (by
        intro i hiLo hiHi
        have huI := multiplySubtractUAddress_ofNat_toNat u current i hcurrent
          (by omega) (by omega) (by omega)
        dsimp only [topAddress]
        rw [huI, huTopAddress]
        omega)
    simpa only [concrete, topAddStep, value] using hpreserve
  have htopStored :
      MultiLimbDivisionTrace.readWord concrete.memory concrete.activeWords topAddress =
        value := by
    have hreadBack := readWord_wordWrite_self added.memory aw topAddress value
      topAddress.toNat rfl htopWrite htopAccess hawFit
    rw [hconcreteActive]
    simpa only [concrete, topAddStep, value] using hreadBack
  have hconcreteSize : concrete.memory.size = mem.size := by
    have hwriteSize := toByteArray_write32_size_of_le added.memory value topAddress.toNat
      added.memory.size added.memory.size rfl (by omega) (max_eq_left htopWrite)
    calc
      concrete.memory.size = added.memory.size := by
        simpa only [concrete, topAddStep, value] using hwriteSize
      _ = mem.size := haddedSize
  have hpureLower : pure.lower = windowReadSlice added.memory aw u current 0 count := by
    dsimp only [pure, knuthAddBack]
    exact hadd'.1
  have haddCarry :
      (evmAddLimbs subtracted.lower vDigits ⟨0⟩).2 = added.carry := by
    simpa only [added, addInitial] using hadd'.2
  have hpureTop : pure.top = value := by
    dsimp only [pure, knuthAddBack, value]
    rw [htopRead', haddCarry]
    simp only [evmAddCarryStep]
    rw [u256_add_comm subtracted.top ⟨0⟩, u256_zero_add]
  have haddedActual :
      MultiLimbSchoolbookDigitFunction.addBackFinal mem aw v u
        (UInt256.ofNat current) qHat count = added := by
    dsimp only [MultiLimbSchoolbookDigitFunction.addBackFinal,
      MultiLimbSchoolbookDigitFunction.addBackInitial, added, addInitial, top]
    rw [htopActiveEq]
  have hconcreteActual :
      MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u
        (UInt256.ofNat current) qHat count = concrete := by
    dsimp only [MultiLimbSchoolbookDigitFunction.correctionTop]
    rw [haddedActual]
    change topAddStep added.memory added.activeWords top.address added.carry = concrete
    change topAddStep added.memory added.activeWords topAddress added.carry = concrete
    rfl
  dsimp only
  rw [hconcreteActual]
  exact ⟨hpureLower.trans hlowerPreserved.symm,
    hpureTop.trans htopStored.symm, hconcreteActive, hconcreteSize⟩

/-- The full multiply-subtract plus saved-top write preserves every padded word below the `u`
window. -/
theorem topResult_read_below_eq
    (mem : ByteArray) (aw v u qHat : UInt256) (current count read : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (hreadBelow : read + 32 ≤ u.toNat + 32 * current) :
    (MultiLimbSchoolbookDigitFunction.topResult mem aw v u (UInt256.ofNat current)
      qHat count).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let subtraction := evmSubBorrow
    (MultiLimbDivisionTrace.readWord final.memory final.activeWords topAddr)
    final.carry final.borrow
  have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  have hmul : final.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
    apply multiplySubtractIterate_read_below v u (UInt256.ofNat current) qHat count initial read
    intro j hj
    let step := multiplySubtractIterate v u (UInt256.ofNat current) qHat j initial
    have hstep := multiplySubtractIterate_preserves_geometry v u qHat current 0 j mem.size
      aw initial hcurrent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
    have huJ := multiplySubtractUAddress_ofNat_toNat u current j hcurrent
      (by omega) (by omega) (by omega)
    constructor
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1,
        huJ, show step.memory.size = mem.size by simpa only [step] using hstep.2.2]
      omega
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1, huJ]
      omega
  have huTop := multiplySubtractUAddress_ofNat_toNat u current count hcurrent hsumWord
    (by omega) (by omega)
  have htopWrite : topAddr.toNat + 32 ≤ final.memory.size := by
    dsimp only [topAddr]
    rw [huTop, show final.memory.size = mem.size by
      simpa only [final] using hgeometry.2.2]
    omega
  have htopFrame := write32_read_below subtraction.1.toByteArray final.memory topAddr.toNat
    read (by rw [toByteArray_size]) (by omega) (by
      dsimp only [topAddr]
      rw [huTop]
      omega)
  calc
    (MultiLimbSchoolbookDigitFunction.topResult mem aw v u (UInt256.ofNat current)
        qHat count).memory.readWithPadding read 32 =
        final.memory.readWithPadding read 32 := by
      simpa only [MultiLimbSchoolbookDigitFunction.topResult,
        MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial,
        topSubtractStep, topAddr, subtraction] using htopFrame
    _ = mem.readWithPadding read 32 := hmul

/-- The full multiply-subtract plus saved-top write also preserves every padded word wholly above
the current `u` window. -/
theorem topResult_read_above_eq
    (mem : ByteArray) (aw v u qHat : UInt256) (current count read : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (hreadAbove : u.toNat + 32 * (current + count + 1) ≤ read) :
    (MultiLimbSchoolbookDigitFunction.topResult mem aw v u (UInt256.ofNat current)
      qHat count).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  let initial := MultiLimbSchoolbookDigitFunction.multiplyInitial mem aw
  let final := multiplySubtractIterate v u (UInt256.ofNat current) qHat count initial
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let subtraction := evmSubBorrow
    (MultiLimbDivisionTrace.readWord final.memory final.activeWords topAddr)
    final.carry final.borrow
  have hgeometry := multiplySubtractIterate_preserves_geometry v u qHat current 0 count
    mem.size aw initial hcurrent (by simpa using hrange) (by simpa using hwindowRange)
    (by simpa using hsumWord) (by simpa using hvFit) (by simpa using huFit)
    (by simpa using hvMem) (by simpa using huMem) (by simpa using hvActive)
    (by simpa using huActive) rfl rfl rfl
  have hmul : final.memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
    apply multiplySubtractIterate_read_above v u (UInt256.ofNat current) qHat count initial read
    intro j hj
    let step := multiplySubtractIterate v u (UInt256.ofNat current) qHat j initial
    have hstep := multiplySubtractIterate_preserves_geometry v u qHat current 0 j mem.size
      aw initial hcurrent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) rfl rfl rfl
    have huJ := multiplySubtractUAddress_ofNat_toNat u current j hcurrent
      (by omega) (by omega) (by omega)
    constructor
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1,
        huJ, show step.memory.size = mem.size by simpa only [step] using hstep.2.2]
      omega
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1, huJ]
      omega
  have huTop := multiplySubtractUAddress_ofNat_toNat u current count hcurrent hsumWord
    (by omega) (by omega)
  have htopWrite : topAddr.toNat + 32 ≤ final.memory.size := by
    dsimp only [topAddr]
    rw [huTop, show final.memory.size = mem.size by
      simpa only [final] using hgeometry.2.2]
    omega
  have htopFrame := write32_read_above_padded subtraction.1.toByteArray final.memory
    topAddr.toNat read (by rw [toByteArray_size]) htopWrite (by
      dsimp only [topAddr]
      rw [huTop]
      omega)
  calc
    (MultiLimbSchoolbookDigitFunction.topResult mem aw v u (UInt256.ofNat current)
        qHat count).memory.readWithPadding read 32 =
        final.memory.readWithPadding read 32 := by
      simpa only [MultiLimbSchoolbookDigitFunction.topResult,
        MultiLimbSchoolbookDigitFunction.multiplyFinal, final, initial,
        topSubtractStep, topAddr, subtraction] using htopFrame
    _ = mem.readWithPadding read 32 := hmul

/-- The optional add-back and final top-carry write retain the same below-`u` frame. -/
theorem correctionTop_read_below_eq
    (mem : ByteArray) (aw v u qHat : UInt256) (current count read : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hreadBelow : read + 32 ≤ u.toNat + 32 * current) :
    (MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u (UInt256.ofNat current)
      qHat count).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  let initial := MultiLimbSchoolbookDigitFunction.addBackInitial top.memory aw
  let added := addBackIterate v u (UInt256.ofNat current) count initial
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let value := MultiLimbDivisionTrace.readWord added.memory added.activeWords topAddr + added.carry
  have htopSemantic := topResult_eq_knuthSubtractWindow mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have htopActiveEq : top.activeWords = aw := by simpa only [top] using htopSemantic.2.2.2
  have htopSize : top.memory.size = mem.size := by simpa only [top] using hphase.2
  have haddedGeometry := addBackIterate_preserves_geometry v u current 0 count
    top.memory.size aw initial hcurrent (by simpa using hrange)
    (by simpa using hwindowRange) (by simpa using hsumWord) (by simpa using hvFit)
    (by simpa using huFit) (by rw [htopSize]; simpa only [Nat.zero_add] using hvMem)
    (by rw [htopSize]; simpa only [Nat.zero_add] using huMem)
    (by simpa only [Nat.zero_add] using hvActive)
    (by simpa only [Nat.zero_add] using huActive) rfl rfl rfl
  have hadd : added.memory.readWithPadding read 32 = top.memory.readWithPadding read 32 := by
    apply addBackIterate_read_below v u (UInt256.ofNat current) count initial read
    intro j hj
    let step := addBackIterate v u (UInt256.ofNat current) j initial
    have hstep := addBackIterate_preserves_geometry v u current 0 j top.memory.size aw initial
      hcurrent (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) rfl rfl rfl
    have huJ := addBackUAddress_ofNat_toNat u current j hcurrent
      (by omega) (by omega) (by omega)
    constructor
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1,
        huJ, show step.memory.size = top.memory.size by
          simpa only [step] using hstep.2.2]
      rw [htopSize]
      omega
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1, huJ]
      omega
  have huTop := addBackUAddress_ofNat_toNat u current count hcurrent hsumWord
    (by omega) (by omega)
  have huTop' : topAddr.toNat = u.toNat + 32 * (current + count) := by
    simpa only [topAddr, addBackUAddress] using huTop
  have htopWrite : topAddr.toNat + 32 ≤ added.memory.size := by
    rw [huTop', show added.memory.size = top.memory.size by
      simpa only [added, initial] using haddedGeometry.2.2, htopSize]
    omega
  have htopFrame := write32_read_below value.toByteArray added.memory topAddr.toNat read
    (by rw [toByteArray_size]) (by omega) (by
      rw [huTop']
      omega)
  have htopInitial := topResult_read_below_eq mem aw v u qHat current count read hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    hreadBelow
  calc
    (MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u (UInt256.ofNat current)
        qHat count).memory.readWithPadding read 32 =
        added.memory.readWithPadding read 32 := by
      have hactualAdded :
          MultiLimbSchoolbookDigitFunction.addBackFinal mem aw v u
            (UInt256.ofNat current) qHat count = added := by
        dsimp only [MultiLimbSchoolbookDigitFunction.addBackFinal,
          MultiLimbSchoolbookDigitFunction.addBackInitial, added, initial, top]
        rw [htopActiveEq]
      simpa only [MultiLimbSchoolbookDigitFunction.correctionTop, hactualAdded,
        topAddr, top, topAddStep, value] using htopFrame
    _ = top.memory.readWithPadding read 32 := hadd
    _ = mem.readWithPadding read 32 := by simpa only [top] using htopInitial

/-- The optional add-back and final top-carry write preserve every padded word wholly above the
current `u` window. -/
theorem correctionTop_read_above_eq
    (mem : ByteArray) (aw v u qHat : UInt256) (current count read : Nat)
    (hcurrent : 0 < current)
    (hrange : count ≤ 32)
    (hwindowRange : current + count ≤ 66)
    (hsumWord : current + count < UInt256.size)
    (hvFit : v.toNat + 32 * (count + 1) < UInt256.size)
    (huFit : u.toNat + 32 * (current + count) < UInt256.size)
    (hvMem : v.toNat + 32 * (count + 1) ≤ mem.size)
    (huMem : u.toNat + 32 * (current + count) ≤ mem.size)
    (hvActive : v.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (huActive : u.toNat + 32 * (current + count) ≤ 32 * aw.toNat)
    (htopMem : u.toNat + 32 * (current + count + 1) ≤ mem.size)
    (htopActive : u.toNat + 32 * (current + count + 1) ≤ 32 * aw.toNat)
    (htopBelowV : u.toNat + 32 * (current + count + 1) ≤ v.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hreadAbove : u.toNat + 32 * (current + count + 1) ≤ read) :
    (MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u (UInt256.ofNat current)
      qHat count).memory.readWithPadding read 32 = mem.readWithPadding read 32 := by
  let top := MultiLimbSchoolbookDigitFunction.topResult mem aw v u
    (UInt256.ofNat current) qHat count
  let initial := MultiLimbSchoolbookDigitFunction.addBackInitial top.memory aw
  let added := addBackIterate v u (UInt256.ofNat current) count initial
  let topAddr := multiplySubtractUAddress u (UInt256.ofNat current) (UInt256.ofNat count)
  let value := MultiLimbDivisionTrace.readWord added.memory added.activeWords topAddr + added.carry
  have htopSemantic := topResult_eq_knuthSubtractWindow mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have hphase := topResult_preserves_divisor_and_size mem aw v u qHat current count hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem
    htopActive htopBelowV hawFit
  have htopActiveEq : top.activeWords = aw := by simpa only [top] using htopSemantic.2.2.2
  have htopSize : top.memory.size = mem.size := by simpa only [top] using hphase.2
  have haddedGeometry := addBackIterate_preserves_geometry v u current 0 count
    top.memory.size aw initial hcurrent (by simpa using hrange)
    (by simpa using hwindowRange) (by simpa using hsumWord) (by simpa using hvFit)
    (by simpa using huFit) (by rw [htopSize]; simpa only [Nat.zero_add] using hvMem)
    (by rw [htopSize]; simpa only [Nat.zero_add] using huMem)
    (by simpa only [Nat.zero_add] using hvActive)
    (by simpa only [Nat.zero_add] using huActive) rfl rfl rfl
  have hadd : added.memory.readWithPadding read 32 = top.memory.readWithPadding read 32 := by
    apply addBackIterate_read_above v u (UInt256.ofNat current) count initial read
    intro j hj
    let step := addBackIterate v u (UInt256.ofNat current) j initial
    have hstep := addBackIterate_preserves_geometry v u current 0 j top.memory.size aw initial
      hcurrent (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) rfl rfl rfl
    have huJ := addBackUAddress_ofNat_toNat u current j hcurrent
      (by omega) (by omega) (by omega)
    constructor
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1,
        huJ, show step.memory.size = top.memory.size by
          simpa only [step] using hstep.2.2, htopSize]
      omega
    · rw [show step.index = UInt256.ofNat j by
          simpa only [step, Nat.zero_add] using hstep.1, huJ]
      omega
  have huTop := addBackUAddress_ofNat_toNat u current count hcurrent hsumWord
    (by omega) (by omega)
  have huTop' : topAddr.toNat = u.toNat + 32 * (current + count) := by
    simpa only [topAddr, addBackUAddress] using huTop
  have htopWrite : topAddr.toNat + 32 ≤ added.memory.size := by
    rw [huTop', show added.memory.size = top.memory.size by
      simpa only [added, initial] using haddedGeometry.2.2, htopSize]
    omega
  have htopFrame := write32_read_above_padded value.toByteArray added.memory topAddr.toNat read
    (by rw [toByteArray_size]) htopWrite (by rw [huTop']; omega)
  have htopInitial := topResult_read_above_eq mem aw v u qHat current count read hcurrent
    hrange hwindowRange hsumWord hvFit huFit hvMem huMem hvActive huActive htopMem hreadAbove
  calc
    (MultiLimbSchoolbookDigitFunction.correctionTop mem aw v u (UInt256.ofNat current)
        qHat count).memory.readWithPadding read 32 =
        added.memory.readWithPadding read 32 := by
      have hactualAdded :
          MultiLimbSchoolbookDigitFunction.addBackFinal mem aw v u
            (UInt256.ofNat current) qHat count = added := by
        dsimp only [MultiLimbSchoolbookDigitFunction.addBackFinal,
          MultiLimbSchoolbookDigitFunction.addBackInitial, added, initial, top]
        rw [htopActiveEq]
      simpa only [MultiLimbSchoolbookDigitFunction.correctionTop, hactualAdded,
        topAddr, top, topAddStep, value] using htopFrame
    _ = top.memory.readWithPadding read 32 := hadd
    _ = mem.readWithPadding read 32 := by simpa only [top] using htopInitial

end Modexp.MultiLimbSchoolbookIterationSemantic
