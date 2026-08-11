import Examples.Precompiles.Modexp.MultiLimbBarrettSubtractContract

/-!
# Barrett correction comparison and final-copy contracts

This module executes the outer correction control flow around the concrete subtraction pass.  It
keeps the descending comparison branches separate so their instruction and gas costs remain exact.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettCompare

open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option Elab.async false

def barrettCopyBytes (kWords : Nat) : UInt256 :=
  (UInt256.ofNat kWords).shiftLeft ⟨5⟩

def barrettCopySource (r2 : UInt256) : UInt256 := r2 + ⟨32⟩

def barrettCopyTarget (result : UInt256) : UInt256 := result + ⟨32⟩

def barrettFinalMemory
    (mem : ByteArray) (r2 result : UInt256) (kWords : Nat) : ByteArray :=
  mem.write (barrettCopySource r2).toNat mem (barrettCopyTarget result).toNat
    (barrettCopyBytes kWords).toNat

def barrettFinalWords
    (aw r2 result : UInt256) (kWords : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat
    (max (barrettCopyTarget result).toNat (barrettCopySource r2).toNat)
    (barrettCopyBytes kWords).toNat)

/-- Gas of the deployed `MCOPY` itself, including both source/destination expansion. -/
def barrettCopyOpcodeGas
    (aw r2 result : UInt256) (kWords : Nat) : Nat :=
  (Cₘ (barrettFinalWords aw r2 result kWords) - Cₘ aw) +
    GasConstants.Gverylow +
      GasConstants.Gcopy * (((barrettCopyBytes kWords).toNat + 31) / 32)

/-- Enter the descending comparison when the extra `r2[k]` limb is zero and `k>0`. -/
theorem correctionTopZeroEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {top iter n r2 returnPc result : UInt256}
    (htop : top = ⟨0⟩) (hkPos : 0 < kWords)
    (hkWord : kWords < UInt256.size)
    (hdepth : tail.length + 7 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: top.isZero :: top.isZero.isZero :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat kWords :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc (steps + 9) (gasUsed + 36) := by
  subst top
  have htopZero : (⟨0⟩ : UInt256).isZero = ⟨1⟩ := by native_decide
  have hgeqZero : (⟨0⟩ : UInt256).isZero.isZero = ⟨0⟩ := by native_decide
  have hkCondition : UInt256.ofNat kWords ≠ ⟨0⟩ := by
    intro hk
    have hnat := congrArg UInt256.toNat hk
    rw [UInt256.toNat_ofNat_of_lt hkWord] at hnat
    have hzero : (⟨0⟩ : UInt256).toNat = 0 := by decide
    rw [hzero] at hnat
    omega
  have rd6866 := h.jumpiT (by native_decide) (by rw [htopZero]; native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd6876 := GeneratedTraces.trace_6866_body
    (by simp only [List.length_cons]; omega) rd6866
  have rd6882 := rd6876.jumpiT (by native_decide) hkCondition
    (by native_decide) (by simp only [List.length_cons]; omega)
  have normalized := rd6882.withIndices (k' := steps + 9) (by omega)
    (C' := gasUsed + 36) (by omega)
  simpa using normalized

/-- A nonzero extra limb enters subtraction while retaining either outer iteration value. -/
theorem correctionTopNonzeroEntryGeneralExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {top iter n r2 returnPc result : UInt256}
    (htop : top ≠ ⟨0⟩)
    (hdepth : tail.length + 7 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: top.isZero :: top.isZero.isZero :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6780⟩
      (⟨0⟩ :: ⟨0⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc (steps + 12) (gasUsed + 49) := by
  have hzero : top.isZero = ⟨0⟩ := isZero_eq_zero_of_ne htop
  have hone : top.isZero.isZero = ⟨1⟩ := by rw [hzero]; native_decide
  have hzero2 : top.isZero.isZero.isZero = ⟨0⟩ := by rw [hone]; native_decide
  have rd6757 := h.jumpiNT (by native_decide) hzero
    (by simp only [List.length_cons]; omega)
  have rd6764 := GeneratedTraces.trace_6757_notTaken
    (by simp only [List.length_cons]; omega) rd6757 (by native_decide)
    (by simpa only [hzero2])
  have rd6777 := GeneratedTraces.trace_6764_taken
    (by simp only [List.length_cons]; omega) rd6764 (by native_decide)
    (by rw [hone]; native_decide) (by native_decide)
  have rd6780 := evm_run rd6777 with [
    jumpdest,
    push0,
    push0
  ]
  have normalized := rd6780.withIndices (k' := steps + 12) (by omega)
    (C' := gasUsed + 49) (by omega)
  simpa [hzero, hone] using normalized

/-- Include the proved initial correction-loop guard and stop at the common pass body. -/
theorem correctionTopNonzeroPassExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {top iter n r2 returnPc result : UInt256}
    (htop : top ≠ ⟨0⟩) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: top.isZero :: top.isZero.isZero :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6794⟩
      (⟨0⟩ :: ⟨0⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc (steps + 18) (gasUsed + 72) := by
  have rd6780 := correctionTopNonzeroEntryGeneralExact
    (tail := tail) htop (by omega) h
  have hcondition : (⟨0⟩ : UInt256).lt (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
    rw [ult_one (by
      rw [UInt256.toNat_ofNat_of_lt hkWord]
      norm_num)]
    native_decide
  have rd6794 := GeneratedTraces.trace_6780_taken
    (tail := n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) rd6780 (by native_decide)
    hcondition (by native_decide)
  have normalized := rd6794.withIndices (k' := steps + 18) (by omega)
    (C' := gasUsed + 72) (by omega)
  simpa using normalized

/-- After the first selected subtraction, increment `iter=0` and begin the second top-word test. -/
theorem correctionFirstPassContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {i borrow n r2 returnPc result : UInt256}
    (hdepth : tail.length + 9 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨6788⟩
      (i :: borrow :: ⟨0⟩ :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6738⟩
      (⟨1⟩ :: UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords ::
        r2 :: returnPc :: result :: tail)
      mem aw rdata acc (steps + 15) (gasUsed + 56) := by
  have rd := GeneratedTraces.trace_6788_taken
    (tail := UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
      returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide)
    (by native_decide) (by native_decide)
  have normalized := rd.withIndices (k' := steps + 15) (by omega)
    (C' := gasUsed + 56) (by omega)
  simpa using normalized

/-- Load the current extra limb at the start of either correction iteration. -/
theorem correctionIterationSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hdepth : tail.length + 7 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨6738⟩
      (iter :: UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    let top := correctionTopWord mem aw r2 kWords
    RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: top.isZero :: top.isZero.isZero :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem (correctionTopWords aw r2 kWords) rdata acc
      (steps + 14) (gasUsed + 40 +
        (Cₘ (correctionTopWords aw r2 kWords) - Cₘ aw)) := by
  have rd := GeneratedTraces.trace_6738_body
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h
  rw [u256_add_comm r2 ((UInt256.ofNat kWords).shiftLeft ⟨5⟩)] at rd
  have normalized := rd.withIndices (k' := steps + 14) (by omega)
    (C' := gasUsed + 40 + (Cₘ (correctionTopWords aw r2 kWords) - Cₘ aw)) (by
      simp only [correctionTopWords, correctionTopPtr, elementPtr, afterLoad, readWords1]
      omega)
  exact normalized

/-- A completed second subtraction increments `iter=1`, exits, and copies the low `k` limbs. -/
theorem correctionSecondPassCopyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {i borrow n r2 returnPc result : UInt256}
    (hdepth : tail.length + 9 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨6788⟩
      (i :: borrow :: ⟨1⟩ :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6737⟩
      (returnPc :: result :: tail)
      (barrettFinalMemory mem r2 result kWords)
      (barrettFinalWords aw r2 result kWords) rdata acc
      (steps + 28) (gasUsed + 89 + barrettCopyOpcodeGas aw r2 result kWords) := by
  have rd6721 := GeneratedTraces.trace_6788_notTaken
    (tail := UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
      returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide)
    (by native_decide)
  have rd6737 := GeneratedTraces.trace_6721_body
    (tail := tail) (by omega) (by simpa using rd6721)
  have normalized := rd6737.withIndices (k' := steps + 28) (by omega)
    (C' := gasUsed + 89 + barrettCopyOpcodeGas aw r2 result kWords) (by
      simp only [barrettCopyOpcodeGas, barrettFinalWords, barrettCopyBytes,
        barrettCopySource, barrettCopyTarget]
      omega)
  simpa [barrettFinalMemory, barrettFinalWords, barrettCopyBytes,
    barrettCopySource, barrettCopyTarget, MachineState.M, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def compareIndex (iWords : Nat) : UInt256 := UInt256.ofNat (iWords - 1)

def comparePtr (array : UInt256) (iWords : Nat) : UInt256 :=
  array + (compareIndex iWords).shiftLeft ⟨5⟩ + ⟨32⟩

def compareLeft
    (mem : ByteArray) (aw r2 : UInt256) (iWords : Nat) : UInt256 :=
  readWord mem aw (comparePtr r2 iWords)

def compareAfterLeft (aw r2 : UInt256) (iWords : Nat) : UInt256 :=
  afterLoad aw (comparePtr r2 iWords)

def compareRight
    (mem : ByteArray) (aw n r2 : UInt256) (iWords : Nat) : UInt256 :=
  readWord mem (compareAfterLeft aw r2 iWords) (comparePtr n iWords)

def compareWords (aw n r2 : UInt256) (iWords : Nat) : UInt256 :=
  afterLoad (compareAfterLeft aw r2 iWords) (comparePtr n iWords)

def compareLoadExpansion (aw n r2 : UInt256) (iWords : Nat) : Nat :=
  (Cₘ (compareAfterLeft aw r2 iWords) - Cₘ aw) +
    (Cₘ (compareWords aw n r2 iWords) - Cₘ (compareAfterLeft aw r2 iWords))

private theorem comparePreviousWord
    (iWords : Nat) (hiPos : 0 < iWords) (hiWord : iWords < UInt256.size) :
    UInt256.ofNat iWords + (⟨0⟩ : UInt256).lnot = compareIndex iWords := by
  rw [show iWords = (iWords - 1) + 1 by omega, u256_add_comm]
  change MultiLimbOddCompare.scanIndex (UInt256.ofNat ((iWords - 1) + 1)) =
    UInt256.ofNat (iWords - 1)
  exact MultiLimbOddCompare.scanIndex_ofNat_succ (iWords - 1) (by omega)

private theorem comparePreviousWordLeft
    (iWords : Nat) (hiPos : 0 < iWords) (hiWord : iWords < UInt256.size) :
    (⟨0⟩ : UInt256).lnot + UInt256.ofNat iWords = compareIndex iWords := by
  rw [u256_add_comm]
  exact comparePreviousWord iWords hiPos hiWord

private theorem compareRLenCondition
    (kWords : Nat) (hkWord : kWords + 1 < UInt256.size) :
    (⟨0⟩ : UInt256).lt (UInt256.ofNat (kWords + 1)) ≠ ⟨0⟩ := by
  rw [ult_one (by
    rw [UInt256.toNat_ofNat_of_lt hkWord]
    norm_num)]
  native_decide

/-- Equal limbs with another lower limb remaining continue the descending comparison. -/
theorem compareEqualContinueExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hiMore : 1 < iWords) (hiWord : iWords < UInt256.size)
    (heq : compareLeft mem aw r2 iWords = compareRight mem aw n r2 iWords)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat iWords :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat (iWords - 1) :: ⟨1⟩ :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem (compareWords aw n r2 iWords) rdata acc
      (steps + 36) (gasUsed + 125 + compareLoadExpansion aw n r2 iWords) := by
  have hprevious := comparePreviousWordLeft iWords (by omega) hiWord
  have hgtZero : (compareLeft mem aw r2 iWords).gt
      (compareRight mem aw n r2 iWords) = ⟨0⟩ := by
    rw [heq]
    exact ugt_zero (by omega)
  have hltZero : (compareLeft mem aw r2 iWords).lt
      (compareRight mem aw n r2 iWords) = ⟨0⟩ := by
    rw [heq]
    exact ult_zero (by omega)
  have hcontinue : UInt256.ofNat (iWords - 1) ≠ ⟨0⟩ := by
    intro hz
    have hnat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt (by omega : iWords - 1 < UInt256.size)] at hnat
    have hzero : (⟨0⟩ : UInt256).toNat = 0 := by decide
    rw [hzero] at hnat
    omega
  have rd6911 := GeneratedTraces.trace_6882_notTaken
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hgtZero)
  have rd6917 := GeneratedTraces.trace_6911_notTaken
    (by simp only [List.length_cons]; omega) rd6911 (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hltZero)
  have rd6882 := GeneratedTraces.trace_6917_taken
    (by simp only [List.length_cons]; omega) rd6917 (by native_decide)
    (by simpa [hprevious] using hcontinue) (by native_decide)
  rw [hprevious] at rd6882
  have normalized := rd6882.withIndices (k' := steps + 36) (by omega)
    (C' := gasUsed + 125 + compareLoadExpansion aw n r2 iWords) (by
      simp only [compareLoadExpansion, compareWords, compareAfterLeft, comparePtr,
        compareIndex, afterLoad, readWords1]
      omega)
  simpa [compareWords, compareAfterLeft, comparePtr, compareIndex, afterLoad, readWord,
    readWords1, hprevious] using normalized

/-- A greater limb fixes `geq=1` and enters the selected subtraction pass. -/
theorem compareGreaterExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hiPos : 0 < iWords) (hiWord : iWords < UInt256.size)
    (hkWord : kWords + 1 < UInt256.size)
    (hgt : (compareLeft mem aw r2 iWords).gt
      (compareRight mem aw n r2 iWords) ≠ ⟨0⟩)
    (hnotLt : (compareLeft mem aw r2 iWords).lt
      (compareRight mem aw n r2 iWords) = ⟨0⟩)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat iWords :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6794⟩
      (⟨0⟩ :: ⟨0⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem (compareWords aw n r2 iWords) rdata acc
      (steps + 62) (gasUsed + 219 + compareLoadExpansion aw n r2 iWords) := by
  have hprevious := comparePreviousWordLeft iWords hiPos hiWord
  have rd6932 := GeneratedTraces.trace_6882_taken
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hgt) (by native_decide)
  have rd6917 := GeneratedTraces.trace_6932_notTaken
    (by simp only [List.length_cons]; omega) rd6932 (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hnotLt)
  have rd6877 := GeneratedTraces.trace_6917_notTaken
    (by simp only [List.length_cons]; omega) rd6917 (by native_decide) (by native_decide)
  have rd6764 := GeneratedTraces.trace_6877_notTaken
    (by simp only [List.length_cons]; omega) rd6877 (by native_decide) (by native_decide)
  have rd6777 := GeneratedTraces.trace_6764_taken
    (by simp only [List.length_cons]; omega) rd6764 (by native_decide)
    (by native_decide) (by native_decide)
  have rd6794 := GeneratedTraces.trace_6777_taken
    (by simp only [List.length_cons]; omega) rd6777 (by native_decide)
    (compareRLenCondition kWords hkWord) (by native_decide)
  rw [hprevious] at rd6794
  have normalized := rd6794.withIndices (k' := steps + 62) (by omega)
    (C' := gasUsed + 219 + compareLoadExpansion aw n r2 iWords) (by
      simp only [compareLoadExpansion, compareWords, compareAfterLeft, comparePtr,
        compareIndex, afterLoad, readWords1]
      omega)
  simpa [compareWords, compareAfterLeft, comparePtr, compareIndex, afterLoad, readWord,
    readWords1, hprevious] using normalized

/-- Equality at the least-significant limb also selects subtraction (`r2=n`). -/
theorem compareEqualTerminalExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (heq : compareLeft mem aw r2 1 = compareRight mem aw n r2 1)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6882⟩
      (⟨1⟩ :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6794⟩
      (⟨0⟩ :: ⟨0⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem (compareWords aw n r2 1) rdata acc
      (steps + 56) (gasUsed + 200 + compareLoadExpansion aw n r2 1) := by
  have hleftZero : (compareLeft mem aw r2 1).lt
      (compareRight mem aw n r2 1) = ⟨0⟩ := by
    rw [heq]
    exact ult_zero (by omega)
  have hrightZero : (compareLeft mem aw r2 1).gt
      (compareRight mem aw n r2 1) = ⟨0⟩ := by
    rw [heq]
    exact ugt_zero (by omega)
  have hprevious : (⟨0⟩ : UInt256).lnot + ⟨1⟩ = compareIndex 1 := by
    native_decide
  have rd6911 := GeneratedTraces.trace_6882_notTaken
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hrightZero)
  have rd6917 := GeneratedTraces.trace_6911_notTaken
    (by simp only [List.length_cons]; omega) rd6911 (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hleftZero)
  have rd6877 := GeneratedTraces.trace_6917_notTaken
    (by simp only [List.length_cons]; omega) rd6917 (by native_decide) (by native_decide)
  have rd6764 := GeneratedTraces.trace_6877_notTaken
    (by simp only [List.length_cons]; omega) rd6877 (by native_decide) (by native_decide)
  have rd6777 := GeneratedTraces.trace_6764_taken
    (by simp only [List.length_cons]; omega) rd6764 (by native_decide)
    (by native_decide) (by native_decide)
  have rd6794 := GeneratedTraces.trace_6777_taken
    (by simp only [List.length_cons]; omega) rd6777 (by native_decide)
    (compareRLenCondition kWords hkWord) (by native_decide)
  rw [hprevious] at rd6794
  have normalized := rd6794.withIndices (k' := steps + 56) (by omega)
    (C' := gasUsed + 200 + compareLoadExpansion aw n r2 1) (by
      simp only [compareLoadExpansion, compareWords, compareAfterLeft, comparePtr,
        compareIndex, afterLoad, readWords1]
      omega)
  simpa [compareWords, compareAfterLeft, comparePtr, compareIndex, afterLoad, readWord,
    readWords1] using normalized

/-- A smaller first differing limb exits correction and copies the computed remainder. -/
theorem compareLessCopyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed iWords kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hiPos : 0 < iWords) (hiWord : iWords < UInt256.size)
    (hnotGt : (compareLeft mem aw r2 iWords).gt
      (compareRight mem aw n r2 iWords) = ⟨0⟩)
    (hlt : (compareLeft mem aw r2 iWords).lt
      (compareRight mem aw n r2 iWords) ≠ ⟨0⟩)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat iWords :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6737⟩
      (returnPc :: result :: tail)
      (barrettFinalMemory mem r2 result kWords)
      (barrettFinalWords (compareWords aw n r2 iWords) r2 result kWords)
      rdata acc (steps + 84)
      (gasUsed + 286 + compareLoadExpansion aw n r2 iWords +
        barrettCopyOpcodeGas (compareWords aw n r2 iWords) r2 result kWords) := by
  have hprevious := comparePreviousWordLeft iWords hiPos hiWord
  have rd6911 := GeneratedTraces.trace_6882_notTaken
    (tail := returnPc :: result :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hnotGt)
  have rd6923 := GeneratedTraces.trace_6911_taken
    (by simp only [List.length_cons]; omega) rd6911 (by native_decide) (by
      simpa [compareLeft, compareRight, compareAfterLeft, comparePtr, compareIndex,
        afterLoad, readWord, readWords1, hprevious] using hlt) (by native_decide)
  have rd6737 := GeneratedTraces.trace_6923_body
    (by omega) rd6923
  rw [hprevious] at rd6737
  have normalized := rd6737.withIndices (k' := steps + 84) (by omega)
    (C' := gasUsed + 286 + compareLoadExpansion aw n r2 iWords +
      barrettCopyOpcodeGas (compareWords aw n r2 iWords) r2 result kWords) (by
      simp only [compareLoadExpansion, compareWords, compareAfterLeft, comparePtr, compareIndex,
        barrettCopyOpcodeGas, barrettFinalWords, barrettCopyBytes, barrettCopySource,
        barrettCopyTarget, afterLoad, readWords1]
      omega)
  simpa [compareWords, compareAfterLeft, compareIndex, barrettFinalMemory,
    barrettFinalWords, barrettCopyBytes, barrettCopySource, barrettCopyTarget,
    comparePtr, afterLoad, readWord, readWords1, MachineState.M,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

structure BarrettCompareSelection where
  doSub : Bool
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

/-- Executable descending comparison over the words actually loaded by the deployed code. -/
def selectBarrettCompare (fuel : Nat) (mem : ByteArray) (aw n r2 result : UInt256)
    (kWords iWords : Nat) : Option BarrettCompareSelection :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      let left := compareLeft mem aw r2 iWords
      let right := compareRight mem aw n r2 iWords
      let nextAw := compareWords aw n r2 iWords
      let loadGas := compareLoadExpansion aw n r2 iWords
      if right.toNat < left.toNat then
        some {
          doSub := true
          memory := mem
          activeWords := nextAw
          steps := 62
          gas := 219 + loadGas }
      else if left.toNat < right.toNat then
        some {
          doSub := false
          memory := barrettFinalMemory mem r2 result kWords
          activeWords := barrettFinalWords nextAw r2 result kWords
          steps := 84
          gas := 286 + loadGas + barrettCopyOpcodeGas nextAw r2 result kWords }
      else if iWords = 1 then
        some {
          doSub := true
          memory := mem
          activeWords := nextAw
          steps := 56
          gas := 200 + loadGas }
      else
        match selectBarrettCompare fuel mem nextAw n r2 result kWords (iWords - 1) with
        | none => none
        | some rest => some {
            doSub := rest.doSub
            memory := rest.memory
            activeWords := rest.activeWords
            steps := 36 + rest.steps
            gas := 125 + loadGas + rest.gas }

/-- Fuel at least the number of compared limbs makes the descending selector total. -/
theorem selectBarrettCompare_exists
    {fuel iWords kWords : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    (hiPos : 0 < iWords) (hfuel : iWords ≤ fuel) :
    ∃ selected, selectBarrettCompare fuel mem aw n r2 result kWords iWords = some selected := by
  induction fuel generalizing aw iWords with
  | zero => omega
  | succ fuel ih =>
      rw [selectBarrettCompare]
      by_cases hgreater :
          (compareRight mem aw n r2 iWords).toNat < (compareLeft mem aw r2 iWords).toNat
      · simp only [hgreater, if_true]
        exact ⟨_, rfl⟩
      · simp only [hgreater, if_false]
        by_cases hless :
            (compareLeft mem aw r2 iWords).toNat < (compareRight mem aw n r2 iWords).toNat
        · simp only [hless, if_true]
          exact ⟨_, rfl⟩
        · simp only [hless, if_false]
          by_cases hiOne : iWords = 1
          · simp only [hiOne, if_true]
            exact ⟨_, rfl⟩
          · simp only [hiOne, if_false]
            have hiNext : 0 < iWords - 1 := by omega
            have hfuelNext : iWords - 1 ≤ fuel := by omega
            rcases ih (aw := compareWords aw n r2 iWords) hiNext hfuelNext with
              ⟨rest, hrest⟩
            rw [hrest]
            exact ⟨_, rfl⟩

def BarrettComparePost
    (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (iter n r2 returnPc result : UInt256) (kWords : Nat) (tail : List UInt256)
    (selected : BarrettCompareSelection) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (steps gasUsed : Nat) : Prop :=
  if selected.doSub then
    RDx runtimeBytecode ee g s0 ⟨6794⟩
      (⟨0⟩ :: ⟨0⟩ :: iter :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      selected.memory selected.activeWords rdata acc steps gasUsed
  else
    RDx runtimeBytecode ee g s0 ⟨6737⟩
      (returnPc :: result :: tail)
      selected.memory selected.activeWords rdata acc steps gasUsed

/-- The executable comparison selector describes the exact deployed branch and accumulated gas. -/
theorem barrettCompareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel iWords kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hiPos : 0 < iWords) (hiWord : iWords < UInt256.size)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat iWords :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    match selectBarrettCompare fuel mem aw n r2 result kWords iWords with
    | none => True
    | some selected => BarrettComparePost ee g s0 iter n r2 returnPc result kWords tail
        selected rdata acc (steps + selected.steps) (gasUsed + selected.gas) := by
  induction fuel generalizing aw iWords steps gasUsed with
  | zero => simp [selectBarrettCompare]
  | succ fuel ih =>
      simp only [selectBarrettCompare]
      let left := compareLeft mem aw r2 iWords
      let right := compareRight mem aw n r2 iWords
      let nextAw := compareWords aw n r2 iWords
      let loadGas := compareLoadExpansion aw n r2 iWords
      by_cases hgreater : right.toNat < left.toNat
      · rw [if_pos hgreater]
        have hgt : left.gt right ≠ ⟨0⟩ := by
          apply ne_of_eq_of_ne (ugt_one hgreater)
          native_decide
        have hnotLt : left.lt right = ⟨0⟩ := ult_zero (by omega)
        have rd := compareGreaterExact hiPos hiWord hkWord
          (by simpa [left, right] using hgt) (by simpa [left, right] using hnotLt)
          hdepth h
        simpa [BarrettComparePost, nextAw, loadGas, Nat.add_assoc] using rd
      · rw [if_neg hgreater]
        by_cases hless : left.toNat < right.toNat
        · rw [if_pos hless]
          have hnotGt : left.gt right = ⟨0⟩ := ugt_zero (by omega)
          have hlt : left.lt right ≠ ⟨0⟩ := by
            apply ne_of_eq_of_ne (ult_one hless)
            native_decide
          have rd := compareLessCopyExact hiPos hiWord
            (by simpa [left, right] using hnotGt) (by simpa [left, right] using hlt)
            hdepth h
          simpa [BarrettComparePost, nextAw, loadGas, Nat.add_assoc] using rd
        · rw [if_neg hless]
          have hequal : left = right := by apply u256_inj; omega
          by_cases hiOne : iWords = 1
          · rw [if_pos hiOne]
            subst iWords
            have rd := compareEqualTerminalExact hkWord
              (by simpa [left, right] using hequal) hdepth h
            simpa [BarrettComparePost, nextAw, loadGas, Nat.add_assoc] using rd
          · rw [if_neg hiOne]
            have hiMore : 1 < iWords := by omega
            have hnextPos : 0 < iWords - 1 := by omega
            have hnextWord : iWords - 1 < UInt256.size := by omega
            cases hrest : selectBarrettCompare fuel mem nextAw n r2 result kWords
                (iWords - 1) with
            | none => exact True.intro
            | some rest =>
                change BarrettComparePost ee g s0 iter n r2 returnPc result kWords tail
                  rest rdata acc (steps + (36 + rest.steps))
                  (gasUsed + (125 + loadGas + rest.gas))
                have rdNext := compareEqualContinueExact hiMore hiWord
                  (by simpa [left, right] using hequal) hdepth h
                have rdFinal := ih (aw := nextAw) (iWords := iWords - 1)
                  (steps := steps + 36) (gasUsed := gasUsed + 125 + loadGas)
                  hnextPos hnextWord (by
                    simpa [nextAw, loadGas, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using rdNext)
                rw [hrest] at rdFinal
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal

/-- A successful selector result is an exact path rather than a vacuous `none` case. -/
theorem selectedBarrettCompareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel iWords kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (selected : BarrettCompareSelection)
    (hiPos : 0 < iWords) (hiWord : iWords < UInt256.size)
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1019)
    (hselect : selectBarrettCompare fuel mem aw n r2 result kWords iWords = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨6882⟩
      (UInt256.ofNat iWords :: ⟨1⟩ :: iter :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: r2 :: returnPc :: result :: tail)
      mem aw rdata acc steps gasUsed) :
    BarrettComparePost ee g s0 iter n r2 returnPc result kWords tail selected
      rdata acc (steps + selected.steps) (gasUsed + selected.gas) := by
  have rd := barrettCompareExact (fuel := fuel) hiPos hiWord hkWord hdepth h
  rw [hselect] at rd
  exact rd

/-- Select the nonzero-top shortcut or the complete descending comparison. -/
def selectBarrettDecision (fuel : Nat) (mem : ByteArray) (aw n r2 result : UInt256)
    (kWords : Nat) : Option BarrettCompareSelection :=
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  if top ≠ ⟨0⟩ then
    some {
      doSub := true
      memory := mem
      activeWords := topAw
      steps := 18
      gas := 72 }
  else
    match selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => none
    | some rest => some {
        doSub := rest.doSub
        memory := rest.memory
        activeWords := rest.activeWords
        steps := 9 + rest.steps
        gas := 36 + rest.gas }

/-- The complete top-word/descending decision is total with one unit of fuel per modulus limb. -/
theorem selectBarrettDecision_exists
    {fuel kWords : Nat} {mem : ByteArray} {aw n r2 result : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected, selectBarrettDecision fuel mem aw n r2 result kWords = some selected := by
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  simp only [selectBarrettDecision]
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop]
    exact ⟨_, rfl⟩
  · rw [if_neg htop]
    rcases selectBarrettCompare_exists (mem := mem)
      (aw := topAw) (n := n) (r2 := r2) (result := result)
      (kWords := kWords) hkPos hfuel with ⟨selected, hselected⟩
    rw [hselected]
    exact ⟨_, rfl⟩

/-- The top-word decision is an exact path to subtraction or an already-copied result. -/
theorem barrettDecisionExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: (correctionTopWord mem aw r2 kWords).isZero ::
        (correctionTopWord mem aw r2 kWords).isZero.isZero :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem (correctionTopWords aw r2 kWords) rdata acc steps gasUsed) :
    match selectBarrettDecision fuel mem aw n r2 result kWords with
    | none => True
    | some selected => BarrettComparePost ee g s0 iter n r2 returnPc result kWords tail
        selected rdata acc (steps + selected.steps) (gasUsed + selected.gas) := by
  let top := correctionTopWord mem aw r2 kWords
  let topAw := correctionTopWords aw r2 kWords
  simp only [selectBarrettDecision]
  by_cases htop : top ≠ ⟨0⟩
  · rw [if_pos htop]
    have rd := correctionTopNonzeroPassExact (top := top)
      (aw := topAw) (tail := tail) (n := n) (r2 := r2)
      (returnPc := returnPc) (result := result)
      htop hkWord hdepth (by simpa [top, topAw] using h)
    simpa [BarrettComparePost] using rd
  · rw [if_neg htop]
    have htopZero : top = ⟨0⟩ := by simpa using htop
    have rd6882 := correctionTopZeroEntryExact (top := top) (iter := iter)
      (tail := tail) (n := n) (r2 := r2) (returnPc := returnPc) (result := result)
      htopZero hkPos (by omega) (by omega) (by simpa [top, topAw] using h)
    have rdCompare := barrettCompareExact (fuel := fuel) (iWords := kWords)
      (aw := topAw) hkPos (by omega) hkWord hdepth (by
        simpa [topAw] using rd6882)
    cases hselect : selectBarrettCompare fuel mem topAw n r2 result kWords kWords with
    | none => simp [hselect]
    | some rest =>
        rw [hselect] at rdCompare
        simp only [hselect]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdCompare

/-- A successful complete decision is its exact deployed trace. -/
theorem selectedBarrettDecisionExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel kWords : Nat} {tail : List UInt256}
    {iter n r2 returnPc result : UInt256}
    (selected : BarrettCompareSelection)
    (hkPos : 0 < kWords) (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1019)
    (hselect : selectBarrettDecision fuel mem aw n r2 result kWords = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨6756⟩
      (⟨6866⟩ :: (correctionTopWord mem aw r2 kWords).isZero ::
        (correctionTopWord mem aw r2 kWords).isZero.isZero :: iter ::
        UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords :: r2 ::
        returnPc :: result :: tail)
      mem (correctionTopWords aw r2 kWords) rdata acc steps gasUsed) :
    BarrettComparePost ee g s0 iter n r2 returnPc result kWords tail selected
      rdata acc (steps + selected.steps) (gasUsed + selected.gas) := by
  have rd := barrettDecisionExact (fuel := fuel) hkPos hkWord hdepth h
  rw [hselect] at rd
  exact rd

end Modexp.MultiLimbBarrettCompare
