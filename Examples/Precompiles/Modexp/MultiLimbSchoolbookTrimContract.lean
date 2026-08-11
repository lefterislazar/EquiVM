import Examples.Precompiles.Modexp.MultiLimbSchoolbookRemContract

/-!
# Leading-zero trimming in `schoolbookDiv`

The first division loop scans the dividend from its most significant allocated limb and decrements
`m` while that limb is zero.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookTrim

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def dividendHeader (mem : ByteArray) (aw dividend : UInt256) : UInt256 :=
  MultiLimbOddCompare.headerWord mem aw dividend

def dividendAfterHeader (aw dividend : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader aw dividend

def dividendAddress (dividend : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.elementPtr dividend (UInt256.ofNat index)

def dividendWord (mem : ByteArray) (aw dividend : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.loadedWord mem aw (dividendAddress dividend index)

def dividendAfterWord (aw dividend : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.afterLoad aw (dividendAddress dividend index)

/-- `schoolbookDiv` swaps the allocated remainder pointer below `dLen` at its entry. -/
theorem entryToHeader
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {dLen rem dividend : UInt256}
    (hdepth : tail.length + 3 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨5199⟩
      (rem :: dLen :: dividend :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5201⟩
      (dLen :: rem :: dividend :: tail) mem aw rdata acc (k + 2) (C + 4) := by
  have rd5201 := (evm_run h with [jumpdest, swap1])
  have normalized := rd5201.withIndices
    (k' := k + 2) (C' := C + 4) (by omega) (by omega)
  simpa using normalized

/-- Inspect the current most-significant dividend limb and stop at the value branch. -/
theorem inspectTop
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C remaining count : Nat} {tail : List UInt256}
    {rem dividend value : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (hcount : remaining < count)
    (hcountBound : count ≤ 65)
    (hheader : dividendHeader mem aw dividend = UInt256.ofNat count)
    (hheaderAw : dividendAfterHeader aw dividend = aw)
    (helementAw : dividendAfterWord aw dividend remaining = aw)
    (hvalue : dividendWord mem aw dividend remaining = value)
    (h : RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat (remaining + 1) :: rem :: dividend :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5215⟩
      (⟨5229⟩ :: value.isZero.isZero :: UInt256.ofNat (remaining + 1) ::
        rem :: dividend :: tail)
      mem aw rdata acc (k + 54) (C + 192) := by
  have hsmall : count < UInt256.size := by
    have : 65 < UInt256.size := by decide
    omega
  have hremaining : remaining + 1 < UInt256.size := by omega
  have hmNonzero : UInt256.ofNat (remaining + 1) ≠ ⟨0⟩ := by
    intro hz
    have hn := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hremaining] at hn
    norm_num at hn
  have hguard : (UInt256.ofNat (remaining + 1)).isZero.isZero ≠ ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hmNonzero, Bool.toUInt256]
    native_decide
  have rd6427 := GeneratedTraces.trace_5201_taken
    (tail := rem :: dividend :: tail) (by simp only [List.length_cons]; omega)
    h (by native_decide) hguard (by native_decide)
  have hprev : MultiLimbOddCompare.previousIndex (UInt256.ofNat (remaining + 1)) =
      UInt256.ofNat remaining := by
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (remaining + 1)) =
      UInt256.ofNat remaining
    exact MultiLimbOddCompare.scanIndex_ofNat_succ remaining hremaining
  have hdecIndex :
      UInt256.ofNat (remaining + 1) + (⟨0⟩ : UInt256).lnot = UInt256.ofNat remaining := by
    rw [u256_add_comm]
    exact hprev
  have hnoUnderflow :
      ((UInt256.ofNat (remaining + 1)) + (⟨0⟩ : UInt256).lnot).gt
          (UInt256.ofNat (remaining + 1)) = ⟨0⟩ := by
    rw [hdecIndex]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (by omega : remaining < UInt256.size),
      UInt256.toNat_ofNat_of_lt hremaining]
    omega
  have rd1036 := GeneratedTraces.trace_6420_notTaken
    (by simp only [List.length_cons]; omega) rd6427 (by native_decide)
    hnoUnderflow
  have rd6440 := GeneratedTraces.trace_1036_jump
    (by simp only [List.length_cons]; omega) rd1036 (by native_decide) (by native_decide)
  have harrayBound :
      (UInt256.ofNat remaining).lt (dividendHeader mem aw dividend) ≠ ⟨0⟩ := by
    rw [hheader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt (by omega : remaining < UInt256.size),
        UInt256.toNat_ofNat_of_lt hsmall]
      exact hcount
  have harrayCondition :
      ((UInt256.ofNat (remaining + 1) + (⟨0⟩ : UInt256).lnot).lt
        (MultiLimbOddCompare.headerWord mem aw dividend)).isZero = ⟨0⟩ := by
    rw [hdecIndex]
    have harrayBound' :
        (UInt256.ofNat remaining).lt
          (MultiLimbOddCompare.headerWord mem aw dividend) ≠ ⟨0⟩ := harrayBound
    simp [UInt256.isZero, UInt256.eq0, harrayBound', Bool.toUInt256]
    native_decide
  have rd1539 := GeneratedTraces.trace_6433_notTaken
    (by omega) rd6440 (by native_decide) harrayCondition
  have hheaderAw' : MultiLimbOddCompare.afterHeader aw dividend = aw := hheaderAw
  rw [hdecIndex, ← MultiLimbOddCompare.afterHeader_generated, hheaderAw'] at rd1539
  have rd6446 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have rd5215 := GeneratedTraces.trace_6439_body
    (by simp only [List.length_cons]; omega) rd6446
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd5215
  have hvalueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat remaining).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = value := by
    simpa only [dividendWord, MultiLimbOddCompare.loadedWord, dividendAddress,
      MultiLimbOddCompare.elementPtr] using hvalue
  have helementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat remaining).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = aw := by
    simpa only [dividendAfterWord, MultiLimbOddCompare.afterLoad, dividendAddress,
      MultiLimbOddCompare.elementPtr] using helementAw
  rw [hvalueRaw, helementAwRaw] at rd5215
  have normalized := rd5215.withIndices
    (k' := k + 54) (C' := C + 192) (by omega) (by omega)
  simpa using normalized

/-- One zero most-significant dividend limb decrements `m` and returns to the loop header. -/
theorem zeroCycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C remaining count : Nat} {tail : List UInt256}
    {rem dividend : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (hcount : remaining < count)
    (hcountBound : count ≤ 65)
    (hheader : dividendHeader mem aw dividend = UInt256.ofNat count)
    (hheaderAw : dividendAfterHeader aw dividend = aw)
    (helementAw : dividendAfterWord aw dividend remaining = aw)
    (hzero : dividendWord mem aw dividend remaining = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat (remaining + 1) :: rem :: dividend :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat remaining :: rem :: dividend :: tail)
      mem aw rdata acc (k + 72) (C + 270) := by
  have hremaining : remaining + 1 < UInt256.size := by
    have : 65 < UInt256.size := by decide
    omega
  have hmNonzero : UInt256.ofNat (remaining + 1) ≠ ⟨0⟩ := by
    intro hz
    have hn := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hremaining] at hn
    norm_num at hn
  have hprev : MultiLimbOddCompare.previousIndex (UInt256.ofNat (remaining + 1)) =
      UInt256.ofNat remaining := by
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (remaining + 1)) =
      UInt256.ofNat remaining
    exact MultiLimbOddCompare.scanIndex_ofNat_succ remaining hremaining
  have rd5215 := inspectTop hdepth hcount hcountBound hheader hheaderAw
    helementAw hzero h
  have rd5216 := rd5215.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons]; omega)
  have hmCondition : (UInt256.ofNat (remaining + 1)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hmNonzero, Bool.toUInt256]
    native_decide
  have rd3149 := GeneratedTraces.trace_5216_notTaken
    (by simp only [List.length_cons]; omega) rd5216 (by native_decide)
    hmCondition
  have rd5224 := GeneratedTraces.trace_3149_jump
    (by simp only [List.length_cons]; omega) rd3149 (by native_decide) (by native_decide)
  have rd5201 := (evm_run rd5224 with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨0x1451⟩ (by decide),
    jump (by native_decide)
  ])
  have hprevRaw :
      (⟨0⟩ : UInt256).lnot + UInt256.ofNat (remaining + 1) =
        UInt256.ofNat remaining := hprev
  rw [hprevRaw] at rd5201
  have normalized := rd5201.withIndices
    (k' := k + 72) (C' := C + 270) (by omega) (by omega)
  simpa only [dividendAddress, dividendWord, dividendAfterWord] using normalized

/-- A nonzero current top limb exits the dividend-trimming loop at PC 5229. -/
theorem nonzeroExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C remaining count : Nat} {tail : List UInt256}
    {rem dividend value : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (hcount : remaining < count)
    (hcountBound : count ≤ 65)
    (hheader : dividendHeader mem aw dividend = UInt256.ofNat count)
    (hheaderAw : dividendAfterHeader aw dividend = aw)
    (helementAw : dividendAfterWord aw dividend remaining = aw)
    (hvalue : dividendWord mem aw dividend remaining = value)
    (hvalueNonzero : value ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat (remaining + 1) :: rem :: dividend :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5229⟩
      (UInt256.ofNat (remaining + 1) :: rem :: dividend :: tail)
      mem aw rdata acc (k + 55) (C + 202) := by
  have rd5215 := inspectTop hdepth hcount hcountBound hheader hheaderAw
    helementAw hvalue h
  have hcondition : value.isZero.isZero ≠ ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hvalueNonzero, Bool.toUInt256]
    native_decide
  have rd5229 := rd5215.jumpiT (by native_decide) hcondition (by native_decide)
    (by simp only [List.length_cons]; omega)
  have normalized := rd5229.withIndices
    (k' := k + 55) (C' := C + 202) (by omega) (by omega)
  simpa using normalized

/-- A zero effective dividend length exits without reading an array element. -/
theorem zeroLengthExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {rem dividend : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨5201⟩
      (⟨0⟩ :: rem :: dividend :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5229⟩
      (⟨0⟩ :: rem :: dividend :: tail) mem aw rdata acc (k + 11) (C + 43) := by
  have rd5210 := GeneratedTraces.trace_5201_notTaken
    (tail := rem :: dividend :: tail) (by simp only [List.length_cons]; omega)
    h (by native_decide) (by native_decide)
  have rd5229 := GeneratedTraces.trace_5210_taken
    (by simp only [List.length_cons]; omega) rd5210
    (by native_decide) (by native_decide) (by native_decide)
  have normalized := rd5229.withIndices
    (k' := k + 11) (C' := C + 43) (by omega) (by omega)
  simpa using normalized

/-- A positive effective dividend length transfers the original divisor length to `kEff`. -/
theorem positiveLengthToDivisorTrim
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {m rem dividend ret count divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hm : m ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5229⟩
      (m :: rem :: dividend :: ret :: count :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5237⟩
      (count :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc (k + 6) (C + 23) := by
  have hcondition : m.isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hm, Bool.toUInt256]
    native_decide
  have rd5237 := GeneratedTraces.trace_5229_notTaken
    (tail := divisor :: tail) (by simp only [List.length_cons]; omega)
    h (by native_decide) hcondition
  have normalized := rd5237.withIndices
    (k' := k + 6) (C' := C + 23) (by omega) (by omega)
  simpa using normalized

/-- Trimming `n` explicit zero limbs is the exact iteration of `zeroCycle`. -/
theorem zeroCycles
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C start n count : Nat} {tail : List UInt256}
    {rem dividend : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (hspan : start + n ≤ count)
    (hcountBound : count ≤ 65)
    (hheader : dividendHeader mem aw dividend = UInt256.ofNat count)
    (hheaderAw : dividendAfterHeader aw dividend = aw)
    (helementAw : ∀ i, start ≤ i → i < start + n →
      dividendAfterWord aw dividend i = aw)
    (hzero : ∀ i, start ≤ i → i < start + n →
      dividendWord mem aw dividend i = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat (start + n) :: rem :: dividend :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat start :: rem :: dividend :: tail)
      mem aw rdata acc (k + 72 * n) (C + 270 * n) := by
  induction n generalizing k C with
  | zero =>
      simpa using h
  | succ n ih =>
      have htop : start + n < count := by omega
      have hstartSucc : start + (n + 1) = (start + n) + 1 := by omega
      rw [hstartSucc] at h
      have hcycle := zeroCycle
        (k := k) (C := C) (remaining := start + n) (count := count)
        hdepth htop hcountBound hheader hheaderAw
        (helementAw (start + n) (by omega) (by omega))
        (hzero (start + n) (by omega) (by omega)) h
      have hrest := ih
        (k := k + 72) (C := C + 270)
        (by omega : start + n ≤ count)
        (fun i hlo hhi => helementAw i hlo (by omega))
        (fun i hlo hhi => hzero i hlo (by omega))
        hcycle
      have normalized := hrest.withIndices
        (k' := k + 72 * (n + 1)) (C' := C + 270 * (n + 1))
        (by omega) (by omega)
      simpa using normalized

/-- Compose the function entry with arbitrary leading-zero trimming. -/
theorem entryThroughZeroCycles
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C start n : Nat} {tail : List UInt256}
    {rem dividend : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (hcountBound : start + n ≤ 65)
    (hheader : dividendHeader mem aw dividend = UInt256.ofNat (start + n))
    (hheaderAw : dividendAfterHeader aw dividend = aw)
    (helementAw : ∀ i, start ≤ i → i < start + n →
      dividendAfterWord aw dividend i = aw)
    (hzero : ∀ i, start ≤ i → i < start + n →
      dividendWord mem aw dividend i = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5199⟩
      (rem :: UInt256.ofNat (start + n) :: dividend :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5201⟩
      (UInt256.ofNat start :: rem :: dividend :: tail)
      mem aw rdata acc (k + 2 + 72 * n) (C + 4 + 270 * n) := by
  have rd5201 := entryToHeader (by omega) h
  have trimmed := zeroCycles hdepth (by omega : start + n ≤ start + n)
    hcountBound hheader hheaderAw helementAw hzero rd5201
  have normalized := trimmed.withIndices
    (k' := k + 2 + 72 * n) (C' := C + 4 + 270 * n)
    (by omega) (by omega)
  simpa using normalized

end Modexp.MultiLimbSchoolbookTrim
