import Examples.Precompiles.Modexp.MultiLimbSchoolbookTrimContract

/-!
# Effective-divisor trimming in `schoolbookDiv`

The second division loop decrements `kEff` while it exceeds one and its current top divisor
limb is zero.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookDivisorTrim

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def divisorHeader (mem : ByteArray) (aw divisor : UInt256) : UInt256 :=
  MultiLimbOddCompare.headerWord mem aw divisor

def divisorAfterHeader (aw divisor : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader aw divisor

def divisorAddress (divisor : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.elementPtr divisor (UInt256.ofNat index)

def divisorWord (mem : ByteArray) (aw divisor : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.loadedWord mem aw (divisorAddress divisor index)

def divisorAfterWord (aw divisor : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.afterLoad aw (divisorAddress divisor index)

/-- One zero divisor limb above index zero decrements `kEff` and returns to the loop header. -/
theorem zeroCycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C top count : Nat} {tail : List UInt256}
    {rem dividend ret m divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (htopPos : 0 < top)
    (htop : top < count)
    (hcountBound : count ≤ 32)
    (hheader : divisorHeader mem aw divisor = UInt256.ofNat count)
    (hheaderAw : divisorAfterHeader aw divisor = aw)
    (helementAw : divisorAfterWord aw divisor top = aw)
    (hzero : divisorWord mem aw divisor top = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5237⟩
      (UInt256.ofNat (top + 1) :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5237⟩
      (UInt256.ofNat top :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc (k + 72) (C + 270) := by
  have hsmall : count < UInt256.size := by
    have : 32 < UInt256.size := by decide
    omega
  have htopSucc : top + 1 < UInt256.size := by omega
  have hloop : (UInt256.ofNat (top + 1)).gt ⟨1⟩ ≠ ⟨0⟩ := by
    have heq : (UInt256.ofNat (top + 1)).gt ⟨1⟩ = ⟨1⟩ := by
      apply ugt_one
      rw [UInt256.toNat_ofNat_of_lt htopSucc]
      change 1 < top + 1
      omega
    rw [heq]
    native_decide
  have rd6383 := GeneratedTraces.trace_5237_taken
    (tail := rem :: dividend :: ret :: m :: divisor :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hloop (by native_decide)
  have hprev : MultiLimbOddCompare.previousIndex (UInt256.ofNat (top + 1)) =
      UInt256.ofNat top := by
    change MultiLimbOddCompare.scanIndex (UInt256.ofNat (top + 1)) = UInt256.ofNat top
    exact MultiLimbOddCompare.scanIndex_ofNat_succ top htopSucc
  have hdecIndex :
      UInt256.ofNat (top + 1) + (⟨0⟩ : UInt256).lnot = UInt256.ofNat top := by
    rw [u256_add_comm]
    exact hprev
  have hnoUnderflow :
      (UInt256.ofNat (top + 1) + (⟨0⟩ : UInt256).lnot).gt
        (UInt256.ofNat (top + 1)) = ⟨0⟩ := by
    rw [hdecIndex]
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt (by omega : top < UInt256.size),
      UInt256.toNat_ofNat_of_lt htopSucc]
    omega
  have rd1036 := GeneratedTraces.trace_6376_notTaken
    (by simp only [List.length_cons]; omega) rd6383 (by native_decide) hnoUnderflow
  have rd6396 := GeneratedTraces.trace_1036_jump
    (by simp only [List.length_cons]; omega) rd1036 (by native_decide) (by native_decide)
  have harrayBound :
      (UInt256.ofNat top).lt (divisorHeader mem aw divisor) ≠ ⟨0⟩ := by
    rw [hheader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt (by omega : top < UInt256.size),
        UInt256.toNat_ofNat_of_lt hsmall]
      exact htop
  have harrayCondition :
      ((UInt256.ofNat (top + 1) + (⟨0⟩ : UInt256).lnot).lt
        (MultiLimbOddCompare.headerWord mem aw divisor)).isZero = ⟨0⟩ := by
    rw [hdecIndex]
    have harrayBound' :
        (UInt256.ofNat top).lt (MultiLimbOddCompare.headerWord mem aw divisor) ≠ ⟨0⟩ :=
      harrayBound
    simp [UInt256.isZero, UInt256.eq0, harrayBound', Bool.toUInt256]
    native_decide
  have rd1539 := GeneratedTraces.trace_6389_notTaken
    (by omega) rd6396 (by native_decide) harrayCondition
  have hheaderAw' : MultiLimbOddCompare.afterHeader aw divisor = aw := hheaderAw
  rw [hdecIndex, ← MultiLimbOddCompare.afterHeader_generated, hheaderAw'] at rd1539
  have rd6402 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have rd5252 := GeneratedTraces.trace_6395_body
    (by simp only [List.length_cons]; omega) rd6402
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd5252
  have hzeroRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat top).shiftLeft ⟨5⟩ + divisor + ⟨32⟩) = ⟨0⟩ := by
    simpa only [divisorWord, MultiLimbOddCompare.loadedWord, divisorAddress,
      MultiLimbOddCompare.elementPtr] using hzero
  have helementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat top).shiftLeft ⟨5⟩ + divisor + ⟨32⟩) = aw := by
    simpa only [divisorAfterWord, MultiLimbOddCompare.afterLoad, divisorAddress,
      MultiLimbOddCompare.elementPtr] using helementAw
  rw [hzeroRaw, helementAwRaw] at rd5252
  have rd5253 := rd5252.jumpiNT (by native_decide) rfl
    (by simp only [List.length_cons]; omega)
  have hkCondition : (UInt256.ofNat (top + 1)).isZero = ⟨0⟩ := by
    have hne : UInt256.ofNat (top + 1) ≠ ⟨0⟩ := by
      intro hz
      have hn := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt htopSucc] at hn
      norm_num at hn
    simp [UInt256.isZero, UInt256.eq0, hne, Bool.toUInt256]
    native_decide
  have rd3149 := GeneratedTraces.trace_5253_notTaken
    (by simp only [List.length_cons]; omega) rd5253 (by native_decide) hkCondition
  have rd5261 := GeneratedTraces.trace_3149_jump
    (by simp only [List.length_cons]; omega) rd3149 (by native_decide) (by native_decide)
  have rd5237 := (evm_run rd5261 with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨0x1475⟩ (by decide),
    jump (by native_decide)
  ])
  have hprevRaw :
      (⟨0⟩ : UInt256).lnot + UInt256.ofNat (top + 1) = UInt256.ofNat top := hprev
  rw [hprevRaw] at rd5237
  have normalized := rd5237.withIndices
    (k' := k + 72) (C' := C + 270) (by omega) (by omega)
  simpa only [divisorAddress, divisorWord, divisorAfterWord] using normalized

/-- Trimming `n` explicit zero divisor limbs preserves a positive effective length. -/
theorem zeroCycles
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C start n count : Nat} {tail : List UInt256}
    {rem dividend ret m divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (hstart : 0 < start)
    (hspan : start + n ≤ count)
    (hcountBound : count ≤ 32)
    (hheader : divisorHeader mem aw divisor = UInt256.ofNat count)
    (hheaderAw : divisorAfterHeader aw divisor = aw)
    (helementAw : ∀ i, start ≤ i → i < start + n →
      divisorAfterWord aw divisor i = aw)
    (hzero : ∀ i, start ≤ i → i < start + n →
      divisorWord mem aw divisor i = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨5237⟩
      (UInt256.ofNat (start + n) :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5237⟩
      (UInt256.ofNat start :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc (k + 72 * n) (C + 270 * n) := by
  induction n generalizing k C with
  | zero =>
      simpa using h
  | succ n ih =>
      have htop : start + n < count := by omega
      have hstartSucc : start + (n + 1) = (start + n) + 1 := by omega
      rw [hstartSucc] at h
      have hcycle := zeroCycle
        (k := k) (C := C) (top := start + n) (count := count)
        hdepth (by omega) htop hcountBound hheader hheaderAw
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

/-- `kEff = 1` exits the trim loop without reading the divisor. -/
theorem oneLengthExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {rem dividend ret m divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨5237⟩
      (⟨1⟩ :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5266⟩
      (⟨1⟩ :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc (k + 11) (C + 43) := by
  have rd5247 := GeneratedTraces.trace_5237_notTaken
    (tail := rem :: dividend :: ret :: m :: divisor :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) (by native_decide)
  have rd5266 := GeneratedTraces.trace_5247_taken
    (by simp only [List.length_cons]; omega) rd5247
    (by native_decide) (by native_decide) (by native_decide)
  have normalized := rd5266.withIndices
    (k' := k + 11) (C' := C + 43) (by omega) (by omega)
  simpa using normalized

/-- The effective single-limb divisor dispatches to the specialized division body. -/
theorem oneLengthToSingleLimb
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {rem dividend ret m divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (h : RDx runtimeBytecode ee g s0 ⟨5266⟩
      (⟨1⟩ :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6274⟩
      (⟨1⟩ :: m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc (k + 11) (C + 38) := by
  have rd6281 := GeneratedTraces.trace_5266_taken
    (tail := divisor :: tail) (by simp only [List.length_cons]; omega) h
    (by native_decide) (by native_decide) (by native_decide)
  have normalized := rd6281.withIndices
    (k' := k + 11) (C' := C + 38) (by omega) (by omega)
  simpa using normalized

/-- An effective divisor with at least two limbs proceeds to the multi-limb size check. -/
theorem multiLengthToSizeCheck
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C kEff : Nat} {tail : List UInt256}
    {rem dividend ret m divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hkEff : 2 ≤ kEff)
    (hkEffBound : kEff < UInt256.size)
    (h : RDx runtimeBytecode ee g s0 ⟨5266⟩
      (UInt256.ofNat kEff :: rem :: dividend :: ret :: m :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5280⟩
      (UInt256.ofNat kEff :: m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc (k + 11) (C + 38) := by
  have hne : UInt256.ofNat kEff ≠ ⟨1⟩ := by
    intro heq
    have hn := congrArg UInt256.toNat heq
    rw [UInt256.toNat_ofNat_of_lt hkEffBound] at hn
    have hone : (⟨1⟩ : UInt256).toNat = 1 := by native_decide
    rw [hone] at hn
    omega
  have hcondition : (UInt256.ofNat kEff).eq ⟨1⟩ = ⟨0⟩ := by
    simp [UInt256.eq, hne]
    native_decide
  have rd5280 := GeneratedTraces.trace_5266_notTaken
    (tail := divisor :: tail) (by simp only [List.length_cons]; omega) h
    (by native_decide) hcondition
  have normalized := rd5280.withIndices
    (k' := k + 11) (C' := C + 38) (by omega) (by omega)
  simpa using normalized

/-- A shorter dividend dispatches to the direct remainder-copy case. -/
theorem shorterDividend
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m kEff : Nat} {tail : List UInt256}
    {rem dividend ret divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hshort : m < kEff)
    (hmBound : m < UInt256.size)
    (hkEffBound : kEff < UInt256.size)
    (h : RDx runtimeBytecode ee g s0 ⟨5280⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6214⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc (k + 5) (C + 22) := by
  have hcondition : (UInt256.ofNat m).lt (UInt256.ofNat kEff) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hmBound,
        UInt256.toNat_ofNat_of_lt hkEffBound]
      exact hshort
  have rd6221 := GeneratedTraces.trace_5280_taken
    (tail := rem :: dividend :: ret :: divisor :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hcondition (by native_decide)
  have normalized := rd6221.withIndices
    (k' := k + 5) (C' := C + 22) (by omega) (by omega)
  simpa using normalized

/-- A dividend at least as long as the divisor enters normalized Knuth division. -/
theorem sufficientDividend
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m kEff : Nat} {tail : List UInt256}
    {rem dividend ret divisor : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hsufficient : kEff ≤ m)
    (hmBound : m < UInt256.size)
    (hkEffBound : kEff < UInt256.size)
    (h : RDx runtimeBytecode ee g s0 ⟨5280⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨5287⟩
      (UInt256.ofNat kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc (k + 5) (C + 22) := by
  have hcondition : (UInt256.ofNat m).lt (UInt256.ofNat kEff) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hmBound,
      UInt256.toNat_ofNat_of_lt hkEffBound]
    exact hsufficient
  have rd5287 := GeneratedTraces.trace_5280_notTaken
    (tail := rem :: dividend :: ret :: divisor :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hcondition
  have normalized := rd5287.withIndices
    (k' := k + 5) (C' := C + 22) (by omega) (by omega)
  simpa using normalized

end Modexp.MultiLimbSchoolbookDivisorTrim
