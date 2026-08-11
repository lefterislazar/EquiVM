import Examples.Precompiles.Modexp.MultiLimbOddBaseConversionContract

/-!
# Odd-backend branches after base comparison

This module packages the generated caller path that selects the already-reduced base and enters
the exponent classifier. The schoolbook-remainder edge is handled separately.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbOddBranch

open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exponentHeader (mem : ByteArray) (aw exponent : UInt256) : UInt256 :=
  MultiLimbOddCompare.headerWord mem aw exponent

def exponentAfter (aw exponent : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader aw exponent

def fastBranchGas (aw exponent : UInt256) : Nat :=
  61 + (Cₘ (exponentAfter aw exponent) - Cₘ aw)

/-- When `_limbsLt` returned true, retain the converted base as `a` and enter the generated
`_exponentToUint` classifier. This is PC 2051 through the branch opcode at PC 3794. -/
theorem lessToExponentClassifierExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {base modulus exponent count : UInt256}
    (hdepth : tail.length + 9 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨2051⟩
      (MultiLimbOddCompare.boolWord true :: modulus :: count :: base ::
        modulus :: count :: exponent :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3794⟩
      (⟨3930⟩ :: (exponentHeader mem aw exponent).isZero :: exponent ::
        exponentHeader mem aw exponent :: ⟨2069⟩ :: exponent ::
        modulus :: count :: base :: tail)
      mem (exponentAfter aw exponent) rdata acc (k + 19)
      (C + fastBranchGas aw exponent) := by
  have hcondition :
      (MultiLimbOddCompare.boolWord true).isZero = ⟨0⟩ := by
    native_decide
  have rd2057 := GeneratedTraces.trace_2051_notTaken
    (tail := modulus :: count :: base :: modulus :: count :: exponent :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
  have rd3794 := GeneratedTraces.trace_2057_body
    (tail := tail) (by omega) rd2057
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd3794
  have normalized := rd3794.withIndices
    (k' := k + 19) (C' := C + fastBranchGas aw exponent)
    (by omega) (by simp [fastBranchGas, exponentAfter]; omega)
  simpa only [exponentHeader, exponentAfter] using normalized

/-- When `_limbsLt` returned false, enter the `schoolbookRem(base, k, n, k)` call with the exact
caller frame intact. -/
theorem notLessToSchoolbookEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {base modulus exponent count : UInt256}
    (hdepth : tail.length + 9 ≤ 1023)
    (h : RDx runtimeBytecode ee g s0 ⟨2051⟩
      (MultiLimbOddCompare.boolWord false :: modulus :: count :: base ::
        modulus :: count :: exponent :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2279⟩
      (modulus :: count :: base :: modulus :: count :: exponent :: tail)
      mem aw rdata acc (k + 4) (C + 17) := by
  have hcondition :
      (MultiLimbOddCompare.boolWord false).isZero ≠ ⟨0⟩ := by
    native_decide
  have rd2279 := GeneratedTraces.trace_2051_taken
    (tail := modulus :: count :: base :: modulus :: count :: exponent :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
    (by native_decide)
  exact rd2279.withIndices (k' := k + 4) (C' := C + 17) (by omega) (by omega)

def compareLessSteps (mem : ByteArray) (aw first second : UInt256) (count : Nat) : Nat :=
  35 + MultiLimbOddCompare.compareSteps mem aw first second count

def compareLessGas (mem : ByteArray) (aw first second exponent : UInt256)
    (count : Nat) : Nat :=
  54 + MultiLimbOddCompare.compareGas mem aw first second count +
    fastBranchGas aw exponent

/-- Compare two concrete arrays and, when the pure comparison is true, continue through the
already-reduced-base edge into the exponent classifier. -/
theorem compareLessToExponentClassifierExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {first second exponent : UInt256}
    (hdepth : tail.length + 12 ≤ 1019)
    (hcountPositive : 0 < count)
    (hcount : count ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstHeader : MultiLimbOddCompare.headerWord mem aw first = UInt256.ofNat count)
    (hsecondHeader : MultiLimbOddCompare.headerWord mem aw second = UInt256.ofNat count)
    (hfirstRange : first.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (hsecondRange : second.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (hless : MultiLimbOddCompare.compareMemory mem aw first second count = true)
    (h : RDx runtimeBytecode ee g s0 ⟨2038⟩
      (first :: second :: UInt256.ofNat count :: exponent :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨3794⟩
      (⟨3930⟩ :: (exponentHeader mem aw exponent).isZero :: exponent ::
        exponentHeader mem aw exponent :: ⟨2069⟩ :: exponent ::
        second :: UInt256.ofNat count :: first :: tail)
      mem (exponentAfter aw exponent) rdata acc
      (k + compareLessSteps mem aw first second count)
      (C + compareLessGas mem aw first second exponent count) := by
  have rd2051 := MultiLimbOddCompare.fromCallerEntryExactOfArrayGeometry
    (tail := exponent :: tail) (by simp only [List.length_cons]; omega)
    hcountPositive hcount hawFit hfirstHeader hsecondHeader hfirstRange hsecondRange h
  rw [hless] at rd2051
  have rd3794 := lessToExponentClassifierExact (tail := tail) (by omega) rd2051
  have normalized := rd3794.withIndices
    (k' := k + compareLessSteps mem aw first second count)
    (C' := C + compareLessGas mem aw first second exponent count)
    (by simp [compareLessSteps]; omega)
    (by simp [compareLessGas]; omega)
  exact normalized

def compareNotLessSteps (mem : ByteArray) (aw first second : UInt256)
    (count : Nat) : Nat :=
  20 + MultiLimbOddCompare.compareSteps mem aw first second count

def compareNotLessGas (mem : ByteArray) (aw first second : UInt256)
    (count : Nat) : Nat :=
  71 + MultiLimbOddCompare.compareGas mem aw first second count

/-- Compare two concrete arrays and, when the pure comparison is false, enter the full
schoolbook-remainder call. -/
theorem compareNotLessToSchoolbookEntryExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C count : Nat} {tail : List UInt256}
    {first second exponent : UInt256}
    (hdepth : tail.length + 12 ≤ 1019)
    (hcountPositive : 0 < count)
    (hcount : count ≤ 32)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstHeader : MultiLimbOddCompare.headerWord mem aw first = UInt256.ofNat count)
    (hsecondHeader : MultiLimbOddCompare.headerWord mem aw second = UInt256.ofNat count)
    (hfirstRange : first.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (hsecondRange : second.toNat + 32 * (count + 1) ≤ 32 * aw.toNat)
    (hnless : MultiLimbOddCompare.compareMemory mem aw first second count = false)
    (h : RDx runtimeBytecode ee g s0 ⟨2038⟩
      (first :: second :: UInt256.ofNat count :: exponent :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2279⟩
      (second :: UInt256.ofNat count :: first :: second ::
        UInt256.ofNat count :: exponent :: tail)
      mem aw rdata acc
      (k + compareNotLessSteps mem aw first second count)
      (C + compareNotLessGas mem aw first second count) := by
  have rd2051 := MultiLimbOddCompare.fromCallerEntryExactOfArrayGeometry
    (tail := exponent :: tail) (by simp only [List.length_cons]; omega)
    hcountPositive hcount hawFit hfirstHeader hsecondHeader hfirstRange hsecondRange h
  rw [hnless] at rd2051
  have rd2279 := notLessToSchoolbookEntryExact (tail := tail) (by omega) rd2051
  have normalized := rd2279.withIndices
    (k' := k + compareNotLessSteps mem aw first second count)
    (C' := C + compareNotLessGas mem aw first second count)
    (by simp [compareNotLessSteps]; omega)
    (by simp [compareNotLessGas]; omega)
  exact normalized

end Modexp.MultiLimbOddBranch
