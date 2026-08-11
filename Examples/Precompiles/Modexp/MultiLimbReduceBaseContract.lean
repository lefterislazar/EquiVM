import Examples.Precompiles.Modexp.Allocation
import Examples.Precompiles.Modexp.MultiLimbBytesToLimbsCall
import Examples.Precompiles.Modexp.MultiLimbSchoolbookRemContract

/-!
# Barrett `reduceBase` execution contract

The direct Barrett backend cannot use the odd-modulus base-conversion shortcut: an arbitrary
base may occupy more limbs than the modulus and therefore has to be converted and divided.  This
module records that distinction explicitly.  It proves the zero-length return separately and,
for nonempty bases, follows the deployed code through the checked ceiling division, the
`max(baseK, k)` selection, `bytesToLimbs`, and the remainder allocation at the `schoolbookDiv`
entry.  Keeping this as an executable contract prevents the Barrett proof from replacing the
division by an unproved arithmetic callback.

The split in `setupSteps` and `setupGas` is genuine path-sensitive accounting: Solidity executes
an additional six-instruction assignment block exactly when `ceil(baseLen / 32) < k`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbReduceBase

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def naturalWords (baseSize : Nat) : Nat := (baseSize + 31) / 32

def baseWords (baseSize k : Nat) : Nat := max (naturalWords baseSize) k

def setupSteps (baseSize k : Nat) : Nat :=
  if naturalWords baseSize < k then 34 else 28

def setupGas (baseSize k : Nat) : Nat :=
  if naturalWords baseSize < k then 123 else 103

private theorem shiftRight_div32 {baseSize : Nat} (hbaseSize : baseSize ≤ 1024) :
    UInt256.shiftRight (UInt256.ofNat (baseSize + 31)) ⟨5⟩ =
      UInt256.ofNat (naturalWords baseSize) := by
  have hsum : baseSize + 31 < UInt256.size := by
    have hsmall : 1055 < UInt256.size := by decide
    omega
  have hwords : naturalWords baseSize < UInt256.size := by
    unfold naturalWords
    exact lt_of_le_of_lt (Nat.div_le_self (baseSize + 31) 32) hsum
  apply u256_inj
  rw [shiftRight_toNat_of_lt256 _ _ (by decide),
    UInt256.toNat_ofNat_of_lt hsum,
    show (⟨5⟩ : UInt256).toNat = 5 by decide,
    UInt256.toNat_ofNat_of_lt hwords]
  norm_num [naturalWords]

/-- Follow nonempty `reduceBase` inputs from its function entry to the selected conversion width.
The base-length header is required to be in already-active memory, as it is for the public copied
operand layout. -/
theorem nonzeroSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize k : Nat} {tail : List UInt256}
    {basePtr modulusPtr ret : UInt256}
    (hdepth : tail.length ≤ 1012)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024) (hk : k ≤ 32)
    (haccess : basePtr.toNat + 32 ≤ 32 * aw.toNat)
    (hload : wideLoadWord mem aw basePtr = UInt256.ofNat baseSize)
    (h : RDx runtimeBytecode ee g s0 ⟨2957⟩
      (basePtr :: modulusPtr :: UInt256.ofNat k :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨2995⟩
      (basePtr :: UInt256.ofNat (baseWords baseSize k) :: modulusPtr ::
        UInt256.ofNat k :: ⟨3010⟩ :: ret :: tail)
      mem aw rdata acc (steps + setupSteps baseSize k)
      (gasUsed + setupGas baseSize k) := by
  have hbaseWord : baseSize < UInt256.size :=
    lt_trans (lt_of_le_of_lt hbaseSize (by decide : 1024 < 2 ^ 64)) (by decide)
  have hkWord : k < UInt256.size :=
    lt_trans (lt_of_le_of_lt hk (by decide : 32 < 2 ^ 64)) (by decide)
  have hsumWord : baseSize + 31 < UInt256.size := by
    have hsmall : 1055 < UInt256.size := by decide
    omega
  have hwordsWord : naturalWords baseSize < UInt256.size := by
    unfold naturalWords
    exact lt_of_le_of_lt (Nat.div_le_self (baseSize + 31) 32) hsumWord
  have rd2961 := evm_run h with [jumpdest, swap2, swap1, dup3]
  have rd2962 := RDx.mloadWithin rd2961 (by native_decide) haccess
    (by simp only [List.length_cons]; omega)
  rw [hload] at rd2962
  have rd2968 := evm_run rd2962 with [
    swap3, dup4, iszero, pushCanonical 2 .PUSH2 ⟨3023⟩ (by decide)]
  have hbaseNe : UInt256.ofNat baseSize ≠ ⟨0⟩ := by
    intro hz
    have hzNat := congrArg UInt256.toNat hz
    rw [UInt256.toNat_ofNat_of_lt hbaseWord,
      show (⟨0⟩ : UInt256).toNat = 0 by decide] at hzNat
    omega
  have hnonzero : UInt256.isZero (UInt256.ofNat baseSize) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hbaseNe
  have rd2969 := rd2968.jumpiNT (by native_decide) hnonzero
    (by simp only [List.length_cons]; omega)
  have hsum : UInt256.ofNat baseSize + (⟨31⟩ : UInt256) =
      UInt256.ofNat (baseSize + 31) := by
    apply u256_inj
    rw [uadd_toNat,
      UInt256.toNat_ofNat_of_lt hbaseWord,
      show (⟨31⟩ : UInt256).toNat = 31 by decide,
      UInt256.toNat_ofNat_of_lt hsumWord,
      Nat.mod_eq_of_lt hsumWord]
  have hoverflow :
      (UInt256.ofNat baseSize).gt
        (UInt256.ofNat baseSize + (⟨31⟩ : UInt256)) = ⟨0⟩ := by
    apply ugt_zero
    rw [hsum, UInt256.toNat_ofNat_of_lt hsumWord,
      UInt256.toNat_ofNat_of_lt hbaseWord]
    omega
  have rd2979 := GeneratedTraces.trace_2969_body
    (by simp only [List.length_cons]; omega) rd2969
  have rd2980 := rd2979.jumpiNT (by native_decide) hoverflow
    (by simp only [List.length_cons]; omega)
  rw [hsum] at rd2980
  have rd2994 := GeneratedTraces.trace_2980_body
    (by simp only [List.length_cons]; omega) rd2980
  rw [shiftRight_div32 hbaseSize] at rd2994
  by_cases hreplace : naturalWords baseSize < k
  · have hcondition :
        (UInt256.ofNat (naturalWords baseSize)).lt (UInt256.ofNat k) = ⟨1⟩ := by
      apply ult_one
      rw [UInt256.toNat_ofNat_of_lt hwordsWord,
        UInt256.toNat_ofNat_of_lt hkWord]
      exact hreplace
    have rd3015 := rd2994.jumpiT (by native_decide)
      (by rw [hcondition]; native_decide) (by native_decide)
      (by simp only [List.length_cons]; omega)
    have rd2995 := evm_run rd3015 with [
      jumpdest, dup4, swap2, pop,
      pushCanonical 2 .PUSH2 ⟨2995⟩ (by decide), jump (by native_decide)]
    have normalized := rd2995.withIndices
      (k' := steps + setupSteps baseSize k)
      (C' := gasUsed + setupGas baseSize k)
      (by simp [setupSteps, hreplace]; omega)
      (by simp [setupGas, hreplace]; omega)
    simpa [baseWords, max_eq_right (Nat.le_of_lt hreplace)] using normalized
  · have hcondition :
        (UInt256.ofNat (naturalWords baseSize)).lt (UInt256.ofNat k) = ⟨0⟩ := by
      apply ult_zero
      rw [UInt256.toNat_ofNat_of_lt hwordsWord,
        UInt256.toNat_ofNat_of_lt hkWord]
      omega
    have rd2995 := rd2994.jumpiNT (by native_decide) hcondition
      (by simp only [List.length_cons]; omega)
    have normalized := rd2995.withIndices
      (k' := steps + setupSteps baseSize k)
      (C' := gasUsed + setupGas baseSize k)
      (by simp [setupSteps, hreplace]; omega)
      (by simp [setupGas, hreplace]; omega)
    have hbaseWords : baseWords baseSize k = naturalWords baseSize := by
      unfold baseWords
      exact Nat.max_eq_left (by omega)
    have normalizedPC := normalized.withPC (pc' := ⟨2995⟩) (by native_decide)
    simpa [hbaseWords] using normalizedPC

/-- Arrange the selected base width and conversion continuation at the array allocator. -/
theorem conversionAllocationSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {basePtr baseK modulusPtr k ret : UInt256}
    (hdepth : tail.length ≤ 1010)
    (h : RDx runtimeBytecode ee g s0 ⟨2995⟩
      (basePtr :: baseK :: modulusPtr :: k :: ⟨3010⟩ :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (baseK :: ⟨2847⟩ :: ⟨3005⟩ :: basePtr :: baseK ::
        modulusPtr :: k :: ⟨3010⟩ :: ret :: tail)
      mem aw rdata acc (steps + 13) (gasUsed + 45) := by
  have rd2836 := evm_run h with [
    jumpdest, dup2, pushCanonical 2 .PUSH2 ⟨3005⟩ (by decide), swap2,
    pushCanonical 2 .PUSH2 ⟨2836⟩ (by decide), jump (by native_decide)]
  have rd1487 := evm_run rd2836 with [
    jumpdest, swap2, swap1, pushCanonical 2 .PUSH2 ⟨2847⟩ (by decide), swap1,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide), jump (by native_decide)]
  exact rd1487.withIndices (k' := steps + 13) (C' := gasUsed + 45)
    (by omega) (by omega)

/-- Arrange `schoolbookDiv`'s `k`-limb remainder allocation after base conversion. -/
theorem remainderAllocationSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {baseLimbs baseK modulusPtr k ret : UInt256}
    (hdepth : tail.length ≤ 1009)
    (h : RDx runtimeBytecode ee g s0 ⟨3005⟩
      (baseLimbs :: baseK :: modulusPtr :: k :: ⟨3010⟩ :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (k :: ⟨5199⟩ :: baseK :: baseLimbs :: ⟨3010⟩ ::
        k :: modulusPtr :: ret :: tail)
      mem aw rdata acc (steps + 12) (gasUsed + 42) := by
  have rd1487 := evm_run h with [
    jumpdest, pushCanonical 2 .PUSH2 ⟨5186⟩ (by decide), jump (by native_decide),
    jumpdest, swap1, swap4, swap2, swap4,
    pushCanonical 2 .PUSH2 ⟨5199⟩ (by decide), dup5,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide), jump (by native_decide)]
  exact rd1487.withIndices (k' := steps + 12) (C' := gasUsed + 42)
    (by omega) (by omega)

def baseAllocatedMemory (mem : ByteArray) (fp baseSize k : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr mem (fp + wordArrayAllocationSize (baseWords baseSize k)))
    fp (baseWords baseSize k)

def baseAllocatedWords (aw : UInt256) (fp baseSize k : Nat) : UInt256 :=
  newWordArrayWords aw fp (baseWords baseSize k)

def convertedMemory (mem : ByteArray) (aw : UInt256)
    (fp baseSize k : Nat) (basePtr : UInt256) : ByteArray :=
  MultiLimbGenerated.bytesToLimbsMemory
    (baseAllocatedMemory mem fp baseSize k)
    (baseAllocatedWords aw fp baseSize k)
    basePtr (UInt256.ofNat fp) baseSize

def convertedWords (mem : ByteArray) (aw : UInt256)
    (fp baseSize k : Nat) (basePtr : UInt256) : UInt256 :=
  MultiLimbGenerated.bytesToLimbsActiveWords
    (baseAllocatedMemory mem fp baseSize k)
    (baseAllocatedWords aw fp baseSize k)
    basePtr (UInt256.ofNat fp) baseSize

def remainderMemory (mem : ByteArray) (aw : UInt256)
    (baseFp remFp baseSize k : Nat) (basePtr : UInt256) : ByteArray :=
  storeBytesLength
    (setFreePtr (convertedMemory mem aw baseFp baseSize k basePtr)
      (remFp + wordArrayAllocationSize k)) remFp k

def remainderWords (mem : ByteArray) (aw : UInt256)
    (baseFp remFp baseSize k : Nat) (basePtr : UInt256) : UInt256 :=
  newWordArrayWords (convertedWords mem aw baseFp baseSize k basePtr) remFp k

def nonzeroSteps (baseSize k : Nat) : Nat :=
  setupSteps baseSize k + 190 + MultiLimbGenerated.bytesToLimbsSteps baseSize

def nonzeroGas (mem : ByteArray) (aw : UInt256)
    (baseFp remFp baseSize k : Nat) (basePtr : UInt256) : Nat :=
  setupGas baseSize k + 111 +
    newWordArrayGas aw baseFp (baseWords baseSize k) +
    MultiLimbGenerated.bytesToLimbsGas
      (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k)
      basePtr (UInt256.ofNat baseFp) baseSize +
    newWordArrayGas
      (convertedWords mem aw baseFp baseSize k basePtr) remFp k

/-- Complete the nonempty `reduceBase` prefix through conversion and both allocations.  The result
is the concrete `schoolbookDiv` entry state, not an abstract remainder specification. -/
theorem nonzeroToDivisionEntry
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize k baseFp remFp : Nat} {tail : List UInt256}
    {basePtr modulusPtr ret : UInt256}
    (hdepth : tail.length ≤ 1003)
    (hbasePos : 0 < baseSize) (hbaseSize : baseSize ≤ 1024) (hk : k ≤ 32)
    (hbaseAccess : basePtr.toNat + 32 ≤ 32 * aw.toNat)
    (hbaseLoad : wideLoadWord mem aw basePtr = UInt256.ofNat baseSize)
    (hbaseFp : 96 ≤ baseFp)
    (hbaseBound : baseFp + wordArrayAllocationSize (baseWords baseSize k) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ baseFp)
    (hbaseGap : baseFp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hbaseFree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat baseFp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hbaseAccessAllocated : basePtr.toNat + 32 ≤
      32 * (baseAllocatedWords aw baseFp baseSize k).toNat)
    (hbaseLoadAllocated : wideLoadWord
      (baseAllocatedMemory mem baseFp baseSize k)
      (baseAllocatedWords aw baseFp baseSize k) basePtr = UInt256.ofNat baseSize)
    (hremFp : 96 ≤ remFp)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64)
    (hconvertedSize : 96 ≤
      (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hconvertedLe :
      (convertedMemory mem aw baseFp baseSize k basePtr).size ≤ remFp)
    (hremGap : remFp -
      (convertedMemory mem aw baseFp baseSize k basePtr).size < USize.size)
    (hconvertedAw3 : 3 ≤
      (convertedWords mem aw baseFp baseSize k basePtr).toNat)
    (hconvertedAw64 : ¬ (⟨64⟩ : UInt256) ≥
      convertedWords mem aw baseFp baseSize k basePtr * ⟨32⟩)
    (hremFree :
      (convertedMemory mem aw baseFp baseSize k basePtr).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat remFp))
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      (basePtr :: modulusPtr :: UInt256.ofNat k :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat remFp :: UInt256.ofNat (baseWords baseSize k) ::
        UInt256.ofNat baseFp :: ⟨3010⟩ :: UInt256.ofNat k ::
        modulusPtr :: ret :: tail)
      (remainderMemory mem aw baseFp remFp baseSize k basePtr)
      (remainderWords mem aw baseFp remFp baseSize k basePtr)
      rdata acc (steps + nonzeroSteps baseSize k)
      (gasUsed + nonzeroGas mem aw baseFp remFp baseSize k basePtr) := by
  have hbaseWords : baseWords baseSize k ≤ 32 := by
    unfold baseWords naturalWords
    have hceil : (baseSize + 31) / 32 ≤ 32 := by omega
    omega
  have rd2995 := nonzeroSetup (by omega) hbasePos hbaseSize hk
    hbaseAccess hbaseLoad h
  have rd1487 := conversionAllocationSetup (by omega) rd2995
  have rd2847 := newWordArrayExact
    (n := baseWords baseSize k) (fp := baseFp) (ret := 2847)
    (tail := ⟨3005⟩ :: basePtr :: UInt256.ofNat (baseWords baseSize k) ::
      modulusPtr :: UInt256.ofNat k :: ⟨3010⟩ :: ret :: tail)
    hbaseWords hbaseFp hbaseBound hmemSize hmemLe hbaseGap haw3 haw64
    hbaseFree hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have rd3005 := MultiLimbBytesToLimbsCall.postAllocatorComplete
    (dataLen := baseSize) (limbsPtr := UInt256.ofNat baseFp)
    (innerRet := ⟨3005⟩) (dataPtr := basePtr)
    (tail := UInt256.ofNat (baseWords baseSize k) :: modulusPtr ::
      UInt256.ofNat k :: ⟨3010⟩ :: ret :: tail)
    (by simp only [List.length_cons]; omega) hbaseSize hbaseAccessAllocated
    hbaseLoadAllocated (by native_decide) (by
      simpa [baseAllocatedMemory, baseAllocatedWords] using rd2847)
  have rdRem1487 := remainderAllocationSetup
    (tail := tail) (baseLimbs := UInt256.ofNat baseFp)
    (baseK := UInt256.ofNat (baseWords baseSize k))
    (modulusPtr := modulusPtr) (k := UInt256.ofNat k) (ret := ret)
    (by omega) (by
    simpa [convertedMemory, convertedWords] using rd3005)
  have rd5199 := newWordArrayExact
    (n := k) (fp := remFp) (ret := 5199)
    (tail := UInt256.ofNat (baseWords baseSize k) :: UInt256.ofNat baseFp ::
      ⟨3010⟩ :: UInt256.ofNat k :: modulusPtr :: ret :: tail)
    hk hremFp hremBound hconvertedSize hconvertedLe hremGap
    hconvertedAw3 hconvertedAw64 hremFree hcalldata
    (by simp only [List.length_cons]; omega) (by native_decide) (by
      simpa [convertedMemory, convertedWords] using rdRem1487)
  have normalized := rd5199.withIndices
    (k' := steps + nonzeroSteps baseSize k)
    (C' := gasUsed + nonzeroGas mem aw baseFp remFp baseSize k basePtr)
    (by simp [nonzeroSteps]; omega)
    (by simp [nonzeroGas]; omega)
  simpa [remainderMemory, remainderWords] using normalized

def zeroMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize k)) fp k

def zeroWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  newWordArrayWords aw fp k

def zeroGas (aw : UInt256) (fp k : Nat) : Nat :=
  71 + newWordArrayGas aw fp k

/-- The empty-base branch returns a freshly allocated zero `k`-limb array without entering
division.  This is still exact execution, including allocation and the PC 1271 return trampoline. -/
theorem zeroExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k : Nat} {tail : List UInt256}
    {basePtr modulusPtr ret : UInt256}
    (hk : k ≤ 32)
    (haccess : basePtr.toNat + 32 ≤ 32 * aw.toNat)
    (hload : wideLoadWord mem aw basePtr = ⟨0⟩)
    (hfp : 96 ≤ fp) (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1009)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2957⟩
      (basePtr :: modulusPtr :: UInt256.ofNat k :: ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.ofNat fp :: tail) (zeroMemory mem fp k) (zeroWords aw fp k)
      rdata acc (steps + 99) (gasUsed + zeroGas aw fp k) := by
  have rd2961 := evm_run h with [jumpdest, swap2, swap1, dup3]
  have rd2962 := RDx.mloadWithin rd2961 (by native_decide) haccess
    (by simp only [List.length_cons]; omega)
  rw [hload] at rd2962
  have rd2968 := evm_run rd2962 with [
    swap3, dup4, iszero, pushCanonical 2 .PUSH2 ⟨3023⟩ (by decide)]
  have rd3023 := rd2968.jumpiT (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons]; omega)
  have rd1487 := evm_run rd3023 with [
    jumpdest, pop, pop, pushCanonical 2 .PUSH2 ⟨1271⟩ (by decide),
    swap2, pop, pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide), jump (by native_decide)]
  have rd1271 := newWordArrayExact
    (n := k) (fp := fp) (ret := 1271) (tail := ret :: tail)
    hk hfp hbound hmemSize hmemLe hgap haw3 haw64 hfree hcalldata
    (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have rdret := GeneratedTraces.trace_1271_jump
    (by omega) rd1271 (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := steps + 99) (C' := gasUsed + zeroGas aw fp k)
    (by omega) (by simp [zeroGas]; omega)
  simpa [zeroMemory, zeroWords] using normalized

end Modexp.MultiLimbReduceBase
