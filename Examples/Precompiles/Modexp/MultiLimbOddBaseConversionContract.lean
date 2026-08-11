import Examples.Precompiles.Modexp.Allocation
import Examples.Precompiles.Modexp.MultiLimbGenerated
import Examples.Precompiles.Modexp.MultiLimbOddCompareContract

/-!
# Fast-path base conversion for the odd ModExp backend

This module covers PC 2029 through PC 2038: allocate a `k`-limb array and convert the base bytes
into it.  The conversion is total over all Osaka-valid base lengths, including zero and lengths
below one full word.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbOddBaseConversion

open Modexp.MultiLimbDivisionTrace
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def allocatedMemory (mem : ByteArray) (fp words : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words

def allocatedWords (aw : UInt256) (fp words : Nat) : UInt256 :=
  newWordArrayWords aw fp words

def baseLength (mem : ByteArray) (aw basePtr : UInt256) : UInt256 :=
  MultiLimbOddCompare.headerWord mem aw basePtr

def baseLengthWords (aw basePtr : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader aw basePtr

def conversionMemory (mem : ByteArray) (aw basePtr : UInt256)
    (fp baseSize : Nat) : ByteArray :=
  MultiLimbGenerated.bytesToLimbsMemory mem (baseLengthWords aw basePtr)
    basePtr (UInt256.ofNat fp) baseSize

def conversionWords (mem : ByteArray) (aw basePtr : UInt256)
    (fp baseSize : Nat) : UInt256 :=
  MultiLimbGenerated.bytesToLimbsActiveWords mem (baseLengthWords aw basePtr)
    basePtr (UInt256.ofNat fp) baseSize

def conversionSetupGas (aw basePtr : UInt256) : Nat :=
  24 + (Cₘ (baseLengthWords aw basePtr) - Cₘ aw)

def totalSteps (baseSize : Nat) : Nat :=
  99 + MultiLimbGenerated.bytesToLimbsSteps baseSize

def totalGas (mem : ByteArray) (aw basePtr : UInt256)
    (fp words baseSize : Nat) : Nat :=
  43 + newWordArrayGas aw fp words +
    conversionSetupGas (allocatedWords aw fp words) basePtr +
    MultiLimbGenerated.bytesToLimbsGas
      (allocatedMemory mem fp words)
      (baseLengthWords (allocatedWords aw fp words) basePtr)
      basePtr (UInt256.ofNat fp) baseSize

/-- Compute `ceil(baseSize / 32)` and take the `baseK ≤ k` branch. -/
theorem fastPathSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C baseSize words : Nat} {tail : List UInt256}
    {modulusPtr basePtr : UInt256}
    (hdepth : tail.length + 3 ≤ 1016)
    (hbaseSize : baseSize ≤ 1024)
    (hwords : (baseSize + 31) / 32 ≤ words)
    (hwordsBound : words ≤ 32)
    (hbaseLength : baseLength mem aw basePtr = UInt256.ofNat baseSize)
    (h : RDx runtimeBytecode ee g s0 ⟨2006⟩
      (modulusPtr :: basePtr :: UInt256.ofNat words :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2029⟩
      (modulusPtr :: UInt256.ofNat words :: basePtr :: modulusPtr ::
        UInt256.ofNat words :: tail)
      mem (baseLengthWords aw basePtr) rdata acc (k + 31)
      (C + 114 + (Cₘ (baseLengthWords aw basePtr) - Cₘ aw)) := by
  have rd1321 := GeneratedTraces.trace_2006_body hdepth h
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd1321
  have hlengthWord : MultiLimbOddCompare.headerWord mem aw basePtr =
      UInt256.ofNat baseSize := hbaseLength
  rw [hlengthWord] at rd1321
  have hsizeFit : baseSize + 31 < UInt256.size := by
    have hsmall : 1055 < UInt256.size := by decide
    omega
  have hsum : UInt256.ofNat baseSize + (⟨31⟩ : UInt256) =
      UInt256.ofNat (baseSize + 31) := by
    apply u256_inj
    rw [uadd_toNat,
      UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hbaseSize (by decide)),
      show (⟨31⟩ : UInt256).toNat = 31 by decide,
      UInt256.toNat_ofNat_of_lt hsizeFit,
      Nat.mod_eq_of_lt (by omega : baseSize + 31 < UInt256.size)]
  have hoverflow :
      (UInt256.ofNat baseSize).gt
        (UInt256.ofNat baseSize + (⟨31⟩ : UInt256)) = ⟨0⟩ := by
    apply ugt_zero
    rw [hsum, UInt256.toNat_ofNat_of_lt hsizeFit,
      UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hbaseSize (by decide))]
    omega
  have rd1322 := rd1321.jumpiNT (by native_decide) hoverflow
    (by simp only [List.length_cons]; omega)
  rw [hsum] at rd1322
  have rd1659 := GeneratedTraces.trace_1322_body
    (by simp only [List.length_cons]; omega) rd1322
  have rd1659' := rd1659.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1664 := GeneratedTraces.trace_1659_body
    (by simp only [List.length_cons]; omega) rd1659'
  have hshift : UInt256.shiftRight (UInt256.ofNat (baseSize + 31)) ⟨5⟩ =
      UInt256.ofNat ((baseSize + 31) / 32) := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt256 _ _ (by decide),
      UInt256.toNat_ofNat_of_lt hsizeFit,
      show (⟨5⟩ : UInt256).toNat = 5 by decide,
      UInt256.toNat_ofNat_of_lt (by
        have hle := Nat.div_le_self (baseSize + 31) 32
        omega)]
    norm_num
  rw [hshift] at rd1664
  have rd2023 := rd1664.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2028 := GeneratedTraces.trace_2023_body
    (by simp only [List.length_cons]; omega) rd2023
  have hbaseKFit : (baseSize + 31) / 32 < UInt256.size := by
    have hsmall : 1055 < UInt256.size := by decide
    have hle := Nat.div_le_self (baseSize + 31) 32
    omega
  have hwordsFit : words < UInt256.size := by
    have hsmall : 32 < UInt256.size := by decide
    omega
  have hcondition :
      (UInt256.ofNat words).lt (UInt256.ofNat ((baseSize + 31) / 32)) = ⟨0⟩ := by
    apply ult_zero
    rw [UInt256.toNat_ofNat_of_lt hwordsFit,
      UInt256.toNat_ofNat_of_lt hbaseKFit]
    exact hwords
  have rd2029 := rd2028.jumpiNT (by native_decide) hcondition
    (by simp only [List.length_cons]; omega)
  have normalized := rd2029.withIndices
    (k' := k + 31)
    (C' := C + 114 + (Cₘ (baseLengthWords aw basePtr) - Cₘ aw))
    (by omega) (by simp only [baseLengthWords]; omega)
  simpa only [baseLengthWords] using normalized

/-- The caller's two wrappers place `(words, 2847, 2038, basePtr)` at the allocator entry. -/
theorem allocationCallSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {baseK words basePtr : UInt256}
    (hdepth : tail.length + 3 ≤ 1018)
    (h : RDx runtimeBytecode ee g s0 ⟨2029⟩
      (baseK :: words :: basePtr :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (words :: ⟨2847⟩ :: ⟨2038⟩ :: basePtr :: tail)
      mem aw rdata acc (k + 12) (C + 43) := by
  have rd2836 := (evm_run h with [
    pop,
    pushCanonical 2 .PUSH2 ⟨0x7f6⟩ (by decide),
    swap2,
    pushCanonical 2 .PUSH2 ⟨0xb14⟩ (by decide),
    jump (by native_decide)
  ])
  have rd1487 := (evm_run rd2836 with [
    jumpdest,
    swap2,
    swap1,
    pushCanonical 2 .PUSH2 ⟨0xb1f⟩ (by decide),
    swap1,
    pushCanonical 2 .PUSH2 ⟨0x5cf⟩ (by decide),
    jump (by native_decide)
  ])
  have normalized := rd1487.withIndices
    (k' := k + 12) (C' := C + 43) (by omega) (by omega)
  exact normalized

/-- Set up the generated full-word loop after allocation returns to PC 2847. -/
theorem conversionCallSetup
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C baseSize : Nat} {tail : List UInt256}
    {basePtr limbsPtr : UInt256}
    (hdepth : tail.length + 3 ≤ 1019)
    (hbaseSize : baseSize ≤ 1024)
    (hbaseLength : baseLength mem aw basePtr = UInt256.ofNat baseSize)
    (h : RDx runtimeBytecode ee g s0 ⟨2847⟩
      (limbsPtr :: ⟨2038⟩ :: basePtr :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨2857⟩
      (MultiLimbGenerated.fullWordLoopStack ⟨0⟩
        (UInt256.ofNat (baseSize / 32)) basePtr (UInt256.ofNat baseSize)
        ⟨2038⟩ limbsPtr tail)
      mem (baseLengthWords aw basePtr) rdata acc (k + 9)
      (C + conversionSetupGas aw basePtr) := by
  have rd := (evm_run h with [
    jumpdest,
    swap2,
    dup1,
    mloadCanonical,
    swap1,
    dup2,
    pushCanonical 1 .PUSH1 ⟨0x5⟩ (by decide),
    shr,
    push0
  ])
  rw [← MultiLimbOddCompare.afterHeader_generated,
    ← MultiLimbOddCompare.headerWord_generated] at rd
  have hlengthWord : MultiLimbOddCompare.headerWord mem aw basePtr =
      UInt256.ofNat baseSize := hbaseLength
  have hfull : UInt256.shiftRight (UInt256.ofNat baseSize) ⟨5⟩ =
      UInt256.ofNat (baseSize / 32) := by
    apply u256_inj
    rw [shiftRight_toNat_of_lt256 _ _ (by decide),
      UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt hbaseSize (by decide)),
      show (⟨5⟩ : UInt256).toNat = 5 by decide,
      UInt256.toNat_ofNat_of_lt (by
        have hsmall : 1024 < UInt256.size := by decide
        have hle := Nat.div_le_self baseSize 32
        omega)]
    norm_num
  rw [hlengthWord, hfull] at rd
  have normalized := rd.withIndices
    (k' := k + 9) (C' := C + conversionSetupGas aw basePtr)
    (by omega) (by simp [conversionSetupGas, baseLengthWords]; omega)
  simpa only [MultiLimbGenerated.fullWordLoopStack, baseLengthWords] using normalized

/-- Exact allocation and conversion from the fast-path branch to the comparison call site. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp words baseSize : Nat} {tail : List UInt256}
    {junk basePtr : UInt256}
    (hwords : words ≤ 32)
    (hbaseSize : baseSize ≤ 1024)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1008)
    (hbaseLength : baseLength (allocatedMemory mem fp words)
      (allocatedWords aw fp words) basePtr = UInt256.ofNat baseSize)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2029⟩
      (junk :: UInt256.ofNat words ::
        basePtr :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2038⟩
      (UInt256.ofNat fp :: tail)
      (conversionMemory (allocatedMemory mem fp words)
        (allocatedWords aw fp words) basePtr fp baseSize)
      (conversionWords (allocatedMemory mem fp words)
        (allocatedWords aw fp words) basePtr fp baseSize)
      rdata acc (k + totalSteps baseSize)
      (C + totalGas mem aw basePtr fp words baseSize) := by
  have rd1487 := allocationCallSetup (by omega) h
  have hret2847 : (D_J runtimeBytecode 0).contains ⟨2847⟩ = true := by
    native_decide
  have rd2847 := newWordArrayExact hwords hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    hret2847 rd1487
  have rd2857 := conversionCallSetup (by omega) hbaseSize hbaseLength rd2847
  have hret2038 : (D_J runtimeBytecode 0).contains ⟨2038⟩ = true := by
    native_decide
  have rd2038 := MultiLimbGenerated.bytesToLimbsTotalOfNat
    (by omega) hbaseSize hret2038 rd2857
  have normalized := rd2038.withIndices
    (k' := k + totalSteps baseSize) (C' := C + totalGas mem aw basePtr fp words baseSize)
    (by simp [totalSteps]; omega)
    (by simp [totalGas, conversionSetupGas]; omega)
  simpa only [conversionMemory, conversionWords] using normalized

def fullSteps (baseSize : Nat) : Nat :=
  31 + totalSteps baseSize

def fullGas (mem : ByteArray) (aw basePtr : UInt256)
    (fp words baseSize : Nat) : Nat :=
  114 + (Cₘ (baseLengthWords aw basePtr) - Cₘ aw) +
    totalGas mem (baseLengthWords aw basePtr) basePtr fp words baseSize

/-- Exact fast-path base preparation from the converted-modulus boundary at PC 2006 through the
comparison call site at PC 2038. -/
theorem fromConvertedModulusExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp words baseSize : Nat} {tail : List UInt256}
    {modulusPtr basePtr : UInt256}
    (hwords : words ≤ 32)
    (hbaseSize : baseSize ≤ 1024)
    (hfast : (baseSize + 31) / 32 ≤ words)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ (baseLengthWords aw basePtr).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ baseLengthWords aw basePtr * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1003)
    (hbaseLength : baseLength mem aw basePtr = UInt256.ofNat baseSize)
    (hbaseLengthAllocated :
      baseLength (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words) basePtr =
          UInt256.ofNat baseSize)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2006⟩
      (modulusPtr :: basePtr :: UInt256.ofNat words :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2038⟩
      (UInt256.ofNat fp :: modulusPtr :: UInt256.ofNat words :: tail)
      (conversionMemory (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      (conversionWords (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      rdata acc (k + fullSteps baseSize)
      (C + fullGas mem aw basePtr fp words baseSize) := by
  have rd2029 := fastPathSetup (by omega) hbaseSize hfast hwords
    hbaseLength h
  have rd2038 := exact
    (mem := mem) (aw := baseLengthWords aw basePtr)
    (fp := fp) (words := words) (baseSize := baseSize)
    (tail := modulusPtr :: UInt256.ofNat words :: tail)
    hwords hbaseSize hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega)
    hbaseLengthAllocated rd2029
  have normalized := rd2038.withIndices
    (k' := k + fullSteps baseSize)
    (C' := C + fullGas mem aw basePtr fp words baseSize)
    (by simp [fullSteps]; omega)
    (by simp [fullGas]; omega)
  exact normalized

def throughCompareSteps (mem : ByteArray) (aw basePtr modulusPtr : UInt256)
    (fp words baseSize : Nat) : Nat :=
  fullSteps baseSize + 16 +
    MultiLimbOddCompare.compareSteps
      (conversionMemory (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      (conversionWords (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      (UInt256.ofNat fp) modulusPtr words

def throughCompareGas (mem : ByteArray) (aw basePtr modulusPtr : UInt256)
    (fp words baseSize : Nat) : Nat :=
  fullGas mem aw basePtr fp words baseSize + 54 +
    MultiLimbOddCompare.compareGas
      (conversionMemory (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      (conversionWords (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      (UInt256.ofNat fp) modulusPtr words

/-- Exact base preparation and comparison from PC 2006 through PC 2051. The comparison coverage
premises are stated only as concrete properties of the fully computed conversion state. -/
theorem fromConvertedModulusThroughCompareExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp words baseSize : Nat} {tail : List UInt256}
    {modulusPtr basePtr : UInt256}
    (hwordsPositive : 0 < words)
    (hwords : words ≤ 32)
    (hbaseSize : baseSize ≤ 1024)
    (hfast : (baseSize + 31) / 32 ≤ words)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ (baseLengthWords aw basePtr).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ baseLengthWords aw basePtr * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1003)
    (hbaseLength : baseLength mem aw basePtr = UInt256.ofNat baseSize)
    (hbaseLengthAllocated :
      baseLength (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words) basePtr =
          UInt256.ofNat baseSize)
    (hawFit :
      (conversionWords (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize).toNat * 32 < UInt256.size)
    (hbaseHeader :
      MultiLimbOddCompare.headerWord
        (conversionMemory (allocatedMemory mem fp words)
          (allocatedWords (baseLengthWords aw basePtr) fp words)
          basePtr fp baseSize)
        (conversionWords (allocatedMemory mem fp words)
          (allocatedWords (baseLengthWords aw basePtr) fp words)
          basePtr fp baseSize)
        (UInt256.ofNat fp) = UInt256.ofNat words)
    (hmodulusHeader :
      MultiLimbOddCompare.headerWord
        (conversionMemory (allocatedMemory mem fp words)
          (allocatedWords (baseLengthWords aw basePtr) fp words)
          basePtr fp baseSize)
        (conversionWords (allocatedMemory mem fp words)
          (allocatedWords (baseLengthWords aw basePtr) fp words)
          basePtr fp baseSize)
        modulusPtr = UInt256.ofNat words)
    (hbaseRange :
      (UInt256.ofNat fp).toNat + 32 * (words + 1) ≤
        32 * (conversionWords (allocatedMemory mem fp words)
          (allocatedWords (baseLengthWords aw basePtr) fp words)
          basePtr fp baseSize).toNat)
    (hmodulusRange :
      modulusPtr.toNat + 32 * (words + 1) ≤
        32 * (conversionWords (allocatedMemory mem fp words)
          (allocatedWords (baseLengthWords aw basePtr) fp words)
          basePtr fp baseSize).toNat)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2006⟩
      (modulusPtr :: basePtr :: UInt256.ofNat words :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2051⟩
      (MultiLimbOddCompare.boolWord
          (MultiLimbOddCompare.compareMemory
            (conversionMemory (allocatedMemory mem fp words)
              (allocatedWords (baseLengthWords aw basePtr) fp words)
              basePtr fp baseSize)
            (conversionWords (allocatedMemory mem fp words)
              (allocatedWords (baseLengthWords aw basePtr) fp words)
              basePtr fp baseSize)
            (UInt256.ofNat fp) modulusPtr words) ::
        modulusPtr :: UInt256.ofNat words :: UInt256.ofNat fp ::
        modulusPtr :: UInt256.ofNat words :: tail)
      (conversionMemory (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      (conversionWords (allocatedMemory mem fp words)
        (allocatedWords (baseLengthWords aw basePtr) fp words)
        basePtr fp baseSize)
      rdata acc (k + throughCompareSteps mem aw basePtr modulusPtr fp words baseSize)
      (C + throughCompareGas mem aw basePtr modulusPtr fp words baseSize) := by
  have rd2038 := fromConvertedModulusExact hwords hbaseSize hfast hfp hbound
    hmemSize hmemLe hgap haw3 haw64 hread hcalldata htail hbaseLength
    hbaseLengthAllocated h
  have rd2051 := MultiLimbOddCompare.fromCallerEntryExactOfArrayGeometry
    (tail := tail) (by omega) hwordsPositive hwords hawFit
    hbaseHeader hmodulusHeader hbaseRange hmodulusRange rd2038
  have normalized := rd2051.withIndices
    (k' := k + throughCompareSteps mem aw basePtr modulusPtr fp words baseSize)
    (C' := C + throughCompareGas mem aw basePtr modulusPtr fp words baseSize)
    (by simp [throughCompareSteps]; omega)
    (by simp [throughCompareGas]; omega)
  exact normalized

end Modexp.MultiLimbOddBaseConversion
