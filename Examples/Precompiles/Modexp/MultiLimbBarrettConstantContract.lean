import Examples.Precompiles.Modexp.MultiLimbBarrettReduceBaseContract
import Examples.Precompiles.Modexp.MultiLimbOddConversionSemantic

/-!
# Barrett-constant setup

This module returns from `reduceBase` and executes the checked computation
`dLen = 2 * k + 1` at the start of `_computeBarrettConstant`. SymCheck independently measured the
PC 3010 return trampoline as five steps/17 gas and exposed the two overflow guards in the PC 1707
to PC 3094 prefix.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettConstant

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def dividendLength (k : Nat) : Nat := 2 * k + 1

def dividendMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr mem (fp + wordArrayAllocationSize (dividendLength k))) fp
    (dividendLength k)

def dividendWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  newWordArrayWords aw fp (dividendLength k)

def dividendHighAddress (fp k : Nat) : UInt256 :=
  MultiLimbOddCompare.elementPtr (UInt256.ofNat fp) (UInt256.ofNat (2 * k))

def storedDividendMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  UInt256.toByteArray ⟨1⟩ |>.write 0 (dividendMemory mem fp k)
    (dividendHighAddress fp k).toNat 32

def remainderPtr (fp k : Nat) : Nat :=
  fp + wordArrayAllocationSize (dividendLength k)

def barrettDivisionMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr (storedDividendMemory mem fp k)
      (remainderPtr fp k + wordArrayAllocationSize k))
    (remainderPtr fp k) k

def barrettDivisionWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  newWordArrayWords (dividendWords aw fp k) (remainderPtr fp k) k

/-- The last payload word is exactly element `2*k` of the `2*k+1`-word dividend. -/
theorem dividendHighAddress_toNat (fp k : Nat)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (dividendHighAddress fp k).toNat = fp + 32 * (2 * k + 1) := by
  have hfpWord : fp < UInt256.size := by
    unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have haddressFit :
      (UInt256.ofNat fp).toNat + 32 * (2 * k + 1) < UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord]
    unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  unfold dividendHighAddress
  rw [MultiLimbOddCompare.elementPtr_ofNat_toNat_of_fit _ _ haddressFit,
    UInt256.toNat_ofNat_of_lt hfpWord]

theorem dividendMemory_size (mem : ByteArray) (fp k : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) :
    (dividendMemory mem fp k).size = fp + 32 := by
  unfold dividendMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- The high-word store makes the complete first allocation concrete up to its free pointer. -/
theorem storedDividendMemory_size (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (storedDividendMemory mem fp k).size =
      fp + wordArrayAllocationSize (dividendLength k) := by
  have hbaseSize := dividendMemory_size mem fp k hmemSize hmemLe hgap
  have haddress := dividendHighAddress_toNat fp k hfit
  have hwriteGap :
      (dividendHighAddress fp k).toNat - (dividendMemory mem fp k).size <
        USize.size := by
    rw [haddress, hbaseSize]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hsize := MultiLimbMontgomeryCIOSSemantic.toByteArray_write_size_eq_max
    (⟨1⟩ : UInt256) (dividendMemory mem fp k) (dividendHighAddress fp k).toNat
    hwriteGap
  unfold storedDividendMemory
  rw [haddress, hbaseSize] at hsize
  rw [haddress]
  rw [hsize]
  unfold wordArrayAllocationSize wordArrayPayloadSize dividendLength
  simp only [max_eq_right (by omega : fp + 32 ≤ fp + 32 * (2 * k + 1) + 32)]
  omega

/-- The high payload store is above Solidity's free-memory-pointer word. -/
theorem storedDividendMemory_read64 (mem : ByteArray) (fp k : Nat)
    (hk : k ≤ 32) (hfp : 96 ≤ fp) (hmemSize : 96 ≤ mem.size)
    (hmemLe : mem.size ≤ fp) (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    (storedDividendMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray
        (UInt256.ofNat (fp + wordArrayAllocationSize (dividendLength k))) := by
  have hbaseSize := dividendMemory_size mem fp k hmemSize hmemLe hgap
  have haddress := dividendHighAddress_toNat fp k hfit
  have hwriteGap :
      (dividendHighAddress fp k).toNat - (dividendMemory mem fp k).size <
        USize.size := by
    rw [haddress, hbaseSize]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hbelow : 64 + 32 ≤ (dividendHighAddress fp k).toNat := by
    rw [haddress]
    omega
  unfold storedDividendMemory
  rw [toByteArray_write_read_below_padded_of_gap (⟨1⟩ : UInt256)
    (dividendMemory mem fp k) (dividendHighAddress fp k).toNat 64
    (by rw [hbaseSize]; omega) hbelow hwriteGap]
  unfold dividendMemory
  rw [storeBytesLength_read64 (by rw [setFreePtr_size hmemSize]; omega) hfp
    (by rw [setFreePtr_size hmemSize]; exact hgap)]
  exact setFreePtr_read64 hmemSize

/-- Allocating and materializing the Barrett numerator preserves every complete source word
above Solidity's reserved prefix and below the fresh allocation. -/
theorem storedDividendMemory_read_below_fp (mem : ByteArray) (fp k read : Nat)
    (hk : k ≤ 32) (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hread96 : 96 ≤ read) (hreadBelow : read + 32 ≤ fp) :
    (storedDividendMemory mem fp k).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  have hbaseSize := dividendMemory_size mem fp k hmemSize hmemLe hgap
  have haddress := dividendHighAddress_toNat fp k hfit
  have hwriteGap :
      (dividendHighAddress fp k).toNat - (dividendMemory mem fp k).size <
        USize.size := by
    rw [haddress, hbaseSize]
    have husize : 2048 < USize.size := by native_decide
    omega
  have hbelowHigh : read + 32 ≤ (dividendHighAddress fp k).toNat := by
    rw [haddress]
    omega
  unfold storedDividendMemory
  rw [toByteArray_write_read_below_padded_of_gap (⟨1⟩ : UInt256)
    (dividendMemory mem fp k) (dividendHighAddress fp k).toNat read
    (by rw [hbaseSize]; omega) hbelowHigh hwriteGap]
  unfold dividendMemory
  rw [storeBytesLength_read_below_padded
    (by rw [setFreePtr_size hmemSize]; omega) hreadBelow
    (by rw [setFreePtr_size hmemSize]; exact hgap)]
  exact setFreePtr_read_above_padded hmemSize hread96

/-- The allocator materializes the declared Barrett dividend length at its returned pointer. -/
theorem dividendHeader
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hk : k ≤ 32) (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size) :
    MultiLimbOddCompare.headerWord (dividendMemory mem fp k)
      (dividendWords aw fp k) (UInt256.ofNat fp) =
        UInt256.ofNat (dividendLength k) := by
  have hfpWord : fp < UInt256.size := by
    unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (dividendLength k) (by unfold dividendLength; omega) hawFit hfit
  have hsize : (dividendMemory mem fp k).size = fp + 32 := by
    unfold dividendMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size hmemSize]
      exact hmemLe
    · rw [setFreePtr_size hmemSize]
      exact hgap
  have hactive : ¬ UInt256.ofNat fp ≥ dividendWords aw fp k * ⟨32⟩ := by
    exact MultiLimbMontgomeryCIOSSemantic.wordBelowActive_of_covered
      (dividendMemory mem fp k) (dividendWords aw fp k) (UInt256.ofNat fp)
      (by
        unfold MultiLimbMontgomeryCIOSSemantic.MemoryCovered dividendWords
        rw [hsize]
        omega)
      hrange.2 (by rw [UInt256.toNat_ofNat_of_lt hfpWord, hsize])
  unfold MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [if_neg (not_or.mpr ⟨by rw [UInt256.toNat_ofNat_of_lt hfpWord, hsize]; omega,
    hactive⟩)]
  rw [UInt256.toNat_ofNat_of_lt hfpWord]
  have hself :
      (dividendMemory mem fp k).readWithPadding fp 32 =
        UInt256.toByteArray (UInt256.ofNat (dividendLength k)) := by
    unfold dividendMemory
    apply storeBytesLength_read_self
    rw [setFreePtr_size hmemSize]
    exact hgap
  rw [hself, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- Check the last dividend index and compute the concrete address of element `2*k`. -/
theorem dividendHighAddressExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k fp : Nat} {tail : List UInt256}
    {modulus : UInt256}
    (hk : k ≤ 32) (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hdepth : tail.length ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨3111⟩
      (UInt256.ofNat fp :: ⟨3118⟩ :: ⟨1⟩ :: UInt256.ofNat (2 * k) ::
        UInt256.ofNat (dividendLength k) :: modulus :: UInt256.ofNat k ::
        ⟨3124⟩ :: tail)
      (dividendMemory mem fp k) (dividendWords aw fp k) rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3118⟩
      (dividendHighAddress fp k :: ⟨1⟩ :: UInt256.ofNat fp ::
        UInt256.ofNat (dividendLength k) :: modulus :: UInt256.ofNat k ::
        ⟨3124⟩ :: tail)
      (dividendMemory mem fp k) (dividendWords aw fp k) rdata acc
      (steps + 21) (gasUsed + 76) := by
  have hfpWord : fp < UInt256.size := by
    unfold dividendLength wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (dividendLength k) (by unfold dividendLength; omega) hawFit hfit
  have hloadAw :
      UInt256.ofNat
          (MachineState.M (dividendWords aw fp k).toNat
            (UInt256.ofNat fp).toNat 32) = dividendWords aw fp k := by
    rw [UInt256.toNat_ofNat_of_lt hfpWord,
      machineM_eq_of_access (by unfold dividendWords; omega), u256_ofNat_toNat]
  have hheader := dividendHeader mem aw fp k hk hmemSize hmemLe hgap hawFit hfit
  have rd1538 := GeneratedTraces.trace_3111_body
    (tail := UInt256.ofNat (dividendLength k) :: modulus :: UInt256.ofNat k ::
      ⟨3124⟩ :: tail) (by simp only [List.length_cons]; omega) h
  rw [← MultiLimbOddCompare.headerWord_generated, hheader, hloadAw] at rd1538
  have hdoubleWord : 2 * k < UInt256.size := by
    apply lt_of_le_of_lt (by omega : 2 * k ≤ 64) (by native_decide)
  have hlengthWord : dividendLength k < UInt256.size := by
    unfold dividendLength
    apply lt_of_le_of_lt (by omega : 2 * k + 1 ≤ 65) (by native_decide)
  have hlt : UInt256.ofNat (2 * k) < UInt256.ofNat (dividendLength k) := by
    change (UInt256.ofNat (2 * k)).toNat <
      (UInt256.ofNat (dividendLength k)).toNat
    rw [UInt256.toNat_ofNat_of_lt hdoubleWord,
      UInt256.toNat_ofNat_of_lt hlengthWord]
    unfold dividendLength
    omega
  have hcondition :
      ((UInt256.ofNat (2 * k)).lt (UInt256.ofNat (dividendLength k))).isZero =
        ⟨0⟩ := by
    rw [ult_one hlt]
    native_decide
  rw [hcondition] at rd1538
  have rd1539 := rd1538.jumpiNT (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1539' := rd1539.withPC (pc' := ⟨1539⟩) (by native_decide)
  have rd3118 := GeneratedTraces.trace_1539_jump
    (tail := ⟨1⟩ :: UInt256.ofNat fp :: UInt256.ofNat (dividendLength k) ::
      modulus :: UInt256.ofNat k :: ⟨3124⟩ :: tail)
    (by simp only [List.length_cons]; omega) rd1539'
    (by native_decide) (by native_decide)
  exact rd3118.withIndices (by omega) (by simp; omega)

/-- Store the sole nonzero word of `B^(2*k)` and set up the `k`-word remainder allocation. -/
theorem storeHighAndRemainderSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k fp : Nat} {tail : List UInt256}
    {modulus : UInt256}
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hdepth : tail.length ≤ 1012)
    (h : RDx runtimeBytecode ee g s0 ⟨3118⟩
      (dividendHighAddress fp k :: ⟨1⟩ :: UInt256.ofNat fp ::
        UInt256.ofNat (dividendLength k) :: modulus :: UInt256.ofNat k ::
        ⟨3124⟩ :: tail)
      (dividendMemory mem fp k) (dividendWords aw fp k) rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (UInt256.ofNat k :: ⟨5199⟩ :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat fp :: ⟨3124⟩ :: UInt256.ofNat k :: modulus :: tail)
      (storedDividendMemory mem fp k) (dividendWords aw fp k) rdata acc
      (steps + 13) (gasUsed + 45) := by
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (dividendLength k) (by unfold dividendLength; omega) hawFit hfit
  have haddress := dividendHighAddress_toNat fp k hfit
  have hstoreAw :
      UInt256.ofNat
          (MachineState.M (dividendWords aw fp k).toNat
            (dividendHighAddress fp k).toNat 32) = dividendWords aw fp k := by
    rw [machineM_eq_of_access]
    · exact u256_ofNat_toNat (dividendWords aw fp k)
    · calc
        (dividendHighAddress fp k).toNat + 32 =
            fp + 32 * (2 * k + 1) + 32 := by rw [haddress]
        _ = fp + 32 + 32 * dividendLength k := by
          unfold dividendLength
          omega
        _ ≤ 32 * (dividendWords aw fp k).toNat := by
          exact hrange.1
  have rd3119 := evm_run h with [jumpdest]
  have rd3120 := RDx.mstore 0 (storedDividendMemory mem fp k)
    (dividendWords aw fp k) rd3119 (by native_decide)
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk, hstoreAw])
    (by rfl) hstoreAw (by simp only [List.length_cons]; omega)
  have rd := evm_run rd3120 with [
    push2 ⟨5186⟩,
    jump (by native_decide),
    jumpdest,
    swap1,
    swap4,
    swap2,
    swap4,
    push2 ⟨5199⟩,
    dup5,
    push2 ⟨1487⟩,
    jump (by native_decide)]
  exact rd.withIndices (by omega) (by omega)

/-- Allocate the schoolbook remainder and expose its exact division-entry stack. -/
theorem remainderAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k fp : Nat} {tail : List UInt256}
    {modulus : UInt256}
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfirstFit : fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size)
    (hbound : remainderPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 1009)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
      (UInt256.ofNat k :: ⟨5199⟩ :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat fp :: ⟨3124⟩ :: UInt256.ofNat k :: modulus :: tail)
      (storedDividendMemory mem fp k) (dividendWords aw fp k)
      rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat (remainderPtr fp k) :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat fp :: ⟨3124⟩ :: UInt256.ofNat k :: modulus :: tail)
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      rdata acc (steps + 78)
      (gasUsed + newWordArrayGas (dividendWords aw fp k) (remainderPtr fp k) k) := by
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp
    (dividendLength k) (by unfold dividendLength; omega) hawFit hfirstFit
  have hstoredSize := storedDividendMemory_size mem fp k hk hmemSize hmemLe hgap
    hfirstFit
  have hstoredRead := storedDividendMemory_read64 mem fp k hk hfp hmemSize hmemLe
    hgap hfirstFit
  have haw3 : 3 ≤ (dividendWords aw fp k).toNat := by
    unfold dividendWords
    have hcoverage := hrange.1
    omega
  have hmul :
      (dividendWords aw fp k * (⟨32⟩ : UInt256)).toNat =
        (dividendWords aw fp k).toNat * 32 := by
    simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
      umul_toNat (a := dividendWords aw fp k) (b := (⟨32⟩ : UInt256)) hrange.2
  have haw64 : ¬ (⟨64⟩ : UInt256) ≥ dividendWords aw fp k * ⟨32⟩ := by
    intro hge
    have hgeNat :
        (dividendWords aw fp k * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa using hge
    rw [hmul] at hgeNat
    have hcoverage := hrange.1
    omega
  have rd5199 := newWordArrayExact (n := k) (fp := remainderPtr fp k) (ret := 5199)
    hk (by dsimp [remainderPtr]; omega) hbound
    (by rw [hstoredSize]; omega)
    (by rw [hstoredSize]; rfl)
    (by rw [hstoredSize]; simp [remainderPtr])
    haw3 haw64 hstoredRead hcalldata
    (by simp only [List.length_cons]; omega) (by native_decide) h
  simpa only [barrettDivisionMemory, barrettDivisionWords] using rd5199


/-- Discard `schoolbookDiv`'s unused quotient pointer and return the concrete remainder from
`reduceBase`. -/
theorem divisionReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {remainder discarded modulus : UInt256}
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨3010⟩
      (remainder :: discarded :: ⟨1707⟩ :: modulus :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1707⟩
      (remainder :: modulus :: tail)
      mem aw rdata acc (steps + 5) (gasUsed + 17) := by
  have rd := evm_run h with [
    jumpdest,
    swap1,
    pop,
    swap1,
    jump (by native_decide)]
  exact rd.withIndices (by omega) (by omega)

/-- Discard schoolbook division's remainder and return its quotient as the Barrett constant. -/
theorem constantReturnExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed ret : Nat} {tail : List UInt256}
    {remainder quotient : UInt256}
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨3124⟩
      (remainder :: quotient :: UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (quotient :: tail) mem aw rdata acc (steps + 4) (gasUsed + 14) := by
  have rd := GeneratedTraces.trace_3124_jump
    (tail := tail) (by omega) h
    (by native_decide) hret
  exact rd.withIndices (by omega) (by omega)

/-- Enter `_computeBarrettConstant` and form its exact `2*k+1`-word dividend length, taking both
checked-arithmetic non-revert edges. -/
theorem lengthExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k : Nat} {tail : List UInt256}
    {baseReduced modulus exponent : UInt256}
    (hk : k ≤ 32)
    (hdepth : tail.length ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨1707⟩
      (baseReduced :: modulus :: exponent :: UInt256.ofNat k :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3094⟩
      (UInt256.ofNat (2 * k + 1) :: modulus :: UInt256.ofNat k ::
        UInt256.ofNat (2 * k) :: ⟨1718⟩ :: exponent :: modulus :: baseReduced ::
        UInt256.ofNat k :: tail)
      mem aw rdata acc (steps + 28) (gasUsed + 99) := by
  have hkWord : k < UInt256.size := lt_of_le_of_lt hk (by native_decide)
  have hdoubleWord : 2 * k < UInt256.size :=
    lt_of_le_of_lt (by omega : 2 * k ≤ 64) (by native_decide)
  have hlengthWord : 2 * k + 1 < UInt256.size :=
    lt_of_le_of_lt (by omega : 2 * k + 1 ≤ 65) (by native_decide)
  have hmask :
      UInt256.land (UInt256.ofNat k)
          ⟨0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff⟩ =
        UInt256.ofNat k := by
    interval_cases k <;> native_decide
  have hshift : UInt256.shiftLeft (UInt256.ofNat k) ⟨1⟩ =
      UInt256.ofNat (2 * k) := by
    apply u256_inj
    change ((UInt256.ofNat k).shiftLeft (UInt256.ofNat 1)).toNat = _
    rw [ushl_ofNat_toNat (UInt256.ofNat k) 1 (by omega), Nat.shiftLeft_eq,
      UInt256.toNat_ofNat_of_lt hkWord, UInt256.toNat_ofNat_of_lt hdoubleWord]
    rw [Nat.mod_eq_of_lt (by simpa [Nat.mul_comm] using hdoubleWord)]
    omega
  have rd3082 := GeneratedTraces.trace_1707_body
    (tail := tail) (by omega) h
  rw [hmask, u256_sub_self, hshift] at rd3082
  have rd3083 := rd3082.jumpiNT (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd : UInt256.ofNat (2 * k) + ⟨1⟩ = UInt256.ofNat (2 * k + 1) := by
    simpa using ofNat_add_bounded hlengthWord
  have hguard : UInt256.gt (UInt256.ofNat (2 * k))
      (UInt256.ofNat (2 * k + 1)) = ⟨0⟩ := by
    apply ugt_zero
    rw [UInt256.toNat_ofNat_of_lt hdoubleWord,
      UInt256.toNat_ofNat_of_lt hlengthWord]
    omega
  have rd3093 := GeneratedTraces.trace_3083_body
    (tail := ⟨1718⟩ :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: tail)
    (by simp only [List.length_cons]; omega) rd3083
  rw [hadd, hguard] at rd3093
  have rd3094 := rd3093.jumpiNT (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact rd3094.withIndices (by omega) (by omega)

/-- Arrange the `2*k+1` dividend allocation and its two post-allocation store continuations. -/
theorem dividendAllocationSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k : Nat} {tail : List UInt256}
    {modulus : UInt256}
    (hdepth : tail.length ≤ 1010)
    (h : RDx runtimeBytecode ee g s0 ⟨3094⟩
      (UInt256.ofNat (2 * k + 1) :: modulus :: UInt256.ofNat k ::
        UInt256.ofNat (2 * k) :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨1487⟩
      (UInt256.ofNat (2 * k + 1) :: ⟨3111⟩ :: ⟨3118⟩ :: ⟨1⟩ ::
        UInt256.ofNat (2 * k) :: UInt256.ofNat (2 * k + 1) :: modulus ::
        UInt256.ofNat k :: ⟨3124⟩ :: tail)
      mem aw rdata acc (steps + 8) (gasUsed + 29) := by
  have rd := evm_run h with [
    push2 ⟨3124⟩,
    swap4,
    push1 ⟨1⟩,
    push2 ⟨3118⟩,
    push2 ⟨3111⟩,
    dup5,
    push2 ⟨1487⟩,
    jump (by native_decide)]
  exact rd.withIndices (by omega) (by omega)

/-- Allocate the full `2*k+1`-word dividend used to represent `B^(2*k)`. -/
theorem dividendAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k fp : Nat} {tail : List UInt256}
    {modulus : UInt256}
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (2 * k + 1) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 1007)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3094⟩
      (UInt256.ofNat (2 * k + 1) :: modulus :: UInt256.ofNat k ::
        UInt256.ofNat (2 * k) :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3111⟩
      (UInt256.ofNat fp :: ⟨3118⟩ :: ⟨1⟩ :: UInt256.ofNat (2 * k) ::
        UInt256.ofNat (2 * k + 1) :: modulus :: UInt256.ofNat k :: ⟨3124⟩ :: tail)
      (storeBytesLength
        (setFreePtr mem (fp + wordArrayAllocationSize (2 * k + 1))) fp (2 * k + 1))
      (newWordArrayWords aw fp (2 * k + 1)) rdata acc
      (steps + 86) (gasUsed + 29 + newWordArrayGas aw fp (2 * k + 1)) := by
  have rd1487 := dividendAllocationSetupExact (k := k) (modulus := modulus)
    (by omega) h
  have rd3111 := newWordArrayExact65 (n := 2 * k + 1) (fp := fp) (ret := 3111)
    (by omega) hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
    (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  exact rd3111.withIndices (by omega) (by omega)

/-- Complete Barrett-constant setup, exposing the call to the verified schoolbook divider. -/
theorem divisionEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k fp : Nat} {tail : List UInt256}
    {modulus : UInt256}
    (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hfirstBound : fp + wordArrayAllocationSize (dividendLength k) < 2 ^ 64)
    (hsecondBound : remainderPtr fp k + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 1007)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3094⟩
      (UInt256.ofNat (dividendLength k) :: modulus :: UInt256.ofNat k ::
        UInt256.ofNat (2 * k) :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5199⟩
      (UInt256.ofNat (remainderPtr fp k) :: UInt256.ofNat (dividendLength k) ::
        UInt256.ofNat fp :: ⟨3124⟩ :: UInt256.ofNat k :: modulus :: tail)
      (barrettDivisionMemory mem fp k) (barrettDivisionWords aw fp k)
      rdata acc (steps + 198)
      (gasUsed + 150 + newWordArrayGas aw fp (dividendLength k) +
        newWordArrayGas (dividendWords aw fp k) (remainderPtr fp k) k) := by
  have hfirstFit :
      fp + wordArrayAllocationSize (dividendLength k) + 31 < UInt256.size := by
    have h64 : 2 ^ 64 + 31 < UInt256.size := by native_decide
    omega
  have rd3111 := dividendAllocationExact (k := k) (fp := fp) (modulus := modulus)
    hk hfp hfirstBound hmemSize hmemLe hgap haw3 haw64 hread hcalldata hdepth h
  have rd3118 := dividendHighAddressExact (k := k) (fp := fp) (modulus := modulus)
    hk hmemSize hmemLe hgap hawFit hfirstFit (by omega) rd3111
  have rd1487 := storeHighAndRemainderSetupExact (k := k) (fp := fp)
    (modulus := modulus) hawFit hfirstFit (by omega) rd3118
  have rd5199 := remainderAllocationExact (k := k) (fp := fp) (modulus := modulus)
    hk hfp hmemSize hmemLe hgap hawFit hfirstFit hsecondBound hcalldata
    (by omega) rd1487
  simpa only [dividendLength] using
    rd5199.withIndices (by omega) (by omega)

/-- The schoolbook return followed by the checked Barrett-constant length setup. -/
theorem divisionReturnToLengthExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed k : Nat} {tail : List UInt256}
    {baseReduced discarded modulus exponent : UInt256}
    (hk : k ≤ 32)
    (hdepth : tail.length ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨3010⟩
      (baseReduced :: discarded :: ⟨1707⟩ :: modulus :: exponent ::
        UInt256.ofNat k :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3094⟩
      (UInt256.ofNat (2 * k + 1) :: modulus :: UInt256.ofNat k ::
        UInt256.ofNat (2 * k) :: ⟨1718⟩ :: exponent :: modulus :: baseReduced ::
        UInt256.ofNat k :: tail)
      mem aw rdata acc (steps + 33) (gasUsed + 116) := by
  have rd1707 := divisionReturnExact (tail := exponent :: UInt256.ofNat k :: tail)
    (by simp only [List.length_cons]; omega) h
  have rd3094 := lengthExact hk hdepth rd1707
  exact rd3094.withIndices (by omega) (by omega)

end Modexp.MultiLimbBarrettConstant
