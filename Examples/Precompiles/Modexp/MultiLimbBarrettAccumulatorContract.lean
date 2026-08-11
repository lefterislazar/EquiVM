import Examples.Precompiles.Modexp.MultiLimbBarrettContinuationExecutable
import Examples.Precompiles.Modexp.MultiLimbBarrettExponentSemantic

/-!
# Barrett accumulator setup

After `_computeBarrettConstant` returns at PC 1718, the deployed caller allocates the `k`-limb
accumulator, stores one in its low limb, and enters `_barrettModexpLoop` at PC 3154. This file
keeps that short caller segment executable: the array header and active-memory facts are derived
from the concrete allocator result, and the exact path cost includes the checked element access.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettAccumulator

open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryCIOSSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def allocatedMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize k)) fp k

def allocatedWords (aw : UInt256) (fp k : Nat) : UInt256 :=
  newWordArrayWords aw fp k

def initializedMemory (mem : ByteArray) (fp k : Nat) : ByteArray :=
  (UInt256.toByteArray (⟨1⟩ : UInt256)).write 0 (allocatedMemory mem fp k) (fp + 32) 32

def setupGas (aw : UInt256) (fp k : Nat) : Nat :=
  newWordArrayGas aw fp k + 97

/-- The allocator materializes only the array header; its zero payload remains represented by EVM
padding until the caller writes the first limb. -/
theorem allocatedMemory_size
    (mem : ByteArray) (fp k : Nat)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size) :
    (allocatedMemory mem fp k).size = fp + 32 := by
  unfold allocatedMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hmemSize]
    exact hmemLe
  · rw [setFreePtr_size hmemSize]
    exact hgap

/-- Initializing `r[0]` extends concrete memory by exactly one word. -/
theorem initializedMemory_size
    (mem : ByteArray) (fp k : Nat)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size) :
    (initializedMemory mem fp k).size = fp + 64 := by
  unfold initializedMemory
  rw [toByteArray_write_size_eq_max]
  · rw [allocatedMemory_size mem fp k hmemSize hmemLe hgap]
    omega
  · rw [allocatedMemory_size mem fp k hmemSize hmemLe hgap]
    simpa using lt_usize 0 (by omega)

/-- The first initialized payload word reads back as one. -/
theorem initializedMemory_firstWord
    (mem : ByteArray) (fp k : Nat)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size) :
    Modexp.MultiLimbMemoryModel.memoryWordNat (initializedMemory mem fp k) (fp + 32) = 1 := by
  unfold initializedMemory Modexp.MultiLimbMemoryModel.memoryWordNat
  rw [toByteArray_write32_read_back]
  · exact fromByteArrayBigEndian_toByteArray (⟨1⟩ : UInt256)
  · rw [allocatedMemory_size mem fp k hmemSize hmemLe hgap]

/-- The complete initialized payload is one followed by the allocator's implicit zero limbs. -/
theorem initializedMemory_words
    (mem : ByteArray) (fp k : Nat)
    (hkPos : 0 < k)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size) :
    memoryWordsFrom (initializedMemory mem fp k) (fp + 32) k =
      (⟨1⟩ : UInt256) :: List.replicate (k - 1) (⟨0⟩ : UInt256) := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [memoryWordsFrom, Nat.add_sub_cancel]
  rw [initializedMemory_firstWord mem fp (rest + 1) hmemSize hmemLe hgap]
  have hpast : (initializedMemory mem fp (rest + 1)).size <= fp + 32 + 32 := by
    rw [initializedMemory_size mem fp (rest + 1) hmemSize hmemLe hgap]
  rw [Modexp.MultiLimbSchoolbookMulTrace.memoryWordsFrom_past_end_zero _ _ _ hpast]
  rfl

/-- The concrete caller initialization gives the persistent accumulator the exact natural value
`1` for every positive limb count. -/
theorem initializedMemory_value
    (mem : ByteArray) (fp k : Nat)
    (hkPos : 0 < k) (hfpFit : fp + 32 < UInt256.size)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size) :
    Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
      (UInt256.ofNat fp) (initializedMemory mem fp k) = 1 := by
  unfold Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue
  rw [uadd_word_lit32_toNat (UInt256.ofNat fp) (by
      rw [UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size)]
      exact hfpFit),
    UInt256.toNat_ofNat_of_lt (by omega : fp < UInt256.size),
    initializedMemory_words mem fp k hkPos hmemSize hmemLe hgap]
  simp [Modexp.wordLimbsToNat, Modexp.wordLimbsToNat_replicate_zero,
    show (⟨1⟩ : UInt256).toNat = 1 by decide]

/-- Initializing the first limb does not alter the accumulator's array header. -/
theorem initializedMemory_header
    (mem : ByteArray) (fp k : Nat)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size) :
    (initializedMemory mem fp k).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
  unfold initializedMemory
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by rw [allocatedMemory_size mem fp k hmemSize hmemLe hgap]) (by omega)]
  unfold allocatedMemory
  apply storeBytesLength_read_self
  rw [setFreePtr_size hmemSize]
  exact hgap

/-- The accumulator allocation exposes its updated Solidity free-memory pointer at `0x40`. -/
theorem initializedMemory_freePointer
    (mem : ByteArray) (fp k : Nat)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size) (hfp : 96 ≤ fp) :
    (initializedMemory mem fp k).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat (fp + wordArrayAllocationSize k)) := by
  unfold initializedMemory
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by rw [allocatedMemory_size mem fp k hmemSize hmemLe hgap]) (by omega)]
  unfold allocatedMemory
  rw [storeBytesLength_read64 (by rw [setFreePtr_size hmemSize]; omega) hfp
    (by rw [setFreePtr_size hmemSize]; exact hgap)]
  exact setFreePtr_read64 hmemSize

/-- Array allocation and `r[0] = 1` preserve every padded word wholly below the accumulator
pointer. -/
theorem initializedMemory_read_below
    (mem : ByteArray) (fp k read : Nat)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size)
    (hread : 96 <= read) (hbelow : read + 32 <= fp) :
    (initializedMemory mem fp k).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  unfold initializedMemory
  rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
    (by rw [allocatedMemory_size mem fp k hmemSize hmemLe hgap]) (by omega)]
  unfold allocatedMemory
  rw [storeBytesLength_read_below_padded (by
      rw [setFreePtr_size hmemSize]
      omega) hbelow (by
      rw [setFreePtr_size hmemSize]
      exact hgap)]
  exact setFreePtr_read_above_padded hmemSize hread

/-- The allocator preserves an arbitrary persistent limb range ending below the new accumulator. -/
theorem initializedMemory_words_below
    (mem : ByteArray) (fp k ptr words : Nat)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size)
    (hptr : 96 <= ptr) (hbelow : ptr + 32 * words <= fp) :
    memoryWordsFrom (initializedMemory mem fp k) ptr words =
      memoryWordsFrom mem ptr words := by
  induction words generalizing ptr with
  | zero => rfl
  | succ words ih =>
      simp only [memoryWordsFrom]
      rw [show Modexp.MultiLimbMemoryModel.memoryWordNat
            (initializedMemory mem fp k) ptr =
          Modexp.MultiLimbMemoryModel.memoryWordNat mem ptr by
        unfold Modexp.MultiLimbMemoryModel.memoryWordNat
        rw [initializedMemory_read_below mem fp k ptr hmemSize hmemLe hgap hptr (by omega)]]
      congr 1
      exact ih (ptr + 32) (by omega) (by omega)

/-- The active-word result of the allocator covers the initialized accumulator and remains an
exactly representable EVM byte extent. -/
theorem initializedMemory_coverage
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hkPos : 0 < k)
    (hmemSize : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size) :
    MemoryCovered (initializedMemory mem fp k) (allocatedWords aw fp k) /\
      (allocatedWords aw fp k).toNat * 32 < UInt256.size := by
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp k hkPos
    hawFit hfit
  change fp + 32 + 32 * k <= 32 * (allocatedWords aw fp k).toNat /\
    (allocatedWords aw fp k).toNat * 32 < UInt256.size at hrange
  constructor
  · unfold MemoryCovered
    rw [initializedMemory_size mem fp k hmemSize hmemLe hgap]
    omega
  · exact hrange.2

/-- The array returned by the concrete allocator exposes its stored `k` header through the same
guarded `MLOAD` expression used by the generated checked-index helper. -/
theorem allocatedHeader
    (mem : ByteArray) (aw : UInt256) (fp k : Nat)
    (hkPos : 0 < k) (hk : k ≤ 32)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size) :
    MultiLimbOddCompare.headerWord (allocatedMemory mem fp k) (allocatedWords aw fp k)
      (UInt256.ofNat fp) = UInt256.ofNat k := by
  have hfpWord : fp < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp k hkPos
    hawFit hfit
  change fp + 32 + 32 * k ≤ 32 * (allocatedWords aw fp k).toNat ∧
    (allocatedWords aw fp k).toNat * 32 < UInt256.size at hrange
  have hsetSize : (setFreePtr mem (fp + wordArrayAllocationSize k)).size = mem.size :=
    setFreePtr_size hmemSize
  have hallocatedSize : (allocatedMemory mem fp k).size = fp + 32 := by
    unfold allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rw [hsetSize]
      exact hgap
  have hread : (allocatedMemory mem fp k).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat k) := by
    unfold allocatedMemory
    apply storeBytesLength_read_self
    rw [hsetSize]
    exact hgap
  have hactive :
      ¬ (UInt256.ofNat fp) ≥ allocatedWords aw fp k * (⟨32⟩ : UInt256) := by
    intro hge
    have hawMul :
        (allocatedWords aw fp k * (⟨32⟩ : UInt256)).toNat =
          (allocatedWords aw fp k).toNat * 32 := by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 by decide] using
        umul_toNat (a := allocatedWords aw fp k) (b := (⟨32⟩ : UInt256)) hrange.2
    have hgeNat :
        (allocatedWords aw fp k * (⟨32⟩ : UInt256)).toNat ≤
          (UInt256.ofNat fp).toNat := hge
    rw [hawMul, UInt256.toNat_ofNat_of_lt hfpWord] at hgeNat
    omega
  unfold MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [if_neg]
  · rw [UInt256.toNat_ofNat_of_lt hfpWord, hread, fromByteArrayBigEndian_toByteArray]
    exact u256_ofNat_toNat (UInt256.ofNat k)
  · rw [UInt256.toNat_ofNat_of_lt hfpWord, hallocatedSize]
    exact not_or.mpr ⟨by omega, hactive⟩

/-- Execute the real allocation, checked `r[0]` access, initialization store, and dynamic call to
the Barrett exponent loop. The caller continuation below `k` is left untouched. -/
theorem setupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp k : Nat} {tail : List UInt256}
    {mu exponent modulus baseReduced : UInt256}
    (hkTwo : 2 ≤ k) (hk : k ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize k < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 1008)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1718⟩
      (mu :: exponent :: modulus :: baseReduced :: UInt256.ofNat k :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3154⟩
      (UInt256.ofNat fp :: baseReduced :: exponent :: modulus :: mu :: UInt256.ofNat k :: tail)
      (initializedMemory mem fp k) (allocatedWords aw fp k) rdata acc
      (steps + 104) (gasUsed + setupGas aw fp k) := by
  have hkPos : 0 < k := by omega
  have hkWord : k < UInt256.size := lt_of_le_of_lt hk (by native_decide)
  have hfpWord : fp < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hfp32Word : fp + 32 < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hfit
    omega
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp k hkPos
    hawFit hfit
  change fp + 32 + 32 * k ≤ 32 * (allocatedWords aw fp k).toNat ∧
    (allocatedWords aw fp k).toNat * 32 < UInt256.size at hrange
  have rd1487 := evm_run h with [
    jumpdest,
    swap3,
    push2 ⟨1728⟩,
    dup6,
    push2 ⟨1487⟩,
    jump (by native_decide)]
  have rd1728 := newWordArrayExact hk hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have hheader := allocatedHeader mem aw fp k hkPos hk hmemSize hmemLe hgap
    hawFit hfit
  have hcondition :
      (MultiLimbOddCompare.headerWord (allocatedMemory mem fp k)
        (allocatedWords aw fp k) (UInt256.ofNat fp)).isZero = ⟨0⟩ := by
    rw [hheader, isZero_eq_zero_of_ne]
    intro hkZero
    have hnat := congrArg UInt256.toNat hkZero
    rw [UInt256.toNat_ofNat_of_lt hkWord] at hnat
    simp at hnat
    omega
  have hconditionRaw :
      (if (UInt256.ofNat fp).toNat ≥ (allocatedMemory mem fp k).size ∨
          UInt256.ofNat fp ≥ allocatedWords aw fp k * ⟨32⟩ then
        (⟨0⟩ : UInt256)
      else
        UInt256.ofNat (fromByteArrayBigEndian
          ((allocatedMemory mem fp k).readWithPadding (UInt256.ofNat fp).toNat 32))).isZero =
        ⟨0⟩ := by
    rw [← MultiLimbOddCompare.headerWord_generated]
    exact hcondition
  have rd1524 := GeneratedTraces.trace_1728_notTaken
    (tail := baseReduced :: exponent :: modulus :: mu :: UInt256.ofNat k :: tail)
    (by simp only [List.length_cons]; omega)
    (by simpa [allocatedMemory, allocatedWords] using rd1728)
    (by native_decide) hconditionRaw
  have hfp32 : UInt256.ofNat fp + ⟨32⟩ = UInt256.ofNat (fp + 32) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨32⟩ : UInt256).toNat = 32 by decide,
      UInt256.toNat_ofNat_of_lt hfp32Word, Nat.mod_eq_of_lt hfp32Word]
  have rd1739raw := GeneratedTraces.trace_1524_jump
    (tail := (⟨1⟩ : UInt256) :: UInt256.ofNat fp :: baseReduced :: exponent :: modulus ::
      mu :: UInt256.ofNat k :: tail)
    (by simp only [List.length_cons]; omega) rd1524
    (by native_decide) (by native_decide)
  rw [u256_add_comm (⟨32⟩ : UInt256) (UInt256.ofNat fp), hfp32] at rd1739raw
  have hloadAw :
      UInt256.ofNat (MachineState.M (allocatedWords aw fp k).toNat fp 32) =
        allocatedWords aw fp k := by
    rw [machineM_eq_of_access]
    · exact u256_ofNat_toNat (allocatedWords aw fp k)
    · exact le_trans (by omega : fp + 32 ≤ fp + 32 + 32 * k) hrange.1
  rw [UInt256.toNat_ofNat_of_lt hfpWord, hloadAw] at rd1739raw
  have hstoreAw :
      UInt256.ofNat (MachineState.M (allocatedWords aw fp k).toNat (fp + 32) 32) =
        allocatedWords aw fp k := by
    rw [machineM_eq_of_access]
    · exact u256_ofNat_toNat (allocatedWords aw fp k)
    · exact le_trans (by omega : fp + 32 + 32 ≤ fp + 32 + 32 * k) hrange.1
  have rd1740 := evm_run rd1739raw with [jumpdest]
  have rd1741 := RDx.mstore 0 (initializedMemory mem fp k) (allocatedWords aw fp k)
    rd1740 (by native_decide)
    (by
      intro s hsaw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
        UInt256.toNat_ofNat_of_lt hfp32Word, hstoreAw])
    (by simp [initializedMemory, UInt256.toNat_ofNat_of_lt hfp32Word])
    (by rw [UInt256.toNat_ofNat_of_lt hfp32Word, hstoreAw])
    (by simp only [List.length_cons]; omega)
  have rd3154 := evm_run rd1741 with [
    push2 ⟨3154⟩,
    jump (by native_decide)]
  have normalized := rd3154.withIndices (k' := steps + 104) (by omega)
    (C' := gasUsed + setupGas aw fp k) (by
      unfold setupGas
      omega)
  simpa [initializedMemory, allocatedMemory, allocatedWords] using normalized

end Modexp.MultiLimbBarrettAccumulator
