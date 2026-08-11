import Examples.Precompiles.Modexp.MultiLimbReduceBaseContract
import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortSemantic
import Examples.Precompiles.Modexp.MultiLimbOddConversionSemantic

/-!
# `reduceBase` short-branch allocation semantics

The remainder array is allocated before `schoolbookDiv`, but its zero payload initially exists as
EVM padding beyond the concrete byte array. The short branch's later quotient allocation extends
memory across that payload. This file proves that all `k` remainder words are still zero at the
copy-loop entry from the concrete nested allocator geometry.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbReduceBaseShortSemantic

open MultiLimbReduceBase
open MultiLimbSchoolbookShort
open MultiLimbSchoolbookShortSemantic

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The concrete remainder allocation has only materialized its header; its payload remains
implicit EVM zero padding until a later allocation crosses it. -/
theorem remainderMemory_size
    (mem : ByteArray) (aw : UInt256) (baseFp remFp baseSize k : Nat)
    (basePtr : UInt256)
    (hconvertedSize : 96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hconvertedLe : (convertedMemory mem aw baseFp baseSize k basePtr).size ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size <
      USize.size) :
    (remainderMemory mem aw baseFp remFp baseSize k basePtr).size = remFp + 32 := by
  unfold remainderMemory
  apply storeBytesLength_size
  · rw [setFreePtr_size hconvertedSize]
    exact hconvertedLe
  · rw [setFreePtr_size hconvertedSize]
    exact hremGap

/-- After the one-word quotient allocation, every word of the earlier `k`-word remainder is zero.
No value premise is used: the result follows from the two allocator extents. -/
theorem remainderWords_zero_after_short_allocation
    (mem : ByteArray) (aw : UInt256) (baseFp remFp baseSize k : Nat)
    (basePtr : UInt256)
    (hkPos : 0 < k) (hk : k ≤ 32) (hremFp : 96 ≤ remFp)
    (hremBound : remFp + wordArrayAllocationSize k < 2 ^ 64)
    (hconvertedSize : 96 ≤ (convertedMemory mem aw baseFp baseSize k basePtr).size)
    (hconvertedLe : (convertedMemory mem aw baseFp baseSize k basePtr).size ≤ remFp)
    (hremGap : remFp - (convertedMemory mem aw baseFp baseSize k basePtr).size <
      USize.size)
    (hremainderAwFit :
      (remainderWords mem aw baseFp remFp baseSize k basePtr).toNat * 32 < UInt256.size)
    (hquotientBound :
      remFp + wordArrayAllocationSize k + wordArrayAllocationSize 1 < 2 ^ 64) :
    ∀ i, i < k ->
      arrayWord
          (shortAllocatedMemory (remainderMemory mem aw baseFp remFp baseSize k basePtr)
            (remFp + wordArrayAllocationSize k))
          (shortAllocatedWords (remainderWords mem aw baseFp remFp baseSize k basePtr)
            (remFp + wordArrayAllocationSize k))
          (UInt256.ofNat remFp) i = ⟨0⟩ := by
  intro i hi
  let remMem := remainderMemory mem aw baseFp remFp baseSize k basePtr
  let remAw := remainderWords mem aw baseFp remFp baseSize k basePtr
  let quotientFp := remFp + wordArrayAllocationSize k
  have hremMemSize : remMem.size = remFp + 32 := by
    exact remainderMemory_size mem aw baseFp remFp baseSize k basePtr hconvertedSize
      hconvertedLe hremGap
  have hremFpWord : remFp < UInt256.size := by
    exact lt_trans (by omega : remFp < 2 ^ 64) (by decide)
  have haddressFit : remFp + 32 * (i + 1) < UInt256.size := by
    unfold wordArrayAllocationSize wordArrayPayloadSize at hremBound
    exact lt_trans (by omega : remFp + 32 * (i + 1) < 2 ^ 64) (by decide)
  have haddress :
      (arrayAddress (UInt256.ofNat remFp) i).toNat = remFp + 32 * (i + 1) := by
    unfold arrayAddress
    rw [MultiLimbOddCompare.elementPtr_ofNat_toNat (UInt256.ofNat remFp) i (by omega) (by
      rw [UInt256.toNat_ofNat_of_lt hremFpWord]
      exact haddressFit)]
    rw [UInt256.toNat_ofNat_of_lt hremFpWord]
  have hquotientFit : quotientFp + wordArrayAllocationSize 1 + 31 < UInt256.size := by
    have hbound64 : quotientFp + wordArrayAllocationSize 1 < 2 ^ 64 := by
      exact hquotientBound
    have h64 : 2 ^ 64 + 31 < UInt256.size := by
      norm_num [UInt256.size]
    omega
  have hshortRange := MultiLimbOddConversionSemantic.newWordArrayWords_range remAw quotientFp 1
    (by omega) hremainderAwFit hquotientFit
  apply shortAllocatedMemory_arrayWord_zero remMem remAw (UInt256.ofNat remFp) quotientFp i
  · rw [hremMemSize]
    omega
  · rw [hremMemSize]
    unfold quotientFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [hremMemSize]
    unfold quotientFp wordArrayAllocationSize wordArrayPayloadSize
    exact lt_usize _ (by omega)
  · exact hshortRange.2
  · rw [haddress]
    omega
  · rw [hremMemSize, haddress]
    omega
  · rw [haddress]
    unfold quotientFp wordArrayAllocationSize wordArrayPayloadSize
    omega
  · rw [haddress]
    have := hshortRange.1
    unfold shortAllocatedWords quotientFp wordArrayAllocationSize wordArrayPayloadSize at this ⊢
    omega

end Modexp.MultiLimbReduceBaseShortSemantic
