import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthPrefixContract

/-!
# Knuth setup memory semantics

The generated setup contract exposes Solidity's `MCOPY` as `ByteArray.write`. This module proves
that each copied destination limb is the corresponding source limb, including overlapping ranges:
`ByteArray.write` reads from the original source snapshot, matching EIP-5656.
-/

open Ethereum Reasoning.Theory

namespace Modexp.MultiLimbSchoolbookKnuthSetupSemantic

open MultiLimbSchoolbookKnuthSetup

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- A generated Solidity word-array allocation preserves every padded word below its new header.
This is the memory-frame fact needed for the quotient and normalized-dividend allocations that
precede the Knuth `MCOPY`. -/
theorem allocatedWordArray_read_below
    (mem : ByteArray) (fp words read : Nat)
    (hmemSize : 96 ≤ mem.size) (hgap : fp - mem.size < USize.size) (hread : 96 ≤ read)
    (hbelow : read + 32 ≤ fp) :
    (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
      ).readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hsetSize :
      (setFreePtr mem (fp + wordArrayAllocationSize words)).size = mem.size :=
    setFreePtr_size hmemSize
  rw [storeBytesLength_read_below_padded]
  · exact setFreePtr_read_above_padded hmemSize hread
  · rw [hsetSize]
    omega
  · exact hbelow
  · rwa [hsetSize]

private theorem write_read_window_from
    (src base : ByteArray) (srcAddr destAddr totalLen start len : Nat)
    (htotal : totalLen ≠ 0) (hsrc : srcAddr + totalLen ≤ src.size)
    (hdest : destAddr ≤ base.size) (hwindow : start + len ≤ totalLen)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr totalLen).readWithPadding (destAddr + start) len =
      src.extract (srcAddr + start) (srcAddr + start + len) := by
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsource : (src.extract srcAddr (srcAddr + totalLen)).size = totalLen := by
    rw [ByteArray.size_extract]
    omega
  by_cases hin : destAddr + totalLen ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr totalLen htotal hsrc hin]
    rw [readWithPadding_eq_extract' _ (destAddr + start) len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsource]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hprefix, hsource]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show destAddr + start - destAddr = start by omega,
      show destAddr + start + len - destAddr = start + len by omega]
    rw [extract_extract_BA]
    congr 1
    all_goals omega
  · have hext : base.size < destAddr + totalLen := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend_from src base srcAddr destAddr totalLen htotal hsrc hdest hext]
    rw [readWithPadding_eq_extract' _ (destAddr + start) len hpos hlen64 (by
      rw [ByteArray.size_append, hprefix, hsource]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show destAddr + start - destAddr = start by omega,
      show destAddr + start + len - destAddr = start + len by omega]
    rw [extract_extract_BA]
    congr 1
    all_goals omega

/-- One complete word copied by the deployed Knuth-setup `MCOPY` is byte-for-byte the
corresponding dividend word. -/
theorem copiedUMemory_read_word
    (mem : ByteArray) (fp dividend m i : Nat)
    (hmPos : 0 < m) (hi : i < m)
    (hsource : dividend + 32 + 32 * m ≤ mem.size)
    (hdest : fp + 32 ≤ mem.size) :
    (copiedUMemory mem fp dividend m).readWithPadding (fp + 32 + 32 * i) 32 =
      mem.readWithPadding (dividend + 32 + 32 * i) 32 := by
  unfold copiedUMemory
  rw [show fp + 32 + 32 * i = fp + 32 + (32 * i) by omega]
  rw [write_read_window_from mem mem (dividend + 32) (fp + 32) (32 * m)
    (32 * i) 32 (by omega) (by omega) hdest (by omega) (by omega) (by norm_num)]
  rw [readWithPadding_eq_extract' mem (dividend + 32 + 32 * i) 32 (by omega)
    (by norm_num) (by omega)]

end Modexp.MultiLimbSchoolbookKnuthSetupSemantic
