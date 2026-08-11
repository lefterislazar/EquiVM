import Examples.Precompiles.Modexp.BarrettSpec
import Examples.Precompiles.Modexp.MultiLimbBarrettComposition
import Examples.Precompiles.Modexp.MultiLimbBarrettResultSemantic

/-!
# Normalized multi-limb Barrett composition

This module composes the leading-zero normalization/re-entry path with the complete multi-limb
Barrett selector.  The first bridge below identifies the PC 1808 restore copy with left-padding
the normalized fixed-width result back to the original modulus width.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettNormalizedComposition

open Modexp.MultiLimbBarrettComposition
open Modexp.MultiLimbBarrettConstant
open Modexp.MultiLimbBarrettConstantSemantic
open Modexp.MultiLimbBarrettConstantComplete
open Modexp.MultiLimbBarrettAccumulator

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

private theorem barrettReturnDecodesNormalizedComposition :
    [decode runtimeBytecode ⟨1271⟩, decode runtimeBytecode ⟨1272⟩,
      decode runtimeBytecode ⟨1273⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_wrapper173NormalizedComposition :
    (D_J runtimeBytecode 0).contains (UInt256.ofNat 173) = true := by
  native_decide

/-- Removing the zero prefix identified by the deployed Barrett scan preserves the modulus value.
The proof uses the scan recurrence itself for every skipped byte and the guarded EVM load semantics
to identify those bytes with the trusted padded-byte model. -/
theorem normalizedSuffix_value_eq_original
    {mem : ByteArray} {aw : UInt256} {p m : Nat}
    (hm : 0 < m)
    (hpend256 : p + m + 31 < UInt256.size)
    (hpend64 : p + m + 31 < 2 ^ 64)
    (hactiveEnd : p + m + 31 + 32 <= 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    Model.bytesToNatPadded mem (p + barrettNormalizedOffset mem aw p m)
        (barrettNormalizedLen mem aw p m) =
      Model.bytesToNatPadded mem (p + 32) m := by
  let prefixLen := barrettNormalizedOffset mem aw p m - 32
  let len := barrettNormalizedLen mem aw p m
  have hsplitLen : prefixLen + len = m := by
    dsimp only [prefixLen, len]
    exact barrettNormalizedSkippedPrefix_add_len mem aw p m hm
  have hstopBounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p m) (barrettScanStart p) (by
      unfold barrettScanStart barrettScanEnd
      omega)
  have hstopUpper : barrettScanStop mem aw p m <= p + m + 31 := by
    simpa [barrettScanStop, barrettScanEnd] using hstopBounds.2
  have hstopLower : p + 32 <= barrettScanStop mem aw p m := by
    simpa [barrettScanStop, barrettScanStart] using hstopBounds.1
  have hawMul : (aw * (UInt256.ofNat 32)).toNat = 32 * aw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      simpa [Nat.mul_comm] using hawFit
  have hprefixZero : Model.bytesToNatPadded mem (p + 32) prefixLen = 0 := by
    apply model_bytesToNatPadded_eq_zero_of_bytes
    intro i hi
    have hcurStop : p + 32 + i < barrettScanStop mem aw p m := by
      dsimp only [prefixLen, barrettNormalizedOffset] at hi
      omega
    have hscanZero : barrettScanByteAt mem aw (p + 32 + i) = UInt256.ofNat 0 := by
      simpa [barrettScanStop, barrettScanStart] using
        barrettScanStopAt_zero_before mem aw
          (barrettScanEnd p m) (barrettScanStart p) (p + 32 + i)
          (by simp [barrettScanStart])
          (by simpa [barrettScanStop] using hcurStop)
    have hcur256 : p + 32 + i < UInt256.size := by
      exact lt_of_lt_of_le (lt_of_lt_of_le hcurStop hstopUpper) hpend256.le
    have hcur64 : p + 32 + i < 2 ^ 64 := by
      exact lt_of_lt_of_le (lt_of_lt_of_le hcurStop hstopUpper) hpend64.le
    have hguard : ¬ (UInt256.ofNat (p + 32 + i) >= aw * UInt256.ofNat 32) := by
      intro h
      change (aw * UInt256.ofNat 32).toNat <=
        (UInt256.ofNat (p + 32 + i)).toNat at h
      rw [hawMul, UInt256.toNat_ofNat_of_lt hcur256] at h
      omega
    have hbyteModel := barrettScanByteAt_toNat_eq_model
      (mem := mem) (aw := aw) hcur256 hcur64 hguard
    have hzeroNat : (barrettScanByteAt mem aw (p + 32 + i)).toNat = 0 := by
      rw [hscanZero]
      rfl
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hbyteModel.symm.trans hzeroNat
  have hsplit := model_bytesToNatPadded_split mem (p + 32) prefixLen len
  rw [hsplitLen, hprefixZero] at hsplit
  simp only [zero_mul, zero_add] at hsplit
  have hstart : p + 32 + prefixLen = p + barrettNormalizedOffset mem aw p m := by
    change p + 32 + (barrettScanStop mem aw p m - p - 32) =
      p + (barrettScanStop mem aw p m - p)
    omega
  rw [<- hstart]
  exact hsplit.symm

/-- An in-bounds slice is preserved when every 32-byte window beginning inside it is preserved.
The overlapping form matches the fixed-word frame exported by the Barrett exponent loop. -/
theorem readWithPadding_eq_of_wordFrames
    (left right : ByteArray) (start len : Nat)
    (hend64 : start + len < 2 ^ 64)
    (hleftIn : start + len ≤ left.size)
    (hrightIn : start + len ≤ right.size)
    (hframes : ∀ i, i < len →
      left.readWithPadding (start + i) 32 = right.readWithPadding (start + i) 32) :
    left.readWithPadding start len = right.readWithPadding start len := by
  induction len generalizing start with
  | zero => rw [byteArray_readWithPadding_zero, byteArray_readWithPadding_zero]
  | succ len ih =>
      have hstart64 : start < 2 ^ 64 := by omega
      have hfirstFrame := hframes 0 (by omega)
      have hfirst : left.readWithPadding start 1 = right.readWithPadding start 1 := by
        calc
          left.readWithPadding start 1 =
              (left.readWithPadding start 32).extract 0 1 := by
                symm
                exact readWithPadding_window left start 32 0 1 hstart64 (by decide)
                  (by simpa using hstart64) (by decide) (by decide)
          _ = (right.readWithPadding start 32).extract 0 1 := by
                exact congrArg (fun bs : ByteArray => bs.extract 0 1) (by simpa using hfirstFrame)
          _ = right.readWithPadding start 1 := by
                exact readWithPadding_window right start 32 0 1 hstart64 (by decide)
                  (by simpa using hstart64) (by decide) (by decide)
      cases len with
      | zero => simpa using hfirst
      | succ rest =>
          have hrestLen64 : rest + 1 < 2 ^ 64 := by omega
          have hsum64 : 1 + (rest + 1) < 2 ^ 64 := by omega
          have hlenEq : rest + 1 + 1 = 1 + (rest + 1) := by omega
          rw [hlenEq]
          rw [byteArray_readWithPadding_split left start 1 (rest + 1) (by decide)
              (by omega) (by decide) hrestLen64 hsum64 (by omega),
            byteArray_readWithPadding_split right start 1 (rest + 1) (by decide)
              (by omega) (by decide) hrestLen64 hsum64 (by omega), hfirst]
          congr 1
          apply ih (start := start + 1)
          · omega
          · omega
          · omega
          · intro i hi
            have hframe := hframes (i + 1) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hframe

/-- If the original result prefix is zero and the temporary normalized payload is the trusted
fixed-width encoding, the real PC 1808 `MCOPY` reconstructs that encoding at the original width. -/
theorem restoreMemory_bytes_eq_natToBytes
    {mem : ByteArray} {temp result offset len width value : Nat}
    (hlen : 0 < len)
    (hoffset : 32 ≤ offset)
    (hwidth : offset - 32 + len = width)
    (hwidth64 : width < 2 ^ 64)
    (hsrc : temp + 32 + len ≤ mem.size)
    (hdest : result + offset + len ≤ mem.size)
    (hprefix : mem.readWithPadding (result + 32) (offset - 32) =
      ffi.ByteArray.zeroes (offset - 32))
    (htemp : mem.readWithPadding (temp + 32) len = Model.natToBytes value len)
    (hfit : value < 256 ^ len) :
    (barrettRestoreMemory mem temp result offset len).readWithPadding
        (result + 32) width = Model.natToBytes value width := by
  let restored := barrettRestoreMemory mem temp result offset len
  let prefixLen := offset - 32
  have hoffsetEq : 32 + prefixLen = offset := by
    dsimp only [prefixLen]
    omega
  have hrestoredSize : restored.size = mem.size := by
    dsimp only [restored]
    exact barrettRestoreMemory_size_inBounds hlen hsrc hdest
  have hprefixFinal : restored.readWithPadding (result + 32) prefixLen =
      ffi.ByteArray.zeroes prefixLen := by
    by_cases hp : prefixLen = 0
    · dsimp only [prefixLen] at hp ⊢
      rw [hp, byteArray_readWithPadding_zero]
      exact (zeroes_zero (n := 0) rfl).symm
    · have hpPos : 0 < prefixLen := Nat.pos_of_ne_zero hp
      have hpres := barrettRestoreMemory_read_below_len
        (mem := mem) (temp := temp) (result := result) (offset := offset)
        (written := len) (read := result + 32) (len := prefixLen)
        hlen hpPos (by omega) hsrc (by omega)
        (by rw [show result + 32 + prefixLen = result + offset by omega])
        (by omega)
      simpa only [restored, prefixLen, hprefix] using hpres
  have hsuffixFinal : restored.readWithPadding (result + offset) len =
      Model.natToBytes value len := by
    have hrestored := barrettRestoreMemory_read_restored
      (mem := mem) (temp := temp) (result := result) (offset := offset) (len := len)
      hlen hsrc (by omega) (by omega)
    exact hrestored.trans htemp
  apply readWithPadding_eq_leftPaddedNatToBytes
    (mem := restored) (start := result + 32) (k := prefixLen) (len := len)
    (width := width) (value := value)
  · simpa only [prefixLen] using hwidth
  · exact hlen
  · exact hwidth64
  · rw [hrestoredSize]
    omega
  · exact hprefixFinal
  · rw [show result + 32 + prefixLen = result + offset by omega]
    exact hsuffixFinal
  · exact hfit

/-- Pure memory/control facts needed by the deployed normalization and result-allocation prefix.
They are grouped so the concrete prepared-input proof can derive them once from allocator geometry. -/
structure NormalizeReentryGeometry (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256)
    (p m fp resultFp : Nat) : Prop where
  modPos : 0 < m
  modBound : m <= 1024
  p32 : p + 32 < UInt256.size
  pend : p + m + 31 < UInt256.size
  pend64 : p + m + 31 < 2 ^ 64
  activeEnd : p + m + 31 + 32 <= 32 * aw.toNat
  normalize : p + 32 < barrettScanStop mem aw p m
  fp96 : 96 <= fp
  allocationBound : fp + bytesAllocationSize (barrettNormalizedLen mem aw p m) < 2 ^ 64
  memSize : 96 <= mem.size
  memLe : mem.size <= fp
  gap : fp - mem.size < USize.size
  aw3 : 3 <= aw.toNat
  aw64 : ¬ ((UInt256.ofNat 64) >= aw * UInt256.ofNat 32)
  awFit : aw.toNat * 32 < UInt256.size
  freePtr : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp)
  calldataBound : I.calldata.size < 2 ^ 64
  fp32 : fp + 32 < UInt256.size
  normalizedLenPos : 0 < barrettNormalizedLen mem aw p m
  modulusAccess : (UInt256.ofNat fp).toNat + 32 <=
    32 * (barrettNormalizedAw aw mem fp p m).toNat
  modulusLength : wideLoadWord (barrettNormalizedMem mem aw fp p m)
    (barrettNormalizedAw aw mem fp p m) (UInt256.ofNat fp) =
      UInt256.ofNat (barrettNormalizedLen mem aw p m)
  resultFp96 : 96 <= resultFp
  resultBound : resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m) < 2 ^ 64
  normalizedMemSize : 96 <= (barrettNormalizedMem mem aw fp p m).size
  normalizedMemLe : (barrettNormalizedMem mem aw fp p m).size <= resultFp
  resultGap : resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size
  normalizedAw3 : 3 <= (barrettNormalizedAw aw mem fp p m).toNat
  normalizedAw64 : ¬ ((UInt256.ofNat 64) >=
    barrettNormalizedAw aw mem fp p m * UInt256.ofNat 32)
  normalizedFreePtr : (barrettNormalizedMem mem aw fp p m).readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat resultFp)
  checksBound : fp + 32 + barrettNormalizedLen mem aw p m + 32 < UInt256.size
  checksActive : fp + 32 + barrettNormalizedLen mem aw p m + 32 <=
    32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat
  resultPayloadActive : resultFp + 32 + barrettNormalizedLen mem aw p m <=
    32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat
  checksAw : 32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat < UInt256.size
  lengthAfterResult : wideLoadWord
    (barrettNormalizedResultMem mem aw fp p m resultFp)
    (barrettNormalizedResultAw mem aw fp p m resultFp) (UInt256.ofNat fp) =
      UInt256.ofNat (barrettNormalizedLen mem aw p m)
  modulusHeaderAfterResult :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat (barrettNormalizedLen mem aw p m))
  modulusPayloadAfterResult :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding
        (fp + 32) (barrettNormalizedLen mem aw p m) =
      mem.readWithPadding (p + barrettNormalizedOffset mem aw p m)
        (barrettNormalizedLen mem aw p m)
  

/-- Completed normalization facts after deriving the multi-limb zero/one checks from the first
copied word. -/
structure NormalizeReentryFacts (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256)
    (p m fp resultFp : Nat) : Prop extends NormalizeReentryGeometry I mem aw p m fp resultFp where
  zeroCheck : memoryZeroResult
    (barrettNormalizedResultMem mem aw fp p m resultFp)
    (barrettNormalizedResultAw mem aw fp p m resultFp)
    (fp + 32) (fp + 32 + barrettNormalizedLen mem aw p m) = 0
  oneCheck : memoryOneResult
    (barrettNormalizedResultMem mem aw fp p m resultFp)
    (barrettNormalizedResultAw mem aw fp p m resultFp)
    fp (barrettNormalizedLen mem aw p m) = 0

/-- The two normalized allocations preserve any concrete source slice that stays below both
allocation frontiers. -/
theorem NormalizeReentryGeometry.readOriginal
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp read len : Nat}
    (geometry : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hsourceForCopy : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m ≤ fp + 32)
    (hlenPos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hread96 : 96 ≤ read) (hreadIn : read + len ≤ mem.size)
    (hbelowFp : read + len ≤ fp) (hbelowResult : read + len ≤ resultFp) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding read len =
      mem.readWithPadding read len := by
  exact barrettNormalizedResultMem_read_original_len
    geometry.memSize geometry.memLe geometry.gap geometry.normalizedLenPos hsourceForCopy
    geometry.normalizedMemSize geometry.resultGap hlenPos hlen64 hread96 hreadIn
    hbelowFp hbelowResult

/-- The zero-filled gap below the normalized allocations remains zero after allocating the
temporary normalized result object. -/
theorem NormalizeReentryGeometry.readGap
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp read len : Nat}
    (geometry : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hsourceForCopy : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m ≤ fp + 32)
    (hlenPos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hread96 : 96 ≤ read) (hstart : mem.size ≤ read)
    (hbelowFp : read + len ≤ fp) (hbelowResult : read + len ≤ resultFp) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding read len =
      ffi.ByteArray.zeroes len := by
  have hnormalizedSize : (barrettNormalizedMem mem aw fp p m).size =
      fp + 32 + barrettNormalizedLen mem aw p m := by
    exact barrettNormalizedMemory_size geometry.memSize geometry.memLe geometry.gap
      geometry.normalizedLenPos hsourceForCopy
  have hpreserved := barrettNormalizedResultMem_read_below_len
    geometry.normalizedMemSize geometry.resultGap hread96 hlenPos hlen64
    (by rw [hnormalizedSize]; omega) hbelowResult
  have hzero := barrettNormalizedMemory_read_gap_len
    geometry.memSize geometry.memLe geometry.gap geometry.normalizedLenPos hsourceForCopy
    hlenPos hlen64 hstart hbelowFp
  exact hpreserved.trans hzero

/-- The temporary normalized result allocation materializes exactly its bytes header. -/
theorem NormalizeReentryGeometry.resultMemSize
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp : Nat}
    (geometry : NormalizeReentryGeometry I mem aw p m fp resultFp) :
    (barrettNormalizedResultMem mem aw fp p m resultFp).size = resultFp + 32 := by
  unfold barrettNormalizedResultMem
  exact storeBytesLength_size
    (by rw [setFreePtr_size geometry.normalizedMemSize]; exact geometry.normalizedMemLe)
    (by rw [setFreePtr_size geometry.normalizedMemSize]; exact geometry.resultGap)

/-- Exact allocator geometry for the normalization path from an aligned Solidity free-memory
frontier.  The alignment hypotheses describe the compiler's allocator state; all effects of the
two concrete `bytes` allocations and the intervening `MCOPY` are derived here. -/
theorem normalizeReentryGeometry_of_aligned
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp q : Nat}
    (hmodPos : 0 < m) (hmodBound : m <= 1024)
    (hp64 : 64 <= p)
    (hpend64 : p + m + 31 < 2 ^ 64)
    (hactiveEnd : p + m + 31 + 32 <= 32 * aw.toNat)
    (hnormalize : p + 32 < barrettScanStop mem aw p m)
    (hmem96 : 96 <= mem.size) (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size)
    (hfreePtr : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hawEq : aw = UInt256.ofNat q) (hfpEq : fp = 32 * q)
    (hsourceInMem : p + 32 + m <= mem.size)
    (hsourceBelowFp : p + 32 + m <= fp)
    (hresultFpEq : resultFp = fp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (hresultBound : resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m) < 2 ^ 64) :
    NormalizeReentryGeometry I mem aw p m fp resultFp := by
  let n := barrettNormalizedLen mem aw p m
  let offset := barrettNormalizedOffset mem aw p m
  let normMem := barrettNormalizedMem mem aw fp p m
  let normAw := barrettNormalizedAw aw mem fp p m
  let resultMem := barrettNormalizedResultMem mem aw fp p m resultFp
  let resultAw := barrettNormalizedResultAw mem aw fp p m resultFp
  have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p m hmodPos
  have hoffsetGe : 32 <= offset := by
    dsimp only [offset, barrettNormalizedOffset]
    have hbounds := barrettScanStopAt_bounds mem aw
      (barrettScanEnd p m) (barrettScanStart p) (by
        unfold barrettScanStart barrettScanEnd
        omega)
    have hlower : p + 32 <= barrettScanStop mem aw p m := by
      simpa [barrettScanStop, barrettScanStart] using hbounds.1
    omega
  have hoffsetLe : offset <= m + 31 := by
    dsimp only [offset, barrettNormalizedOffset]
    have hbounds := barrettScanStopAt_bounds mem aw
      (barrettScanEnd p m) (barrettScanStart p) (by
        unfold barrettScanStart barrettScanEnd
        omega)
    have hupper : barrettScanStop mem aw p m <= p + m + 31 := by
      simpa [barrettScanStop, barrettScanEnd] using hbounds.2
    omega
  have hoffsetLen : offset + n = m + 32 := by
    dsimp only [offset, n]
    omega
  have hnPos : 0 < n := by
    omega
  have hnLe : n <= m := by
    dsimp only [n]
    omega
  have hn64 : n < 2 ^ 64 := lt_of_le_of_lt hnLe (lt_of_le_of_lt hmodBound (by decide))
  have hsourceEnd : p + offset + n = p + 32 + m := by omega
  have hsourceForCopy : p + offset + n <= fp + 32 := by
    rw [hsourceEnd]
    omega
  have hsourceInMem' : p + offset + n <= mem.size := by
    rw [hsourceEnd]
    exact hsourceInMem
  have hsourceBelowFp' : p + offset + n <= fp := by
    rw [hsourceEnd]
    exact hsourceBelowFp
  have hsourceAbove : 96 <= p + offset := by
    omega
  have hfp96 : 96 <= fp := hmem96.trans hmemLe
  have hq3 : 3 <= q := by
    rw [hfpEq] at hfp96
    omega
  have hallocPos : 0 < bytesAllocationSize n := by
    unfold bytesAllocationSize
    omega
  have hallocationBound : fp + bytesAllocationSize n < 2 ^ 64 := by
    rw [show fp + bytesAllocationSize n = resultFp by
      simpa only [n] using hresultFpEq.symm]
    omega
  have hfpBound : fp < 2 ^ 64 := by
    omega
  have hqBound : q + bytesAllocationWords n < UInt256.size := by
    have hbytes : 32 * (q + bytesAllocationWords n) < 2 ^ 64 := by
      rw [Nat.mul_add, <- hfpEq, <- bytesAllocationSize_eq_words]
      exact hallocationBound
    have h64 : 2 ^ 64 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hawNat : aw.toNat = q := by
    rw [hawEq, UInt256.toNat_ofNat_of_lt]
    have hwordsPos : 0 < bytesAllocationWords n := by
      unfold bytesAllocationWords
      omega
    omega
  have hawFit : aw.toNat * 32 < UInt256.size := by
    rw [hawNat, Nat.mul_comm, <- hfpEq]
    exact lt_trans hfpBound (by norm_num [UInt256.size])
  have hawMul : (aw * UInt256.ofNat 32).toNat = 32 * aw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      simpa [Nat.mul_comm] using hawFit
  have hnewEq : newBytesWords aw fp n = UInt256.ofNat (q + bytesAllocationWords n) := by
    rw [hawEq, hfpEq]
    exact newBytesWords_aligned hqBound
  have hnewNat : (newBytesWords aw fp n).toNat = q + bytesAllocationWords n := by
    rw [hnewEq, UInt256.toNat_ofNat_of_lt hqBound]
  have hnewActive : 32 * (newBytesWords aw fp n).toNat = fp + bytesAllocationSize n := by
    rw [hnewNat, hfpEq, bytesAllocationSize_eq_words]
    omega
  have hcopySource : p + offset + n <= 32 * (newBytesWords aw fp n).toNat := by
    rw [hnewActive]
    exact le_trans hsourceBelowFp' (Nat.le_add_right _ _)
  have hcopyDest : fp + 32 + n <= 32 * (newBytesWords aw fp n).toNat := by
    rw [hnewActive]
    unfold bytesAllocationSize
    omega
  have hcopyMax : max (fp + 32) (p + offset) + n <=
      32 * (newBytesWords aw fp n).toNat := by
    rw [<- Nat.add_max_add_right]
    exact max_le hcopyDest hcopySource
  have hnormAwEq : normAw = newBytesWords aw fp n := by
    dsimp only [normAw]
    unfold barrettNormalizedAw barrettNormalizeCopyWords
    have hM : MachineState.M
        (newBytesWords aw fp (barrettNormalizedLen mem aw p m)).toNat
        (max (fp + 32) (p + barrettNormalizedOffset mem aw p m))
        (barrettNormalizedLen mem aw p m) =
      (newBytesWords aw fp (barrettNormalizedLen mem aw p m)).toNat := by
      simpa only [n, offset] using machineM_eq_of_access hcopyMax
    rw [hM, u256_ofNat_toNat]
  have hnormAwNat : normAw.toNat = q + bytesAllocationWords n := by
    rw [hnormAwEq, hnewNat]
  have hnormActive : 32 * normAw.toNat = fp + bytesAllocationSize n := by
    rw [hnormAwNat, hfpEq, bytesAllocationSize_eq_words]
    omega
  have hnormAwFit : normAw.toNat * 32 < UInt256.size := by
    rw [Nat.mul_comm, hnormActive]
    exact lt_trans hallocationBound (by norm_num [UInt256.size])
  have hnormAwMul : (normAw * UInt256.ofNat 32).toNat = 32 * normAw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      simpa [Nat.mul_comm] using hnormAwFit
  have hnormMemSize : normMem.size = fp + 32 + n := by
    dsimp only [normMem]
    unfold barrettNormalizedMem
    simpa only [n, offset] using barrettNormalizedMemory_size
      (mem := mem) (fp := fp) (p := p) (offset := offset) (len := n)
      hmem96 hmemLe hgap hnPos hsourceForCopy
  have hmodulusAccess : (UInt256.ofNat fp).toNat + 32 <= 32 * normAw.toNat := by
    rw [UInt256.toNat_ofNat_of_lt (lt_trans hfpBound (by norm_num [UInt256.size])), hnormActive]
    unfold bytesAllocationSize
    omega
  have hmodulusLength : wideLoadWord normMem normAw (UInt256.ofNat fp) = UInt256.ofNat n := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (lt_trans hfpBound (by norm_num [UInt256.size])),
        hnormMemSize]
      omega
    · intro h
      change (normAw * UInt256.ofNat 32).toNat <= (UInt256.ofNat fp).toNat at h
      rw [hnormAwMul,
        UInt256.toNat_ofNat_of_lt (lt_trans hfpBound (by norm_num [UInt256.size]))] at h
      rw [hnormActive] at h
      unfold bytesAllocationSize at h
      omega
    · have hread := barrettNormalizedMemory_read_length
        (mem := mem) (fp := fp) (p := p) (offset := offset) (len := n)
        hmem96 hmemLe hgap hnPos hsourceForCopy
      simpa only [normMem, barrettNormalizedMem, n, offset,
        UInt256.toNat_ofNat_of_lt (lt_trans hfpBound (by norm_num [UInt256.size]))] using hread
  have hnormMem96 : 96 <= normMem.size := by rw [hnormMemSize]; omega
  have hnormMemLe : normMem.size <= resultFp := by
    rw [hnormMemSize, hresultFpEq]
    dsimp only [n]
    unfold bytesAllocationSize
    omega
  have hresultGap : resultFp - normMem.size < USize.size := by
    rw [hnormMemSize, hresultFpEq]
    dsimp only [n]
    exact lt_usize _ (by unfold bytesAllocationSize; omega)
  have hnormFreePtr : normMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat resultFp) := by
    have hread := barrettNormalizedMemory_read64
      (mem := mem) (fp := fp) (p := p) (offset := offset) (len := n)
      hmem96 (by omega) hmemLe hgap hnPos hsourceForCopy
    simpa only [normMem, barrettNormalizedMem, n, offset, hresultFpEq] using hread
  let qn := q + bytesAllocationWords n
  have hnormAwOfNat : normAw = UInt256.ofNat qn := by
    dsimp only [qn]
    rw [hnormAwEq, hnewEq]
  have hresultFpWords : resultFp = 32 * qn := by
    dsimp only [qn]
    rw [hresultFpEq]
    dsimp only [n]
    rw [<- hnewActive, hnewNat]
  have hqnBound : qn + bytesAllocationWords n < UInt256.size := by
    have hbytes : 32 * (qn + bytesAllocationWords n) < 2 ^ 64 := by
      rw [Nat.mul_add, <- hresultFpWords, <- bytesAllocationSize_eq_words]
      exact hresultBound
    have h64 : 2 ^ 64 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hresultAwEq : resultAw = UInt256.ofNat (qn + bytesAllocationWords n) := by
    dsimp only [resultAw]
    unfold barrettNormalizedResultAw
    rw [show barrettNormalizedAw aw mem fp p m = normAw by rfl, hnormAwOfNat,
      show resultFp = 32 * qn from hresultFpWords]
    exact newBytesWords_aligned hqnBound
  have hresultAwNat : resultAw.toNat = qn + bytesAllocationWords n := by
    rw [hresultAwEq, UInt256.toNat_ofNat_of_lt hqnBound]
  have hresultActive : 32 * resultAw.toNat = resultFp + bytesAllocationSize n := by
    rw [hresultAwNat, hresultFpWords, bytesAllocationSize_eq_words]
    omega
  have hchecksActive : fp + 32 + n + 32 <= 32 * resultAw.toNat := by
    rw [hresultActive, hresultFpEq]
    dsimp only [n]
    unfold bytesAllocationSize
    omega
  have hchecksAw : 32 * resultAw.toNat < UInt256.size := by
    rw [hresultActive]
    exact lt_trans hresultBound (by norm_num [UInt256.size])
  have hresultAwMul : (resultAw * UInt256.ofNat 32).toNat = 32 * resultAw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      simpa [Nat.mul_comm] using hchecksAw
  have hresultMemSize : resultMem.size = resultFp + 32 := by
    dsimp only [resultMem]
    unfold barrettNormalizedResultMem
    exact storeBytesLength_size
      (by rw [setFreePtr_size hnormMem96]; exact hnormMemLe)
      (by rw [setFreePtr_size hnormMem96]; exact hresultGap)
  have hheader : resultMem.readWithPadding fp 32 =
      UInt256.toByteArray (UInt256.ofNat n) := by
    have hnormHeader := barrettNormalizedMemory_read_length
      (mem := mem) (fp := fp) (p := p) (offset := offset) (len := n)
      hmem96 hmemLe hgap hnPos hsourceForCopy
    have hnormHeader' : normMem.readWithPadding fp 32 =
        UInt256.toByteArray (UInt256.ofNat n) := by
      simpa only [normMem, barrettNormalizedMem, n, offset] using hnormHeader
    dsimp only [resultMem]
    unfold barrettNormalizedResultMem
    rw [storeBytesLength_read_below_padded]
    · rw [setFreePtr_read_above_padded]
      · exact hnormHeader'
      · exact hnormMem96
      · omega
    · rw [setFreePtr_size hnormMem96]
      omega
    · rw [hresultFpEq]
      unfold bytesAllocationSize
      omega
    · rw [setFreePtr_size hnormMem96]
      exact hresultGap
  have hlengthAfter : wideLoadWord resultMem resultAw (UInt256.ofNat fp) = UInt256.ofNat n := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (lt_trans hfpBound (by norm_num [UInt256.size])),
        hresultMemSize]
      omega
    · intro h
      change (resultAw * UInt256.ofNat 32).toNat <= (UInt256.ofNat fp).toNat at h
      rw [hresultAwMul,
        UInt256.toNat_ofNat_of_lt (lt_trans hfpBound (by norm_num [UInt256.size]))] at h
      rw [hresultActive, hresultFpEq] at h
      dsimp only [n] at h
      unfold bytesAllocationSize at h
      omega
    · simpa only [UInt256.toNat_ofNat_of_lt
        (lt_trans hfpBound (by norm_num [UInt256.size]))] using hheader
  have hp32 : p + 32 < UInt256.size := by
    exact lt_trans (by omega : p + 32 < 2 ^ 64) (by norm_num [UInt256.size])
  have hpend : p + m + 31 < UInt256.size :=
    lt_trans hpend64 (by norm_num [UInt256.size])
  have hfp32 : fp + 32 < UInt256.size := by
    exact lt_trans (by omega : fp + 32 < 2 ^ 64) (by norm_num [UInt256.size])
  have hchecksBound : fp + 32 + n + 32 < UInt256.size := by
    exact lt_of_le_of_lt hchecksActive hchecksAw
  have hpayload := barrettNormalizedResultMem_read_source_payload
    (mem := mem) (aw := aw) (fp := fp) (p := p) (m := m) (resultFp := resultFp)
    hmem96 hmemLe hgap (by simpa only [n] using hnPos) (by simpa only [n] using hn64)
    (by simpa only [n, offset] using hsourceForCopy)
    (by simpa only [n, offset] using hsourceInMem')
    (by simpa only [offset] using hsourceAbove)
    (by simpa only [n, offset] using hsourceBelowFp') hresultFpEq
  refine {
    modPos := hmodPos
    modBound := hmodBound
    p32 := hp32
    pend := hpend
    pend64 := hpend64
    activeEnd := hactiveEnd
    normalize := hnormalize
    fp96 := hfp96
    allocationBound := by simpa only [n] using hallocationBound
    memSize := hmem96
    memLe := hmemLe
    gap := hgap
    aw3 := by rw [hawNat]; exact hq3
    aw64 := by
      intro h
      change (aw * UInt256.ofNat 32).toNat <= (UInt256.ofNat 64).toNat at h
      rw [hawMul, show (UInt256.ofNat 64).toNat = 64 by decide] at h
      rw [hawNat, <- hfpEq] at h
      omega
    awFit := hawFit
    freePtr := hfreePtr
    calldataBound := hcalldata
    fp32 := hfp32
    normalizedLenPos := by simpa only [n] using hnPos
    modulusAccess := by simpa only [normAw] using hmodulusAccess
    modulusLength := by simpa only [normMem, normAw, n] using hmodulusLength
    resultFp96 := by rw [hresultFpEq]; omega
    resultBound := hresultBound
    normalizedMemSize := by simpa only [normMem] using hnormMem96
    normalizedMemLe := by simpa only [normMem] using hnormMemLe
    resultGap := by simpa only [normMem] using hresultGap
    normalizedAw3 := by
      rw [show barrettNormalizedAw aw mem fp p m = normAw by rfl, hnormAwNat]
      omega
    normalizedAw64 := by
      intro h
      change (barrettNormalizedAw aw mem fp p m * UInt256.ofNat 32).toNat <=
        (UInt256.ofNat 64).toNat at h
      rw [show barrettNormalizedAw aw mem fp p m = normAw by rfl, hnormAwMul,
        show (UInt256.ofNat 64).toNat = 64 by decide, hnormActive] at h
      omega
    normalizedFreePtr := by simpa only [normMem] using hnormFreePtr
    checksBound := by simpa only [n] using hchecksBound
    checksActive := by simpa only [n, resultAw] using hchecksActive
    resultPayloadActive := by
      rw [show 32 * (barrettNormalizedResultAw mem aw fp p m resultFp).toNat =
        resultFp + bytesAllocationSize n by simpa only [resultAw] using hresultActive]
      have h := Nat.add_le_add_left (bytesHeaderAndSize_le_allocation n) resultFp
      dsimp only [n]
      omega
    checksAw := by simpa only [resultAw] using hchecksAw
    lengthAfterResult := by simpa only [resultMem, resultAw, n] using hlengthAfter
    modulusHeaderAfterResult := by simpa only [resultMem, n] using hheader
    modulusPayloadAfterResult := by simpa only [n] using hpayload
  }

/-- The concrete prepared operand/result state satisfies the aligned normalization allocator
contract for every bounded multi-limb modulus. -/
theorem preparedNormalizeReentryGeometryAny
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    NormalizeReentryGeometry I
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize) := by
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  let q := operandModulusWords baseSize exponentSize modulusSize +
    bytesAllocationWords modulusSize
  have hmodPos : 0 < modulusSize := by
    by_contra hnot
    have hz : modulusSize = 0 := Nat.eq_zero_of_not_pos hnot
    subst modulusSize
    simp [barrettScanStop, barrettScanStart, barrettScanEnd, barrettScanStopAt] at hnormalize
  have hmemSize : mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa only [mem] using wideWordResultMemory_size I hb he hm
  have hmem96 : 96 <= mem.size := by
    rw [hmemSize]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hmemLe : mem.size <= fp := by
    rw [hmemSize]
    dsimp only [fp]
    unfold wideBarrettNormalizedFp bytesAllocationSize
    omega
  have hgap : fp - mem.size < USize.size := by
    rw [hmemSize]
    exact lt_usize _ (by
      dsimp only [fp]
      unfold wideBarrettNormalizedFp bytesAllocationSize
      omega)
  have hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp) := by
    simpa only [mem, fp, wideBarrettNormalizedFp] using
      wideWordResultMemory_read64 I hb he hm
  have hawEq : aw = UInt256.ofNat q := by
    dsimp only [aw, q]
    exact wideWordResultWords_eq hb he hm
  have hfpEq : fp = 32 * q := by
    dsimp only [fp, q]
    unfold wideBarrettNormalizedFp
    rw [operandFreePtr_eq, bytesAllocationSize_eq_words]
    omega
  have hsourceInMem : p + 32 + modulusSize <= mem.size := by
    rw [hmemSize]
    dsimp only [p]
    unfold operandFreePtr operandModulusPtr bytesAllocationSize
    omega
  have hsourceBelowFp : p + 32 + modulusSize <= fp := by
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr bytesAllocationSize
    omega
  have hactiveEnd : p + modulusSize + 31 + 32 <= 32 * aw.toNat := by
    dsimp only [p, aw]
    rw [wideWordResultWords_toNat hb he hm]
    simp only [operandModulusPtr, operandExponentPtr, operandBasePtr, operandModulusWords,
      operandExponentWords, operandBaseWords, bytesAllocationWords, bytesAllocationSize]
    omega
  have hresultEq : resultFp = fp + bytesAllocationSize n := by
    dsimp only [resultFp, fp, n, mem, aw, p]
    rfl
  have hnLe : n <= modulusSize := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize hmodPos
    dsimp only [n]
    omega
  have hallocNLe : bytesAllocationSize n <= 1056 := by
    unfold bytesAllocationSize
    omega
  have hfpLe : fp <= 4352 := by
    dsimp only [fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hresultBound : resultFp + bytesAllocationSize n < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show resultFp + bytesAllocationSize n <= 6464 by
        rw [hresultEq]
        omega)
      (by decide)
  apply normalizeReentryGeometry_of_aligned
    (q := q) (I := I) (mem := mem) (aw := aw) (p := p) (m := modulusSize)
    (fp := fp) (resultFp := resultFp)
  · exact hmodPos
  · exact hm
  · dsimp only [p]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · apply lt_of_le_of_lt
      (show p + modulusSize + 31 <= 4351 by
        dsimp only [p]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide)
  · exact hactiveEnd
  · simpa only [mem, aw, p] using hnormalize
  · exact hmem96
  · exact hmemLe
  · exact hgap
  · exact hfree
  · exact hcalldata
  · exact hawEq
  · exact hfpEq
  · exact hsourceInMem
  · exact hsourceBelowFp
  · exact hresultEq
  · exact hresultBound

/-- Compatibility specialization for callers that already know the original modulus is
multi-limb.  The geometry itself only needs a positive normalization scan. -/
theorem preparedNormalizeReentryGeometry
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (_hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    NormalizeReentryGeometry I
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize) :=
  preparedNormalizeReentryGeometryAny I hb he hm hnormalize hcalldata

/-- The original result payload skipped by normalization is the allocator-created zero gap. -/
theorem preparedNormalizedPrefixZero
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
    let offset := barrettNormalizedOffset mem aw p modulusSize
    (barrettNormalizedResultMem mem aw fp p modulusSize resultFp).readWithPadding
        (operandFreePtr baseSize exponentSize modulusSize + 32) (offset - 32) =
      ffi.ByteArray.zeroes (offset - 32) := by
  dsimp only
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  change (barrettNormalizedResultMem mem aw fp p modulusSize resultFp).readWithPadding
      (operandFreePtr baseSize exponentSize modulusSize + 32) (offset - 32) =
    ffi.ByteArray.zeroes (offset - 32)
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hbounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p modulusSize) (barrettScanStart p) (by
      unfold barrettScanStart barrettScanEnd
      omega)
  have hoffsetPos : 32 < offset := by
    dsimp only [offset, barrettNormalizedOffset]
    have hnormalizeLocal : p + 32 < barrettScanStop mem aw p modulusSize := by
      simpa only [mem, aw, p] using hnormalize
    omega
  have hoffsetLe : offset ≤ modulusSize + 31 := by
    have hupper : barrettScanStop mem aw p modulusSize ≤ p + modulusSize + 31 := by
      simpa [barrettScanStop, barrettScanEnd] using hbounds.2
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hsourceForCopy : p + offset + n ≤ fp + 32 := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    have hend : p + offset + n = p + 32 + modulusSize := by
      dsimp only [offset, n] at hsplit ⊢
      omega
    rw [hend]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hallocation : 32 + modulusSize ≤ bytesAllocationSize modulusSize :=
    bytesHeaderAndSize_le_allocation modulusSize
  apply geometry.readGap
    (read := operandFreePtr baseSize exponentSize modulusSize + 32)
    (len := offset - 32) hsourceForCopy (by omega) (by omega)
  · unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  · rw [show mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 by
      simpa only [mem] using wideWordResultMemory_size I hb he hm]
  · dsimp only [fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  · dsimp only [resultFp, fp, n]
    unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp operandFreePtr
      operandModulusPtr operandExponentPtr operandBasePtr
    omega

/-- Geometry required when the normalized modulus re-enters the already completed direct
multi-limb selector. No arithmetic result is included in these facts. -/
structure NormalizedDirectEntryFacts (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256)
    (fp resultFp basePtr baseSize n : Nat) : Prop where
  modulusLarge : 32 < n
  modulusBound : n <= 1024
  p32 : fp + 32 < UInt256.size
  p64 : fp + 32 < 2 ^ 64
  pend : fp + n + 31 < UInt256.size
  source96 : 96 <= fp + 32
  sourceBefore : fp + 32 + n <= resultFp + bytesAllocationSize n
  active : fp + 64 <= 32 * aw.toNat
  first : UInt256.byteAt (UInt256.ofNat 0)
    (wideLoadWord mem aw (UInt256.ofNat (fp + 32))) ≠ UInt256.ofNat 0
  freePtr96 : 96 <= resultFp + bytesAllocationSize n
  allocationBound : resultFp + bytesAllocationSize n +
    wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words n) < 2 ^ 64
  memSize : 96 <= mem.size
  memLe : mem.size <= resultFp + bytesAllocationSize n
  gap : resultFp + bytesAllocationSize n - mem.size < USize.size
  aw3 : 3 <= aw.toNat
  aw64 : ¬ ((UInt256.ofNat 64) >= aw * UInt256.ofNat 32)
  awFit : aw.toNat * 32 < UInt256.size
  freePtr : mem.readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat (resultFp + bytesAllocationSize n))
  calldataBound : I.calldata.size < 2 ^ 64
  accessAllocated : (UInt256.ofNat fp).toNat + 32 <=
    32 * (Modexp.MultiLimbBarrettConversion.allocatedWords aw
      (resultFp + bytesAllocationSize n) n).toNat
  loadAllocated : wideLoadWord
    (Modexp.MultiLimbBarrettConversion.allocatedMemory mem
      (resultFp + bytesAllocationSize n) n)
    (Modexp.MultiLimbBarrettConversion.allocatedWords aw
      (resultFp + bytesAllocationSize n) n)
    (UInt256.ofNat fp) = UInt256.ofNat n
  basePos : 0 < baseSize
  baseBound : baseSize <= 1024
  basePtr96 : 96 <= basePtr
  baseSourceBefore : basePtr + 32 + baseSize <= resultFp + bytesAllocationSize n
  baseHeader : mem.readWithPadding basePtr 32 =
    UInt256.toByteArray (UInt256.ofNat baseSize)
  backendWorkspace : directRemFp (resultFp + bytesAllocationSize n) n baseSize +
    wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words n) +
    Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 < 2 ^ 64

/-- The two normalized allocations preserve the original base value, while the copied significant
modulus suffix has the same value as the original modulus. -/
theorem normalizedResult_values_eq_original
    {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp basePtr baseSize : Nat}
    (hm : 0 < m)
    (hmem96 : 96 <= mem.size)
    (hmemLe : mem.size <= fp)
    (hgap : fp - mem.size < USize.size)
    (hlen : 0 < barrettNormalizedLen mem aw p m)
    (hlen64 : barrettNormalizedLen mem aw p m < 2 ^ 64)
    (hsrc : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m <= fp + 32)
    (hsourceInMem : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m <= mem.size)
    (hsourceAbove : 96 <= p + barrettNormalizedOffset mem aw p m)
    (hsourceBelowFp : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m <= fp)
    (hresultFp : resultFp = fp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (hbasePos : 0 < baseSize)
    (hbase64 : baseSize < 2 ^ 64)
    (hbaseAbove : 96 <= basePtr + 32)
    (hbaseIn : basePtr + 32 + baseSize <= mem.size)
    (hbaseBelowFp : basePtr + 32 + baseSize <= fp)
    (hbaseBelowResult : basePtr + 32 + baseSize <= resultFp)
    (hbaseAddr64 : basePtr + 32 < 2 ^ 64)
    (hnormalizedAddr64 : fp + 32 < 2 ^ 64)
    (hsourceAddr64 : p + barrettNormalizedOffset mem aw p m < 2 ^ 64)
    (hpend256 : p + m + 31 < UInt256.size)
    (hpend64 : p + m + 31 < 2 ^ 64)
    (hactiveEnd : p + m + 31 + 32 <= 32 * aw.toNat)
    (hawFit : aw.toNat * 32 < UInt256.size) :
    Model.bytesToNatPadded (barrettNormalizedResultMem mem aw fp p m resultFp)
        (basePtr + 32) baseSize = Model.bytesToNatPadded mem (basePtr + 32) baseSize ∧
      Model.bytesToNatPadded (barrettNormalizedResultMem mem aw fp p m resultFp)
        (fp + 32) (barrettNormalizedLen mem aw p m) =
          Model.bytesToNatPadded mem (p + 32) m := by
  have hnormSize : (barrettNormalizedMem mem aw fp p m).size =
      fp + 32 + barrettNormalizedLen mem aw p m := by
    unfold barrettNormalizedMem
    exact barrettNormalizedMemory_size hmem96 hmemLe hgap hlen hsrc
  have hnormMem96 : 96 <= (barrettNormalizedMem mem aw fp p m).size := by
    rw [hnormSize]
    omega
  have hresultGap : resultFp - (barrettNormalizedMem mem aw fp p m).size < USize.size := by
    rw [hresultFp, hnormSize]
    unfold bytesAllocationSize
    exact lt_usize _ (by omega)
  have hbaseRead := barrettNormalizedResultMem_read_original_len
    (mem := mem) (aw := aw) (fp := fp) (p := p) (m := m) (resultFp := resultFp)
    (read := basePtr + 32) (len := baseSize)
    hmem96 hmemLe hgap hlen hsrc hnormMem96 hresultGap hbasePos hbase64
    hbaseAbove hbaseIn hbaseBelowFp hbaseBelowResult
  have hbaseValue := model_bytesToNatPadded_eq_of_readWithPadding
    hbaseAddr64 hbaseAddr64 hbase64 hbaseRead
  have hmodulusRead := barrettNormalizedResultMem_read_source_payload
    (mem := mem) (aw := aw) (fp := fp) (p := p) (m := m) (resultFp := resultFp)
    hmem96 hmemLe hgap hlen hlen64 hsrc hsourceInMem hsourceAbove hsourceBelowFp hresultFp
  have hnormalizedValue := model_bytesToNatPadded_eq_of_readWithPadding
    hnormalizedAddr64 hsourceAddr64 hlen64 hmodulusRead
  have hsuffixValue := normalizedSuffix_value_eq_original
    (mem := mem) (aw := aw) hm hpend256 hpend64 hactiveEnd hawFit
  exact ⟨hbaseValue, hnormalizedValue.trans hsuffixValue⟩

/-- The normalized bytes object denotes exactly the original modulus.  This is the value bridge
used by both the one-word and recursive normalized backends. -/
theorem normalizedResult_modulusValue_eq_original
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp : Nat}
    (facts : NormalizeReentryGeometry I mem aw p m fp resultFp) :
    Model.bytesToNatPadded (barrettNormalizedResultMem mem aw fp p m resultFp)
        (fp + 32) (barrettNormalizedLen mem aw p m) =
      Model.bytesToNatPadded mem (p + 32) m := by
  let n := barrettNormalizedLen mem aw p m
  let offset := barrettNormalizedOffset mem aw p m
  have hnLe : n <= m := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p m facts.modPos
    dsimp only [n]
    omega
  have hn64 : n < 2 ^ 64 :=
    lt_of_le_of_lt hnLe (lt_of_le_of_lt facts.modBound (by decide))
  have hresultAddr64 : fp + 32 < 2 ^ 64 := by
    have hbound := facts.allocationBound
    unfold bytesAllocationSize at hbound
    omega
  have hstopUpper : barrettScanStop mem aw p m <= p + m + 31 := by
    have hbounds := barrettScanStopAt_bounds mem aw
      (barrettScanEnd p m) (barrettScanStart p) (by
        have hm := facts.modPos
        unfold barrettScanStart barrettScanEnd
        omega)
    simpa [barrettScanStop, barrettScanEnd] using hbounds.2
  have hstopLower : p + 32 <= barrettScanStop mem aw p m := by
    have hbounds := barrettScanStopAt_bounds mem aw
      (barrettScanEnd p m) (barrettScanStart p) (by
        have hm := facts.modPos
        unfold barrettScanStart barrettScanEnd
        omega)
    simpa [barrettScanStop, barrettScanStart] using hbounds.1
  have hsourceEq : p + offset = barrettScanStop mem aw p m := by
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hsourceAddr64 : p + offset < 2 ^ 64 := by
    rw [hsourceEq]
    exact lt_of_le_of_lt hstopUpper facts.pend64
  have hnormalizedValue := model_bytesToNatPadded_eq_of_readWithPadding
    hresultAddr64 hsourceAddr64 hn64
    (by simpa only [n, offset] using facts.modulusPayloadAfterResult)
  have hsuffixValue := normalizedSuffix_value_eq_original
    (mem := mem) (aw := aw) facts.modPos facts.pend facts.pend64 facts.activeEnd facts.awFit
  exact hnormalizedValue.trans hsuffixValue

/-- Every normalized payload of at least two bytes begins with the nonzero byte at which the
deployed scan stopped. This derives both the recursive direct-branch test and the short normalized
word-branch test from the scan, rather than assuming a second unrelated selector. -/
theorem normalizedResult_first_nonzero
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp : Nat}
    (facts : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hnMoreThanOne : 1 < barrettNormalizedLen mem aw p m) :
    UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp)
        (UInt256.ofNat (fp + 32))) ≠ UInt256.ofNat 0 := by
  let n := barrettNormalizedLen mem aw p m
  let offset := barrettNormalizedOffset mem aw p m
  let stop := barrettScanStop mem aw p m
  let resultMem := barrettNormalizedResultMem mem aw fp p m resultFp
  let resultAw := barrettNormalizedResultAw mem aw fp p m resultFp
  have hstopBounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p m) (barrettScanStart p) (by
      have hm := facts.modPos
      unfold barrettScanStart barrettScanEnd
      omega)
  have hstopLower : p + 32 <= stop := by
    dsimp only [stop]
    simpa [barrettScanStop, barrettScanStart] using hstopBounds.1
  have hstopUpper : stop <= p + m + 31 := by
    dsimp only [stop]
    simpa [barrettScanStop, barrettScanEnd] using hstopBounds.2
  have hsourceEq : p + offset = stop := by
    dsimp only [offset, stop, barrettNormalizedOffset]
    omega
  have hstopLtEnd : stop < p + m + 31 := by
    by_contra hnot
    have heq : stop = p + m + 31 := by omega
    have hnOne : n = 1 := by
      dsimp only [n, barrettNormalizedLen, barrettNormalizedOffset]
      rw [show barrettScanStop mem aw p m = p + m + 31 by simpa only [stop] using heq]
      omega
    have hn : 1 < n := by simpa only [n] using hnMoreThanOne
    omega
  have hstopNonzero : barrettScanByteAt mem aw stop ≠ UInt256.ofNat 0 := by
    have hstop := barrettScanStopAt_stop mem aw (barrettScanEnd p m) (barrettScanStart p)
    rcases hstop with hend | hnonzero
    · have hend' : p + m + 31 <= stop := by
        simpa [stop, barrettScanStop, barrettScanEnd] using hend
      omega
    · dsimp only [stop]
      simpa [barrettScanStop] using hnonzero
  have hn64 : n < 2 ^ 64 := by
    have hnBound : n <= m := by
      have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p m facts.modPos
      dsimp only [n]
      omega
    have hmBound := facts.modBound
    omega
  have hresultAddr64 : fp + 32 < 2 ^ 64 := by
    have hbound := facts.allocationBound
    unfold bytesAllocationSize at hbound
    omega
  have hsourceAddr64 : p + offset < 2 ^ 64 := by
    rw [hsourceEq]
    exact lt_of_le_of_lt hstopUpper facts.pend64
  have hreadOne : resultMem.readWithPadding (fp + 32) 1 =
      mem.readWithPadding (p + offset) 1 := by
    calc
      resultMem.readWithPadding (fp + 32) 1 =
          (resultMem.readWithPadding (fp + 32) n).extract 0 1 := by
            symm
            exact readWithPadding_window resultMem (fp + 32) n 0 1
              hresultAddr64 hn64 (by simpa using hresultAddr64) (by decide) (by omega)
      _ = (mem.readWithPadding (p + offset) n).extract 0 1 := by
            exact congrArg (fun bs : ByteArray => bs.extract 0 1)
              (by simpa only [resultMem, n, offset] using facts.modulusPayloadAfterResult)
      _ = mem.readWithPadding (p + offset) 1 := by
            exact readWithPadding_window mem (p + offset) n 0 1
              hsourceAddr64 hn64 (by simpa using hsourceAddr64) (by decide) (by omega)
  have hawMul : (aw * UInt256.ofNat 32).toNat = 32 * aw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      exact facts.awFit
  have hsourceWord : p + offset < UInt256.size :=
    lt_trans hsourceAddr64 (by norm_num [UInt256.size])
  have hsourceGuard : ¬ (UInt256.ofNat (p + offset) >= aw * UInt256.ofNat 32) := by
    intro h
    change (aw * UInt256.ofNat 32).toNat <= (UInt256.ofNat (p + offset)).toNat at h
    rw [hawMul, UInt256.toNat_ofNat_of_lt hsourceWord] at h
    rw [hsourceEq] at h
    have hactive := facts.activeEnd
    omega
  have hresultAwFit : resultAw.toNat * 32 < UInt256.size := by
    dsimp only [resultAw]
    simpa [Nat.mul_comm] using facts.checksAw
  have hresultAwMul : (resultAw * UInt256.ofNat 32).toNat = 32 * resultAw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      exact hresultAwFit
  have hresultWord : fp + 32 < UInt256.size := facts.fp32
  have hresultGuard : ¬ (UInt256.ofNat (fp + 32) >= resultAw * UInt256.ofNat 32) := by
    intro h
    change (resultAw * UInt256.ofNat 32).toNat <= (UInt256.ofNat (fp + 32)).toNat at h
    rw [hresultAwMul, UInt256.toNat_ofNat_of_lt hresultWord] at h
    have hactive : fp + 32 + n + 32 <= 32 * resultAw.toNat := by
      simpa only [n, resultAw] using facts.checksActive
    omega
  have hresultModel := barrettScanByteAt_toNat_eq_model
    (mem := resultMem) (aw := resultAw) (cur := fp + 32)
    hresultWord hresultAddr64 hresultGuard
  have hsourceModel := barrettScanByteAt_toNat_eq_model
    (mem := mem) (aw := aw) (cur := p + offset)
    hsourceWord hsourceAddr64 hsourceGuard
  have hmodelEq : Model.bytesToNatPadded resultMem (fp + 32) 1 =
      Model.bytesToNatPadded mem (p + offset) 1 :=
    model_bytesToNatPadded_eq_of_readWithPadding
      hresultAddr64 hsourceAddr64 (by decide) hreadOne
  have hbyteEq : barrettScanByteAt resultMem resultAw (fp + 32) =
      barrettScanByteAt mem aw (p + offset) := by
    apply u256_inj
    rw [hresultModel, hsourceModel, hmodelEq]
  intro hzero
  apply hstopNonzero
  rw [← hsourceEq, ← hbyteEq]
  simpa only [barrettScanByteAt, resultMem, resultAw] using hzero

/-- On a normalized multi-limb payload, the first full word is already nonzero, so both generic
`memoryZero` and `memoryOne` checks stop on their first iteration with result zero. -/
theorem normalizedZeroOneChecks_of_first_nonzero
    {mem : ByteArray} {aw : UInt256} {fp n : Nat}
    (hnLarge : 32 < n)
    (hfirst : UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord mem aw (UInt256.ofNat (fp + 32))) ≠ UInt256.ofNat 0) :
    memoryZeroResult mem aw (fp + 32) (fp + 32 + n) = 0 ∧
      memoryOneResult mem aw fp n = 0 := by
  have hword : wideLoadWord mem aw (UInt256.ofNat (fp + 32)) ≠ UInt256.ofNat 0 := by
    intro hz
    apply hfirst
    rw [hz]
    rfl
  have hzeroFull : ¬ fp + 32 + n - (fp + 32) < 32 := by omega
  have honeFull : ¬ fp + 32 + (n - 1) - (fp + 32) < 32 := by omega
  have hword0 : wideLoadWord mem aw (UInt256.ofNat (fp + 32)) ≠ (⟨0⟩ : UInt256) := by
    simpa using hword
  constructor
  · rw [memoryZeroResult, dif_pos (by omega)]
    unfold memoryZeroChunk
    simp only [if_neg hzeroFull, if_neg hword0]
  · rw [memoryOneResult, if_neg (by omega)]
    rw [memoryOneLoopResult, dif_pos (by omega)]
    unfold memoryZeroChunk
    simp only [if_neg honeFull, if_neg hword0]

/-- Complete the re-entry facts constructively for every normalized multi-limb payload. -/
theorem NormalizeReentryGeometry.complete
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp : Nat}
    (facts : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hnLarge : 32 < barrettNormalizedLen mem aw p m) :
    NormalizeReentryFacts I mem aw p m fp resultFp := by
  have hfirst := normalizedResult_first_nonzero facts (by omega)
  have hchecks := normalizedZeroOneChecks_of_first_nonzero hnLarge hfirst
  exact {
    toNormalizeReentryGeometry := facts
    zeroCheck := hchecks.1
    oneCheck := hchecks.2
  }

/-- Completed re-entry facts for the branch whose normalized modulus fits in one EVM word.  The
zero/one checks are consequences of the preserved modulus value, and the first-byte selector is a
consequence of the original leading-zero scan. -/
structure NormalizedWordReentryFacts
    (I : ExecutionEnv) (mem : ByteArray) (aw : UInt256)
    (p m fp resultFp : Nat) : Prop extends NormalizeReentryFacts I mem aw p m fp resultFp where
  normalizedLenLe32 : barrettNormalizedLen mem aw p m <= 32
  first : barrettNormalizedLen mem aw p m = 1 ∨
    UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
        (barrettNormalizedResultAw mem aw fp p m resultFp)
        (UInt256.ofNat (fp + 32))) ≠ UInt256.ofNat 0

theorem NormalizeReentryGeometry.completeWord
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp : Nat}
    (facts : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hresultFp : resultFp = fp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (hnLe32 : barrettNormalizedLen mem aw p m <= 32)
    (hmodulusGtOne : 1 < Model.bytesToNatPadded mem (p + 32) m) :
    NormalizedWordReentryFacts I mem aw p m fp resultFp := by
  let n := barrettNormalizedLen mem aw p m
  let resultMem := barrettNormalizedResultMem mem aw fp p m resultFp
  let resultAw := barrettNormalizedResultAw mem aw fp p m resultFp
  have hvalueEq := normalizedResult_modulusValue_eq_original facts
  have hvalue : 1 < Model.bytesToNatPadded resultMem (fp + 32) n := by
    rw [show Model.bytesToNatPadded resultMem (fp + 32) n =
      Model.bytesToNatPadded mem (p + 32) m by
        simpa only [resultMem, n] using hvalueEq]
    exact hmodulusGtOne
  have hallocCover := bytesHeaderAndSize_le_allocation n
  have hchecks64 : fp + 32 + n + 32 < 2 ^ 64 := by
    have hbound : fp + bytesAllocationSize n + bytesAllocationSize n < 2 ^ 64 := by
      rw [<- hresultFp]
      simpa only [n] using facts.resultBound
    omega
  have hzero : memoryZeroResult resultMem resultAw
      (fp + 32) (fp + 32 + n) = 0 := by
    rw [memoryZeroResult_eq_reference hchecks64
      (by simpa only [n, resultAw] using facts.checksActive)
      (by simpa only [resultAw] using facts.checksAw) (by omega)]
    unfold memoryZeroReference
    rw [show fp + 32 + n - (fp + 32) = n by omega]
    simp only [if_neg (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hvalue))]
  have hone : memoryOneResult resultMem resultAw fp n = 0 := by
    rw [memoryOneResult_eq_reference hchecks64
      (by simpa only [n, resultAw] using facts.checksActive)
      (by simpa only [resultAw] using facts.checksAw)]
    unfold memoryOneReference
    simp only [if_neg (ne_of_gt hvalue)]
  have hfirst : n = 1 ∨
      UInt256.byteAt (UInt256.ofNat 0)
        (wideLoadWord resultMem resultAw (UInt256.ofNat (fp + 32))) ≠ UInt256.ofNat 0 := by
    by_cases hnOne : n = 1
    · exact Or.inl hnOne
    · exact Or.inr (by
        have hnMoreThanOne : 1 < n := by
          have hnPos : 0 < n := by simpa only [n] using facts.normalizedLenPos
          omega
        simpa only [resultMem, resultAw, n] using
          normalizedResult_first_nonzero facts hnMoreThanOne)
  exact {
    toNormalizeReentryFacts := {
      toNormalizeReentryGeometry := facts
      zeroCheck := by simpa only [resultMem, resultAw, n] using hzero
      oneCheck := by simpa only [resultMem, resultAw, n] using hone
    }
    normalizedLenLe32 := hnLe32
    first := by simpa only [resultMem, resultAw, n] using hfirst
  }

/-- Concrete short normalized-suffix facts for an originally multi-limb modulus.  Solidity's two
aligned allocations, the operand copy, and the deployed scan discharge every memory predicate. -/
theorem preparedNormalizedWordReentryFactsAny
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLe32 : wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize <= 32)
    (hmodulusGtOne : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    NormalizedWordReentryFacts I
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize) := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  have hmodPos : 0 < modulusSize := by
    by_contra hnot
    have hz : modulusSize = 0 := Nat.eq_zero_of_not_pos hnot
    subst modulusSize
    simp only [model_bytesToNatPadded_zero_width] at hmodulusGtOne
    omega
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizeReentryGeometryAny I hb he hm hnormalize hcalldata
  have hresultFp : resultFp = fp + bytesAllocationSize n := by
    dsimp only [resultFp, fp, n, mem, aw, p]
    rfl
  have hpreserved := wideWordResultMemory_readOperandLenPadded I hb he hm
    (read := p + 32) (len := modulusSize)
    (by
      dsimp only [p]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by omega) (by omega) (by
      have h := Nat.add_le_add_left (bytesHeaderAndSize_le_allocation modulusSize)
        (operandModulusPtr baseSize exponentSize)
      simpa only [p, operandFreePtr, Nat.add_assoc] using h)
  have hpayload := operandCopiedModulusPayload I baseSize exponentSize modulusSize hb he hm
  have hcalldataRead : I.calldata.readWithPadding
      (96 + baseSize + exponentSize) modulusSize =
      Model.readPadded I.calldata (96 + baseSize + exponentSize) modulusSize :=
    readWithPadding_eq_model_readPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize (by omega) (by omega)
  have hmemoryValue : Model.bytesToNatPadded mem (p + 32) modulusSize =
      Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
    have hreadPrepared : mem.readWithPadding (p + 32) modulusSize =
        (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding
          (operandModulusPtr baseSize exponentSize + 32) modulusSize := by
      simpa only [mem, p] using hpreserved
    apply model_bytesToNatPadded_eq_of_readWithPadding (by
      dsimp only [p]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega) (by omega) (by omega)
    exact hreadPrepared.trans (hpayload.trans hcalldataRead.symm)
  apply geometry.completeWord hresultFp
    (by simpa only [wideBarrettNormalizedLenFor, n, mem, aw, p] using hnLe32)
  rw [hmemoryValue]
  exact hmodulusGtOne

/-- Compatibility specialization for an originally multi-limb modulus. -/
theorem preparedNormalizedWordReentryFacts
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (_hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLe32 : wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize <= 32)
    (hmodulusGtOne : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    NormalizedWordReentryFacts I
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize) :=
  preparedNormalizedWordReentryFactsAny I hb he hm hnormalize hnLe32
    hmodulusGtOne hcalldata

/-- Both normalized allocations preserve an original operand header below the allocator frontier,
and the enlarged active-memory frontier makes the corresponding guarded `MLOAD` exact. -/
theorem NormalizeReentryGeometry.wideLoadOriginalWord
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp read : Nat} {value : UInt256}
    (facts : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hsourceForCopy : p + barrettNormalizedOffset mem aw p m +
      barrettNormalizedLen mem aw p m <= fp + 32)
    (hreadAbove : 96 <= read)
    (hreadIn : read + 32 <= mem.size)
    (hbelowFp : read + 32 <= fp)
    (hbelowResultFp : read + 32 <= resultFp)
    (hvalue : mem.readWithPadding read 32 = UInt256.toByteArray value) :
    wideLoadWord (barrettNormalizedResultMem mem aw fp p m resultFp)
      (barrettNormalizedResultAw mem aw fp p m resultFp)
      (UInt256.ofNat read) = value := by
  let resultMem := barrettNormalizedResultMem mem aw fp p m resultFp
  let resultAw := barrettNormalizedResultAw mem aw fp p m resultFp
  have hreadPreserved : resultMem.readWithPadding read 32 =
      mem.readWithPadding read 32 := by
    apply barrettNormalizedResultMem_read_original_len
      facts.memSize facts.memLe facts.gap facts.normalizedLenPos hsourceForCopy
      facts.normalizedMemSize facts.resultGap (by decide) (by decide)
      hreadAbove hreadIn hbelowFp hbelowResultFp
  have hresultSize : resultMem.size = resultFp + 32 := by
    dsimp only [resultMem]
    unfold barrettNormalizedResultMem
    exact storeBytesLength_size
      (by rw [setFreePtr_size facts.normalizedMemSize]; exact facts.normalizedMemLe)
      (by rw [setFreePtr_size facts.normalizedMemSize]; exact facts.resultGap)
  have hreadWord : read < UInt256.size := by
    have hresultFp64 : resultFp < 2 ^ 64 := by
      exact lt_of_le_of_lt (Nat.le_add_right resultFp _) facts.resultBound
    exact lt_trans (by omega : read < 2 ^ 64) (by decide)
  have hreadNat : (UInt256.ofNat read).toNat = read :=
    UInt256.toNat_ofNat_of_lt hreadWord
  have hresultAwMul : (resultAw * UInt256.ofNat 32).toNat = 32 * resultAw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      dsimp only [resultAw]
      simpa [Nat.mul_comm] using facts.checksAw
  apply wideLoadWord_eq_of_read
  · rw [hreadNat, hresultSize]
    omega
  · intro h
    change (resultAw * UInt256.ofNat 32).toNat <= (UInt256.ofNat read).toNat at h
    rw [hresultAwMul, hreadNat] at h
    have hactive := facts.checksActive
    dsimp only [resultAw] at h
    omega
  · rw [hreadNat]
    exact hreadPreserved.trans hvalue

/-- Exact prepared execution for any bounded modulus whose normalized significant suffix fits in
one word.  The exposed selector is the actual leading-zero scan result; every
allocator, zero/one-check, operand-header, and active-memory premise is derived here. -/
theorem runPreparedBarrettNormalizedToWordExact
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {baseSize exponentSize modulusSize ret : Nat} {tail : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {steps gasUsed : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (hmodulusGtOne : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = UInt256.ofNat 0)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLe32 : wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize <= 32)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (htail : tail.length <= 993)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) (UInt256.ofNat 1183)
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc steps gasUsed) :
    exists steps', RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I)
      (UInt256.ofNat ret)
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) :: tail)
      (wideBarrettNormalizedFinalMemory I baseSize exponentSize modulusSize)
      (wideBarrettNormalizedFinalWords I baseSize exponentSize modulusSize)
      ByteArray.empty acc steps'
      (gasUsed + preparedBarrettNormalizedWordGasFromAw I
        (operandModulusActiveWords baseSize exponentSize modulusSize)
        baseSize exponentSize modulusSize
        (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
        (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)) := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  let resultAw := barrettNormalizedResultAw mem aw fp p modulusSize resultFp
  have hmodPos : 0 < modulusSize := by
    by_contra hnot
    have hz : modulusSize = 0 := Nat.eq_zero_of_not_pos hnot
    subst modulusSize
    simp only [model_bytesToNatPadded_zero_width] at hmodulusGtOne
    omega
  have wordFacts : NormalizedWordReentryFacts I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizedWordReentryFactsAny I hb he hm hnormalize hnLe32
        hmodulusGtOne hcalldata
  have geometry := wordFacts.toNormalizeReentryFacts.toNormalizeReentryGeometry
  have hresultFpEq : resultFp = fp + bytesAllocationSize n := by
    dsimp only [resultFp, fp, n, mem, aw, p]
    rfl
  have hmemSize : mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa only [mem] using wideWordResultMemory_size I hb he hm
  have hsourceForCopy : p + barrettNormalizedOffset mem aw p modulusSize + n <= fp + 32 := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize hmodPos
    have hnormalizeLocal : p + 32 < barrettScanStop mem aw p modulusSize := by
      simpa only [mem, aw, p] using hnormalize
    have hoffsetGe : 32 <= barrettNormalizedOffset mem aw p modulusSize := by
      dsimp only [barrettNormalizedOffset]
      omega
    have hsourceEnd : p + barrettNormalizedOffset mem aw p modulusSize + n =
        p + 32 + modulusSize := by
      dsimp only [n]
      omega
    rw [hsourceEnd]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hbaseOriginal : mem.readWithPadding operandBasePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize) := by
    have hpres := wideWordResultMemory_readOperand I hb he hm
      (read := operandBasePtr) (by unfold operandBasePtr; omega) (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    exact hpres.trans (operandCopiedMemory_readBaseLength I baseSize exponentSize modulusSize hb he)
  have hexponentOriginal : mem.readWithPadding (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
    have hpres := wideWordResultMemory_readOperand I hb he hm
      (read := operandExponentPtr baseSize) (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega) (by
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
    exact hpres.trans
      (operandCopiedMemory_readExponentLength I baseSize exponentSize modulusSize hb he)
  have hbaseLength : wideLoadWord
      (barrettNormalizedResultMem mem aw fp p modulusSize resultFp) resultAw
      (UInt256.ofNat operandBasePtr) = UInt256.ofNat baseSize := by
    apply geometry.wideLoadOriginalWord hsourceForCopy
      (by unfold operandBasePtr; omega)
    · rw [hmemSize]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · rw [hresultFpEq]
      dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · exact hbaseOriginal
  have hexponentLength : wideLoadWord
      (barrettNormalizedResultMem mem aw fp p modulusSize resultFp) resultAw
      (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize := by
    apply geometry.wideLoadOriginalWord hsourceForCopy
      (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    · rw [hmemSize]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · rw [hresultFpEq]
      dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · exact hexponentOriginal
  have hbaseActive : operandBasePtr + 32 + baseSize <= 32 * resultAw.toNat := by
    have hactive := geometry.checksActive
    change fp + 32 + n + 32 <= 32 * resultAw.toNat at hactive
    apply le_trans (b := fp + 32 + n + 32)
    · dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · exact hactive
  have hbaseDataActive : operandBasePtr + 64 <= 32 * resultAw.toNat := by
    have hactive := geometry.checksActive
    change fp + 32 + n + 32 <= 32 * resultAw.toNat at hactive
    apply le_trans (b := fp + 32 + n + 32)
    · dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · exact hactive
  have hexponentActive : wideExponentDataPtr baseSize + exponentSize + 32 <=
      32 * resultAw.toNat := by
    have hactive := geometry.checksActive
    change fp + 32 + n + 32 <= 32 * resultAw.toNat at hactive
    apply le_trans (b := fp + 32 + n + 32)
    · dsimp only [fp]
      unfold wideExponentDataPtr wideBarrettNormalizedFp operandFreePtr operandModulusPtr
        operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · exact hactive
  have hresultFpWord : resultFp + 32 < UInt256.size := by
    have hcover := bytesHeaderAndSize_le_allocation n
    have hbound : resultFp + bytesAllocationSize n < 2 ^ 64 := by
      simpa only [n] using geometry.resultBound
    exact lt_trans (by omega : resultFp + 32 < 2 ^ 64) (by decide)
  have hfpEndWord : fp + n + 31 < UInt256.size := by
    exact lt_of_lt_of_le (by omega) geometry.checksBound.le
  have hfpActive : fp + 64 <= 32 * resultAw.toNat := by
    have hactive := geometry.checksActive
    have hnPos := geometry.normalizedLenPos
    change fp + 32 + n + 32 <= 32 * resultAw.toNat at hactive
    change fp + 64 <= 32 * resultAw.toNat
    omega
  have hoffsetLe : barrettNormalizedOffset mem aw p modulusSize <= modulusSize + 31 := by
    have hbounds := barrettScanStopAt_bounds mem aw
      (barrettScanEnd p modulusSize) (barrettScanStart p) (by
        unfold barrettScanStart barrettScanEnd
        omega)
    have hupper : barrettScanStop mem aw p modulusSize <= p + modulusSize + 31 := by
      simpa [barrettScanStop, barrettScanEnd] using hbounds.2
    unfold barrettNormalizedOffset
    omega
  have hresultOffsetWord : operandFreePtr baseSize exponentSize modulusSize +
      barrettNormalizedOffset mem aw p modulusSize < UInt256.size := by
    apply lt_trans (b := 5000)
    · unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega
    · decide
  have hrun := runPreparedBarrettNormalizedWordExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (fp := fp) (resultFp := resultFp) (tail := tail)
    hb he hmodPos hm hmodulusGtOne hcalldata heven hnormalize
    geometry.fp96 geometry.allocationBound geometry.memSize geometry.memLe geometry.gap
    geometry.aw3 geometry.aw64 geometry.freePtr geometry.fp32 geometry.normalizedLenPos
    (lt_of_le_of_lt (by simpa only [n] using wordFacts.normalizedLenLe32) (by decide))
    (by simpa only [wideBarrettNormalizedLenFor, n, mem, aw, p] using hnLe32)
    geometry.modulusAccess geometry.modulusLength geometry.resultFp96 geometry.resultBound
    geometry.normalizedMemSize geometry.normalizedMemLe geometry.resultGap
    geometry.normalizedAw3 geometry.normalizedAw64 geometry.normalizedFreePtr
    geometry.checksBound geometry.checksActive geometry.checksAw geometry.lengthAfterResult
    wordFacts.zeroCheck wordFacts.oneCheck hfpEndWord hfpActive wordFacts.first
    (by simpa only [resultAw] using hbaseLength)
    (by simpa only [resultAw] using hexponentLength)
    (by simpa only [resultAw] using hbaseActive)
    (by simpa only [resultAw] using hbaseDataActive)
    (by simpa only [resultAw] using hexponentActive)
    hresultFpWord
    (by simpa only [resultAw] using geometry.resultPayloadActive)
    hresultOffsetWord hret htail rd0
  simpa only [fp, resultFp, wideBarrettNormalizedFinalMemory,
    wideBarrettNormalizedFinalWords, mem, aw, p, n] using hrun

/-- The normalized allocator/check state supplies all generic geometry needed by the recursive
direct selector. The remaining premises are the selected nonzero first byte, the preserved base
object, and the backend's fixed structural address-space reserve. -/
theorem normalizedDirectEntryFacts_of_reentry
    {I : ExecutionEnv} {mem : ByteArray} {aw : UInt256}
    {p m fp resultFp basePtr baseSize : Nat}
    (facts : NormalizeReentryGeometry I mem aw p m fp resultFp)
    (hresultFp : resultFp = fp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (hnLarge : 32 < barrettNormalizedLen mem aw p m)
    (hbasePos : 0 < baseSize)
    (hbaseBound : baseSize <= 1024)
    (hbasePtr96 : 96 <= basePtr)
    (hbaseSourceBefore : basePtr + 32 + baseSize <=
      resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (hbaseHeader : (barrettNormalizedResultMem mem aw fp p m resultFp).readWithPadding
      basePtr 32 = UInt256.toByteArray (UInt256.ofNat baseSize))
    (hbackend : directRemFp
        (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
        (barrettNormalizedLen mem aw p m) baseSize +
      wordArrayAllocationSize
        (Modexp.MultiLimbBarrettConversion.words (barrettNormalizedLen mem aw p m)) +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 < 2 ^ 64) :
    NormalizedDirectEntryFacts I
      (barrettNormalizedResultMem mem aw fp p m resultFp)
      (barrettNormalizedResultAw mem aw fp p m resultFp)
      fp resultFp basePtr baseSize (barrettNormalizedLen mem aw p m) := by
  let n := barrettNormalizedLen mem aw p m
  let resultMem := barrettNormalizedResultMem mem aw fp p m resultFp
  let resultAw := barrettNormalizedResultAw mem aw fp p m resultFp
  let free := resultFp + bytesAllocationSize n
  let words := Modexp.MultiLimbBarrettConversion.words n
  have hfirst := normalizedResult_first_nonzero facts (by omega)
  have hnBound : n <= m := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p m facts.modPos
    dsimp only [n]
    omega
  have hn1024 : n <= 1024 := le_trans hnBound facts.modBound
  have hresultSize : resultMem.size = resultFp + 32 := by
    dsimp only [resultMem]
    unfold barrettNormalizedResultMem
    apply storeBytesLength_size
    · rw [setFreePtr_size facts.normalizedMemSize]
      exact facts.normalizedMemLe
    · rw [setFreePtr_size facts.normalizedMemSize]
      exact facts.resultGap
  have hresultMem96 : 96 <= resultMem.size := by
    rw [hresultSize]
    exact le_trans facts.resultFp96 (Nat.le_add_right _ 32)
  have hresultMemLe : resultMem.size <= free := by
    rw [hresultSize]
    dsimp only [free, n]
    unfold bytesAllocationSize
    omega
  have hresultGap : free - resultMem.size < USize.size := by
    have hsmall : free - resultMem.size < 2 ^ 32 := by
      rw [hresultSize]
      dsimp only [free]
      unfold bytesAllocationSize
      omega
    exact lt_usize _ hsmall
  have hresultFree : resultMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat free) := by
    dsimp only [resultMem, free, n]
    unfold barrettNormalizedResultMem
    rw [storeBytesLength_read64]
    · exact setFreePtr_read64 facts.normalizedMemSize
    · rw [setFreePtr_size facts.normalizedMemSize]
      exact facts.normalizedMemSize
    · exact facts.resultFp96
    · rw [setFreePtr_size facts.normalizedMemSize]
      exact facts.resultGap
  have hresultAwFit : resultAw.toNat * 32 < UInt256.size := by
    dsimp only [resultAw]
    simpa [Nat.mul_comm] using facts.checksAw
  have hresultAwMul : (resultAw * UInt256.ofNat 32).toNat = 32 * resultAw.toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      exact hresultAwFit
  have hresultAw3 : 3 <= resultAw.toNat := by
    have hactive : fp + 32 + n + 32 <= 32 * resultAw.toNat := by
      simpa only [n, resultAw] using facts.checksActive
    omega
  have hresultAw64 : ¬ ((UInt256.ofNat 64) >= resultAw * UInt256.ofNat 32) := by
    intro h
    change (resultAw * UInt256.ofNat 32).toNat <= (UInt256.ofNat 64).toNat at h
    rw [hresultAwMul, show (UInt256.ofNat 64).toNat = 64 by decide] at h
    have hactive : fp + 32 + n + 32 <= 32 * resultAw.toNat := by
      simpa only [n, resultAw] using facts.checksActive
    omega
  have hactive : fp + 64 <= 32 * resultAw.toNat := by
    have hchecks : fp + 32 + n + 32 <= 32 * resultAw.toNat := by
      simpa only [n, resultAw] using facts.checksActive
    omega
  have hfp64 : fp + 32 < 2 ^ 64 := by
    have hbound : fp + bytesAllocationSize n < 2 ^ 64 := by
      simpa only [n] using facts.allocationBound
    unfold bytesAllocationSize at hbound
    omega
  have hpend : fp + n + 31 < UInt256.size := by
    have hbound : fp + 32 + n + 32 < UInt256.size := by
      simpa only [n] using facts.checksBound
    omega
  have hsourceBefore : fp + 32 + n <= free := by
    dsimp only [free]
    rw [hresultFp]
    unfold bytesAllocationSize
    omega
  have hfree96 : 96 <= free := by
    dsimp only [free]
    omega
  have hallocationBound : free + wordArrayAllocationSize words < 2 ^ 64 := by
    apply lt_of_le_of_lt (b :=
      directRemFp free n baseSize + wordArrayAllocationSize words +
        Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539)
    · unfold directRemFp directBaseFp
      omega
    · simpa only [free, n, words] using hbackend
  have hwordsPos : 0 < words := by
    dsimp only [words]
    unfold Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hallocationFit : free + wordArrayAllocationSize words + 31 < UInt256.size := by
    exact lt_trans (by omega : free + wordArrayAllocationSize words + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := Modexp.MultiLimbOddConversionSemantic.newWordArrayWords_range
    resultAw free words hwordsPos hresultAwFit hallocationFit
  have hallocatedSize :
      (Modexp.MultiLimbBarrettConversion.allocatedMemory resultMem free n).size = free + 32 := by
    unfold Modexp.MultiLimbBarrettConversion.allocatedMemory
    apply storeBytesLength_size
    · rw [setFreePtr_size hresultMem96]
      exact hresultMemLe
    · rw [setFreePtr_size hresultMem96]
      exact hresultGap
  have hallocatedHeader :
      (Modexp.MultiLimbBarrettConversion.allocatedMemory resultMem free n).readWithPadding
          fp 32 = UInt256.toByteArray (UInt256.ofNat n) := by
    have hstore := storeBytesLength_read_below_padded
      (mem := setFreePtr resultMem (free + wordArrayAllocationSize words))
      (fp := free) (n := words) (read := fp)
      (by rw [setFreePtr_size hresultMem96]; omega)
      (by dsimp only [free]; rw [hresultFp]; unfold bytesAllocationSize; omega)
      (by rw [setFreePtr_size hresultMem96]; exact hresultGap)
    have hfreeRead := setFreePtr_read_above_padded
      (mem := resultMem) (fp := free + wordArrayAllocationSize words) (read := fp)
      hresultMem96 facts.fp96
    simpa only [Modexp.MultiLimbBarrettConversion.allocatedMemory] using
      hstore.trans (hfreeRead.trans (by simpa only [n, resultMem] using
        facts.modulusHeaderAfterResult))
  have hallocatedAwMul :
      ((Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n) *
          UInt256.ofNat 32).toNat =
        32 * (Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n).toNat := by
    rw [umul_toNat]
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      omega
    · rw [show (UInt256.ofNat 32).toNat = 32 by decide]
      simpa only [Modexp.MultiLimbBarrettConversion.allocatedWords, words, Nat.mul_comm] using
        hrange.2
  have hfpWord : fp < UInt256.size := by omega
  have hallocatedGuard : ¬ (UInt256.ofNat fp >=
      Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n * UInt256.ofNat 32) := by
    intro h
    change (Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n *
      UInt256.ofNat 32).toNat <= (UInt256.ofNat fp).toNat at h
    rw [hallocatedAwMul, UInt256.toNat_ofNat_of_lt hfpWord] at h
    have hcover : free + 32 + 32 * words <=
        32 * (Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n).toNat := by
      simpa only [Modexp.MultiLimbBarrettConversion.allocatedWords] using hrange.1
    omega
  have hloadAllocated : wideLoadWord
      (Modexp.MultiLimbBarrettConversion.allocatedMemory resultMem free n)
      (Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n)
      (UInt256.ofNat fp) = UInt256.ofNat n := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt hfpWord, hallocatedSize]
      omega
    · exact hallocatedGuard
    · simpa only [UInt256.toNat_ofNat_of_lt hfpWord] using hallocatedHeader
  refine {
    modulusLarge := by simpa only [n] using hnLarge
    modulusBound := by simpa only [n] using hn1024
    p32 := facts.fp32
    p64 := hfp64
    pend := by simpa only [n] using hpend
    source96 := le_trans facts.fp96 (Nat.le_add_right _ 32)
    sourceBefore := by simpa only [n, free] using hsourceBefore
    active := by simpa only [resultAw] using hactive
    first := by simpa only [n, resultMem, resultAw] using hfirst
    freePtr96 := by simpa only [n, free] using hfree96
    allocationBound := by simpa only [n, free, words] using hallocationBound
    memSize := by simpa only [resultMem] using hresultMem96
    memLe := by simpa only [n, resultMem, free] using hresultMemLe
    gap := by simpa only [n, resultMem, free] using hresultGap
    aw3 := by simpa only [resultAw] using hresultAw3
    aw64 := by simpa only [resultAw] using hresultAw64
    awFit := by simpa only [resultAw] using hresultAwFit
    freePtr := by simpa only [n, resultMem, free] using hresultFree
    calldataBound := facts.calldataBound
    accessAllocated := by
      have hcover : free + 32 + 32 * words <=
          32 * (Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n).toNat := by
        simpa only [Modexp.MultiLimbBarrettConversion.allocatedWords] using hrange.1
      change (UInt256.ofNat fp).toNat + 32 <=
        32 * (Modexp.MultiLimbBarrettConversion.allocatedWords resultAw free n).toNat
      rw [UInt256.toNat_ofNat_of_lt hfpWord]
      exact le_trans (by omega : fp + 32 <= free + 32 + 32 * words) hcover
    loadAllocated := by simpa only [n, resultMem, resultAw, free] using hloadAllocated
    basePos := hbasePos
    baseBound := hbaseBound
    basePtr96 := hbasePtr96
    baseSourceBefore := by simpa only [n] using hbaseSourceBefore
    baseHeader := by simpa only [resultMem] using hbaseHeader
    backendWorkspace := by simpa only [n] using hbackend
  }

/-- The concrete prepared normalized state supplies the complete recursive direct-entry contract.
The base header is preserved through both allocator writes, and the fixed backend reserve follows
from the public 1024-byte input bounds. -/
theorem preparedNormalizedDirectEntryFacts
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLarge : 32 < wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    NormalizedDirectEntryFacts I
      (barrettNormalizedResultMem
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize
        (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize))
      (barrettNormalizedResultAw
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize
        (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize))
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize
      (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hresultFp : resultFp = fp + bytesAllocationSize n := by
    dsimp only [resultFp, fp, n, mem, aw, p]
    rfl
  have hmemSize : mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa only [mem] using wideWordResultMemory_size I hb he hm
  have hbaseMem : mem.readWithPadding operandBasePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize) := by
    have hpres := wideWordResultMemory_readOperand I hb he hm
      (read := operandBasePtr) (by unfold operandBasePtr; omega) (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    exact hpres.trans (operandCopiedMemory_readBaseLength I baseSize exponentSize modulusSize hb he)
  have hsourceForCopy : p + barrettNormalizedOffset mem aw p modulusSize + n <= fp + 32 := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    have hoffsetGe : 32 <= barrettNormalizedOffset mem aw p modulusSize := by
      unfold barrettNormalizedOffset
      have hbounds := barrettScanStopAt_bounds mem aw
        (barrettScanEnd p modulusSize) (barrettScanStart p) (by
          unfold barrettScanStart barrettScanEnd
          omega)
      have hlower : p + 32 <= barrettScanStop mem aw p modulusSize := by
        simpa [barrettScanStop, barrettScanStart] using hbounds.1
      omega
    have hsourceEnd : p + barrettNormalizedOffset mem aw p modulusSize + n =
        p + 32 + modulusSize := by
      dsimp only [n]
      omega
    rw [hsourceEnd]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hbaseReadIn : operandBasePtr + 32 <= mem.size := by
    rw [hmemSize]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hbaseBelowFp : operandBasePtr + 32 <= fp := by
    dsimp only [fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hbaseBelowResult : operandBasePtr + 32 <= resultFp := by
    rw [hresultFp]
    omega
  have hbaseResult :
      (barrettNormalizedResultMem mem aw fp p modulusSize resultFp).readWithPadding
          operandBasePtr 32 = UInt256.toByteArray (UInt256.ofNat baseSize) := by
    have hpres := barrettNormalizedResultMem_read_original_len
      (mem := mem) (aw := aw) (fp := fp) (p := p) (m := modulusSize)
      (resultFp := resultFp) (read := operandBasePtr) (len := 32)
      geometry.memSize geometry.memLe geometry.gap geometry.normalizedLenPos
      hsourceForCopy geometry.normalizedMemSize geometry.resultGap
      (by decide) (by decide) (by unfold operandBasePtr; omega)
      hbaseReadIn hbaseBelowFp hbaseBelowResult
    exact hpres.trans hbaseMem
  have hnLe : n <= modulusSize := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    dsimp only [n]
    omega
  have hn1024 : n <= 1024 := hnLe.trans hm
  have hfreeLe : resultFp + bytesAllocationSize n <= 6464 := by
    rw [hresultFp]
    dsimp only [fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hwords : Modexp.MultiLimbBarrettConversion.words n <= 32 := by
    unfold Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hbaseWords : MultiLimbReduceBase.baseWords baseSize
      (Modexp.MultiLimbBarrettConversion.words n) <= 32 := by
    unfold MultiLimbReduceBase.baseWords MultiLimbReduceBase.naturalWords
      Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hbackend : directRemFp (resultFp + bytesAllocationSize n) n baseSize +
      wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words n) +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show directRemFp (resultFp + bytesAllocationSize n) n baseSize +
          wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words n) +
          Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 <= 32768 by
        unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
          Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes
        omega)
      (by decide)
  apply normalizedDirectEntryFacts_of_reentry geometry hresultFp
    (by simpa only [wideBarrettNormalizedLenFor, n, mem, aw, p] using hnLarge)
    hbasePos hb (by unfold operandBasePtr; omega)
  · rw [hresultFp]
    dsimp only [fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  · simpa only [mem, aw, fp, p, resultFp] using hbaseResult
  · exact hbackend

/-- Exposed selection of the normalized recursive call. `reentrySteps` is the concrete absolute
step index selected by the normalization checks; gas remains the exact executable path expression. -/
structure NormalizedSelection
    (I : ExecutionEnv) (g : Sat256) (s0 : State) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (mem : ByteArray) (aw : UInt256) (gasUsed p m fp resultFp basePtr baseSize : Nat)
    (exponent retBar result ret : Nat) (tail : List UInt256) where
  reentrySteps : Nat
  direct : DirectSelection I g s0 rdata acc
    (barrettNormalizedResultMem mem aw fp p m resultFp)
    (barrettNormalizedResultAw mem aw fp p m resultFp)
    reentrySteps (gasUsed + barrettNormalizeReentryChecksGas mem aw fp p m resultFp)
    fp (resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (barrettNormalizedLen mem aw p m) basePtr baseSize (UInt256.ofNat exponent)
    (UInt256.ofNat resultFp) (UInt256.ofNat 1808)
    (UInt256.ofNat (barrettNormalizedOffset mem aw p m))
    (UInt256.ofNat (barrettNormalizedLen mem aw p m) :: UInt256.ofNat result ::
      UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)

/-- Compose the real PC 1592 normalization/allocation prefix with construction of the complete
direct multi-limb selector at the recursive PC 1592 entry. -/
theorem normalizedSelection_exists
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p m fp resultFp basePtr baseSize exponent retBar result ret : Nat}
    {tail : List UInt256}
    (normalizeFacts : NormalizeReentryFacts I mem aw p m fp resultFp)
    (directFacts : NormalizedDirectEntryFacts I
      (barrettNormalizedResultMem mem aw fp p m resultFp)
      (barrettNormalizedResultAw mem aw fp p m resultFp)
      fp resultFp basePtr baseSize (barrettNormalizedLen mem aw p m))
    (hdepth : tail.length <= 979)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) (UInt256.ofNat 1592)
      (UInt256.ofNat p :: UInt256.ofNat m :: UInt256.ofNat retBar ::
        UInt256.ofNat result :: UInt256.ofNat exponent :: UInt256.ofNat basePtr ::
        UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    Nonempty (NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I) rdata acc
      mem aw gasUsed p m fp resultFp basePtr baseSize exponent retBar result ret tail) := by
  obtain ⟨kReentry, rdReentry⟩ := reachBarrettNormalizeReentryChecks
    (p := p) (m := m) (retBar := retBar) (result := result) (exp := exponent)
    (base := basePtr) (ret := ret) (fp := fp) (resultFp := resultFp)
    normalizeFacts.modPos normalizeFacts.modBound normalizeFacts.p32 normalizeFacts.pend
    normalizeFacts.activeEnd normalizeFacts.normalize normalizeFacts.fp96
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.allocationBound)
    normalizeFacts.memSize normalizeFacts.memLe normalizeFacts.gap normalizeFacts.aw3
    normalizeFacts.aw64 normalizeFacts.freePtr normalizeFacts.calldataBound normalizeFacts.fp32
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.normalizedLenPos)
    (by simpa [barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.modulusAccess)
    (by simpa [barrettNormalizedMem, barrettNormalizedAw, barrettNormalizedLen,
      barrettNormalizedOffset] using normalizeFacts.modulusLength)
    normalizeFacts.resultFp96
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using normalizeFacts.resultBound)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.normalizedMemSize)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.normalizedMemLe)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.resultGap)
    (by simpa [barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.normalizedAw3)
    (by simpa [barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.normalizedAw64)
    (by simpa [barrettNormalizedMem, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.normalizedFreePtr)
    (by simpa [barrettNormalizedLen, barrettNormalizedOffset] using normalizeFacts.checksBound)
    (by simpa [barrettNormalizedResultAw, barrettNormalizedAw, barrettNormalizedLen,
      barrettNormalizedOffset] using normalizeFacts.checksActive)
    (by simpa [barrettNormalizedResultAw, barrettNormalizedAw, barrettNormalizedLen,
      barrettNormalizedOffset] using normalizeFacts.checksAw)
    (by simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
      barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.lengthAfterResult)
    (by simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
      barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.zeroCheck)
    (by simpa [barrettNormalizedResultMem, barrettNormalizedResultAw, barrettNormalizedMem,
      barrettNormalizedAw, barrettNormalizedLen, barrettNormalizedOffset] using
      normalizeFacts.oneCheck)
    (by omega) rd0
  have rdReentry' : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I)
      (UInt256.ofNat 1592)
      (UInt256.ofNat fp :: UInt256.ofNat (barrettNormalizedLen mem aw p m) ::
        UInt256.ofNat 1808 :: UInt256.ofNat resultFp :: UInt256.ofNat exponent ::
        UInt256.ofNat basePtr :: UInt256.ofNat (barrettNormalizedOffset mem aw p m) ::
        UInt256.ofNat (barrettNormalizedLen mem aw p m) :: UInt256.ofNat result ::
        UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
      (barrettNormalizedResultMem mem aw fp p m resultFp)
      (barrettNormalizedResultAw mem aw fp p m resultFp)
      rdata acc kReentry
      (gasUsed + barrettNormalizeReentryChecksGas mem aw fp p m resultFp) := by
    simpa [barrettNormalizeReentryChecksGas, barrettNormalizedResultMem,
      barrettNormalizedResultAw, barrettNormalizedMem, barrettNormalizedAw,
      barrettNormalizedLen, barrettNormalizedOffset, Nat.add_assoc,
      show UInt256.ofNat 1808 = (⟨1808⟩ : UInt256) by native_decide] using rdReentry
  obtain ⟨selected⟩ := directSelection_exists
    (p := fp)
    (modulusFp := resultFp + bytesAllocationSize (barrettNormalizedLen mem aw p m))
    (modulusSize := barrettNormalizedLen mem aw p m)
    (basePtr := basePtr) (baseSize := baseSize) (exponentPtr := exponent)
    (resultPtr := resultFp) (retBar := 1808)
    (ret := barrettNormalizedOffset mem aw p m)
    (tail := UInt256.ofNat (barrettNormalizedLen mem aw p m) :: UInt256.ofNat result ::
      UInt256.ofNat retBar :: UInt256.ofNat ret :: tail)
    directFacts.modulusLarge directFacts.modulusBound directFacts.p32 directFacts.p64
    directFacts.pend directFacts.source96 directFacts.sourceBefore directFacts.active
    directFacts.first directFacts.freePtr96 directFacts.allocationBound directFacts.memSize
    directFacts.memLe directFacts.gap directFacts.aw3 directFacts.aw64 directFacts.awFit
    directFacts.freePtr directFacts.calldataBound directFacts.accessAllocated
    directFacts.loadAllocated directFacts.basePos directFacts.baseBound directFacts.basePtr96
    directFacts.baseSourceBefore directFacts.baseHeader directFacts.backendWorkspace
    (by simp only [List.length_cons]; omega) rdReentry'
  exact ⟨{ reentrySteps := kReentry, direct := selected }⟩

/-- Concrete normalized multi-limb selector from the prepared operand/result state.  All recursive
allocator and entry facts are constructed from the bounded calldata layout. -/
theorem preparedNormalizedSelection_exists
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (hb : baseSize <= 1024) (he : exponentSize <= 1024) (hm : modulusSize <= 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLarge : 32 < wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length <= 979)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) (UInt256.ofNat 1592)
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat retBar ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc steps gasUsed) :
    Nonempty (NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail) := by
  have geometry := preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have complete := geometry.complete (by
    simpa only [wideBarrettNormalizedLenFor] using hnLarge)
  have direct := preparedNormalizedDirectEntryFacts I hb he hm hbasePos hmodLarge
    hnormalize hnLarge hcalldata
  exact normalizedSelection_exists complete direct hdepth rd0

/-- The normalized recursive source still contains the prepared exponent-array header. -/
theorem preparedNormalizedExponentHeader
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    (barrettNormalizedResultMem
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
    ).readWithPadding (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hsourceForCopy : p + barrettNormalizedOffset mem aw p modulusSize + n ≤ fp + 32 := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    have hoffset : 32 ≤ barrettNormalizedOffset mem aw p modulusSize := by
      unfold barrettNormalizedOffset
      dsimp only [p, mem, aw]
      omega
    have hend : p + barrettNormalizedOffset mem aw p modulusSize + n =
        p + 32 + modulusSize := by
      dsimp only [n]
      omega
    rw [hend]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hread := geometry.readOriginal (read := operandExponentPtr baseSize) (len := 32)
    hsourceForCopy (by omega) (by omega)
    (show 96 ≤ operandExponentPtr baseSize by
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by
      rw [show mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 by
        simpa only [mem] using wideWordResultMemory_size I hb he hm]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    (by
      dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega)
    (by
      dsimp only [resultFp, fp, n, mem, aw, p]
      unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp operandFreePtr
        operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  have horiginal : mem.readWithPadding (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
    have hpres := wideWordResultMemory_readOperand I hb he hm
      (read := operandExponentPtr baseSize)
      (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
      (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    exact hpres.trans
      (operandCopiedMemory_readExponentLength I baseSize exponentSize modulusSize hb he)
  exact hread.trans horiginal

/-- A prepared normalized selector presents the copied exponent header unchanged to the recursive
Barrett exponent setup. -/
theorem NormalizedSelection.initializedExponentHeader
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    (initializedMemory selected.direct.constant.finalMemory
      (accumulatorFp selected.direct.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words
          (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)))
      (Modexp.MultiLimbBarrettConversion.words
        (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize))
    ).readWithPadding (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
  have hframe := selected.direct.initializedReadBelow (operandExponentPtr baseSize)
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by
      unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp
        operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  have hheader := preparedNormalizedExponentHeader I hb he hm hmodLarge hnormalize hcalldata
  simpa only [wideBarrettNormalizedLenFor] using hframe.trans hheader

/-- Every exponent byte in the initialized recursive selector is still the corresponding byte
of the trusted padded calldata field. The proof crosses both normalization allocations and the
direct Barrett setup; no execution result is assumed. -/
theorem NormalizedSelection.initializedExponentByte
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (start : Nat) (hstart : start < exponentSize) :
    (initializedMemory selected.direct.constant.finalMemory
      (accumulatorFp selected.direct.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words
          (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)))
      (Modexp.MultiLimbBarrettConversion.words
        (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize))
    ).readWithPadding (operandExponentPtr baseSize + 32 + start) 1 =
      I.calldata.readWithPadding (96 + baseSize + start) 1 := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  let normalized := barrettNormalizedResultMem mem aw fp p modulusSize resultFp
  let initialized := initializedMemory selected.direct.constant.finalMemory
    (accumulatorFp selected.direct.reduced.finalFreePtr
      (Modexp.MultiLimbBarrettConversion.words n))
    (Modexp.MultiLimbBarrettConversion.words n)
  let read := operandExponentPtr baseSize + 32 + start
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hsourceForCopy : p + barrettNormalizedOffset mem aw p modulusSize + n ≤ fp + 32 := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    have hoffset : 32 ≤ barrettNormalizedOffset mem aw p modulusSize := by
      unfold barrettNormalizedOffset
      dsimp only [p, mem, aw]
      omega
    have hend : p + barrettNormalizedOffset mem aw p modulusSize + n =
        p + 32 + modulusSize := by
      dsimp only [n]
      omega
    rw [hend]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hread64 : read < 2 ^ 64 := by
    dsimp only [read]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hframe32 := selected.direct.initializedReadBelow read
    (by
      dsimp only [read]
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by
      dsimp only [read, resultFp, n, mem, aw, p]
      unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp operandFreePtr
        operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
  have hnormalizedOne : initialized.readWithPadding read 1 =
      normalized.readWithPadding read 1 := by
    calc
      initialized.readWithPadding read 1 =
          (initialized.readWithPadding read 32).extract 0 1 := by
            symm
            exact readWithPadding_window initialized read 32 0 1 hread64 (by decide)
              (by simpa using hread64) (by decide) (by omega)
      _ = (normalized.readWithPadding read 32).extract 0 1 := by
            exact congrArg (fun bs : ByteArray => bs.extract 0 1)
              (by simpa only [initialized, normalized, n, wideBarrettNormalizedLenFor]
                using hframe32)
      _ = normalized.readWithPadding read 1 := by
            exact readWithPadding_window normalized read 32 0 1 hread64 (by decide)
              (by simpa using hread64) (by decide) (by omega)
  have hnormalizedOriginal : normalized.readWithPadding read 1 =
      mem.readWithPadding read 1 := by
    exact geometry.readOriginal hsourceForCopy (by decide) (by decide)
      (by
        dsimp only [read]
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by
        rw [show mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 by
          simpa only [mem] using wideWordResultMemory_size I hb he hm]
        dsimp only [read]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by
        dsimp only [read, fp]
        unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
          operandBasePtr bytesAllocationSize
        omega)
      (by
        dsimp only [read, resultFp, fp, n, mem, aw, p]
        unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp operandFreePtr
          operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
  have hwideOriginal : mem.readWithPadding read 1 =
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding read 1 := by
    exact wideWordResultMemory_readOperandLen I hb he hm
      (by
        dsimp only [read]
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide) (by decide)
      (by
        have hsize := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
        apply le_trans (b := operandModulusPtr baseSize exponentSize + 32)
        · dsimp only [read]
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega
        · exact hsize)
      (by
        dsimp only [read]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
  have hwindow := operandCopiedExponentWindow I baseSize exponentSize modulusSize start 1
    hb he (by omega)
  have hcalldataRead : Model.readPadded I.calldata (96 + baseSize + start) 1 =
      I.calldata.readWithPadding (96 + baseSize + start) 1 := by
    symm
    exact readWithPadding_eq_model_readPadded I.calldata (96 + baseSize + start) 1
      (by omega) (by decide)
  simpa only [initialized, n, wideBarrettNormalizedLenFor, read] using
    hnormalizedOne.trans
      (hnormalizedOriginal.trans (hwideOriginal.trans (hwindow.trans hcalldataRead)))

/-- The prepared normalized selector satisfies every checked exponent load bound in one concrete
frame. The bounds follow from the Solidity operand layout and the `≤ 1024` input limits. -/
theorem NormalizedSelection.exponentAccessFrame
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    Modexp.MultiLimbBarrettExponentLoop.BarrettExponentAccessFrame
      (initializedMemory selected.direct.constant.finalMemory rFp k)
      (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat exponentSize)
      (UInt256.ofNat rFp) := by
  dsimp only
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  have hexponentPtr : operandExponentPtr baseSize < UInt256.size := by
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    exact lt_of_le_of_lt (by omega) (by decide : 1216 < UInt256.size)
  have hexponentSize : exponentSize < UInt256.size :=
    lt_trans (by omega : exponentSize < 2 ^ 64) (by norm_num [UInt256.size])
  have hrFp64 : rFp < 2 ^ 64 := by
    have hbackend := selected.direct.backendWorkspace
    have hfinalFree :=
      Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
        selected.direct.entryFacts selected.direct.reduced
    have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
        (accumulatorFp selected.direct.reduced.finalFreePtr k + wordArrayAllocationSize k) k <
          2 ^ 64 := by
      apply lt_of_le_of_lt
        (scratchEnd_afterAccumulator_le_reserve selected.direct.reduced.finalFreePtr k
          selected.direct.entryFacts.divisorBound)
      dsimp only [k, n, wideBarrettNormalizedLenFor] at hbackend hfinalFree ⊢
      omega
    apply lt_trans (b := Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (accumulatorFp selected.direct.reduced.finalFreePtr k + wordArrayAllocationSize k) k)
    · dsimp only [rFp]
      unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
        Modexp.MultiLimbBarrettReusedCall.callResultFp wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    · exact hscratch
  have hrFp256 : rFp < UInt256.size :=
    lt_trans hrFp64 (by norm_num [UInt256.size])
  have hheader := selected.initializedExponentHeader hb he hm hmodLarge hnormalize hcalldata
  have hmemSize : 96 ≤ selected.direct.constant.finalMemory.size := by
    rw [selected.direct.constant.finalMemorySize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemLe : selected.direct.constant.finalMemory.size ≤ rFp := by
    rw [selected.direct.constant.finalMemorySize]
    rfl
  have hgap : rFp - selected.direct.constant.finalMemory.size < USize.size := by
    have hmemEq : selected.direct.constant.finalMemory.size = rFp := by
      rw [selected.direct.constant.finalMemorySize]
      rfl
    rw [hmemEq, Nat.sub_self]
    native_decide
  have hinitialSize := initializedMemory_size selected.direct.constant.finalMemory rFp k
    hmemSize hmemLe hgap
  have hexponentBelow : operandExponentPtr baseSize + 32 ≤ rFp := by
    apply le_trans (b := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
      bytesAllocationSize n)
    · dsimp only [n]
      unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp operandFreePtr
        operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · apply le_trans (b := selected.direct.reduced.finalFreePtr)
      · apply le_trans (b := directRemFp
            (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
              bytesAllocationSize n) n baseSize + wordArrayAllocationSize k)
        · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.direct.reduced
      · dsimp only [rFp]
        unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega
  refine {
    exponentBase := ?_
    exponentBelowAccumulator := ?_
    headerConcrete := ?_
    header := ?_
    exponentFit := ?_
    byteFit := ?_ }
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr,
      UInt256.toNat_ofNat_of_lt hrFp256]
    exact hexponentBelow
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr, hinitialSize]
    exact hexponentBelow.trans (Nat.le_add_right rFp 64)
  · simpa only [n, k, rFp, wideBarrettNormalizedLenFor,
      UInt256.toNat_ofNat_of_lt hexponentPtr] using hheader
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr]
    exact lt_trans (by
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega : operandExponentPtr baseSize + 32 + 31 < 2 ^ 64)
      (by norm_num [UInt256.size])
  · intro idx hidx
    have hidxNat : idx.toNat < exponentSize := by
      have hlt : idx < UInt256.ofNat exponentSize := by
        by_contra hn
        apply hidx
        simp [UInt256.lt, hn]
        rfl
      change idx.toNat < (UInt256.ofNat exponentSize).toNat at hlt
      rw [UInt256.toNat_ofNat_of_lt hexponentSize] at hlt
      exact hlt
    have hinner : idx.toNat + operandExponentPtr baseSize < UInt256.size :=
      lt_trans (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega : idx.toNat + operandExponentPtr baseSize < 2 ^ 64)
        (by norm_num [UInt256.size])
    have houter : 32 + (idx.toNat + operandExponentPtr baseSize) < UInt256.size :=
      lt_trans (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega : 32 + (idx.toNat + operandExponentPtr baseSize) < 2 ^ 64)
        (by norm_num [UInt256.size])
    unfold Modexp.MultiLimbExponentTrace.exponentByteAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide, uadd_toNat,
      UInt256.toNat_ofNat_of_lt hexponentPtr, Nat.mod_eq_of_lt hinner,
      Nat.mod_eq_of_lt houter]
    exact lt_trans (by
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega : 32 + (idx.toNat + operandExponentPtr baseSize) + 32 + 31 < 2 ^ 64)
      (by norm_num [UInt256.size])

/-- The complete fresh exponent selector on a prepared normalized recursive branch satisfies the
trusted calldata alignment contract constructively. -/
theorem NormalizedSelection.exponentAlignment
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n) n baseSize))
        (UInt256.ofNat
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n))
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected) :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
      bytesAllocationSize n
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I baseSize exponentSize
      (UInt256.ofNat exponentSize).toNat 8 k k (rFp + wordArrayAllocationSize k)
      (UInt256.ofNat rFp) (UInt256.ofNat (directRemFp modulusFp n baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
      (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat exponentSize)
      (initializedMemory selected.direct.constant.finalMemory rFp k)
      (allocatedWords selected.direct.constant.finalWords rFp k) exponentSelected := by
  dsimp only
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
    bytesAllocationSize n
  let remFp := directRemFp modulusFp n baseSize
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let loopFp := rFp + wordArrayAllocationSize k
  let exponent := UInt256.ofNat (operandExponentPtr baseSize)
  let expLen := UInt256.ofNat exponentSize
  let r := UInt256.ofNat rFp
  let a := UInt256.ofNat remFp
  let modulus := UInt256.ofNat modulusFp
  let mu := UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k)
  let initialMem := initializedMemory selected.direct.constant.finalMemory rFp k
  let initialAw := allocatedWords selected.direct.constant.finalWords rFp k
  have hbackend := selected.direct.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, modulusFp, k, n, wideBarrettNormalizedLenFor] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤
      selected.direct.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.direct.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.direct.entryFacts selected.direct.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.direct.reduced.finalFreePtr k
        selected.direct.entryFacts.divisorBound)
    dsimp only [loopFp, rFp, remFp, modulusFp, k, n, wideBarrettNormalizedLenFor]
      at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.direct.entryFacts hreduceWorkspace
    selected.direct.reduced selected.direct.constant hconstantAfter hscratch
    selected.direct.calldataBound selected.direct.baseInput_eq selected.direct.modulus_eq
  have access := selected.exponentAccessFrame hb he hm hmodLarge hnormalize hcalldata
  have hrFp64 : rFp < 2 ^ 64 := by
    dsimp only [loopFp] at hscratch
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    omega
  have hrFp256 : rFp < UInt256.size :=
    lt_trans hrFp64 (by norm_num [UInt256.size])
  have hexponentSize : exponentSize < UInt256.size :=
    lt_trans (by omega : exponentSize < 2 ^ 64) (by norm_num [UInt256.size])
  have hexponentPtr : operandExponentPtr baseSize < UInt256.size := by
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    exact lt_of_le_of_lt (by omega) (by decide : 1216 < UInt256.size)
  have haddress : ∀ s, s < exponentSize →
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent
        (UInt256.ofNat s)).toNat = exponent.toNat + 32 + s := by
    intro s hs
    have hsWord : s < UInt256.size := lt_trans hs hexponentSize
    have hinner : s + operandExponentPtr baseSize < UInt256.size := by
      apply lt_trans (b := 2 ^ 64)
      · unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · norm_num [UInt256.size]
    have houter : 32 + (s + operandExponentPtr baseSize) < UInt256.size := by
      apply lt_trans (b := 2 ^ 64)
      · unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega
      · norm_num [UInt256.size]
    unfold Modexp.MultiLimbExponentTrace.exponentByteAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide, uadd_toNat,
      UInt256.toNat_ofNat_of_lt hsWord, UInt256.toNat_ofNat_of_lt hexponentPtr,
      Nat.mod_eq_of_lt hinner, Nat.mod_eq_of_lt houter]
    omega
  have hpayloadBelow : exponent.toNat + 32 + exponentSize + 31 ≤ r.toNat := by
    rw [show exponent.toNat = operandExponentPtr baseSize by
        dsimp only [exponent]; rw [UInt256.toNat_ofNat_of_lt hexponentPtr],
      show r.toNat = rFp by
        dsimp only [r]; rw [UInt256.toNat_ofNat_of_lt hrFp256]]
    apply le_trans (b := modulusFp)
    · dsimp only [modulusFp, n]
      unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp operandFreePtr
        operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · apply le_trans (b := remFp + wordArrayAllocationSize k)
      · dsimp only [remFp, modulusFp]
        unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      · apply le_trans (b := selected.direct.reduced.finalFreePtr)
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.direct.reduced
        · dsimp only [rFp]
          unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega
  have hconstantSize : selected.direct.constant.finalMemory.size = rFp := by
    rw [selected.direct.constant.finalMemorySize]
    rfl
  have hinitialSize : initialMem.size = rFp + 64 := by
    apply initializedMemory_size
    · rw [hconstantSize]
      have hr := invariant.rBase
      change 96 ≤ (UInt256.ofNat rFp).toNat at hr
      rw [UInt256.toNat_ofNat_of_lt hrFp256] at hr
      exact hr
    · rw [hconstantSize]
    · rw [hconstantSize, Nat.sub_self]
      native_decide
  have hpayloadConcrete : exponent.toNat + 32 + exponentSize + 31 ≤ initialMem.size := by
    rw [hinitialSize]
    have hrNat : r.toNat = rFp := by
      dsimp only [r]
      rw [UInt256.toNat_ofNat_of_lt hrFp256]
    rw [hrNat] at hpayloadBelow
    omega
  have haddress64 : exponent.toNat + 32 + exponentSize < 2 ^ 64 := by
    rw [show exponent.toNat = operandExponentPtr baseSize by
      dsimp only [exponent]; rw [UInt256.toNat_ofNat_of_lt hexponentPtr]]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hcalldataBound : 96 + baseSize + exponentSize < 2 ^ 64 := by omega
  have hsource : ∀ s, s < exponentSize →
      initialMem.readWithPadding (exponent.toNat + 32 + s) 1 =
        I.calldata.readWithPadding (96 + baseSize + s) 1 := by
    intro s hs
    have hbyte := selected.initializedExponentByte hb he hm hmodLarge hnormalize hcalldata
      s hs
    simpa only [initialMem, exponent, n, k, rFp, wideBarrettNormalizedLenFor,
      UInt256.toNat_ofNat_of_lt hexponentPtr] using hbyte
  unfold Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup at hselect
  exact Modexp.MultiLimbBarrettResultSemantic.selectFreshBarrettLoopSetup_modelAlignmentFramed
    invariant access rfl hexponentSize haddress hpayloadConcrete hpayloadBelow haddress64
    hcalldataBound hsource hselect

/-- The complete fresh exponent selector on the prepared normalized state is valid without
external path callbacks.  The selected leading scan supplies its own terminal guard, and the
allocator header supplies the exact recursive scratch pointer. -/
theorem NormalizedSelection.exponentValid
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n) n baseSize))
        (UInt256.ofNat
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n))
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected) :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
      bytesAllocationSize n
    Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I k k
        (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp n baseSize)) (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat exponentSize)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k) exponentSelected ∧
      rFp + 64 ≤ exponentSelected.memory.size ∧
      rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat ∧
      exponentSelected.activeWords.toNat * 32 < UInt256.size ∧
      Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize := by
  dsimp only
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
    bytesAllocationSize n
  let remFp := directRemFp modulusFp n baseSize
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let loopFp := rFp + wordArrayAllocationSize k
  let exponent := UInt256.ofNat (operandExponentPtr baseSize)
  let expLen := UInt256.ofNat exponentSize
  let r := UInt256.ofNat rFp
  let a := UInt256.ofNat remFp
  let modulus := UInt256.ofNat modulusFp
  let mu := UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k)
  let initialMem := initializedMemory selected.direct.constant.finalMemory rFp k
  let initialAw := allocatedWords selected.direct.constant.finalWords rFp k
  have hbackend := selected.direct.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, modulusFp, k, n, wideBarrettNormalizedLenFor] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤
      selected.direct.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.direct.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.direct.entryFacts selected.direct.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.direct.reduced.finalFreePtr k
        selected.direct.entryFacts.divisorBound)
    dsimp only [loopFp, rFp, remFp, modulusFp, k, n, wideBarrettNormalizedLenFor]
      at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.direct.entryFacts hreduceWorkspace
    selected.direct.reduced selected.direct.constant hconstantAfter hscratch
    selected.direct.calldataBound selected.direct.baseInput_eq selected.direct.modulus_eq
  have access := selected.exponentAccessFrame hb he hm hmodLarge hnormalize hcalldata
  have hrFp64 : rFp < 2 ^ 64 := by
    dsimp only [loopFp] at hscratch
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    omega
  have hrFp256 : rFp < UInt256.size :=
    lt_trans hrFp64 (by norm_num [UInt256.size])
  have hconstantSize : selected.direct.constant.finalMemory.size = rFp := by
    rw [selected.direct.constant.finalMemorySize]
    rfl
  have hrFp96 : 96 ≤ rFp := by
    have hr := invariant.rBase
    change 96 ≤ (UInt256.ofNat rFp).toNat at hr
    rw [UInt256.toNat_ofNat_of_lt hrFp256] at hr
    exact hr
  have hfreeRead : initialMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat loopFp) := by
    dsimp only [initialMem, loopFp]
    apply Modexp.MultiLimbBarrettAccumulator.initializedMemory_freePointer
    · rw [hconstantSize]
      exact hrFp96
    · rw [hconstantSize]
    · rw [hconstantSize, Nat.sub_self]
      native_decide
    · exact hrFp96
  have hlength : Modexp.MultiLimbExponentTrace.exponentArrayLength initialMem initialAw
      exponent = expLen := by
    exact Modexp.MultiLimbBarrettExponentLoop.exponentArrayLength_eq_of_header
      invariant.covered invariant.activeWordsFit access.headerConcrete access.header
  unfold Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup at hselect
  have result :=
    Modexp.MultiLimbBarrettResultSemantic.selectFreshBarrettLoopSetup_validInvariantFramedAllocated
      invariant access hfreeRead hselect
  refine ⟨result.1, ?_⟩
  cases exponentSelected with
  | allZero scan =>
      cases result.1 with
      | allZero scanValid exhausted =>
          constructor
          · have hinitialSize : initialMem.size = rFp + 64 := by
              dsimp only [initialMem]
              apply Modexp.MultiLimbBarrettAccumulator.initializedMemory_size
              · rw [hconstantSize]
                exact hrFp96
              · rw [hconstantSize]
              · rw [hconstantSize, Nat.sub_self]
                native_decide
            change rFp + 64 ≤ scan.memory.size
            rw [scanValid.memoryEq]
            simpa only [initialMem, rFp, k, n, wideBarrettNormalizedLenFor] using
              hinitialSize.ge
          · constructor
            · change rFp + 32 + 32 * k ≤ 32 * scan.activeWords.toNat
              have hfit : rFp + wordArrayAllocationSize k + 31 < UInt256.size := by
                apply lt_trans (b := 2 ^ 64)
                · apply lt_of_le_of_lt (b :=
                      Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k)
                  · dsimp only [loopFp]
                    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
                      Modexp.MultiLimbBarrettReusedCall.callResultFp
                      wordArrayAllocationSize wordArrayPayloadSize
                    omega
                  · exact hscratch
                · norm_num [UInt256.size]
              have hrange :=
                Modexp.MultiLimbOddConversionSemantic.newWordArrayWords_range
                  selected.direct.constant.finalWords rFp k invariant.wordsPos
                  selected.direct.constant.finalWordsFit hfit
              have hheaderMono :=
                Modexp.MultiLimbBarrettResultSemantic.readWords1_active_mono
                  initialAw exponent invariant.activeWordsFit access.exponentFit
              have scanStartInvariant :=
                invariant.afterExponentArrayLengthLoad access.exponentFit
              have hscanMono :=
                Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.initialActive_le
                  scanValid scanStartInvariant access
              have hmono : initialAw.toNat ≤ scan.activeWords.toNat :=
                hheaderMono.trans hscanMono
              apply le_trans (b := 32 * initialAw.toNat)
              · simpa only [initialAw, Modexp.MultiLimbBarrettAccumulator.allocatedWords,
                  wordArrayAllocationSize, wordArrayPayloadSize] using hrange.1
              · exact Nat.mul_le_mul_left 32 hmono
            · constructor
              · have scanStartInvariant :=
                    invariant.afterExponentArrayLengthLoad access.exponentFit
                have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
                  access.exponentFit access.byteFit
                simpa [Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection.activeWords]
                  using scanInvariant.activeWordsFit
              · simpa only [initialMem, initialAw, exponent, expLen, n, k, rFp,
                  wideBarrettNormalizedLenFor] using hlength
  | nonzero scan top first rest =>
      rcases result.2 with ⟨finalValue, finalInvariant⟩
      constructor
      · change rFp + 64 ≤ rest.memory.size
        have hrScratch : rFp + 64 ≤
            Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k := by
          dsimp only [loopFp]
          unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
            Modexp.MultiLimbBarrettReusedCall.callResultFp wordArrayAllocationSize
            wordArrayPayloadSize
          omega
        exact hrScratch.trans finalInvariant.scratchConcrete
      · constructor
        · change rFp + 32 + 32 * k ≤ 32 * rest.activeWords.toNat
          apply le_trans (b :=
            Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k)
          · dsimp only [loopFp]
            unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
              Modexp.MultiLimbBarrettReusedCall.callResultFp wordArrayAllocationSize
              wordArrayPayloadSize
            omega
          · exact finalInvariant.scratchConcrete.trans finalInvariant.covered
        · constructor
          · simpa [Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection.activeWords]
              using finalInvariant.activeWordsFit
          · simpa only [initialMem, initialAw, exponent, expLen, n, k, rFp,
              wideBarrettNormalizedLenFor] using hlength

/-- Every complete word below the normalized accumulator is preserved by the selected exponent
trace. This is the frame used for the original result prefix at the restore boundary. -/
theorem NormalizedSelection.exponentReadBelow
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret read : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hread : 96 ≤ read)
    (hbelow : read + 32 ≤ accumulatorFp selected.direct.reduced.finalFreePtr
      (Modexp.MultiLimbBarrettConversion.words
        (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)))
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n) n baseSize))
        (UInt256.ofNat
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n))
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected) :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    exponentSelected.memory.readWithPadding read 32 =
      (initializedMemory selected.direct.constant.finalMemory rFp k).readWithPadding read 32 := by
  dsimp only
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
    bytesAllocationSize n
  let remFp := directRemFp modulusFp n baseSize
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let loopFp := rFp + wordArrayAllocationSize k
  let exponent := UInt256.ofNat (operandExponentPtr baseSize)
  let expLen := UInt256.ofNat exponentSize
  let r := UInt256.ofNat rFp
  let a := UInt256.ofNat remFp
  let modulus := UInt256.ofNat modulusFp
  let mu := UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k)
  let initialMem := initializedMemory selected.direct.constant.finalMemory rFp k
  let initialAw := allocatedWords selected.direct.constant.finalWords rFp k
  have hbackend := selected.direct.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, modulusFp, k, n, wideBarrettNormalizedLenFor] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤
      selected.direct.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.direct.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.direct.entryFacts selected.direct.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.direct.reduced.finalFreePtr k
        selected.direct.entryFacts.divisorBound)
    dsimp only [loopFp, rFp, remFp, modulusFp, k, n, wideBarrettNormalizedLenFor]
      at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.direct.entryFacts hreduceWorkspace
    selected.direct.reduced selected.direct.constant hconstantAfter hscratch
    selected.direct.calldataBound selected.direct.baseInput_eq selected.direct.modulus_eq
  have access := selected.exponentAccessFrame hb he hm hmodLarge hnormalize hcalldata
  have hrFp64 : rFp < 2 ^ 64 := by
    dsimp only [loopFp] at hscratch
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    omega
  have hrFp256 : rFp < UInt256.size :=
    lt_trans hrFp64 (by norm_num [UInt256.size])
  have hbelow' : read + 32 ≤ r.toNat := by
    dsimp only [r]
    rw [UInt256.toNat_ofNat_of_lt hrFp256]
    exact hbelow
  unfold Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup at hselect
  exact Modexp.MultiLimbBarrettResultSemantic.selectFreshBarrettLoopSetup_readBelowFramed
    invariant access hread hbelow' hselect

/-- The prepared normalized recursive branch has a canonical complete exponent selection, together
with executable validity and equality to the trusted calldata exponent model. -/
theorem NormalizedSelection.exponentSelection
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
      bytesAllocationSize n
    let exponent := UInt256.ofNat (operandExponentPtr baseSize)
    let expLen := UInt256.ofNat exponentSize
    let initialMem := initializedMemory selected.direct.constant.finalMemory rFp k
    let initialAw := allocatedWords selected.direct.constant.finalWords rFp k
    ∃ exponentSelected,
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k) initialMem initialAw exponent
        (UInt256.ofNat rFp) (UInt256.ofNat (directRemFp modulusFp n baseSize))
        (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k)) expLen =
          some exponentSelected ∧
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I k k
        (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp n baseSize)) (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k)) exponent expLen
        initialMem initialAw exponentSelected ∧
      rFp + 64 ≤ exponentSelected.memory.size ∧
      rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat ∧
      exponentSelected.activeWords.toNat * 32 < UInt256.size ∧
      Modexp.MultiLimbExponentTrace.exponentArrayLength initialMem initialAw exponent = expLen ∧
      Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I baseSize exponentSize
        expLen.toNat 8 k k (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp n baseSize)) (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k)) exponent expLen
        initialMem initialAw exponentSelected := by
  dsimp only
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let modulusFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
    bytesAllocationSize n
  have hkPos : 0 < k := by
    have hkTwo := selected.direct.entryFacts.divisorTwo
    simpa only [k, n, wideBarrettNormalizedLenFor] using lt_of_lt_of_le (by decide : 0 < 2) hkTwo
  rcases Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup_exists
      (mem := initializedMemory selected.direct.constant.finalMemory rFp k)
      (aw := allocatedWords selected.direct.constant.finalWords rFp k)
      (exponent := UInt256.ofNat (operandExponentPtr baseSize))
      (r := UInt256.ofNat rFp)
      (a := UInt256.ofNat (directRemFp modulusFp n baseSize))
      (n := UInt256.ofNat modulusFp)
      (mu := UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
      (expLen := UInt256.ofNat exponentSize) hkPos with ⟨exponentSelected, hselect⟩
  have hvalid := selected.exponentValid hb he hm hmodLarge hnormalize hcalldata hselect
  exact ⟨exponentSelected, hselect, hvalid.1, hvalid.2.1, hvalid.2.2.1,
    hvalid.2.2.2.1, hvalid.2.2.2.2,
    selected.exponentAlignment hb he hm hmodLarge hnormalize hcalldata hselect⟩

/-- The allocator-created zero prefix survives the direct backend and the complete selected
exponent execution. -/
theorem NormalizedSelection.exponentPrefixZero
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n) n baseSize))
        (UInt256.ofNat
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n))
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected)
    (hselectedSize :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      rFp + 64 ≤ exponentSelected.memory.size) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let offset := barrettNormalizedOffset mem aw p modulusSize
    exponentSelected.memory.readWithPadding
        (operandFreePtr baseSize exponentSize modulusSize + 32) (offset - 32) =
      ffi.ByteArray.zeroes (offset - 32) := by
  dsimp only
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let prefixLen := offset - 32
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
  let initialMem := initializedMemory selected.direct.constant.finalMemory rFp k
  change exponentSelected.memory.readWithPadding (result + 32) prefixLen =
    ffi.ByteArray.zeroes prefixLen
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp temp := by
    simpa only [mem, aw, p, fp, temp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hbounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p modulusSize) (barrettScanStart p) (by
      unfold barrettScanStart barrettScanEnd
      omega)
  have hoffsetPos : 32 < offset := by
    have hnormalizeLocal : p + 32 < barrettScanStop mem aw p modulusSize := by
      simpa only [mem, aw, p] using hnormalize
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hoffsetLe : offset ≤ modulusSize + 31 := by
    have hupper : barrettScanStop mem aw p modulusSize ≤ p + modulusSize + 31 := by
      simpa [barrettScanStop, barrettScanEnd] using hbounds.2
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hallocation : 32 + modulusSize ≤ bytesAllocationSize modulusSize :=
    bytesHeaderAndSize_le_allocation modulusSize
  have hprefixEndFp : result + 32 + prefixLen ≤ fp := by
    dsimp only [result, prefixLen, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr
    omega
  have hprefixWordModulus : result + 32 + prefixLen + 31 ≤ modulusFp := by
    have hnAllocation : 32 ≤ bytesAllocationSize n := by
      have := bytesHeaderAndSize_le_allocation n
      omega
    dsimp only [modulusFp, temp]
    unfold wideBarrettNormalizedResultFp
    omega
  have hfinalLower :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
      selected.direct.reduced
  have hmodulusLeRFp : modulusFp ≤ rFp := by
    have hmodulusLeEntry : modulusFp ≤
        directRemFp modulusFp n baseSize + wordArrayAllocationSize k := by
      unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hentryLeFinal : directRemFp modulusFp n baseSize + wordArrayAllocationSize k ≤
        selected.direct.reduced.finalFreePtr := by
      simpa only [modulusFp, temp, n, k, wideBarrettNormalizedLenFor] using hfinalLower
    have hfinalLeRFp : selected.direct.reduced.finalFreePtr ≤ rFp := by
      dsimp only [rFp]
      unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact hmodulusLeEntry.trans (hentryLeFinal.trans hfinalLeRFp)
  have hprefixWordRFp : result + 32 + prefixLen + 31 ≤ rFp :=
    hprefixWordModulus.trans hmodulusLeRFp
  have hsourceSize : sourceMem.size = temp + 32 := by
    simpa only [sourceMem] using geometry.resultMemSize
  have hrFp96 : 96 ≤ rFp := by
    dsimp only [rFp]
    unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hconstantSize : selected.direct.constant.finalMemory.size = rFp := by
    rw [selected.direct.constant.finalMemorySize]
    rfl
  have hinitialSize : initialMem.size = rFp + 64 := by
    dsimp only [initialMem]
    apply Modexp.MultiLimbBarrettAccumulator.initializedMemory_size
    · rw [hconstantSize]
      exact hrFp96
    · rw [hconstantSize]
    · rw [hconstantSize, Nat.sub_self]
      native_decide
  have hsourceZero : sourceMem.readWithPadding (result + 32) prefixLen =
      ffi.ByteArray.zeroes prefixLen := by
    simpa only [sourceMem, result, prefixLen, offset, mem, aw, p, fp, temp] using
      preparedNormalizedPrefixZero I hb he hm hmodLarge hnormalize hcalldata
  have hinitialFrame : initialMem.readWithPadding (result + 32) prefixLen =
      sourceMem.readWithPadding (result + 32) prefixLen := by
    apply readWithPadding_eq_of_wordFrames
    · apply lt_of_le_of_lt hprefixEndFp
      have hfpBound := geometry.allocationBound
      omega
    · rw [hinitialSize]
      omega
    · rw [hsourceSize]
      have hfpTemp : fp ≤ temp := by
        dsimp only [temp, fp, n]
        unfold wideBarrettNormalizedResultFp
        omega
      omega
    · intro i hi
      have hframe := selected.direct.initializedReadBelow (result + 32 + i)
        (by
          dsimp only [result]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by
          apply le_trans (b := result + 32 + prefixLen + 31)
          · omega
          · exact hprefixWordModulus)
      simpa only [initialMem, sourceMem, modulusFp, temp, n, k, rFp,
        wideBarrettNormalizedLenFor, Nat.add_assoc] using hframe
  have hfinalFrame : exponentSelected.memory.readWithPadding (result + 32) prefixLen =
      initialMem.readWithPadding (result + 32) prefixLen := by
    apply readWithPadding_eq_of_wordFrames
    · apply lt_of_le_of_lt hprefixEndFp
      have hfpBound := geometry.allocationBound
      omega
    · have hsize : rFp + 64 ≤ exponentSelected.memory.size := by
        simpa only [n, k, rFp, wideBarrettNormalizedLenFor] using hselectedSize
      exact le_trans (by omega : result + 32 + prefixLen ≤ rFp + 64) hsize
    · rw [hinitialSize]
      omega
    · intro i hi
      have hframe := selected.exponentReadBelow hb he hm hmodLarge hnormalize hcalldata
        (read := result + 32 + i)
        (by
          dsimp only [result]
          unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
            bytesAllocationSize
          omega)
        (by
          apply le_trans (b := result + 32 + prefixLen + 31)
          · omega
          · exact hprefixWordRFp) hselect
      simpa only [initialMem, n, k, rFp, wideBarrettNormalizedLenFor,
        Nat.add_assoc] using hframe
  exact hfinalFrame.trans (hinitialFrame.trans hsourceZero)

/-- Serialization writes only the temporary normalized payload and preserves the zero prefix of
the original result object used by PC 1808. -/
theorem NormalizedSelection.serializedPrefixZero
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n) n baseSize))
        (UInt256.ofNat
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n))
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected)
    (hselectedSize :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      rFp + 64 ≤ exponentSelected.memory.size) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
    let offset := barrettNormalizedOffset mem aw p modulusSize
    (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat temp) n
      ).readWithPadding (operandFreePtr baseSize exponentSize modulusSize + 32)
        (offset - 32) = ffi.ByteArray.zeroes (offset - 32) := by
  dsimp only
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let prefixLen := offset - 32
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
    exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat temp) n
  change serialized.readWithPadding (result + 32) prefixLen =
    ffi.ByteArray.zeroes prefixLen
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp temp := by
    simpa only [mem, aw, p, fp, temp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
  have hnLe : n ≤ modulusSize := by
    have hsplit' : prefixLen + n = modulusSize := by
      simpa only [prefixLen, offset, n, wideBarrettNormalizedLenFor, mem, aw, p] using hsplit
    omega
  have hnBound : n ≤ 1024 := hnLe.trans hm
  have hbounds := barrettScanStopAt_bounds mem aw
    (barrettScanEnd p modulusSize) (barrettScanStart p) (by
      unfold barrettScanStart barrettScanEnd
      omega)
  have hoffsetLe : offset ≤ modulusSize + 31 := by
    have hu : barrettScanStop mem aw p modulusSize ≤ p + modulusSize + 31 := by
      simpa [barrettScanStop, barrettScanEnd] using hbounds.2
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hmodAllocation : 32 + modulusSize ≤ bytesAllocationSize modulusSize :=
    bytesHeaderAndSize_le_allocation modulusSize
  have hprefixEndFp : result + 32 + prefixLen ≤ fp := by
    dsimp only [result, prefixLen, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr
    omega
  have hfpLeTemp : fp ≤ temp := by
    dsimp only [temp, fp, n, wideBarrettNormalizedLenFor]
    unfold wideBarrettNormalizedResultFp
    omega
  have hprefixWordTemp : result + 32 + prefixLen + 31 ≤ temp + 32 := by
    omega
  have hfinalLower :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
      selected.direct.reduced
  have hmodulusLeRFp : modulusFp ≤ rFp := by
    have hmodulusLeEntry : modulusFp ≤
        directRemFp modulusFp n baseSize + wordArrayAllocationSize k := by
      unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hentryLeFinal : directRemFp modulusFp n baseSize + wordArrayAllocationSize k ≤
        selected.direct.reduced.finalFreePtr := by
      simpa only [modulusFp, temp, n, k, wideBarrettNormalizedLenFor] using hfinalLower
    have hfinalLeRFp : selected.direct.reduced.finalFreePtr ≤ rFp := by
      dsimp only [rFp]
      unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact hmodulusLeEntry.trans (hentryLeFinal.trans hfinalLeRFp)
  have hnAllocation : 32 + n ≤ bytesAllocationSize n :=
    bytesHeaderAndSize_le_allocation n
  have htempPayloadRFp : temp + 32 + n ≤ rFp := by
    apply le_trans (b := modulusFp)
    · dsimp only [modulusFp]
      omega
    · exact hmodulusLeRFp
  have htempLeRFp : temp ≤ rFp := by omega
  have hsize : rFp + 64 ≤ exponentSelected.memory.size := by
    simpa only [n, k, rFp, wideBarrettNormalizedLenFor] using hselectedSize
  have htempMem : temp + 32 + n ≤ exponentSelected.memory.size :=
    htempPayloadRFp.trans (le_trans (Nat.le_add_right rFp 64) hsize)
  have hpartialMem : temp + 64 ≤ exponentSelected.memory.size := by
    have hnLarge : 32 < n := by
      simpa only [n, wideBarrettNormalizedLenFor] using selected.direct.dataLenLarge
    exact le_trans (by omega) htempMem
  have htempAddr : temp + 32 + n < UInt256.size := by
    apply lt_trans (b := 2 ^ 64)
    · have hbound : temp + bytesAllocationSize n < 2 ^ 64 := by
        simpa only [temp, n, wideBarrettNormalizedLenFor, mem, aw, p] using
          geometry.resultBound
      omega
    · norm_num [UInt256.size]
  have htempNat : (UInt256.ofNat temp).toNat = temp :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have hserializedSize : serialized.size = exponentSelected.memory.size := by
    dsimp only [serialized]
    apply Modexp.MultiLimbBarrettResultSemantic.resultMemory_size hnBound
    · rw [htempNat]
      exact htempAddr
    · rw [htempNat]
      exact htempMem
    · intro _
      rw [htempNat]
      exact hpartialMem
  have hprefix := selected.exponentPrefixZero hb he hm hmodLarge hnormalize hcalldata
    hselect hselectedSize
  apply Eq.trans (readWithPadding_eq_of_wordFrames serialized exponentSelected.memory
    (result + 32) prefixLen (by
      apply lt_of_le_of_lt hprefixEndFp
      exact lt_of_le_of_lt (Nat.le_add_right fp _) geometry.allocationBound) (by
        rw [hserializedSize]
        exact le_trans (hprefixEndFp.trans (hfpLeTemp.trans htempLeRFp))
          (le_trans (Nat.le_add_right rFp 64) hsize)) (by
        exact le_trans (hprefixEndFp.trans (hfpLeTemp.trans htempLeRFp))
          (le_trans (Nat.le_add_right rFp 64) hsize)) (by
      intro i hi
      apply Modexp.MultiLimbBarrettResultSemantic.resultMemory_read_below hnBound
      · rw [htempNat]
        exact htempAddr
      · rw [htempNat]
        exact htempMem
      · intro _
        rw [htempNat]
        exact hpartialMem
      · rw [htempNat]
        exact le_trans (by omega : result + 32 + i + 32 ≤
          result + 32 + prefixLen + 31) hprefixWordTemp))
  simpa only [result, prefixLen, offset, mem, aw, p] using hprefix

/-- All concrete memory and address premises needed to restore a selected normalized recursive
result.  This contract is deliberately tied to the prepared Solidity layout: the only layout
restriction exposed to callers is the compiler allocator geometry proved by
`preparedNormalizeReentryGeometry`. -/
structure PreparedNormalizedRestoreGeometry
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection) : Prop where
  tempAddr : wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize + 32 +
    wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize < UInt256.size
  tempAddr64 : wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize + 32 +
    wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize < 2 ^ 64
  tempMem : wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize + 32 +
    wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize ≤
      exponentSelected.memory.size
  sourceActive :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    accumulatorFp selected.direct.reduced.finalFreePtr k + 32 + 32 * ((n + 31) / 32) ≤
      32 * exponentSelected.activeWords.toNat
  outputBeforeHeader :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize + 32 + n ≤
      accumulatorFp selected.direct.reduced.finalFreePtr k
  offset : 32 ≤ barrettNormalizedOffset
    (wideWordResultMemory I baseSize exponentSize modulusSize)
    (wideWordResultWords baseSize exponentSize modulusSize)
    (operandModulusPtr baseSize exponentSize) modulusSize
  width : barrettNormalizedOffset
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize) modulusSize - 32 +
        wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize = modulusSize
  originalSize64 : modulusSize < 2 ^ 64
  destinationEnd : operandFreePtr baseSize exponentSize modulusSize +
      barrettNormalizedOffset
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize +
      wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize ≤
        exponentSelected.memory.size
  zeroPrefix :
    (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords
        (UInt256.ofNat (accumulatorFp selected.direct.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words
            (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize))))
        (UInt256.ofNat (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize))
        (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)
      ).readWithPadding (operandFreePtr baseSize exponentSize modulusSize + 32)
        (barrettNormalizedOffset
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize - 32) =
      ffi.ByteArray.zeroes (barrettNormalizedOffset
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize - 32)
  resultOffset : operandFreePtr baseSize exponentSize modulusSize +
      barrettNormalizedOffset
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize < UInt256.size

/-- A complete direct selector used recursively by the normalization path returns to PC 1808,
which restores the temporary result into the original result object and jumps to the saved Barrett
continuation. Both the recursive selector and the exact path-sensitive gas remain explicit. -/
theorem DirectSelection.freshRestoreToRetBar
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed p modulusFp modulusSize basePtr baseSize : Nat}
    {temp offset result originalSize retBar ret : Nat} {tail : List UInt256}
    {exponent : UInt256} {exponentSize byteFuel bitFuel callFuel : Nat}
    {exponentSelected : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (selected : DirectSelection I g (initState cA gh bl σ σ₀ g A I) rdata acc mem aw
      steps gasUsed p modulusFp modulusSize basePtr baseSize exponent (UInt256.ofNat temp)
      ⟨1808⟩ (UInt256.ofNat offset)
      (UInt256.ofNat modulusSize :: UInt256.ofNat result :: UInt256.ofNat retBar ::
        UInt256.ofNat ret :: tail))
    (valid : Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I callFuel
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (allocatedWords selected.constant.finalWords
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponentSelected)
    (alignment : Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I
      baseSize exponentSize byteFuel bitFuel callFuel
      (Modexp.MultiLimbBarrettConversion.words modulusSize)
      (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) +
        wordArrayAllocationSize (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
      (allocatedWords selected.constant.finalWords
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponentSelected)
    (access : Modexp.MultiLimbBarrettExponentLoop.BarrettExponentAccessFrame
      (initializedMemory selected.constant.finalMemory
        (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent
      (Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize))
        (allocatedWords selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize)) exponent)
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))))
    (htempAddr : temp + 32 + modulusSize < UInt256.size)
    (htempAddr64 : temp + 32 + modulusSize < 2 ^ 64)
    (htempMem : temp + 32 + modulusSize ≤ exponentSelected.memory.size)
    (hsourceActive : accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) + 32 +
      32 * ((modulusSize + 31) / 32) ≤ 32 * exponentSelected.activeWords.toNat)
    (houtBeforeHeader : temp + 32 + modulusSize ≤
      accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize))
    (hoffset : 32 ≤ offset)
    (hwidth : offset - 32 + modulusSize = originalSize)
    (horiginalSize64 : originalSize < 2 ^ 64)
    (hdestEnd : result + offset + modulusSize ≤ exponentSelected.memory.size)
    (hprefix :
      (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
          exponentSelected.activeWords
          (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize)))
          (UInt256.ofNat temp) modulusSize).readWithPadding
        (result + 32) (offset - 32) = ffi.ByteArray.zeroes (offset - 32))
    (hresultOffset : result + offset < UInt256.size)
    (hretBar : (D_J runtimeBytecode 0).contains (UInt256.ofNat retBar) = true)
    (hdepth : tail.length + 47 ≤ 1015) :
    (RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat retBar)
      (UInt256.ofNat result :: UInt256.ofNat ret :: tail)
      (barrettRestoreMemory
        (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
          exponentSelected.activeWords
          (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize)))
          (UInt256.ofNat temp) modulusSize)
        temp result offset modulusSize)
      (barrettRestoreWords exponentSelected.activeWords temp result offset modulusSize)
      rdata acc
      (selected.scanSteps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize
          (Modexp.MultiLimbBarrettConversion.words modulusSize) + selected.reduced.stepDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
          selected.reduced.finalMemory selected.reduced.finalWords
          selected.reduced.finalFreePtr (Modexp.MultiLimbBarrettConversion.words modulusSize)
          modulusFp + selected.constant.stepDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionSteps exponentSelected modulusSize + 9)
      (gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
          modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
          (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
          (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
          (directBaseFp modulusFp modulusSize)
          (directRemFp modulusFp modulusSize baseSize) baseSize
          (Modexp.MultiLimbBarrettConversion.words modulusSize) (UInt256.ofNat basePtr) +
        selected.reduced.gasDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
          selected.reduced.finalMemory selected.reduced.finalWords
          selected.reduced.finalFreePtr (Modexp.MultiLimbBarrettConversion.words modulusSize)
          modulusFp + selected.constant.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas selected.constant.finalWords
          (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize))
          (Modexp.MultiLimbBarrettConversion.words modulusSize) exponent exponentSelected
          modulusSize +
        barrettRestoreGas exponentSelected.activeWords temp result offset modulusSize)) ∧
    Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue
        (Modexp.MultiLimbBarrettConversion.words modulusSize)
        (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize))) exponentSelected.memory =
      Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
        Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
          Model.bytesToNatPadded mem (p + 32) modulusSize ∧
    (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
        exponentSelected.activeWords
        (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
          (Modexp.MultiLimbBarrettConversion.words modulusSize)))
        (UInt256.ofNat temp) modulusSize).readWithPadding (temp + 32) modulusSize =
      Model.natToBytes
        (Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded mem (p + 32) modulusSize) modulusSize ∧
    (barrettRestoreMemory
        (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
          exponentSelected.activeWords
          (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
            (Modexp.MultiLimbBarrettConversion.words modulusSize)))
          (UInt256.ofNat temp) modulusSize)
        temp result offset modulusSize).readWithPadding (result + 32) originalSize =
      Model.natToBytes
        (Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded mem (p + 32) modulusSize) originalSize := by
  have htempFit : (UInt256.ofNat temp).toNat + 32 + modulusSize < UInt256.size := by
    rw [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)]
    exact htempAddr
  have htempMem' : (UInt256.ofNat temp).toNat + 32 + modulusSize ≤
      exponentSelected.memory.size := by
    rw [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)]
    exact htempMem
  have htempFit64 : (UInt256.ofNat temp).toNat + 32 + modulusSize < 2 ^ 64 := by
    rw [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)]
    exact htempAddr64
  have houtBeforeHeader' : (UInt256.ofNat temp).toNat + 32 + modulusSize ≤
      accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize) := by
    rw [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)]
    exact houtBeforeHeader
  have recursive := selected.freshReturn valid alignment access htempFit
    htempFit64 htempMem' hsourceActive houtBeforeHeader' (by
      simp only [List.length_cons]
      omega) (by native_decide)
  have rd1808 := recursive.1
  have hpartialOutIn : temp + 64 ≤ exponentSelected.memory.size := by
    have hlarge := selected.dataLenLarge
    exact le_trans (by omega) htempMem
  have hserializedSize := Modexp.MultiLimbBarrettResultSemantic.resultMemory_size
    (aw := exponentSelected.activeWords)
    (fp := accumulatorFp selected.reduced.finalFreePtr
      (Modexp.MultiLimbBarrettConversion.words modulusSize))
    selected.dataLenBound htempFit htempMem'
    (fun _ => by
      rw [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)]
      exact hpartialOutIn)
  have hvalueFit :
      Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded mem (p + 32) modulusSize < 256 ^ modulusSize := by
    exact recursive.2.2.2
  have hrestoredBytes := restoreMemory_bytes_eq_natToBytes
    (mem := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
      exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat temp) modulusSize)
    (temp := temp) (result := result) (offset := offset) (len := modulusSize)
    (width := originalSize)
    (value := Model.bytesToNatPadded mem (basePtr + 32) baseSize ^
      Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
        Model.bytesToNatPadded mem (p + 32) modulusSize)
    (lt_trans (by decide : 0 < 32) selected.dataLenLarge) hoffset hwidth horiginalSize64
    (by rw [hserializedSize]; exact htempMem)
    (by rw [hserializedSize]; exact hdestEnd)
    hprefix (by
      simpa only [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)] using
        recursive.2.2.1) hvalueFit
  have hlenWord : modulusSize < UInt256.size := by omega
  have htemp32Word : temp + 32 < UInt256.size := by omega
  have rdRet := reachBarrettRestoreToRetBar
    (temp := temp) (result := result) (offset := offset) (len := modulusSize)
    (retBar := retBar) (ret := ret) (tail := tail) hlenWord htemp32Word hresultOffset
    hretBar (by omega) (by simpa using rd1808)
  constructor
  · simpa only [Nat.add_assoc] using rdRet
  · constructor
    · exact recursive.2.1
    · constructor
      · simpa only [UInt256.toNat_ofNat_of_lt (by omega : temp < UInt256.size)] using
          recursive.2.2.1
      · exact hrestoredBytes

/-- The prepared normalized state discharges every concrete premise of the PC 1808 restore.
The selected exponent execution supplies the only dynamic memory bounds used here. -/
theorem NormalizedSelection.preparedRestoreGeometry
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.direct.constant.finalMemory rFp k)
        (allocatedWords selected.direct.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n) n baseSize))
        (UInt256.ofNat
          (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
            bytesAllocationSize n))
        (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected)
    (hselectedSize :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      rFp + 64 ≤ exponentSelected.memory.size)
    (hselectedActive :
      let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
      let k := Modexp.MultiLimbBarrettConversion.words n
      let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
      rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat) :
    PreparedNormalizedRestoreGeometry selected exponentSelected := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp temp := by
    simpa only [mem, aw, p, fp, temp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
  have hnLe : n ≤ modulusSize := by
    have hsplit' : offset - 32 + n = modulusSize := by
      simpa only [offset, n, wideBarrettNormalizedLenFor, mem, aw, p] using hsplit
    omega
  have hfinalLower :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
      selected.direct.reduced
  have hmodulusLeRFp : modulusFp ≤ rFp := by
    have hmodulusLeEntry : modulusFp ≤
        directRemFp modulusFp n baseSize + wordArrayAllocationSize k := by
      unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
      omega
    have hentryLeFinal : directRemFp modulusFp n baseSize + wordArrayAllocationSize k ≤
        selected.direct.reduced.finalFreePtr := by
      simpa only [modulusFp, temp, n, k, wideBarrettNormalizedLenFor] using hfinalLower
    have hfinalLeRFp : selected.direct.reduced.finalFreePtr ≤ rFp := by
      dsimp only [rFp]
      unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
        wordArrayAllocationSize wordArrayPayloadSize
      omega
    exact hmodulusLeEntry.trans (hentryLeFinal.trans hfinalLeRFp)
  have htempRFp : temp + 32 + n ≤ rFp := by
    apply le_trans (b := modulusFp)
    · dsimp only [modulusFp]
      have halloc := bytesHeaderAndSize_le_allocation n
      omega
    · exact hmodulusLeRFp
  have hrFpMem : rFp ≤ exponentSelected.memory.size := by
    have hs : rFp + 64 ≤ exponentSelected.memory.size := by
      simpa only [rFp, k, n, wideBarrettNormalizedLenFor] using hselectedSize
    omega
  have htempAddr64 : temp + 32 + n < 2 ^ 64 := by
    have hbound : temp + bytesAllocationSize n < 2 ^ 64 := by
      simpa only [temp, n, wideBarrettNormalizedLenFor, mem, aw, p] using
        geometry.resultBound
    have halloc := bytesHeaderAndSize_le_allocation n
    omega
  have hwidth : offset - 32 + n = modulusSize := by
    simpa only [offset, n, wideBarrettNormalizedLenFor, mem, aw, p] using hsplit
  have hoffset : 32 ≤ offset := by
    change p + 32 < barrettScanStop mem aw p modulusSize at hnormalize
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hoffsetLe : offset ≤ modulusSize + 31 := by
    have hbounds := barrettScanStopAt_bounds mem aw
      (barrettScanEnd p modulusSize) (barrettScanStart p) (by
        unfold barrettScanStart barrettScanEnd
        omega)
    have hupper : barrettScanStop mem aw p modulusSize ≤ p + modulusSize + 31 := by
      simpa [barrettScanStop, barrettScanEnd] using hbounds.2
    dsimp only [offset, barrettNormalizedOffset]
    omega
  have hresultEndFp : result + offset + n ≤ fp := by
    have hfpEq : fp = result + bytesAllocationSize modulusSize := by
      dsimp only [fp, result]
      rfl
    rw [hfpEq]
    have halloc := bytesHeaderAndSize_le_allocation modulusSize
    omega
  have hfpLeTemp : fp ≤ temp := by
    dsimp only [fp, temp, n, wideBarrettNormalizedLenFor]
    unfold wideBarrettNormalizedResultFp
    omega
  refine {
    tempAddr := lt_trans (by simpa only [temp, n] using htempAddr64)
      (by norm_num [UInt256.size])
    tempAddr64 := by simpa only [temp, n] using htempAddr64
    tempMem := by
      simpa only [temp, n] using htempRFp.trans hrFpMem
    sourceActive := by
      dsimp only
      simpa only [rFp, k, n, wideBarrettNormalizedLenFor,
        Modexp.MultiLimbBarrettConversion.words, MultiLimbBarrettDispatch.limbCount] using
        hselectedActive
    outputBeforeHeader := by simpa only [temp, n, rFp] using htempRFp
    offset := by simpa only [offset, mem, aw, p] using hoffset
    width := by simpa only [offset, n, mem, aw, p] using hwidth
    originalSize64 := by omega
    destinationEnd := by
      simpa only [result, offset, n, mem, aw, p, wideBarrettNormalizedLenFor] using
        hresultEndFp.trans (hfpLeTemp.trans (le_trans (by omega : temp ≤ rFp) hrFpMem))
    zeroPrefix := by
      simpa only [n, k, rFp, temp, offset, mem, aw, p, result,
        wideBarrettNormalizedLenFor] using
        selected.serializedPrefixZero hb he hm hmodLarge hnormalize hcalldata
          hselect hselectedSize
    resultOffset := by
      change result + offset < UInt256.size
      apply lt_trans (b := 6000)
      · dsimp only [result]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega
      · norm_num [UInt256.size]
  }

/-- Normalization preserves the prepared base value and changes only the byte representation of
the modulus, not its natural-number value. -/
theorem preparedNormalizedValues_eq_original
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
    Model.bytesToNatPadded (barrettNormalizedResultMem mem aw fp p modulusSize resultFp)
        (operandBasePtr + 32) baseSize =
        Model.bytesToNatPadded mem (operandBasePtr + 32) baseSize ∧
      Model.bytesToNatPadded (barrettNormalizedResultMem mem aw fp p modulusSize resultFp)
        (fp + 32) (barrettNormalizedLen mem aw p modulusSize) =
        Model.bytesToNatPadded mem (p + 32) modulusSize := by
  dsimp only
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let n := barrettNormalizedLen mem aw p modulusSize
  have geometry : NormalizeReentryGeometry I mem aw p modulusSize fp resultFp := by
    simpa only [mem, aw, p, fp, resultFp] using
      preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
  have hoffset : 32 ≤ barrettNormalizedOffset mem aw p modulusSize := by
    change p + 32 < barrettScanStop mem aw p modulusSize at hnormalize
    unfold barrettNormalizedOffset
    omega
  have hsourceForCopy : p + barrettNormalizedOffset mem aw p modulusSize + n ≤ fp + 32 := by
    have hend : p + barrettNormalizedOffset mem aw p modulusSize + n =
        p + 32 + modulusSize := by
      dsimp only [n]
      omega
    rw [hend]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hmemSize : mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa only [mem] using wideWordResultMemory_size I hb he hm
  have hbaseIn : operandBasePtr + 32 + baseSize ≤ mem.size := by
    rw [hmemSize]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hbaseBelowFp : operandBasePtr + 32 + baseSize ≤ fp := by
    dsimp only [fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hbaseBelowResult : operandBasePtr + 32 + baseSize ≤ resultFp := by
    have hresultEq : resultFp = fp + bytesAllocationSize n := by
      dsimp only [resultFp, fp, n, mem, aw, p]
      rfl
    rw [hresultEq]
    omega
  have hbaseRead := geometry.readOriginal hsourceForCopy hbasePos (by omega)
    (by unfold operandBasePtr; omega) hbaseIn hbaseBelowFp hbaseBelowResult
  have hbaseValue := model_bytesToNatPadded_eq_of_readWithPadding
    (by unfold operandBasePtr; omega) (by unfold operandBasePtr; omega) (by omega) hbaseRead
  exact ⟨hbaseValue, normalizedResult_modulusValue_eq_original geometry⟩

/-- Complete selected execution evidence for a prepared normalized multi-limb branch.  The
selector equation is a public field, and `execution` contains the exact path gas together with
the accumulator, serialized temporary bytes, and restored original-width bytes. -/
structure PreparedNormalizedExecution
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection) : Prop where
  selection :
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
      (rFp + wordArrayAllocationSize k)
      (initializedMemory selected.direct.constant.finalMemory rFp k)
      (allocatedWords selected.direct.constant.finalWords rFp k)
      (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
      (UInt256.ofNat (directRemFp
        (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
          bytesAllocationSize n) n baseSize))
      (UInt256.ofNat
        (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize +
          bytesAllocationSize n))
      (UInt256.ofNat (quotientPtr selected.direct.reduced.finalFreePtr k))
      (UInt256.ofNat exponentSize) = some exponentSelected
  execution :
    (let mem := wideWordResultMemory I baseSize exponentSize modulusSize
     let aw := wideWordResultWords baseSize exponentSize modulusSize
     let p := operandModulusPtr baseSize exponentSize
     let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
     let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
     let result := operandFreePtr baseSize exponentSize modulusSize
     let offset := barrettNormalizedOffset mem aw p modulusSize
     let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
     let k := Modexp.MultiLimbBarrettConversion.words n
     let modulusFp := temp + bytesAllocationSize n
     let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
     let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
     let sourceAw := barrettNormalizedResultAw mem aw fp p modulusSize temp
     let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
       exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat temp) n
     let restored := barrettRestoreMemory serialized temp result offset n
     RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I)
        (UInt256.ofNat retBar) (UInt256.ofNat result :: UInt256.ofNat ret :: tail)
        restored (barrettRestoreWords exponentSelected.activeWords temp result offset n)
        ByteArray.empty acc
        (selected.direct.scanSteps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize k +
          selected.direct.reduced.stepDelta +
          Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
            selected.direct.reduced.finalMemory selected.direct.reduced.finalWords
            selected.direct.reduced.finalFreePtr k modulusFp +
          selected.direct.constant.stepDelta +
          Modexp.MultiLimbBarrettResult.freshExecutionSteps exponentSelected n + 9)
        ((gasUsed + barrettNormalizeReentryChecksGas mem aw fp p modulusSize temp) +
          Modexp.MultiLimbBarrettConversion.scanConversionGas sourceMem sourceAw modulusFp fp n +
          18 + MultiLimbReduceBase.nonzeroGas
            (Modexp.MultiLimbBarrettConversion.convertedMemory sourceMem sourceAw modulusFp fp n)
            (Modexp.MultiLimbBarrettConversion.convertedWords sourceMem sourceAw modulusFp fp n)
            (directBaseFp modulusFp n) (directRemFp modulusFp n baseSize) baseSize k
            (UInt256.ofNat operandBasePtr) + selected.direct.reduced.gasDelta +
          Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
            selected.direct.reduced.finalMemory selected.direct.reduced.finalWords
            selected.direct.reduced.finalFreePtr k modulusFp +
          selected.direct.constant.gasDelta +
          Modexp.MultiLimbBarrettResult.freshExecutionGas
            selected.direct.constant.finalWords rFp k
            (UInt256.ofNat (operandExponentPtr baseSize)) exponentSelected n +
          barrettRestoreGas exponentSelected.activeWords temp result offset n) ∧
      Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
          (UInt256.ofNat rFp) exponentSelected.memory =
        Model.bytesToNatPadded sourceMem (operandBasePtr + 32) baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded sourceMem (fp + 32) n ∧
      serialized.readWithPadding (temp + 32) n =
        Model.natToBytes
          (Model.bytesToNatPadded sourceMem (operandBasePtr + 32) baseSize ^
            Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
              Model.bytesToNatPadded sourceMem (fp + 32) n) n ∧
      restored.readWithPadding (result + 32) modulusSize =
        Model.natToBytes
          (Model.bytesToNatPadded sourceMem (operandBasePtr + 32) baseSize ^
            Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
              Model.bytesToNatPadded sourceMem (fp + 32) n) modulusSize)
  valueBridge :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
    let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
    Model.bytesToNatPadded sourceMem (operandBasePtr + 32) baseSize =
        Model.bytesToNatPadded mem (operandBasePtr + 32) baseSize ∧
      Model.bytesToNatPadded sourceMem (fp + 32)
          (wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize) =
        Model.bytesToNatPadded mem (p + 32) modulusSize

/-- Select and execute the complete normalized multi-limb computation.  No callback or
existential gas variable remains: the existential is only the executable exponent-path selector,
and its equation is retained in `PreparedNormalizedExecution.selection`. -/
theorem NormalizedSelection.preparedExecution
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hretBar : (D_J runtimeBytecode 0).contains (UInt256.ofNat retBar) = true)
    (hdepth : tail.length ≤ 968) :
    ∃ exponentSelected, PreparedNormalizedExecution selected exponentSelected := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  rcases selected.exponentSelection hb he hm hmodLarge hnormalize hcalldata with
    ⟨exponentSelected, hselect, hvalid, hsize, hactive, _hawFit, hlength, halignment⟩
  have haccess := selected.exponentAccessFrame hb he hm hmodLarge hnormalize hcalldata
  have hvalid' := hvalid
  have halignment' := halignment
  have haccess' := haccess
  rw [← hlength] at hvalid' halignment' haccess'
  have geometry := selected.preparedRestoreGeometry hb he hm hmodLarge hnormalize hcalldata
    hselect hsize hactive
  have recursive := DirectSelection.freshRestoreToRetBar selected.direct
    hvalid' halignment' haccess'
    geometry.tempAddr geometry.tempAddr64 geometry.tempMem geometry.sourceActive
    geometry.outputBeforeHeader geometry.offset geometry.width geometry.originalSize64
    geometry.destinationEnd geometry.zeroPrefix geometry.resultOffset hretBar (by omega)
  refine ⟨exponentSelected, {
    selection := hselect
    execution := ?_
    valueBridge := ?_ }⟩
  · simpa only [mem, aw, p, fp, temp, result, offset, n, k, modulusFp, rFp,
      wideBarrettNormalizedLenFor] using recursive
  · simpa only [mem, aw, p, fp, temp, wideBarrettNormalizedLenFor] using
      preparedNormalizedValues_eq_original I hb he hm hbasePos hmodLarge hnormalize hcalldata

/-- Compose the common prepared even-Barrett prefix with the arbitrary-width normalized backend.
Both executable selectors remain exposed in the conclusion. -/
theorem runPreparedBarrettNormalizedMultiLimbSelected
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {C steps baseSize exponentSize modulusSize ret : Nat}
    {tail : List UInt256}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hmodulusGtOne : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = UInt256.ofNat 0)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hnLarge : 32 < wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize)
    (htail : tail.length ≤ 968)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc steps C) :
    ∃ selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
        ByteArray.empty acc
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (C + preparedBarrettPrefixGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize
        (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
        (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
        operandBasePtr baseSize (operandExponentPtr baseSize) 1271
        (operandFreePtr baseSize exponentSize modulusSize) ret tail,
      ∃ exponentSelected, PreparedNormalizedExecution selected exponentSelected := by
  obtain ⟨prefixSteps, rd1592⟩ := runPreparedBarrettPrefixExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail) hb he (by omega) hm hmodulusGtOne hcalldata heven
    (by omega) rd0
  obtain ⟨selected⟩ := preparedNormalizedSelection_exists
    (gasUsed := C + preparedBarrettPrefixGasFromAw I
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize)
    (retBar := 1271) (ret := ret) (tail := tail)
    hb he hm hbasePos hmodLarge hnormalize hnLarge hcalldata (by omega) (by
      simpa [show (⟨1271⟩ : UInt256) = UInt256.ofNat 1271 by native_decide] using rd1592)
  obtain ⟨exponentSelected, execution⟩ := selected.preparedExecution hb he hm hbasePos
    hmodLarge hnormalize hcalldata jumpDest_1271 (by omega)
  exact ⟨selected, exponentSelected, execution⟩

/-- Construct the direct multi-limb selector from the prepared Solidity operand/result state.
This is the no-leading-zero counterpart of `preparedNormalizedSelection_exists`. -/
theorem preparedDirectSelection_exists
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed steps baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hfirst : UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠
          UInt256.ofNat 0)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 983)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨1592⟩
      (UInt256.ofNat (operandModulusPtr baseSize exponentSize) ::
        UInt256.ofNat modulusSize :: UInt256.ofNat retBar ::
        UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize) ::
        UInt256.ofNat (operandExponentPtr baseSize) :: UInt256.ofNat operandBasePtr ::
        UInt256.ofNat ret :: tail)
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize)
      ByteArray.empty acc steps gasUsed) :
    Nonempty (DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail) := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  have hmemEq : mem.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa only [mem] using wideWordResultMemory_size I hb he hm
  have hmem96 : 96 ≤ mem.size := by
    rw [hmemEq]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hmemLe : mem.size ≤ fp := by
    rw [hmemEq]
    dsimp only [fp]
    unfold wideBarrettNormalizedFp bytesAllocationSize
    omega
  have hgap : fp - mem.size < USize.size := by
    rw [hmemEq]
    exact lt_usize _ (by
      dsimp only [fp]
      unfold wideBarrettNormalizedFp bytesAllocationSize
      omega)
  have hp32 : p + 32 < UInt256.size := by
    apply lt_trans (b := 2 ^ 64)
    · dsimp only [p]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · norm_num [UInt256.size]
  have hp64 : p + 32 < 2 ^ 64 := by
    dsimp only [p]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hpend : p + modulusSize + 31 < UInt256.size := by
    apply lt_trans (b := 2 ^ 64)
    · dsimp only [p]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega
    · norm_num [UInt256.size]
  have hsourceBefore : p + 32 + modulusSize ≤ fp := by
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hawNat : aw.toNat = operandModulusWords baseSize exponentSize modulusSize +
      bytesAllocationWords modulusSize := by
    dsimp only [aw]
    exact wideWordResultWords_toNat hb he hm
  have hactive : p + 64 ≤ 32 * aw.toNat := by
    rw [hawNat]
    dsimp only [p]
    rw [operandModulusPtr_eq]
    unfold operandModulusWords bytesAllocationWords
    have hround : 1 ≤ (modulusSize + 31) / 32 := by omega
    omega
  have hawFit : aw.toNat * 32 < UInt256.size := by
    rw [hawNat]
    apply lt_trans (b := 5000)
    · unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      omega
    · norm_num [UInt256.size]
  have hallocationBound : fp + wordArrayAllocationSize k < 2 ^ 64 := by
    dsimp only [fp, k]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize Modexp.MultiLimbBarrettConversion.words
      MultiLimbBarrettDispatch.limbCount wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hbackend : directRemFp fp modulusSize baseSize + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (show directRemFp fp modulusSize baseSize + wordArrayAllocationSize k +
          Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes + 32 * 539 ≤ 65536 by
        dsimp only [fp, k]
        unfold directRemFp directBaseFp wideBarrettNormalizedFp operandFreePtr
          operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
          wordArrayAllocationSize wordArrayPayloadSize
          Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes
          MultiLimbReduceBase.baseWords MultiLimbReduceBase.naturalWords
        omega)
      (by decide)
  have hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp) := by
    simpa only [mem, fp, wideBarrettNormalizedFp] using
      wideWordResultMemory_read64 I hb he hm
  have haw3 : 3 ≤ aw.toNat := by
    rw [hawNat]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
    omega
  have haw64 : ¬ (UInt256.ofNat 64) ≥ aw * UInt256.ofNat 32 := by
    intro h
    have hmul := umul_toNat (a := aw) (b := UInt256.ofNat 32) hawFit
    have hnat : (aw * UInt256.ofNat 32).toNat ≤ (UInt256.ofNat 64).toNat := h
    rw [hmul, UInt256.toNat_ofNat_of_lt (by decide : 32 < UInt256.size),
      UInt256.toNat_ofNat_of_lt (by decide : 64 < UInt256.size)] at hnat
    omega
  have hkPos : 0 < k := by
    dsimp only [k]
    unfold Modexp.MultiLimbBarrettConversion.words MultiLimbBarrettDispatch.limbCount
    omega
  have hfit : fp + wordArrayAllocationSize k + 31 < UInt256.size := by
    exact lt_trans (by omega : fp + wordArrayAllocationSize k + 31 < 2 ^ 64 + 31)
      (by norm_num [UInt256.size])
  have hrange := MultiLimbOddConversionSemantic.newWordArrayWords_range aw fp k hkPos hawFit hfit
  have haccess : (UInt256.ofNat p).toNat + 32 ≤
      32 * (Modexp.MultiLimbBarrettConversion.allocatedWords aw fp modulusSize).toNat := by
    rw [UInt256.toNat_ofNat_of_lt (by omega : p < UInt256.size)]
    change p + 32 ≤ 32 * (newWordArrayWords aw fp k).toNat
    exact le_trans (by omega) hrange.1
  have hsetSize : (setFreePtr mem (fp + wordArrayAllocationSize k)).size = mem.size :=
    setFreePtr_size hmem96
  have hallocatedSize :
      (Modexp.MultiLimbBarrettConversion.allocatedMemory mem fp modulusSize).size = fp + 32 := by
    unfold Modexp.MultiLimbBarrettConversion.allocatedMemory
    apply storeBytesLength_size
    · rw [hsetSize]
      exact hmemLe
    · rwa [hsetSize]
  have hsourceHeader : mem.readWithPadding p 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    have hpres := wideWordResultMemory_readOperand I hb he hm
      (read := p) (by
        dsimp only [p]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega) (by
        dsimp only [p]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    exact hpres.trans (by
      simpa only [p] using operandCopiedMemory_readModulusLength I baseSize exponentSize
        modulusSize hb he)
  have hallocatedRead :
      (Modexp.MultiLimbBarrettConversion.allocatedMemory mem fp modulusSize).readWithPadding
          p 32 = UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    unfold Modexp.MultiLimbBarrettConversion.allocatedMemory
    rw [storeBytesLength_read_below_len_padded]
    · exact (setFreePtr_read_above_len_padded hmem96 (by
        dsimp only [p]
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega) (by decide) (by decide)).trans hsourceHeader
    · omega
    · decide
    · decide
    · rw [hsetSize]
      exact hgap
  have hload : wideLoadWord
      (Modexp.MultiLimbBarrettConversion.allocatedMemory mem fp modulusSize)
      (Modexp.MultiLimbBarrettConversion.allocatedWords aw fp modulusSize)
      (UInt256.ofNat p) = UInt256.ofNat modulusSize := by
    apply wideLoadWord_eq_of_read
    · rw [UInt256.toNat_ofNat_of_lt (by omega : p < UInt256.size), hallocatedSize]
      omega
    · intro hge
      have hfitAw :
          (Modexp.MultiLimbBarrettConversion.allocatedWords aw fp modulusSize).toNat * 32 <
            UInt256.size := by
        simpa [Modexp.MultiLimbBarrettConversion.allocatedWords] using hrange.2
      have hmul := umul_toNat
        (a := Modexp.MultiLimbBarrettConversion.allocatedWords aw fp modulusSize)
        (b := UInt256.ofNat 32) hfitAw
      have hnat := hge
      change (Modexp.MultiLimbBarrettConversion.allocatedWords aw fp modulusSize *
        UInt256.ofNat 32).toNat ≤ (UInt256.ofNat p).toNat at hnat
      rw [hmul, UInt256.toNat_ofNat_of_lt (by decide : 32 < UInt256.size),
        UInt256.toNat_ofNat_of_lt (by omega : p < UInt256.size)] at hnat
      have hcover : fp + 32 + 32 * k ≤
          32 * (Modexp.MultiLimbBarrettConversion.allocatedWords aw fp modulusSize).toNat := by
        simpa [Modexp.MultiLimbBarrettConversion.allocatedWords] using hrange.1
      omega
    · simpa only [UInt256.toNat_ofNat_of_lt (by omega : p < UInt256.size)] using
        hallocatedRead
  have hbaseHeader : mem.readWithPadding operandBasePtr 32 =
      UInt256.toByteArray (UInt256.ofNat baseSize) := by
    have hpres := wideWordResultMemory_readOperand I hb he hm
      (read := operandBasePtr) (by unfold operandBasePtr; omega) (by
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
    exact hpres.trans (operandCopiedMemory_readBaseLength I baseSize exponentSize modulusSize hb he)
  apply directSelection_exists hmodLarge hm hp32 hp64 hpend
    (by
      dsimp only [p]
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    hsourceBefore hactive (by simpa only [mem, aw, p] using hfirst)
    (by
      dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega)
    hallocationBound hmem96 hmemLe hgap haw3 haw64 hawFit hfree hcalldata haccess hload
    hbasePos hb (by unfold operandBasePtr; omega)
    (by
      dsimp only [fp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega)
    hbaseHeader (by simpa only [k] using hbackend) hdepth
    (by simpa only [mem, aw, p, fp] using rd0)

/-- The direct backend's initialized accumulator memory still contains the prepared exponent
header. -/
theorem DirectSelection.preparedExponentHeader
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    (initializedMemory selected.constant.finalMemory rFp k).readWithPadding
        (operandExponentPtr baseSize) 32 =
      UInt256.toByteArray (UInt256.ofNat exponentSize) := by
  dsimp only
  have hframe := selected.initializedReadBelow (operandExponentPtr baseSize)
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega)
  have hpres := wideWordResultMemory_readOperand I hb he hm
    (read := operandExponentPtr baseSize)
    (by unfold operandExponentPtr operandBasePtr bytesAllocationSize; omega)
    (by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  exact hframe.trans (hpres.trans
    (operandCopiedMemory_readExponentLength I baseSize exponentSize modulusSize hb he))

/-- Every exponent byte used by the direct selector is the corresponding trusted calldata byte. -/
theorem DirectSelection.preparedExponentByte
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (start : Nat) (hstart : start < exponentSize) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    (initializedMemory selected.constant.finalMemory rFp k).readWithPadding
        (operandExponentPtr baseSize + 32 + start) 1 =
      I.calldata.readWithPadding (96 + baseSize + start) 1 := by
  dsimp only
  let initialized := initializedMemory selected.constant.finalMemory
    (accumulatorFp selected.reduced.finalFreePtr
      (Modexp.MultiLimbBarrettConversion.words modulusSize))
    (Modexp.MultiLimbBarrettConversion.words modulusSize)
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let read := operandExponentPtr baseSize + 32 + start
  have hread64 : read < 2 ^ 64 := by
    dsimp only [read]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hframe32 := selected.initializedReadBelow read
    (by
      dsimp only [read]
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by
      dsimp only [read]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega)
  have hinitialOne : initialized.readWithPadding read 1 = mem.readWithPadding read 1 := by
    calc
      initialized.readWithPadding read 1 =
          (initialized.readWithPadding read 32).extract 0 1 := by
            symm
            exact readWithPadding_window initialized read 32 0 1 hread64 (by decide)
              (by simpa using hread64) (by decide) (by omega)
      _ = (mem.readWithPadding read 32).extract 0 1 := by
            exact congrArg (fun bs : ByteArray => bs.extract 0 1)
              (by simpa only [initialized, mem] using hframe32)
      _ = mem.readWithPadding read 1 := by
            exact readWithPadding_window mem read 32 0 1 hread64 (by decide)
              (by simpa using hread64) (by decide) (by omega)
  have hwideOriginal : mem.readWithPadding read 1 =
      (operandCopiedMemory I baseSize exponentSize modulusSize).readWithPadding read 1 := by
    exact wideWordResultMemory_readOperandLen I hb he hm
      (by
        dsimp only [read]
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega)
      (by decide) (by decide)
      (by
        have hsize := operandCopiedMemory_size_ge I baseSize exponentSize modulusSize hb he
        apply le_trans (b := operandModulusPtr baseSize exponentSize + 32)
        · dsimp only [read]
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
          omega
        · exact hsize)
      (by
        dsimp only [read]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
  have hwindow := operandCopiedExponentWindow I baseSize exponentSize modulusSize start 1
    hb he (by omega)
  have hcalldataRead : Model.readPadded I.calldata (96 + baseSize + start) 1 =
      I.calldata.readWithPadding (96 + baseSize + start) 1 := by
    symm
    exact readWithPadding_eq_model_readPadded I.calldata (96 + baseSize + start) 1
      (by omega) (by decide)
  exact hinitialOne.trans (hwideOriginal.trans (hwindow.trans hcalldataRead))

/-- Concrete exponent access bounds for the direct prepared selector. -/
theorem DirectSelection.preparedExponentAccessFrame
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    Modexp.MultiLimbBarrettExponentLoop.BarrettExponentAccessFrame
      (initializedMemory selected.constant.finalMemory rFp k)
      (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat exponentSize)
      (UInt256.ofNat rFp) := by
  dsimp only
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  have hexponentPtr : operandExponentPtr baseSize < UInt256.size := by
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    exact lt_of_le_of_lt (by omega) (by decide : 1216 < UInt256.size)
  have hexponentSize : exponentSize < UInt256.size :=
    lt_trans (by omega : exponentSize < 2 ^ 64) (by norm_num [UInt256.size])
  have hrFp64 : rFp < 2 ^ 64 := by
    have hbackend := selected.backendWorkspace
    have hfinalFree :=
      Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
        selected.entryFacts selected.reduced
    have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd
        (rFp + wordArrayAllocationSize k) k < 2 ^ 64 := by
      apply lt_of_le_of_lt
        (scratchEnd_afterAccumulator_le_reserve selected.reduced.finalFreePtr k
          selected.entryFacts.divisorBound)
      dsimp only [rFp, k] at hbackend hfinalFree ⊢
      omega
    apply lt_trans (b := Modexp.MultiLimbBarrettReusedCall.scratchEnd
      (rFp + wordArrayAllocationSize k) k)
    · unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
        Modexp.MultiLimbBarrettReusedCall.callResultFp wordArrayAllocationSize
        wordArrayPayloadSize
      omega
    · exact hscratch
  have hrFp256 : rFp < UInt256.size := lt_trans hrFp64 (by norm_num [UInt256.size])
  have hheader := DirectSelection.preparedExponentHeader selected hb he hm
  have hmemSize : 96 ≤ selected.constant.finalMemory.size := by
    rw [selected.constant.finalMemorySize]
    unfold normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
      wordArrayAllocationSize wordArrayPayloadSize
    omega
  have hmemLe : selected.constant.finalMemory.size ≤ rFp := by
    rw [selected.constant.finalMemorySize]
    rfl
  have hgap : rFp - selected.constant.finalMemory.size < USize.size := by
    rw [selected.constant.finalMemorySize]
    dsimp only [rFp, k]
    simpa [accumulatorFp] using (lt_usize 0 (by omega))
  have hinitialSize := initializedMemory_size selected.constant.finalMemory rFp k
    hmemSize hmemLe hgap
  have hexponentBelow : operandExponentPtr baseSize + 32 ≤ rFp := by
    apply le_trans (b := wideBarrettNormalizedFp baseSize exponentSize modulusSize)
    · unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · apply le_trans (b := selected.reduced.finalFreePtr)
      · apply le_trans (b := directRemFp
            (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize baseSize +
            wordArrayAllocationSize k)
        · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.reduced
      · dsimp only [rFp]
        unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega
  refine {
    exponentBase := ?_
    exponentBelowAccumulator := ?_
    headerConcrete := ?_
    header := ?_
    exponentFit := ?_
    byteFit := ?_ }
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr, UInt256.toNat_ofNat_of_lt hrFp256]
    exact hexponentBelow
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr, hinitialSize]
    exact hexponentBelow.trans (Nat.le_add_right rFp 64)
  · simpa only [k, rFp, UInt256.toNat_ofNat_of_lt hexponentPtr] using hheader
  · rw [UInt256.toNat_ofNat_of_lt hexponentPtr]
    exact lt_trans (by
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega : operandExponentPtr baseSize + 32 + 31 < 2 ^ 64)
      (by norm_num [UInt256.size])
  · intro idx hidx
    have hidxNat : idx.toNat < exponentSize := by
      have hlt : idx < UInt256.ofNat exponentSize := by
        by_contra hn
        apply hidx
        simp [UInt256.lt, hn]
        rfl
      change idx.toNat < (UInt256.ofNat exponentSize).toNat at hlt
      rw [UInt256.toNat_ofNat_of_lt hexponentSize] at hlt
      exact hlt
    have hinner : idx.toNat + operandExponentPtr baseSize < UInt256.size :=
      lt_trans (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega : idx.toNat + operandExponentPtr baseSize < 2 ^ 64)
        (by norm_num [UInt256.size])
    have houter : 32 + (idx.toNat + operandExponentPtr baseSize) < UInt256.size :=
      lt_trans (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega : 32 + (idx.toNat + operandExponentPtr baseSize) < 2 ^ 64)
        (by norm_num [UInt256.size])
    unfold Modexp.MultiLimbExponentTrace.exponentByteAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide, uadd_toNat,
      UInt256.toNat_ofNat_of_lt hexponentPtr, Nat.mod_eq_of_lt hinner,
      Nat.mod_eq_of_lt houter]
    exact lt_trans (by
      unfold operandExponentPtr operandBasePtr bytesAllocationSize
      omega : 32 + (idx.toNat + operandExponentPtr baseSize) + 32 + 31 < 2 ^ 64)
      (by norm_num [UInt256.size])

/-- Model alignment for the complete direct exponent selector, derived from the concrete copied
calldata frame. -/
theorem DirectSelection.preparedExponentAlignment
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let k := Modexp.MultiLimbBarrettConversion.words modulusSize
      let rFp := accumulatorFp selected.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.constant.finalMemory rFp k)
        (allocatedWords selected.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize baseSize))
        (UInt256.ofNat (wideBarrettNormalizedFp baseSize exponentSize modulusSize))
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I baseSize exponentSize
      (UInt256.ofNat exponentSize).toNat 8 k k (rFp + wordArrayAllocationSize k)
      (UInt256.ofNat rFp) (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (UInt256.ofNat modulusFp)
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
      (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat exponentSize)
      (initializedMemory selected.constant.finalMemory rFp k)
      (allocatedWords selected.constant.finalWords rFp k) exponentSelected := by
  dsimp only
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  let loopFp := rFp + wordArrayAllocationSize k
  let exponent := UInt256.ofNat (operandExponentPtr baseSize)
  let expLen := UInt256.ofNat exponentSize
  let r := UInt256.ofNat rFp
  let a := UInt256.ofNat remFp
  let modulus := UInt256.ofNat modulusFp
  let mu := UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k)
  let initialMem := initializedMemory selected.constant.finalMemory rFp k
  let initialAw := allocatedWords selected.constant.finalWords rFp k
  have hbackend := selected.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, modulusFp, k] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤ selected.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.entryFacts selected.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.reduced.finalFreePtr k
        selected.entryFacts.divisorBound)
    dsimp only [loopFp, rFp, remFp, modulusFp, k] at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.entryFacts hreduceWorkspace
    selected.reduced selected.constant hconstantAfter hscratch selected.calldataBound
    selected.baseInput_eq selected.modulus_eq
  have access := DirectSelection.preparedExponentAccessFrame selected hb he hm
  have hrFp64 : rFp < 2 ^ 64 := by
    dsimp only [loopFp] at hscratch
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    omega
  have hrFp256 : rFp < UInt256.size := lt_trans hrFp64 (by norm_num [UInt256.size])
  have hexponentSize : exponentSize < UInt256.size :=
    lt_trans (by omega : exponentSize < 2 ^ 64) (by norm_num [UInt256.size])
  have hexponentPtr : operandExponentPtr baseSize < UInt256.size := by
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    exact lt_of_le_of_lt (by omega) (by decide : 1216 < UInt256.size)
  have haddress : ∀ s, s < exponentSize →
      (Modexp.MultiLimbExponentTrace.exponentByteAddress exponent
        (UInt256.ofNat s)).toNat = exponent.toNat + 32 + s := by
    intro s hs
    have hsWord : s < UInt256.size := lt_trans hs hexponentSize
    have hinner : s + operandExponentPtr baseSize < UInt256.size :=
      lt_trans (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega : s + operandExponentPtr baseSize < 2 ^ 64)
        (by norm_num [UInt256.size])
    have houter : 32 + (s + operandExponentPtr baseSize) < UInt256.size :=
      lt_trans (by
        unfold operandExponentPtr operandBasePtr bytesAllocationSize
        omega : 32 + (s + operandExponentPtr baseSize) < 2 ^ 64)
        (by norm_num [UInt256.size])
    unfold Modexp.MultiLimbExponentTrace.exponentByteAddress
    rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 by decide, uadd_toNat,
      UInt256.toNat_ofNat_of_lt hsWord, UInt256.toNat_ofNat_of_lt hexponentPtr,
      Nat.mod_eq_of_lt hinner, Nat.mod_eq_of_lt houter]
    omega
  have hpayloadBelow : exponent.toNat + 32 + exponentSize + 31 ≤ r.toNat := by
    rw [show exponent.toNat = operandExponentPtr baseSize by
        dsimp only [exponent]; rw [UInt256.toNat_ofNat_of_lt hexponentPtr],
      show r.toNat = rFp by
        dsimp only [r]; rw [UInt256.toNat_ofNat_of_lt hrFp256]]
    apply le_trans (b := modulusFp)
    · dsimp only [modulusFp]
      unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
        operandBasePtr bytesAllocationSize
      omega
    · apply le_trans (b := remFp + wordArrayAllocationSize k)
      · dsimp only [remFp]
        unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
        omega
      · apply le_trans (b := selected.reduced.finalFreePtr)
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.reduced
        · dsimp only [rFp]
          unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega
  have hconstantSize : selected.constant.finalMemory.size = rFp := by
    rw [selected.constant.finalMemorySize]
    rfl
  have hinitialSize : initialMem.size = rFp + 64 := by
    apply initializedMemory_size
    · rw [hconstantSize]
      have hr := invariant.rBase
      change 96 ≤ (UInt256.ofNat rFp).toNat at hr
      rw [UInt256.toNat_ofNat_of_lt hrFp256] at hr
      exact hr
    · rw [hconstantSize]
    · rw [hconstantSize, Nat.sub_self]
      native_decide
  have hpayloadConcrete : exponent.toNat + 32 + exponentSize + 31 ≤ initialMem.size := by
    rw [hinitialSize]
    have hrNat : r.toNat = rFp := by
      dsimp only [r]
      rw [UInt256.toNat_ofNat_of_lt hrFp256]
    rw [hrNat] at hpayloadBelow
    omega
  have haddress64 : exponent.toNat + 32 + exponentSize < 2 ^ 64 := by
    rw [show exponent.toNat = operandExponentPtr baseSize by
      dsimp only [exponent]; rw [UInt256.toNat_ofNat_of_lt hexponentPtr]]
    unfold operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hcalldataBound : 96 + baseSize + exponentSize < 2 ^ 64 := by omega
  have hsource : ∀ s, s < exponentSize →
      initialMem.readWithPadding (exponent.toNat + 32 + s) 1 =
        I.calldata.readWithPadding (96 + baseSize + s) 1 := by
    intro s hs
    have hbyte := DirectSelection.preparedExponentByte selected hb he hm s hs
    simpa only [initialMem, exponent, k, rFp,
      UInt256.toNat_ofNat_of_lt hexponentPtr] using hbyte
  unfold Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup at hselect
  exact Modexp.MultiLimbBarrettResultSemantic.selectFreshBarrettLoopSetup_modelAlignmentFramed
    invariant access rfl hexponentSize haddress hpayloadConcrete hpayloadBelow haddress64
    hcalldataBound hsource hselect

/-- Executable validity, memory coverage, and exact exponent-array length for a selected direct
prepared exponent trace. -/
theorem DirectSelection.preparedExponentValid
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let k := Modexp.MultiLimbBarrettConversion.words modulusSize
      let rFp := accumulatorFp selected.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.constant.finalMemory rFp k)
        (allocatedWords selected.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize baseSize))
        (UInt256.ofNat (wideBarrettNormalizedFp baseSize exponentSize modulusSize))
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I k k
        (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
        (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat exponentSize)
        (initializedMemory selected.constant.finalMemory rFp k)
        (allocatedWords selected.constant.finalWords rFp k) exponentSelected ∧
      rFp + 64 ≤ exponentSelected.memory.size ∧
      rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat ∧
      exponentSelected.activeWords.toNat * 32 < UInt256.size ∧
      Modexp.MultiLimbExponentTrace.exponentArrayLength
        (initializedMemory selected.constant.finalMemory rFp k)
        (allocatedWords selected.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) = UInt256.ofNat exponentSize := by
  dsimp only
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  let loopFp := rFp + wordArrayAllocationSize k
  let exponent := UInt256.ofNat (operandExponentPtr baseSize)
  let expLen := UInt256.ofNat exponentSize
  let r := UInt256.ofNat rFp
  let a := UInt256.ofNat remFp
  let modulus := UInt256.ofNat modulusFp
  let mu := UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k)
  let initialMem := initializedMemory selected.constant.finalMemory rFp k
  let initialAw := allocatedWords selected.constant.finalWords rFp k
  have hbackend := selected.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, modulusFp, k] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤ selected.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.entryFacts selected.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.reduced.finalFreePtr k
        selected.entryFacts.divisorBound)
    dsimp only [loopFp, rFp, remFp, modulusFp, k] at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.entryFacts hreduceWorkspace
    selected.reduced selected.constant hconstantAfter hscratch selected.calldataBound
    selected.baseInput_eq selected.modulus_eq
  have access := DirectSelection.preparedExponentAccessFrame selected hb he hm
  have hrFp64 : rFp < 2 ^ 64 := by
    dsimp only [loopFp] at hscratch
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    omega
  have hrFp256 : rFp < UInt256.size := lt_trans hrFp64 (by norm_num [UInt256.size])
  have hconstantSize : selected.constant.finalMemory.size = rFp := by
    rw [selected.constant.finalMemorySize]
    rfl
  have hrFp96 : 96 ≤ rFp := by
    have hr := invariant.rBase
    change 96 ≤ (UInt256.ofNat rFp).toNat at hr
    rw [UInt256.toNat_ofNat_of_lt hrFp256] at hr
    exact hr
  have hfreeRead : initialMem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat loopFp) := by
    dsimp only [initialMem, loopFp]
    apply Modexp.MultiLimbBarrettAccumulator.initializedMemory_freePointer
    · rw [hconstantSize]
      exact hrFp96
    · rw [hconstantSize]
    · rw [hconstantSize, Nat.sub_self]
      native_decide
    · exact hrFp96
  have hlength : Modexp.MultiLimbExponentTrace.exponentArrayLength initialMem initialAw
      exponent = expLen := by
    exact Modexp.MultiLimbBarrettExponentLoop.exponentArrayLength_eq_of_header
      invariant.covered invariant.activeWordsFit access.headerConcrete access.header
  unfold Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup at hselect
  have result :=
    Modexp.MultiLimbBarrettResultSemantic.selectFreshBarrettLoopSetup_validInvariantFramedAllocated
      invariant access hfreeRead hselect
  refine ⟨result.1, ?_⟩
  cases exponentSelected with
  | allZero scan =>
      cases result.1 with
      | allZero scanValid exhausted =>
          constructor
          · have hinitialSize : initialMem.size = rFp + 64 := by
              dsimp only [initialMem]
              apply Modexp.MultiLimbBarrettAccumulator.initializedMemory_size
              · rw [hconstantSize]
                exact hrFp96
              · rw [hconstantSize]
              · rw [hconstantSize, Nat.sub_self]
                native_decide
            change rFp + 64 ≤ scan.memory.size
            rw [scanValid.memoryEq]
            simpa only [initialMem, rFp, k] using hinitialSize.ge
          · constructor
            · change rFp + 32 + 32 * k ≤ 32 * scan.activeWords.toNat
              have hfit : rFp + wordArrayAllocationSize k + 31 < UInt256.size := by
                apply lt_trans (b := 2 ^ 64)
                · apply lt_of_le_of_lt (b :=
                      Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k)
                  · dsimp only [loopFp]
                    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
                      Modexp.MultiLimbBarrettReusedCall.callResultFp
                      wordArrayAllocationSize wordArrayPayloadSize
                    omega
                  · exact hscratch
                · norm_num [UInt256.size]
              have hrange :=
                Modexp.MultiLimbOddConversionSemantic.newWordArrayWords_range
                  selected.constant.finalWords rFp k invariant.wordsPos
                  selected.constant.finalWordsFit hfit
              have hheaderMono :=
                Modexp.MultiLimbBarrettResultSemantic.readWords1_active_mono
                  initialAw exponent invariant.activeWordsFit access.exponentFit
              have scanStartInvariant :=
                invariant.afterExponentArrayLengthLoad access.exponentFit
              have hscanMono :=
                Modexp.MultiLimbBarrettResultSemantic.BarrettLeadingScanValid.initialActive_le
                  scanValid scanStartInvariant access
              have hmono : initialAw.toNat ≤ scan.activeWords.toNat :=
                hheaderMono.trans hscanMono
              apply le_trans (b := 32 * initialAw.toNat)
              · simpa only [initialAw, Modexp.MultiLimbBarrettAccumulator.allocatedWords,
                  wordArrayAllocationSize, wordArrayPayloadSize] using hrange.1
              · exact Nat.mul_le_mul_left 32 hmono
            · constructor
              · have scanStartInvariant :=
                    invariant.afterExponentArrayLengthLoad access.exponentFit
                have scanInvariant := scanValid.preserveInitialInvariant scanStartInvariant
                  access.exponentFit access.byteFit
                simpa [Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection.activeWords]
                  using scanInvariant.activeWordsFit
              · simpa only [initialMem, initialAw, exponent, expLen, k, rFp] using hlength
  | nonzero scan top first rest =>
      rcases result.2 with ⟨finalValue, finalInvariant⟩
      constructor
      · change rFp + 64 ≤ rest.memory.size
        have hrScratch : rFp + 64 ≤
            Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k := by
          dsimp only [loopFp]
          unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
            Modexp.MultiLimbBarrettReusedCall.callResultFp wordArrayAllocationSize
            wordArrayPayloadSize
          omega
        exact hrScratch.trans finalInvariant.scratchConcrete
      · constructor
        · change rFp + 32 + 32 * k ≤ 32 * rest.activeWords.toNat
          apply le_trans (b := Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k)
          · dsimp only [loopFp]
            unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
              Modexp.MultiLimbBarrettReusedCall.callResultFp wordArrayAllocationSize
              wordArrayPayloadSize
            omega
          · exact finalInvariant.scratchConcrete.trans finalInvariant.covered
        · constructor
          · simpa [Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection.activeWords]
              using finalInvariant.activeWordsFit
          · simpa only [initialMem, initialAw, exponent, expLen, k, rFp] using hlength

/-- Canonical complete exponent selection for the prepared direct multi-limb backend. -/
theorem DirectSelection.preparedExponentSelection
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let exponent := UInt256.ofNat (operandExponentPtr baseSize)
    let expLen := UInt256.ofNat exponentSize
    let initialMem := initializedMemory selected.constant.finalMemory rFp k
    let initialAw := allocatedWords selected.constant.finalWords rFp k
    ∃ exponentSelected,
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k) initialMem initialAw exponent
        (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
        (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k)) expLen =
          some exponentSelected ∧
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupValid I k k
        (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
        (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k)) exponent expLen
        initialMem initialAw exponentSelected ∧
      rFp + 64 ≤ exponentSelected.memory.size ∧
      rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat ∧
      exponentSelected.activeWords.toNat * 32 < UInt256.size ∧
      Modexp.MultiLimbExponentTrace.exponentArrayLength initialMem initialAw exponent =
        expLen ∧
      Modexp.MultiLimbBarrettResultSemantic.FreshBarrettModelAlignment I baseSize exponentSize
        expLen.toNat 8 k k (rFp + wordArrayAllocationSize k) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
        (UInt256.ofNat modulusFp)
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k)) exponent expLen
        initialMem initialAw exponentSelected := by
  dsimp only
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  have hkPos : 0 < k := by
    have hkTwo := selected.entryFacts.divisorTwo
    simpa only [k] using lt_of_lt_of_le (by decide : 0 < 2) hkTwo
  rcases Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup_exists
      (mem := initializedMemory selected.constant.finalMemory rFp k)
      (aw := allocatedWords selected.constant.finalWords rFp k)
      (exponent := UInt256.ofNat (operandExponentPtr baseSize))
      (r := UInt256.ofNat rFp)
      (a := UInt256.ofNat (directRemFp modulusFp modulusSize baseSize))
      (n := UInt256.ofNat modulusFp)
      (mu := UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
      (expLen := UInt256.ofNat exponentSize) hkPos with ⟨exponentSelected, hselect⟩
  have hvalid := DirectSelection.preparedExponentValid selected hb he hm hselect
  exact ⟨exponentSelected, hselect, hvalid.1, hvalid.2.1, hvalid.2.2.1,
    hvalid.2.2.2.1, hvalid.2.2.2.2,
    DirectSelection.preparedExponentAlignment selected hb he hm hselect⟩

/-- Complete fixed words below the direct accumulator are frame-preserved by the selected
exponent trace. -/
theorem DirectSelection.preparedExponentReadBelow
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret read : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hread : 96 ≤ read)
    (hbelow : read + 32 ≤ accumulatorFp selected.reduced.finalFreePtr
      (Modexp.MultiLimbBarrettConversion.words modulusSize))
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (hselect :
      let k := Modexp.MultiLimbBarrettConversion.words modulusSize
      let rFp := accumulatorFp selected.reduced.finalFreePtr k
      Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
        (rFp + wordArrayAllocationSize k)
        (initializedMemory selected.constant.finalMemory rFp k)
        (allocatedWords selected.constant.finalWords rFp k)
        (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
        (UInt256.ofNat (directRemFp
          (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize baseSize))
        (UInt256.ofNat (wideBarrettNormalizedFp baseSize exponentSize modulusSize))
        (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
        (UInt256.ofNat exponentSize) = some exponentSelected) :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    exponentSelected.memory.readWithPadding read 32 =
      (initializedMemory selected.constant.finalMemory rFp k).readWithPadding read 32 := by
  dsimp only
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let remFp := directRemFp modulusFp modulusSize baseSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  let loopFp := rFp + wordArrayAllocationSize k
  let exponent := UInt256.ofNat (operandExponentPtr baseSize)
  let expLen := UInt256.ofNat exponentSize
  let r := UInt256.ofNat rFp
  let a := UInt256.ofNat remFp
  let modulus := UInt256.ofNat modulusFp
  let mu := UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k)
  let initialMem := initializedMemory selected.constant.finalMemory rFp k
  let initialAw := allocatedWords selected.constant.finalWords rFp k
  have hbackend := selected.backendWorkspace
  have hreduceWorkspace : remFp + wordArrayAllocationSize k +
      Modexp.MultiLimbBarrettReduceBaseComplete.workspaceBytes < 2 ^ 64 := by
    dsimp only [remFp, modulusFp, k] at hbackend ⊢
    omega
  have hconstantAfter : remFp + 32 * (k + 1) ≤ selected.reduced.finalFreePtr := by
    apply le_trans (b := remFp + wordArrayAllocationSize k)
    · unfold wordArrayAllocationSize wordArrayPayloadSize
      omega
    · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
        selected.reduced
  have hfinalFree :=
    Modexp.MultiLimbBarrettReduceBaseComplete.Selection.finalFreePtr_le_workspace
      selected.entryFacts selected.reduced
  have hscratch : Modexp.MultiLimbBarrettReusedCall.scratchEnd loopFp k < 2 ^ 64 := by
    apply lt_of_le_of_lt
      (scratchEnd_afterAccumulator_le_reserve selected.reduced.finalFreePtr k
        selected.entryFacts.divisorBound)
    dsimp only [loopFp, rFp, remFp, modulusFp, k] at hbackend hfinalFree ⊢
    omega
  have invariant := reducedInitializedInvariant selected.entryFacts hreduceWorkspace
    selected.reduced selected.constant hconstantAfter hscratch selected.calldataBound
    selected.baseInput_eq selected.modulus_eq
  have access := DirectSelection.preparedExponentAccessFrame selected hb he hm
  have hrFp64 : rFp < 2 ^ 64 := by
    dsimp only [loopFp] at hscratch
    unfold Modexp.MultiLimbBarrettReusedCall.scratchEnd
      Modexp.MultiLimbBarrettReusedCall.callResultFp at hscratch
    omega
  have hrFp256 : rFp < UInt256.size := lt_trans hrFp64 (by norm_num [UInt256.size])
  have hbelow' : read + 32 ≤ r.toNat := by
    dsimp only [r]
    rw [UInt256.toNat_ofNat_of_lt hrFp256]
    exact hbelow
  unfold Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup at hselect
  exact Modexp.MultiLimbBarrettResultSemantic.selectFreshBarrettLoopSetup_readBelowFramed
    invariant access hread hbelow' hselect

/-- The prepared result allocation preserves both operand values exactly. -/
theorem preparedWideResultValues_eq_calldata
    (I : ExecutionEnv) {baseSize exponentSize modulusSize : Nat}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodPos : 0 < modulusSize) :
    Model.bytesToNatPadded (wideWordResultMemory I baseSize exponentSize modulusSize)
        (operandBasePtr + 32) baseSize =
        Model.bytesToNatPadded I.calldata 96 baseSize ∧
      Model.bytesToNatPadded (wideWordResultMemory I baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize + 32) modulusSize =
        Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
  have hbaseRead := wideWordResultMemory_readOperandLenPadded I hb he hm
    (read := operandBasePtr + 32) (len := baseSize)
    (by unfold operandBasePtr; omega) hbasePos (by omega) (by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  have hmodRead := wideWordResultMemory_readOperandLenPadded I hb he hm
    (read := operandModulusPtr baseSize exponentSize + 32) (len := modulusSize)
    (by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega) hmodPos (by omega) (by
      unfold operandFreePtr operandModulusPtr bytesAllocationSize
      omega)
  have hbasePrepared := model_bytesToNatPadded_eq_of_readWithPadding
    (by unfold operandBasePtr; omega) (by unfold operandBasePtr; omega) (by omega) hbaseRead
  have hmodPrepared := model_bytesToNatPadded_eq_of_readWithPadding
    (by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by
      unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
      omega)
    (by omega) hmodRead
  have hbaseCopied : Model.bytesToNatPadded
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandBasePtr + 32) baseSize = Model.bytesToNatPadded I.calldata 96 baseSize := by
    unfold Model.bytesToNatPadded
    rw [← readWithPadding_eq_model_readPadded
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandBasePtr + 32) baseSize (by unfold operandBasePtr; omega) (by omega)]
    rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian]
    exact operandCopiedBaseValue I baseSize exponentSize modulusSize hb he
  have hmodCopied : Model.bytesToNatPadded
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize + 32) modulusSize =
        Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
    unfold Model.bytesToNatPadded
    rw [← readWithPadding_eq_model_readPadded
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusPtr baseSize exponentSize + 32) modulusSize (by
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
        omega) (by omega)]
    rw [bytesToBigEndianNat_eq_fromByteArrayBigEndian]
    exact operandCopiedModulusValue I baseSize exponentSize modulusSize hb he hm
  exact ⟨hbasePrepared.trans hbaseCopied, hmodPrepared.trans hmodCopied⟩

/-- Complete direct multi-limb execution with an exposed exponent selector, exact path gas, and
the public calldata model. -/
structure PreparedDirectExecution
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection) : Prop where
  selection :
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    Modexp.MultiLimbBarrettExponentSetup.selectCompleteFreshBarrettLoopSetup k
      (rFp + wordArrayAllocationSize k)
      (initializedMemory selected.constant.finalMemory rFp k)
      (allocatedWords selected.constant.finalWords rFp k)
      (UInt256.ofNat (operandExponentPtr baseSize)) (UInt256.ofNat rFp)
      (UInt256.ofNat (directRemFp
        (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize baseSize))
      (UInt256.ofNat (wideBarrettNormalizedFp baseSize exponentSize modulusSize))
      (UInt256.ofNat (quotientPtr selected.reduced.finalFreePtr k))
      (UInt256.ofNat exponentSize) = some exponentSelected
  execution :
    (let mem := wideWordResultMemory I baseSize exponentSize modulusSize
     let aw := wideWordResultWords baseSize exponentSize modulusSize
     let p := operandModulusPtr baseSize exponentSize
     let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
     let result := operandFreePtr baseSize exponentSize modulusSize
     let k := Modexp.MultiLimbBarrettConversion.words modulusSize
     let rFp := accumulatorFp selected.reduced.finalFreePtr k
     let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
       exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat result) modulusSize
     RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I)
        (UInt256.ofNat retBar) (UInt256.ofNat result :: UInt256.ofNat ret :: tail)
        serialized exponentSelected.activeWords ByteArray.empty acc
        (selected.scanSteps + 5 + MultiLimbReduceBase.nonzeroSteps baseSize k +
          selected.reduced.stepDelta +
          Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixSteps
            selected.reduced.finalMemory selected.reduced.finalWords
            selected.reduced.finalFreePtr k modulusFp + selected.constant.stepDelta +
          Modexp.MultiLimbBarrettResult.freshExecutionSteps exponentSelected modulusSize)
        (gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
            modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
            (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
            (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
            (directBaseFp modulusFp modulusSize)
            (directRemFp modulusFp modulusSize baseSize) baseSize k
            (UInt256.ofNat operandBasePtr) + selected.reduced.gasDelta +
          Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
            selected.reduced.finalMemory selected.reduced.finalWords
            selected.reduced.finalFreePtr k modulusFp + selected.constant.gasDelta +
          Modexp.MultiLimbBarrettResult.freshExecutionGas selected.constant.finalWords
            rFp k (UInt256.ofNat (operandExponentPtr baseSize)) exponentSelected modulusSize) ∧
      Modexp.MultiLimbBarrettExponentSemantic.barrettAccumulatorValue k
          (UInt256.ofNat rFp) exponentSelected.memory =
        Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize ∧
      serialized.readWithPadding (result + 32) modulusSize =
        Model.natToBytes
          (Model.bytesToNatPadded I.calldata 96 baseSize ^
            Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
              Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
          modulusSize ∧
      Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize <
        256 ^ modulusSize)

/-- Select and execute the prepared direct multi-limb branch. -/
theorem DirectSelection.preparedExecution
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    (selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodPos : 0 < modulusSize)
    (hretBar : (D_J runtimeBytecode 0).contains (UInt256.ofNat retBar) = true)
    (hdepth : tail.length ≤ 972) :
    ∃ exponentSelected, PreparedDirectExecution selected exponentSelected := by
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  rcases DirectSelection.preparedExponentSelection selected hb he hm with
    ⟨exponentSelected, hselect, hvalid, hsize, hactive, hawFit, hlength, halignment⟩
  have haccess := DirectSelection.preparedExponentAccessFrame selected hb he hm
  have hvalid' := hvalid
  have halignment' := halignment
  have haccess' := haccess
  rw [← hlength] at hvalid' halignment' haccess'
  have hresultAddr64 : result + 32 + modulusSize < 2 ^ 64 := by
    dsimp only [result]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  have hresultMem : result + 32 + modulusSize ≤ exponentSelected.memory.size := by
    have hrLe : result + 32 + modulusSize ≤ rFp := by
      apply le_trans (b := modulusFp)
      · dsimp only [result, modulusFp]
        unfold wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega
      · apply le_trans (b := selected.reduced.finalFreePtr)
        · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
              wordArrayAllocationSize k)
          · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
            omega
          · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
              selected.reduced
        · dsimp only [rFp]
          unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega
    exact hrLe.trans (by
      have hs : rFp + 64 ≤ exponentSelected.memory.size := by
        simpa only [rFp, k] using hsize
      omega)
  have houtBefore : result + 32 + modulusSize ≤ rFp := by
    apply le_trans (b := modulusFp)
    · dsimp only [result, modulusFp]
      unfold wideBarrettNormalizedFp
      have halloc := bytesHeaderAndSize_le_allocation modulusSize
      omega
    · apply le_trans (b := selected.reduced.finalFreePtr)
      · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
            wordArrayAllocationSize k)
        · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.reduced
      · dsimp only [rFp]
        unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega
  have recursive := selected.freshReturn hvalid' halignment' haccess'
    (by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans (by omega : result < 2 ^ 64)
        (by norm_num [UInt256.size]))]
      exact lt_trans hresultAddr64 (by norm_num [UInt256.size]))
    (by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans (by omega : result < 2 ^ 64)
        (by norm_num [UInt256.size]))]
      exact hresultAddr64)
    (by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans (by omega : result < 2 ^ 64)
        (by norm_num [UInt256.size]))]
      exact hresultMem)
    (by simpa only [rFp, k] using hactive)
    (by
      rw [UInt256.toNat_ofNat_of_lt (lt_trans (by omega : result < 2 ^ 64)
        (by norm_num [UInt256.size]))]
      exact houtBefore)
    (by omega) hretBar
  have values := preparedWideResultValues_eq_calldata I hb he hm hbasePos hmodPos
  have hresultNat : (UInt256.ofNat result).toNat = result :=
    UInt256.toNat_ofNat_of_lt (lt_trans (by omega : result < 2 ^ 64)
      (by norm_num [UInt256.size]))
  refine ⟨exponentSelected, { selection := hselect, execution := ?_ }⟩
  simpa only [mem, aw, p, modulusFp, result, k, rFp, hresultNat, values.1, values.2]
    using recursive

/-- The direct serializer preserves the original Solidity `bytes` length header. -/
theorem PreparedDirectExecution.resultHeader
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    {selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat retBar) (UInt256.ofNat ret) tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (execution : PreparedDirectExecution selected exponentSelected)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize) :
    (Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
      exponentSelected.activeWords
      (UInt256.ofNat (accumulatorFp selected.reduced.finalFreePtr
        (Modexp.MultiLimbBarrettConversion.words modulusSize)))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize)) modulusSize
    ).readWithPadding (operandFreePtr baseSize exponentSize modulusSize) 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
  let result := operandFreePtr baseSize exponentSize modulusSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  let source := wideWordResultMemory I baseSize exponentSize modulusSize
  let initialized := initializedMemory selected.constant.finalMemory rFp k
  have hsourceHeader : source.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    unfold source result wideWordResultMemory
    apply storeBytesLength_read_self
    apply lt_of_le_of_lt (Nat.sub_le _ _)
    exact lt_usize _ (by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  have hinitialHeader : initialized.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    have hframe := selected.initializedReadBelow result
      (by
        dsimp only [result]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by
        dsimp only [result, modulusFp]
        unfold wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega)
    have hframe' : initialized.readWithPadding result 32 = source.readWithPadding result 32 := by
      simpa only [initialized, rFp, k, source] using hframe
    exact hframe'.trans hsourceHeader
  have hexponentHeader := DirectSelection.preparedExponentReadBelow selected hb he hm
    (read := result)
    (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    (by
      apply le_trans (b := modulusFp)
      · dsimp only [result, modulusFp]
        unfold wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega
      · apply le_trans (b := selected.reduced.finalFreePtr)
        · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
              wordArrayAllocationSize k)
          · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
            omega
          · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
              selected.reduced
        · dsimp only [rFp]
          unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
    execution.selection
  have hresultNat : (UInt256.ofNat result).toNat = result :=
    UInt256.toNat_ofNat_of_lt (lt_trans (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega : result < 2 ^ 64) (by norm_num [UInt256.size]))
  have hmem : result + 32 + modulusSize ≤ exponentSelected.memory.size := by
    have hexec := execution.execution
    have hsize : rFp + 64 ≤ exponentSelected.memory.size := by
      rcases DirectSelection.preparedExponentSelection selected hb he hm with
        ⟨chosen, hchosen, hvalid, hsize, rest⟩
      have hsame : chosen = exponentSelected := by
        rw [execution.selection] at hchosen
        exact Option.some.inj hchosen.symm
      subst chosen
      simpa only [rFp, k] using hsize
    have hbefore : result + 32 + modulusSize ≤ rFp := by
      apply le_trans (b := modulusFp)
      · dsimp only [result, modulusFp]
        unfold wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega
      · apply le_trans (b := selected.reduced.finalFreePtr)
        · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
              wordArrayAllocationSize k)
          · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
            omega
          · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
              selected.reduced
        · dsimp only [rFp]
          unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega
    exact hbefore.trans (by omega)
  apply Eq.trans (Modexp.MultiLimbBarrettResultSemantic.resultMemory_read_below
    (result := UInt256.ofNat result) (fp := rFp) (dataLen := modulusSize) (read := result) hm
    (by rw [hresultNat]; exact lt_trans (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega : result + 32 + modulusSize < 2 ^ 64) (by norm_num [UInt256.size]))
    (by rw [hresultNat]; exact hmem)
    (by intro _; rw [hresultNat]; omega)
    (by rw [hresultNat]))
  have hframe : exponentSelected.memory.readWithPadding result 32 =
      initialized.readWithPadding result 32 := by
    simpa only [rFp, k, initialized, result] using hexponentHeader
  exact hframe.trans hinitialHeader

/-- Execute the real PC 1271 trampoline and wrapper return for a prepared direct execution. -/
theorem PreparedDirectExecution.returnExact
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize : Nat}
    {tail : List UInt256}
    {selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat 1271) (UInt256.ofNat 173) tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (execution : PreparedDirectExecution selected exponentSelected)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hdepth : tail.length ≤ 972) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words modulusSize
    let rFp := accumulatorFp selected.reduced.finalFreePtr k
    RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
      (Model.natToBytes
        (Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
        modulusSize)
      (gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
          modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
          (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
          (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
          (directBaseFp modulusFp modulusSize)
          (directRemFp modulusFp modulusSize baseSize) baseSize k
          (UInt256.ofNat operandBasePtr) + selected.reduced.gasDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
          selected.reduced.finalMemory selected.reduced.finalWords
          selected.reduced.finalFreePtr k modulusFp + selected.constant.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas selected.constant.finalWords
          rFp k (UInt256.ofNat (operandExponentPtr baseSize)) exponentSelected modulusSize + 28) := by
  dsimp only
  let result := operandFreePtr baseSize exponentSize modulusSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
    exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat result) modulusSize
  have hexec := execution.execution
  have rd1271 := hexec.1
  have houtput := hexec.2.2.1
  rcases DirectSelection.preparedExponentSelection selected hb he hm with
    ⟨chosen, hchosen, hvalid, hsize, hactive, hawFit, hlength, halignment⟩
  have hsame : chosen = exponentSelected := by
    rw [execution.selection] at hchosen
    exact Option.some.inj hchosen.symm
  subst chosen
  have hresultHeader := execution.resultHeader hb he hm hmodLarge
  have hresultNat : (UInt256.ofNat result).toNat = result :=
    UInt256.toNat_ofNat_of_lt (lt_trans (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega : result < 2 ^ 64) (by norm_num [UInt256.size]))
  have hbeforeRfp : result + 32 + modulusSize ≤ rFp := by
    apply le_trans (b := modulusFp)
    · dsimp only [result, modulusFp]
      unfold wideBarrettNormalizedFp
      have halloc := bytesHeaderAndSize_le_allocation modulusSize
      omega
    · apply le_trans (b := selected.reduced.finalFreePtr)
      · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
            wordArrayAllocationSize k)
        · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
          omega
        · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
            selected.reduced
      · dsimp only [rFp]
        unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
          wordArrayAllocationSize wordArrayPayloadSize
        omega
  have hreturnActive : result + 32 + modulusSize ≤
      32 * exponentSelected.activeWords.toNat := by
    have hcover : rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat := by
      simpa only [rFp, k] using hactive
    omega
  have hheader :
      (if result ≥ serialized.size ∨
          UInt256.ofNat result ≥ exponentSelected.activeWords * UInt256.ofNat 32 then
        UInt256.ofNat 0
       else UInt256.ofNat
          (fromByteArrayBigEndian (serialized.readWithPadding result 32))) =
        UInt256.ofNat modulusSize := by
    rw [if_neg]
    · rw [hresultHeader, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
    · simp only [not_or]
      constructor
      · intro h
        have hmem := hreturnActive
        have hsizeEq := Modexp.MultiLimbBarrettResultSemantic.resultMemory_size
          (mem := exponentSelected.memory) (aw := exponentSelected.activeWords)
          (fp := rFp) (result := UInt256.ofNat result) (dataLen := modulusSize) hm
          (by rw [hresultNat]; exact lt_trans (by
            dsimp only [result]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega : result + 32 + modulusSize < 2 ^ 64) (by norm_num [UInt256.size]))
          (by
            rw [hresultNat]
            have hs : rFp + 64 ≤ exponentSelected.memory.size := by
              simpa only [rFp, k] using hsize
            have hbefore : result + 32 + modulusSize ≤ rFp := by
              apply le_trans (b := modulusFp)
              · dsimp only [result, modulusFp]
                unfold wideBarrettNormalizedFp
                have halloc := bytesHeaderAndSize_le_allocation modulusSize
                omega
              · apply le_trans (b := selected.reduced.finalFreePtr)
                · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
                      wordArrayAllocationSize k)
                  · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
                    omega
                  · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
                      selected.reduced
                · dsimp only [rFp]
                  unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr
                    remainderPtr wordArrayAllocationSize wordArrayPayloadSize
                  omega
            exact hbefore.trans ((Nat.le_add_right rFp 64).trans hs))
          (by
            intro _
            rw [hresultNat]
            have hs : rFp + 64 ≤ exponentSelected.memory.size := by
              simpa only [rFp, k] using hsize
            have hbefore : result + 64 ≤ rFp := by
              apply le_trans (b := modulusFp)
              · dsimp only [result, modulusFp]
                unfold wideBarrettNormalizedFp
                have halloc := bytesHeaderAndSize_le_allocation modulusSize
                omega
              · apply le_trans (b := selected.reduced.finalFreePtr)
                · apply le_trans (b := directRemFp modulusFp modulusSize baseSize +
                      wordArrayAllocationSize k)
                  · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
                    omega
                  · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
                      selected.reduced
                · dsimp only [rFp]
                  unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr
                    remainderPtr wordArrayAllocationSize wordArrayPayloadSize
                  omega
            exact hbefore.trans ((Nat.le_add_right rFp 64).trans hs))
        have hserializedSize : serialized.size = exponentSelected.memory.size := by
          simpa only [serialized] using hsizeEq
        rw [hserializedSize] at h
        have hs : rFp + 64 ≤ exponentSelected.memory.size := by
          simpa only [rFp, k] using hsize
        omega
      · intro hge
        have hmul := umul_toNat (a := exponentSelected.activeWords)
          (b := UInt256.ofNat 32) hawFit
        have hnat : (exponentSelected.activeWords * UInt256.ofNat 32).toNat ≤
            (UInt256.ofNat result).toNat := hge
        rw [hmul, UInt256.toNat_ofNat_of_lt (by decide : 32 < UInt256.size),
          hresultNat] at hnat
        omega
  have hd := barrettReturnDecodesNormalizedComposition
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0, h1, h2⟩
  have rd173 := evm_run rd1271 with
    [known jumpdest h0, known swap1 h1, known jump h2
      jumpDest_wrapper173NormalizedComposition]
  have hret := wrapperReturnExact (ptr := result) (len := modulusSize) (tail := tail)
    hm (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    (by omega) hreturnActive hheader
    (by simpa only [serialized, result] using houtput) (by omega) (by
      simpa only [result, serialized] using rd173)
  simpa only [Nat.add_assoc] using hret

/-- The normalized serializer and PC 1808 restore both preserve the original result header. -/
theorem PreparedNormalizedExecution.resultHeader
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize retBar ret : Nat}
    {tail : List UInt256}
    {selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) retBar
      (operandFreePtr baseSize exponentSize modulusSize) ret tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (execution : PreparedNormalizedExecution selected exponentSelected)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
    let result := operandFreePtr baseSize exponentSize modulusSize
    let offset := barrettNormalizedOffset mem aw p modulusSize
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
      exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat temp) n
    (barrettRestoreMemory serialized temp result offset n).readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
  dsimp only
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
  let initialized := initializedMemory selected.direct.constant.finalMemory rFp k
  let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
    exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat temp) n
  have hnEq : n = barrettNormalizedLen mem aw p modulusSize := by rfl
  rcases selected.exponentSelection hb he hm hmodLarge hnormalize hcalldata with
    ⟨chosen, hchosen, hvalid, hsize, hactive, hawFit, hlength, halignment⟩
  have hsame : chosen = exponentSelected := by
    rw [execution.selection] at hchosen
    exact Option.some.inj hchosen.symm
  subst chosen
  have restoreGeometry := selected.preparedRestoreGeometry hb he hm hmodLarge hnormalize
    hcalldata execution.selection hsize hactive
  have geometry := preparedNormalizeReentryGeometry I hb he hm hmodLarge hnormalize hcalldata
  have hsourceHeader : mem.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    unfold mem result wideWordResultMemory
    apply storeBytesLength_read_self
    apply lt_of_le_of_lt (Nat.sub_le _ _)
    exact lt_usize _ (by
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
  have hsourceForCopy : p + offset + n ≤ fp + 32 := by
    have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    have hoff : 32 ≤ barrettNormalizedOffset mem aw p modulusSize := by
      dsimp only [mem, aw, p]
      change operandModulusPtr baseSize exponentSize + 32 <
        barrettScanStop
          (wideWordResultMemory I baseSize exponentSize modulusSize)
          (wideWordResultWords baseSize exponentSize modulusSize)
          (operandModulusPtr baseSize exponentSize) modulusSize at hnormalize
      unfold barrettNormalizedOffset
      omega
    have hend : p + offset + n = p + 32 + modulusSize := by
      rw [hnEq]
      dsimp only [offset] at hsplit ⊢
      omega
    rw [hend]
    dsimp only [p, fp]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hnormalizedHeader : sourceMem.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    have hread := geometry.readOriginal (read := result) (len := 32) hsourceForCopy
      (by decide) (by decide)
      (by
        dsimp only [result]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by
        have hmemSize := wideWordResultMemory_size I hb he hm
        dsimp only [mem, result]
        omega)
      (by
        dsimp only [result, fp]
        unfold wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega)
      (by
        dsimp only [result, temp, fp, n, wideBarrettNormalizedLenFor]
        unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega)
    have hframe : sourceMem.readWithPadding result 32 = mem.readWithPadding result 32 := by
      simpa only [sourceMem, mem, aw, fp, p, temp, result] using hread
    exact hframe.trans hsourceHeader
  have hinitialHeader : initialized.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    have hframe := selected.direct.initializedReadBelow result
      (by
        dsimp only [result]
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize
        omega)
      (by
        dsimp only [result, modulusFp, temp, n, wideBarrettNormalizedLenFor]
        unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega)
    have hframe' : initialized.readWithPadding result 32 = sourceMem.readWithPadding result 32 := by
      simpa only [initialized, rFp, k, sourceMem] using hframe
    exact hframe'.trans hnormalizedHeader
  have hexponentHeader := selected.exponentReadBelow hb he hm hmodLarge hnormalize hcalldata
    (read := result)
    (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    (by
      apply le_trans (b := modulusFp)
      · dsimp only [result, modulusFp, temp, n, wideBarrettNormalizedLenFor]
        unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        omega
      · apply le_trans (b := selected.direct.reduced.finalFreePtr)
        · apply le_trans (b := directRemFp modulusFp n baseSize + wordArrayAllocationSize k)
          · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
            omega
          · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
              selected.direct.reduced
        · dsimp only [rFp]
          unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr remainderPtr
            wordArrayAllocationSize wordArrayPayloadSize
          omega)
    execution.selection
  have htempNat : (UInt256.ofNat temp).toNat = temp :=
    UInt256.toNat_ofNat_of_lt (by
      exact lt_trans (by
        have h := restoreGeometry.tempAddr64
        omega : temp < 2 ^ 64) (by norm_num [UInt256.size]))
  have hserializedSize : serialized.size = exponentSelected.memory.size := by
    dsimp only [serialized]
    apply Modexp.MultiLimbBarrettResultSemantic.resultMemory_size
      (by
        have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
        rw [hnEq]
        omega)
    · rw [htempNat]
      exact restoreGeometry.tempAddr
    · rw [htempNat]
      exact restoreGeometry.tempMem
    · intro _
      rw [htempNat]
      have hnLarge := selected.direct.dataLenLarge
      have htemp := restoreGeometry.tempMem
      dsimp only [n, wideBarrettNormalizedLenFor] at hnLarge htemp
      omega
  have hserializedHeader : serialized.readWithPadding result 32 =
      UInt256.toByteArray (UInt256.ofNat modulusSize) := by
    have hframe := Modexp.MultiLimbBarrettResultSemantic.resultMemory_read_below
      (mem := exponentSelected.memory) (aw := exponentSelected.activeWords)
      (fp := rFp) (result := UInt256.ofNat temp) (dataLen := n) (read := result)
      (by
        have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
        rw [hnEq]
        omega)
      (by rw [htempNat]; exact restoreGeometry.tempAddr)
      (by rw [htempNat]; exact restoreGeometry.tempMem)
      (by
        intro _
        rw [htempNat]
        have hnLarge := selected.direct.dataLenLarge
        have htemp := restoreGeometry.tempMem
        dsimp only [n, wideBarrettNormalizedLenFor] at hnLarge htemp
        omega)
      (by
        rw [htempNat]
        dsimp only [result, temp, n, wideBarrettNormalizedLenFor]
        unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp
        omega)
    have hexponentFrame : exponentSelected.memory.readWithPadding result 32 =
        initialized.readWithPadding result 32 := by
      simpa only [initialized, rFp, k, result] using hexponentHeader
    exact hframe.trans (hexponentFrame.trans hinitialHeader)
  change (barrettRestoreMemory serialized temp result offset n).readWithPadding result 32 =
    UInt256.toByteArray (UInt256.ofNat modulusSize)
  apply Eq.trans (barrettRestoreMemory_read_below
    (mem := serialized) (temp := temp) (result := result) (offset := offset) (len := n)
    (by
      have hn := selected.direct.dataLenLarge
      simpa only [n, wideBarrettNormalizedLenFor] using lt_trans (by decide : 0 < 32) hn)
    (by
      rw [hserializedSize]
      simpa only [temp, n] using restoreGeometry.tempMem)
    (by
      rw [hserializedSize]
      have hd : result + offset + n ≤ exponentSelected.memory.size := by
        simpa only [result, offset, n] using restoreGeometry.destinationEnd
      omega)
    (by
      have ho : 32 ≤ offset := by simpa only [offset] using restoreGeometry.offset
      omega)
    (by
      rw [hserializedSize]
      have hd : result + offset + n ≤ exponentSelected.memory.size := by
        simpa only [result, offset, n] using restoreGeometry.destinationEnd
      have ho : 32 ≤ offset := by simpa only [offset] using restoreGeometry.offset
      omega))
  exact hserializedHeader

/-- Execute the PC 1271 trampoline and wrapper return after normalized recursive restore. -/
theorem PreparedNormalizedExecution.returnExact
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize : Nat}
    {tail : List UInt256}
    {selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) 1271
      (operandFreePtr baseSize exponentSize modulusSize) 173 tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (execution : PreparedNormalizedExecution selected exponentSelected)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 968) :
    let mem := wideWordResultMemory I baseSize exponentSize modulusSize
    let aw := wideWordResultWords baseSize exponentSize modulusSize
    let p := operandModulusPtr baseSize exponentSize
    let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
    let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
    let result := operandFreePtr baseSize exponentSize modulusSize
    let offset := barrettNormalizedOffset mem aw p modulusSize
    let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
    let k := Modexp.MultiLimbBarrettConversion.words n
    let modulusFp := temp + bytesAllocationSize n
    let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
    let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
    RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
      (Model.natToBytes
        (Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
        modulusSize)
      ((gasUsed + barrettNormalizeReentryChecksGas mem aw fp p modulusSize temp) +
        Modexp.MultiLimbBarrettConversion.scanConversionGas sourceMem
          (barrettNormalizedResultAw mem aw fp p modulusSize temp) modulusFp fp n + 18 +
        MultiLimbReduceBase.nonzeroGas
          (Modexp.MultiLimbBarrettConversion.convertedMemory sourceMem
            (barrettNormalizedResultAw mem aw fp p modulusSize temp) modulusFp fp n)
          (Modexp.MultiLimbBarrettConversion.convertedWords sourceMem
            (barrettNormalizedResultAw mem aw fp p modulusSize temp) modulusFp fp n)
          (directBaseFp modulusFp n) (directRemFp modulusFp n baseSize) baseSize k
          (UInt256.ofNat operandBasePtr) + selected.direct.reduced.gasDelta +
        Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
          selected.direct.reduced.finalMemory selected.direct.reduced.finalWords
          selected.direct.reduced.finalFreePtr k modulusFp + selected.direct.constant.gasDelta +
        Modexp.MultiLimbBarrettResult.freshExecutionGas selected.direct.constant.finalWords
          rFp k (UInt256.ofNat (operandExponentPtr baseSize)) exponentSelected n +
        barrettRestoreGas exponentSelected.activeWords temp result offset n + 28) := by
  dsimp only
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
  let serialized := Modexp.MultiLimbBarrettResult.resultMemory exponentSelected.memory
    exponentSelected.activeWords (UInt256.ofNat rFp) (UInt256.ofNat temp) n
  let restored := barrettRestoreMemory serialized temp result offset n
  let finalAw := barrettRestoreWords exponentSelected.activeWords temp result offset n
  have hnEq : n = barrettNormalizedLen mem aw p modulusSize := by rfl
  have hexec := execution.execution
  have rd1271 := hexec.1
  have houtputInternal := hexec.2.2.2
  rcases selected.exponentSelection hb he hm hmodLarge hnormalize hcalldata with
    ⟨chosen, hchosen, hvalid, hsize, hactive, hawFit, hlength, halignment⟩
  have hsame : chosen = exponentSelected := by
    rw [execution.selection] at hchosen
    exact Option.some.inj hchosen.symm
  subst chosen
  have restoreGeometry := selected.preparedRestoreGeometry hb he hm hmodLarge hnormalize
    hcalldata execution.selection hsize hactive
  have hheaderRead := execution.resultHeader hb he hm hmodLarge hnormalize hcalldata
  have wideValues := preparedWideResultValues_eq_calldata I hb he hm hbasePos (by omega)
  have hbridge := execution.valueBridge
  dsimp only at hbridge
  rw [hbridge.1, hbridge.2, wideValues.1, wideValues.2] at houtputInternal
  have houtput : restored.readWithPadding (result + 32) modulusSize =
      Model.natToBytes
        (Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
        modulusSize := by
    simpa only [restored, serialized, sourceMem, fp, n, mem, aw, p, temp, result,
      wideBarrettNormalizedLenFor] using houtputInternal
  have hresultEnd : result + offset + n ≤ 32 * exponentSelected.activeWords.toNat := by
    apply le_trans (b := rFp)
    · apply le_trans (b := fp)
      · have hsplit := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
        have hoff : 32 ≤ offset := by simpa only [offset] using restoreGeometry.offset
        have hfpEq : fp = result + bytesAllocationSize modulusSize := by
          dsimp only [fp, result]
          rfl
        rw [hfpEq]
        have halloc := bytesHeaderAndSize_le_allocation modulusSize
        rw [hnEq]
        omega
      · apply le_trans (b := modulusFp)
        · dsimp only [modulusFp, temp, fp, n, wideBarrettNormalizedLenFor]
          unfold wideBarrettNormalizedResultFp
          omega
        · apply le_trans (b := selected.direct.reduced.finalFreePtr)
          · apply le_trans (b := directRemFp modulusFp n baseSize + wordArrayAllocationSize k)
            · unfold directRemFp directBaseFp wordArrayAllocationSize wordArrayPayloadSize
              omega
            · exact Modexp.MultiLimbBarrettReduceBaseComplete.Selection.entryFp_le_finalFreePtr
                selected.direct.reduced
          · dsimp only [rFp]
            unfold accumulatorFp normalizedDivisorPtr normalizedDividendPtr quotientPtr
              remainderPtr wordArrayAllocationSize wordArrayPayloadSize
            omega
    · have hc : rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat := by
        simpa only [rFp, k, n, wideBarrettNormalizedLenFor] using hactive
      omega
  have htempEnd : temp + 32 + n ≤ 32 * exponentSelected.activeWords.toNat := by
    have hout : temp + 32 + n ≤ rFp := by
      simpa only [temp, n, rFp, k] using restoreGeometry.outputBeforeHeader
    have hc : rFp + 32 + 32 * k ≤ 32 * exponentSelected.activeWords.toNat := by
      simpa only [rFp, k, n, wideBarrettNormalizedLenFor] using hactive
    omega
  have hM : MachineState.M exponentSelected.activeWords.toNat
      (max (result + offset) (temp + 32)) n = exponentSelected.activeWords.toNat := by
    apply machineM_eq_of_access
    by_cases hle : result + offset ≤ temp + 32
    · rw [Nat.max_eq_right hle]
      exact htempEnd
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      exact hresultEnd
  have hfinalAw : finalAw = exponentSelected.activeWords := by
    dsimp only [finalAw, barrettRestoreWords]
    rw [hM]
    exact u256_ofNat_toNat _
  have hreturnActive : result + 32 + modulusSize ≤ 32 * finalAw.toNat := by
    rw [hfinalAw]
    have hwidth : offset - 32 + n = modulusSize := by
      simpa only [offset, n] using restoreGeometry.width
    have hoff : 32 ≤ offset := by simpa only [offset] using restoreGeometry.offset
    omega
  have htempNat : (UInt256.ofNat temp).toNat = temp :=
    UInt256.toNat_ofNat_of_lt (lt_trans (by
      have ht := restoreGeometry.tempAddr64
      simpa only [temp, n] using (show temp < 2 ^ 64 by omega))
      (by norm_num [UInt256.size]))
  have hnBound : n ≤ 1024 := by
    rw [hnEq]
    have hs := barrettNormalizedSkippedPrefix_add_len mem aw p modulusSize (by omega)
    omega
  have hpartialMem : temp + 64 ≤ exponentSelected.memory.size := by
    have hnLarge := selected.direct.dataLenLarge
    have ht := restoreGeometry.tempMem
    dsimp only [n, wideBarrettNormalizedLenFor] at hnLarge ht
    omega
  have hserializedSize : serialized.size = exponentSelected.memory.size := by
    dsimp only [serialized]
    exact Modexp.MultiLimbBarrettResultSemantic.resultMemory_size
      (result := UInt256.ofNat temp) (dataLen := n) hnBound
      (by rw [htempNat]; simpa only [temp, n] using restoreGeometry.tempAddr)
      (by rw [htempNat]; simpa only [temp, n] using restoreGeometry.tempMem)
      (by intro _; rw [htempNat]; exact hpartialMem)
  have hrestoredSize : restored.size = serialized.size := by
    dsimp only [restored]
    apply barrettRestoreMemory_size_inBounds
    · have hn := selected.direct.dataLenLarge
      simpa only [n, wideBarrettNormalizedLenFor] using lt_trans (by decide : 0 < 32) hn
    ·
      rw [hserializedSize]
      simpa only [temp, n] using restoreGeometry.tempMem
    · rw [hserializedSize]
      have hd : result + offset + n ≤ exponentSelected.memory.size := by
        simpa only [result, offset, n] using restoreGeometry.destinationEnd
      omega
  have hheader :
      (if result ≥ restored.size ∨ UInt256.ofNat result ≥ finalAw * UInt256.ofNat 32 then
        UInt256.ofNat 0
       else UInt256.ofNat (fromByteArrayBigEndian (restored.readWithPadding result 32))) =
        UInt256.ofNat modulusSize := by
    rw [if_neg]
    · rw [hheaderRead, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]
    · simp only [not_or]
      constructor
      · intro h
        rw [hrestoredSize] at h
        have hsrcSize : temp + 32 + n ≤ serialized.size := by
          rw [hserializedSize]
          simpa only [temp, n] using restoreGeometry.tempMem
        have hresultTemp : result < temp + 32 + n := by
          dsimp only [result, temp, n, wideBarrettNormalizedLenFor]
          unfold wideBarrettNormalizedResultFp wideBarrettNormalizedFp
          have halloc := bytesHeaderAndSize_le_allocation modulusSize
          omega
        omega
      · intro hge
        rw [hfinalAw] at hge
        rw [hfinalAw] at hreturnActive
        have hmul := umul_toNat (a := exponentSelected.activeWords)
          (b := UInt256.ofNat 32) hawFit
        have hresultNat : (UInt256.ofNat result).toNat = result :=
          UInt256.toNat_ofNat_of_lt (lt_trans (by
            dsimp only [result]
            unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
              bytesAllocationSize
            omega : result < 2 ^ 64) (by norm_num [UInt256.size]))
        have hnat : (exponentSelected.activeWords * UInt256.ofNat 32).toNat ≤
            (UInt256.ofNat result).toNat := hge
        rw [hmul, UInt256.toNat_ofNat_of_lt (by decide : 32 < UInt256.size),
          hresultNat] at hnat
        omega
  have hd := barrettReturnDecodesNormalizedComposition
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0, h1, h2⟩
  have rd173 := evm_run rd1271 with
    [known jumpdest h0, known swap1 h1, known jump h2
      jumpDest_wrapper173NormalizedComposition]
  have hret := wrapperReturnExact (ptr := result) (len := modulusSize) (tail := tail)
    hm (by
      dsimp only [result]
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize
      omega)
    (by omega) hreturnActive hheader houtput (by omega) (by
      simpa only [restored, finalAw, result, serialized] using rd173)
  simpa only [Nat.add_assoc] using hret

/-- Exact gas selected by a complete prepared direct execution, including PC 1271 and wrapper
return. -/
def PreparedDirectExecution.totalGas
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize : Nat}
    {tail : List UInt256}
    {selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat 1271) (UInt256.ofNat 173) tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (_execution : PreparedDirectExecution selected exponentSelected) : Nat :=
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let modulusFp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words modulusSize
  let rFp := accumulatorFp selected.reduced.finalFreePtr k
  gasUsed + Modexp.MultiLimbBarrettConversion.scanConversionGas mem aw modulusFp p
      modulusSize + 18 + MultiLimbReduceBase.nonzeroGas
      (Modexp.MultiLimbBarrettConversion.convertedMemory mem aw modulusFp p modulusSize)
      (Modexp.MultiLimbBarrettConversion.convertedWords mem aw modulusFp p modulusSize)
      (directBaseFp modulusFp modulusSize)
      (directRemFp modulusFp modulusSize baseSize) baseSize k
      (UInt256.ofNat operandBasePtr) + selected.reduced.gasDelta +
    Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
      selected.reduced.finalMemory selected.reduced.finalWords
      selected.reduced.finalFreePtr k modulusFp + selected.constant.gasDelta +
    Modexp.MultiLimbBarrettResult.freshExecutionGas selected.constant.finalWords
      rFp k (UInt256.ofNat (operandExponentPtr baseSize)) exponentSelected modulusSize + 28

/-- Exact gas selected by a complete normalized execution, including restore, PC 1271, and
wrapper return. -/
def PreparedNormalizedExecution.totalGas
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize : Nat}
    {tail : List UInt256}
    {selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) 1271
      (operandFreePtr baseSize exponentSize modulusSize) 173 tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (_execution : PreparedNormalizedExecution selected exponentSelected) : Nat :=
  let mem := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let temp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let result := operandFreePtr baseSize exponentSize modulusSize
  let offset := barrettNormalizedOffset mem aw p modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let k := Modexp.MultiLimbBarrettConversion.words n
  let modulusFp := temp + bytesAllocationSize n
  let rFp := accumulatorFp selected.direct.reduced.finalFreePtr k
  let sourceMem := barrettNormalizedResultMem mem aw fp p modulusSize temp
  (gasUsed + barrettNormalizeReentryChecksGas mem aw fp p modulusSize temp) +
    Modexp.MultiLimbBarrettConversion.scanConversionGas sourceMem
      (barrettNormalizedResultAw mem aw fp p modulusSize temp) modulusFp fp n + 18 +
    MultiLimbReduceBase.nonzeroGas
      (Modexp.MultiLimbBarrettConversion.convertedMemory sourceMem
        (barrettNormalizedResultAw mem aw fp p modulusSize temp) modulusFp fp n)
      (Modexp.MultiLimbBarrettConversion.convertedWords sourceMem
        (barrettNormalizedResultAw mem aw fp p modulusSize temp) modulusFp fp n)
      (directBaseFp modulusFp n) (directRemFp modulusFp n baseSize) baseSize k
      (UInt256.ofNat operandBasePtr) + selected.direct.reduced.gasDelta +
    Modexp.MultiLimbBarrettConstantComplete.Selection.callPrefixGas
      selected.direct.reduced.finalMemory selected.direct.reduced.finalWords
      selected.direct.reduced.finalFreePtr k modulusFp + selected.direct.constant.gasDelta +
    Modexp.MultiLimbBarrettResult.freshExecutionGas selected.direct.constant.finalWords
      rFp k (UInt256.ofNat (operandExponentPtr baseSize)) exponentSelected n +
    barrettRestoreGas exponentSelected.activeWords temp result offset n + 28

theorem PreparedDirectExecution.returnExactSelected
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed baseSize exponentSize modulusSize : Nat}
    {tail : List UInt256}
    {selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) steps gasUsed
      (operandModulusPtr baseSize exponentSize)
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
      operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
      (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
      (UInt256.ofNat 1271) (UInt256.ofNat 173) tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (execution : PreparedDirectExecution selected exponentSelected)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hdepth : tail.length ≤ 972) :
    RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
      (Model.natToBytes
        (Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
        modulusSize) execution.totalGas := by
  simpa [PreparedDirectExecution.totalGas] using
    execution.returnExact hb he hm hbasePos hmodLarge hdepth

theorem PreparedNormalizedExecution.returnExactSelected
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {gasUsed baseSize exponentSize modulusSize : Nat}
    {tail : List UInt256}
    {selected : NormalizedSelection I g (initState cA gh bl sigma sigma0 g A I)
      ByteArray.empty acc
      (wideWordResultMemory I baseSize exponentSize modulusSize)
      (wideWordResultWords baseSize exponentSize modulusSize) gasUsed
      (operandModulusPtr baseSize exponentSize) modulusSize
      (wideBarrettNormalizedFp baseSize exponentSize modulusSize)
      (wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize)
      operandBasePtr baseSize (operandExponentPtr baseSize) 1271
      (operandFreePtr baseSize exponentSize modulusSize) 173 tail}
    {exponentSelected :
      Modexp.MultiLimbBarrettExponentSetup.FreshBarrettLoopSetupSelection}
    (execution : PreparedNormalizedExecution selected exponentSelected)
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hnormalize : operandModulusPtr baseSize exponentSize + 32 <
      barrettScanStop
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length ≤ 968) :
    RDxRet runtimeBytecode g (initState cA gh bl sigma sigma0 g A I) acc
      (Model.natToBytes
        (Model.bytesToNatPadded I.calldata 96 baseSize ^
          Model.bytesToNatPadded I.calldata (96 + baseSize) exponentSize %
            Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize)
        modulusSize) execution.totalGas := by
  simpa [PreparedNormalizedExecution.totalGas] using
    execution.returnExact hb he hm hbasePos hmodLarge hnormalize hcalldata hdepth

/-- Compose the common prepared even-Barrett prefix with the direct arbitrary-width backend. -/
theorem runPreparedBarrettDirectMultiLimbSelected
    {cA gh bl sigma sigma0 A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {C steps baseSize exponentSize modulusSize ret : Nat}
    {tail : List UInt256}
    (hb : baseSize ≤ 1024) (he : exponentSize ≤ 1024) (hm : modulusSize ≤ 1024)
    (hbasePos : 0 < baseSize) (hmodLarge : 32 < modulusSize)
    (hmodulusGtOne : 1 < Model.bytesToNatPadded I.calldata
      (96 + baseSize + exponentSize) modulusSize)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (heven : modulusLastByteParity
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize = UInt256.ofNat 0)
    (hfirst : UInt256.byteAt (UInt256.ofNat 0)
      (wideLoadWord
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize)
        (UInt256.ofNat (operandModulusPtr baseSize exponentSize + 32))) ≠
          UInt256.ofNat 0)
    (htail : tail.length ≤ 972)
    (rd0 : RDx runtimeBytecode I g (initState cA gh bl sigma sigma0 g A I) ⟨1183⟩
      (UInt256.ofNat operandBasePtr :: UInt256.ofNat (operandExponentPtr baseSize) ::
        UInt256.ofNat (operandModulusPtr baseSize exponentSize) :: UInt256.ofNat ret :: tail)
      (operandCopiedMemory I baseSize exponentSize modulusSize)
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      ByteArray.empty acc steps C) :
    ∃ selectedSteps,
      ∃ selected : DirectSelection I g (initState cA gh bl sigma sigma0 g A I)
        ByteArray.empty acc
        (wideWordResultMemory I baseSize exponentSize modulusSize)
        (wideWordResultWords baseSize exponentSize modulusSize) selectedSteps
        (C + preparedBarrettPrefixGasFromAw I
          (operandModulusActiveWords baseSize exponentSize modulusSize)
          baseSize exponentSize modulusSize)
        (operandModulusPtr baseSize exponentSize)
        (wideBarrettNormalizedFp baseSize exponentSize modulusSize) modulusSize
        operandBasePtr baseSize (UInt256.ofNat (operandExponentPtr baseSize))
        (UInt256.ofNat (operandFreePtr baseSize exponentSize modulusSize))
        (UInt256.ofNat 1271) (UInt256.ofNat ret) tail,
      ∃ exponentSelected, PreparedDirectExecution selected exponentSelected := by
  obtain ⟨prefixSteps, rd1592⟩ := runPreparedBarrettPrefixExactAny
    (baseSize := baseSize) (exponentSize := exponentSize) (modulusSize := modulusSize)
    (ret := ret) (tail := tail) hb he (by omega) hm hmodulusGtOne hcalldata heven
    (by omega) rd0
  obtain ⟨selected⟩ := preparedDirectSelection_exists
    (gasUsed := C + preparedBarrettPrefixGasFromAw I
      (operandModulusActiveWords baseSize exponentSize modulusSize)
      baseSize exponentSize modulusSize)
    (steps := prefixSteps) (retBar := 1271) (ret := ret) (tail := tail)
    hb he hm hbasePos hmodLarge hfirst hcalldata (by omega)
    (by simpa [show (⟨1271⟩ : UInt256) = UInt256.ofNat 1271 by native_decide] using rd1592)
  obtain ⟨exponentSelected, execution⟩ := DirectSelection.preparedExecution selected
    hb he hm hbasePos (by omega) jumpDest_1271 (by omega)
  exact ⟨prefixSteps, selected, exponentSelected, execution⟩

end Modexp.MultiLimbBarrettNormalizedComposition
