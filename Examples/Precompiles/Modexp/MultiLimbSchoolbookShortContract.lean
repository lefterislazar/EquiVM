import Examples.Precompiles.Modexp.MultiLimbSchoolbookDivisorTrimContract

/-!
# Short-dividend remainder copying

When the effective dividend is shorter than the effective divisor, `schoolbookDiv` returns a
zero one-limb quotient and copies the effective dividend limbs into the preallocated remainder.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookShort

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arrayHeader (mem : ByteArray) (aw array : UInt256) : UInt256 :=
  MultiLimbOddCompare.headerWord mem aw array

def arrayAfterHeader (aw array : UInt256) : UInt256 :=
  MultiLimbOddCompare.afterHeader aw array

def arrayAddress (array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.elementPtr array (UInt256.ofNat index)

def arrayWord (mem : ByteArray) (aw array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.loadedWord mem aw (arrayAddress array index)

def arrayAfterWord (aw array : UInt256) (index : Nat) : UInt256 :=
  MultiLimbOddCompare.afterLoad aw (arrayAddress array index)

def copyMemory (mem : ByteArray) (rem : UInt256) (index : Nat) (value : UInt256) : ByteArray :=
  value.toByteArray.write 0 mem (arrayAddress rem index).toNat 32

def shortAllocatedMemory (mem : ByteArray) (fp : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize 1)) fp 1

def shortAllocatedWords (aw : UInt256) (fp : Nat) : UInt256 :=
  newWordArrayWords aw fp 1

def shortAllocationGas (aw : UInt256) (fp : Nat) : Nat :=
  178 + newBytesStoreExpansionGas aw fp + newWordArrayCopyExpansionGas aw fp 1

/-- Allocate the one-limb zero quotient and arrive at the shorter-case copy-loop setup. -/
theorem allocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m : Nat} {tail : List UInt256}
    {kEff rem dividend ret divisor : UInt256}
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1009)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6214⟩
      (kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6226⟩
      (UInt256.ofNat fp :: UInt256.ofNat m :: dividend :: ret :: rem :: tail)
      (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp)
      rdata acc (k + 53) (C + shortAllocationGas aw fp) := by
  have hsize : bytesAllocationSize 32 = wordArrayAllocationSize 1 := by
    native_decide
  have rd485raw := (evm_run h with [
    jumpdest,
    pop,
    swap1,
    swap4,
    pop,
    pushCanonical 2 .PUSH2 ⟨0x1852⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨0x5b2⟩ (by decide),
    jump (by native_decide),
    jumpdest,
    pushCanonical 1 .PUSH1 ⟨0x40⟩ (by decide),
    swap1,
    pushCanonical 2 .PUSH2 ⟨0x5be⟩ (by decide),
    dup3,
    pushCanonical 2 .PUSH2 ⟨0x1e5⟩ (by decide),
    jump (by native_decide)
  ])
  have rd485 : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨485⟩
      (UInt256.ofNat (bytesAllocationSize 32) :: ⟨1470⟩ :: ⟨6226⟩ :: ⟨64⟩ ::
        UInt256.ofNat m :: dividend :: ret :: rem :: tail)
      mem aw rdata acc (k + 15) (C + 49) := by
    have normalized := rd485raw.withIndices
      (k' := k + 15) (C' := C + 49) (by omega) (by omega)
    simpa [bytesAllocationSize] using normalized
  have hbound32 : fp + bytesAllocationSize 32 < 2 ^ 64 := by
    rw [hsize]
    exact hbound
  have rd1470 := allocateMemoryExact
    (n := 32) (fp := fp) (ret := 1470)
    (by omega) hfp hbound32 hmemSize haw3 haw64 hread
    (by simp only [List.length_cons]; omega) (by native_decide) rd485
  have rd1486 := GeneratedTraces.trace_1470_body
    (by simp only [List.length_cons]; omega) rd1470
  have rd6233 := rd1486.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hfpWord : fp < UInt256.size := by
    exact lt_trans (by omega : fp < 2 ^ 64) (by decide)
  have hfp32Word : fp + 32 < UInt256.size := by
    have halloc : wordArrayAllocationSize 1 = 64 := by native_decide
    rw [halloc] at hbound
    exact lt_trans (by omega : fp + 32 < 2 ^ 64) (by decide)
  have hpayloadWord : wordArrayPayloadSize 1 < UInt256.size := by
    native_decide
  have hdest : (UInt256.ofNat fp + ⟨32⟩).toNat = fp + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
    rw [Nat.mod_eq_of_lt hfp32Word]
  have hlen : ((⟨31⟩ : UInt256).lnot + ⟨64⟩).toNat =
      wordArrayPayloadSize 1 := by native_decide
  have hcopy :
      I.calldata.write (UInt256.ofNat I.calldata.size).toNat
          (UInt256.toByteArray ⟨1⟩ |>.write 0
            (setFreePtr mem (fp + wordArrayAllocationSize 1)) fp 32)
          (UInt256.ofNat fp + ⟨32⟩).toNat
          ((⟨31⟩ : UInt256).lnot + ⟨64⟩).toNat =
        shortAllocatedMemory mem fp := by
    rw [UInt256.toNat_ofNat_of_lt
      (lt_trans hcalldata (by decide) : I.calldata.size < UInt256.size)]
    rw [hdest, hlen]
    simpa only [shortAllocatedMemory] using
      (write_from_source_end_past_dest I.calldata
        (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize 1)) fp 1)
        I.calldata.size (fp + 32) (wordArrayPayloadSize 1) (le_refl _) (by
          simp [storeBytesLength]
          have hsetSize : (setFreePtr mem (fp + wordArrayAllocationSize 1)).size = mem.size := by
            unfold setFreePtr
            apply toByteArray_write32_size_of_le mem _ 64 mem.size mem.size rfl (by omega)
            omega
          exact (toByteArray_write32_size_of_ge _ _ fp mem.size (fp + 32)
            hsetSize hmemLe hgap rfl).le))
  rw [hsize, UInt256.toNat_ofNat_of_lt hfpWord, hcopy, hdest, hlen] at rd6233
  have hawEq :
      UInt256.ofNat
        (MachineState.M (UInt256.ofNat (MachineState.M aw.toNat fp 32)).toNat
          (fp + 32) (wordArrayPayloadSize 1)) = shortAllocatedWords aw fp := by
    rfl
  rw [hawEq] at rd6233
  have normalized := rd6233.withIndices
    (k' := k + 53) (C' := C + shortAllocationGas aw fp)
    (by omega) (by
      simp [shortAllocationGas, newWordArrayCopyExpansionGas,
        newBytesStoreExpansionGas, shortAllocatedWords, newWordArrayWords,
        newBytesStoreWords, GasConstants.Gverylow, GasConstants.Gcopy,
        wordArrayPayloadSize]
      omega)
  simpa only [shortAllocatedMemory, shortAllocatedWords] using normalized

/-- Rearrange the shorter-case locals and initialize the copy-loop index to zero. -/
theorem setupCopyLoop
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m : Nat} {tail : List UInt256}
    {quotient dividend ret rem : UInt256}
    (hdepth : tail.length + 5 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨6226⟩
      (quotient :: UInt256.ofNat m :: dividend :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6229⟩
      (⟨0⟩ :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      mem aw rdata acc (k + 3) (C + 6) := by
  have rd6236 := (evm_run h with [
    jumpdest,
    swap2,
    push0
  ])
  have normalized := rd6236.withIndices
    (k' := k + 3) (C' := C + 6) (by omega) (by omega)
  simpa using normalized

/-- One exact iteration of `rem[i] = dividend[i]`. -/
theorem copyCycle
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C i m dividendCount remCount : Nat} {tail : List UInt256}
    {quotient ret dividend rem value : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hi : i < m)
    (hmDividend : m ≤ dividendCount)
    (hmRem : m ≤ remCount)
    (hcountBound : dividendCount ≤ 32)
    (hremCountBound : remCount ≤ 32)
    (hdivHeader : arrayHeader mem aw dividend = UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hdivElementAw : arrayAfterWord aw dividend i = aw)
    (hvalue : arrayWord mem aw dividend i = value)
    (hremHeader : arrayHeader mem aw rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremElementAw : arrayAfterWord aw rem i = aw)
    (h : RDx runtimeBytecode ee g s0 ⟨6229⟩
      (UInt256.ofNat i :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6229⟩
      (UInt256.ofNat (i + 1) :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      (copyMemory mem rem i value) aw rdata acc (k + 58) (C + 208) := by
  have hsmall : dividendCount < UInt256.size := by
    have : 32 < UInt256.size := by decide
    omega
  have hremSmall : remCount < UInt256.size := by
    have : 32 < UInt256.size := by decide
    omega
  have hiSmall : i < UInt256.size := by omega
  have hmSmall : m < UInt256.size := by
    have : 32 < UInt256.size := by decide
    omega
  have hloop : (UInt256.ofNat i).lt (UInt256.ofNat m) ≠ ⟨0⟩ := by
    rw [ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall, UInt256.toNat_ofNat_of_lt hmSmall]
      exact hi
  have rd6250 := GeneratedTraces.trace_6229_taken
    (tail := quotient :: ret :: rem :: tail)
    (by simp only [List.length_cons]; omega) h
    (by native_decide) hloop (by native_decide)
  have hdivBound :
      (UInt256.ofNat i).lt (MultiLimbOddCompare.headerWord mem aw dividend) ≠ ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw dividend = UInt256.ofNat dividendCount
      from hdivHeader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall, UInt256.toNat_ofNat_of_lt hsmall]
      omega
  have hdivCondition :
      ((UInt256.ofNat i).lt (MultiLimbOddCompare.headerWord mem aw dividend)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hdivBound, Bool.toUInt256]
    native_decide
  have rd1539 := GeneratedTraces.trace_6243_notTaken
    (by simp only [List.length_cons]; omega) rd6250 (by native_decide) hdivCondition
  have hdivHeaderAw' : MultiLimbOddCompare.afterHeader aw dividend = aw := hdivHeaderAw
  rw [← MultiLimbOddCompare.afterHeader_generated, hdivHeaderAw'] at rd1539
  have rd6263 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539 (by native_decide) (by native_decide)
  have hremBound :
      (UInt256.ofNat i).lt (MultiLimbOddCompare.headerWord mem aw rem) ≠ ⟨0⟩ := by
    rw [show MultiLimbOddCompare.headerWord mem aw rem = UInt256.ofNat remCount
      from hremHeader, ult_one]
    · native_decide
    · rw [UInt256.toNat_ofNat_of_lt hiSmall, UInt256.toNat_ofNat_of_lt hremSmall]
      omega
  have hremCondition :
      ((UInt256.ofNat i).lt (MultiLimbOddCompare.headerWord mem aw rem)).isZero = ⟨0⟩ := by
    simp [UInt256.isZero, UInt256.eq0, hremBound, Bool.toUInt256]
    native_decide
  have hdivValueRaw :
      MultiLimbOddCompare.headerWord mem aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = value := by
    simpa only [arrayWord, MultiLimbOddCompare.loadedWord, arrayAddress,
      MultiLimbOddCompare.elementPtr] using hvalue
  have hdivElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbOddCompare.afterLoad, arrayAddress,
      MultiLimbOddCompare.elementPtr] using hdivElementAw
  have rd1539b := GeneratedTraces.trace_6256_notTaken
    (by omega) rd6263 (by native_decide)
    (by
      rw [← MultiLimbOddCompare.afterHeader_generated, hdivElementAwRaw,
        ← MultiLimbOddCompare.headerWord_generated]
      exact hremCondition)
  rw [← MultiLimbOddCompare.headerWord_generated,
    ← MultiLimbOddCompare.afterHeader_generated] at rd1539b
  have hremHeaderAw' : MultiLimbOddCompare.afterHeader aw rem = aw := hremHeaderAw
  have hdivElementAwMachine :
      UInt256.ofNat (MachineState.M aw.toNat
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + dividend + ⟨32⟩).toNat 32) = aw := by
    rw [← MultiLimbOddCompare.afterHeader_generated]
    exact hdivElementAwRaw
  rw [hdivValueRaw, hdivElementAwMachine, hremHeaderAw'] at rd1539b
  have rd6274 := GeneratedTraces.trace_1539_jump
    (by simp only [List.length_cons]; omega) rd1539b (by native_decide) (by native_decide)
  have hremElementAwRaw :
      MultiLimbOddCompare.afterHeader aw
        ((UInt256.ofNat i).shiftLeft ⟨5⟩ + rem + ⟨32⟩) = aw := by
    simpa only [arrayAfterWord, MultiLimbOddCompare.afterLoad, arrayAddress,
      MultiLimbOddCompare.elementPtr] using hremElementAw
  have rd6236 := (evm_run rd6274 with [
    jumpdest,
    mstoreCanonical,
    add,
    pushCanonical 2 .PUSH2 ⟨0x1855⟩ (by decide),
    jump (by native_decide)
  ])
  rw [← MultiLimbOddCompare.afterHeader_generated, hremElementAwRaw] at rd6236
  have hnext : UInt256.ofNat i + ⟨1⟩ = UInt256.ofNat (i + 1) := by
    rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 by native_decide]
    rw [ofNat_add_bounded]
    omega
  rw [hnext] at rd6236
  have normalized := rd6236.withIndices
    (k' := k + 58) (C' := C + 208) (by omega) (by omega)
  simpa only [copyMemory, arrayAddress, MultiLimbOddCompare.elementPtr] using normalized

def copyLoopMemory (mem : ByteArray) (aw dividend rem : UInt256) : Nat → ByteArray
  | 0 => mem
  | n + 1 =>
      let current := copyLoopMemory mem aw dividend rem n
      copyMemory current rem n (arrayWord current aw dividend n)

/-- In-bounds copy-loop stores preserve the concrete memory size. -/
theorem copyLoopMemory_size_eq
    (mem : ByteArray) (aw dividend rem : UInt256) (n : Nat)
    (hwrite : ∀ i, i < n → (arrayAddress rem i).toNat + 32 ≤ mem.size) :
    (copyLoopMemory mem aw dividend rem n).size = mem.size := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprevious : (copyLoopMemory mem aw dividend rem n).size = mem.size :=
        ih (fun i hi => hwrite i (by omega))
      unfold copyLoopMemory copyMemory
      apply toByteArray_write32_size_of_le
        (copyLoopMemory mem aw dividend rem n)
        (arrayWord (copyLoopMemory mem aw dividend rem n) aw dividend n)
        (arrayAddress rem n).toNat mem.size mem.size hprevious
      · rw [hprevious]
        have hw := hwrite n (by omega)
        omega
      · apply max_eq_left
        exact hwrite n (by omega)

/-- A complete word below every destination store is unchanged by the copy loop. -/
theorem copyLoopMemory_read_below
    (mem : ByteArray) (aw dividend rem : UInt256) (n read : Nat)
    (hwrite : ∀ i, i < n → (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hbelow : ∀ i, i < n → read + 32 ≤ (arrayAddress rem i).toNat) :
    (copyLoopMemory mem aw dividend rem n).readWithPadding read 32 =
      mem.readWithPadding read 32 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprevious : (copyLoopMemory mem aw dividend rem n).size = mem.size :=
        copyLoopMemory_size_eq mem aw dividend rem n
          (fun i hi => hwrite i (by omega))
      unfold copyLoopMemory copyMemory
      rw [write32_read_below _ _ _ _ (by rw [toByteArray_size])
        (by rw [hprevious]; have hw := hwrite n (by omega); omega)
        (hbelow n (by omega))]
      exact ih (fun i hi => hwrite i (by omega)) (fun i hi => hbelow i (by omega))

/-- Header loads below the remainder payload retain their initial value throughout copying. -/
theorem arrayHeader_copyLoopMemory_eq
    (mem : ByteArray) (aw dividend rem ptr : UInt256) (n : Nat)
    (hwrite : ∀ i, i < n → (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hbelow : ∀ i, i < n → ptr.toNat + 32 ≤ (arrayAddress rem i).toNat) :
    arrayHeader (copyLoopMemory mem aw dividend rem n) aw ptr = arrayHeader mem aw ptr := by
  unfold arrayHeader MultiLimbOddCompare.headerWord MultiLimbDivisionTrace.readWord
  rw [copyLoopMemory_size_eq mem aw dividend rem n hwrite,
    copyLoopMemory_read_below mem aw dividend rem n ptr.toNat hwrite hbelow]

/-- Source element loads below the remainder payload retain their initial value. -/
theorem arrayWord_copyLoopMemory_eq
    (mem : ByteArray) (aw dividend rem : UInt256) (n index : Nat)
    (hwrite : ∀ i, i < n → (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hbelow : ∀ i, i < n →
      (arrayAddress dividend index).toNat + 32 ≤ (arrayAddress rem i).toNat) :
    arrayWord (copyLoopMemory mem aw dividend rem n) aw dividend index =
      arrayWord mem aw dividend index := by
  unfold arrayWord MultiLimbOddCompare.loadedWord
  exact arrayHeader_copyLoopMemory_eq mem aw dividend rem (arrayAddress dividend index) n
    hwrite hbelow

/-- Every completed destination limb contains the corresponding initial source limb. -/
theorem copyLoopMemory_copied_word
    (mem : ByteArray) (aw dividend rem : UInt256) (n index : Nat)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hindex : index < n)
    (hwrite : ∀ i, i < n → (arrayAddress rem i).toNat + 32 ≤ mem.size)
    (hsourceBelow : ∀ i, i < n → ∀ j, j < n →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationBelow : ∀ i, i < n → ∀ j, j < n → i < j →
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdestinationActive : ∀ i, i < n →
      (arrayAddress rem i).toNat + 32 ≤ 32 * aw.toNat) :
    arrayWord (copyLoopMemory mem aw dividend rem n) aw rem index =
      arrayWord mem aw dividend index := by
  induction n with
  | zero => omega
  | succ n ih =>
      let current := copyLoopMemory mem aw dividend rem n
      let value := arrayWord current aw dividend n
      have hcurrentSize : current.size = mem.size :=
        copyLoopMemory_size_eq mem aw dividend rem n
          (fun i hi => hwrite i (by omega))
      have hdestination : (arrayAddress rem n).toNat + 32 ≤ mem.size :=
        hwrite n (by omega)
      have hfinalSize : (copyMemory current rem n value).size = mem.size := by
        unfold copyMemory
        apply toByteArray_write32_size_of_le current value (arrayAddress rem n).toNat
          mem.size mem.size hcurrentSize
        · rw [hcurrentSize]
          omega
        · apply max_eq_left
          exact hdestination
      by_cases hlast : index = n
      · subst index
        have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
          simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using
            umul_toNat (a := aw) (b := (⟨32⟩ : UInt256)) hawFit
        have hactive : ¬ arrayAddress rem n ≥ aw * ⟨32⟩ := by
          intro hge
          have hgeNat : (aw * (⟨32⟩ : UInt256)).toNat ≤ (arrayAddress rem n).toNat := hge
          rw [hmul] at hgeNat
          have ha := hdestinationActive n (by omega)
          omega
        have hsource : value = arrayWord mem aw dividend n := by
          exact arrayWord_copyLoopMemory_eq mem aw dividend rem n n
            (fun i hi => hwrite i (by omega))
            (fun i hi => hsourceBelow n (by omega) i (by omega))
        have hstored : arrayWord (copyMemory current rem n value) aw rem n = value := by
          unfold arrayWord MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
            MultiLimbDivisionTrace.readWord
          rw [if_neg (not_or.mpr ⟨by rw [hfinalSize]; omega, hactive⟩)]
          unfold copyMemory
          rw [toByteArray_write32_read_back current value (arrayAddress rem n).toNat
            (by rw [hcurrentSize]; omega), fromByteArrayBigEndian_toByteArray,
            u256_ofNat_toNat]
        unfold copyLoopMemory
        change arrayWord (copyMemory current rem n value) aw rem n = _
        exact hstored.trans hsource
      · have hi : index < n := by omega
        have hread :
            (value.toByteArray.write 0 current (arrayAddress rem n).toNat 32).readWithPadding
                (arrayAddress rem index).toNat 32 =
              current.readWithPadding (arrayAddress rem index).toNat 32 := by
          apply write32_read_below
          · rw [toByteArray_size]
          · rw [hcurrentSize]
            omega
          · exact hdestinationBelow index (by omega) n (by omega) (by omega)
        unfold copyLoopMemory
        change arrayWord (copyMemory current rem n value) aw rem index = _
        have hpreserved :
            arrayWord (copyMemory current rem n value) aw rem index =
              arrayWord current aw rem index := by
          unfold arrayWord MultiLimbOddCompare.loadedWord MultiLimbOddCompare.headerWord
            MultiLimbDivisionTrace.readWord
          rw [hfinalSize, hcurrentSize]
          unfold copyMemory
          rw [hread]
        rw [hpreserved]
        exact ih hi
          (fun i hi' => hwrite i (by omega))
          (fun i hi' j hj => hsourceBelow i (by omega) j (by omega))
          (fun i hi' j hj hij => hdestinationBelow i (by omega) j (by omega) hij)
          (fun i hi' => hdestinationActive i (by omega))

/-- Exact iteration of the shorter-dividend copy loop over an evolving memory state. -/
theorem copyCycles
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C n m dividendCount remCount : Nat} {tail : List UInt256}
    {quotient ret dividend rem : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hn : n ≤ m)
    (hmDividend : m ≤ dividendCount)
    (hmRem : m ≤ remCount)
    (hcountBound : dividendCount ≤ 32)
    (hremCountBound : remCount ≤ 32)
    (hdivHeader : ∀ i, i < n →
      arrayHeader (copyLoopMemory mem aw dividend rem i) aw dividend =
        UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hdivElementAw : ∀ i, i < n → arrayAfterWord aw dividend i = aw)
    (hremHeader : ∀ i, i < n →
      arrayHeader (copyLoopMemory mem aw dividend rem i) aw rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremElementAw : ∀ i, i < n → arrayAfterWord aw rem i = aw)
    (h : RDx runtimeBytecode ee g s0 ⟨6229⟩
      (⟨0⟩ :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨6229⟩
      (UInt256.ofNat n :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      (copyLoopMemory mem aw dividend rem n) aw rdata acc
      (k + 58 * n) (C + 208 * n) := by
  induction n with
  | zero =>
      simpa [copyLoopMemory] using h
  | succ n ih =>
      have hn' : n ≤ m := by omega
      have rdCurrent := ih hn'
        (fun i hi => hdivHeader i (by omega))
        (fun i hi => hdivElementAw i (by omega))
        (fun i hi => hremHeader i (by omega))
        (fun i hi => hremElementAw i (by omega))
      have rdNext := copyCycle
        (mem := copyLoopMemory mem aw dividend rem n)
        (i := n) (m := m) (dividendCount := dividendCount) (remCount := remCount)
        hdepth (by omega) hmDividend hmRem hcountBound hremCountBound
        (hdivHeader n (by omega)) hdivHeaderAw (hdivElementAw n (by omega))
        rfl (hremHeader n (by omega)) hremHeaderAw (hremElementAw n (by omega))
        rdCurrent
      have normalized := rdNext.withIndices
        (k' := k + 58 * (n + 1)) (C' := C + 208 * (n + 1))
        (by omega) (by omega)
      simpa [copyLoopMemory] using normalized

/-- The exhausted copy loop removes its locals and returns `(quotient, rem)` to PC 2289. -/
theorem copyExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m : Nat} {tail : List UInt256}
    {quotient ret dividend rem : UInt256}
    (hdepth : tail.length + 6 ≤ 1022)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6229⟩
      (UInt256.ofNat m :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (rem :: quotient :: tail)
      mem aw rdata acc (k + 12) (C + 43) := by
  have hcondition : (UInt256.ofNat m).lt (UInt256.ofNat m) = ⟨0⟩ := by
    apply ult_zero
    omega
  have rd6244 := GeneratedTraces.trace_6229_notTaken
    (tail := quotient :: ret :: rem :: tail)
    (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
  have rdret := GeneratedTraces.trace_6237_jump
    (by omega) rd6244 (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := k + 12) (C' := C + 43) (by omega) (by omega)
  simpa using normalized

/-- Exact complete copy loop from index zero through the internal function return. -/
theorem copyAllThroughReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C m dividendCount remCount : Nat} {tail : List UInt256}
    {quotient ret dividend rem : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (hmDividend : m ≤ dividendCount)
    (hmRem : m ≤ remCount)
    (hcountBound : dividendCount ≤ 32)
    (hremCountBound : remCount ≤ 32)
    (hdivHeader : ∀ i, i < m →
      arrayHeader (copyLoopMemory mem aw dividend rem i) aw dividend =
        UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader aw dividend = aw)
    (hdivElementAw : ∀ i, i < m → arrayAfterWord aw dividend i = aw)
    (hremHeader : ∀ i, i < m →
      arrayHeader (copyLoopMemory mem aw dividend rem i) aw rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader aw rem = aw)
    (hremElementAw : ∀ i, i < m → arrayAfterWord aw rem i = aw)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6229⟩
      (⟨0⟩ :: dividend :: UInt256.ofNat m :: quotient :: ret :: rem :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ret (rem :: quotient :: tail)
      (copyLoopMemory mem aw dividend rem m) aw rdata acc
      (k + 58 * m + 12) (C + 208 * m + 43) := by
  have rdEnd := copyCycles hdepth (by omega : m ≤ m) hmDividend hmRem
    hcountBound hremCountBound hdivHeader hdivHeaderAw hdivElementAw
    hremHeader hremHeaderAw hremElementAw h
  have rdret := copyExit (by omega) hret rdEnd
  have normalized := rdret.withIndices
    (k' := k + 58 * m + 12) (C' := C + 208 * m + 43)
    (by omega) (by omega)
  simpa using normalized

/-- Exact shorter-dividend execution from the branch body through its internal return. -/
theorem executeThroughReturn
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m dividendCount remCount : Nat} {tail : List UInt256}
    {kEff rem dividend ret divisor : UInt256}
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1008)
    (hmDividend : m ≤ dividendCount)
    (hmRem : m ≤ remCount)
    (hcountBound : dividendCount ≤ 32)
    (hremCountBound : remCount ≤ 32)
    (hdivHeader : ∀ i, i < m →
      arrayHeader
          (copyLoopMemory (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp)
            dividend rem i)
          (shortAllocatedWords aw fp) dividend = UInt256.ofNat dividendCount)
    (hdivHeaderAw : arrayAfterHeader (shortAllocatedWords aw fp) dividend =
      shortAllocatedWords aw fp)
    (hdivElementAw : ∀ i, i < m →
      arrayAfterWord (shortAllocatedWords aw fp) dividend i = shortAllocatedWords aw fp)
    (hremHeader : ∀ i, i < m →
      arrayHeader
          (copyLoopMemory (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp)
            dividend rem i)
          (shortAllocatedWords aw fp) rem = UInt256.ofNat remCount)
    (hremHeaderAw : arrayAfterHeader (shortAllocatedWords aw fp) rem =
      shortAllocatedWords aw fp)
    (hremElementAw : ∀ i, i < m →
      arrayAfterWord (shortAllocatedWords aw fp) rem i = shortAllocatedWords aw fp)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6214⟩
      (kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (rem :: UInt256.ofNat fp :: tail)
      (copyLoopMemory (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp)
        dividend rem m)
      (shortAllocatedWords aw fp) rdata acc
      (k + 68 + 58 * m) (C + shortAllocationGas aw fp + 49 + 208 * m) := by
  have rd6233 := allocationExact hfp hbound hmemSize hmemLe hgap haw3 haw64 hread
    hcalldata (by omega) h
  have rd6236 := setupCopyLoop (by omega) rd6233
  have rdret := copyAllThroughReturn (by omega) hmDividend hmRem hcountBound
    hremCountBound hdivHeader hdivHeaderAw hdivElementAw hremHeader hremHeaderAw
    hremElementAw hret rd6236
  have normalized := rdret.withIndices
    (k' := k + 68 + 58 * m)
    (C' := C + shortAllocationGas aw fp + 49 + 208 * m)
    (by omega) (by omega)
  simpa using normalized

/-- The exact shorter-dividend execution under ordinary in-memory array-layout facts. -/
theorem executeThroughReturnOfLayout
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp m dividendCount remCount : Nat} {tail : List UInt256}
    {kEff rem dividend ret divisor : UInt256}
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1008)
    (hmDividend : m ≤ dividendCount)
    (hmRem : m ≤ remCount)
    (hcountBound : dividendCount ≤ 32)
    (hremCountBound : remCount ≤ 32)
    (hdivHeaderInitial :
      arrayHeader (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp) dividend =
        UInt256.ofNat dividendCount)
    (hremHeaderInitial :
      arrayHeader (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp) rem =
        UInt256.ofNat remCount)
    (hwrite : ∀ i, i < m →
      (arrayAddress rem i).toNat + 32 ≤ (shortAllocatedMemory mem fp).size)
    (hdivHeaderBelow : ∀ j, j < m →
      dividend.toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hdivElementBelow : ∀ i, i < m → ∀ j, j < m →
      (arrayAddress dividend i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hremHeaderBelow : ∀ j, j < m →
      rem.toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hremElementBelow : ∀ i, i < m → ∀ j, j < m → i < j →
      (arrayAddress rem i).toNat + 32 ≤ (arrayAddress rem j).toNat)
    (hawFit : (shortAllocatedWords aw fp).toNat * 32 < UInt256.size)
    (hdivHeaderActive : dividend.toNat + 32 ≤
      32 * (shortAllocatedWords aw fp).toNat)
    (hdivElementActive : ∀ i, i < m →
      (arrayAddress dividend i).toNat + 32 ≤ 32 * (shortAllocatedWords aw fp).toNat)
    (hremHeaderActive : rem.toNat + 32 ≤ 32 * (shortAllocatedWords aw fp).toNat)
    (hremElementActive : ∀ i, i < m →
      (arrayAddress rem i).toNat + 32 ≤ 32 * (shortAllocatedWords aw fp).toNat)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6214⟩
      (kEff :: UInt256.ofNat m :: rem :: dividend :: ret :: divisor :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
        (rem :: UInt256.ofNat fp :: tail)
        (copyLoopMemory (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp)
          dividend rem m)
        (shortAllocatedWords aw fp) rdata acc
        (k + 68 + 58 * m) (C + shortAllocationGas aw fp + 49 + 208 * m) ∧
      ∀ i, i < m →
        arrayWord
            (copyLoopMemory (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp)
              dividend rem m)
            (shortAllocatedWords aw fp) rem i =
          arrayWord (shortAllocatedMemory mem fp) (shortAllocatedWords aw fp) dividend i := by
  let allocatedMem := shortAllocatedMemory mem fp
  let allocatedAw := shortAllocatedWords aw fp
  have hdivHeader : ∀ i, i < m →
      arrayHeader (copyLoopMemory allocatedMem allocatedAw dividend rem i)
          allocatedAw dividend = UInt256.ofNat dividendCount := by
    intro i hi
    rw [arrayHeader_copyLoopMemory_eq allocatedMem allocatedAw dividend rem dividend i
      (fun j hj => hwrite j (by omega))
      (fun j hj => hdivHeaderBelow j (by omega))]
    exact hdivHeaderInitial
  have hremHeader : ∀ i, i < m →
      arrayHeader (copyLoopMemory allocatedMem allocatedAw dividend rem i)
          allocatedAw rem = UInt256.ofNat remCount := by
    intro i hi
    rw [arrayHeader_copyLoopMemory_eq allocatedMem allocatedAw dividend rem rem i
      (fun j hj => hwrite j (by omega))
      (fun j hj => hremHeaderBelow j (by omega))]
    exact hremHeaderInitial
  have hdivHeaderAw : arrayAfterHeader allocatedAw dividend = allocatedAw :=
    MultiLimbOddCompare.afterHeader_eq_of_access allocatedAw dividend hdivHeaderActive
  have hremHeaderAw : arrayAfterHeader allocatedAw rem = allocatedAw :=
    MultiLimbOddCompare.afterHeader_eq_of_access allocatedAw rem hremHeaderActive
  have hdivElementAw : ∀ i, i < m → arrayAfterWord allocatedAw dividend i = allocatedAw := by
    intro i hi
    exact MultiLimbOddCompare.afterHeader_eq_of_access allocatedAw (arrayAddress dividend i)
      (hdivElementActive i hi)
  have hremElementAw : ∀ i, i < m → arrayAfterWord allocatedAw rem i = allocatedAw := by
    intro i hi
    exact MultiLimbOddCompare.afterHeader_eq_of_access allocatedAw (arrayAddress rem i)
      (hremElementActive i hi)
  constructor
  · exact executeThroughReturn hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
      htail hmDividend hmRem hcountBound hremCountBound hdivHeader hdivHeaderAw
      hdivElementAw hremHeader hremHeaderAw hremElementAw hret h
  · intro i hi
    exact copyLoopMemory_copied_word allocatedMem allocatedAw dividend rem m i hawFit hi
      hwrite hdivElementBelow hremElementBelow hremElementActive

end Modexp.MultiLimbSchoolbookShort
