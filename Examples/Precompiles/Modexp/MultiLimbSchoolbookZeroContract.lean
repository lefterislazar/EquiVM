import Examples.Precompiles.Modexp.MultiLimbSchoolbookShortContract

/-!
# Zero-dividend `schoolbookDiv` return

After leading-zero trimming, an arbitrary nonempty base byte string can still have effective
dividend length zero.  Solidity does not return immediately from that test: it allocates the
one-limb zero quotient first and then returns the already allocated remainder.  This module is
separate so the Barrett proof records that allocation, its memory writes, and its exact gas rather
than replacing the branch with a pure zero shortcut.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookZero

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def allocatedMemory (mem : ByteArray) (fp : Nat) : ByteArray :=
  MultiLimbSchoolbookShort.shortAllocatedMemory mem fp

def allocatedWords (aw : UInt256) (fp : Nat) : UInt256 :=
  MultiLimbSchoolbookShort.shortAllocatedWords aw fp

def totalGas (aw : UInt256) (fp : Nat) : Nat :=
  42 + MultiLimbSchoolbookShort.shortAllocationGas aw fp

/-- Execute the `m == 0` branch from PC 5229 through the internal return. -/
theorem exact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp : Nat} {tail : List UInt256}
    {rem dividend ret count divisor : UInt256}
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize 1 < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (htail : tail.length ≤ 1010)
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5229⟩
      (⟨0⟩ :: rem :: dividend :: ret :: count :: divisor :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (rem :: UInt256.ofNat fp :: tail) (allocatedMemory mem fp)
      (allocatedWords aw fp) rdata acc (steps + 65)
      (gasUsed + totalGas aw fp) := by
  have hsize : bytesAllocationSize 32 = wordArrayAllocationSize 1 := by
    native_decide
  have rd6402 := GeneratedTraces.trace_5229_taken
    (by simp only [List.length_cons]; omega) h
    (by native_decide) (by native_decide) (by native_decide)
  have rd485 := evm_run rd6402 with [
    jumpdest, pop, swap4, pop, pop, swap1, pop,
    pushCanonical 2 .PUSH2 ⟨6416⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨1458⟩ (by decide), jump (by native_decide),
    jumpdest, pushCanonical 1 .PUSH1 ⟨64⟩ (by decide), swap1,
    pushCanonical 2 .PUSH2 ⟨1470⟩ (by decide), dup3,
    pushCanonical 2 .PUSH2 ⟨485⟩ (by decide), jump (by native_decide)]
  have hbound32 : fp + bytesAllocationSize 32 < 2 ^ 64 := by
    rw [hsize]
    exact hbound
  have rd1470 := allocateMemoryExact
    (n := 32) (fp := fp) (ret := 1470)
    (by omega) hfp hbound32 hmemSize haw3 haw64 hread
    (by simp only [List.length_cons]; omega) (by native_decide) rd485
  have rd1486 := GeneratedTraces.trace_1470_body
    (by simp only [List.length_cons]; omega) rd1470
  have rd6416 := rd1486.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hfpWord : fp < UInt256.size :=
    lt_trans (by omega : fp < 2 ^ 64) (by decide)
  have hfp32Word : fp + 32 < UInt256.size := by
    have halloc : wordArrayAllocationSize 1 = 64 := by native_decide
    rw [halloc] at hbound
    exact lt_trans (by omega : fp + 32 < 2 ^ 64) (by decide)
  have hdest : (UInt256.ofNat fp + ⟨32⟩).toNat = fp + 32 := by
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hfpWord,
      show (⟨32⟩ : UInt256).toNat = 32 by native_decide,
      Nat.mod_eq_of_lt hfp32Word]
  have hlen : ((⟨31⟩ : UInt256).lnot + ⟨64⟩).toNat =
      wordArrayPayloadSize 1 := by
    native_decide
  have hcopy :
      I.calldata.write (UInt256.ofNat I.calldata.size).toNat
          (UInt256.toByteArray ⟨1⟩ |>.write 0
            (setFreePtr mem (fp + wordArrayAllocationSize 1)) fp 32)
          (UInt256.ofNat fp + ⟨32⟩).toNat
          ((⟨31⟩ : UInt256).lnot + ⟨64⟩).toNat =
        allocatedMemory mem fp := by
    rw [UInt256.toNat_ofNat_of_lt
      (lt_trans hcalldata (by decide) : I.calldata.size < UInt256.size)]
    rw [hdest, hlen]
    simpa only [allocatedMemory, MultiLimbSchoolbookShort.shortAllocatedMemory] using
      (write_from_source_end_past_dest I.calldata
        (storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize 1)) fp 1)
        I.calldata.size (fp + 32) (wordArrayPayloadSize 1) (le_refl _) (by
          simp [storeBytesLength]
          have hsetSize : (setFreePtr mem (fp + wordArrayAllocationSize 1)).size =
              mem.size := by
            unfold setFreePtr
            apply toByteArray_write32_size_of_le mem _ 64 mem.size mem.size rfl
              (by omega)
            omega
          exact (toByteArray_write32_size_of_ge _ _ fp mem.size (fp + 32)
            hsetSize hmemLe hgap rfl).le))
  rw [hsize, UInt256.toNat_ofNat_of_lt hfpWord, hcopy, hdest, hlen] at rd6416
  have hawEq :
      UInt256.ofNat
        (MachineState.M (UInt256.ofNat (MachineState.M aw.toNat fp 32)).toNat
          (fp + 32) (wordArrayPayloadSize 1)) = allocatedWords aw fp := by
    rfl
  rw [hawEq] at rd6416
  have rdret := GeneratedTraces.trace_6416_jump
    (by omega) rd6416 (by native_decide) hret
  have normalized := rdret.withIndices
    (k' := steps + 65) (C' := gasUsed + totalGas aw fp)
    (by omega) (by
      simp [totalGas, MultiLimbSchoolbookShort.shortAllocationGas,
        newWordArrayCopyExpansionGas, newBytesStoreExpansionGas,
        allocatedWords, MultiLimbSchoolbookShort.shortAllocatedWords,
        newWordArrayWords, newBytesStoreWords, GasConstants.Gverylow,
        GasConstants.Gcopy, wordArrayPayloadSize]
      omega)
  simpa [allocatedMemory, allocatedWords] using normalized

end Modexp.MultiLimbSchoolbookZero
