import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulOuter
import Examples.Precompiles.Modexp.Allocation

/-!
# Standalone schoolbook-multiplication function contract

This module executes Solidity's checked result-length addition, the concrete zero-initialized
result allocation, the complete assembly multiplication loops, and the dynamic return.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem addLengthsWord
    (aCount bCount : Nat) (hsumWord : aCount + bCount < UInt256.size) :
    UInt256.ofNat aCount + UInt256.ofNat bCount = UInt256.ofNat (aCount + bCount) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : aCount < UInt256.size),
    UInt256.toNat_ofNat_of_lt (by omega : bCount < UInt256.size),
    Nat.mod_eq_of_lt hsumWord, UInt256.toNat_ofNat_of_lt hsumWord]

/-- The PC 5016 prefix performs Solidity's checked `aLen + bLen` and reaches the deployed dynamic
word-array allocator. The overflow branch is proved unreachable from the natural sum bound. -/
theorem allocationEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr returnPc : UInt256}
    (hsumWord : aCount + bCount < UInt256.size)
    (hdepth : tail.length + 5 ≤ 1019)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (aPtr :: UInt256.ofNat aCount :: bPtr :: UInt256.ofNat bCount :: returnPc :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
      (UInt256.ofNat (aCount + bCount) :: ⟨5036⟩ :: UInt256.ofNat bCount ::
        UInt256.ofNat aCount :: bPtr :: returnPc :: aPtr :: tail)
      mem aw rdata acc (k + 23) (C + 85) := by
  have hsum := addLengthsWord aCount bCount hsumWord
  have hoverflow : UInt256.gt (UInt256.ofNat aCount)
      (UInt256.ofNat aCount + UInt256.ofNat bCount) = ⟨0⟩ := by
    apply ugt_zero
    rw [hsum, UInt256.toNat_ofNat_of_lt hsumWord,
      UInt256.toNat_ofNat_of_lt (by omega : aCount < UInt256.size)]
    omega
  have rd1432 := GeneratedTraces.trace_5016_body hdepth h
  have rd1433 := rd1432.jumpiNT (by native_decide) hoverflow
    (by simp only [List.length_cons]; omega)
  have rd5031 := rd1433.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1487 := evm_run rd5031 with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)
  ]
  have normalized := rd1487.withIndices (k' := k + 23) (C' := C + 85)
    (by omega) (by omega)
  simpa [hsum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

def functionAllocatedMemory (mem : ByteArray) (fp aCount bCount : Nat) : ByteArray :=
  storeBytesLength
    (setFreePtr mem (fp + wordArrayAllocationSize (aCount + bCount)))
    fp (aCount + bCount)

def functionAllocatedWords (aw : UInt256) (fp aCount bCount : Nat) : UInt256 :=
  newWordArrayWords aw fp (aCount + bCount)

/-- Execute the checked prefix and concrete result allocation, then initialize the assembly outer
guard at `i = 0`. -/
theorem setupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr returnPc : UInt256}
    (hsum : aCount + bCount ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (aPtr :: UInt256.ofNat aCount :: bPtr :: UInt256.ofNat bCount :: returnPc :: tail)
      mem aw rdata acc k C) :
    let allocatedMem := functionAllocatedMemory mem fp aCount bCount
    let allocatedAw := functionAllocatedWords aw fp aCount bCount
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5046⟩
      (outerGuardStack { i := ⟨0⟩, memory := allocatedMem, activeWords := allocatedAw }
        aPtr bCount (UInt256.ofNat aCount) bPtr returnPc (UInt256.ofNat fp) tail)
      allocatedMem allocatedAw rdata acc (k + 109)
      (C + 104 + newWordArrayGas aw fp (aCount + bCount)) := by
  have hsumWord : aCount + bCount < UInt256.size := by
    exact lt_trans (by omega : aCount + bCount < 2 ^ 64) (by decide)
  have rd1487 := allocationEntryExact hsumWord (by omega) h
  have rd5036 := newWordArrayExact68 hsum hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have rd5046 := GeneratedTraces.trace_5036_body
    (by omega) rd5036
  have normalized := rd5046.withIndices (k' := k + 109) (by omega)
    (C' := C + 104 + newWordArrayGas aw fp (aCount + bCount)) (by omega)
  simpa [functionAllocatedMemory, functionAllocatedWords, outerGuardStack,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

def functionInitialState
    (mem : ByteArray) (aw : UInt256) (fp aCount bCount : Nat) : OuterState where
  i := ⟨0⟩
  memory := functionAllocatedMemory mem fp aCount bCount
  activeWords := functionAllocatedWords aw fp aCount bCount

def functionFinalState
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat) : OuterState :=
  rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount aCount
    (functionInitialState mem aw fp aCount bCount)

/-- Complete exact execution of the deployed standalone `LimbMath.schoolbookMul`: checked length
addition, zero-initialized result allocation, all source rows, and dynamic return. -/
theorem functionExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr returnPc : UInt256}
    (hsum : aCount + bCount ≤ 68)
    (hbPos : 0 < bCount)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (aPtr :: UInt256.ofNat aCount :: bPtr :: UInt256.ofNat bCount :: returnPc :: tail)
      mem aw rdata acc k C) :
    let initial := functionInitialState mem aw fp aCount bCount
    let final := functionFinalState mem aw aPtr bPtr fp aCount bCount
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat fp :: tail) final.memory final.activeWords rdata acc
      (k + 116 + rowsSteps aPtr bPtr (UInt256.ofNat fp) bCount aCount initial)
      (C + 132 + newWordArrayGas aw fp (aCount + bCount) +
        rowsGas aPtr bPtr (UInt256.ofNat fp) bCount aCount initial) := by
  have haWord : aCount < UInt256.size :=
    lt_trans (by omega : aCount < 2 ^ 64) (by decide)
  have hbWord : bCount < UInt256.size :=
    lt_trans (by omega : bCount < 2 ^ 64) (by decide)
  have rdSetup := setupExact hsum hfp hbound hmemSize hmemLe hgap haw3 haw64 hread
    hcalldata hdepth h
  let initial := functionInitialState mem aw fp aCount bCount
  let final := functionFinalState mem aw aPtr bPtr fp aCount bCount
  have rdReturn := rowsFromZeroReturnExact haWord hbPos hbWord hreturn hdepth
    (by simpa [initial, functionInitialState, functionAllocatedMemory, functionAllocatedWords]
      using rdSetup)
  have normalized := rdReturn.withIndices
    (k' := k + 116 + rowsSteps aPtr bPtr (UInt256.ofNat fp) bCount aCount initial) (by
      dsimp only [initial, functionInitialState, functionAllocatedMemory,
        functionAllocatedWords]
      omega)
    (C' := C + 132 + newWordArrayGas aw fp (aCount + bCount) +
      rowsGas aPtr bPtr (UInt256.ofNat fp) bCount aCount initial) (by
        dsimp only [initial, functionInitialState, functionAllocatedMemory,
          functionAllocatedWords]
        omega)
  simpa [final, functionFinalState, initial, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

/-! ## Reused scratch-memory execution

After the first Barrett multiplication, EVM memory remains materialized through the complete
scratch region while Solidity restores only `mem[0x40]`.  These definitions and wrappers retain
that concrete tail and use the allocator's in-place zeroing result. -/

def reusedFunctionAllocatedMemory (mem : ByteArray) (fp aCount bCount : Nat) : ByteArray :=
  reusedWordArrayMemory mem fp (aCount + bCount)

def reusedFunctionInitialState
    (mem : ByteArray) (aw : UInt256) (fp aCount bCount : Nat) : OuterState where
  i := ⟨0⟩
  memory := reusedFunctionAllocatedMemory mem fp aCount bCount
  activeWords := functionAllocatedWords aw fp aCount bCount

def reusedFunctionFinalState
    (mem : ByteArray) (aw aPtr bPtr : UInt256) (fp aCount bCount : Nat) : OuterState :=
  rowsIterate aPtr bPtr (UInt256.ofNat fp) bCount aCount
    (reusedFunctionInitialState mem aw fp aCount bCount)

theorem setupExactReused
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr returnPc : UInt256}
    (hsum : aCount + bCount ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (aPtr :: UInt256.ofNat aCount :: bPtr :: UInt256.ofNat bCount :: returnPc :: tail)
      mem aw rdata acc k C) :
    let allocatedMem := reusedFunctionAllocatedMemory mem fp aCount bCount
    let allocatedAw := functionAllocatedWords aw fp aCount bCount
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5046⟩
      (outerGuardStack { i := ⟨0⟩, memory := allocatedMem, activeWords := allocatedAw }
        aPtr bCount (UInt256.ofNat aCount) bPtr returnPc (UInt256.ofNat fp) tail)
      allocatedMem allocatedAw rdata acc (k + 109)
      (C + 104 + newWordArrayGas aw fp (aCount + bCount)) := by
  have hsumWord : aCount + bCount < UInt256.size :=
    lt_trans (by omega : aCount + bCount < 2 ^ 64) (by decide)
  have rd1487 := allocationEntryExact hsumWord (by omega) h
  have rd5036 := newWordArrayExact68Reused hsum hfp hbound hmemSize haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have rd5046 := GeneratedTraces.trace_5036_body (by omega) rd5036
  have normalized := rd5046.withIndices (k' := k + 109) (by omega)
    (C' := C + 104 + newWordArrayGas aw fp (aCount + bCount)) (by omega)
  simpa [reusedFunctionAllocatedMemory, functionAllocatedWords, outerGuardStack,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

theorem functionExactReused
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fp aCount bCount : Nat} {tail : List UInt256}
    {aPtr bPtr returnPc : UInt256}
    (hsum : aCount + bCount ≤ 68) (hbPos : 0 < bCount)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (aCount + bCount) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hdepth : tail.length + 10 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (aPtr :: UInt256.ofNat aCount :: bPtr :: UInt256.ofNat bCount :: returnPc :: tail)
      mem aw rdata acc k C) :
    let initial := reusedFunctionInitialState mem aw fp aCount bCount
    let final := reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat fp :: tail) final.memory final.activeWords rdata acc
      (k + 116 + rowsSteps aPtr bPtr (UInt256.ofNat fp) bCount aCount initial)
      (C + 132 + newWordArrayGas aw fp (aCount + bCount) +
        rowsGas aPtr bPtr (UInt256.ofNat fp) bCount aCount initial) := by
  have haWord : aCount < UInt256.size :=
    lt_trans (by omega : aCount < 2 ^ 64) (by decide)
  have hbWord : bCount < UInt256.size :=
    lt_trans (by omega : bCount < 2 ^ 64) (by decide)
  have rdSetup := setupExactReused hsum hfp hbound hmemSize haw3 haw64 hread
    hcalldata hdepth h
  let initial := reusedFunctionInitialState mem aw fp aCount bCount
  let final := reusedFunctionFinalState mem aw aPtr bPtr fp aCount bCount
  have rdReturn := rowsFromZeroReturnExact haWord hbPos hbWord hreturn hdepth
    (by simpa [initial, reusedFunctionInitialState, reusedFunctionAllocatedMemory,
      functionAllocatedWords] using rdSetup)
  have normalized := rdReturn.withIndices
    (k' := k + 116 + rowsSteps aPtr bPtr (UInt256.ofNat fp) bCount aCount initial) (by
      dsimp only [initial, reusedFunctionInitialState, reusedFunctionAllocatedMemory,
        functionAllocatedWords]
      omega)
    (C' := C + 132 + newWordArrayGas aw fp (aCount + bCount) +
      rowsGas aPtr bPtr (UInt256.ofNat fp) bCount aCount initial) (by
        dsimp only [initial, reusedFunctionInitialState, reusedFunctionAllocatedMemory,
          functionAllocatedWords]
        omega)
  simpa [final, reusedFunctionFinalState, initial, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

end Modexp.MultiLimbSchoolbookMulTrace
