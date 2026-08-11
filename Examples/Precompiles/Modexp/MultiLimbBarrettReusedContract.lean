import Examples.Precompiles.Modexp.MultiLimbBarrettReductionContract

/-!
# Barrett execution over reused Solidity scratch memory

EVM memory does not shrink when the exponent loop restores Solidity's free-memory pointer.  This
module gives each Barrett allocation/product boundary an exact counterpart that retains the
already-materialized scratch tail and zeroes reused array payloads through the deployed
`CALLDATACOPY(calldatasize(), ...)` instruction.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettReused

open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbBarrettCorrection
open Modexp.MultiLimbBarrettReduction
open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbBarrettTruncatedMul
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def firstProductInitial
    (mem : ByteArray) (aw : UInt256) (fp kWords : Nat) : OuterState :=
  reusedFunctionInitialState mem aw fp kWords kWords

def firstProductFinal
    (mem : ByteArray) (aw a b : UInt256) (fp kWords : Nat) : OuterState :=
  reusedFunctionFinalState mem aw a b fp kWords kWords

theorem firstProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {a b n mu returnPc : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 16 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial := firstProductInitial mem aw fp kWords
    let final := firstProductFinal mem aw a b fp kWords
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6468⟩
      (UInt256.ofNat fp :: ⟨6536⟩ :: n :: UInt256.ofNat kWords :: ⟨6530⟩ ::
        returnPc :: mu :: tail)
      final.memory final.activeWords rdata acc
      (steps + 130 + rowsSteps a b (UInt256.ofNat fp) kWords kWords initial)
      (gasUsed + 177 + newWordArrayGas aw fp (2 * kWords) +
        rowsGas a b (UInt256.ofNat fp) kWords kWords initial) := by
  have rd5016 := Modexp.MultiLimbBarrettMul.firstProductEntryExact (by omega) h
  have rd6468 := functionExactReused (aCount := kWords) (bCount := kWords) (fp := fp)
    (returnPc := (⟨6468⟩ : UInt256))
    (tail := ⟨6536⟩ :: n :: UInt256.ofNat kWords :: ⟨6530⟩ :: returnPc :: mu :: tail)
    (by omega) hkPos hfp (by
      rw [show kWords + kWords = 2 * kWords by omega]
      exact hbound)
    hmemSize haw3 haw64 hread hcalldata (by native_decide)
    (by simp only [List.length_cons]; omega) rd5016
  let initial := firstProductInitial mem aw fp kWords
  let final := firstProductFinal mem aw a b fp kWords
  have normalized := rd6468.withIndices
    (k' := steps + 130 + rowsSteps a b (UInt256.ofNat fp) kWords kWords initial) (by
      dsimp only [initial, firstProductInitial])
    (C' := gasUsed + 177 + newWordArrayGas aw fp (2 * kWords) +
      rowsGas a b (UInt256.ofNat fp) kWords kWords initial) (by
        dsimp only [initial, firstProductInitial]
        rw [show kWords + kWords = 2 * kWords by omega])
  simpa [final, firstProductFinal, reusedFunctionFinalState, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def q1AllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  reusedWordArrayMemory mem fp (kWords + 2)

theorem q1AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {product n mu returnPc : UInt256}
    (hkBound : kWords + 2 ≤ 68) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6468⟩
      (product :: ⟨6536⟩ :: n :: UInt256.ofNat kWords :: ⟨6530⟩ :: returnPc :: mu :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6490⟩
      (UInt256.ofNat fp :: mu :: ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ ::
        n :: UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      (q1AllocatedMemory mem fp kWords) (q1AllocatedWords aw fp kWords)
      rdata acc (steps + 103) (gasUsed + 91 + newWordArrayGas aw fp (kWords + 2)) := by
  have hkWord : kWords + 2 < UInt256.size :=
    lt_trans (by omega : kWords + 2 < 2 ^ 64) (by decide)
  have rd1487 := Modexp.MultiLimbBarrettMul.q1AllocationEntryExact hkWord hdepth h
  have rd6490 := newWordArrayExact68Reused hkBound hfp hbound hmemSize haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have normalized := rd6490.withIndices (k' := steps + 103) (by omega)
    (C' := gasUsed + 91 + newWordArrayGas aw fp (kWords + 2)) (by omega)
  simpa [q1AllocatedMemory, q1AllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def secondProductInitial
    (mem : ByteArray) (aw : UInt256) (fp kWords : Nat) : OuterState :=
  reusedFunctionInitialState mem aw fp (kWords + 2) (kWords + 2)

def secondProductFinal
    (mem : ByteArray) (aw q1 mu : UInt256) (fp kWords : Nat) : OuterState :=
  reusedFunctionFinalState mem aw q1 mu fp (kWords + 2) (kWords + 2)

theorem secondProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (hkBound : 2 * kWords + 4 ≤ 68) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 17 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (q1 :: UInt256.ofNat (kWords + 2) :: mu :: UInt256.ofNat (kWords + 2) ::
        ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial := secondProductInitial mem aw fp kWords
    let final := secondProductFinal mem aw q1 mu fp kWords
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6530⟩
      (UInt256.ofNat fp :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      final.memory final.activeWords rdata acc
      (steps + 116 + rowsSteps q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) initial)
      (gasUsed + 132 + newWordArrayGas aw fp (2 * kWords + 4) +
        rowsGas q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) initial) := by
  have rd6530 := functionExactReused (aCount := kWords + 2) (bCount := kWords + 2)
    (fp := fp) (returnPc := (⟨6530⟩ : UInt256))
    (tail := UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
      UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
    (by omega) (by omega) hfp (by
      rw [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega]
      exact hbound)
    hmemSize haw3 haw64 hread hcalldata (by native_decide)
    (by simp only [List.length_cons]; omega) h
  let initial := secondProductInitial mem aw fp kWords
  let final := secondProductFinal mem aw q1 mu fp kWords
  have normalized := rd6530.withIndices
    (k' := steps + 116 +
      rowsSteps q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) initial) (by
        dsimp only [initial, secondProductInitial])
    (C' := gasUsed + 132 + newWordArrayGas aw fp (2 * kWords + 4) +
      rowsGas q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) initial) (by
        dsimp only [initial, secondProductInitial]
        rw [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega])
  simpa [final, secondProductFinal, reusedFunctionFinalState, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def q3AllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  reusedWordArrayMemory mem fp (kWords + 3)

theorem q3AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords + 4 ≤ 68) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6530⟩
      (q2 :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6582⟩
      (UInt256.ofNat fp :: q2 :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (2 * kWords + 4) :: returnPc :: product :: tail)
      (q3AllocatedMemory mem fp kWords) (q3AllocatedWords aw fp kWords)
      rdata acc (steps + 154) (gasUsed + 288 + newWordArrayGas aw fp (kWords + 3)) := by
  have rd1487 := Modexp.MultiLimbBarrettMul.q3AllocationEntryExact hkPos hkBound hdepth h
  have rd6582 := newWordArrayExact68Reused (by omega) hfp hbound hmemSize haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have normalized := rd6582.withIndices (k' := steps + 154) (by omega)
    (C' := gasUsed + 288 + newWordArrayGas aw fp (kWords + 3)) (by omega)
  simpa [q3AllocatedMemory, q3AllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def r2AllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  reusedWordArrayMemory mem fp (kWords + 1)

theorem r2AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q3 n returnPc product : UInt256}
    (hkBound : kWords + 1 ≤ 68) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6656⟩
      (UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6666⟩
      (UInt256.ofNat fp :: UInt256.ofNat (kWords + 3) :: UInt256.ofNat (kWords + 1) ::
        n :: UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      (r2AllocatedMemory mem fp kWords) (r2AllocatedWords aw fp kWords)
      rdata acc (steps + 84) (gasUsed + 21 + newWordArrayGas aw fp (kWords + 1)) := by
  have rd1487 := evm_run h with [jumpdest, swap1, pushCanonical 2 .PUSH2 ⟨6666⟩ (by decide),
    dup3, pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide), jump (by native_decide)]
  have rd6666 := newWordArrayExact68Reused hkBound hfp hbound hmemSize haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have normalized := rd6666.withIndices (k' := steps + 84) (by omega)
    (C' := gasUsed + 21 + newWordArrayGas aw fp (kWords + 1)) (by omega)
  simpa [r2AllocatedMemory, r2AllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def resultAllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  reusedWordArrayMemory mem fp kWords

theorem resultAllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {i q3 q3Cap n r2 returnPc product : UInt256}
    (hkBound : kWords ≤ 68) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kWords < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6685⟩
      (i :: q3 :: q3Cap :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: r2 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6696⟩
      (UInt256.ofNat fp :: UInt256.ofNat (kWords + 1) :: n :: UInt256.ofNat kWords ::
        r2 :: returnPc :: product :: tail)
      (resultAllocatedMemory mem fp kWords) (resultAllocatedWords aw fp kWords)
      rdata acc (steps + 85) (gasUsed + 23 + newWordArrayGas aw fp kWords) := by
  have rd1487 := Modexp.MultiLimbBarrettSubtract.resultAllocationEntryExact (by omega) h
  have rd6696 := newWordArrayExact68Reused hkBound hfp hbound hmemSize haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have normalized := rd6696.withIndices (k' := steps + 85) (by omega)
    (C' := gasUsed + 23 + newWordArrayGas aw fp kWords) (by omega)
  simpa [resultAllocatedMemory, resultAllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

def selectBarrettFromTruncated (fuel : Nat) (mem : ByteArray) (aw q3 n r2 product : UInt256)
    (fp kWords : Nat) : Option BarrettCorrectionSelection :=
  let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory fp kWords
  let resultAw := resultAllocatedWords final.activeWords fp kWords
  selectBarrettReductionTail fuel resultMem resultAw product n r2 (UInt256.ofNat fp) kWords

theorem selectBarrettFromTruncated_exists
    {fuel fp kWords : Nat} {mem : ByteArray} {aw q3 n r2 product : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected,
      selectBarrettFromTruncated fuel mem aw q3 n r2 product fp kWords = some selected := by
  unfold selectBarrettFromTruncated
  exact selectBarrettReductionTail_exists hkPos hfuel

theorem selectedBarrettFromTruncatedExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {q3 n r2 returnPc product : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize kWords < 2 ^ 64)
    (hmemSize : 96 ≤ (truncatedFinal mem aw q3 n r2 kWords).memory.size)
    (haw3 : 3 ≤ (truncatedFinal mem aw q3 n r2 kWords).activeWords.toNat)
    (haw64 : ¬(⟨64⟩ : UInt256) ≥
      (truncatedFinal mem aw q3 n r2 kWords).activeWords * ⟨32⟩)
    (hread : (truncatedFinal mem aw q3 n r2 kWords).memory.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 13 ≤ 1016)
    (hselect : selectBarrettFromTruncated fuel mem aw q3 n r2 product fp kWords =
      some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6666⟩
      (r2 :: UInt256.ofNat (kWords + 3) :: UInt256.ofNat (kWords + 1) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
    let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
    let resultMem := resultAllocatedMemory final.memory fp kWords
    let resultAw := resultAllocatedWords final.activeWords fp kWords
    let subtractionInitial := subtractionInitialState resultMem resultAw
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (returnPc :: UInt256.ofNat fp :: tail)
      selected.memory selected.activeWords rdata acc
      (steps + 116 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
        44 * (kWords + 1) + selected.steps)
      (gasUsed + 126 + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
        newWordArrayGas final.activeWords fp kWords +
        subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) := by
  have hkWord : kWords + 1 < UInt256.size :=
    (show kWords + 1 < 2 ^ 64 by omega).trans (by decide)
  have hkCap : kWords + 3 < UInt256.size :=
    (show kWords + 3 < 2 ^ 64 by omega).trans (by decide)
  let initial : TruncatedOuterState := { i := 0, memory := mem, activeWords := aw }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory fp kWords
  let resultAw := resultAllocatedWords final.activeWords fp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  have rd6677 := truncatedEntryExact hkCap hdepth h
  have rd6685 := truncatedRowsFromZeroExitExact hkPos hkWord hdepth
    (by simpa only [initial, truncatedOuterStack] using rd6677)
  dsimp only at rd6685
  have rd6696 := resultAllocationExact (fp := fp) (kWords := kWords) (tail := tail)
    (i := UInt256.ofNat final.i) (q3 := q3)
    (q3Cap := UInt256.ofNat (kWords + 1)) (n := n) (r2 := r2)
    (returnPc := returnPc) (product := product) (by omega) hfp hbound
    (by simpa only [final, initial, truncatedFinal] using hmemSize)
    (by simpa only [final, initial, truncatedFinal] using haw3)
    (by simpa only [final, initial, truncatedFinal] using haw64)
    (by simpa only [final, initial, truncatedFinal] using hread)
    hcalldata (by omega) (by simpa only [final, initial, truncatedOuterStack] using rd6685)
  have hselect' : selectBarrettReductionTail fuel resultMem resultAw product n r2
      (UInt256.ofNat fp) kWords = some selected := by
    simpa only [selectBarrettFromTruncated, final, initial, resultMem, resultAw] using hselect
  have rd6737 := selectedBarrettReductionTailExact (tail := tail) (product := product)
    (n := n) (r2 := r2) (returnPc := returnPc) (result := UInt256.ofNat fp)
    selected hkPos hkWord (by omega) hselect'
    (by simpa only [resultMem, resultAw] using rd6696)
  have normalized := rd6737.withIndices
    (k' := steps + 116 + truncatedRowsSteps q3 n r2 kWords (kWords + 1) initial +
      44 * (kWords + 1) + selected.steps) (by simp only [initial]; omega)
    (C' := gasUsed + 126 + truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
      newWordArrayGas final.activeWords fp kWords +
      subtractionThroughExitGas product r2 kWords subtractionInitial + selected.gas) (by
        simp only [subtractionInitial, resultMem, resultAw, final, initial]
        omega)
  simpa only [initial, final, resultMem, resultAw, subtractionInitial] using normalized

end Modexp.MultiLimbBarrettReused
