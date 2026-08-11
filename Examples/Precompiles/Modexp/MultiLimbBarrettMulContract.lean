import Examples.Precompiles.Modexp.MultiLimbSchoolbookMulSemantic
import Examples.Precompiles.Modexp.MultiLimbSchoolbookKnuthSetupContract

/-!
# Barrett multiply-reduce execution contract

This module starts `_barrettMulMod` at PC 6446 and composes its concrete standalone
schoolbook-multiplication calls with the surrounding Barrett setup.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettMul

open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- Enter `_barrettMulMod` and reach its first `schoolbookMul(a,k,b,k)` call. -/
theorem firstProductEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {a b n mu returnPc : UInt256}
    (hdepth : tail.length + 6 ≤ 1014)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: returnPc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (a :: UInt256.ofNat kWords :: b :: UInt256.ofNat kWords :: ⟨6468⟩ ::
        ⟨6536⟩ :: n :: UInt256.ofNat kWords :: ⟨6530⟩ :: returnPc :: mu :: tail)
      mem aw rdata acc (steps + 14) (gasUsed + 45) := by
  have rd := evm_run h with [
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨6468⟩ (by decide),
    dup6,
    dup1,
    swap5,
    swap4,
    pushCanonical 2 .PUSH2 ⟨6530⟩ (by decide),
    swap7,
    swap9,
    swap8,
    pushCanonical 2 .PUSH2 ⟨6536⟩ (by decide),
    swap5,
    pushCanonical 2 .PUSH2 ⟨5016⟩ (by decide),
    jump (by native_decide)
  ]
  exact rd.withIndices (by omega) (by omega)

def firstProductInitial
    (mem : ByteArray) (aw : UInt256) (fp kWords : Nat) : OuterState :=
  functionInitialState mem aw fp kWords kWords

def firstProductFinal
    (mem : ByteArray) (aw a b : UInt256) (fp kWords : Nat) : OuterState :=
  functionFinalState mem aw a b fp kWords kWords

/-- Execute the first full Barrett product `a*b`, including allocation and every multiplication
row, and return to the real PC 6468 continuation. -/
theorem firstProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {a b n mu returnPc : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
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
  have rd5016 := firstProductEntryExact (by omega) h
  have rd6468 := functionExact (aCount := kWords) (bCount := kWords) (fp := fp)
    (returnPc := (⟨6468⟩ : UInt256))
    (tail := ⟨6536⟩ :: n :: UInt256.ofNat kWords :: ⟨6530⟩ :: returnPc :: mu :: tail)
    (by omega) hkPos hfp (by
      rw [show kWords + kWords = 2 * kWords by omega]
      exact hbound)
    hmemSize hmemLe hgap haw3 haw64 hread hcalldata (by native_decide)
    (by simp only [List.length_cons]; omega)
    rd5016
  let initial := firstProductInitial mem aw fp kWords
  let final := firstProductFinal mem aw a b fp kWords
  have normalized := rd6468.withIndices
    (k' := steps + 130 + rowsSteps a b (UInt256.ofNat fp) kWords kWords initial) (by
      dsimp only [initial, firstProductInitial])
    (C' := gasUsed + 177 + newWordArrayGas aw fp (2 * kWords) +
      rowsGas a b (UInt256.ofNat fp) kWords kWords initial) (by
        dsimp only [initial, firstProductInitial]
        rw [show kWords + kWords = 2 * kWords by omega])
  simpa [final, firstProductFinal, functionFinalState, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

theorem addTwoWord (kWords : Nat) (hkWord : kWords + 2 < UInt256.size) :
    UInt256.ofNat kWords + ⟨2⟩ = UInt256.ofNat (kWords + 2) := by
  apply u256_inj
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size),
    show (⟨2⟩ : UInt256).toNat = 2 by decide, Nat.mod_eq_of_lt hkWord,
    UInt256.toNat_ofNat_of_lt hkWord]

/-- After the first product returns, compute checked `q1Len = k+2` and reach the concrete q1
allocation helper while retaining the product pointer and Barrett caller frame. -/
theorem q1AllocationEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {product n mu returnPc : UInt256}
    (hkWord : kWords + 2 < UInt256.size)
    (hdepth : tail.length + 11 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6468⟩
      (product :: ⟨6536⟩ :: n :: UInt256.ofNat kWords :: ⟨6530⟩ :: returnPc :: mu :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
      (UInt256.ofNat (kWords + 2) :: ⟨6490⟩ :: mu :: ⟨6530⟩ ::
        UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 25) (gasUsed + 91) := by
  have hsum := addTwoWord kWords hkWord
  have hoverflow : UInt256.gt (UInt256.ofNat kWords)
      (UInt256.ofNat kWords + ⟨2⟩) = ⟨0⟩ := by
    apply ugt_zero
    rw [hsum, UInt256.toNat_ofNat_of_lt hkWord,
      UInt256.toNat_ofNat_of_lt (by omega : kWords < UInt256.size)]
    omega
  have rd1349 := GeneratedTraces.trace_6468_body (by omega) h
  have rd1350 := rd1349.jumpiNT (by native_decide) hoverflow
    (by simp only [List.length_cons]; omega)
  have rd6478 := rd1350.jump (by native_decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1487 := evm_run rd6478 with [
    jumpdest,
    swap5,
    dup6,
    swap2,
    pushCanonical 2 .PUSH2 ⟨6490⟩ (by decide),
    dup4,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)
  ]
  have normalized := rd1487.withIndices (k' := steps + 25) (C' := gasUsed + 91)
    (by omega) (by omega)
  simpa [hsum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

def q1AllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize (kWords + 2)))
    fp (kWords + 2)

def q1AllocatedWords (aw : UInt256) (fp kWords : Nat) : UInt256 :=
  newWordArrayWords aw fp (kWords + 2)

/-- Allocate the concrete `k+2`-limb q1 array and return to PC 6490 with the product pointer and
all Barrett locals retained. -/
theorem q1AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {product n mu returnPc : UInt256}
    (hkBound : kWords + 2 ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
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
  have rd1487 := q1AllocationEntryExact hkWord hdepth h
  have rd6490 := newWordArrayExact68 hkBound hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata (by simp only [List.length_cons]; omega) (by native_decide) rd1487
  have normalized := rd6490.withIndices (k' := steps + 103) (by omega)
    (C' := gasUsed + 91 + newWordArrayGas aw fp (kWords + 2)) (by omega)
  simpa [q1AllocatedMemory, q1AllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

/-- After q1 allocation, execute the checked `k+1` computation used as the slice length and reach
the concrete copy at PC 6500. -/
theorem q1CopyEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 11 ≤ 1018)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6490⟩
      (q1 :: mu :: ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6500⟩
      (UInt256.ofNat (kWords + 1) :: mu :: q1 :: ⟨6530⟩ ::
        UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 17) (gasUsed + 64) := by
  have rd1323 := evm_run h with [
    jumpdest,
    swap1,
    pushCanonical 2 .PUSH2 ⟨6500⟩ (by decide),
    dup8,
    pushCanonical 2 .PUSH2 ⟨1323⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6500 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedAddOneExact hkWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1323
  exact rd6500.withIndices (by omega) (by omega)

def q1CopyLengthWord (kWords : Nat) : UInt256 :=
  (UInt256.ofNat (kWords + 1)).shiftLeft ⟨5⟩

def q1CopySourceWord (product : UInt256) (kWords : Nat) : UInt256 :=
  product + (UInt256.ofNat kWords + (⟨0⟩ : UInt256).lnot).shiftLeft ⟨5⟩ + ⟨32⟩

def q1CopyDestinationWord (q1 : UInt256) : UInt256 := q1 + ⟨32⟩

def q1CopiedMemory (mem : ByteArray) (q1 product : UInt256) (kWords : Nat) : ByteArray :=
  mem.write (q1CopySourceWord product kWords).toNat mem
    (q1CopyDestinationWord q1).toNat (q1CopyLengthWord kWords).toNat

def q1CopiedWords (aw : UInt256) (q1 product : UInt256) (kWords : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat
    (max (q1CopyDestinationWord q1).toNat (q1CopySourceWord product kWords).toNat)
    (q1CopyLengthWord kWords).toNat)

def q1LoadedWords (aw : UInt256) (q1 product mu : UInt256) (kWords : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M (q1CopiedWords aw q1 product kWords).toNat mu.toNat 32)

def q1SliceGas (aw : UInt256) (q1 product mu : UInt256) (kWords : Nat) : Nat :=
  71 +
    (Cₘ (q1CopiedWords aw q1 product kWords) - Cₘ aw) +
    GasConstants.Gverylow +
    GasConstants.Gcopy * (((q1CopyLengthWord kWords).toNat + 31) / 32) +
    (Cₘ (q1LoadedWords aw q1 product mu kWords) -
      Cₘ (q1CopiedWords aw q1 product kWords))

/-- Execute the generated PC 6500 trace prefix through the real `MCOPY`, load `mu.length` from
the copied-memory state, and stop at the second standalone multiplication call. -/
theorem q1SliceExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords muWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (hmuInMemory : mu.toNat < (q1CopiedMemory mem q1 product kWords).size)
    (hmuActive : ¬ mu ≥ q1CopiedWords aw q1 product kWords * ⟨32⟩)
    (hmuHeader : (q1CopiedMemory mem q1 product kWords).readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat muWords))
    (hdepth : tail.length + 11 ≤ 1018)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6500⟩
      (UInt256.ofNat (kWords + 1) :: mu :: q1 :: ⟨6530⟩ ::
        UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (q1 :: UInt256.ofNat (kWords + 2) :: mu :: UInt256.ofNat muWords :: ⟨6530⟩ ::
        UInt256.ofNat muWords :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      (q1CopiedMemory mem q1 product kWords)
      (q1LoadedWords aw q1 product mu kWords)
      rdata acc (steps + 24) (gasUsed + q1SliceGas aw q1 product mu kWords) := by
  have rd5016 := evm_run h with [
    jumpdest,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    push0,
    not,
    dup10,
    add,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    dup13,
    add,
    add,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    dup5,
    add,
    mcopyCanonical,
    dup1,
    mloadCanonical,
    swap4,
    dup5,
    swap3,
    pushCanonical 2 .PUSH2 ⟨5016⟩ (by decide),
    jump (by native_decide)
  ]
  have hload := mloadWordValue_of_readWithPadding hmuInMemory hmuActive hmuHeader
  simp only [q1CopiedMemory, q1CopiedWords, q1CopyLengthWord,
    q1CopySourceWord, q1CopyDestinationWord] at hload
  rw [hload] at rd5016
  have normalized := rd5016.withIndices (k' := steps + 24) (by omega)
    (C' := gasUsed + q1SliceGas aw q1 product mu kWords) (by
      simp [q1SliceGas, q1CopiedWords, q1LoadedWords, q1CopyLengthWord,
        q1CopySourceWord, q1CopyDestinationWord]
      omega)
  simpa [q1CopiedMemory, q1CopiedWords, q1LoadedWords, q1CopyLengthWord,
    q1CopySourceWord, q1CopyDestinationWord] using normalized

/-- Compose the checked slice length and the exact generated copy prefix. -/
theorem q1ProductEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords muWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hmuInMemory : mu.toNat < (q1CopiedMemory mem q1 product kWords).size)
    (hmuActive : ¬ mu ≥ q1CopiedWords aw q1 product kWords * ⟨32⟩)
    (hmuHeader : (q1CopiedMemory mem q1 product kWords).readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat muWords))
    (hdepth : tail.length + 11 ≤ 1018)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6490⟩
      (q1 :: mu :: ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (q1 :: UInt256.ofNat (kWords + 2) :: mu :: UInt256.ofNat muWords :: ⟨6530⟩ ::
        UInt256.ofNat muWords :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      (q1CopiedMemory mem q1 product kWords)
      (q1LoadedWords aw q1 product mu kWords)
      rdata acc (steps + 41) (gasUsed + 64 + q1SliceGas aw q1 product mu kWords) := by
  have rd6500 := q1CopyEntryExact hkWord hdepth h
  have rd5016 := q1SliceExact hmuInMemory hmuActive hmuHeader hdepth rd6500
  exact rd5016.withIndices (by omega) (by omega)

def secondProductInitial
    (mem : ByteArray) (aw : UInt256) (fp kWords : Nat) : OuterState :=
  functionInitialState mem aw fp (kWords + 2) (kWords + 2)

def secondProductFinal
    (mem : ByteArray) (aw q1 mu : UInt256) (fp kWords : Nat) : OuterState :=
  functionFinalState mem aw q1 mu fp (kWords + 2) (kWords + 2)

/-- Execute the complete second Barrett product `q1*mu` from the concrete PC 5016 call through
its dynamic return to PC 6530. -/
theorem secondProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (hkBound : 2 * kWords + 4 ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 17 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5016⟩
      (q1 :: UInt256.ofNat (kWords + 2) :: mu :: UInt256.ofNat (kWords + 2) ::
        ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
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
  have rd6530 := functionExact (aCount := kWords + 2) (bCount := kWords + 2) (fp := fp)
    (returnPc := (⟨6530⟩ : UInt256))
    (tail := UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
      UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
    (by omega) (by omega) hfp (by
      rw [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega]
      exact hbound)
    hmemSize hmemLe hgap haw3 haw64 hread hcalldata (by native_decide)
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
  simpa [final, secondProductFinal, functionFinalState, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

/-- Starting at q1's allocation return, perform the real slice and the complete `q1*mu` product.
The conclusion retains the first product pointer for the later Barrett subtraction. -/
theorem q1ProductExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q1 mu n returnPc product : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hkBound : 2 * kWords + 4 ≤ 68)
    (hmuInMemory : mu.toNat < (q1CopiedMemory mem q1 product kWords).size)
    (hmuActive : ¬ mu ≥ q1CopiedWords aw q1 product kWords * ⟨32⟩)
    (hmuHeader : (q1CopiedMemory mem q1 product kWords).readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2)))
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hmemSize : 96 ≤ (q1CopiedMemory mem q1 product kWords).size)
    (hmemLe : (q1CopiedMemory mem q1 product kWords).size ≤ fp)
    (hgap : fp - (q1CopiedMemory mem q1 product kWords).size < USize.size)
    (haw3 : 3 ≤ (q1LoadedWords aw q1 product mu kWords).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥
      q1LoadedWords aw q1 product mu kWords * ⟨32⟩)
    (hread : (q1CopiedMemory mem q1 product kWords).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 17 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6490⟩
      (q1 :: mu :: ⟨6530⟩ :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    let copiedMem := q1CopiedMemory mem q1 product kWords
    let copiedAw := q1LoadedWords aw q1 product mu kWords
    let initial := secondProductInitial copiedMem copiedAw fp kWords
    let final := secondProductFinal copiedMem copiedAw q1 mu fp kWords
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6530⟩
      (UInt256.ofNat fp :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n ::
        UInt256.ofNat kWords :: UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      final.memory final.activeWords rdata acc
      (steps + 157 + rowsSteps q1 mu (UInt256.ofNat fp)
        (kWords + 2) (kWords + 2) initial)
      (gasUsed + 196 + q1SliceGas aw q1 product mu kWords +
        newWordArrayGas copiedAw fp (2 * kWords + 4) +
        rowsGas q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) initial) := by
  have rd5016 := q1ProductEntryExact hkWord hmuInMemory hmuActive hmuHeader
    (by omega) h
  have rd6530 := secondProductExact hkBound hfp hbound hmemSize hmemLe hgap haw3 haw64
    hread hcalldata hdepth rd5016
  let copiedMem := q1CopiedMemory mem q1 product kWords
  let copiedAw := q1LoadedWords aw q1 product mu kWords
  let initial := secondProductInitial copiedMem copiedAw fp kWords
  let final := secondProductFinal copiedMem copiedAw q1 mu fp kWords
  have normalized := rd6530.withIndices
    (k' := steps + 157 + rowsSteps q1 mu (UInt256.ofNat fp)
      (kWords + 2) (kWords + 2) initial) (by
        dsimp only [initial, copiedMem, copiedAw])
    (C' := gasUsed + 196 + q1SliceGas aw q1 product mu kWords +
      newWordArrayGas copiedAw fp (2 * kWords + 4) +
      rowsGas q1 mu (UInt256.ofNat fp) (kWords + 2) (kWords + 2) initial) (by
        dsimp only [initial, copiedMem, copiedAw]
        omega)
  simpa [final, copiedMem, copiedAw, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

/-- Exact successful path through Solidity's checked binary-add helper at PC 1421. -/
theorem checkedAddExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed x y ret : Nat} {tail : List UInt256}
    (hxy : x + y < UInt256.size)
    (hret : (D_J runtimeBytecode 0).contains (UInt256.ofNat ret) = true)
    (hdepth : tail.length ≤ 1020)
    (h : RDx runtimeBytecode ee g s0 ⟨1421⟩
      (UInt256.ofNat x :: UInt256.ofNat y :: UInt256.ofNat ret :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 (UInt256.ofNat ret)
      (UInt256.ofNat (x + y) :: tail) mem aw rdata acc
      (steps + 11) (gasUsed + 43) := by
  have hxWord : x < UInt256.size := by omega
  have hyWord : y < UInt256.size := by omega
  have hadd : UInt256.ofNat x + UInt256.ofNat y = UInt256.ofNat (x + y) := by
    apply u256_inj
    rw [uadd_toNat, UInt256.toNat_ofNat_of_lt hxWord,
      UInt256.toNat_ofNat_of_lt hyWord, UInt256.toNat_ofNat_of_lt hxy,
      Nat.mod_eq_of_lt hxy]
  have hoverflow : UInt256.gt (UInt256.ofNat x)
      (UInt256.ofNat x + UInt256.ofNat y) = ⟨0⟩ := by
    apply ugt_zero
    rw [hadd, UInt256.toNat_ofNat_of_lt hxy,
      UInt256.toNat_ofNat_of_lt hxWord]
    omega
  have rd1432 := GeneratedTraces.trace_1421_body (by omega) h
  have rd1433 := rd1432.jumpiNT (by native_decide) hoverflow
    (by simp only [List.length_cons]; omega)
  rw [hadd] at rd1433
  have rdret := GeneratedTraces.trace_1433_jump
    (by simp only [List.length_cons]; omega) rd1433 (by native_decide) hret
  exact rdret.withIndices (by omega) (by omega)

/-- Compute the concrete `q2Len = (k+2)+(k+2) = 2*k+4` after the second product. -/
theorem q2LengthExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkBound : 2 * kWords + 4 ≤ 68)
    (hdepth : tail.length + 8 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6530⟩
      (q2 :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6536⟩
      (UInt256.ofNat (2 * kWords + 4) :: n :: UInt256.ofNat kWords :: q2 ::
        returnPc :: product :: tail)
      mem aw rdata acc (steps + 15) (gasUsed + 58) := by
  have rd1421 := evm_run h with [
    jumpdest,
    swap5,
    pushCanonical 2 .PUSH2 ⟨1421⟩ (by decide),
    jump (by native_decide)
  ]
  have hsumWord : (kWords + 2) + (kWords + 2) < UInt256.size :=
    lt_trans (by omega : (kWords + 2) + (kWords + 2) < 2 ^ 64) (by decide)
  have rd6536 := checkedAddExact hsumWord (by native_decide)
    (by simp only [List.length_cons]; omega) rd1421
  have normalized := rd6536.withIndices (k' := steps + 15) (by omega)
    (C' := gasUsed + 58) (by omega)
  simpa [show (kWords + 2) + (kWords + 2) = 2 * kWords + 4 by omega] using normalized

/-- Compute the checked q3 shift offset `k+1`. -/
theorem q3OffsetExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 6 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6536⟩
      (UInt256.ofNat (2 * kWords + 4) :: n :: UInt256.ofNat kWords :: q2 ::
        returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6546⟩
      (UInt256.ofNat (kWords + 1) :: q2 :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (2 * kWords + 4) :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 17) (gasUsed + 64) := by
  have rd1323 := evm_run h with [
    jumpdest,
    swap3,
    pushCanonical 2 .PUSH2 ⟨6546⟩ (by decide),
    dup4,
    pushCanonical 2 .PUSH2 ⟨1323⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6546 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedAddOneExact hkWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1323
  exact rd6546.withIndices (by omega) (by omega)

/-- Prove and take the deployed long-q2 branch. For valid positive `k`, `2*k+4 > k+1`. -/
theorem q3LongBranchExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords + 4 ≤ 68)
    (hdepth : tail.length + 7 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6546⟩
      (UInt256.ofNat (kWords + 1) :: q2 :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (2 * kWords + 4) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6554⟩
      (q2 :: n :: UInt256.ofNat kWords :: UInt256.ofNat (2 * kWords + 4) ::
        returnPc :: product :: tail)
      mem aw rdata acc (steps + 6) (gasUsed + 23) := by
  have hlargeWord : 2 * kWords + 4 < UInt256.size :=
    lt_trans (by omega : 2 * kWords + 4 < 2 ^ 64) (by decide)
  have hoffWord : kWords + 1 < UInt256.size := by omega
  have hgt : UInt256.gt (UInt256.ofNat (2 * kWords + 4))
      (UInt256.ofNat (kWords + 1)) = ⟨1⟩ := by
    apply ugt_one
    rw [UInt256.toNat_ofNat_of_lt hlargeWord, UInt256.toNat_ofNat_of_lt hoffWord]
    omega
  have hcondition : (UInt256.gt (UInt256.ofNat (2 * kWords + 4))
      (UInt256.ofNat (kWords + 1))).isZero = ⟨0⟩ := by
    rw [hgt]
    native_decide
  have rd6554 := GeneratedTraces.trace_6546_notTaken
    (by simp only [List.length_cons]; omega) h (by native_decide) hcondition
  exact rd6554.withIndices (by omega) (by omega)

/-- On the long branch, execute checked `(2*k+4) - (k+1) = k+3`. -/
theorem q3LengthExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkWord : 2 * kWords + 4 < UInt256.size)
    (hdepth : tail.length + 6 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6554⟩
      (q2 :: n :: UInt256.ofNat kWords :: UInt256.ofNat (2 * kWords + 4) ::
        returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6571⟩
      (UInt256.ofNat (kWords + 3) :: q2 :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (2 * kWords + 4) :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 31) (gasUsed + 121) := by
  have hoffWord : kWords + 1 < UInt256.size := by omega
  have rd1323 := evm_run h with [
    pushCanonical 2 .PUSH2 ⟨6571⟩ (by decide),
    pushCanonical 2 .PUSH2 ⟨6565⟩ (by decide),
    dup5,
    pushCanonical 2 .PUSH2 ⟨1323⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6565 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedAddOneExact hoffWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1323
  have rd1103 := evm_run rd6565 with [
    jumpdest,
    dup6,
    pushCanonical 2 .PUSH2 ⟨1103⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6571 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedSubExact
    (x := 2 * kWords + 4) (y := kWords + 1) (ret := 6571)
    (by omega) hkWord (by native_decide)
    (by simp only [List.length_cons]; omega) rd1103
  have normalized := rd6571.withIndices (k' := steps + 31) (by omega)
    (C' := gasUsed + 121) (by omega)
  simpa [show 2 * kWords + 4 - (kWords + 1) = kWords + 3 by omega] using normalized

/-- Compose q2 length, q3 offset/branch/subtraction, and reach q3's concrete allocator. -/
theorem q3AllocationEntryExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords + 4 ≤ 68)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6530⟩
      (q2 :: UInt256.ofNat (kWords + 2) :: ⟨6536⟩ :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (kWords + 2) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
      (UInt256.ofNat (kWords + 3) :: ⟨6582⟩ :: q2 :: UInt256.ofNat (kWords + 3) ::
        n :: UInt256.ofNat kWords :: UInt256.ofNat (2 * kWords + 4) ::
        returnPc :: product :: tail)
      mem aw rdata acc (steps + 76) (gasUsed + 288) := by
  have hkWord : kWords + 1 < UInt256.size :=
    lt_trans (by omega : kWords + 1 < 2 ^ 64) (by decide)
  have hq2Word : 2 * kWords + 4 < UInt256.size :=
    lt_trans (by omega : 2 * kWords + 4 < 2 ^ 64) (by decide)
  have rd6536 := q2LengthExact hkBound (by omega) h
  have rd6546 := q3OffsetExact hkWord (by omega) rd6536
  have rd6554 := q3LongBranchExact hkPos hkBound (by omega) rd6546
  have rd6571 := q3LengthExact hq2Word (by omega) rd6554
  have rd1487 := evm_run rd6571 with [
    jumpdest,
    swap1,
    jumpdest,
    pushCanonical 2 .PUSH2 ⟨6582⟩ (by decide),
    dup3,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)
  ]
  exact rd1487.withIndices (by omega) (by omega)

def q3AllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize (kWords + 3)))
    fp (kWords + 3)

def q3AllocatedWords (aw : UInt256) (fp kWords : Nat) : UInt256 :=
  newWordArrayWords aw fp (kWords + 3)

/-- Execute q3's concrete `k+3`-limb allocation and return to its copy continuation. -/
theorem q3AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q2 n returnPc product : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords + 4 ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
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
        UInt256.ofNat kWords :: UInt256.ofNat (2 * kWords + 4) ::
        returnPc :: product :: tail)
      (q3AllocatedMemory mem fp kWords) (q3AllocatedWords aw fp kWords)
      rdata acc (steps + 154) (gasUsed + 288 + newWordArrayGas aw fp (kWords + 3)) := by
  have rd1487 := q3AllocationEntryExact hkPos hkBound hdepth h
  have rd6582 := newWordArrayExact68 (by omega) hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd6582.withIndices (k' := steps + 154) (by omega)
    (C' := gasUsed + 288 + newWordArrayGas aw fp (kWords + 3)) (by omega)
  simpa [q3AllocatedMemory, q3AllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

/-- Recompute and validate q3's concrete copy length, including both deployed comparisons. -/
theorem q3CopySetupExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 q2 n returnPc product : UInt256}
    (hkPos : 0 < kWords) (hkBound : 2 * kWords + 4 ≤ 68)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6582⟩
      (q3 :: q2 :: UInt256.ofNat (kWords + 3) :: n :: UInt256.ofNat kWords ::
        UInt256.ofNat (2 * kWords + 4) :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6626⟩
      (UInt256.ofNat (kWords + 3) :: q2 :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc (steps + 61) (gasUsed + 234) := by
  have hoffWord : kWords + 1 < UInt256.size :=
    lt_trans (by omega : kWords + 1 < 2 ^ 64) (by decide)
  have hq2Word : 2 * kWords + 4 < UInt256.size :=
    lt_trans (by omega : 2 * kWords + 4 < 2 ^ 64) (by decide)
  have hq3Word : kWords + 3 < UInt256.size := by omega
  have hgt : UInt256.gt (UInt256.ofNat (2 * kWords + 4))
      (UInt256.ofNat (kWords + 1)) = ⟨1⟩ := by
    apply ugt_one
    rw [UInt256.toNat_ofNat_of_lt hq2Word, UInt256.toNat_ofNat_of_lt hoffWord]
    omega
  have hlong : (UInt256.gt (UInt256.ofNat (2 * kWords + 4))
      (UInt256.ofNat (kWords + 1))).isZero = ⟨0⟩ := by
    rw [hgt]
    native_decide
  have rd1323a := evm_run h with [
    jumpdest,
    swap5,
    pushCanonical 2 .PUSH2 ⟨6592⟩ (by decide),
    dup6,
    pushCanonical 2 .PUSH2 ⟨1323⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6592 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedAddOneExact hoffWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1323a
  have rd6600 := GeneratedTraces.trace_6592_notTaken
    (by simp only [List.length_cons]; omega) rd6592 (by native_decide) hlong
  have rd1323b := evm_run rd6600 with [
    pushCanonical 2 .PUSH2 ⟨6618⟩ (by decide),
    swap1,
    pushCanonical 2 .PUSH2 ⟨6612⟩ (by decide),
    dup7,
    pushCanonical 2 .PUSH2 ⟨1323⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6612 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedAddOneExact hoffWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1323b
  have rd1103 := evm_run rd6612 with [
    jumpdest,
    swap1,
    pushCanonical 2 .PUSH2 ⟨1103⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6618 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedSubExact
    (x := 2 * kWords + 4) (y := kWords + 1) (ret := 6618)
    (by omega) hq2Word (by native_decide)
    (by simp only [List.length_cons]; omega) rd1103
  have hsub : 2 * kWords + 4 - (kWords + 1) = kWords + 3 := by omega
  rw [hsub] at rd6618
  have hcap : UInt256.gt (UInt256.ofNat (kWords + 3))
      (UInt256.ofNat (kWords + 3)) = ⟨0⟩ := ugt_zero (by omega)
  have rd6626 := GeneratedTraces.trace_6618_notTaken
    (by simp only [List.length_cons]; omega) rd6618 (by native_decide) hcap
  have normalized := rd6626.withIndices (k' := steps + 61) (by omega)
    (C' := gasUsed + 234) (by omega)
  simpa using normalized

def q3CopyLengthWord (kWords : Nat) : UInt256 :=
  (UInt256.ofNat (kWords + 3)).shiftLeft ⟨5⟩

def q3CopySourceWord (q2 : UInt256) (kWords : Nat) : UInt256 :=
  (UInt256.ofNat kWords + ⟨1⟩).shiftLeft ⟨5⟩ + q2 + ⟨32⟩

def q3CopyDestinationWord (q3 : UInt256) : UInt256 := q3 + ⟨32⟩

def q3CopiedMemory (mem : ByteArray) (q3 q2 : UInt256) (kWords : Nat) : ByteArray :=
  mem.write (q3CopySourceWord q2 kWords).toNat mem
    (q3CopyDestinationWord q3).toNat (q3CopyLengthWord kWords).toNat

def q3CopiedWords (aw : UInt256) (q3 q2 : UInt256) (kWords : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat
    (max (q3CopyDestinationWord q3).toNat (q3CopySourceWord q2 kWords).toNat)
    (q3CopyLengthWord kWords).toNat)

def q3CopyGas (aw : UInt256) (q3 q2 : UInt256) (kWords : Nat) : Nat :=
  106 + (Cₘ (q3CopiedWords aw q3 q2 kWords) - Cₘ aw) +
    GasConstants.Gverylow +
    GasConstants.Gcopy * (((q3CopyLengthWord kWords).toNat + 31) / 32)

/-- Execute q3's actual `MCOPY` and the checked `rLen=k+1` computation. -/
theorem q3CopyAndRLenExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed kWords : Nat} {tail : List UInt256}
    {q3 q2 n returnPc product : UInt256}
    (hkWord : kWords + 1 < UInt256.size)
    (hdepth : tail.length + 9 ≤ 1016)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6626⟩
      (UInt256.ofNat (kWords + 3) :: q2 :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6656⟩
      (UInt256.ofNat (kWords + 1) :: UInt256.ofNat (kWords + 3) :: n ::
        UInt256.ofNat kWords :: q3 :: returnPc :: product :: tail)
      (q3CopiedMemory mem q3 q2 kWords) (q3CopiedWords aw q3 q2 kWords)
      rdata acc (steps + 32) (gasUsed + q3CopyGas aw q3 q2 kWords) := by
  have rd1323 := evm_run h with [
    jumpdest,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    swap1,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    swap2,
    pushCanonical 1 .PUSH1 ⟨1⟩ (by decide),
    dup7,
    add,
    pushCanonical 1 .PUSH1 ⟨5⟩ (by decide),
    shl,
    add,
    add,
    pushCanonical 1 .PUSH1 ⟨32⟩ (by decide),
    dup7,
    add,
    mcopyCanonical,
    pushCanonical 2 .PUSH2 ⟨6656⟩ (by decide),
    dup4,
    pushCanonical 2 .PUSH2 ⟨1323⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6656 := Modexp.MultiLimbSchoolbookKnuthSetup.checkedAddOneExact hkWord
    (by native_decide) (by simp only [List.length_cons]; omega) rd1323
  have normalized := rd6656.withIndices (k' := steps + 32) (by omega)
    (C' := gasUsed + q3CopyGas aw q3 q2 kWords) (by
      simp [q3CopyGas, q3CopiedWords, q3CopyLengthWord,
        q3CopySourceWord, q3CopyDestinationWord]
      omega)
  simpa [q3CopiedMemory, q3CopiedWords, q3CopyLengthWord,
    q3CopySourceWord, q3CopyDestinationWord] using normalized

def r2AllocatedMemory (mem : ByteArray) (fp kWords : Nat) : ByteArray :=
  storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize (kWords + 1)))
    fp (kWords + 1)

def r2AllocatedWords (aw : UInt256) (fp kWords : Nat) : UInt256 :=
  newWordArrayWords aw fp (kWords + 1)

/-- Allocate the concrete zeroed `k+1`-limb r2 array and enter its truncated multiply. -/
theorem r2AllocationExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fp kWords : Nat} {tail : List UInt256}
    {q3 n returnPc product : UInt256}
    (hkBound : kWords + 1 ≤ 68)
    (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
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
  have rd1487 := evm_run h with [
    jumpdest,
    swap1,
    pushCanonical 2 .PUSH2 ⟨6666⟩ (by decide),
    dup3,
    pushCanonical 2 .PUSH2 ⟨1487⟩ (by decide),
    jump (by native_decide)
  ]
  have rd6666 := newWordArrayExact68 hkBound hfp hbound hmemSize hmemLe hgap
    haw3 haw64 hread hcalldata (by simp only [List.length_cons]; omega)
    (by native_decide) rd1487
  have normalized := rd6666.withIndices (k' := steps + 84) (by omega)
    (C' := gasUsed + 21 + newWordArrayGas aw fp (kWords + 1)) (by omega)
  simpa [r2AllocatedMemory, r2AllocatedWords, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using normalized

end Modexp.MultiLimbBarrettMul
