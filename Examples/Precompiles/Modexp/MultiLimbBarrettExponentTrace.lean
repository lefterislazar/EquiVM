import Examples.Precompiles.Modexp.MultiLimbBarrettReductionContract
import Examples.Precompiles.Modexp.MultiLimbExponentTrace

/-!
# Exact Barrett exponent-loop call boundaries

This module connects the deployed Barrett exponent loop to the complete `_barrettMulMod`
contract.  The first boundary is the square entry: it resets Solidity's free-memory pointer and
enters PC 6446 with `r` supplied as both multiplication operands.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbBarrettExponentTrace

open Modexp.MultiLimbMontgomeryCIOSSemantic
open Modexp.MultiLimbBarrettReduction
open Modexp.MultiLimbBarrettCorrection
open Modexp.MultiLimbBarrettMul
open Modexp.MultiLimbBarrettTruncatedMul
open Modexp.MultiLimbBarrettSubtract
open Modexp.MultiLimbSchoolbookMulTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def barrettResetMemory (mem : ByteArray) (freeMemBase : UInt256) : ByteArray :=
  freeMemBase.toByteArray.write 0 mem 64 32

def barrettResetAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat 64 32)

def barrettSquareEntryGas (aw : UInt256) : Nat :=
  62 + (Cₘ (barrettResetAw aw) - Cₘ aw)

def barrettMultiplyEntryGas (aw : UInt256) : Nat :=
  39 + (Cₘ (barrettResetAw aw) - Cₘ aw)

def barrettCallResultFp (fp kWords : Nat) : Nat :=
  fp + wordArrayAllocationSize (2 * kWords) +
    wordArrayAllocationSize (kWords + 2) +
    wordArrayAllocationSize (2 * kWords + 4) +
    wordArrayAllocationSize (kWords + 3) +
    wordArrayAllocationSize (kWords + 1)

def selectBarrettCall (fuel : Nat) (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords : Nat) : Option BarrettCorrectionSelection :=
  let firstFinal := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  selectBarrettFromTruncated fuel
    (r2AllocatedMemory (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords)
      r2Fp kWords)
    (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords)
      r2Fp kWords)
    q3 n (UInt256.ofNat r2Fp) (UInt256.ofNat fp)
    (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords

/-- All allocation, multiplication, slicing, and truncation layers are total computations; only
the bounded correction comparison consumes selector fuel. -/
theorem selectBarrettCall_exists
    {fuel fp kWords : Nat} {mem : ByteArray} {aw a b n mu : UInt256}
    (hkPos : 0 < kWords) (hfuel : kWords ≤ fuel) :
    ∃ selected, selectBarrettCall fuel mem aw a b n mu fp kWords = some selected := by
  unfold selectBarrettCall
  exact selectBarrettFromTruncated_exists hkPos hfuel

/-- Exact reduction steps from PC 6446 up to, but not including, its final dynamic return. -/
def barrettReductionSteps (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords : Nat) (selected : BarrettCorrectionSelection) : Nat :=
  let firstInitial := firstProductInitial mem aw fp kWords
  let firstFinal := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Initial := secondProductInitial copiedMem copiedAw secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let q3Mem := q3AllocatedMemory
    (secondProductFinal copiedMem copiedAw q1 mu secondFp kWords).memory q3Fp kWords
  let q3Aw := q3AllocatedWords
    (secondProductFinal copiedMem copiedAw q1 mu secondFp kWords).activeWords q3Fp kWords
  let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let initial : TruncatedOuterState := {
    i := 0
    memory := r2AllocatedMemory q3CopiedMem r2Fp kWords
    activeWords := r2AllocatedWords q3CopiedAw r2Fp kWords }
  837 + rowsSteps a b (UInt256.ofNat fp) kWords kWords firstInitial +
    rowsSteps q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
    truncatedRowsSteps q3 n (UInt256.ofNat r2Fp) kWords (kWords + 1) initial +
    44 * (kWords + 1) + selected.steps

/-- Exact reduction gas from PC 6446 up to, but not including, its final dynamic return. -/
def barrettReductionGas (mem : ByteArray) (aw a b n mu : UInt256)
    (fp kWords : Nat) (selected : BarrettCorrectionSelection) : Nat :=
  let firstInitial := firstProductInitial mem aw fp kWords
  let firstFinal := firstProductFinal mem aw a b fp kWords
  let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
  let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
  let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
  let q1 := UInt256.ofNat q1Fp
  let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
  let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
  let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
  let q2Initial := secondProductInitial copiedMem copiedAw secondFp kWords
  let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
  let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
  let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
  let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
  let q3 := UInt256.ofNat q3Fp
  let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
  let q3CopiedMem := q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords
  let q3CopiedAw := q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords
  let allocatedMemory := r2AllocatedMemory q3CopiedMem r2Fp kWords
  let allocatedWords := r2AllocatedWords q3CopiedAw r2Fp kWords
  let r2 := UInt256.ofNat r2Fp
  let resultFp := r2Fp + wordArrayAllocationSize (kWords + 1)
  let initial : TruncatedOuterState :=
    { i := 0, memory := allocatedMemory, activeWords := allocatedWords }
  let final := truncatedRowsIterate q3 n r2 kWords (kWords + 1) initial
  let resultMem := resultAllocatedMemory final.memory resultFp kWords
  let resultAw := resultAllocatedWords final.activeWords resultFp kWords
  let subtractionInitial := subtractionInitialState resultMem resultAw
  1133 + newWordArrayGas aw fp (2 * kWords) +
    rowsGas a b (UInt256.ofNat fp) kWords kWords firstInitial +
    newWordArrayGas firstFinal.activeWords q1Fp (kWords + 2) +
    q1SliceGas q1Aw q1 (UInt256.ofNat fp) mu kWords +
    newWordArrayGas copiedAw secondFp (2 * kWords + 4) +
    rowsGas q1 mu (UInt256.ofNat secondFp) (kWords + 2) (kWords + 2) q2Initial +
    newWordArrayGas q2Final.activeWords q3Fp (kWords + 3) +
    q3CopyGas q3Aw q3 (UInt256.ofNat secondFp) kWords +
    newWordArrayGas q3CopiedAw r2Fp (kWords + 1) +
    truncatedRowsGas q3 n r2 kWords (kWords + 1) initial +
    newWordArrayGas final.activeWords resultFp kWords +
    subtractionThroughExitGas (UInt256.ofNat fp) r2 kWords subtractionInitial +
    selected.gas

private theorem barrettSquareEntryDecodes :
    [decode runtimeBytecode ⟨3379⟩, decode runtimeBytecode ⟨3380⟩,
      decode runtimeBytecode ⟨3381⟩, decode runtimeBytecode ⟨3382⟩,
      decode runtimeBytecode ⟨3385⟩, decode runtimeBytecode ⟨3386⟩,
      decode runtimeBytecode ⟨3387⟩, decode runtimeBytecode ⟨3388⟩,
      decode runtimeBytecode ⟨3391⟩, decode runtimeBytecode ⟨3392⟩,
      decode runtimeBytecode ⟨3393⟩, decode runtimeBytecode ⟨3394⟩,
      decode runtimeBytecode ⟨3395⟩, decode runtimeBytecode ⟨3396⟩,
      decode runtimeBytecode ⟨3398⟩, decode runtimeBytecode ⟨3399⟩,
      decode runtimeBytecode ⟨3400⟩, decode runtimeBytecode ⟨3401⟩,
      decode runtimeBytecode ⟨3402⟩, decode runtimeBytecode ⟨3405⟩] =
    [some (.JUMPDEST, .none), some (.DUP3, .none), some (.DUP3, .none),
      some (.Push .PUSH2, some (⟨3406⟩, 2)), some (.DUP3, .none),
      some (.PUSH0, .none), some (.NOT, .none),
      some (.Push .PUSH2, some (⟨3411⟩, 2)), some (.SWAP6, .none),
      some (.ADD, .none), some (.SWAP10, .none), some (.DUP11, .none),
      some (.SWAP10, .none), some (.Push .PUSH1, some (⟨64⟩, 1)),
      some (.MSTORE, .none), some (.DUP9, .none), some (.DUP5, .none),
      some (.DUP1, .none), some (.Push .PUSH2, some (⟨6446⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_6446_barrettExponent :
    (D_J runtimeBytecode 0).contains ⟨6446⟩ = true := by
  native_decide

/-- One positive-bit-loop iteration resets temporary memory and enters the concrete Barrett
square.  The remaining stack is the exact frame consumed later by the copy-back and bit guard. -/
theorem barrettSquareEntry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {bit r words n freeMemBase mu : UInt256}
    (hdepth : tail.length + 6 ≤ 1006)
    (h : RDx runtimeBytecode ee g s0 ⟨3379⟩
      (bit :: r :: words :: n :: freeMemBase :: mu :: tail)
      mem aw rdata acc steps gasUsed) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode ee g s0 ⟨6446⟩
      (r :: r :: n :: mu :: words :: ⟨3406⟩ ::
        r :: words :: ⟨3411⟩ :: r :: words :: n :: previousBit :: previousBit :: tail)
      (barrettResetMemory mem freeMemBase) (barrettResetAw aw)
      rdata acc (steps + 20) (gasUsed + barrettSquareEntryGas aw) := by
  have hd := barrettSquareEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
      h15, h16, h17, h18, h19⟩
  have rd := evm_run h with [known jumpdest h0, known dup3 h1, known dup3 h2,
    known push2 h3 ⟨3406⟩, known dup3 h4, known push0 h5, known not h6,
    known push2 h7 ⟨3411⟩, known swap6 h8, known add h9, known swap10 h10,
    known dup11 h11, known swap10 h12, known push1 h13 ⟨64⟩]
  have rdStore := RDx.mstore (Cₘ (barrettResetAw aw) - Cₘ aw)
    (barrettResetMemory mem freeMemBase) (barrettResetAw aw) rd h14
    (by
      intro s hsaw hstk
      simp [barrettResetAw, memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
        show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [barrettResetMemory, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [barrettResetAw, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp only [List.length_cons]; omega)
  have rd6446 := evm_run rdStore with [known dup9 h15, known dup5 h16,
    known dup1 h17, known push2 h18 ⟨6446⟩,
    known jump h19 jumpDest_6446_barrettExponent]
  have normalized := rd6446.withIndices (k' := steps + 20) (by omega)
    (C' := gasUsed + barrettSquareEntryGas aw) (by
      unfold barrettSquareEntryGas
      omega)
  simpa [u256_add_comm] using normalized

private theorem barrettMultiplyEntryDecodes :
    [decode runtimeBytecode ⟨3448⟩, decode runtimeBytecode ⟨3449⟩,
      decode runtimeBytecode ⟨3452⟩, decode runtimeBytecode ⟨3453⟩,
      decode runtimeBytecode ⟨3456⟩, decode runtimeBytecode ⟨3457⟩,
      decode runtimeBytecode ⟨3458⟩, decode runtimeBytecode ⟨3459⟩,
      decode runtimeBytecode ⟨3461⟩, decode runtimeBytecode ⟨3462⟩,
      decode runtimeBytecode ⟨3463⟩, decode runtimeBytecode ⟨3466⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨3467⟩, 2)),
      some (.SWAP6, .none), some (.Push .PUSH2, some (⟨3406⟩, 2)),
      some (.SWAP4, .none), some (.DUP7, .none), some (.SWAP4, .none),
      some (.Push .PUSH1, some (⟨64⟩, 1)), some (.MSTORE, .none),
      some (.DUP6, .none), some (.Push .PUSH2, some (⟨6446⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

/-- The set-bit branch resets temporary memory and enters the concrete Barrett multiplication
with the persistent accumulator and fixed base as its two operands. -/
theorem barrettMultiplyEntry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {mu freeMemBase a r words n : UInt256}
    (hdepth : tail.length + 6 ≤ 1011)
    (h : RDx runtimeBytecode ee g s0 ⟨3448⟩
      (mu :: freeMemBase :: a :: r :: words :: n :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨6446⟩
      (r :: a :: n :: mu :: words :: ⟨3406⟩ :: r :: words :: ⟨3467⟩ :: tail)
      (barrettResetMemory mem freeMemBase) (barrettResetAw aw)
      rdata acc (steps + 12) (gasUsed + barrettMultiplyEntryGas aw) := by
  have hd := barrettMultiplyEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  have rd := evm_run h with [known jumpdest h0, known push2 h1 ⟨3467⟩,
    known swap6 h2, known push2 h3 ⟨3406⟩, known swap4 h4, known dup7 h5,
    known swap4 h6, known push1 h7 ⟨64⟩]
  have rdStore := RDx.mstore (Cₘ (barrettResetAw aw) - Cₘ aw)
    (barrettResetMemory mem freeMemBase) (barrettResetAw aw) rd h8
    (by
      intro s hsaw hstk
      simp [barrettResetAw, memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
        show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [barrettResetMemory, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [barrettResetAw, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp only [List.length_cons]; omega)
  have rd6446 := evm_run rdStore with [known dup6 h9, known push2 h10 ⟨6446⟩,
    known jump h11 jumpDest_6446_barrettExponent]
  have normalized := rd6446.withIndices (k' := steps + 12) (by omega)
    (C' := gasUsed + barrettMultiplyEntryGas aw) (by
      unfold barrettMultiplyEntryGas
      omega)
  simpa using normalized

/-- PC 3406 is shared with the Montgomery loop: it copies a returned Barrett result into the
persistent accumulator and resumes at the supplied deployed continuation. -/
theorem barrettCopyReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {resultBase r words resumePc : UInt256}
    (hdepth : tail.length + 4 ≤ 1021)
    (hresume : (D_J runtimeBytecode 0).contains resumePc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3406⟩
      (resultBase :: r :: words :: resumePc :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 resumePc tail
      (Modexp.MultiLimbExponentTrace.exponentCopyMemory mem resultBase r words)
      (Modexp.MultiLimbExponentTrace.exponentCopyAw aw resultBase r words)
      rdata acc (steps + 16)
      (gasUsed + Modexp.MultiLimbExponentTrace.exponentCopyGas aw resultBase r words) := by
  exact Modexp.MultiLimbExponentTrace.exponentCopyReturn hdepth hresume h

/-- Execute `_barrettMulMod`'s final dynamic return.  The complete reduction theorem stops at
this instruction so callers can expose and choose the deployed return destination. -/
theorem barrettDynamicReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {returnPc result : UInt256}
    (hdepth : tail.length + 2 ≤ 1024)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨6737⟩
      (returnPc :: result :: tail) mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 returnPc (result :: tail)
      mem aw rdata acc (steps + 1) (gasUsed + 8) := by
  have rd := h.jump (by native_decide) hreturn (by simp only [List.length_cons]; omega)
  simpa using rd

/-- Execute one already-prepared Barrett call, its exposed correction path, dynamic return, and
copy-back into a persistent limb array.  The result and resume pointers remain caller-selected. -/
theorem selectedBarrettCallAndCopyExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed fuel fp kWords : Nat} {tail : List UInt256}
    {a b n mu target resumePc : UInt256}
    (selected : BarrettCorrectionSelection)
    (hkPos : 0 < kWords) (hk : kWords ≤ 32)
    (hcovered : MemoryCovered mem aw)
    (hawFit : aw.toNat * 32 < UInt256.size)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (haEnd : a.toNat + 32 * (kWords + 1) ≤ fp)
    (hbEnd : b.toNat + 32 * (kWords + 1) ≤ fp)
    (hmuBase : 96 ≤ mu.toNat)
    (hmuEnd : mu.toNat + 32 * (kWords + 3) ≤ fp)
    (hmuHeader : mem.readWithPadding mu.toNat 32 =
      UInt256.toByteArray (UInt256.ofNat (kWords + 2)))
    (hfirstBound : fp + wordArrayAllocationSize (2 * kWords) < 2 ^ 64)
    (hq1Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) < 2 ^ 64)
    (hsecondBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) < 2 ^ 64)
    (hq3Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) < 2 ^ 64)
    (hr2Bound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) < 2 ^ 64)
    (hresultBound : fp + wordArrayAllocationSize (2 * kWords) +
      wordArrayAllocationSize (kWords + 2) +
      wordArrayAllocationSize (2 * kWords + 4) +
      wordArrayAllocationSize (kWords + 3) +
      wordArrayAllocationSize (kWords + 1) + wordArrayAllocationSize kWords < 2 ^ 64)
    (hnFit : n.toNat + 32 * (kWords + 2) < UInt256.size)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hdepth : tail.length + 20 ≤ 1016)
    (hresume : (D_J runtimeBytecode 0).contains resumePc = true)
    (hselect : selectBarrettCall fuel mem aw a b n mu fp kWords = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6446⟩
      (a :: b :: n :: mu :: UInt256.ofNat kWords :: ⟨3406⟩ ::
        target :: UInt256.ofNat kWords :: resumePc :: tail)
      mem aw rdata acc steps gasUsed) :
    let resultFp := barrettCallResultFp fp kWords
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) resumePc tail
      (Modexp.MultiLimbExponentTrace.exponentCopyMemory selected.memory
        (UInt256.ofNat resultFp) target (UInt256.ofNat kWords))
      (Modexp.MultiLimbExponentTrace.exponentCopyAw selected.activeWords
        (UInt256.ofNat resultFp) target (UInt256.ofNat kWords))
      rdata acc
      (steps + barrettReductionSteps mem aw a b n mu fp kWords selected + 17)
      (gasUsed + barrettReductionGas mem aw a b n mu fp kWords selected + 8 +
        Modexp.MultiLimbExponentTrace.exponentCopyGas selected.activeWords
          (UInt256.ofNat resultFp) target (UInt256.ofNat kWords)) := by
  let resultFp := barrettCallResultFp fp kWords
  let callTail := target :: UInt256.ofNat kWords :: resumePc :: tail
  have hselect' :
      let firstFinal := firstProductFinal mem aw a b fp kWords
      let q1Fp := fp + wordArrayAllocationSize (2 * kWords)
      let q1Mem := q1AllocatedMemory firstFinal.memory q1Fp kWords
      let q1Aw := q1AllocatedWords firstFinal.activeWords q1Fp kWords
      let q1 := UInt256.ofNat q1Fp
      let secondFp := q1Fp + wordArrayAllocationSize (kWords + 2)
      let copiedMem := q1CopiedMemory q1Mem q1 (UInt256.ofNat fp) kWords
      let copiedAw := q1LoadedWords q1Aw q1 (UInt256.ofNat fp) mu kWords
      let q2Final := secondProductFinal copiedMem copiedAw q1 mu secondFp kWords
      let q3Fp := secondFp + wordArrayAllocationSize (2 * kWords + 4)
      let q3Mem := q3AllocatedMemory q2Final.memory q3Fp kWords
      let q3Aw := q3AllocatedWords q2Final.activeWords q3Fp kWords
      let q3 := UInt256.ofNat q3Fp
      let r2Fp := q3Fp + wordArrayAllocationSize (kWords + 3)
      selectBarrettFromTruncated fuel
        (r2AllocatedMemory (q3CopiedMemory q3Mem q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        (r2AllocatedWords (q3CopiedWords q3Aw q3 (UInt256.ofNat secondFp) kWords)
          r2Fp kWords)
        q3 n (UInt256.ofNat r2Fp) (UInt256.ofNat fp)
        (r2Fp + wordArrayAllocationSize (kWords + 1)) kWords = some selected := by
    simpa only [selectBarrettCall] using hselect
  have rd6737 := selectedBarrettFromFirstProductExact (tail := callTail) selected hkPos hk
    hcovered hawFit hmemSize hmemLe hgap haw3 haw64 hread haEnd hbEnd hmuBase hmuEnd
    hmuHeader hfirstBound hq1Bound hsecondBound hq3Bound hr2Bound hresultBound hnFit
    hcalldata (by dsimp only [callTail]; simp only [List.length_cons]; omega) hselect'
    (by simpa only [callTail] using h)
  have rd6737' : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6737⟩
      (⟨3406⟩ :: UInt256.ofNat resultFp :: callTail)
      selected.memory selected.activeWords rdata acc
      (steps + barrettReductionSteps mem aw a b n mu fp kWords selected)
      (gasUsed + barrettReductionGas mem aw a b n mu fp kWords selected) := by
    simpa only [resultFp, callTail, barrettCallResultFp, barrettReductionSteps,
      barrettReductionGas, Nat.add_assoc] using rd6737
  have rd3406 := barrettDynamicReturn (tail := callTail) (returnPc := ⟨3406⟩)
    (result := UInt256.ofNat resultFp)
    (by dsimp only [callTail]; simp only [List.length_cons]; omega)
    (by native_decide) rd6737'
  have rdResume := barrettCopyReturn (tail := tail) (resultBase := UInt256.ofNat resultFp)
    (r := target) (words := UInt256.ofNat kWords) (resumePc := resumePc)
    (by omega) hresume (by simpa only [callTail] using rd3406)
  simpa only [resultFp, Nat.add_assoc] using rdResume

/-! ## Exact Barrett bit-loop frame -/

/-- The optimizer-retained frame below the source-level Barrett bit-loop locals. -/
def barrettBitFrame
    (r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  r :: words :: n :: freeMemBase :: mu :: byte :: aux0 :: aux1 :: aux2 ::
    mu :: freeMemBase :: a :: words :: aux3 :: n :: r :: tail

def barrettSquareStack
    (bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  bit :: barrettBitFrame r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 tail

def barrettBitGuardStack
    (bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  ⟨3379⟩ :: bit ::
    barrettSquareStack bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 tail

/-- A positive bit counter takes the one-instruction guard edge to the next Barrett square. -/
theorem barrettBitGuardTaken
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 : UInt256}
    (hdepth : tail.length + 18 ≤ 1024)
    (hbit : bit ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3364⟩
      (barrettBitGuardStack bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3379⟩
      (barrettSquareStack bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 tail)
      mem aw rdata acc (steps + 1) (gasUsed + 10) := by
  have rd := h.jumpiT (by native_decide) hbit (by native_decide) (by
    simp [barrettBitGuardStack, barrettSquareStack, barrettBitFrame] at hdepth ⊢
    omega)
  simpa [barrettBitGuardStack, barrettSquareStack, barrettBitFrame] using rd

/-- An unset exponent bit skips multiplication and restores the decremented guard frame. -/
theorem barrettUnsetBitToGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {r words n bit byte aux0 aux1 aux2 mu freeMemBase a aux3 : UInt256}
    (hdepth : tail.length + 16 ≤ 1018)
    (hunset : ((⟨1⟩ : UInt256).land ((byte.land ⟨255⟩).shiftRight bit)).eq ⟨1⟩ = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3411⟩
      (r :: words :: n :: bit :: bit :: byte :: aux0 :: aux1 :: aux2 :: mu ::
        freeMemBase :: a :: words :: aux3 :: n :: r :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3364⟩
      (barrettBitGuardStack bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 tail)
      mem aw rdata acc (steps + 33) (gasUsed + 99) := by
  have rd3429 := GeneratedTraces.trace_3411_body (by
    simp only [List.length_cons]
    omega) h
  have rd3430 := rd3429.jumpiNT (by native_decide) hunset (by
    simp only [List.length_cons]
    omega)
  have rd3364 := GeneratedTraces.trace_3430_body (by
    omega) rd3430
  simpa [barrettBitGuardStack, barrettSquareStack, barrettBitFrame,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3364

/-- A set exponent bit reaches the deployed conditional Barrett multiply entry exactly. -/
theorem barrettSetBitToMultiply
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {r words n bit byte aux0 aux1 aux2 mu freeMemBase a aux3 : UInt256}
    (hdepth : tail.length + 16 ≤ 1018)
    (hset : ((⟨1⟩ : UInt256).land ((byte.land ⟨255⟩).shiftRight bit)).eq ⟨1⟩ ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3411⟩
      (r :: words :: n :: bit :: bit :: byte :: aux0 :: aux1 :: aux2 :: mu ::
        freeMemBase :: a :: words :: aux3 :: n :: r :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3448⟩
      (mu :: freeMemBase :: a :: r :: words :: n :: bit :: bit :: byte :: aux0 :: aux1 ::
        aux2 :: mu :: freeMemBase :: a :: words :: aux3 :: n :: r :: tail)
      mem aw rdata acc (steps + 15) (gasUsed + 50) := by
  have rd3429 := GeneratedTraces.trace_3411_body (by
    simp only [List.length_cons]
    omega) h
  have rd3448 := rd3429.jumpiT (by native_decide) hset (by native_decide) (by
    simp only [List.length_cons]
    omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3448

/-- The multiply return continuation restores the same bit guard with the updated accumulator. -/
theorem barrettSetResultToGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {r words n bit byte aux0 aux1 aux2 mu freeMemBase a aux3 : UInt256}
    (hdepth : tail.length + 13 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨3467⟩
      (bit :: bit :: byte :: aux0 :: aux1 :: aux2 :: mu :: freeMemBase :: a ::
        words :: aux3 :: n :: r :: tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3364⟩
      (barrettBitGuardStack bit r words n freeMemBase mu byte aux0 aux1 aux2 a aux3 tail)
      mem aw rdata acc (steps + 27) (gasUsed + 79) := by
  have rd3364 := GeneratedTraces.trace_3467_body (by
    omega) h
  simpa [barrettBitGuardStack, barrettSquareStack, barrettBitFrame,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3364

/-! ## Barrett exponent-byte loading -/

def barrettExponentByteLoadGas (aw exponent byteIdx : UInt256) : Nat :=
  let aw1 := Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw exponent
  let aw2 := Modexp.MultiLimbExponentTrace.exponentByteLoadAw aw exponent byteIdx
  214 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1)

/-- The Barrett branch omits the redundant final `AND 0xff` after extracting the masked high
byte, so its trace-level value is recorded directly. -/
def barrettExponentByteValue (mem : ByteArray) (aw exponent byteIdx : UInt256) : UInt256 :=
  let address := Modexp.MultiLimbExponentTrace.exponentByteAddress exponent byteIdx
  ((⟨115339776388732929035197660848497720713218148788040405586178452820382218977280⟩ :
      UInt256).land
    (Modexp.MultiLimbExponentTrace.exponentByteWord mem aw address)).shiftRight ⟨248⟩

/-- The valid byte path performs both checked loads, extracts the byte, installs the next-byte
`topBit = 7`, and reaches the first Barrett bit guard exactly. -/
theorem barrettExponentByteLoadToBitGuardExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {byteIdx exponent topBit mu freeMemBase a words expLen n r : UInt256}
    (hdepth : tail.length + 10 ≤ 1011)
    (hindex : (byteIdx.lt
      (Modexp.MultiLimbExponentTrace.exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3323⟩
      (byteIdx :: exponent :: topBit :: mu :: freeMemBase :: a :: words :: expLen :: n :: r ::
        tail) mem aw rdata acc steps gasUsed) :
    let byte := barrettExponentByteValue mem
      (Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw exponent) exponent byteIdx
    RDx runtimeBytecode ee g s0 ⟨3364⟩
      (barrettBitGuardStack (topBit + ⟨1⟩) r words n freeMemBase mu byte
        byteIdx exponent ⟨7⟩ a expLen tail)
      mem (Modexp.MultiLimbExponentTrace.exponentByteLoadAw aw exponent byteIdx)
      rdata acc (steps + 62) (gasUsed + barrettExponentByteLoadGas aw exponent byteIdx) := by
  have rd1171 := GeneratedTraces.trace_3323_body hdepth h
  have rd1172 := rd1171.jumpiNT (by native_decide) (by
    simpa [Modexp.MultiLimbExponentTrace.exponentArrayLength] using hindex) (by
      simp only [List.length_cons]
      omega)
  have rd3218 := (GeneratedTraces.trace_1172_body (by
    simp only [List.length_cons]
    omega) rd1172).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3256 := (GeneratedTraces.trace_3218_body (by
    simp only [List.length_cons]
    omega) rd3218).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3348 := (GeneratedTraces.trace_3256_body (by
    simp only [List.length_cons]
    omega) rd3256).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd1335 := GeneratedTraces.trace_3348_body (by
    simp only [List.length_cons]
    omega) rd3348
  have rd1336 := rd1335.jumpiNT (by native_decide) htop (by
    simp only [List.length_cons]
    omega)
  have rd3354 := rd1336.jump (by native_decide) (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rd3364 := GeneratedTraces.trace_3354_body (by
    simp only [List.length_cons]
    omega) rd3354
  have normalized := rd3364.withIndices (k' := steps + 62) (by omega)
    (C' := gasUsed + barrettExponentByteLoadGas aw exponent byteIdx) (by
      simp [barrettExponentByteLoadGas,
        Modexp.MultiLimbExponentTrace.exponentByteLoadAw,
        Modexp.MultiLimbExponentTrace.exponentArrayLengthAw,
        Modexp.MultiLimbExponentTrace.exponentByteAddress]
      omega)
  simpa [barrettBitGuardStack, barrettSquareStack, barrettBitFrame,
    Modexp.MultiLimbExponentTrace.exponentArrayLengthAw,
    Modexp.MultiLimbExponentTrace.exponentByteAddress,
    Modexp.MultiLimbExponentTrace.exponentByteWord,
    barrettExponentByteValue,
    Modexp.MultiLimbExponentTrace.exponentByteLoadAw, u256_add_comm] using normalized

def barrettByteGuardStack
    (byteIdx exponent topBit mu freeMemBase a words expLen n r : UInt256)
    (tail : List UInt256) : List UInt256 :=
  byteIdx :: exponent :: topBit :: mu :: freeMemBase :: a :: words :: expLen :: n :: r :: tail

/-- A nonterminal byte guard reaches the checked byte loader exactly. -/
theorem barrettByteGuardTaken
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {byteIdx exponent topBit mu freeMemBase a words expLen n r : UInt256}
    (hdepth : tail.length + 10 ≤ 1022)
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu freeMemBase a words expLen n r tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3323⟩
      (byteIdx :: exponent :: topBit :: mu :: freeMemBase :: a :: words :: expLen :: n :: r ::
        tail) mem aw rdata acc (steps + 6) (gasUsed + 23) := by
  have rd3311 := GeneratedTraces.trace_3304_body (by
    simp [barrettByteGuardStack] at hdepth ⊢
    omega) h
  have rd3323 := rd3311.jumpiT (by native_decide) hguard (by native_decide) (by
    simp only [List.length_cons]
    omega)
  simpa [barrettByteGuardStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3323

/-- A zero bit counter removes the completed byte frame, increments `byteIdx`, and restores the
outer byte guard. -/
theorem barrettBitGuardExitToByteGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {r words n freeMemBase mu byte byteIdx exponent a expLen : UInt256}
    (hdepth : tail.length + 19 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨3364⟩
      (barrettBitGuardStack ⟨0⟩ r words n freeMemBase mu byte byteIdx exponent ⟨7⟩ a
        expLen tail) mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3304⟩
      (barrettByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ mu freeMemBase a words
        expLen n r tail) mem aw rdata acc (steps + 12) (gasUsed + 41) := by
  have rd3365 := h.jumpiNT (by native_decide) (by native_decide) (by
    simp [barrettBitGuardStack, barrettSquareStack, barrettBitFrame] at hdepth ⊢
    omega)
  have rd3365' := rd3365.withStack (stk' :=
      ⟨0⟩ :: r :: words :: n :: freeMemBase :: mu :: byte :: byteIdx :: exponent :: ⟨7⟩ ::
        mu :: freeMemBase :: a :: words :: expLen :: n :: r :: tail) (by
    simp [barrettBitGuardStack, barrettSquareStack, barrettBitFrame])
  have rd3304 := evm_run rd3365' with [pop, pop, pop, pop, pop, pop, pop,
    pushCanonical 1 .PUSH1 ⟨1⟩ (by decide), add,
    pushCanonical 2 .PUSH2 ⟨3304⟩ (by decide), jump (by native_decide)]
  have normalized := rd3304.withIndices (k' := steps + 12) (by omega)
    (C' := gasUsed + 41) (by omega)
  simpa [barrettByteGuardStack, barrettBitGuardStack, barrettSquareStack, barrettBitFrame,
    u256_add_comm] using normalized

/-- The terminal byte guard removes loop locals and dynamically returns the accumulator. -/
theorem barrettByteGuardReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {byteIdx exponent topBit mu freeMemBase a words expLen n r returnPc : UInt256}
    (hdepth : tail.length + 11 ≤ 1022)
    (hguard : byteIdx.lt expLen = ⟨0⟩)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3304⟩
      (barrettByteGuardStack byteIdx exponent topBit mu freeMemBase a words expLen n r
        (returnPc :: tail)) mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 returnPc (r :: tail)
      mem aw rdata acc (steps + 17) (gasUsed + 52) := by
  have rd3311 := GeneratedTraces.trace_3304_body (by
    simp [barrettByteGuardStack] at hdepth ⊢
    omega) h
  have rd3312 := rd3311.jumpiNT (by native_decide) hguard (by
    simp only [List.length_cons]
    omega)
  have rdReturn := GeneratedTraces.trace_3312_jump (by omega) rd3312
    (by native_decide) hreturn
  simpa [barrettByteGuardStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

/-! ## Barrett exponent-loop setup -/

def barrettSetupStack
    (startByte exponent a words expLen n r mu : UInt256) (tail : List UInt256) :
    List UInt256 :=
  startByte :: exponent :: a :: words :: expLen :: n :: r :: mu :: tail

def barrettSetupGas (aw exponent : UInt256) : Nat :=
  let aw' := Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw exponent
  21 + (Cₘ aw' - Cₘ aw)

/-- Install the leading-zero scan frame and load the exponent-array length. -/
theorem barrettSetupToScanExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {r a exponent n mu words : UInt256}
    (hdepth : tail.length + 6 ≤ 1019)
    (h : RDx runtimeBytecode ee g s0 ⟨3154⟩
      (r :: a :: exponent :: n :: mu :: words :: tail)
      mem aw rdata acc steps gasUsed) :
    let expLen := Modexp.MultiLimbExponentTrace.exponentArrayLength mem aw exponent
    RDx runtimeBytecode ee g s0 ⟨3162⟩
      (barrettSetupStack ⟨0⟩ exponent a words expLen n r mu tail)
      mem (Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw exponent) rdata acc
      (steps + 8) (gasUsed + barrettSetupGas aw exponent) := by
  have rd3162 := evm_run h with [jumpdest, swap4, swap5, swap1, dup3,
    mloadCanonical, swap3, push0]
  have normalized := rd3162.withIndices (k' := steps + 8) (by omega)
    (C' := gasUsed + barrettSetupGas aw exponent) (by
      simp [barrettSetupGas, Modexp.MultiLimbExponentTrace.exponentArrayLengthAw]
      omega)
  simpa [barrettSetupStack, Modexp.MultiLimbExponentTrace.exponentArrayLength,
    Modexp.MultiLimbExponentTrace.exponentArrayLengthAw] using normalized

def barrettScanMaskedWord (mem : ByteArray) (aw exponent startByte : UInt256) : UInt256 :=
  let address := Modexp.MultiLimbExponentTrace.exponentByteAddress exponent startByte
  let mask : UInt256 :=
    ⟨115339776388732929035197660848497720713218148788040405586178452820382218977280⟩
  (mask.land
    (Modexp.MultiLimbExponentTrace.exponentByteWord mem aw address)).land mask

def barrettScanLoadGas (aw exponent startByte : UInt256) : Nat :=
  let aw1 := Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw exponent
  let aw2 := Modexp.MultiLimbExponentTrace.exponentByteLoadAw aw exponent startByte
  146 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1)

/-- One in-range scan test performs the deployed checked byte access and stops before deciding
whether the loaded byte is zero. -/
theorem barrettScanByteExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent a words expLen n r mu : UInt256}
    (hdepth : tail.length + 8 ≤ 1017)
    (hguard : startByte.lt expLen ≠ ⟨0⟩)
    (hindex : (startByte.lt
      (Modexp.MultiLimbExponentTrace.exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3162⟩
      (barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc steps gasUsed) :
    let aw' := Modexp.MultiLimbExponentTrace.exponentByteLoadAw aw exponent startByte
    RDx runtimeBytecode ee g s0 ⟨3171⟩
      ((barrettScanMaskedWord mem
          (Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw exponent)
          exponent startByte).isZero ::
        barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw' rdata acc (steps + 41) (gasUsed + barrettScanLoadGas aw exponent startByte) := by
  have rd3170 := GeneratedTraces.trace_3162_body (by
    simp [barrettSetupStack] at hdepth ⊢
    omega) h
  have rd3505 := rd3170.jumpiT (by native_decide) hguard (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rd1171 := GeneratedTraces.trace_3505_body (by
    simp only [List.length_cons]
    omega) rd3505
  have rd1172 := rd1171.jumpiNT (by native_decide) (by
    simpa [Modexp.MultiLimbExponentTrace.exponentArrayLength] using hindex) (by
      simp only [List.length_cons]
      omega)
  have rd3218 := (GeneratedTraces.trace_1172_body (by
    simp only [List.length_cons]
    omega) rd1172).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3552 := (GeneratedTraces.trace_3218_body (by
    simp only [List.length_cons]
    omega) rd3218).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3171 := evm_run rd3552 with [jumpdest, and, iszero,
    pushCanonical 2 .PUSH2 ⟨3171⟩ (by decide), jump (by native_decide)]
  have normalized := rd3171.withIndices (k' := steps + 41) (by omega)
    (C' := gasUsed + barrettScanLoadGas aw exponent startByte) (by
      simp [barrettScanLoadGas, Modexp.MultiLimbExponentTrace.exponentByteLoadAw,
        Modexp.MultiLimbExponentTrace.exponentArrayLengthAw,
        Modexp.MultiLimbExponentTrace.exponentByteAddress]
      omega)
  simpa [barrettSetupStack, barrettScanMaskedWord,
    Modexp.MultiLimbExponentTrace.exponentArrayLengthAw,
    Modexp.MultiLimbExponentTrace.exponentByteAddress,
    Modexp.MultiLimbExponentTrace.exponentByteWord,
    Modexp.MultiLimbExponentTrace.exponentByteLoadAw, u256_add_comm] using normalized

/-- A zero scan byte increments `startByte` through the compiler's checked increment helper and
returns to the scan guard. -/
theorem barrettScanZeroToGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent a words expLen n r mu scanWord : UInt256}
    (hdepth : tail.length + 9 ≤ 1016)
    (hzero : scanWord = ⟨0⟩)
    (hinc : startByte ≠ (UInt256.lnot ⟨0⟩))
    (h : RDx runtimeBytecode ee g s0 ⟨3171⟩
      (scanWord.isZero :: barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3162⟩
      (barrettSetupStack (startByte + ⟨1⟩) exponent a words expLen n r mu tail)
      mem aw rdata acc (steps + 22) (gasUsed + 88) := by
  have hzeroTest : scanWord.isZero.isZero = ⟨0⟩ := by
    rw [hzero]
    native_decide
  have rd3176 := GeneratedTraces.trace_3171_body (by
    simp [barrettSetupStack] at hdepth ⊢
    omega) h
  have rd3177 := rd3176.jumpiNT (by native_decide) hzeroTest (by
    simp [barrettSetupStack]
    omega)
  have rd3136 := GeneratedTraces.trace_3177_body (by
    simp only [List.length_cons]
    omega) rd3177
  have hincTest : (startByte.eq (UInt256.lnot ⟨0⟩)) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro heq
    exact hinc (uInt256_eq_one_eq heq)
  have rd3137 := rd3136.jumpiNT (by native_decide) hincTest (by
    simp only [List.length_cons]
    omega)
  have rd3185 := GeneratedTraces.trace_3137_jump (by
    simp only [List.length_cons]
    omega) rd3137 (by native_decide) (by native_decide)
  have rd3162 := evm_run rd3185 with [jumpdest,
    pushCanonical 2 .PUSH2 ⟨3162⟩ (by decide), jump (by native_decide)]
  have normalized := rd3162.withIndices (k' := steps + 22) (by omega)
    (C' := gasUsed + 88) (by omega)
  simpa [barrettSetupStack, hzero, u256_add_comm] using normalized

/-- A nonzero scan byte leaves the leading-zero scan at PC 3190 without changing its index. -/
theorem barrettScanNonzeroToExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent a words expLen n r mu scanWord : UInt256}
    (hdepth : tail.length + 9 ≤ 1023)
    (hnonzero : scanWord ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3171⟩
      (scanWord.isZero :: barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3190⟩
      (barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc (steps + 4) (gasUsed + 17) := by
  have htest : scanWord.isZero.isZero ≠ ⟨0⟩ := by
    rw [isZero_eq_zero_of_ne hnonzero]
    native_decide
  have rd3176 := GeneratedTraces.trace_3171_body (by
    simp [barrettSetupStack] at hdepth ⊢
    omega) h
  have rd3190 := rd3176.jumpiT (by native_decide) htest (by native_decide) (by
    simp [barrettSetupStack]
    omega)
  simpa [barrettSetupStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3190

/-- An exhausted leading-zero guard reaches the common scan exit. -/
theorem barrettScanExhaustedToExit
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent a words expLen n r mu : UInt256}
    (hdepth : tail.length + 8 ≤ 1021)
    (hguard : startByte.lt expLen = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3162⟩
      (barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3190⟩
      (barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc (steps + 11) (gasUsed + 43) := by
  have rd3170 := GeneratedTraces.trace_3162_body (by
    simp [barrettSetupStack] at hdepth ⊢
    omega) h
  have rd3171 := rd3170.jumpiNT (by native_decide) hguard (by
    simp [barrettSetupStack]
    omega)
  have rd3176 := GeneratedTraces.trace_3171_body (by
    simp [barrettSetupStack]
    omega) rd3171
  have rd3190 := rd3176.jumpiT (by native_decide) (by
    rw [hguard]
    native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  simpa [barrettSetupStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd3190

/-- The all-zero exponent case removes the setup frame and returns the initialized accumulator. -/
theorem barrettAllZeroReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent a words expLen n r mu returnPc : UInt256}
    (hdepth : tail.length + 9 ≤ 1022)
    (hexhausted : startByte.eq expLen ≠ ⟨0⟩)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3190⟩
      (barrettSetupStack startByte exponent a words expLen n r mu (returnPc :: tail))
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 returnPc (r :: tail)
      mem aw rdata acc (steps + 18) (gasUsed + 55) := by
  have rd3198 := GeneratedTraces.trace_3190_body (by
    simp [barrettSetupStack] at hdepth ⊢
    omega) h
  have rd3494 := rd3198.jumpiT (by native_decide) hexhausted (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rdReturn := GeneratedTraces.trace_3494_jump (by omega) rd3494
    (by native_decide) hreturn
  simpa [barrettSetupStack, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

def barrettTopBitStack
    (topBit startByte exponent mu freeMemBase a words expLen n r byte : UInt256)
    (tail : List UInt256) : List UInt256 :=
  topBit :: startByte :: exponent :: mu :: freeMemBase :: a :: words :: expLen :: n :: r ::
    byte :: tail

def barrettTopByteLoadGas (aw exponent startByte : UInt256) : Nat :=
  let aw0 := Modexp.MultiLimbArithmeticTrace.readWords1 aw ⟨64⟩
  let aw1 := Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw0 exponent
  let aw2 := Modexp.MultiLimbExponentTrace.exponentByteLoadAw aw0 exponent startByte
  159 + (Cₘ aw0 - Cₘ aw) + (Cₘ aw1 - Cₘ aw0) + (Cₘ aw2 - Cₘ aw1)

/-- Reload the first nonzero exponent byte, save the free-memory pointer, and install the
seven-bit top-bit scan. -/
theorem barrettExitToTopBitGuardExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent a words expLen n r mu : UInt256}
    (hdepth : tail.length + 8 ≤ 1016)
    (hnonexhausted : startByte.eq expLen = ⟨0⟩)
    (hindex : (startByte.lt
      (Modexp.MultiLimbExponentTrace.exponentArrayLength mem
        (Modexp.MultiLimbArithmeticTrace.readWords1 aw ⟨64⟩) exponent)).isZero = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3190⟩
      (barrettSetupStack startByte exponent a words expLen n r mu tail)
      mem aw rdata acc steps gasUsed) :
    let aw0 := Modexp.MultiLimbArithmeticTrace.readWords1 aw ⟨64⟩
    let aw1 := Modexp.MultiLimbExponentTrace.exponentArrayLengthAw aw0 exponent
    let aw2 := Modexp.MultiLimbExponentTrace.exponentByteLoadAw aw0 exponent startByte
    let freeMemBase := Modexp.MultiLimbArithmeticTrace.readWord mem aw ⟨64⟩
    let byte := barrettExponentByteValue mem aw1 exponent startByte
    RDx runtimeBytecode ee g s0 ⟨3266⟩
      (barrettTopBitStack ⟨7⟩ startByte exponent mu freeMemBase a words expLen n r byte tail)
      mem aw2 rdata acc (steps + 45) (gasUsed + barrettTopByteLoadGas aw exponent startByte) := by
  have rd3198 := GeneratedTraces.trace_3190_body (by
    simp [barrettSetupStack] at hdepth ⊢
    omega) h
  have rd3199 := rd3198.jumpiNT (by native_decide) hnonexhausted (by
    simp [barrettSetupStack]
    omega)
  have rd1171 := GeneratedTraces.trace_3199_body (by omega) rd3199
  have rd1172 := rd1171.jumpiNT (by native_decide) (by
    simpa [Modexp.MultiLimbExponentTrace.exponentArrayLength,
      Modexp.MultiLimbArithmeticTrace.readWords1] using hindex) (by
      simp only [List.length_cons]
      omega)
  have rd3218 := (GeneratedTraces.trace_1172_body (by
    simp only [List.length_cons]
    omega) rd1172).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3256 := (GeneratedTraces.trace_3218_body (by
    simp only [List.length_cons]
    omega) rd3218).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3262 := (GeneratedTraces.trace_3256_body (by
    simp only [List.length_cons]
    omega) rd3256).jump (by native_decide) (by native_decide) (by
      simp only [List.length_cons]
      omega)
  have rd3266 := evm_run rd3262 with [jumpdest, swap9,
    pushCanonical 1 .PUSH1 ⟨7⟩ (by decide)]
  have normalized := rd3266.withIndices (k' := steps + 45) (by omega)
    (C' := gasUsed + barrettTopByteLoadGas aw exponent startByte) (by
      simp [barrettTopByteLoadGas, Modexp.MultiLimbArithmeticTrace.readWords1,
        Modexp.MultiLimbExponentTrace.exponentArrayLengthAw,
        Modexp.MultiLimbExponentTrace.exponentByteLoadAw,
        Modexp.MultiLimbExponentTrace.exponentByteAddress]
      omega)
  simpa [barrettSetupStack, barrettTopBitStack,
    Modexp.MultiLimbArithmeticTrace.readWord, Modexp.MultiLimbArithmeticTrace.readWords1,
    Modexp.MultiLimbExponentTrace.exponentArrayLengthAw,
    Modexp.MultiLimbExponentTrace.exponentByteAddress,
    Modexp.MultiLimbExponentTrace.exponentByteWord,
    Modexp.MultiLimbExponentTrace.exponentByteLoadAw,
    barrettExponentByteValue, u256_add_comm] using normalized

def barrettTopBitTest (byte topBit : UInt256) : UInt256 :=
  (⟨1⟩ : UInt256).land ((byte.land ⟨255⟩).shiftRight topBit)

/-- Cursor zero exits through the left conjunct of the Solidity `while` guard without testing
the byte again. -/
theorem barrettTopBitZeroCursorToByteGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {startByte exponent mu freeMemBase a words expLen n r byte : UInt256}
    (hdepth : tail.length + 11 ≤ 1018)
    (h : RDx runtimeBytecode ee g s0 ⟨3266⟩
      (barrettTopBitStack ⟨0⟩ startByte exponent mu freeMemBase a words expLen n r byte tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3304⟩
      (barrettByteGuardStack startByte exponent ⟨0⟩ mu freeMemBase a words expLen n r tail)
      mem aw rdata acc (steps + 21) (gasUsed + 70) := by
  have rd3274 := GeneratedTraces.trace_3266_body (by
    simp [barrettTopBitStack] at hdepth ⊢
    omega) h
  have rd3275 := rd3274.jumpiNT (by native_decide) (by native_decide) (by
    simp [barrettTopBitStack]
    omega)
  have rd3294 := GeneratedTraces.trace_3275_taken (by
    simp [barrettTopBitStack]
    omega) rd3275
    (by native_decide) (by native_decide) (by native_decide)
  have rd3304 := evm_run rd3294 with [jumpdest, swap3, swap4, swap5, swap6,
    swap7, swap8, swap9, swap10, pop]
  have normalized := rd3304.withIndices (k' := steps + 21) (by omega)
    (C' := gasUsed + 70) (by omega)
  simpa [barrettTopBitStack, barrettByteGuardStack,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

/-- A zero tested bit decrements the bounded top-bit cursor and returns to its guard. -/
theorem barrettTopBitZeroToGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {topBit startByte exponent mu freeMemBase a words expLen n r byte : UInt256}
    (hdepth : tail.length + 11 ≤ 1018)
    (htop : topBit ≠ ⟨0⟩)
    (hzero : barrettTopBitTest byte topBit = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3266⟩
      (barrettTopBitStack topBit startByte exponent mu freeMemBase a words expLen n r byte tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3266⟩
      (barrettTopBitStack (topBit - ⟨1⟩) startByte exponent mu freeMemBase a words
        expLen n r byte tail)
      mem aw rdata acc (steps + 40) (gasUsed + 149) := by
  have hguard : topBit.isZero.isZero ≠ ⟨0⟩ := by
    rw [isZero_eq_zero_of_ne htop]
    native_decide
  have rd3274 := GeneratedTraces.trace_3266_body (by
    simp [barrettTopBitStack] at hdepth ⊢
    omega) h
  have rd3478 := rd3274.jumpiT (by native_decide) hguard (by native_decide) (by
    simp [barrettTopBitStack]
    omega)
  have hbit : (barrettTopBitTest byte topBit).isZero.isZero = ⟨0⟩ := by
    rw [hzero]
    native_decide
  have rd3281 := GeneratedTraces.trace_3478_notTaken (by omega) rd3478
    (by native_decide) (by simpa [barrettTopBitTest] using hbit)
  have hdec : topBit.isZero = ⟨0⟩ := isZero_eq_zero_of_ne htop
  have rd3149 := GeneratedTraces.trace_3281_notTaken (by
    simp only [List.length_cons]
    omega) rd3281 (by native_decide) hdec
  have rd3289 := GeneratedTraces.trace_3149_jump (by
    simp only [List.length_cons]
    omega) rd3149 (by native_decide) (by native_decide)
  have rd3266 := evm_run rd3289 with [jumpdest,
    pushCanonical 2 .PUSH2 ⟨3266⟩ (by decide), jump (by native_decide)]
  have normalized := rd3266.withIndices (k' := steps + 40) (by omega)
    (C' := gasUsed + 149) (by omega)
  simpa [barrettTopBitStack, barrettTopBitTest, hzero,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

/-- The first set bit exits the top-bit scan and normalizes the outer byte-loop frame. -/
theorem barrettTopBitSetToByteGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {steps gasUsed : Nat} {tail : List UInt256}
    {topBit startByte exponent mu freeMemBase a words expLen n r byte : UInt256}
    (hdepth : tail.length + 11 ≤ 1018)
    (htop : topBit ≠ ⟨0⟩)
    (hset : barrettTopBitTest byte topBit ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨3266⟩
      (barrettTopBitStack topBit startByte exponent mu freeMemBase a words expLen n r byte tail)
      mem aw rdata acc steps gasUsed) :
    RDx runtimeBytecode ee g s0 ⟨3304⟩
      (barrettByteGuardStack startByte exponent topBit mu freeMemBase a words expLen n r tail)
      mem aw rdata acc (steps + 33) (gasUsed + 108) := by
  have hguard : topBit.isZero.isZero ≠ ⟨0⟩ := by
    rw [isZero_eq_zero_of_ne htop]
    native_decide
  have rd3274 := GeneratedTraces.trace_3266_body (by
    simp [barrettTopBitStack] at hdepth ⊢
    omega) h
  have rd3478 := rd3274.jumpiT (by native_decide) hguard (by native_decide) (by
    simp [barrettTopBitStack]
    omega)
  have hbit : (barrettTopBitTest byte topBit).isZero.isZero ≠ ⟨0⟩ := by
    rw [isZero_eq_zero_of_ne hset]
    native_decide
  have rd3294 := GeneratedTraces.trace_3478_taken (by omega) rd3478
    (by native_decide) (by simpa [barrettTopBitTest] using hbit) (by native_decide)
  have rd3304 := evm_run rd3294 with [jumpdest, swap3, swap4, swap5, swap6,
    swap7, swap8, swap9, swap10, pop]
  have normalized := rd3304.withIndices (k' := steps + 33) (by omega)
    (C' := gasUsed + 108) (by omega)
  simpa [barrettTopBitStack, barrettByteGuardStack, barrettTopBitTest,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

end Modexp.MultiLimbBarrettExponentTrace
