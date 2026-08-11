import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSCall
import Examples.Precompiles.Modexp.MultiLimbMontgomeryCIOSCall

/-! # Exact multi-limb exponent-loop square call -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbExponentTrace

open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomerySOSCall
open Modexp.MultiLimbMontgomeryCIOSCall

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def exponentResetMemory (mem : ByteArray) (freeMemBase : UInt256) : ByteArray :=
  freeMemBase.toByteArray.write 0 mem 64 32

def exponentResetAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat 64 32)

def exponentResetGas (aw : UInt256) : Nat :=
  59 + (Cₘ (exponentResetAw aw) - Cₘ aw)

private theorem exponentSquareEntryDecodes :
    [decode runtimeBytecode ⟨4754⟩, decode runtimeBytecode ⟨4755⟩,
      decode runtimeBytecode ⟨4756⟩, decode runtimeBytecode ⟨4757⟩,
      decode runtimeBytecode ⟨4760⟩, decode runtimeBytecode ⟨4761⟩,
      decode runtimeBytecode ⟨4762⟩, decode runtimeBytecode ⟨4763⟩,
      decode runtimeBytecode ⟨4766⟩, decode runtimeBytecode ⟨4767⟩,
      decode runtimeBytecode ⟨4768⟩, decode runtimeBytecode ⟨4769⟩,
      decode runtimeBytecode ⟨4770⟩, decode runtimeBytecode ⟨4771⟩,
      decode runtimeBytecode ⟨4773⟩, decode runtimeBytecode ⟨4774⟩,
      decode runtimeBytecode ⟨4775⟩, decode runtimeBytecode ⟨4776⟩,
      decode runtimeBytecode ⟨4779⟩] =
    [some (.JUMPDEST, .none), some (.DUP3, .none), some (.DUP3, .none),
      some (.Push .PUSH2, some (⟨3406⟩, 2)), some (.DUP3, .none),
      some (.PUSH0, .none), some (.NOT, .none),
      some (.Push .PUSH2, some (⟨4780⟩, 2)), some (.SWAP6, .none),
      some (.ADD, .none), some (.SWAP10, .none), some (.DUP11, .none),
      some (.SWAP10, .none), some (.Push .PUSH1, some (⟨64⟩, 1)),
      some (.MSTORE, .none), some (.DUP9, .none), some (.DUP5, .none),
      some (.Push .PUSH2, some (⟨7201⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_7208_exponent :
    (D_J runtimeBytecode 0).contains ⟨7201⟩ = true := by native_decide

/-- The square branch resets temporary memory and enters `_montSqr` at PC 7201 exactly. -/
theorem exponentSquareEntry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {bit rM words n freeMemBase n0inv : UInt256}
    (hdepth : tail.length + 6 ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨4754⟩
      (bit :: rM :: words :: n :: freeMemBase :: n0inv :: tail)
      mem aw rdata acc k C) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode ee g s0 ⟨7201⟩
      (rM :: n :: n0inv :: words :: ⟨3406⟩ ::
        rM :: words :: ⟨4780⟩ :: rM :: words :: n :: previousBit :: previousBit :: tail)
      (exponentResetMemory mem freeMemBase) (exponentResetAw aw)
      rdata acc (k + 19) (C + exponentResetGas aw) := by
  have hd := exponentSquareEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18⟩
  have rd := evm_run h with [known jumpdest h0, known dup3 h1, known dup3 h2,
    known push2 h3 ⟨3406⟩, known dup3 h4, known push0 h5, known not h6,
    known push2 h7 ⟨4780⟩, known swap6 h8, known add h9, known swap10 h10,
    known dup11 h11, known swap10 h12, known push1 h13 ⟨64⟩]
  have rdStore := RDx.mstore (Cₘ (exponentResetAw aw) - Cₘ aw)
    (exponentResetMemory mem freeMemBase) (exponentResetAw aw) rd h14
    (by
      intro s hsaw hstk
      simp [exponentResetAw, memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
        show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [exponentResetMemory, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [exponentResetAw, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp only [List.length_cons]; omega)
  have rd7208 := evm_run rdStore with [known dup9 h15, known dup5 h16,
    known push2 h17 ⟨7201⟩, known jump h18 jumpDest_7208_exponent]
  have normalized := rd7208.withIndices (k' := k + 19) (by omega)
    (C' := C + exponentResetGas aw) (by
      simp only [exponentResetGas]
      omega)
  simpa [u256_add_comm] using normalized

def exponentCopyMemory
    (mem : ByteArray) (resultBase rM words : UInt256) : ByteArray :=
  finalCopyMemory mem (resultBase + ⟨32⟩) (rM + ⟨32⟩)
    (UInt256.shiftLeft words ⟨5⟩)

def exponentCopyAw (aw resultBase rM words : UInt256) : UInt256 :=
  finalCopyAw aw (resultBase + ⟨32⟩) (rM + ⟨32⟩)
    (UInt256.shiftLeft words ⟨5⟩)

def exponentCopyGas (aw resultBase rM words : UInt256) : Nat :=
  let source := resultBase + ⟨32⟩
  let result := rM + ⟨32⟩
  let bytes := UInt256.shiftLeft words ⟨5⟩
  let nextAw := finalCopyAw aw source result bytes
  51 + (Cₘ nextAw - Cₘ aw) + GasConstants.Gverylow +
    GasConstants.Gcopy * ((bytes.toNat + 31) / 32)

/-- The shared PC 3406 continuation copies the square into `rM` and resumes at PC 4780. -/
theorem exponentSquareCopyReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {resultBase rM words : UInt256}
    (hdepth : tail.length + 4 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨3406⟩
      (resultBase :: rM :: words :: ⟨4780⟩ :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4780⟩ tail
      (exponentCopyMemory mem resultBase rM words)
      (exponentCopyAw aw resultBase rM words)
      rdata acc (k + 16) (C + exponentCopyGas aw resultBase rM words) := by
  have rd7207 := GeneratedTraces.trace_3406_body hdepth h
  have rd4780 := rd7207.jump (by native_decide) (by native_decide) (by omega)
  have normalized := rd4780.withIndices (k' := k + 16) (by omega)
    (C' := C + exponentCopyGas aw resultBase rM words) (by
      simp [exponentCopyGas, finalCopyAw,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega)
  simpa [exponentCopyMemory, exponentCopyAw, finalCopyMemory, finalCopyAw] using normalized

/-- The shared PC 3406 copy continuation can resume at any valid deployed jump destination. -/
theorem exponentCopyReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {resultBase rM words resumePc : UInt256}
    (hdepth : tail.length + 4 ≤ 1021)
    (hresume : (D_J runtimeBytecode 0).contains resumePc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨3406⟩
      (resultBase :: rM :: words :: resumePc :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 resumePc tail
      (exponentCopyMemory mem resultBase rM words)
      (exponentCopyAw aw resultBase rM words)
      rdata acc (k + 16) (C + exponentCopyGas aw resultBase rM words) := by
  have rd7207 := GeneratedTraces.trace_3406_body hdepth h
  have rdResume := rd7207.jump (by native_decide) hresume (by omega)
  have normalized := rdResume.withIndices (k' := k + 16) (by omega)
    (C' := C + exponentCopyGas aw resultBase rM words) (by
      simp [exponentCopyGas, finalCopyAw,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      omega)
  simpa [exponentCopyMemory, exponentCopyAw, finalCopyMemory, finalCopyAw] using normalized

def exponentMultiplyResetGas (aw : UInt256) : Nat :=
  39 + (Cₘ (exponentResetAw aw) - Cₘ aw)

private theorem exponentMultiplyEntryDecodes :
    [decode runtimeBytecode ⟨4814⟩, decode runtimeBytecode ⟨4815⟩,
      decode runtimeBytecode ⟨4818⟩, decode runtimeBytecode ⟨4819⟩,
      decode runtimeBytecode ⟨4822⟩, decode runtimeBytecode ⟨4823⟩,
      decode runtimeBytecode ⟨4824⟩, decode runtimeBytecode ⟨4825⟩,
      decode runtimeBytecode ⟨4827⟩, decode runtimeBytecode ⟨4828⟩,
      decode runtimeBytecode ⟨4829⟩, decode runtimeBytecode ⟨4832⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH2, some (⟨4833⟩, 2)),
      some (.SWAP6, .none), some (.Push .PUSH2, some (⟨3406⟩, 2)),
      some (.SWAP4, .none), some (.DUP7, .none), some (.SWAP4, .none),
      some (.Push .PUSH1, some (⟨64⟩, 1)), some (.MSTORE, .none),
      some (.DUP6, .none), some (.Push .PUSH2, some (⟨4052⟩, 2)),
      some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_4052_exponent :
    (D_J runtimeBytecode 0).contains ⟨4052⟩ = true := by native_decide

/-- The set-bit branch resets temporary memory and enters `_montMul` at PC 4052 exactly. -/
theorem exponentMultiplyEntry
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {n0inv freeMemBase bM rM words n : UInt256}
    (hdepth : tail.length + 7 ≤ 1013)
    (h : RDx runtimeBytecode ee g s0 ⟨4814⟩
      (n0inv :: freeMemBase :: bM :: rM :: words :: n :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4052⟩
      (rM :: bM :: n :: n0inv :: words :: ⟨3406⟩ ::
        rM :: words :: ⟨4833⟩ :: tail)
      (exponentResetMemory mem freeMemBase) (exponentResetAw aw)
      rdata acc (k + 12) (C + exponentMultiplyResetGas aw) := by
  have hd := exponentMultiplyEntryDecodes
  simp only [List.cons.injEq, and_true] at hd
  rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
  have rd := evm_run h with [known jumpdest h0, known push2 h1 ⟨4833⟩,
    known swap6 h2, known push2 h3 ⟨3406⟩, known swap4 h4, known dup7 h5,
    known swap4 h6, known push1 h7 ⟨64⟩]
  have rdStore := RDx.mstore (Cₘ (exponentResetAw aw) - Cₘ aw)
    (exponentResetMemory mem freeMemBase) (exponentResetAw aw) rd h8
    (by
      intro s hsaw hstk
      simp [exponentResetAw, memoryExpansionCost, memoryExpansionCost.μᵢ', hsaw, hstk,
        show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [exponentResetMemory, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp [exponentResetAw, show (⟨64⟩ : UInt256).toNat = 64 by decide])
    (by simp only [List.length_cons]; omega)
  have rd4052 := evm_run rdStore with [known dup6 h9, known push2 h10 ⟨4052⟩,
    known jump h11 jumpDest_4052_exponent]
  have normalized := rd4052.withIndices (k' := k + 12) (by omega)
    (C' := C + exponentMultiplyResetGas aw) (by
      simp [exponentMultiplyResetGas]
      omega)
  simpa using normalized

/-- The post-square bit test selects the deployed CIOS multiply branch exactly. -/
theorem exponentSetBitToMultiply
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : UInt256}
    (hdepth : tail.length + 12 ≤ 1017)
    (hset : ((v5.shiftRight v3).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4780⟩
      (v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 :: v8 :: v9 :: v10 ::
        v11 :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4814⟩
      (v9 :: v10 :: v11 :: v0 :: v1 :: v2 :: v3 :: v4 :: v5 :: v6 :: v7 ::
        v8 :: v9 :: v10 :: v11 :: tail)
      mem aw rdata acc (k + 13) (C + 44) := by
  have rd4795 := GeneratedTraces.trace_4780_body hdepth h
  have rd4814 := rd4795.jumpiT (by native_decide) hset (by native_decide) (by
    simp only [List.length_cons]
    omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4814

/-! ## Exact bit-loop frame

The optimizer keeps several values duplicated below the source-level locals.  Naming the
whole deployed frame once makes the common post-square branch invariant explicit.
-/

def exponentBitFrame
    (rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  rM :: words :: n :: freeMemBase :: n0inv :: byte :: aux0 :: aux1 :: aux2 ::
    n0inv :: freeMemBase :: aM :: words :: aux3 :: n :: rM :: tail

def exponentSquareStack
    (bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  bit :: exponentBitFrame rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 tail

def exponentBitGuardStack
    (bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 : UInt256)
    (tail : List UInt256) : List UInt256 :=
  ⟨4754⟩ :: bit ::
    exponentSquareStack bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 tail

/-- An unset exponent bit skips multiplication and restores the exact bit-loop guard frame. -/
theorem exponentUnsetBitToGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {rM words n bit byte aux0 aux1 aux2 n0inv freeMemBase aM aux3 : UInt256}
    (hdepth : tail.length + 16 ≤ 1017)
    (hunset : ((byte.shiftRight bit).land ⟨1⟩).eq ⟨1⟩ = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4780⟩
      (rM :: words :: n :: bit :: bit :: byte :: aux0 :: aux1 :: aux2 :: n0inv ::
        freeMemBase :: aM :: words :: aux3 :: n :: rM :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4739⟩
      (exponentBitGuardStack bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM
        aux3 tail)
      mem aw rdata acc (k + 31) (C + 93) := by
  have rd4795 := GeneratedTraces.trace_4780_body (by
    simp only [List.length_cons]
    omega) h
  have rd4796 := rd4795.jumpiNT (by native_decide) hunset (by
    simp only [List.length_cons]
    omega)
  have rd4739 := GeneratedTraces.trace_4796_body (by omega) rd4796
  simpa [exponentBitGuardStack, exponentSquareStack, exponentBitFrame,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4739

/-- The set-bit multiply continuation restores the same exact bit-loop guard frame. -/
theorem exponentSetBitResultToGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {bit byte aux0 aux1 aux2 n0inv freeMemBase aM words aux3 n rM : UInt256}
    (hdepth : tail.length + 13 ≤ 1017)
    (h : RDx runtimeBytecode ee g s0 ⟨4833⟩
      (bit :: bit :: byte :: aux0 :: aux1 :: aux2 :: n0inv :: freeMemBase :: aM ::
        words :: aux3 :: n :: rM :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4739⟩
      (exponentBitGuardStack bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM
        aux3 tail)
      mem aw rdata acc (k + 27) (C + 79) := by
  have rd4739 := GeneratedTraces.trace_4833_body hdepth h
  simpa [exponentBitGuardStack, exponentSquareStack, exponentBitFrame,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4739

/-- A positive bit-loop counter enters the next square with the frame unchanged. -/
theorem exponentBitGuardTaken
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 : UInt256}
    (hdepth : tail.length + 18 ≤ 1024)
    (hbit : bit ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4739⟩
      (exponentBitGuardStack bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM
        aux3 tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4754⟩
      (exponentSquareStack bit rM words n freeMemBase n0inv byte aux0 aux1 aux2 aM aux3 tail)
      mem aw rdata acc (k + 1) (C + 10) := by
  have rd4754 := h.jumpiT (by native_decide) hbit (by native_decide) (by
    simp [exponentBitGuardStack, exponentSquareStack, exponentBitFrame] at hdepth ⊢
    omega)
  simpa [exponentBitGuardStack, exponentSquareStack, exponentBitFrame] using rd4754

structure ExponentMultiplySelection where
  multiply : CIOSFunctionSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectExponentMultiply (zeroFuel outerFuel compareFuel subFuel : Nat)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (rM bM n n0inv : UInt256) : Option ExponentMultiplySelection :=
  let resetMemory := exponentResetMemory mem (UInt256.ofNat fp)
  let resetAw := exponentResetAw aw
  match selectCIOSFunction zeroFuel outerFuel compareFuel subFuel resetMemory resetAw
      wordCount fp rM bM n n0inv ⟨3406⟩ with
  | none => none
  | some multiply => some {
      multiply := multiply
      memory := exponentCopyMemory multiply.finalize.memory (UInt256.ofNat fp) rM
        (UInt256.ofNat wordCount)
      activeWords := exponentCopyAw multiply.finalize.activeWords (UInt256.ofNat fp) rM
        (UInt256.ofNat wordCount)
      steps := 12 + multiply.steps + 16
      gas := exponentMultiplyResetGas aw + multiply.gas +
        exponentCopyGas multiply.finalize.activeWords (UInt256.ofNat fp) rM
          (UInt256.ofNat wordCount) }

/-- One set-bit Montgomery multiply, including reset, CIOS, copy-back, and resume at PC 4833. -/
theorem selectedExponentMultiplyExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel outerFuel compareFuel subFuel wordCount fp : Nat}
    {tail : List UInt256} {rM bM n n0inv : UInt256}
    (selected : ExponentMultiplySelection)
    (hwords : wordCount ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize wordCount < 2 ^ 64)
    (hmemSize : 96 ≤ (exponentResetMemory mem (UInt256.ofNat fp)).size)
    (hmemLe : (exponentResetMemory mem (UInt256.ofNat fp)).size ≤ fp)
    (hgap : fp - (exponentResetMemory mem (UInt256.ofNat fp)).size < USize.size)
    (haw3 : 3 ≤ (exponentResetAw aw).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw aw * ⟨32⟩)
    (hread : (exponentResetMemory mem (UInt256.ofNat fp)).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hallocated64 : ¬ (⟨64⟩ : UInt256) ≥
      newWordArrayWords (exponentResetAw aw) fp wordCount * ⟨32⟩)
    (hmultiplyBound : selected.multiply.head.setup.tP.toNat +
      32 * wordCount < UInt256.size)
    (hmultiplyStop : selected.multiply.head.setup.tEnd.toNat =
      selected.multiply.head.setup.tP.toNat + 32 * wordCount)
    (hreductionBound : (selected.multiply.head.setup.tP + ⟨32⟩).toNat +
      32 * (wordCount - 1) < UInt256.size)
    (hreductionStop : selected.multiply.head.setup.tEnd.toNat =
      (selected.multiply.head.setup.tP + ⟨32⟩).toNat + 32 * (wordCount - 1))
    (hdepth : tail.length + 22 ≤ 1014)
    (hselect : selectExponentMultiply zeroFuel outerFuel compareFuel subFuel mem aw
      wordCount fp rM bM n n0inv = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4814⟩
      (n0inv :: UInt256.ofNat fp :: bM :: rM :: UInt256.ofNat wordCount :: n :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4833⟩ tail
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  unfold selectExponentMultiply at hselect
  dsimp only at hselect
  let resetMemory := exponentResetMemory mem (UInt256.ofNat fp)
  let resetAw := exponentResetAw aw
  cases hm : selectCIOSFunction zeroFuel outerFuel compareFuel subFuel resetMemory resetAw
      wordCount fp rM bM n n0inv ⟨3406⟩ with
  | none => simpa [resetMemory, resetAw, hm] using hselect
  | some multiply =>
      have hselected : selected = {
          multiply := multiply
          memory := exponentCopyMemory multiply.finalize.memory (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          activeWords := exponentCopyAw multiply.finalize.activeWords (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          steps := 12 + multiply.steps + 16
          gas := exponentMultiplyResetGas aw + multiply.gas +
            exponentCopyGas multiply.finalize.activeWords (UInt256.ofNat fp) rM
              (UInt256.ofNat wordCount) } := by
        simpa [resetMemory, resetAw, hm] using hselect.symm
      subst selected
      have rd4052 := exponentMultiplyEntry (by omega) h
      let multiplyTail := rM :: UInt256.ofNat wordCount :: ⟨4833⟩ :: tail
      have rd3406 := selectedCIOSFunctionExact multiply
        (tail := multiplyTail) hwords hfp hbound hmemSize hmemLe hgap haw3 haw64
        hread hcalldata hallocated64 hmultiplyBound hmultiplyStop hreductionBound
        hreductionStop (by dsimp [multiplyTail]; omega) (by native_decide) hm (by
          simpa [resetMemory, resetAw, multiplyTail] using rd4052)
      have rd4833 := exponentCopyReturn (resumePc := ⟨4833⟩) (tail := tail)
        (by omega) (by native_decide) (by simpa using rd3406)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4833

structure ExponentSquareSelection where
  square : SOSFunctionSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectExponentSquare
    (zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (rM n n0inv : UInt256) : Option ExponentSquareSelection :=
  let resetMemory := exponentResetMemory mem (UInt256.ofNat fp)
  let resetAw := exponentResetAw aw
  match selectSOSFunction zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel resetMemory resetAw wordCount fp n n0inv
      ⟨3406⟩ rM with
  | none => none
  | some square =>
      let squareMemory := square.setup.initialized.arithmetic.suffix.copy.memory
      let squareAw := square.setup.initialized.arithmetic.suffix.copy.activeWords
      some {
        square := square
        memory := exponentCopyMemory squareMemory (UInt256.ofNat fp) rM
          (UInt256.ofNat wordCount)
        activeWords := exponentCopyAw squareAw (UInt256.ofNat fp) rM
          (UInt256.ofNat wordCount)
        steps := 19 + square.steps + 16
        gas := exponentResetGas aw + square.gas +
          exponentCopyGas squareAw (UInt256.ofNat fp) rM (UInt256.ofNat wordCount) }

/-- One deployed exponent-loop square, including memory reset and copy-back, executes exactly. -/
theorem selectedExponentSquareExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel wordCount fp : Nat}
    {tail : List UInt256}
    {bit rM n n0inv : UInt256}
    (selected : ExponentSquareSelection)
    (hwords : wordCount ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize wordCount < 2 ^ 64)
    (hmemSize : 96 ≤ (exponentResetMemory mem (UInt256.ofNat fp)).size)
    (hmemLe : (exponentResetMemory mem (UInt256.ofNat fp)).size ≤ fp)
    (hgap : fp - (exponentResetMemory mem (UInt256.ofNat fp)).size < USize.size)
    (haw3 : 3 ≤ (exponentResetAw aw).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw aw * ⟨32⟩)
    (hread : (exponentResetMemory mem (UInt256.ofNat fp)).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hallocated64 : ¬ (⟨64⟩ : UInt256) ≥
      newWordArrayWords (exponentResetAw aw) fp wordCount * ⟨32⟩)
    (hdepth : tail.length + 24 ≤ 1012)
    (hselect : selectExponentSquare zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw wordCount fp rM n n0inv =
      some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4754⟩
      (bit :: rM :: UInt256.ofNat wordCount :: n :: UInt256.ofNat fp :: n0inv :: tail)
      mem aw rdata acc k C) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4780⟩
      (rM :: UInt256.ofNat wordCount :: n :: previousBit :: previousBit :: tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  unfold selectExponentSquare at hselect
  dsimp only at hselect
  let resetMemory := exponentResetMemory mem (UInt256.ofNat fp)
  let resetAw := exponentResetAw aw
  cases hs : selectSOSFunction zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel resetMemory resetAw wordCount fp
      n n0inv ⟨3406⟩ rM with
  | none => simpa [resetMemory, resetAw, hs] using hselect
  | some square =>
      let squareMemory := square.setup.initialized.arithmetic.suffix.copy.memory
      let squareAw := square.setup.initialized.arithmetic.suffix.copy.activeWords
      have hselected : selected = {
          square := square
          memory := exponentCopyMemory squareMemory (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          activeWords := exponentCopyAw squareAw (UInt256.ofNat fp) rM
            (UInt256.ofNat wordCount)
          steps := 19 + square.steps + 16
          gas := exponentResetGas aw + square.gas +
            exponentCopyGas squareAw (UInt256.ofNat fp) rM (UInt256.ofNat wordCount) } := by
        simpa [resetMemory, resetAw, squareMemory, squareAw, hs] using hselect.symm
      subst selected
      have rd7208 := exponentSquareEntry (by omega) h
      let squareTail := rM :: UInt256.ofNat wordCount :: ⟨4780⟩ :: rM ::
        UInt256.ofNat wordCount :: n :: (UInt256.lnot ⟨0⟩ + bit) ::
        (UInt256.lnot ⟨0⟩ + bit) :: tail
      have rd3406Post := selectedSOSFunctionExact (tail := squareTail) square
        hwords hfp hbound hmemSize hmemLe
        hgap haw3 haw64 hread hcalldata hallocated64 (by
          dsimp [squareTail]
          omega) (by native_decide) hs (by
          simpa [resetMemory, resetAw, squareTail] using rd7208)
      rw [SOSCopyReturnPost] at rd3406Post
      have rd4780 := exponentSquareCopyReturn (tail :=
          rM :: UInt256.ofNat wordCount :: n :: (UInt256.lnot ⟨0⟩ + bit) ::
            (UInt256.lnot ⟨0⟩ + bit) :: tail)
        (by
          simp only [List.length_cons]
          omega) rd3406Post
      simpa [squareMemory, squareAw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using rd4780

/-! ## Complete deployed bit iterations -/

/-- One unset exponent bit executes the full square and branch-cleanup path exactly. -/
theorem selectedExponentUnsetBitExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel wordCount fp : Nat}
    {tail : List UInt256}
    {bit rM n n0inv byte aux0 aux1 aux2 aM aux3 : UInt256}
    (selected : ExponentSquareSelection)
    (hwords : wordCount ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize wordCount < 2 ^ 64)
    (hmemSize : 96 ≤ (exponentResetMemory mem (UInt256.ofNat fp)).size)
    (hmemLe : (exponentResetMemory mem (UInt256.ofNat fp)).size ≤ fp)
    (hgap : fp - (exponentResetMemory mem (UInt256.ofNat fp)).size < USize.size)
    (haw3 : 3 ≤ (exponentResetAw aw).toNat)
    (haw64 : ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw aw * ⟨32⟩)
    (hread : (exponentResetMemory mem (UInt256.ofNat fp)).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hallocated64 : ¬ (⟨64⟩ : UInt256) ≥
      newWordArrayWords (exponentResetAw aw) fp wordCount * ⟨32⟩)
    (hdepth : tail.length + 35 ≤ 1012)
    (hselect : selectExponentSquare zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw wordCount fp rM n n0inv =
      some selected)
    (hunset : ((byte.shiftRight (UInt256.lnot ⟨0⟩ + bit)).land ⟨1⟩).eq ⟨1⟩ = ⟨0⟩)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4754⟩
      (exponentSquareStack bit rM (UInt256.ofNat wordCount) n (UInt256.ofNat fp) n0inv
        byte aux0 aux1 aux2 aM aux3 tail)
      mem aw rdata acc k C) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4739⟩
      (exponentBitGuardStack previousBit rM (UInt256.ofNat wordCount) n
        (UInt256.ofNat fp) n0inv byte aux0 aux1 aux2 aM aux3 tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps + 31) (C + selected.gas + 93) := by
  let squareTail := byte :: aux0 :: aux1 :: aux2 :: n0inv :: UInt256.ofNat fp :: aM ::
    UInt256.ofNat wordCount :: aux3 :: n :: rM :: tail
  have rd4780 := selectedExponentSquareExact (tail := squareTail) selected
    hwords hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata hallocated64
    (by dsimp [squareTail]; omega) hselect (by
      simpa [exponentSquareStack, exponentBitFrame, squareTail] using h)
  have rd4739 := exponentUnsetBitToGuard (tail := tail) (by omega) hunset (by
    simpa [squareTail] using rd4780)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4739

/-- One set exponent bit executes the full square, CIOS multiply, and cleanup path exactly. -/
theorem selectedExponentSetBitExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel mulZeroFuel mulOuterFuel mulCompareFuel mulSubFuel
      wordCount fp : Nat}
    {tail : List UInt256}
    {bit rM n n0inv byte aux0 aux1 aux2 aM aux3 : UInt256}
    (square : ExponentSquareSelection) (multiply : ExponentMultiplySelection)
    (hwords : wordCount ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize wordCount < 2 ^ 64)
    (hsquareMemSize : 96 ≤ (exponentResetMemory mem (UInt256.ofNat fp)).size)
    (hsquareMemLe : (exponentResetMemory mem (UInt256.ofNat fp)).size ≤ fp)
    (hsquareGap : fp - (exponentResetMemory mem (UInt256.ofNat fp)).size < USize.size)
    (hsquareAw3 : 3 ≤ (exponentResetAw aw).toNat)
    (hsquareAw64 : ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw aw * ⟨32⟩)
    (hsquareRead : (exponentResetMemory mem (UInt256.ofNat fp)).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hsquareAllocated64 : ¬ (⟨64⟩ : UInt256) ≥
      newWordArrayWords (exponentResetAw aw) fp wordCount * ⟨32⟩)
    (hmultiplyMemSize :
      96 ≤ (exponentResetMemory square.memory (UInt256.ofNat fp)).size)
    (hmultiplyMemLe :
      (exponentResetMemory square.memory (UInt256.ofNat fp)).size ≤ fp)
    (hmultiplyGap :
      fp - (exponentResetMemory square.memory (UInt256.ofNat fp)).size < USize.size)
    (hmultiplyAw3 : 3 ≤ (exponentResetAw square.activeWords).toNat)
    (hmultiplyAw64 :
      ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw square.activeWords * ⟨32⟩)
    (hmultiplyRead :
      (exponentResetMemory square.memory (UInt256.ofNat fp)).readWithPadding 64 32 =
        UInt256.toByteArray (UInt256.ofNat fp))
    (hmultiplyAllocated64 : ¬ (⟨64⟩ : UInt256) ≥
      newWordArrayWords (exponentResetAw square.activeWords) fp wordCount * ⟨32⟩)
    (hmultiplyBound : multiply.multiply.head.setup.tP.toNat +
      32 * wordCount < UInt256.size)
    (hmultiplyStop : multiply.multiply.head.setup.tEnd.toNat =
      multiply.multiply.head.setup.tP.toNat + 32 * wordCount)
    (hreductionBound : (multiply.multiply.head.setup.tP + ⟨32⟩).toNat +
      32 * (wordCount - 1) < UInt256.size)
    (hreductionStop : multiply.multiply.head.setup.tEnd.toNat =
      (multiply.multiply.head.setup.tP + ⟨32⟩).toNat + 32 * (wordCount - 1))
    (hdepth : tail.length + 35 ≤ 1012)
    (hsquareSelect : selectExponentSquare zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw wordCount fp rM n n0inv =
      some square)
    (hmultiplySelect : selectExponentMultiply mulZeroFuel mulOuterFuel mulCompareFuel
      mulSubFuel square.memory square.activeWords wordCount fp rM aM n n0inv = some multiply)
    (hset : ((byte.shiftRight (UInt256.lnot ⟨0⟩ + bit)).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4754⟩
      (exponentSquareStack bit rM (UInt256.ofNat wordCount) n (UInt256.ofNat fp) n0inv
        byte aux0 aux1 aux2 aM aux3 tail)
      mem aw rdata acc k C) :
    let previousBit := UInt256.lnot ⟨0⟩ + bit
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4739⟩
      (exponentBitGuardStack previousBit rM (UInt256.ofNat wordCount) n
        (UInt256.ofNat fp) n0inv byte aux0 aux1 aux2 aM aux3 tail)
      multiply.memory multiply.activeWords rdata acc
      (k + square.steps + multiply.steps + 40) (C + square.gas + multiply.gas + 123) := by
  let previousBit := UInt256.lnot ⟨0⟩ + bit
  let squareTail := byte :: aux0 :: aux1 :: aux2 :: n0inv :: UInt256.ofNat fp :: aM ::
    UInt256.ofNat wordCount :: aux3 :: n :: rM :: tail
  have rd4780 := selectedExponentSquareExact (tail := squareTail) square
    hwords hfp hbound hsquareMemSize hsquareMemLe hsquareGap hsquareAw3 hsquareAw64
    hsquareRead hcalldata hsquareAllocated64 (by dsimp [squareTail]; omega)
    hsquareSelect (by
      simpa [exponentSquareStack, exponentBitFrame, squareTail] using h)
  have rd4814 := exponentSetBitToMultiply (tail :=
      UInt256.ofNat wordCount :: aux3 :: n :: rM :: tail) (by
        simp only [List.length_cons]
        omega) hset (by
          simpa [squareTail, previousBit] using rd4780)
  let multiplyTail := previousBit :: previousBit :: byte :: aux0 :: aux1 :: aux2 ::
    n0inv :: UInt256.ofNat fp :: aM :: UInt256.ofNat wordCount :: aux3 :: n :: rM :: tail
  have rd4833 := selectedExponentMultiplyExact (tail := multiplyTail) multiply
    hwords hfp hbound hmultiplyMemSize
    hmultiplyMemLe hmultiplyGap hmultiplyAw3 hmultiplyAw64 hmultiplyRead hcalldata
    hmultiplyAllocated64 hmultiplyBound hmultiplyStop hreductionBound hreductionStop
    (by dsimp [multiplyTail]; omega) hmultiplySelect (by
      simpa [multiplyTail, previousBit] using rd4814)
  have rd4739 := exponentSetBitResultToGuard (tail := tail) (by omega) (by
    simpa [multiplyTail, previousBit] using rd4833)
  simpa [previousBit, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4739

/-! ## Executable bit-loop selection -/

structure ExponentLoopFuel where
  squareZero : Nat
  squareRow : Nat
  squareProduct : Nat
  squareDouble : Nat
  squareDiagonal : Nat
  squareReduction : Nat
  squareColumn : Nat
  squareCarry : Nat
  squareCompare : Nat
  squareSub : Nat
  multiplyZero : Nat
  multiplyOuter : Nat
  multiplyCompare : Nat
  multiplySub : Nat

inductive ExponentBitLoopSelection where
  | done (memory : ByteArray) (activeWords : UInt256)
  | unset (square : ExponentSquareSelection) (rest : ExponentBitLoopSelection)
  | set (square : ExponentSquareSelection) (multiply : ExponentMultiplySelection)
      (rest : ExponentBitLoopSelection)

namespace ExponentBitLoopSelection

def memory : ExponentBitLoopSelection → ByteArray
  | .done mem _ => mem
  | .unset _ rest => rest.memory
  | .set _ _ rest => rest.memory

def activeWords : ExponentBitLoopSelection → UInt256
  | .done _ aw => aw
  | .unset _ rest => rest.activeWords
  | .set _ _ rest => rest.activeWords

def steps : ExponentBitLoopSelection → Nat
  | .done _ _ => 0
  | .unset square rest => square.steps + 32 + rest.steps
  | .set square multiply rest => square.steps + multiply.steps + 41 + rest.steps

def gas : ExponentBitLoopSelection → Nat
  | .done _ _ => 0
  | .unset square rest => square.gas + 103 + rest.gas
  | .set square multiply rest => square.gas + multiply.gas + 133 + rest.gas

end ExponentBitLoopSelection

def selectExponentBitLoop (bitFuel : Nat) (fuel : ExponentLoopFuel)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (bit byte rM aM n n0inv : UInt256) : Option ExponentBitLoopSelection :=
  if bit = ⟨0⟩ then
    some (.done mem aw)
  else
    match bitFuel with
    | 0 => none
    | bitFuel + 1 =>
        match selectExponentSquare fuel.squareZero fuel.squareRow fuel.squareProduct
            fuel.squareDouble fuel.squareDiagonal fuel.squareReduction fuel.squareColumn
            fuel.squareCarry fuel.squareCompare fuel.squareSub mem aw wordCount fp rM n n0inv with
        | none => none
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            if ((byte.shiftRight previousBit).land ⟨1⟩).eq ⟨1⟩ = ⟨0⟩ then
              match selectExponentBitLoop bitFuel fuel square.memory square.activeWords
                  wordCount fp previousBit byte rM aM n n0inv with
              | none => none
              | some rest => some (.unset square rest)
            else
              match selectExponentMultiply fuel.multiplyZero fuel.multiplyOuter
                  fuel.multiplyCompare fuel.multiplySub square.memory square.activeWords
                  wordCount fp rM aM n n0inv with
              | none => none
              | some multiply =>
                  match selectExponentBitLoop bitFuel fuel multiply.memory multiply.activeWords
                      wordCount fp previousBit byte rM aM n n0inv with
                  | none => none
                  | some rest => some (.set square multiply rest)

structure ExponentSquareValid (I : ExecutionEnv) (fuel : ExponentLoopFuel)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (rM n n0inv : UInt256) (square : ExponentSquareSelection) : Prop where
  words : wordCount ≤ 32
  fpMin : 96 ≤ fp
  allocationBound : fp + wordArrayAllocationSize wordCount < 2 ^ 64
  memorySize : 96 ≤ (exponentResetMemory mem (UInt256.ofNat fp)).size
  memoryLe : (exponentResetMemory mem (UInt256.ofNat fp)).size ≤ fp
  memoryGap : fp - (exponentResetMemory mem (UInt256.ofNat fp)).size < USize.size
  activeWordsMin : 3 ≤ (exponentResetAw aw).toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw aw * ⟨32⟩
  freePointerRead : (exponentResetMemory mem (UInt256.ofNat fp)).readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat fp)
  calldataBound : I.calldata.size < 2 ^ 64
  allocated64 : ¬ (⟨64⟩ : UInt256) ≥
    newWordArrayWords (exponentResetAw aw) fp wordCount * ⟨32⟩
  selected : selectExponentSquare fuel.squareZero fuel.squareRow fuel.squareProduct
    fuel.squareDouble fuel.squareDiagonal fuel.squareReduction fuel.squareColumn
    fuel.squareCarry fuel.squareCompare fuel.squareSub mem aw wordCount fp rM n n0inv =
      some square

structure ExponentMultiplyValid (I : ExecutionEnv) (fuel : ExponentLoopFuel)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (rM aM n n0inv : UInt256) (multiply : ExponentMultiplySelection) : Prop where
  words : wordCount ≤ 32
  fpMin : 96 ≤ fp
  allocationBound : fp + wordArrayAllocationSize wordCount < 2 ^ 64
  memorySize : 96 ≤ (exponentResetMemory mem (UInt256.ofNat fp)).size
  memoryLe : (exponentResetMemory mem (UInt256.ofNat fp)).size ≤ fp
  memoryGap : fp - (exponentResetMemory mem (UInt256.ofNat fp)).size < USize.size
  activeWordsMin : 3 ≤ (exponentResetAw aw).toNat
  activeWords64 : ¬ (⟨64⟩ : UInt256) ≥ exponentResetAw aw * ⟨32⟩
  freePointerRead : (exponentResetMemory mem (UInt256.ofNat fp)).readWithPadding 64 32 =
    UInt256.toByteArray (UInt256.ofNat fp)
  calldataBound : I.calldata.size < 2 ^ 64
  allocated64 : ¬ (⟨64⟩ : UInt256) ≥
    newWordArrayWords (exponentResetAw aw) fp wordCount * ⟨32⟩
  multiplyBound : multiply.multiply.head.setup.tP.toNat +
    32 * wordCount < UInt256.size
  multiplyStop : multiply.multiply.head.setup.tEnd.toNat =
    multiply.multiply.head.setup.tP.toNat + 32 * wordCount
  reductionBound : (multiply.multiply.head.setup.tP + ⟨32⟩).toNat +
    32 * (wordCount - 1) < UInt256.size
  reductionStop : multiply.multiply.head.setup.tEnd.toNat =
    (multiply.multiply.head.setup.tP + ⟨32⟩).toNat + 32 * (wordCount - 1)
  selected : selectExponentMultiply fuel.multiplyZero fuel.multiplyOuter fuel.multiplyCompare
    fuel.multiplySub mem aw wordCount fp rM aM n n0inv = some multiply

inductive ExponentBitLoopValid (I : ExecutionEnv) (fuel : ExponentLoopFuel)
    (wordCount fp : Nat) (rM aM n n0inv byte : UInt256) :
    ByteArray → UInt256 → UInt256 → ExponentBitLoopSelection → Prop where
  | done (mem : ByteArray) (aw : UInt256) :
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
        mem aw ⟨0⟩ (.done mem aw)
  | unset {mem : ByteArray} {aw bit : UInt256} {square : ExponentSquareSelection}
      {rest : ExponentBitLoopSelection}
      (bitNonzero : bit ≠ ⟨0⟩)
      (squareValid : ExponentSquareValid I fuel mem aw wordCount fp rM n n0inv square)
      (bitUnset : ((byte.shiftRight (UInt256.lnot ⟨0⟩ + bit)).land ⟨1⟩).eq ⟨1⟩ = ⟨0⟩)
      (restValid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
        square.memory square.activeWords (UInt256.lnot ⟨0⟩ + bit) rest) :
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
        mem aw bit (.unset square rest)
  | set {mem : ByteArray} {aw bit : UInt256} {square : ExponentSquareSelection}
      {multiply : ExponentMultiplySelection} {rest : ExponentBitLoopSelection}
      (bitNonzero : bit ≠ ⟨0⟩)
      (squareValid : ExponentSquareValid I fuel mem aw wordCount fp rM n n0inv square)
      (multiplyValid : ExponentMultiplyValid I fuel square.memory square.activeWords
        wordCount fp rM aM n n0inv multiply)
      (bitSet : ((byte.shiftRight (UInt256.lnot ⟨0⟩ + bit)).land ⟨1⟩).eq ⟨1⟩ ≠ ⟨0⟩)
      (restValid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
        multiply.memory multiply.activeWords (UInt256.lnot ⟨0⟩ + bit) rest) :
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
        mem aw bit (.set square multiply rest)

/-- The executable selector is valid whenever every selected arithmetic call satisfies its
local deployed-call side conditions. -/
theorem selectExponentBitLoop_valid
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp bitFuel : Nat}
    {rM aM n n0inv byte bit : UInt256} {mem : ByteArray} {aw : UInt256}
    {selected : ExponentBitLoopSelection}
    (hsquareValid : ∀ (mem' : ByteArray) (aw' : UInt256)
      (square : ExponentSquareSelection),
      selectExponentSquare fuel.squareZero fuel.squareRow fuel.squareProduct
        fuel.squareDouble fuel.squareDiagonal fuel.squareReduction fuel.squareColumn
        fuel.squareCarry fuel.squareCompare fuel.squareSub mem' aw' wordCount fp rM n n0inv =
          some square →
      ExponentSquareValid I fuel mem' aw' wordCount fp rM n n0inv square)
    (hmultiplyValid : ∀ (mem' : ByteArray) (aw' : UInt256)
      (multiply : ExponentMultiplySelection),
      selectExponentMultiply fuel.multiplyZero fuel.multiplyOuter fuel.multiplyCompare
        fuel.multiplySub mem' aw' wordCount fp rM aM n n0inv = some multiply →
      ExponentMultiplyValid I fuel mem' aw' wordCount fp rM aM n n0inv multiply)
    (hselect : selectExponentBitLoop bitFuel fuel mem aw wordCount fp
      bit byte rM aM n n0inv = some selected) :
    ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected := by
  induction bitFuel generalizing mem aw bit selected with
  | zero =>
      rw [selectExponentBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw
      · simp [hbit] at hselect
  | succ bitFuel ih =>
      rw [selectExponentBitLoop] at hselect
      by_cases hbit : bit = ⟨0⟩
      · subst bit
        simp only [ite_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw
      · simp only [hbit, ↓reduceIte] at hselect
        cases hsquare : selectExponentSquare fuel.squareZero fuel.squareRow fuel.squareProduct
            fuel.squareDouble fuel.squareDiagonal fuel.squareReduction fuel.squareColumn
            fuel.squareCarry fuel.squareCompare fuel.squareSub mem aw wordCount fp rM n n0inv with
        | none => simp [hsquare] at hselect
        | some square =>
            let previousBit := UInt256.lnot ⟨0⟩ + bit
            by_cases hset :
                ((byte.shiftRight previousBit).land ⟨1⟩).eq ⟨1⟩ = ⟨0⟩
            · cases hrest : selectExponentBitLoop bitFuel fuel square.memory
                  square.activeWords wordCount fp previousBit byte rM aM n n0inv with
              | none => simp [hsquare, previousBit, hset, hrest] at hselect
              | some rest =>
                  simp only [hsquare, previousBit, hset, if_true, hrest,
                    Option.some.injEq] at hselect
                  subst selected
                  exact .unset hbit (hsquareValid mem aw square hsquare) hset
                    (ih hrest)
            · cases hmultiply : selectExponentMultiply fuel.multiplyZero fuel.multiplyOuter
                  fuel.multiplyCompare fuel.multiplySub square.memory square.activeWords
                  wordCount fp rM aM n n0inv with
              | none => simp [hsquare, previousBit, hset, hmultiply] at hselect
              | some multiply =>
                  cases hrest : selectExponentBitLoop bitFuel fuel multiply.memory
                      multiply.activeWords wordCount fp previousBit byte rM aM n n0inv with
                  | none =>
                      simp [hsquare, previousBit, hset, hmultiply, hrest] at hselect
                  | some rest =>
                      simp only [hsquare, previousBit, hset, if_false, hmultiply, hrest,
                        Option.some.injEq] at hselect
                      subst selected
                      exact .set hbit (hsquareValid mem aw square hsquare)
                        (hmultiplyValid square.memory square.activeWords multiply hmultiply) hset
                        (ih hrest)

/-- A recursively valid executable selection runs the complete deployed inner bit loop exactly. -/
theorem validExponentBitLoopExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte byteIdx exponent expLen : UInt256}
    {mem : ByteArray} {aw bit : UInt256} {selected : ExponentBitLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {k C : Nat}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected)
    (hdepth : tail.length + 35 ≤ 1012)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4739⟩
      (exponentBitGuardStack bit rM (UInt256.ofNat wordCount) n
        (UInt256.ofNat fp) n0inv byte byteIdx exponent ⟨7⟩ aM expLen tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4739⟩
      (exponentBitGuardStack ⟨0⟩ rM (UInt256.ofNat wordCount) n
        (UInt256.ofNat fp) n0inv byte byteIdx exponent ⟨7⟩ aM expLen tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction valid generalizing k C with
  | done mem aw =>
      simpa [ExponentBitLoopSelection.memory, ExponentBitLoopSelection.activeWords,
        ExponentBitLoopSelection.steps, ExponentBitLoopSelection.gas] using h
  | @unset mem aw bit square rest bitNonzero squareValid bitUnset restValid ih =>
      have rd4754 := exponentBitGuardTaken (by omega) bitNonzero h
      have rdNext := selectedExponentUnsetBitExact square
        squareValid.words squareValid.fpMin squareValid.allocationBound
        squareValid.memorySize squareValid.memoryLe squareValid.memoryGap
        squareValid.activeWordsMin squareValid.activeWords64 squareValid.freePointerRead
        squareValid.calldataBound squareValid.allocated64 hdepth squareValid.selected bitUnset
        rd4754
      have rdFinal := ih (k := k + 1 + square.steps + 31)
        (C := C + 10 + square.gas + 93) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
      simpa [ExponentBitLoopSelection.memory, ExponentBitLoopSelection.activeWords,
        ExponentBitLoopSelection.steps, ExponentBitLoopSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal
  | @set mem aw bit square multiply rest bitNonzero squareValid multiplyValid bitSet
      restValid ih =>
      have rd4754 := exponentBitGuardTaken (by omega) bitNonzero h
      have rdNext := selectedExponentSetBitExact square multiply
        squareValid.words squareValid.fpMin squareValid.allocationBound
        squareValid.memorySize squareValid.memoryLe squareValid.memoryGap
        squareValid.activeWordsMin squareValid.activeWords64 squareValid.freePointerRead
        squareValid.calldataBound squareValid.allocated64
        multiplyValid.memorySize multiplyValid.memoryLe multiplyValid.memoryGap
        multiplyValid.activeWordsMin multiplyValid.activeWords64
        multiplyValid.freePointerRead multiplyValid.allocated64
        multiplyValid.multiplyBound multiplyValid.multiplyStop
        multiplyValid.reductionBound multiplyValid.reductionStop hdepth
        squareValid.selected multiplyValid.selected bitSet rd4754
      have rdFinal := ih (k := k + 1 + square.steps + multiply.steps + 40)
        (C := C + 10 + square.gas + multiply.gas + 123) (by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdNext)
      simpa [ExponentBitLoopSelection.memory, ExponentBitLoopSelection.activeWords,
        ExponentBitLoopSelection.steps, ExponentBitLoopSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal

/-! ## Byte-loop boundaries -/

def exponentByteGuardStack
    (byteIdx exponent topBit n0inv freeMemBase aM words expLen n rM : UInt256)
    (tail : List UInt256) : List UInt256 :=
  ⟨4701⟩ :: byteIdx.lt expLen :: byteIdx :: exponent :: topBit :: n0inv ::
    freeMemBase :: aM :: words :: expLen :: n :: rM :: tail

def exponentArrayLength (mem : ByteArray) (aw exponent : UInt256) : UInt256 :=
  if exponent.toNat ≥ mem.size ∨ exponent ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding exponent.toNat 32))

def exponentArrayLengthAw (aw exponent : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat exponent.toNat 32)

def exponentByteAddress (exponent byteIdx : UInt256) : UInt256 :=
  ⟨32⟩ + (byteIdx + exponent)

def exponentByteWord (mem : ByteArray) (aw address : UInt256) : UInt256 :=
  if address.toNat ≥ mem.size ∨ address ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding address.toNat 32))

def exponentByteValue (mem : ByteArray) (aw exponent byteIdx : UInt256) : UInt256 :=
  let address := exponentByteAddress exponent byteIdx
  (⟨255⟩ : UInt256).land
    (((⟨115339776388732929035197660848497720713218148788040405586178452820382218977280⟩ : UInt256).land
      (exponentByteWord mem aw address)).shiftRight ⟨248⟩)

def exponentByteLoadAw (aw exponent byteIdx : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (exponentArrayLengthAw aw exponent).toNat
      (exponentByteAddress exponent byteIdx).toNat 32)

def exponentByteLoadGas (aw exponent byteIdx : UInt256) : Nat :=
  let aw1 := exponentArrayLengthAw aw exponent
  let aw2 := exponentByteLoadAw aw exponent byteIdx
  218 + (Cₘ aw1 - Cₘ aw) + (Cₘ aw2 - Cₘ aw1)

/-- The deployed Solidity `uint8(exponent[byteIdx])` helper, including both checked loads and
the checked `topBit + 1`, reaches PC 4729 exactly. -/
theorem exponentByteLoadExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {byteIdx exponent topBit n0inv freeMemBase aM words expLen n rM : UInt256}
    (hdepth : tail.length + 10 ≤ 1010)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4701⟩
      (byteIdx :: exponent :: topBit :: n0inv :: freeMemBase :: aM :: words :: expLen ::
        n :: rM :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4729⟩
      ((topBit + ⟨1⟩) :: words :: n :: freeMemBase :: n0inv ::
        exponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx ::
        byteIdx :: exponent :: rM :: n0inv :: freeMemBase :: aM :: words :: expLen ::
        n :: rM :: tail)
      mem (exponentByteLoadAw aw exponent byteIdx) rdata acc
      (k + 61) (C + exponentByteLoadGas aw exponent byteIdx) := by
  have rd1171 := GeneratedTraces.trace_4701_body hdepth h
  have rd1172 := rd1171.jumpiNT (by native_decide) (by
    simpa [exponentArrayLength] using hindex) (by
      simp only [List.length_cons]
      omega)
  have rd1177 := GeneratedTraces.trace_1172_body (by
    simp only [List.length_cons]
    omega) rd1172
  have rd3218 := rd1177.jump (by native_decide) (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rd3255 := GeneratedTraces.trace_3218_body (by
    simp only [List.length_cons]
    omega) rd3218
  have rd3256 := rd3255.jump (by native_decide) (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rd3261 := GeneratedTraces.trace_3256_body (by
    simp only [List.length_cons]
    omega) rd3256
  have rd4636 := rd3261.jump (by native_decide) (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rd4641 := GeneratedTraces.trace_4636_body (by
    simp only [List.length_cons]
    omega) rd4636
  have rd3348 := rd4641.jump (by native_decide) (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have rd1335 := GeneratedTraces.trace_3348_body (by
    simp only [List.length_cons]
    omega) rd3348
  have rd1336 := rd1335.jumpiNT (by native_decide) htop (by
    simp only [List.length_cons]
    omega)
  have rd4729 := rd1336.jump (by native_decide) (by native_decide) (by
    simp only [List.length_cons]
    omega)
  have normalized := rd4729.withIndices (k' := k + 61) (by omega)
    (C' := C + exponentByteLoadGas aw exponent byteIdx) (by
      simp [exponentByteLoadGas, exponentByteLoadAw, exponentArrayLengthAw,
        exponentByteAddress]
      omega)
  simpa [exponentArrayLengthAw, exponentByteAddress, exponentByteWord,
    exponentByteValue, exponentByteLoadAw, u256_add_comm] using normalized

/-- PC 4729 installs `topBit = 7` for later bytes and enters the first bit guard exactly. -/
theorem exponentByteSetupToBitGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {bit words n freeMemBase n0inv byte byteIdx exponent rM aM expLen : UInt256}
    (hdepth : tail.length + 16 ≤ 1021)
    (h : RDx runtimeBytecode ee g s0 ⟨4729⟩
      (bit :: words :: n :: freeMemBase :: n0inv :: byte :: byteIdx :: exponent :: rM ::
        n0inv :: freeMemBase :: aM :: words :: expLen :: n :: rM :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4739⟩
      (exponentBitGuardStack bit rM words n freeMemBase n0inv byte byteIdx exponent ⟨7⟩
        aM expLen tail)
      mem aw rdata acc (k + 7) (C + 17) := by
  have rd4739 := GeneratedTraces.trace_4729_body (by
    simp only [List.length_cons]
    omega) h
  simpa [exponentBitGuardStack, exponentSquareStack, exponentBitFrame,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4739

/-- A zero bit counter exits the inner loop, increments `byteIdx`, and restores the byte guard. -/
theorem exponentBitGuardExitToByteGuard
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {rM words n freeMemBase n0inv byte byteIdx exponent aM expLen : UInt256}
    (hdepth : tail.length + 18 ≤ 1024)
    (h : RDx runtimeBytecode ee g s0 ⟨4739⟩
      (exponentBitGuardStack ⟨0⟩ rM words n freeMemBase n0inv byte byteIdx exponent ⟨7⟩
        aM expLen tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4689⟩
      (exponentByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ n0inv freeMemBase aM
        words expLen n rM tail)
      mem aw rdata acc (k + 17) (C + 54) := by
  have rd4740 := h.jumpiNT (by native_decide) (by native_decide) (by
    simp [exponentBitGuardStack, exponentSquareStack, exponentBitFrame] at hdepth ⊢
    omega)
  have rd4689 := GeneratedTraces.trace_4740_body (by
    simp only [List.length_cons]
    omega) rd4740
  simpa [exponentBitGuardStack, exponentSquareStack, exponentBitFrame,
    exponentByteGuardStack, u256_add_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4689

/-- One loaded exponent byte executes all selected bits and returns to the next byte guard. -/
theorem validExponentByteBitsExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv byte byteIdx exponent expLen : UInt256}
    {mem : ByteArray} {aw bit : UInt256} {selected : ExponentBitLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {k C : Nat}
    (valid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv byte
      mem aw bit selected)
    (hdepth : tail.length + 35 ≤ 1012)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4729⟩
      (bit :: UInt256.ofNat wordCount :: n :: UInt256.ofNat fp :: n0inv :: byte ::
        byteIdx :: exponent :: rM :: n0inv :: UInt256.ofNat fp :: aM ::
        UInt256.ofNat wordCount :: expLen :: n :: rM :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4689⟩
      (exponentByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ n0inv
        (UInt256.ofNat fp) aM (UInt256.ofNat wordCount) expLen n rM tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps + 24) (C + selected.gas + 71) := by
  have rd4739 := exponentByteSetupToBitGuard (by omega) h
  have rdDone := validExponentBitLoopExact valid hdepth rd4739
  have rd4689 := exponentBitGuardExitToByteGuard (by omega) rdDone
  have normalized := rd4689.withIndices (k' := k + selected.steps + 24) (by omega)
    (C' := C + selected.gas + 71) (by omega)
  exact normalized

structure ExponentByteSelection where
  byte : UInt256
  bits : ExponentBitLoopSelection
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectExponentByte (bitFuel : Nat) (fuel : ExponentLoopFuel)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (byteIdx exponent topBit rM aM n n0inv : UInt256) : Option ExponentByteSelection :=
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := exponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  match selectExponentBitLoop bitFuel fuel mem loadAw wordCount fp
      (topBit + ⟨1⟩) byte rM aM n n0inv with
  | none => none
  | some bits => some {
      byte := byte
      bits := bits
      memory := bits.memory
      activeWords := bits.activeWords
      steps := bits.steps + 86
      gas := exponentByteLoadGas aw exponent byteIdx + bits.gas + 81 }

structure ExponentByteValid (I : ExecutionEnv) (fuel : ExponentLoopFuel)
    (wordCount fp : Nat) (rM aM n n0inv : UInt256)
    (mem : ByteArray) (aw byteIdx exponent topBit expLen : UInt256)
    (selected : ExponentByteSelection) : Prop where
  guardTaken : byteIdx.lt expLen ≠ ⟨0⟩
  indexValid : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩
  topBitValid : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩
  byteEq : selected.byte =
    exponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx
  bitsValid : ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv selected.byte
    mem (exponentByteLoadAw aw exponent byteIdx) (topBit + ⟨1⟩) selected.bits
  memoryEq : selected.memory = selected.bits.memory
  activeWordsEq : selected.activeWords = selected.bits.activeWords
  stepsEq : selected.steps = selected.bits.steps + 86
  gasEq : selected.gas = exponentByteLoadGas aw exponent byteIdx + selected.bits.gas + 81

/-- A successful byte selector is valid once its checked load and selected bit loop satisfy their
local side conditions. -/
theorem selectExponentByte_valid
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp bitFuel : Nat}
    {rM aM n n0inv : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : ExponentByteSelection}
    (hguard : byteIdx.lt expLen ≠ ⟨0⟩)
    (hindex : (byteIdx.lt (exponentArrayLength mem aw exponent)).isZero = ⟨0⟩)
    (htop : topBit.gt (topBit + ⟨1⟩) = ⟨0⟩)
    (hbitsValid : ∀ (bits : ExponentBitLoopSelection),
      selectExponentBitLoop bitFuel fuel mem (exponentByteLoadAw aw exponent byteIdx)
        wordCount fp (topBit + ⟨1⟩)
        (exponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx)
        rM aM n n0inv = some bits →
      ExponentBitLoopValid I fuel wordCount fp rM aM n n0inv
        (exponentByteValue mem (exponentArrayLengthAw aw exponent) exponent byteIdx)
        mem (exponentByteLoadAw aw exponent byteIdx) (topBit + ⟨1⟩) bits)
    (hselect : selectExponentByte bitFuel fuel mem aw wordCount fp byteIdx exponent topBit
      rM aM n n0inv = some selected) :
    ExponentByteValid I fuel wordCount fp rM aM n n0inv
      mem aw byteIdx exponent topBit expLen selected := by
  unfold selectExponentByte at hselect
  dsimp only at hselect
  let lengthAw := exponentArrayLengthAw aw exponent
  let byte := exponentByteValue mem lengthAw exponent byteIdx
  let loadAw := exponentByteLoadAw aw exponent byteIdx
  cases hbits : selectExponentBitLoop bitFuel fuel mem loadAw wordCount fp
      (topBit + ⟨1⟩) byte rM aM n n0inv with
  | none => simpa [lengthAw, byte, loadAw, hbits] using hselect
  | some bits =>
      have hselected : selected = {
          byte := byte
          bits := bits
          memory := bits.memory
          activeWords := bits.activeWords
          steps := bits.steps + 86
          gas := exponentByteLoadGas aw exponent byteIdx + bits.gas + 81 } := by
        simpa [lengthAw, byte, loadAw, hbits] using hselect.symm
      subst selected
      exact {
        guardTaken := hguard
        indexValid := hindex
        topBitValid := htop
        byteEq := by rfl
        bitsValid := hbitsValid bits (by simpa [lengthAw, byte, loadAw] using hbits)
        memoryEq := by rfl
        activeWordsEq := by rfl
        stepsEq := by rfl
        gasEq := by rfl }

/-- One valid selected exponent byte, including its guard, checked load, all bits, and backedge,
executes exactly. -/
theorem validExponentByteExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv : UInt256}
    {mem : ByteArray} {aw byteIdx exponent topBit expLen : UInt256}
    {selected : ExponentByteSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {k C : Nat}
    (valid : ExponentByteValid I fuel wordCount fp rM aM n n0inv
      mem aw byteIdx exponent topBit expLen selected)
    (hdepth : tail.length + 35 ≤ 1012)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4689⟩
      (exponentByteGuardStack byteIdx exponent topBit n0inv (UInt256.ofNat fp) aM
        (UInt256.ofNat wordCount) expLen n rM tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4689⟩
      (exponentByteGuardStack (byteIdx + ⟨1⟩) exponent ⟨7⟩ n0inv
        (UInt256.ofNat fp) aM (UInt256.ofNat wordCount) expLen n rM tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  have rd4701 := h.jumpiT (by native_decide) valid.guardTaken (by native_decide) (by
    simp [exponentByteGuardStack] at hdepth ⊢
    omega)
  have rd4729 := exponentByteLoadExact (by omega) valid.indexValid valid.topBitValid rd4701
  have bitsValid := valid.bitsValid
  rw [valid.byteEq] at bitsValid
  have rd4689 := validExponentByteBitsExact bitsValid hdepth (by
    simpa using rd4729)
  have normalized := rd4689.withIndices (k' := k + selected.steps) (by
      rw [valid.stepsEq]
      omega)
    (C' := C + selected.gas) (by
      rw [valid.gasEq]
      omega)
  simpa [valid.memoryEq, valid.activeWordsEq] using normalized

inductive ExponentByteLoopSelection where
  | done (memory : ByteArray) (activeWords byteIdx topBit : UInt256)
  | next (byte : ExponentByteSelection) (rest : ExponentByteLoopSelection)

namespace ExponentByteLoopSelection

def memory : ExponentByteLoopSelection → ByteArray
  | .done mem _ _ _ => mem
  | .next _ rest => rest.memory

def activeWords : ExponentByteLoopSelection → UInt256
  | .done _ aw _ _ => aw
  | .next _ rest => rest.activeWords

def byteIdx : ExponentByteLoopSelection → UInt256
  | .done _ _ idx _ => idx
  | .next _ rest => rest.byteIdx

def topBit : ExponentByteLoopSelection → UInt256
  | .done _ _ _ top => top
  | .next _ rest => rest.topBit

def steps : ExponentByteLoopSelection → Nat
  | .done _ _ _ _ => 0
  | .next byte rest => byte.steps + rest.steps

def gas : ExponentByteLoopSelection → Nat
  | .done _ _ _ _ => 0
  | .next byte rest => byte.gas + rest.gas

end ExponentByteLoopSelection

def selectExponentByteLoop (byteFuel bitFuel : Nat) (fuel : ExponentLoopFuel)
    (mem : ByteArray) (aw : UInt256) (wordCount fp : Nat)
    (byteIdx exponent topBit expLen rM aM n n0inv : UInt256) :
    Option ExponentByteLoopSelection :=
  if byteIdx.lt expLen = ⟨0⟩ then
    some (.done mem aw byteIdx topBit)
  else
    match byteFuel with
    | 0 => none
    | byteFuel + 1 =>
        match selectExponentByte bitFuel fuel mem aw wordCount fp byteIdx exponent topBit
            rM aM n n0inv with
        | none => none
        | some byte =>
            match selectExponentByteLoop byteFuel bitFuel fuel byte.memory byte.activeWords
                wordCount fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen rM aM n n0inv with
            | none => none
            | some rest => some (.next byte rest)

inductive ExponentByteLoopValid (I : ExecutionEnv) (fuel : ExponentLoopFuel)
    (wordCount fp : Nat) (rM aM n n0inv exponent expLen : UInt256) :
    ByteArray → UInt256 → UInt256 → UInt256 → ExponentByteLoopSelection → Prop where
  | done (mem : ByteArray) (aw byteIdx topBit : UInt256)
      (guardZero : byteIdx.lt expLen = ⟨0⟩) :
      ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
        mem aw byteIdx topBit (.done mem aw byteIdx topBit)
  | next {mem : ByteArray} {aw byteIdx topBit : UInt256}
      {byte : ExponentByteSelection} {rest : ExponentByteLoopSelection}
      (byteValid : ExponentByteValid I fuel wordCount fp rM aM n n0inv
        mem aw byteIdx exponent topBit expLen byte)
      (restValid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
        byte.memory byte.activeWords (byteIdx + ⟨1⟩) ⟨7⟩ rest) :
      ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
        mem aw byteIdx topBit (.next byte rest)

/-- The recursive executable byte selector is valid whenever every successful selected byte
satisfies its local checked-load and arithmetic side conditions. -/
theorem selectExponentByteLoop_valid
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp byteFuel bitFuel : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    (hbyteValid : ∀ (mem' : ByteArray) (aw' byteIdx' topBit' : UInt256)
      (byte : ExponentByteSelection),
      byteIdx'.lt expLen ≠ ⟨0⟩ →
      selectExponentByte bitFuel fuel mem' aw' wordCount fp byteIdx' exponent topBit'
        rM aM n n0inv = some byte →
      ExponentByteValid I fuel wordCount fp rM aM n n0inv
        mem' aw' byteIdx' exponent topBit' expLen byte)
    (hselect : selectExponentByteLoop byteFuel bitFuel fuel mem aw wordCount fp
      byteIdx exponent topBit expLen rM aM n n0inv = some selected) :
    ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected := by
  induction byteFuel generalizing mem aw byteIdx topBit selected with
  | zero =>
      rw [selectExponentByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw byteIdx topBit hguard
      · simp [hguard] at hselect
  | succ byteFuel ih =>
      rw [selectExponentByteLoop] at hselect
      by_cases hguard : byteIdx.lt expLen = ⟨0⟩
      · simp only [hguard, if_true, Option.some.injEq] at hselect
        subst selected
        exact .done mem aw byteIdx topBit hguard
      · simp only [hguard, if_false] at hselect
        cases hbyte : selectExponentByte bitFuel fuel mem aw wordCount fp byteIdx exponent
            topBit rM aM n n0inv with
        | none => simp [hbyte] at hselect
        | some byte =>
            cases hrest : selectExponentByteLoop byteFuel bitFuel fuel byte.memory
                byte.activeWords wordCount fp (byteIdx + ⟨1⟩) exponent ⟨7⟩ expLen
                rM aM n n0inv with
            | none => simp [hbyte, hrest] at hselect
            | some rest =>
                simp only [hbyte, hrest, Option.some.injEq] at hselect
                subst selected
                exact .next (hbyteValid mem aw byteIdx topBit byte hguard hbyte)
                  (ih hrest)

/-- A valid outer selection executes every remaining exponent byte and stops at the terminal
byte guard with exact accumulated gas. -/
theorem validExponentByteLoopExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {k C : Nat}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected)
    (hdepth : tail.length + 35 ≤ 1012)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4689⟩
      (exponentByteGuardStack byteIdx exponent topBit n0inv (UInt256.ofNat fp) aM
        (UInt256.ofNat wordCount) expLen n rM tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4689⟩
      (exponentByteGuardStack selected.byteIdx exponent selected.topBit n0inv
        (UInt256.ofNat fp) aM (UInt256.ofNat wordCount) expLen n rM tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction valid generalizing k C with
  | done mem aw byteIdx topBit guardZero =>
      simpa [ExponentByteLoopSelection.byteIdx, ExponentByteLoopSelection.topBit,
        ExponentByteLoopSelection.memory, ExponentByteLoopSelection.activeWords,
        ExponentByteLoopSelection.steps, ExponentByteLoopSelection.gas] using h
  | @next mem aw byteIdx topBit byte rest byteValid restValid ih =>
      have rdNext := validExponentByteExact byteValid hdepth h
      have rdFinal := ih (k := k + byte.steps) (C := C + byte.gas) rdNext
      simpa [ExponentByteLoopSelection.byteIdx, ExponentByteLoopSelection.topBit,
        ExponentByteLoopSelection.memory, ExponentByteLoopSelection.activeWords,
        ExponentByteLoopSelection.steps, ExponentByteLoopSelection.gas,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdFinal

theorem ExponentByteLoopValid.finalGuardZero
    {I : ExecutionEnv} {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected) :
    selected.byteIdx.lt expLen = ⟨0⟩ := by
  induction valid with
  | done _ _ _ _ guardZero => simpa [ExponentByteLoopSelection.byteIdx] using guardZero
  | next _ _ ih => simpa [ExponentByteLoopSelection.byteIdx] using ih

/-- The terminal byte guard removes loop locals and dynamically returns `rM` to its caller. -/
theorem exponentByteGuardReturn
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {byteIdx exponent topBit n0inv freeMemBase aM words expLen n rM returnPc : UInt256}
    (hdepth : tail.length + 12 ≤ 1024)
    (hguard : byteIdx.lt expLen = ⟨0⟩)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode ee g s0 ⟨4689⟩
      (exponentByteGuardStack byteIdx exponent topBit n0inv freeMemBase aM words expLen n rM
        (returnPc :: tail))
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 returnPc (rM :: tail)
      mem aw rdata acc (k + 12) (C + 39) := by
  have rd4690 := h.jumpiNT (by native_decide) hguard (by
    simp [exponentByteGuardStack] at hdepth ⊢
    omega)
  have rd4700 := GeneratedTraces.trace_4690_body (by omega) rd4690
  have rdReturn := rd4700.jump (by native_decide) hreturn (by
    simp only [List.length_cons]
    omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

/-- All selected exponent bytes execute and `_modexpLoop` returns `rM` exactly. -/
theorem validExponentByteLoopReturnExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {fuel : ExponentLoopFuel} {wordCount fp : Nat}
    {rM aM n n0inv exponent expLen returnPc : UInt256}
    {mem : ByteArray} {aw byteIdx topBit : UInt256}
    {selected : ExponentByteLoopSelection}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {tail : List UInt256} {k C : Nat}
    (valid : ExponentByteLoopValid I fuel wordCount fp rM aM n n0inv exponent expLen
      mem aw byteIdx topBit selected)
    (hdepth : tail.length + 36 ≤ 1012)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4689⟩
      (exponentByteGuardStack byteIdx exponent topBit n0inv (UInt256.ofNat fp) aM
        (UInt256.ofNat wordCount) expLen n rM (returnPc :: tail))
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc (rM :: tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps + 12) (C + selected.gas + 39) := by
  have rdGuard := validExponentByteLoopExact valid (by
    simp only [List.length_cons]
    omega) h
  have rdReturn := exponentByteGuardReturn (by omega) valid.finalGuardZero hreturn rdGuard
  have normalized := rdReturn.withIndices (k' := k + selected.steps + 12) (by omega)
    (C' := C + selected.gas + 39) (by omega)
  exact normalized

end Modexp.MultiLimbExponentTrace
