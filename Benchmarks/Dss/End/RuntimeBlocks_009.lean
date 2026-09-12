import Reasoning.SummaryPatterns
import Benchmarks.Dss.End.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace endRuntimeBlocks

/-- Final stack for bytecode block summary `endRuntime_block_5028`. -/
def endRuntime_block_5028_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5028. -/
theorem endRuntime_block_5028 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5028) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5030) (endRuntime_block_5028_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5030)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5028_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5028) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5030) (endRuntime_block_5028_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5028 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 5030: gas (0x5a). No RD transition is asserted. Summaries resume at pc 5031 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 5031: call (0xf1). No RD transition is asserted. Summaries resume at pc 5032 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_5032_taken`. -/
def endRuntime_block_5032_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5032. -/
theorem endRuntime_block_5032_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5048) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5032) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5048) (endRuntime_block_5032_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5048) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5048)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5032_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5048) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5032) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5048) (endRuntime_block_5032_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5032_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5032_fallthrough`. -/
def endRuntime_block_5032_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5032. -/
theorem endRuntime_block_5032_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5032) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5039) (endRuntime_block_5032_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5048) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5039)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5032_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5032) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5039) (endRuntime_block_5032_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5032_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5039. -/
theorem endRuntime_block_5039 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5039) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5048_taken`. -/
def endRuntime_block_5048_taken_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5048. -/
theorem endRuntime_block_5048_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5070) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5048) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5070) (endRuntime_block_5048_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5070) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5070)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5048_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5070) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5048) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5070) (endRuntime_block_5048_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5048_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5048_fallthrough`. -/
def endRuntime_block_5048_fallthrough_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5048. -/
theorem endRuntime_block_5048_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5048) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5066) (endRuntime_block_5048_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5070) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5066)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5048_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5048) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5066) (endRuntime_block_5048_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5048_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5066. -/
theorem endRuntime_block_5066 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5066) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5070_taken`. -/
def endRuntime_block_5070_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) + (UInt256.ofNat 4)) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 32) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) :: (UInt256.ofNat 1406599397) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad x1 mem) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5070_taken`. -/
def endRuntime_block_5070_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5070. -/
theorem endRuntime_block_5070_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5141) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5070) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5141) (endRuntime_block_5070_taken_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (R := R)) (endRuntime_block_5070_taken_memory (mem := mem)) (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 1406599397) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := RD.mload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.swap2 (by native_decide) (by evm_ov)
  have r25 := r24.push4 (UInt256.ofNat 1406599397) (by native_decide) (by evm_ov)
  have r26 := r25.swap2 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r28 := r27.dup1 (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r33 := r32.swap3 (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.swap2 (by native_decide) (by evm_ov)
  have r36 := r35.swap1 (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.sub (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.dup2 (by native_decide) (by evm_ov)
  have r42 := r41.dup7 (by native_decide) (by evm_ov)
  have r43 := r42.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r44⟩ := r43.extcodesize (by native_decide) (by evm_ov)
  have r45 := r44.iszero (by native_decide) (by evm_ov)
  have r46 := r45.dup1 (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 5141) (by native_decide) (by evm_ov)
  have r49 := r48.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5141)) r49 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5070_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5141) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5070) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5141) (endRuntime_block_5070_taken_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (R := R)) (endRuntime_block_5070_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5070_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5070_fallthrough`. -/
def endRuntime_block_5070_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) + (UInt256.ofNat 4)) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 32) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) :: (UInt256.ofNat 1406599397) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad x1 mem) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5070_fallthrough`. -/
def endRuntime_block_5070_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1406599397) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5070. -/
theorem endRuntime_block_5070_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5070) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5137) (endRuntime_block_5070_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (R := R)) (endRuntime_block_5070_fallthrough_memory (mem := mem)) (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 1406599397) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := RD.mload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r19 := r18.shl (by native_decide) (by evm_ov)
  have r20 := r19.sub (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.swap2 (by native_decide) (by evm_ov)
  have r25 := r24.push4 (UInt256.ofNat 1406599397) (by native_decide) (by evm_ov)
  have r26 := r25.swap2 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r28 := r27.dup1 (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r33 := r32.swap3 (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.swap2 (by native_decide) (by evm_ov)
  have r36 := r35.swap1 (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.sub (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.dup2 (by native_decide) (by evm_ov)
  have r42 := r41.dup7 (by native_decide) (by evm_ov)
  have r43 := r42.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r44⟩ := r43.extcodesize (by native_decide) (by evm_ov)
  have r45 := r44.iszero (by native_decide) (by evm_ov)
  have r46 := r45.dup1 (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 5141) (by native_decide) (by evm_ov)
  have r49 := r48.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5137)) r49 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5070_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5070) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5137) (endRuntime_block_5070_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (R := R)) (endRuntime_block_5070_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5070_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5137. -/
theorem endRuntime_block_5137 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5137) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5141`. -/
def endRuntime_block_5141_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5141. -/
theorem endRuntime_block_5141 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5141) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5143) (endRuntime_block_5141_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5143)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5141_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5141) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5143) (endRuntime_block_5141_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5141 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 5143: gas (0x5a). No RD transition is asserted. Summaries resume at pc 5144 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 5144: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 5145 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_5145_taken`. -/
def endRuntime_block_5145_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5145. -/
theorem endRuntime_block_5145_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5161) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5145) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5161) (endRuntime_block_5145_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5161) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5161)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5145_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5161) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5145) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5161) (endRuntime_block_5145_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5145_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5145_fallthrough`. -/
def endRuntime_block_5145_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5145. -/
theorem endRuntime_block_5145_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5145) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5152) (endRuntime_block_5145_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5161) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5152)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5145_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5145) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5152) (endRuntime_block_5145_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5145_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5152. -/
theorem endRuntime_block_5152 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5152) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5161_taken`. -/
def endRuntime_block_5161_taken_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5161. -/
theorem endRuntime_block_5161_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5183) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5161) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5183) (endRuntime_block_5161_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5183) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5183)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5161_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5183) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5161) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5183) (endRuntime_block_5161_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5161_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5161_fallthrough`. -/
def endRuntime_block_5161_fallthrough_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5161. -/
theorem endRuntime_block_5161_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5161) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5179) (endRuntime_block_5161_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 5183) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5179)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5161_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5161) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5179) (endRuntime_block_5161_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5161_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5179. -/
theorem endRuntime_block_5179 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5179) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5183`. -/
def endRuntime_block_5183_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad x1 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5183. -/
theorem endRuntime_block_5183 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10154) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5183) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10154) (endRuntime_block_5183_stack (mem := mem) (x1 := x1) (R := R)) mem (M aw x1 (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 5) (C + ((17) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 10154) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10154)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5183_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10154) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5183) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10154) (endRuntime_block_5183_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5183 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5190`. -/
def endRuntime_block_5190_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5190. -/
theorem endRuntime_block_5190 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5190) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x1 (endRuntime_block_5190_stack (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 0)) rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 11) x0)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 11) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sstore r2 hperm (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.mload r4 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 35254460948662957652813622441068026052908885352678643374192834455572783397049) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.log1 r9 (by native_decide) hperm (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r11⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5190_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5190) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x1 (endRuntime_block_5190_stack (R := R)) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 11) x0)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5190 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5236`. -/
def endRuntime_block_5236_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5236. -/
theorem endRuntime_block_5236 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5236) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_5236_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r11⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5236_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5236) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_5236_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5236 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5251`. -/
def endRuntime_block_5251_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat 15).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32))) :: x1 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5251`. -/
def endRuntime_block_5251_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.ofNat 15).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5251. -/
theorem endRuntime_block_5251 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5251) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x1 (endRuntime_block_5251_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (endRuntime_block_5251_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 15) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := RD.mstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r14⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5251_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5251) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x1 (endRuntime_block_5251_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (endRuntime_block_5251_memory (mem := mem) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5251 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5269`. -/
def endRuntime_block_5269_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((storageRead ee.codeOwner σ (UInt256.ofNat 10)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 5269. -/
theorem endRuntime_block_5269 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5269) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_5269_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 10) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r5⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5269_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5269) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_5269_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5269 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_5275_taken`. -/
def endRuntime_block_5275_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5275. -/
theorem endRuntime_block_5275_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5364) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5275) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5364) R (endRuntime_block_5275_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.keccak256 r12 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 5364) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5364)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5275_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5364) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5275) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5364) R (endRuntime_block_5275_taken_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5275_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_5275_fallthrough`. -/
def endRuntime_block_5275_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5275. -/
theorem endRuntime_block_5275_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5275) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5299) R (endRuntime_block_5275_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.keccak256 r12 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 5364) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5299)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5275_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5275) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5299) R (endRuntime_block_5275_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5275_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5299. -/
theorem endRuntime_block_5299 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5299) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 1512077989682546607471503411724198105487705) (width := 18) (op := .PUSH18) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 114) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.mstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := RD.mload r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r34 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5364`. -/
def endRuntime_block_5364_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `endRuntime_block_5364`. -/
def endRuntime_block_5364_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5364. -/
theorem endRuntime_block_5364 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5364) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x1 (endRuntime_block_5364_stack (R := R)) (endRuntime_block_5364_memory (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 0)) rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := RD.mstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r14 := r13.dup2 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.mstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.dup1 (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := RD.keccak256 r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sstore r22 hperm (by native_decide) (by evm_ov)
  have r24 := RD.mload r23 (by native_decide) (by evm_ov)
  have r25 := r24.pushConst (UInt256.ofNat 99986234382112180548053307940146098591310749102190014697170127658504464915040) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r26 := r25.swap2 (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := RD.log2 r27 (by native_decide) hperm (by evm_ov)
  have r29 := r28.pop (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r30⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5364_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5364) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x1 (endRuntime_block_5364_stack (R := R)) (endRuntime_block_5364_memory (mem := mem) (x0 := x0)) aw' rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5364 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_5433_taken`. -/
def endRuntime_block_5433_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5433. -/
theorem endRuntime_block_5433_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5522) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5433) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5522) R (endRuntime_block_5433_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.keccak256 r12 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 5522) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5522)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5433_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5522) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5433) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5522) R (endRuntime_block_5433_taken_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5433_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_5433_fallthrough`. -/
def endRuntime_block_5433_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5433. -/
theorem endRuntime_block_5433_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5433) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5457) R (endRuntime_block_5433_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.keccak256 r12 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.eq (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 5522) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5457)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5433_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5433) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5457) R (endRuntime_block_5433_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5433_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5457. -/
theorem endRuntime_block_5457 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5457) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 1512077989682546607471503411724198105487705) (width := 18) (op := .PUSH18) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 114) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.mstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := RD.mload r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r34 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 5522. -/
theorem endRuntime_block_5522_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5592) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5522) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5592) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5592) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5592)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5522_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5592) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5522) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5592) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5522_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5522. -/
theorem endRuntime_block_5522_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5522) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5533) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 5592) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5533)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5522_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5522) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5533) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5522_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5533. -/
theorem endRuntime_block_5533 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5533) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r11 := r10.dup3 (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 21487920629433384185126024805) (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r23 := r22.dup3 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.mstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := RD.mload r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.sub (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r33 := r32.add (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r34 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5592_taken`. -/
def endRuntime_block_5592_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) + (UInt256.ofNat 4)) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5592_taken`. -/
def endRuntime_block_5592_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5592. -/
theorem endRuntime_block_5592_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5667) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5592) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5667) (endRuntime_block_5592_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5592_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.timestamp (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sstore r8 hperm (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := RD.mload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := RD.mload r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.sub (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.swap3 (by native_decide) (by evm_ov)
  have r29 := r28.and (by native_decide) (by evm_ov)
  have r30 := r29.swap3 (by native_decide) (by evm_ov)
  have r31 := r30.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r32 := r31.swap3 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r34 := r33.dup1 (by native_decide) (by evm_ov)
  have r35 := r34.dup5 (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.swap4 (by native_decide) (by evm_ov)
  have r38 := r37.dup3 (by native_decide) (by evm_ov)
  have r39 := r38.swap1 (by native_decide) (by evm_ov)
  have r40 := r39.sub (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := r43.dup8 (by native_decide) (by evm_ov)
  have r45 := r44.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r46⟩ := r45.extcodesize (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  have r49 := r48.iszero (by native_decide) (by evm_ov)
  have r50 := r49.push2 (UInt256.ofNat 5667) (by native_decide) (by evm_ov)
  have r51 := r50.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5667)) r51 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5592_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5667) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5592) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5667) (endRuntime_block_5592_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5592_taken_memory (mem := mem)) aw' rdata (cA, (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5592_taken hstack hperm hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5592_fallthrough`. -/
def endRuntime_block_5592_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) + (UInt256.ofNat 4)) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5592_fallthrough`. -/
def endRuntime_block_5592_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5592. -/
theorem endRuntime_block_5592_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5592) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5663) (endRuntime_block_5592_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5592_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sstore r5 hperm (by native_decide) (by evm_ov)
  have r7 := r6.timestamp (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 9) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sstore r8 hperm (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := RD.sload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := RD.mload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := RD.mload r20 (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.sub (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.swap3 (by native_decide) (by evm_ov)
  have r29 := r28.and (by native_decide) (by evm_ov)
  have r30 := r29.swap3 (by native_decide) (by evm_ov)
  have r31 := r30.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r32 := r31.swap3 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r34 := r33.dup1 (by native_decide) (by evm_ov)
  have r35 := r34.dup5 (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.swap4 (by native_decide) (by evm_ov)
  have r38 := r37.dup3 (by native_decide) (by evm_ov)
  have r39 := r38.swap1 (by native_decide) (by evm_ov)
  have r40 := r39.sub (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := r41.dup2 (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := r43.dup8 (by native_decide) (by evm_ov)
  have r45 := r44.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r46⟩ := r45.extcodesize (by native_decide) (by evm_ov)
  have r47 := r46.iszero (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  have r49 := r48.iszero (by native_decide) (by evm_ov)
  have r50 := r49.push2 (UInt256.ofNat 5667) (by native_decide) (by evm_ov)
  have r51 := r50.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5663)) r51 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5592_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hperm : ee.perm = true)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.land (storageRead ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp)) (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5592) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5663) (endRuntime_block_5592_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5592_fallthrough_memory (mem := mem)) aw' rdata (cA, (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (UInt256.ofNat 8) (UInt256.ofNat 0)) (UInt256.ofNat 9) (UInt256.ofNat ee.header.timestamp))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5592_fallthrough hstack hperm hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5663. -/
theorem endRuntime_block_5663 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5663) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5667`. -/
def endRuntime_block_5667_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5667. -/
theorem endRuntime_block_5667 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5667) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5669) (endRuntime_block_5667_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5669)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5667_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5667) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5669) (endRuntime_block_5667_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5667 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 5669: gas (0x5a). No RD transition is asserted. Summaries resume at pc 5670 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 5670: call (0xf1). No RD transition is asserted. Summaries resume at pc 5671 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_5671_taken`. -/
def endRuntime_block_5671_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5671. -/
theorem endRuntime_block_5671_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5687) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5671) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5687) (endRuntime_block_5671_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5687) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5687)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5671_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5687) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5671) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5687) (endRuntime_block_5671_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5671_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5671_fallthrough`. -/
def endRuntime_block_5671_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5671. -/
theorem endRuntime_block_5671_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5671) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5678) (endRuntime_block_5671_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5687) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5678)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5671_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5671) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5678) (endRuntime_block_5671_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5671_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5678. -/
theorem endRuntime_block_5678 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5678) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5687_taken`. -/
def endRuntime_block_5687_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5687_taken`. -/
def endRuntime_block_5687_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5687. -/
theorem endRuntime_block_5687_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5771) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5687) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5771) (endRuntime_block_5687_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5687_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := r11.exp (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.sub (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.mload r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  have r31 := r30.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.mstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r41 := RD.mload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup1 (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := r43.sub (by native_decide) (by evm_ov)
  have r45 := r44.dup2 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r47 := r46.dup8 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r49⟩ := r48.extcodesize (by native_decide) (by evm_ov)
  have r50 := r49.iszero (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.iszero (by native_decide) (by evm_ov)
  have r53 := r52.push2 (UInt256.ofNat 5771) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5771)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5687_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5771) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5687) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5771) (endRuntime_block_5687_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5687_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5687_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5687_fallthrough`. -/
def endRuntime_block_5687_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5687_fallthrough`. -/
def endRuntime_block_5687_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5687. -/
theorem endRuntime_block_5687_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5687) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5767) (endRuntime_block_5687_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5687_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := r11.exp (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.sub (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.mload r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  have r31 := r30.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.mstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r41 := RD.mload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup1 (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := r43.sub (by native_decide) (by evm_ov)
  have r45 := r44.dup2 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r47 := r46.dup8 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r49⟩ := r48.extcodesize (by native_decide) (by evm_ov)
  have r50 := r49.iszero (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.iszero (by native_decide) (by evm_ov)
  have r53 := r52.push2 (UInt256.ofNat 5771) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5767)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5687_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 2)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5687) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5767) (endRuntime_block_5687_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5687_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5687_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5767. -/
theorem endRuntime_block_5767 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5767) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5771`. -/
def endRuntime_block_5771_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5771. -/
theorem endRuntime_block_5771 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5771) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5773) (endRuntime_block_5771_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5773)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5771_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5771) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5773) (endRuntime_block_5771_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5771 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 5773: gas (0x5a). No RD transition is asserted. Summaries resume at pc 5774 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 5774: call (0xf1). No RD transition is asserted. Summaries resume at pc 5775 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_5775_taken`. -/
def endRuntime_block_5775_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5775. -/
theorem endRuntime_block_5775_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5791) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5775) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5791) (endRuntime_block_5775_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5791) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5791)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5775_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5791) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5775) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5791) (endRuntime_block_5775_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5775_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5775_fallthrough`. -/
def endRuntime_block_5775_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5775. -/
theorem endRuntime_block_5775_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5775) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5782) (endRuntime_block_5775_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5791) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5782)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5775_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5775) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5782) (endRuntime_block_5775_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5775_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5782. -/
theorem endRuntime_block_5782 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5782) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5791_taken`. -/
def endRuntime_block_5791_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5791_taken`. -/
def endRuntime_block_5791_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5791. -/
theorem endRuntime_block_5791_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5875) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5791) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5875) (endRuntime_block_5791_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5791_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := r11.exp (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.sub (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.mload r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  have r31 := r30.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.mstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r41 := RD.mload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup1 (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := r43.sub (by native_decide) (by evm_ov)
  have r45 := r44.dup2 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r47 := r46.dup8 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r49⟩ := r48.extcodesize (by native_decide) (by evm_ov)
  have r50 := r49.iszero (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.iszero (by native_decide) (by evm_ov)
  have r53 := r52.push2 (UInt256.ofNat 5875) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5875)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5791_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5875) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5791) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5875) (endRuntime_block_5791_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5791_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5791_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5791_fallthrough`. -/
def endRuntime_block_5791_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5791_fallthrough`. -/
def endRuntime_block_5791_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5791. -/
theorem endRuntime_block_5791_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5791) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5871) (endRuntime_block_5791_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5791_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r9⟩ := RD.sload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r12 := r11.exp (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.div (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.sub (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r29 := RD.mload r28 (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  have r31 := r30.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.dup2 (by native_decide) (by evm_ov)
  have r36 := RD.mstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r41 := RD.mload r40 (by native_decide) (by evm_ov)
  have r42 := r41.dup1 (by native_decide) (by evm_ov)
  have r43 := r42.dup4 (by native_decide) (by evm_ov)
  have r44 := r43.sub (by native_decide) (by evm_ov)
  have r45 := r44.dup2 (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r47 := r46.dup8 (by native_decide) (by evm_ov)
  have r48 := r47.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r49⟩ := r48.extcodesize (by native_decide) (by evm_ov)
  have r50 := r49.iszero (by native_decide) (by evm_ov)
  have r51 := r50.dup1 (by native_decide) (by evm_ov)
  have r52 := r51.iszero (by native_decide) (by evm_ov)
  have r53 := r52.push2 (UInt256.ofNat 5875) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5871)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5791_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5791) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5871) (endRuntime_block_5791_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5791_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5791_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5871. -/
theorem endRuntime_block_5871 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5871) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5875`. -/
def endRuntime_block_5875_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5875. -/
theorem endRuntime_block_5875 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5875) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5877) (endRuntime_block_5875_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5877)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5875_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5875) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5877) (endRuntime_block_5875_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5875 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 5877: gas (0x5a). No RD transition is asserted. Summaries resume at pc 5878 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 5878: call (0xf1). No RD transition is asserted. Summaries resume at pc 5879 from a fresh symbolic RD state. -/

end endRuntimeBlocks
