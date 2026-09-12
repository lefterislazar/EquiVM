import Reasoning.SummaryPatterns
import Benchmarks.Dss.End.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace endRuntimeBlocks

/-- Final stack for bytecode block summary `endRuntime_block_5879_taken`. -/
def endRuntime_block_5879_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5879. -/
theorem endRuntime_block_5879_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5895) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5895) (endRuntime_block_5879_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5895) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5895)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5879_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5895) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5895) (endRuntime_block_5879_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5879_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5879_fallthrough`. -/
def endRuntime_block_5879_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5879. -/
theorem endRuntime_block_5879_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5886) (endRuntime_block_5879_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5895) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5886)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5879_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5886) (endRuntime_block_5879_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5879_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5886. -/
theorem endRuntime_block_5886 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5886) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5895_taken`. -/
def endRuntime_block_5895_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) + (UInt256.ofNat 4)) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5895_taken`. -/
def endRuntime_block_5895_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5895. -/
theorem endRuntime_block_5895_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5966) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5895) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5966) (endRuntime_block_5895_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5895_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.dup1 (by native_decide) (by evm_ov)
  have r9 := RD.mload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.mstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.mload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.sub (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.swap3 (by native_decide) (by evm_ov)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.swap5 (by native_decide) (by evm_ov)
  have r26 := r25.pop (by native_decide) (by evm_ov)
  have r27 := r26.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r28 := r27.swap4 (by native_decide) (by evm_ov)
  have r29 := r28.pop (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.dup4 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := r32.swap3 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r35 := r34.swap3 (by native_decide) (by evm_ov)
  have r36 := r35.swap2 (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.sub (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.dup2 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := r42.dup8 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := r44.extcodesize (by native_decide) (by evm_ov)
  have r46 := r45.iszero (by native_decide) (by evm_ov)
  have r47 := r46.dup1 (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 5966) (by native_decide) (by evm_ov)
  have r50 := r49.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5966)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5895_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5966) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5895) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5966) (endRuntime_block_5895_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5895_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5895_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5895_fallthrough`. -/
def endRuntime_block_5895_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) + (UInt256.ofNat 4)) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5895_fallthrough`. -/
def endRuntime_block_5895_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.ofNat 1763987465) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5895. -/
theorem endRuntime_block_5895_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5895) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5962) (endRuntime_block_5895_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5895_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.dup1 (by native_decide) (by evm_ov)
  have r9 := RD.mload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.mstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.mload r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.sub (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.swap3 (by native_decide) (by evm_ov)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.swap5 (by native_decide) (by evm_ov)
  have r26 := r25.pop (by native_decide) (by evm_ov)
  have r27 := r26.push4 (UInt256.ofNat 1763987465) (by native_decide) (by evm_ov)
  have r28 := r27.swap4 (by native_decide) (by evm_ov)
  have r29 := r28.pop (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.dup4 (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := r32.swap3 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r35 := r34.swap3 (by native_decide) (by evm_ov)
  have r36 := r35.swap2 (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.swap1 (by native_decide) (by evm_ov)
  have r39 := r38.sub (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.dup2 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := r42.dup8 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := r44.extcodesize (by native_decide) (by evm_ov)
  have r46 := r45.iszero (by native_decide) (by evm_ov)
  have r47 := r46.dup1 (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 5966) (by native_decide) (by evm_ov)
  have r50 := r49.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5962)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5895_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 4)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5895) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5962) (endRuntime_block_5895_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5895_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5895_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5962. -/
theorem endRuntime_block_5962 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5962) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5966`. -/
def endRuntime_block_5966_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 5966. -/
theorem endRuntime_block_5966 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5966) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5968) (endRuntime_block_5966_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5968)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5966_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5966) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5968) (endRuntime_block_5966_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5966 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 5968: gas (0x5a). No RD transition is asserted. Summaries resume at pc 5969 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 5969: call (0xf1). No RD transition is asserted. Summaries resume at pc 5970 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_5970_taken`. -/
def endRuntime_block_5970_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5970. -/
theorem endRuntime_block_5970_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5986) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5970) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5986) (endRuntime_block_5970_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5986) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5986)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5970_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 5986) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5970) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5986) (endRuntime_block_5970_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5970_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5970_fallthrough`. -/
def endRuntime_block_5970_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 5970. -/
theorem endRuntime_block_5970_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5970) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5977) (endRuntime_block_5970_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 5986) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 5977)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5970_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5970) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5977) (endRuntime_block_5970_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_5970_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 5977. -/
theorem endRuntime_block_5977 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5977) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_5986_taken`. -/
def endRuntime_block_5986_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5986_taken`. -/
def endRuntime_block_5986_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5986. -/
theorem endRuntime_block_5986_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6070) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5986) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6070) (endRuntime_block_5986_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5986_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
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
  have r53 := r52.push2 (UInt256.ofNat 6070) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6070)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5986_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6070) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5986) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6070) (endRuntime_block_5986_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5986_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5986_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_5986_fallthrough`. -/
def endRuntime_block_5986_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_5986_fallthrough`. -/
def endRuntime_block_5986_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 5986. -/
theorem endRuntime_block_5986_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5986) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6066) (endRuntime_block_5986_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5986_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
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
  have r53 := r52.push2 (UInt256.ofNat 6070) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6066)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_5986_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 6)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 5986) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6066) (endRuntime_block_5986_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_5986_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_5986_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6066. -/
theorem endRuntime_block_6066 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6066) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6070`. -/
def endRuntime_block_6070_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6070. -/
theorem endRuntime_block_6070 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6070) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6072) (endRuntime_block_6070_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6072)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6070_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6070) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6072) (endRuntime_block_6070_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6070 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 6072: gas (0x5a). No RD transition is asserted. Summaries resume at pc 6073 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 6073: call (0xf1). No RD transition is asserted. Summaries resume at pc 6074 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_6074_taken`. -/
def endRuntime_block_6074_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6074. -/
theorem endRuntime_block_6074_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6090) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6074) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6090) (endRuntime_block_6074_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6090) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6090)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6074_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6090) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6074) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6090) (endRuntime_block_6074_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6074_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6074_fallthrough`. -/
def endRuntime_block_6074_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6074. -/
theorem endRuntime_block_6074_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6074) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6081) (endRuntime_block_6074_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6090) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6081)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6074_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6074) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6081) (endRuntime_block_6074_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6074_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6081. -/
theorem endRuntime_block_6081 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6081) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6090_taken`. -/
def endRuntime_block_6090_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6090_taken`. -/
def endRuntime_block_6090_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6090. -/
theorem endRuntime_block_6090_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6174) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6090) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6174) (endRuntime_block_6090_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6090_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
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
  have r53 := r52.push2 (UInt256.ofNat 6174) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6174)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6090_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6174) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6090) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6174) (endRuntime_block_6090_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6090_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6090_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6090_fallthrough`. -/
def endRuntime_block_6090_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6090_fallthrough`. -/
def endRuntime_block_6090_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6090. -/
theorem endRuntime_block_6090_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6090) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6170) (endRuntime_block_6090_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6090_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
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
  have r53 := r52.push2 (UInt256.ofNat 6174) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6170)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6090_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 5)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6090) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6170) (endRuntime_block_6090_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6090_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6090_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6170. -/
theorem endRuntime_block_6170 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6170) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6174`. -/
def endRuntime_block_6174_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6174. -/
theorem endRuntime_block_6174 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6174) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6176) (endRuntime_block_6174_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6176)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6174_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6174) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6176) (endRuntime_block_6174_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6174 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 6176: gas (0x5a). No RD transition is asserted. Summaries resume at pc 6177 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 6177: call (0xf1). No RD transition is asserted. Summaries resume at pc 6178 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_6178_taken`. -/
def endRuntime_block_6178_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6178. -/
theorem endRuntime_block_6178_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6194) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6178) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6194) (endRuntime_block_6178_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6194) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6194)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6178_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6194) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6178) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6194) (endRuntime_block_6178_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6178_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6178_fallthrough`. -/
def endRuntime_block_6178_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6178. -/
theorem endRuntime_block_6178_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6178) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6185) (endRuntime_block_6178_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6194) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6185)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6178_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6178) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6185) (endRuntime_block_6178_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6178_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6185. -/
theorem endRuntime_block_6185 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6185) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6194_taken`. -/
def endRuntime_block_6194_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6194_taken`. -/
def endRuntime_block_6194_taken_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6194. -/
theorem endRuntime_block_6194_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6278) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6194) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6278) (endRuntime_block_6194_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6194_taken_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
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
  have r53 := r52.push2 (UInt256.ofNat 6278) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6278)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6194_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6278) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6194) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6278) (endRuntime_block_6194_taken_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6194_taken_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6194_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6194_fallthrough`. -/
def endRuntime_block_6194_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))) :: (memLoad (UInt256.ofNat 64) ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) :: (UInt256.ofNat 1763987465) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0))))) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6194_fallthrough`. -/
def endRuntime_block_6194_fallthrough_memory {mem : ByteArray} : ByteArray :=
  ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 1763987465)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6194. -/
theorem endRuntime_block_6194_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6194) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6274) (endRuntime_block_6194_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6194_fallthrough_memory (mem := mem)) (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
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
  have r53 := r52.push2 (UInt256.ofNat 6278) (by native_decide) (by evm_ov)
  have r54 := r53.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6274)) r54 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6194_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.div (storageRead ee.codeOwner σ (UInt256.ofNat 7)) (UInt256.exp (UInt256.ofNat 256) (UInt256.ofNat 0)))))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6194) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6274) (endRuntime_block_6194_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (R := R)) (endRuntime_block_6194_fallthrough_memory (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6194_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6274. -/
theorem endRuntime_block_6274 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6274) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6278`. -/
def endRuntime_block_6278_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6278. -/
theorem endRuntime_block_6278 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6278) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6280) (endRuntime_block_6278_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6280)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6278_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6278) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6280) (endRuntime_block_6278_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6278 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 6280: gas (0x5a). No RD transition is asserted. Summaries resume at pc 6281 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 6281: call (0xf1). No RD transition is asserted. Summaries resume at pc 6282 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_6282_taken`. -/
def endRuntime_block_6282_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6282. -/
theorem endRuntime_block_6282_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6298) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6282) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6298) (endRuntime_block_6282_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6298) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6298)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6282_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6298) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6282) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6298) (endRuntime_block_6282_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6282_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6282_fallthrough`. -/
def endRuntime_block_6282_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6282. -/
theorem endRuntime_block_6282_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6282) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6289) (endRuntime_block_6282_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6298) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6289)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6282_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6282) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6289) (endRuntime_block_6282_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6282_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6289. -/
theorem endRuntime_block_6289 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6289) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6298`. -/
def endRuntime_block_6298_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6298. -/
theorem endRuntime_block_6298 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6298) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 x4 (endRuntime_block_6298_stack (R := R)) mem (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 0)) rdata (cA, σ) (k + 13) (C + ((35) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (UInt256.ofNat 0)) + (375 + 8 * (UInt256.ofNat 0).toNat + 1 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := RD.mload r4 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 15846720854843032105251646702598932867924719938341352344186736728916659600346) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.pop (by native_decide) (by evm_ov)
  have r12 := RD.log1 r11 (by native_decide) hperm (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r13 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6298_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6298) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x4 (endRuntime_block_6298_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6298 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6345. -/
theorem endRuntime_block_6345_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (UInt256.ofNat 11)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6413) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6345) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6413) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 11) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6413) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6413)) r5 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6345_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (UInt256.ofNat 11)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6413) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6345) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6413) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6345_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6345. -/
theorem endRuntime_block_6345_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (UInt256.ofNat 11)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6345) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6353) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 11) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6413) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6353)) r5 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6345_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (UInt256.ofNat 11)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6345) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6353) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6345_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6353. -/
theorem endRuntime_block_6353 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6353) R mem aw rdata (cA, σ) k C)
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
  have r14 := r13.push1 (UInt256.ofNat 13) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 5500907680949753345960233497199) (width := 13) (op := .PUSH13) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 152) (by native_decide) (by evm_ov)
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

/-- Final stack for bytecode block summary `endRuntime_block_6413`. -/
def endRuntime_block_6413_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1000000000000000000000000000) :: x0 :: (UInt256.ofNat 6462) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))) :: (UInt256.ofNat ee.source.val) :: (UInt256.ofNat 3140843579) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6413. -/
theorem endRuntime_block_6413 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10170) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6413) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10170) (endRuntime_block_6413_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.sub (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.and (by native_decide) (by evm_ov)
  have r14 := r13.swap2 (by native_decide) (by evm_ov)
  have r15 := r14.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r16 := r15.swap2 (by native_decide) (by evm_ov)
  have r17 := r16.caller (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.push2 (UInt256.ofNat 6462) (by native_decide) (by evm_ov)
  have r21 := r20.dup6 (by native_decide) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 1000000000000000000000000000) (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 10170) (by native_decide) (by evm_ov)
  have r24 := r23.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10170)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6413_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10170) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6413) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10170) (endRuntime_block_6413_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6413 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6462_taken`. -/
def endRuntime_block_6462_taken_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x4)) :: x4 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))))) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))))) :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6462_taken`. -/
def endRuntime_block_6462_taken_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6462. -/
theorem endRuntime_block_6462_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x4))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6548) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6462) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6548) (endRuntime_block_6462_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_6462_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup5 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := RD.mstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.dup4 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.dup2 (by native_decide) (by evm_ov)
  have r33 := RD.mstore r32 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r35 := r34.add (by native_decide) (by evm_ov)
  have r36 := r35.dup3 (by native_decide) (by evm_ov)
  have r37 := r36.dup2 (by native_decide) (by evm_ov)
  have r38 := RD.mstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.swap4 (by native_decide) (by evm_ov)
  have r42 := r41.pop (by native_decide) (by evm_ov)
  have r43 := r42.pop (by native_decide) (by evm_ov)
  have r44 := r43.pop (by native_decide) (by evm_ov)
  have r45 := r44.pop (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r48 := RD.mload r47 (by native_decide) (by evm_ov)
  have r49 := r48.dup1 (by native_decide) (by evm_ov)
  have r50 := r49.dup4 (by native_decide) (by evm_ov)
  have r51 := r50.sub (by native_decide) (by evm_ov)
  have r52 := r51.dup2 (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r54 := r53.dup8 (by native_decide) (by evm_ov)
  have r55 := r54.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r56⟩ := r55.extcodesize (by native_decide) (by evm_ov)
  have r57 := r56.iszero (by native_decide) (by evm_ov)
  have r58 := r57.dup1 (by native_decide) (by evm_ov)
  have r59 := r58.iszero (by native_decide) (by evm_ov)
  have r60 := r59.push2 (UInt256.ofNat 6548) (by native_decide) (by evm_ov)
  have r61 := r60.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6548)) r61 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6462_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x4))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6548) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6462) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6548) (endRuntime_block_6462_taken_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_6462_taken_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6462_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6462_fallthrough`. -/
def endRuntime_block_6462_fallthrough_stack {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x4)) :: x4 :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))))) (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))))) :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6462_fallthrough`. -/
def endRuntime_block_6462_fallthrough_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x2).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) x3) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))).toNat 32) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6462. -/
theorem endRuntime_block_6462_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x4))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6462) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6544) (endRuntime_block_6462_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_6462_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) (⟨32⟩ : UInt256)) ((UInt256.ofNat 32) + ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)))) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r8 := r7.shl (by native_decide) (by evm_ov)
  have r9 := r8.dup2 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.dup5 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := RD.mstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.dup4 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.dup2 (by native_decide) (by evm_ov)
  have r33 := RD.mstore r32 (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r35 := r34.add (by native_decide) (by evm_ov)
  have r36 := r35.dup3 (by native_decide) (by evm_ov)
  have r37 := r36.dup2 (by native_decide) (by evm_ov)
  have r38 := RD.mstore r37 (by native_decide) (by evm_ov)
  have r39 := r38.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.swap4 (by native_decide) (by evm_ov)
  have r42 := r41.pop (by native_decide) (by evm_ov)
  have r43 := r42.pop (by native_decide) (by evm_ov)
  have r44 := r43.pop (by native_decide) (by evm_ov)
  have r45 := r44.pop (by native_decide) (by evm_ov)
  have r46 := r45.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r47 := r46.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r48 := RD.mload r47 (by native_decide) (by evm_ov)
  have r49 := r48.dup1 (by native_decide) (by evm_ov)
  have r50 := r49.dup4 (by native_decide) (by evm_ov)
  have r51 := r50.sub (by native_decide) (by evm_ov)
  have r52 := r51.dup2 (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r54 := r53.dup8 (by native_decide) (by evm_ov)
  have r55 := r54.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r56⟩ := r55.extcodesize (by native_decide) (by evm_ov)
  have r57 := r56.iszero (by native_decide) (by evm_ov)
  have r58 := r57.dup1 (by native_decide) (by evm_ov)
  have r59 := r58.iszero (by native_decide) (by evm_ov)
  have r60 := r59.push2 (UInt256.ofNat 6548) (by native_decide) (by evm_ov)
  have r61 := r60.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6544)) r61 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6462_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x4))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6462) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6544) (endRuntime_block_6462_fallthrough_stack (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_6462_fallthrough_memory (mem := mem) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6462_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6544. -/
theorem endRuntime_block_6544 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6544) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6548`. -/
def endRuntime_block_6548_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 6548. -/
theorem endRuntime_block_6548 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6548) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6550) (endRuntime_block_6548_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6550)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6548_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6548) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6550) (endRuntime_block_6548_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6548 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 6550: gas (0x5a). No RD transition is asserted. Summaries resume at pc 6551 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 6551: call (0xf1). No RD transition is asserted. Summaries resume at pc 6552 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_6552_taken`. -/
def endRuntime_block_6552_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6552. -/
theorem endRuntime_block_6552_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6568) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6552) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6568) (endRuntime_block_6552_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6568) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6568)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6552_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6568) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6552) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6568) (endRuntime_block_6552_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6552_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6552_fallthrough`. -/
def endRuntime_block_6552_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 6552. -/
theorem endRuntime_block_6552_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6552) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6559) (endRuntime_block_6552_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 6568) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6559)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6552_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6552) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6559) (endRuntime_block_6552_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_6552_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6559. -/
theorem endRuntime_block_6559 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6559) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_6568`. -/
def endRuntime_block_6568_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) :: (UInt256.ofNat 6599) :: x4 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_6568`. -/
def endRuntime_block_6568_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6568. -/
theorem endRuntime_block_6568 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10092) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6568) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10092) (endRuntime_block_6568_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (R := R)) (endRuntime_block_6568_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.caller (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.push2 (UInt256.ofNat 6599) (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := r17.pop (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.push2 (UInt256.ofNat 10092) (by native_decide) (by evm_ov)
  have r23 := r22.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10092)) r23 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6568_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10092) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6568) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10092) (endRuntime_block_6568_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (R := R)) (endRuntime_block_6568_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6568 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6599`. -/
def endRuntime_block_6599_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `endRuntime_block_6599`. -/
def endRuntime_block_6599_memory {ee : ExecutionEnv} {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  (x1.toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6599. -/
theorem endRuntime_block_6599 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6599) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x2 (endRuntime_block_6599_stack (R := R)) (endRuntime_block_6599_memory (ee := ee) (mem := mem) (x1 := x1)) (M (M (M (M (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32)) ((UInt256.sub (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (memLoad (UInt256.ofNat 64) (x1.toByteArray.write 0 ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32))) + (UInt256.ofNat 32))) rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) x0)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.caller (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := r13.dup3 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := RD.keccak256 r15 (by native_decide) (by evm_ov)
  have r17 := r16.swap4 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.swap4 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  have r22 := RD.mload r21 (by native_decide) (by evm_ov)
  have r23 := r22.dup5 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := RD.mstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := RD.mload r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.swap3 (by native_decide) (by evm_ov)
  have r30 := r29.pushConst (UInt256.ofNat 32413705573444452749964784915662512924629124419856669116056918598247152483852) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r31 := r30.swap3 (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := r32.dup3 (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.add (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  have r38 := RD.log2 r37 (by native_decide) hperm (by evm_ov)
  have r39 := r38.pop (by native_decide) (by evm_ov)
  have r40 := r39.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r40⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6599_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6599) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x2 (endRuntime_block_6599_stack (R := R)) (endRuntime_block_6599_memory (ee := ee) (mem := mem) (x1 := x1)) aw' rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 16).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) x0)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6599 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6675`. -/
def endRuntime_block_6675_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 6))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6675. -/
theorem endRuntime_block_6675 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6675) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_6675_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 6) (by native_decide) (by evm_ov)
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
theorem endRuntime_block_6675_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6675) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_6675_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6675 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_6690`. -/
def endRuntime_block_6690_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 7))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 6690. -/
theorem endRuntime_block_6690 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6690) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_6690_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
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
theorem endRuntime_block_6690_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6690) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_6690_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6690 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_6705_taken`. -/
def endRuntime_block_6705_taken_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 12).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6705. -/
theorem endRuntime_block_6705_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6795) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6705) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6795) (x0 :: x1 :: R) (endRuntime_block_6705_taken_memory (mem := mem) (x1 := x1)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 6795) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6795)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6705_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 6795) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6705) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6795) (x0 :: x1 :: R) (endRuntime_block_6705_taken_memory (mem := mem) (x1 := x1)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6705_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_6705_fallthrough`. -/
def endRuntime_block_6705_fallthrough_memory {mem : ByteArray} {x1 : UInt256} : ByteArray :=
  ((UInt256.ofNat 12).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 6705. -/
theorem endRuntime_block_6705_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6705) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6725) (x0 :: x1 :: R) (endRuntime_block_6705_fallthrough_memory (mem := mem) (x1 := x1)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 12) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 6795) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 6725)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_6705_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 12).toByteArray.write 0 (x1.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6705) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6725) (x0 :: x1 :: R) (endRuntime_block_6705_fallthrough_memory (mem := mem) (x1 := x1)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_6705_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 6725. -/
theorem endRuntime_block_6725 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 6725) R mem aw rdata (cA, σ) k C)
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
  have r14 := r13.push1 (UInt256.ofNat 23) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 1662547331793263672767660296024730882676930893819124057) (width := 23) (op := .PUSH23) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 74) (by native_decide) (by evm_ov)
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

end endRuntimeBlocks
