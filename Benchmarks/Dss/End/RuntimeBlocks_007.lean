import Reasoning.SummaryPatterns
import Benchmarks.Dss.End.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace endRuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 3402. -/
theorem endRuntime_block_3402 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3402) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3411_taken`. -/
def endRuntime_block_3411_taken_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3411. -/
theorem endRuntime_block_3411_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 96))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3433) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3411) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3433) (endRuntime_block_3411_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3433) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3433)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3411_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 96))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3433) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3411) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3433) (endRuntime_block_3411_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3411_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3411_fallthrough`. -/
def endRuntime_block_3411_fallthrough_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3411. -/
theorem endRuntime_block_3411_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 96))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3411) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3429) (endRuntime_block_3411_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3433) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3429)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3411_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 96))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3411) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3429) (endRuntime_block_3411_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3411_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3429. -/
theorem endRuntime_block_3429 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3429) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3433_taken`. -/
def endRuntime_block_3433_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) + (UInt256.ofNat 36)) :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 160) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) :: (UInt256.ofNat 3647180086) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad x1 mem) :: (memLoad x1 mem) :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3433_taken`. -/
def endRuntime_block_3433_taken_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3433. -/
theorem endRuntime_block_3433_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3517) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3433) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3517) (endRuntime_block_3433_taken_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_3433_taken_memory (mem := mem) (x4 := x4)) (M (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 1823590043) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup8 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := RD.mload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.swap4 (by native_decide) (by evm_ov)
  have r24 := r23.pop (by native_decide) (by evm_ov)
  have r25 := r24.dup4 (by native_decide) (by evm_ov)
  have r26 := r25.swap3 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r28 := r27.swap3 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r32 := r31.shl (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.swap2 (by native_decide) (by evm_ov)
  have r36 := r35.push4 (UInt256.ofNat 3647180086) (by native_decide) (by evm_ov)
  have r37 := r36.swap2 (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r39 := r38.dup1 (by native_decide) (by evm_ov)
  have r40 := r39.dup4 (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := r41.swap3 (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r44 := r43.swap3 (by native_decide) (by evm_ov)
  have r45 := r44.swap2 (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.dup3 (by native_decide) (by evm_ov)
  have r48 := r47.swap1 (by native_decide) (by evm_ov)
  have r49 := r48.sub (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.dup2 (by native_decide) (by evm_ov)
  have r52 := r51.dup8 (by native_decide) (by evm_ov)
  have r53 := r52.dup8 (by native_decide) (by evm_ov)
  have r54 := r53.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r55⟩ := r54.extcodesize (by native_decide) (by evm_ov)
  have r56 := r55.iszero (by native_decide) (by evm_ov)
  have r57 := r56.dup1 (by native_decide) (by evm_ov)
  have r58 := r57.iszero (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 3517) (by native_decide) (by evm_ov)
  have r60 := r59.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3517)) r60 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3433_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3517) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3433) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3517) (endRuntime_block_3433_taken_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_3433_taken_memory (mem := mem) (x4 := x4)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3433_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3433_fallthrough`. -/
def endRuntime_block_3433_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) + (UInt256.ofNat 36)) :: (memLoad (UInt256.ofNat 64) (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 160) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) :: (UInt256.ofNat 3647180086) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad x1 mem) :: (memLoad x1 mem) :: x3 :: x4 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3433_fallthrough`. -/
def endRuntime_block_3433_fallthrough_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  (x4.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1823590043) (UInt256.ofNat 225)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3433. -/
theorem endRuntime_block_3433_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3433) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3513) (endRuntime_block_3433_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_3433_fallthrough_memory (mem := mem) (x4 := x4)) (M (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 1823590043) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 225) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup8 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := RD.mload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.swap4 (by native_decide) (by evm_ov)
  have r24 := r23.pop (by native_decide) (by evm_ov)
  have r25 := r24.dup4 (by native_decide) (by evm_ov)
  have r26 := r25.swap3 (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r28 := r27.swap3 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r32 := r31.shl (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.and (by native_decide) (by evm_ov)
  have r35 := r34.swap2 (by native_decide) (by evm_ov)
  have r36 := r35.push4 (UInt256.ofNat 3647180086) (by native_decide) (by evm_ov)
  have r37 := r36.swap2 (by native_decide) (by evm_ov)
  have r38 := r37.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r39 := r38.dup1 (by native_decide) (by evm_ov)
  have r40 := r39.dup4 (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := r41.swap3 (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r44 := r43.swap3 (by native_decide) (by evm_ov)
  have r45 := r44.swap2 (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.dup3 (by native_decide) (by evm_ov)
  have r48 := r47.swap1 (by native_decide) (by evm_ov)
  have r49 := r48.sub (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := r50.dup2 (by native_decide) (by evm_ov)
  have r52 := r51.dup8 (by native_decide) (by evm_ov)
  have r53 := r52.dup8 (by native_decide) (by evm_ov)
  have r54 := r53.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r55⟩ := r54.extcodesize (by native_decide) (by evm_ov)
  have r56 := r55.iszero (by native_decide) (by evm_ov)
  have r57 := r56.dup1 (by native_decide) (by evm_ov)
  have r58 := r57.iszero (by native_decide) (by evm_ov)
  have r59 := r58.push2 (UInt256.ofNat 3517) (by native_decide) (by evm_ov)
  have r60 := r59.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3513)) r60 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3433_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3433) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3513) (endRuntime_block_3433_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x3 := x3) (x4 := x4) (R := R)) (endRuntime_block_3433_fallthrough_memory (mem := mem) (x4 := x4)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3433_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3513. -/
theorem endRuntime_block_3513 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3513) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3517`. -/
def endRuntime_block_3517_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3517. -/
theorem endRuntime_block_3517 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3517) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3519) (endRuntime_block_3517_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3519)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3517_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3517) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3519) (endRuntime_block_3517_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3517 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 3519: gas (0x5a). No RD transition is asserted. Summaries resume at pc 3520 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 3520: call (0xf1). No RD transition is asserted. Summaries resume at pc 3521 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_3521_taken`. -/
def endRuntime_block_3521_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3521. -/
theorem endRuntime_block_3521_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3537) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3521) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3537) (endRuntime_block_3521_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3537) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3537)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3521_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3537) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3521) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3537) (endRuntime_block_3521_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3521_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3521_fallthrough`. -/
def endRuntime_block_3521_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3521. -/
theorem endRuntime_block_3521_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3521) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3528) (endRuntime_block_3521_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3537) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3528)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3521_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3521) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3528) (endRuntime_block_3521_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3521_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3528. -/
theorem endRuntime_block_3528 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3528) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3537_taken`. -/
def endRuntime_block_3537_taken_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3537. -/
theorem endRuntime_block_3537_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 160))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3559) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3537) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3559) (endRuntime_block_3537_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3559) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3559)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3537_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 160))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3559) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3537) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3559) (endRuntime_block_3537_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3537_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3537_fallthrough`. -/
def endRuntime_block_3537_fallthrough_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3537. -/
theorem endRuntime_block_3537_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 160))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3537) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3555) (endRuntime_block_3537_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3559) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3555)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3537_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 160))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3537) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3555) (endRuntime_block_3537_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3537_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3555. -/
theorem endRuntime_block_3555 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3555) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3559`. -/
def endRuntime_block_3559_stack {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 3649) :: (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) :: (UInt256.isZero (extCodeSizeWord σ (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1143195121) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1143195121) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) + (UInt256.ofNat 36)) :: (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1143195121) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 256) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) :: (UInt256.ofNat 1143195121) :: (UInt256.land x3 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: (memLoad ((UInt256.ofNat 32) + x1) mem) :: x3 :: x4 :: x5 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3559`. -/
def endRuntime_block_3559_memory {mem : ByteArray} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 1143195121) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3559. -/
theorem endRuntime_block_3559 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3559) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3644) (endRuntime_block_3559_stack (mem := mem) (σ := σ) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (endRuntime_block_3559_memory (mem := mem) (x5 := x5)) (M (M (M (M (M aw ((UInt256.ofNat 32) + x1) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := RD.mload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 1143195121) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup8 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  have r21 := RD.mload r20 (by native_decide) (by evm_ov)
  have r22 := r21.swap2 (by native_decide) (by evm_ov)
  have r23 := r22.swap3 (by native_decide) (by evm_ov)
  have r24 := r23.pop (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r26 := r25.swap2 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  have r30 := r29.swap2 (by native_decide) (by evm_ov)
  have r31 := r30.dup3 (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r36 := r35.shl (by native_decide) (by evm_ov)
  have r37 := r36.sub (by native_decide) (by evm_ov)
  have r38 := r37.dup9 (by native_decide) (by evm_ov)
  have r39 := r38.and (by native_decide) (by evm_ov)
  have r40 := r39.swap2 (by native_decide) (by evm_ov)
  have r41 := r40.push4 (UInt256.ofNat 1143195121) (by native_decide) (by evm_ov)
  have r42 := r41.swap2 (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  have r45 := r44.dup3 (by native_decide) (by evm_ov)
  have r46 := r45.add (by native_decide) (by evm_ov)
  have r47 := r46.swap3 (by native_decide) (by evm_ov)
  have r48 := r47.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r49 := r48.swap3 (by native_decide) (by evm_ov)
  have r50 := r49.swap1 (by native_decide) (by evm_ov)
  have r51 := r50.swap2 (by native_decide) (by evm_ov)
  have r52 := r51.swap1 (by native_decide) (by evm_ov)
  have r53 := r52.dup3 (by native_decide) (by evm_ov)
  have r54 := r53.swap1 (by native_decide) (by evm_ov)
  have r55 := r54.sub (by native_decide) (by evm_ov)
  have r56 := r55.add (by native_decide) (by evm_ov)
  have r57 := r56.dup2 (by native_decide) (by evm_ov)
  have r58 := r57.dup7 (by native_decide) (by evm_ov)
  have r59 := r58.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r60⟩ := r59.extcodesize (by native_decide) (by evm_ov)
  have r61 := r60.iszero (by native_decide) (by evm_ov)
  have r62 := r61.dup1 (by native_decide) (by evm_ov)
  have r63 := r62.iszero (by native_decide) (by evm_ov)
  have r64 := r63.push2 (UInt256.ofNat 3649) (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3644)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3559_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 19 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3559) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3644) (endRuntime_block_3559_stack (mem := mem) (σ := σ) (x1 := x1) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) (endRuntime_block_3559_memory (mem := mem) (x5 := x5)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3559 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3644_taken`. -/
def endRuntime_block_3644_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3644. -/
theorem endRuntime_block_3644_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3644) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_3644_taken_stack (R := R)) mem aw rdata (cA, σ) (k + 1) (C + ((10))) := by
  let r0 := h
  have r1 := r0.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  exact RD.normalizeCounters r1 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3644_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3644) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x0 (endRuntime_block_3644_taken_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3644_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3644_fallthrough`. -/
def endRuntime_block_3644_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3644. -/
theorem endRuntime_block_3644_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3644) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3645) (endRuntime_block_3644_fallthrough_stack (R := R)) mem aw rdata (cA, σ) (k + 1) (C + ((10))) := by
  let r0 := h
  have r1 := r0.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3645)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3644_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x1 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3644) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3645) (endRuntime_block_3644_fallthrough_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3644_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3645. -/
theorem endRuntime_block_3645 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3645) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3649`. -/
def endRuntime_block_3649_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3649. -/
theorem endRuntime_block_3649 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3649) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3651) (endRuntime_block_3649_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3651)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3649_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3649) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3651) (endRuntime_block_3649_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3649 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 3651: gas (0x5a). No RD transition is asserted. Summaries resume at pc 3652 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 3652: staticcall (0xfa). No RD transition is asserted. Summaries resume at pc 3653 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_3653_taken`. -/
def endRuntime_block_3653_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3653. -/
theorem endRuntime_block_3653_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3669) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3653) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3669) (endRuntime_block_3653_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3669) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3669)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3653_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3669) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3653) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3669) (endRuntime_block_3653_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3653_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3653_fallthrough`. -/
def endRuntime_block_3653_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3653. -/
theorem endRuntime_block_3653_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3653) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3660) (endRuntime_block_3653_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3669) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3660)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3653_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3653) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3660) (endRuntime_block_3653_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3653_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3660. -/
theorem endRuntime_block_3660 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3660) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3669_taken`. -/
def endRuntime_block_3669_taken_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3669. -/
theorem endRuntime_block_3669_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3692) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3669) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3692) (endRuntime_block_3669_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3692) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3692)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3669_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 256))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3692) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3669) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3692) (endRuntime_block_3669_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3669_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3669_fallthrough`. -/
def endRuntime_block_3669_fallthrough_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3669. -/
theorem endRuntime_block_3669_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 256))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3669) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3688) (endRuntime_block_3669_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 256) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 3692) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3688)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3669_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 256))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3669) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3688) (endRuntime_block_3669_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3669_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3688. -/
theorem endRuntime_block_3688 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3688) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3692`. -/
def endRuntime_block_3692_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) mem) :: (storageRead ee.codeOwner σ (UInt256.ofNat 1)) :: (memLoad (x1 + (UInt256.ofNat 224)) mem) :: (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) :: (memLoad (UInt256.ofNat 64) ((memLoad (x1 + (UInt256.ofNat 224)) mem).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4065207275) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: (memLoad (x1 + (UInt256.ofNat 160)) mem) :: x2 :: x3 :: (memLoad (x1 + (UInt256.ofNat 32)) mem) :: (memLoad x1 mem) :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3692`. -/
def endRuntime_block_3692_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} : ByteArray :=
  ((memLoad (x1 + (UInt256.ofNat 224)) mem).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4065207275) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3692. -/
theorem endRuntime_block_3692 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3692) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3772) (endRuntime_block_3692_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (endRuntime_block_3692_memory (ee := ee) (mem := mem) (σ := σ) (x1 := x1)) (M (M (M (M (M (M (M (M (M (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 160)) (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 224)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.mload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.dup3 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := RD.mload r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := r14.swap4 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := RD.mload r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r24 := r23.dup1 (by native_decide) (by evm_ov)
  have r25 := RD.mload r24 (by native_decide) (by evm_ov)
  have r26 := r25.push4 (UInt256.ofNat 4065207275) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r28 := r27.shl (by native_decide) (by evm_ov)
  have r29 := r28.dup2 (by native_decide) (by evm_ov)
  have r30 := RD.mstore r29 (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.swap3 (by native_decide) (by evm_ov)
  have r37 := r36.dup4 (by native_decide) (by evm_ov)
  have r38 := r37.and (by native_decide) (by evm_ov)
  have r39 := r38.swap4 (by native_decide) (by evm_ov)
  have r40 := r39.dup2 (by native_decide) (by evm_ov)
  have r41 := r40.add (by native_decide) (by evm_ov)
  have r42 := r41.dup5 (by native_decide) (by evm_ov)
  have r43 := r42.swap1 (by native_decide) (by evm_ov)
  have r44 := RD.mstore r43 (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r46 := r45.dup2 (by native_decide) (by evm_ov)
  have r47 := r46.add (by native_decide) (by evm_ov)
  have r48 := r47.swap4 (by native_decide) (by evm_ov)
  have r49 := r48.swap1 (by native_decide) (by evm_ov)
  have r50 := r49.swap4 (by native_decide) (by evm_ov)
  have r51 := RD.mstore r50 (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r53 := r52.dup4 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := r54.dup6 (by native_decide) (by evm_ov)
  have r56 := r55.swap1 (by native_decide) (by evm_ov)
  have r57 := RD.mstore r56 (by native_decide) (by evm_ov)
  have r58 := RD.mload r57 (by native_decide) (by evm_ov)
  have r59 := r58.swap6 (by native_decide) (by evm_ov)
  have r60 := r59.swap11 (by native_decide) (by evm_ov)
  have r61 := r60.pop (by native_decide) (by evm_ov)
  have r62 := r61.swap4 (by native_decide) (by evm_ov)
  have r63 := RD.swap9 r62 (by native_decide) (by evm_ov)
  have r64 := r63.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3772)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3692_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3692) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3772) (endRuntime_block_3692_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (endRuntime_block_3692_memory (ee := ee) (mem := mem) (σ := σ) (x1 := x1)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3692 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3772_taken`. -/
def endRuntime_block_3772_taken_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land x1 x3))) :: (UInt256.land x1 x3) :: (UInt256.ofNat 0) :: x4 :: ((UInt256.sub x0 x4) + (UInt256.ofNat 100)) :: x4 :: (UInt256.ofNat 0) :: (x0 + (UInt256.ofNat 100)) :: (UInt256.ofNat 4065207275) :: (UInt256.land x1 x3) :: x2 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3772. -/
theorem endRuntime_block_3772_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x1 x3)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3817) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3772) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3817) (endRuntime_block_3772_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.swap5 (by native_decide) (by evm_ov)
  have r2 := r1.swap7 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.swap5 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 4065207275) (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.dup4 (by native_decide) (by evm_ov)
  have r26 := r25.dup8 (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := r27.extcodesize (by native_decide) (by evm_ov)
  have r29 := r28.iszero (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.iszero (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 3817) (by native_decide) (by evm_ov)
  have r33 := r32.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3817)) r33 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3772_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x1 x3)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3817) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3772) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3817) (endRuntime_block_3772_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3772_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3772_fallthrough`. -/
def endRuntime_block_3772_fallthrough_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land x1 x3))) :: (UInt256.land x1 x3) :: (UInt256.ofNat 0) :: x4 :: ((UInt256.sub x0 x4) + (UInt256.ofNat 100)) :: x4 :: (UInt256.ofNat 0) :: (x0 + (UInt256.ofNat 100)) :: (UInt256.ofNat 4065207275) :: (UInt256.land x1 x3) :: x2 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3772. -/
theorem endRuntime_block_3772_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x1 x3)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3772) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3813) (endRuntime_block_3772_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.swap5 (by native_decide) (by evm_ov)
  have r2 := r1.swap7 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.swap5 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 4065207275) (by native_decide) (by evm_ov)
  have r10 := r9.swap2 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup4 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r17 := r16.swap3 (by native_decide) (by evm_ov)
  have r18 := r17.swap2 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.dup4 (by native_decide) (by evm_ov)
  have r26 := r25.dup8 (by native_decide) (by evm_ov)
  have r27 := r26.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r28⟩ := r27.extcodesize (by native_decide) (by evm_ov)
  have r29 := r28.iszero (by native_decide) (by evm_ov)
  have r30 := r29.dup1 (by native_decide) (by evm_ov)
  have r31 := r30.iszero (by native_decide) (by evm_ov)
  have r32 := r31.push2 (UInt256.ofNat 3817) (by native_decide) (by evm_ov)
  have r33 := r32.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3813)) r33 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3772_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land x1 x3)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3772) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3813) (endRuntime_block_3772_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3772_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3813. -/
theorem endRuntime_block_3813 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3813) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3817`. -/
def endRuntime_block_3817_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3817. -/
theorem endRuntime_block_3817 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3817) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3819) (endRuntime_block_3817_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3819)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3817_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3817) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3819) (endRuntime_block_3817_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3817 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 3819: gas (0x5a). No RD transition is asserted. Summaries resume at pc 3820 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 3820: call (0xf1). No RD transition is asserted. Summaries resume at pc 3821 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_3821_taken`. -/
def endRuntime_block_3821_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3821. -/
theorem endRuntime_block_3821_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3837) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3821) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3837) (endRuntime_block_3821_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3837) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3837)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3821_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3837) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3821) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3837) (endRuntime_block_3821_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3821_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3821_fallthrough`. -/
def endRuntime_block_3821_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3821. -/
theorem endRuntime_block_3821_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3821) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3828) (endRuntime_block_3821_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3837) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3828)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3821_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3821) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3828) (endRuntime_block_3821_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3821_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3828. -/
theorem endRuntime_block_3828 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3828) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3837`. -/
def endRuntime_block_3837_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x7.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4065207275) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32))) + (UInt256.ofNat 100)) :: (memLoad (UInt256.ofNat 64) (x7.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4065207275) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)) :: (UInt256.ofNat 4065207275) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x4 :: x5 :: x6 :: x7 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3837`. -/
def endRuntime_block_3837_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x7 : UInt256} : ByteArray :=
  (x7.toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 4065207275) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3837. -/
theorem endRuntime_block_3837 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3837) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3920) (endRuntime_block_3837_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (endRuntime_block_3837_memory (ee := ee) (mem := mem) (σ := σ) (x7 := x7)) (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r8⟩ := RD.sload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  have r11 := RD.mload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push4 (UInt256.ofNat 4065207275) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := RD.mstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.sub (by native_decide) (by evm_ov)
  have r22 := r21.swap3 (by native_decide) (by evm_ov)
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have r24 := r23.and (by native_decide) (by evm_ov)
  have r25 := r24.swap4 (by native_decide) (by evm_ov)
  have r26 := r25.dup2 (by native_decide) (by evm_ov)
  have r27 := r26.add (by native_decide) (by evm_ov)
  have r28 := r27.swap4 (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := r29.swap4 (by native_decide) (by evm_ov)
  have r31 := RD.mstore r30 (by native_decide) (by evm_ov)
  have r32 := r31.address (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r34 := r33.dup5 (by native_decide) (by evm_ov)
  have r35 := r34.add (by native_decide) (by evm_ov)
  have r36 := RD.mstore r35 (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r38 := r37.dup4 (by native_decide) (by evm_ov)
  have r39 := r38.add (by native_decide) (by evm_ov)
  have r40 := r39.dup11 (by native_decide) (by evm_ov)
  have r41 := r40.swap1 (by native_decide) (by evm_ov)
  have r42 := RD.mstore r41 (by native_decide) (by evm_ov)
  have r43 := RD.mload r42 (by native_decide) (by evm_ov)
  have r44 := r43.swap3 (by native_decide) (by evm_ov)
  have r45 := r44.and (by native_decide) (by evm_ov)
  have r46 := r45.swap4 (by native_decide) (by evm_ov)
  have r47 := r46.pop (by native_decide) (by evm_ov)
  have r48 := r47.push4 (UInt256.ofNat 4065207275) (by native_decide) (by evm_ov)
  have r49 := r48.swap3 (by native_decide) (by evm_ov)
  have r50 := r49.pop (by native_decide) (by evm_ov)
  have r51 := r50.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r52 := r51.dup1 (by native_decide) (by evm_ov)
  have r53 := r52.dup3 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := r54.swap3 (by native_decide) (by evm_ov)
  have r56 := r55.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r57 := r56.swap3 (by native_decide) (by evm_ov)
  have r58 := r57.swap1 (by native_decide) (by evm_ov)
  have r59 := r58.swap2 (by native_decide) (by evm_ov)
  have r60 := r59.swap1 (by native_decide) (by evm_ov)
  have r61 := r60.dup3 (by native_decide) (by evm_ov)
  have r62 := r61.swap1 (by native_decide) (by evm_ov)
  have r63 := r62.sub (by native_decide) (by evm_ov)
  have r64 := r63.add (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3920)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3837_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3837) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3920) (endRuntime_block_3837_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (R := R)) (endRuntime_block_3837_memory (ee := ee) (mem := mem) (σ := σ) (x7 := x7)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3837 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3920_taken`. -/
def endRuntime_block_3920_taken_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x5)) :: x5 :: x2 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3920. -/
theorem endRuntime_block_3920_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3936) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3920) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3936) (endRuntime_block_3920_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup8 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := r4.extcodesize (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3936) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3936)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3920_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3936) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3920) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3936) (endRuntime_block_3920_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3920_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3920_fallthrough`. -/
def endRuntime_block_3920_fallthrough_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x5)) :: x5 :: x2 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 3920. -/
theorem endRuntime_block_3920_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3920) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3932) (endRuntime_block_3920_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup8 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := r4.extcodesize (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3936) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3932)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3920_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3920) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3932) (endRuntime_block_3920_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3920_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3932. -/
theorem endRuntime_block_3932 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3932) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3936`. -/
def endRuntime_block_3936_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 3936. -/
theorem endRuntime_block_3936 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3936) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3938) (endRuntime_block_3936_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3938)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3936_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3936) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3938) (endRuntime_block_3936_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3936 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 3938: gas (0x5a). No RD transition is asserted. Summaries resume at pc 3939 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 3939: call (0xf1). No RD transition is asserted. Summaries resume at pc 3940 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_3940_taken`. -/
def endRuntime_block_3940_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3940. -/
theorem endRuntime_block_3940_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3956) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3940) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3956) (endRuntime_block_3940_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3956) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3956)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3940_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 3956) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3940) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3956) (endRuntime_block_3940_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3940_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3940_fallthrough`. -/
def endRuntime_block_3940_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 3940. -/
theorem endRuntime_block_3940_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3940) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3947) (endRuntime_block_3940_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3956) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3947)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3940_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3940) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3947) (endRuntime_block_3940_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_3940_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 3947. -/
theorem endRuntime_block_3947 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3947) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_3956_taken`. -/
def endRuntime_block_3956_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) + (UInt256.ofNat 36)) :: (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) :: (UInt256.ofNat 2746363844) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3956_taken`. -/
def endRuntime_block_3956_taken_memory {mem : ByteArray} {x9 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3956. -/
theorem endRuntime_block_3956_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 4038) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3956) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4038) (endRuntime_block_3956_taken_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (endRuntime_block_3956_taken_memory (mem := mem) (x9 := x9)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 686590961) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 226) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := RD.dup12 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.mstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap2 (by native_decide) (by evm_ov)
  have r27 := RD.mload r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := r29.swap3 (by native_decide) (by evm_ov)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.swap4 (by native_decide) (by evm_ov)
  have r33 := r32.pop (by native_decide) (by evm_ov)
  have r34 := r33.push4 (UInt256.ofNat 2746363844) (by native_decide) (by evm_ov)
  have r35 := r34.swap3 (by native_decide) (by evm_ov)
  have r36 := r35.pop (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r38 := r37.dup1 (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.swap3 (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r43 := r42.swap3 (by native_decide) (by evm_ov)
  have r44 := r43.swap2 (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.dup3 (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.dup2 (by native_decide) (by evm_ov)
  have r51 := r50.dup4 (by native_decide) (by evm_ov)
  have r52 := r51.dup8 (by native_decide) (by evm_ov)
  have r53 := r52.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r54⟩ := r53.extcodesize (by native_decide) (by evm_ov)
  have r55 := r54.iszero (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.iszero (by native_decide) (by evm_ov)
  have r58 := r57.push2 (UInt256.ofNat 4038) (by native_decide) (by evm_ov)
  have r59 := r58.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4038)) r59 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3956_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 4038) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3956) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4038) (endRuntime_block_3956_taken_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (endRuntime_block_3956_taken_memory (mem := mem) (x9 := x9)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3956_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_3956_fallthrough`. -/
def endRuntime_block_3956_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32))) + (UInt256.ofNat 36)) :: (memLoad (UInt256.ofNat 64) ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) :: (UInt256.ofNat 2746363844) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_3956_fallthrough`. -/
def endRuntime_block_3956_fallthrough_memory {mem : ByteArray} {x9 : UInt256} : ByteArray :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 686590961) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 3956. -/
theorem endRuntime_block_3956_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3956) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4034) (endRuntime_block_3956_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (endRuntime_block_3956_fallthrough_memory (mem := mem) (x9 := x9)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := RD.sload r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.push4 (UInt256.ofNat 686590961) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 226) (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := RD.mstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.sub (by native_decide) (by evm_ov)
  have r19 := RD.dup12 r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r23 := r22.dup4 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := RD.mstore r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap2 (by native_decide) (by evm_ov)
  have r27 := RD.mload r26 (by native_decide) (by evm_ov)
  have r28 := r27.swap2 (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := r29.swap3 (by native_decide) (by evm_ov)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.swap4 (by native_decide) (by evm_ov)
  have r33 := r32.pop (by native_decide) (by evm_ov)
  have r34 := r33.push4 (UInt256.ofNat 2746363844) (by native_decide) (by evm_ov)
  have r35 := r34.swap3 (by native_decide) (by evm_ov)
  have r36 := r35.pop (by native_decide) (by evm_ov)
  have r37 := r36.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r38 := r37.dup1 (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.add (by native_decide) (by evm_ov)
  have r41 := r40.swap3 (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r43 := r42.swap3 (by native_decide) (by evm_ov)
  have r44 := r43.swap2 (by native_decide) (by evm_ov)
  have r45 := r44.swap1 (by native_decide) (by evm_ov)
  have r46 := r45.dup3 (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.dup2 (by native_decide) (by evm_ov)
  have r51 := r50.dup4 (by native_decide) (by evm_ov)
  have r52 := r51.dup8 (by native_decide) (by evm_ov)
  have r53 := r52.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r54⟩ := r53.extcodesize (by native_decide) (by evm_ov)
  have r55 := r54.iszero (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.iszero (by native_decide) (by evm_ov)
  have r58 := r57.push2 (UInt256.ofNat 4038) (by native_decide) (by evm_ov)
  have r59 := r58.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4034)) r59 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_3956_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt256} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 3956) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4034) (endRuntime_block_3956_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (R := R)) (endRuntime_block_3956_fallthrough_memory (mem := mem) (x9 := x9)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_3956_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4034. -/
theorem endRuntime_block_4034 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4034) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_4038`. -/
def endRuntime_block_4038_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 4038. -/
theorem endRuntime_block_4038 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4038) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4040) (endRuntime_block_4038_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4040)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_4038_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4038) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4040) (endRuntime_block_4038_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_4038 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 4040: gas (0x5a). No RD transition is asserted. Summaries resume at pc 4041 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 4041: call (0xf1). No RD transition is asserted. Summaries resume at pc 4042 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_4042_taken`. -/
def endRuntime_block_4042_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4042. -/
theorem endRuntime_block_4042_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 4058) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4042) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4058) (endRuntime_block_4042_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 4058) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4058)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_4042_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 4058) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4042) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4058) (endRuntime_block_4042_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_4042_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_4042_fallthrough`. -/
def endRuntime_block_4042_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 4042. -/
theorem endRuntime_block_4042_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4042) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4049) (endRuntime_block_4042_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 4058) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4049)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_4042_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4042) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4049) (endRuntime_block_4042_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_4042_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 4049. -/
theorem endRuntime_block_4049 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4049) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_4058_taken`. -/
def endRuntime_block_4058_taken_stack {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) (memLoad (UInt256.ofNat 64) (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) :: (UInt256.ofNat 652224497) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_4058_taken`. -/
def endRuntime_block_4058_taken_memory {mem : ByteArray} {x11 : UInt256} : ByteArray :=
  (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4058. -/
theorem endRuntime_block_4058_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 4132) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4058) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4132) (endRuntime_block_4058_taken_stack (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (endRuntime_block_4058_taken_memory (mem := mem) (x11 := x11)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 652224497) (by native_decide) (by evm_ov)
  have r14 := r13.dup10 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := RD.mload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := RD.mstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.dup2 (by native_decide) (by evm_ov)
  have r29 := RD.mstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := r32.pop (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r37 := RD.mload r36 (by native_decide) (by evm_ov)
  have r38 := r37.dup1 (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.sub (by native_decide) (by evm_ov)
  have r41 := r40.dup2 (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r43 := r42.dup8 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := r44.extcodesize (by native_decide) (by evm_ov)
  have r46 := r45.iszero (by native_decide) (by evm_ov)
  have r47 := r46.dup1 (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 4132) (by native_decide) (by evm_ov)
  have r50 := r49.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4132)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_4058_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 4132) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4058) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4132) (endRuntime_block_4058_taken_stack (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (endRuntime_block_4058_taken_memory (mem := mem) (x11 := x11)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_4058_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_4058_fallthrough`. -/
def endRuntime_block_4058_fallthrough_stack {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {x7 : UInt256} {x8 : UInt256} {x9 : UInt256} {x10 : UInt256} {x11 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9))) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)) :: (UInt256.sub ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) (memLoad (UInt256.ofNat 64) (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32))) :: (memLoad (UInt256.ofNat 64) (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)) :: (UInt256.ofNat 0) :: ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem))) :: (UInt256.ofNat 652224497) :: (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9) :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_4058_fallthrough`. -/
def endRuntime_block_4058_fallthrough_memory {mem : ByteArray} {x11 : UInt256} : ByteArray :=
  (x11.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) (UInt256.ofNat 652224497)) (UInt256.ofNat 224)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 4058. -/
theorem endRuntime_block_4058_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4058) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4128) (endRuntime_block_4058_fallthrough_stack (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (endRuntime_block_4058_fallthrough_memory (mem := mem) (x11 := x11)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) mem)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r10 := r9.shl (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.push4 (UInt256.ofNat 652224497) (by native_decide) (by evm_ov)
  have r14 := r13.dup10 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := RD.mload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r19 := r18.and (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r21 := r20.shl (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := RD.mstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r25 := r24.add (by native_decide) (by evm_ov)
  have r26 := r25.dup1 (by native_decide) (by evm_ov)
  have r27 := r26.dup3 (by native_decide) (by evm_ov)
  have r28 := r27.dup2 (by native_decide) (by evm_ov)
  have r29 := RD.mstore r28 (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap2 (by native_decide) (by evm_ov)
  have r33 := r32.pop (by native_decide) (by evm_ov)
  have r34 := r33.pop (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r37 := RD.mload r36 (by native_decide) (by evm_ov)
  have r38 := r37.dup1 (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.sub (by native_decide) (by evm_ov)
  have r41 := r40.dup2 (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r43 := r42.dup8 (by native_decide) (by evm_ov)
  have r44 := r43.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r45⟩ := r44.extcodesize (by native_decide) (by evm_ov)
  have r46 := r45.iszero (by native_decide) (by evm_ov)
  have r47 := r46.dup1 (by native_decide) (by evm_ov)
  have r48 := r47.iszero (by native_decide) (by evm_ov)
  have r49 := r48.push2 (UInt256.ofNat 4132) (by native_decide) (by evm_ov)
  have r50 := r49.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4128)) r50 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_4058_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : UInt256} {R : List UInt256}
    (hstack : R.length + 20 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x9)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4058) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 4128) (endRuntime_block_4058_fallthrough_stack (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (x7 := x7) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (R := R)) (endRuntime_block_4058_fallthrough_memory (mem := mem) (x11 := x11)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_4058_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end endRuntimeBlocks
