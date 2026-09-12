import Reasoning.SummaryPatterns
import Benchmarks.Dss.End.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace endRuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 7690. -/
theorem endRuntime_block_7690_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (storageRead ee.codeOwner σ (UInt256.ofNat 8))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7690) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7699) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 7760) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7699)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7690_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (storageRead ee.codeOwner σ (UInt256.ofNat 8))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7690) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7699) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_7690_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7699. -/
theorem endRuntime_block_7699 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7699) R mem aw rdata (cA, σ) k C)
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
  have r14 := r13.push1 (UInt256.ofNat 14) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 1408232366394249557190267185493605) (width := 14) (op := .PUSH14) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
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

/-- Final stack for bytecode block summary `endRuntime_block_7760_taken`. -/
def endRuntime_block_7760_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32))) + (UInt256.ofNat 68)) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.ofNat 64) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) :: (UInt256.ofNat 606387804) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_7760_taken`. -/
def endRuntime_block_7760_taken_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 7760. -/
theorem endRuntime_block_7760_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7843) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7760) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7843) (endRuntime_block_7760_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (endRuntime_block_7760_taken_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.mload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push4 (UInt256.ofNat 151596951) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 226) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.dup5 (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := RD.mstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.caller (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.add (by native_decide) (by evm_ov)
  have r22 := RD.mstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.dup2 (by native_decide) (by evm_ov)
  have r24 := RD.mload r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r26 := r25.swap4 (by native_decide) (by evm_ov)
  have r27 := r26.dup5 (by native_decide) (by evm_ov)
  have r28 := r27.swap4 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r32 := r31.shl (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.swap2 (by native_decide) (by evm_ov)
  have r36 := r35.and (by native_decide) (by evm_ov)
  have r37 := r36.swap3 (by native_decide) (by evm_ov)
  have r38 := r37.push4 (UInt256.ofNat 606387804) (by native_decide) (by evm_ov)
  have r39 := r38.swap3 (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r41 := r40.dup1 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := r43.swap4 (by native_decide) (by evm_ov)
  have r45 := r44.swap3 (by native_decide) (by evm_ov)
  have r46 := r45.dup3 (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.dup2 (by native_decide) (by evm_ov)
  have r51 := r50.dup8 (by native_decide) (by evm_ov)
  have r52 := r51.dup8 (by native_decide) (by evm_ov)
  have r53 := r52.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r54⟩ := r53.extcodesize (by native_decide) (by evm_ov)
  have r55 := r54.iszero (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.iszero (by native_decide) (by evm_ov)
  have r58 := r57.push2 (UInt256.ofNat 7843) (by native_decide) (by evm_ov)
  have r59 := r58.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7843)) r59 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7760_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7843) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7760) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7843) (endRuntime_block_7760_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (endRuntime_block_7760_taken_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_7760_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_7760_fallthrough`. -/
def endRuntime_block_7760_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: ((UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32))) + (UInt256.ofNat 68)) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)) :: (UInt256.ofNat 64) :: ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) :: (UInt256.ofNat 606387804) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (UInt256.ofNat 0) :: (UInt256.ofNat 0) :: x0 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_7760_fallthrough`. -/
def endRuntime_block_7760_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x0.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 151596951) (UInt256.ofNat 226)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 7760. -/
theorem endRuntime_block_7760_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7760) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7839) (endRuntime_block_7760_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (endRuntime_block_7760_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0)) (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.mload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push4 (UInt256.ofNat 151596951) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 226) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.dup5 (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  have r17 := RD.mstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.caller (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := r20.add (by native_decide) (by evm_ov)
  have r22 := RD.mstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.dup2 (by native_decide) (by evm_ov)
  have r24 := RD.mload r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r26 := r25.swap4 (by native_decide) (by evm_ov)
  have r27 := r26.dup5 (by native_decide) (by evm_ov)
  have r28 := r27.swap4 (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r32 := r31.shl (by native_decide) (by evm_ov)
  have r33 := r32.sub (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.swap2 (by native_decide) (by evm_ov)
  have r36 := r35.and (by native_decide) (by evm_ov)
  have r37 := r36.swap3 (by native_decide) (by evm_ov)
  have r38 := r37.push4 (UInt256.ofNat 606387804) (by native_decide) (by evm_ov)
  have r39 := r38.swap3 (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r41 := r40.dup1 (by native_decide) (by evm_ov)
  have r42 := r41.dup4 (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := r43.swap4 (by native_decide) (by evm_ov)
  have r45 := r44.swap3 (by native_decide) (by evm_ov)
  have r46 := r45.dup3 (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.sub (by native_decide) (by evm_ov)
  have r49 := r48.add (by native_decide) (by evm_ov)
  have r50 := r49.dup2 (by native_decide) (by evm_ov)
  have r51 := r50.dup8 (by native_decide) (by evm_ov)
  have r52 := r51.dup8 (by native_decide) (by evm_ov)
  have r53 := r52.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r54⟩ := r53.extcodesize (by native_decide) (by evm_ov)
  have r55 := r54.iszero (by native_decide) (by evm_ov)
  have r56 := r55.dup1 (by native_decide) (by evm_ov)
  have r57 := r56.iszero (by native_decide) (by evm_ov)
  have r58 := r57.push2 (UInt256.ofNat 7843) (by native_decide) (by evm_ov)
  have r59 := r58.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7839)) r59 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7760_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 15 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7760) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7839) (endRuntime_block_7760_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (endRuntime_block_7760_fallthrough_memory (ee := ee) (mem := mem) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_7760_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7839. -/
theorem endRuntime_block_7839 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7839) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_7843`. -/
def endRuntime_block_7843_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 7843. -/
theorem endRuntime_block_7843 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7843) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7845) (endRuntime_block_7843_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7845)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7843_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7843) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7845) (endRuntime_block_7843_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7843 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 7845: gas (0x5a). No RD transition is asserted. Summaries resume at pc 7846 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 7846: call (0xf1). No RD transition is asserted. Summaries resume at pc 7847 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_7847_taken`. -/
def endRuntime_block_7847_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7847. -/
theorem endRuntime_block_7847_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7863) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7847) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7863) (endRuntime_block_7847_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7863) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7863)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7847_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7863) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7847) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7863) (endRuntime_block_7847_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7847_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_7847_fallthrough`. -/
def endRuntime_block_7847_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7847. -/
theorem endRuntime_block_7847_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7847) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7854) (endRuntime_block_7847_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 7863) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7854)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7847_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7847) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7854) (endRuntime_block_7847_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7847_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7854. -/
theorem endRuntime_block_7854 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7854) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_7863_taken`. -/
def endRuntime_block_7863_taken_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7863. -/
theorem endRuntime_block_7863_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7885) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7863) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7885) (endRuntime_block_7863_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 7885) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7885)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7863_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7885) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7863) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7885) (endRuntime_block_7863_taken_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7863_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_7863_fallthrough`. -/
def endRuntime_block_7863_fallthrough_stack {mem : ByteArray} {rdata : ByteArray} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat rdata.size) :: (memLoad (UInt256.ofNat 64) mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7863. -/
theorem endRuntime_block_7863_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7863) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7881) (endRuntime_block_7863_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 14) (C + ((42) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := r10.lt (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 7885) (by native_decide) (by evm_ov)
  have r14 := r13.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7881)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7863_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.ofNat rdata.size) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7863) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7881) (endRuntime_block_7863_fallthrough_stack (mem := mem) (rdata := rdata) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7863_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7881. -/
theorem endRuntime_block_7881 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7881) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_7885_taken`. -/
def endRuntime_block_7885_taken_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x1 + (UInt256.ofNat 32)) mem) :: (memLoad x1 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7885. -/
theorem endRuntime_block_7885_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 32)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7969) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7885) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7969) (endRuntime_block_7885_taken_stack (mem := mem) (x1 := x1) (R := R)) mem (M (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 18) (C + ((56) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.mload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := RD.mload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.pop (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  have r16 := r15.iszero (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 7969) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7969)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7885_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 32)) mem)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 7969) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7885) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7969) (endRuntime_block_7885_taken_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7885_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_7885_fallthrough`. -/
def endRuntime_block_7885_fallthrough_stack {mem : ByteArray} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (x1 + (UInt256.ofNat 32)) mem) :: (memLoad x1 mem) :: R)

/-- Automatically generated RD summary for bytecode block at pc 7885. -/
theorem endRuntime_block_7885_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 32)) mem)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7885) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7906) (endRuntime_block_7885_fallthrough_stack (mem := mem) (x1 := x1) (R := R)) mem (M (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 18) (C + ((56) + (memExpansionCost aw x1 (⟨32⟩ : UInt256)) + (memExpansionCost (M aw x1 (⟨32⟩ : UInt256)) (x1 + (UInt256.ofNat 32)) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.mload r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.swap2 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := RD.mload r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.swap3 (by native_decide) (by evm_ov)
  have r12 := r11.pop (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  have r16 := r15.iszero (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 7969) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7906)) r18 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7885_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (memLoad (x1 + (UInt256.ofNat 32)) mem)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7885) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7906) (endRuntime_block_7885_fallthrough_stack (mem := mem) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7885_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7906. -/
theorem endRuntime_block_7906 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7906) R mem aw rdata (cA, σ) k C)
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
  have r14 := r13.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 92289916358440441735647045770509906543) (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
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

/-- Automatically generated RD summary for bytecode block at pc 7969. -/
theorem endRuntime_block_7969_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8041) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7969) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8041) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.gt (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8041) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8041)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7969_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8041) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7969) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8041) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7969_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7969. -/
theorem endRuntime_block_7969_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7969) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7982) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.gt (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8041) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 7982)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_7969_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x1 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 255)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7969) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7982) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_7969_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 7982. -/
theorem endRuntime_block_7982 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 7982) R mem aw rdata (cA, σ) k C)
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
  have r19 := r18.pushConst (UInt256.ofNat 21487920629507395907578785655) (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
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

/-- Final stack for bytecode block summary `endRuntime_block_8041`. -/
def endRuntime_block_8041_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.sub (UInt256.ofNat 0) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 32419069) (UInt256.ofNat 230)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 132)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 164)).toNat 32)) :: (memLoad (UInt256.ofNat 64) mem) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 1)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_8041`. -/
def endRuntime_block_8041_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.sub (UInt256.ofNat 0) x1).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 4))).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 (x2.toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 32419069) (UInt256.ofNat 230)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 132)).toNat 32) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 164)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8041. -/
theorem endRuntime_block_8041 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8041) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8122) (endRuntime_block_8041_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (endRuntime_block_8041_memory (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 100)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 132)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) mem) + (UInt256.ofNat 164)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.dup1 (by native_decide) (by evm_ov)
  have r9 := RD.mload r8 (by native_decide) (by evm_ov)
  have r10 := r9.push4 (UInt256.ofNat 32419069) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 230) (by native_decide) (by evm_ov)
  have r12 := r11.shl (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := RD.mstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.swap3 (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := r17.dup8 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := RD.mstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.caller (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r23 := r22.dup5 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := RD.mstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r29 := r28.dup5 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := RD.mstore r30 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.swap2 (by native_decide) (by evm_ov)
  have r38 := r37.dup3 (by native_decide) (by evm_ov)
  have r39 := r38.and (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r41 := r40.dup5 (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := RD.mstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r45 := r44.dup7 (by native_decide) (by evm_ov)
  have r46 := r45.dup2 (by native_decide) (by evm_ov)
  have r47 := r46.sub (by native_decide) (by evm_ov)
  have r48 := r47.push1 (UInt256.ofNat 132) (by native_decide) (by evm_ov)
  have r49 := r48.dup6 (by native_decide) (by evm_ov)
  have r50 := r49.add (by native_decide) (by evm_ov)
  have r51 := RD.mstore r50 (by native_decide) (by evm_ov)
  have r52 := r51.push1 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r53 := r52.dup5 (by native_decide) (by evm_ov)
  have r54 := r53.add (by native_decide) (by evm_ov)
  have r55 := r54.dup2 (by native_decide) (by evm_ov)
  have r56 := r55.swap1 (by native_decide) (by evm_ov)
  have r57 := RD.mstore r56 (by native_decide) (by evm_ov)
  have r58 := r57.swap1 (by native_decide) (by evm_ov)
  have r59 := RD.mload r58 (by native_decide) (by evm_ov)
  have r60 := r59.swap2 (by native_decide) (by evm_ov)
  have r61 := r60.swap1 (by native_decide) (by evm_ov)
  have r62 := r61.swap4 (by native_decide) (by evm_ov)
  have r63 := r62.and (by native_decide) (by evm_ov)
  have r64 := r63.swap3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8122)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8041_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8041) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8122) (endRuntime_block_8041_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (endRuntime_block_8041_memory (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8041 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_8122_taken`. -/
def endRuntime_block_8122_taken_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x3)) :: x3 :: x0 :: x1 :: ((UInt256.sub x2 x1) + (UInt256.ofNat 196)) :: x1 :: x0 :: (x2 + (UInt256.ofNat 196)) :: (UInt256.ofNat 2074820416) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8122. -/
theorem endRuntime_block_8122_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x3))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8155) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8122) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8155) (endRuntime_block_8122_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2074820416) (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.swap4 (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.dup8 (by native_decide) (by evm_ov)
  have r16 := r15.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r17⟩ := r16.extcodesize (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.iszero (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8155) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8155)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8122_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x3))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8155) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8122) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8155) (endRuntime_block_8122_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8122_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_8122_fallthrough`. -/
def endRuntime_block_8122_fallthrough_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x3)) :: x3 :: x0 :: x1 :: ((UInt256.sub x2 x1) + (UInt256.ofNat 196)) :: x1 :: x0 :: (x2 + (UInt256.ofNat 196)) :: (UInt256.ofNat 2074820416) :: x3 :: R)

/-- Automatically generated RD summary for bytecode block at pc 8122. -/
theorem endRuntime_block_8122_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x3))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8122) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8151) (endRuntime_block_8122_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.push4 (UInt256.ofNat 2074820416) (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 196) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.swap4 (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.sub (by native_decide) (by evm_ov)
  have r12 := r11.add (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.dup4 (by native_decide) (by evm_ov)
  have r15 := r14.dup8 (by native_decide) (by evm_ov)
  have r16 := r15.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r17⟩ := r16.extcodesize (by native_decide) (by evm_ov)
  have r18 := r17.iszero (by native_decide) (by evm_ov)
  have r19 := r18.dup1 (by native_decide) (by evm_ov)
  have r20 := r19.iszero (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8155) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8151)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8122_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x3))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8122) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8151) (endRuntime_block_8122_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8122_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8151. -/
theorem endRuntime_block_8151 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8151) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_8155`. -/
def endRuntime_block_8155_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 8155. -/
theorem endRuntime_block_8155 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8155) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8157) (endRuntime_block_8155_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8157)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8155_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8155) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8157) (endRuntime_block_8155_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8155 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 8157: gas (0x5a). No RD transition is asserted. Summaries resume at pc 8158 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 8158: call (0xf1). No RD transition is asserted. Summaries resume at pc 8159 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `endRuntime_block_8159_taken`. -/
def endRuntime_block_8159_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8159. -/
theorem endRuntime_block_8159_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8175) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8159) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8175) (endRuntime_block_8159_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8175) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8175)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8159_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8175) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8159) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8175) (endRuntime_block_8159_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8159_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_8159_fallthrough`. -/
def endRuntime_block_8159_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 8159. -/
theorem endRuntime_block_8159_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8159) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8166) (endRuntime_block_8159_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 8175) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8166)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8159_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8159) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8166) (endRuntime_block_8159_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8159_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8166. -/
theorem endRuntime_block_8166 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8166) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `endRuntime_block_8175`. -/
def endRuntime_block_8175_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `endRuntime_block_8175`. -/
def endRuntime_block_8175_memory {mem : ByteArray} {x5 : UInt256} : ByteArray :=
  (x5.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8175. -/
theorem endRuntime_block_8175 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x7 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8175) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 x7 (endRuntime_block_8175_stack (R := R)) (endRuntime_block_8175_memory (mem := mem) (x5 := x5)) (M (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) ((UInt256.ofNat 32) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))))) rdata (cA, σ) (k + 30) (C + ((82) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) mem) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)) ((UInt256.ofNat 32) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32))))) + (375 + 8 * ((UInt256.ofNat 32) + (UInt256.sub (memLoad (UInt256.ofNat 64) mem) (memLoad (UInt256.ofNat 64) (x5.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)))).toNat + 3 * 375))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := RD.mload r5 (by native_decide) (by evm_ov)
  have r7 := r6.dup6 (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.mstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.mload r10 (by native_decide) (by evm_ov)
  have r12 := r11.caller (by native_decide) (by evm_ov)
  have r13 := r12.swap4 (by native_decide) (by evm_ov)
  have r14 := r13.pop (by native_decide) (by evm_ov)
  have r15 := r14.dup7 (by native_decide) (by evm_ov)
  have r16 := r15.swap3 (by native_decide) (by evm_ov)
  have r17 := r16.pop (by native_decide) (by evm_ov)
  have r18 := r17.pushConst (UInt256.ofNat 109656130289137434518609496003275983118662975745057881014998262805362093846744) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r19 := r18.swap2 (by native_decide) (by evm_ov)
  have r20 := r19.dup2 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.sub (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  have r26 := RD.log3 r25 (by native_decide) hperm (by evm_ov)
  have r27 := r26.pop (by native_decide) (by evm_ov)
  have r28 := r27.pop (by native_decide) (by evm_ov)
  have r29 := r28.pop (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r30 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8175_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 x7 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x7 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8175) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x7 (endRuntime_block_8175_stack (R := R)) (endRuntime_block_8175_memory (mem := mem) (x5 := x5)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8175 hstack hperm hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_8239`. -/
def endRuntime_block_8239_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x1.toByteArray.write 0 ((UInt256.ofNat 17).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 17).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32))) :: x2 :: R)

/-- Final memory for bytecode block summary `endRuntime_block_8239`. -/
def endRuntime_block_8239_memory {mem : ByteArray} {x0 : UInt256} {x1 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x1.toByteArray.write 0 ((UInt256.ofNat 17).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)).toByteArray.write 0 (x1.toByteArray.write 0 ((UInt256.ofNat 17).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8239. -/
theorem endRuntime_block_8239 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8239) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x2 (endRuntime_block_8239_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (endRuntime_block_8239_memory (mem := mem) (x0 := x0) (x1 := x1)) (M (M (M (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 17) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup5 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.swap2 (by native_decide) (by evm_ov)
  have r17 := RD.mstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := RD.mstore r19 (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := RD.keccak256 r21 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sload r22 (by native_decide) (by evm_ov)
  have r24 := r23.dup2 (by native_decide) (by evm_ov)
  have r25 := r24.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r25⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8239_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8239) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x2 (endRuntime_block_8239_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (endRuntime_block_8239_memory (mem := mem) (x0 := x0) (x1 := x1)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8239 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_8268_taken`. -/
def endRuntime_block_8268_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8268. -/
theorem endRuntime_block_8268_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8357) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8268) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8357) R (endRuntime_block_8268_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
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
  have r17 := r16.push2 (UInt256.ofNat 8357) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8357)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8268_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8357) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8268) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8357) R (endRuntime_block_8268_taken_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8268_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `endRuntime_block_8268_fallthrough`. -/
def endRuntime_block_8268_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 8268. -/
theorem endRuntime_block_8268_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8268) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8292) R (endRuntime_block_8268_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
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
  have r17 := r16.push2 (UInt256.ofNat 8357) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8292)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8268_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8268) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8292) R (endRuntime_block_8268_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8268_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8292. -/
theorem endRuntime_block_8292 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8292) R mem aw rdata (cA, σ) k C)
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

/-- Automatically generated RD summary for bytecode block at pc 8357. -/
theorem endRuntime_block_8357_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8427) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8357) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8427) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8427) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8427)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8357_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8427) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8357) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8427) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8357_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8357. -/
theorem endRuntime_block_8357_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8357) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8368) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 8427) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8368)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8357_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 8))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8357) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8368) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8357_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8368. -/
theorem endRuntime_block_8368 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8368) R mem aw rdata (cA, σ) k C)
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

/-- Automatically generated RD summary for bytecode block at pc 8427. -/
theorem endRuntime_block_8427_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1939549) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8473) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8427) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1939549) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8473) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8473)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8427_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1939549) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8473) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8427) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8427_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8427. -/
theorem endRuntime_block_8427_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1939549) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8427) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8442) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1939549) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8473) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8442)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8427_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1939549) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8427) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8442) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8427_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8442. -/
theorem endRuntime_block_8442 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8442) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 1) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 1)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.not (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8747) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8747)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8442_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8442) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 1) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 1)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8442 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8473. -/
theorem endRuntime_block_8473_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1628253) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8519) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8519) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1628253) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8519) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8519)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8473_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1628253) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8519) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8519) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8473_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8473. -/
theorem endRuntime_block_8473_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1628253) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8488) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1628253) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8519) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8488)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8473_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1628253) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8473) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8488) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8473_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8488. -/
theorem endRuntime_block_8488 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8488) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 2) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 2)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.not (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8747) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8747)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8488_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8488) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 2) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 2)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8488 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8519. -/
theorem endRuntime_block_8519_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6582119) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8565) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8519) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8565) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 6582119) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8565) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8565)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8519_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6582119) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8565) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8519) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8565) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8519_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8519. -/
theorem endRuntime_block_8519_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6582119) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8519) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8534) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 6582119) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8565) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8534)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8519_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6582119) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8519) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8534) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8519_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8534. -/
theorem endRuntime_block_8534 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8534) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 3) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 3)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.not (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8747) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8747)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8534_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8534) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 3) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 3)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8534 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8565. -/
theorem endRuntime_block_8565_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7761783) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8611) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8565) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8611) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 7761783) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8611) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8611)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8565_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7761783) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8611) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8565) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8611) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8565_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8565. -/
theorem endRuntime_block_8565_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7761783) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8565) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8580) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 7761783) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8611) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8580)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8565_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7761783) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8565) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8580) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8565_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8580. -/
theorem endRuntime_block_8580 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8580) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 4) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 4)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.not (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8747) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8747)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8580_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8580) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 4) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 4)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8580 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8611. -/
theorem endRuntime_block_8611_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1842141) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8657) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8611) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8657) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1842141) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8657) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8657)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8611_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1842141) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8657) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8611) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8657) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8611_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8611. -/
theorem endRuntime_block_8611_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1842141) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8611) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8626) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1842141) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8657) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8626)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8611_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1842141) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8611) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8626) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8611_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8626. -/
theorem endRuntime_block_8626 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8626) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 5)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.sub (by native_decide) (by evm_ov)
  have r9 := r8.not (by native_decide) (by evm_ov)
  have r10 := r9.and (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.sub (by native_decide) (by evm_ov)
  have r16 := r15.dup4 (by native_decide) (by evm_ov)
  have r17 := r16.and (by native_decide) (by evm_ov)
  have r18 := r17.or (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 8747) (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8747)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8626_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8747) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8626) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8747) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.land x0 (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ (UInt256.ofNat 5)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := endRuntime_block_8626 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 8657. -/
theorem endRuntime_block_8657_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 484187101) (UInt256.ofNat 226)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8704) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8657) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8704) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 484187101) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 226) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 8704) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 8704)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_8657_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 484187101) (UInt256.ofNat 226)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 8704) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8657) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 8704) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_8657_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

end endRuntimeBlocks
