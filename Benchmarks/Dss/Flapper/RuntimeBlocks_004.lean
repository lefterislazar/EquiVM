import Reasoning.SummaryPatterns
import Benchmarks.Dss.Flapper.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace flapperRuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 1641. -/
theorem flapperRuntime_block_1641 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1641) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r19 := r18.pushConst (UInt256.ofNat 93608704067736590129290171836229318245) (width := 16) (op := .PUSH16) (by decide) (by native_decide) (by evm_ov)
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

/-- Final memory for bytecode block summary `flapperRuntime_block_1704_taken`. -/
def flapperRuntime_block_1704_taken_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1704. -/
theorem flapperRuntime_block_1704_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1802) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1704) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1704_taken_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1802) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1802)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1704_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1802) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1704) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1704_taken_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1704_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_1704_fallthrough`. -/
def flapperRuntime_block_1704_fallthrough_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1704. -/
theorem flapperRuntime_block_1704_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1704) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1736) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1704_fallthrough_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 1802) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1736)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1704_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1704) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1736) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1704_fallthrough_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1704_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1736. -/
theorem flapperRuntime_block_1736 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1736) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 19) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 392623361906123850923533771317355154356623709) (width := 19) (op := .PUSH19) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 106) (by native_decide) (by evm_ov)
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

/-- Final stack for bytecode block summary `flapperRuntime_block_1802_taken`. -/
def flapperRuntime_block_1802_taken_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) (UInt256.ofNat ee.header.timestamp)) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_1802_taken`. -/
def flapperRuntime_block_1802_taken_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1802. -/
theorem flapperRuntime_block_1802_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) (UInt256.ofNat ee.header.timestamp)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1879) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (flapperRuntime_block_1802_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_1802_taken_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.timestamp (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.div (by native_decide) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.gt (by native_decide) (by evm_ov)
  have r25 := r24.dup1 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 1879) (by native_decide) (by evm_ov)
  have r27 := r26.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1879)) r27 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1802_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) (UInt256.ofNat ee.header.timestamp)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1879) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (flapperRuntime_block_1802_taken_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_1802_taken_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1802_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1802_fallthrough`. -/
def flapperRuntime_block_1802_fallthrough_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) (UInt256.ofNat ee.header.timestamp)) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_1802_fallthrough`. -/
def flapperRuntime_block_1802_fallthrough_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1802. -/
theorem flapperRuntime_block_1802_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) (UInt256.ofNat ee.header.timestamp)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1844) (flapperRuntime_block_1802_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_1802_fallthrough_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.timestamp (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.div (by native_decide) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.gt (by native_decide) (by evm_ov)
  have r25 := r24.dup1 (by native_decide) (by evm_ov)
  have r26 := r25.push2 (UInt256.ofNat 1879) (by native_decide) (by evm_ov)
  have r27 := r26.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1844)) r27 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1802_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) (UInt256.ofNat ee.header.timestamp)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1802) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1844) (flapperRuntime_block_1802_fallthrough_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_1802_fallthrough_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1802_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1844`. -/
def flapperRuntime_block_1844_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))))) :: x1 :: x2 :: x3 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_1844`. -/
def flapperRuntime_block_1844_memory {mem : ByteArray} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1844. -/
theorem flapperRuntime_block_1844 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1844) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (flapperRuntime_block_1844_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (flapperRuntime_block_1844_memory (mem := mem) (x3 := x3)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r17 := r16.shl (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  have r19 := r18.div (by native_decide) (by evm_ov)
  have r20 := r19.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.iszero (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1879)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1844_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1844) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (flapperRuntime_block_1844_stack (ee := ee) (mem := mem) (σ := σ) (x1 := x1) (x2 := x2) (x3 := x3) (R := R)) (flapperRuntime_block_1844_memory (mem := mem) (x3 := x3)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1844 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1879_taken`. -/
def flapperRuntime_block_1879_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1879. -/
theorem flapperRuntime_block_1879_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1960) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1960) (flapperRuntime_block_1879_taken_stack (R := R)) mem aw rdata (cA, σ) (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1960) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1960)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1879_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1960) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1960) (flapperRuntime_block_1879_taken_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1879_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1879_fallthrough`. -/
def flapperRuntime_block_1879_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1879. -/
theorem flapperRuntime_block_1879_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1884) (flapperRuntime_block_1879_fallthrough_stack (R := R)) mem aw rdata (cA, σ) (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 1960) (by native_decide) (by evm_ov)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1884)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1879_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : x0 = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1879) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1884) (flapperRuntime_block_1879_fallthrough_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1879_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1884. -/
theorem flapperRuntime_block_1884 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1884) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 28) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 31853391384571087244587138193170471606179925661305860468948682290248124727296) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.mstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := RD.mload r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r32 (by native_decide) (by evm_ov)

/-- Final memory for bytecode block summary `flapperRuntime_block_1960_taken`. -/
def flapperRuntime_block_1960_taken_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1960. -/
theorem flapperRuntime_block_1960_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208)))) (UInt256.ofNat ee.header.timestamp)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2077) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1960) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2077) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1960_taken_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.timestamp (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 208) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.div (by native_decide) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.gt (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 2077) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2077)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1960_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208)))) (UInt256.ofNat ee.header.timestamp)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2077) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1960) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2077) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1960_taken_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1960_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_1960_fallthrough`. -/
def flapperRuntime_block_1960_fallthrough_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1960. -/
theorem flapperRuntime_block_1960_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208)))) (UInt256.ofNat ee.header.timestamp)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1960) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2001) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1960_fallthrough_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.timestamp (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 208) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap2 (by native_decide) (by evm_ov)
  have r21 := r20.div (by native_decide) (by evm_ov)
  have r22 := r21.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r23 := r22.and (by native_decide) (by evm_ov)
  have r24 := r23.gt (by native_decide) (by evm_ov)
  have r25 := r24.push2 (UInt256.ofNat 2077) (by native_decide) (by evm_ov)
  have r26 := r25.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2001)) r26 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1960_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.gt (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208)))) (UInt256.ofNat ee.header.timestamp)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1960) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2001) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_1960_fallthrough_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1960_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2001. -/
theorem flapperRuntime_block_2001 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2001) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 28) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 31853391384571087244587138193170471606179925661305860468948678073625327173632) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.mstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := RD.mload r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r32 (by native_decide) (by evm_ov)

/-- Final memory for bytecode block summary `flapperRuntime_block_2077_taken`. -/
def flapperRuntime_block_2077_taken_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2077. -/
theorem flapperRuntime_block_2077_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq x1 (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2179) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2077) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2179) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2077_taken_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.eq (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 2179) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2179)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2077_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq x1 (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2179) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2077) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2179) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2077_taken_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2077_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_2077_fallthrough`. -/
def flapperRuntime_block_2077_fallthrough_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2077. -/
theorem flapperRuntime_block_2077_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq x1 (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2077) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2103) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2077_fallthrough_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.eq (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 2179) (by native_decide) (by evm_ov)
  have r20 := r19.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2103)) r20 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2077_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq x1 (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2077) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2103) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2077_fallthrough_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2077_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2103. -/
theorem flapperRuntime_block_2103 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2103) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 24) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 31853391384571087244857145417795988774969394899711855512740324180640028164096) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.mstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := RD.mload r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r32 (by native_decide) (by evm_ov)

/-- Final memory for bytecode block summary `flapperRuntime_block_2179_taken`. -/
def flapperRuntime_block_2179_taken_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2179. -/
theorem flapperRuntime_block_2179_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2270) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2179) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2270) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2179_taken_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.gt (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 2270) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2270)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2179_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2270) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2179) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2270) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2179_taken_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2179_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_2179_fallthrough`. -/
def flapperRuntime_block_2179_fallthrough_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2179. -/
theorem flapperRuntime_block_2179_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2179) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2201) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2179_fallthrough_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sload r11 (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.gt (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 2270) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2201)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2179_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.gt x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2179) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2201) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2179_fallthrough_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2179_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2201. -/
theorem flapperRuntime_block_2201 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2201) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 22) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 13174253898690423139340666486794926060494144161460921) (width := 22) (op := .PUSH22) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 81) (by native_decide) (by evm_ov)
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

/-- Final stack for bytecode block summary `flapperRuntime_block_2270`. -/
def flapperRuntime_block_2270_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) :: (storageRead ee.codeOwner σ (UInt256.ofNat 4)) :: (UInt256.ofNat 2298) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_2270`. -/
def flapperRuntime_block_2270_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2270. -/
theorem flapperRuntime_block_2270 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4894) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2270) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4894) (flapperRuntime_block_2270_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_2270_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.mstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.keccak256 r12 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 2298) (by native_decide) (by evm_ov)
  have r16 := r15.swap2 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 4894) (by native_decide) (by evm_ov)
  have r19 := r18.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4894)) r19 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2270_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4894) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2270) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4894) (flapperRuntime_block_2270_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_2270_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2270 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2298`. -/
def flapperRuntime_block_2298_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1000000000000000000) :: x1 :: (UInt256.ofNat 2316) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2298. -/
theorem flapperRuntime_block_2298 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4894) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2298) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4894) (flapperRuntime_block_2298_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata (cA, σ) (k + 6) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 2316) (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 4894) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4894)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2298_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4894) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2298) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4894) (flapperRuntime_block_2298_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2298 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2316_taken`. -/
def flapperRuntime_block_2316_taken_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2316. -/
theorem flapperRuntime_block_2316_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2399) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2316) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2399) (flapperRuntime_block_2316_taken_stack (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.lt (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2399) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2399)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2316_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2399) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2316) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2399) (flapperRuntime_block_2316_taken_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2316_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2316_fallthrough`. -/
def flapperRuntime_block_2316_fallthrough_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2316. -/
theorem flapperRuntime_block_2316_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2316) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2323) (flapperRuntime_block_2316_fallthrough_stack (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.lt (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2399) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2323)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2316_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2316) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2323) (flapperRuntime_block_2316_fallthrough_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2316_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2323. -/
theorem flapperRuntime_block_2323 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2323) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 29) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 31853391384571087244783489581900947150089838705645715500485436364369438965760) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := RD.mstore r22 (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := RD.mload r24 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.dup2 (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  have r29 := r28.sub (by native_decide) (by evm_ov)
  have r30 := r29.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := r31.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r32 (by native_decide) (by evm_ov)

/-- Final memory for bytecode block summary `flapperRuntime_block_2399_taken`. -/
def flapperRuntime_block_2399_taken_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2399. -/
theorem flapperRuntime_block_2399_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2598) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2399) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2598) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2399_taken_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.caller (by native_decide) (by evm_ov)
  have r22 := r21.eq (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 2598) (by native_decide) (by evm_ov)
  have r24 := r23.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2598)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2399_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2598) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2399) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2598) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2399_taken_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2399_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_2399_fallthrough`. -/
def flapperRuntime_block_2399_fallthrough_memory {mem : ByteArray} {x2 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2399. -/
theorem flapperRuntime_block_2399_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2399) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2433) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2399_fallthrough_memory (mem := mem) (x2 := x2)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup4 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := RD.keccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r18 := r17.shl (by native_decide) (by evm_ov)
  have r19 := r18.sub (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.caller (by native_decide) (by evm_ov)
  have r22 := r21.eq (by native_decide) (by evm_ov)
  have r23 := r22.push2 (UInt256.ofNat 2598) (by native_decide) (by evm_ov)
  have r24 := r23.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2433)) r24 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2399_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2399) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2433) (x0 :: x1 :: x2 :: R) (flapperRuntime_block_2399_fallthrough_memory (mem := mem) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2399_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2433`. -/
def flapperRuntime_block_2433_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  ((memLoad (UInt256.ofNat 64) ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)))).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.ofNat 100) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 100)) :: (UInt256.ofNat 3140843579) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_2433`. -/
def flapperRuntime_block_2433_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x2 : UInt256} : ByteArray :=
  ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)))).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2433. -/
theorem flapperRuntime_block_2433 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2433) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2519) (flapperRuntime_block_2433_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_2433_memory (ee := ee) (mem := mem) (σ := σ) (x2 := x2)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := RD.mstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r11 := r10.dup1 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := RD.keccak256 r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r15 := r14.dup2 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sload r16 (by native_decide) (by evm_ov)
  have r18 := r17.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r19⟩ := RD.sload r18 (by native_decide) (by evm_ov)
  have r20 := r19.dup3 (by native_decide) (by evm_ov)
  have r21 := RD.mload r20 (by native_decide) (by evm_ov)
  have r22 := r21.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.dup2 (by native_decide) (by evm_ov)
  have r26 := RD.mstore r25 (by native_decide) (by evm_ov)
  have r27 := r26.caller (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  have r30 := r29.add (by native_decide) (by evm_ov)
  have r31 := RD.mstore r30 (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r35 := r34.shl (by native_decide) (by evm_ov)
  have r36 := r35.sub (by native_decide) (by evm_ov)
  have r37 := r36.swap3 (by native_decide) (by evm_ov)
  have r38 := r37.dup4 (by native_decide) (by evm_ov)
  have r39 := r38.and (by native_decide) (by evm_ov)
  have r40 := r39.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r41 := r40.dup3 (by native_decide) (by evm_ov)
  have r42 := r41.add (by native_decide) (by evm_ov)
  have r43 := RD.mstore r42 (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r45 := r44.dup2 (by native_decide) (by evm_ov)
  have r46 := r45.add (by native_decide) (by evm_ov)
  have r47 := r46.swap2 (by native_decide) (by evm_ov)
  have r48 := r47.swap1 (by native_decide) (by evm_ov)
  have r49 := r48.swap2 (by native_decide) (by evm_ov)
  have r50 := RD.mstore r49 (by native_decide) (by evm_ov)
  have r51 := r50.swap2 (by native_decide) (by evm_ov)
  have r52 := RD.mload r51 (by native_decide) (by evm_ov)
  have r53 := r52.swap4 (by native_decide) (by evm_ov)
  have r54 := r53.and (by native_decide) (by evm_ov)
  have r55 := r54.swap3 (by native_decide) (by evm_ov)
  have r56 := r55.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r57 := r56.swap3 (by native_decide) (by evm_ov)
  have r58 := r57.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r59 := r58.dup1 (by native_decide) (by evm_ov)
  have r60 := r59.dup5 (by native_decide) (by evm_ov)
  have r61 := r60.add (by native_decide) (by evm_ov)
  have r62 := r61.swap4 (by native_decide) (by evm_ov)
  have r63 := r62.swap2 (by native_decide) (by evm_ov)
  have r64 := r63.swap3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2519)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2433_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2433) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2519) (flapperRuntime_block_2433_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_2433_memory (ee := ee) (mem := mem) (σ := σ) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2433 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2519_taken`. -/
def flapperRuntime_block_2519_taken_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x6)) :: x6 :: x3 :: x0 :: ((UInt256.sub x2 x0) + x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2519. -/
theorem flapperRuntime_block_2519_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2540) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2519) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2540) (flapperRuntime_block_2519_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.swap2 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.dup8 (by native_decide) (by evm_ov)
  have r9 := r8.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := r9.extcodesize (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 2540) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2540)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2519_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2540) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2519) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2540) (flapperRuntime_block_2519_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2519_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2519_fallthrough`. -/
def flapperRuntime_block_2519_fallthrough_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x6)) :: x6 :: x3 :: x0 :: ((UInt256.sub x2 x0) + x1) :: x0 :: x3 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2519. -/
theorem flapperRuntime_block_2519_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2519) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2536) (flapperRuntime_block_2519_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.swap2 (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.dup8 (by native_decide) (by evm_ov)
  have r9 := r8.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r10⟩ := r9.extcodesize (by native_decide) (by evm_ov)
  have r11 := r10.iszero (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.iszero (by native_decide) (by evm_ov)
  have r14 := r13.push2 (UInt256.ofNat 2540) (by native_decide) (by evm_ov)
  have r15 := r14.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2536)) r15 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2519_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2519) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2536) (flapperRuntime_block_2519_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2519_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2536. -/
theorem flapperRuntime_block_2536 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2536) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_2540`. -/
def flapperRuntime_block_2540_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2540. -/
theorem flapperRuntime_block_2540 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2540) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2542) (flapperRuntime_block_2540_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2542)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2540_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2540) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2542) (flapperRuntime_block_2540_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2540 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 2542: gas (0x5a). No RD transition is asserted. Summaries resume at pc 2543 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 2543: call (0xf1). No RD transition is asserted. Summaries resume at pc 2544 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `flapperRuntime_block_2544_taken`. -/
def flapperRuntime_block_2544_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2544. -/
theorem flapperRuntime_block_2544_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2560) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2544) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2560) (flapperRuntime_block_2544_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2560) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2560)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2544_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2560) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2544) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2560) (flapperRuntime_block_2544_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2544_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2544_fallthrough`. -/
def flapperRuntime_block_2544_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2544. -/
theorem flapperRuntime_block_2544_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2544) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2551) (flapperRuntime_block_2544_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2560) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2551)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2544_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2544) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2551) (flapperRuntime_block_2544_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2544_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2551. -/
theorem flapperRuntime_block_2551 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2551) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_2560`. -/
def flapperRuntime_block_2560_stack {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  (x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_2560`. -/
def flapperRuntime_block_2560_memory {mem : ByteArray} {x6 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2560. -/
theorem flapperRuntime_block_2560 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2560) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2598) (flapperRuntime_block_2560_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (flapperRuntime_block_2560_memory (mem := mem) (x6 := x6)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, (storageWrite ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r22 := r21.shl (by native_decide) (by evm_ov)
  have r23 := r22.sub (by native_decide) (by evm_ov)
  have r24 := r23.not (by native_decide) (by evm_ov)
  have r25 := r24.and (by native_decide) (by evm_ov)
  have r26 := r25.caller (by native_decide) (by evm_ov)
  have r27 := r26.or (by native_decide) (by evm_ov)
  have r28 := r27.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by native_decide) (by evm_ov)
  have r30 := r29.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2598)) r30 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2560_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hperm : ee.perm = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2560) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2598) (flapperRuntime_block_2560_stack (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (flapperRuntime_block_2560_memory (mem := mem) (x6 := x6)) aw' rdata (cA, (storageWrite ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.ofNat ee.source.val) (UInt256.land (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2560 hstack hperm h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2598`. -/
def flapperRuntime_block_2598_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (((UInt256.sub (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (memLoad (UInt256.ofNat 64) ((UInt256.sub x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32))) + (UInt256.ofNat 100)) :: (memLoad (UInt256.ofNat 64) ((UInt256.sub x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32)) :: (UInt256.ofNat 0) :: ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 100)) :: (UInt256.ofNat 3140843579) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: x1 :: x2 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_2598`. -/
def flapperRuntime_block_2598_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x2 : UInt256} : ByteArray :=
  ((UInt256.sub x0 (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2598. -/
theorem flapperRuntime_block_2598 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2598) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2683) (flapperRuntime_block_2598_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_2598_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x2 := x2)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x2.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.mstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r15⟩ := RD.sload r14 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := RD.mload r16 (by native_decide) (by evm_ov)
  have r18 := r17.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r20 := r19.shl (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := RD.mstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.caller (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  have r26 := r25.add (by native_decide) (by evm_ov)
  have r27 := RD.mstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.address (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r30 := r29.dup3 (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := RD.mstore r31 (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.dup6 (by native_decide) (by evm_ov)
  have r35 := r34.sub (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r37 := r36.dup3 (by native_decide) (by evm_ov)
  have r38 := r37.add (by native_decide) (by evm_ov)
  have r39 := RD.mstore r38 (by native_decide) (by evm_ov)
  have r40 := r39.swap1 (by native_decide) (by evm_ov)
  have r41 := RD.mload r40 (by native_decide) (by evm_ov)
  have r42 := r41.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r45 := r44.shl (by native_decide) (by evm_ov)
  have r46 := r45.sub (by native_decide) (by evm_ov)
  have r47 := r46.swap1 (by native_decide) (by evm_ov)
  have r48 := r47.swap4 (by native_decide) (by evm_ov)
  have r49 := r48.and (by native_decide) (by evm_ov)
  have r50 := r49.swap3 (by native_decide) (by evm_ov)
  have r51 := r50.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r52 := r51.swap3 (by native_decide) (by evm_ov)
  have r53 := r52.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r54 := r53.dup1 (by native_decide) (by evm_ov)
  have r55 := r54.dup5 (by native_decide) (by evm_ov)
  have r56 := r55.add (by native_decide) (by evm_ov)
  have r57 := r56.swap4 (by native_decide) (by evm_ov)
  have r58 := r57.swap2 (by native_decide) (by evm_ov)
  have r59 := r58.swap3 (by native_decide) (by evm_ov)
  have r60 := r59.swap2 (by native_decide) (by evm_ov)
  have r61 := r60.dup3 (by native_decide) (by evm_ov)
  have r62 := r61.swap1 (by native_decide) (by evm_ov)
  have r63 := r62.sub (by native_decide) (by evm_ov)
  have r64 := r63.add (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2683)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2598_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2598) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2683) (flapperRuntime_block_2598_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) (flapperRuntime_block_2598_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x2 := x2)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2598 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2683_taken`. -/
def flapperRuntime_block_2683_taken_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x5)) :: x5 :: x2 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2683. -/
theorem flapperRuntime_block_2683_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2699) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2683) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2699) (flapperRuntime_block_2683_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup8 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := r4.extcodesize (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2699) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2699)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2683_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2699) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2683) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2699) (flapperRuntime_block_2683_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2683_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2683_fallthrough`. -/
def flapperRuntime_block_2683_fallthrough_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x5)) :: x5 :: x2 :: x1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2683. -/
theorem flapperRuntime_block_2683_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2683) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2695) (flapperRuntime_block_2683_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup8 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r5⟩ := r4.extcodesize (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.dup1 (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 2699) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2695)) r10 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2683_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x5))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2683) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2695) (flapperRuntime_block_2683_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2683_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2695. -/
theorem flapperRuntime_block_2695 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2695) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_2699`. -/
def flapperRuntime_block_2699_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 2699. -/
theorem flapperRuntime_block_2699 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2699) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2701) (flapperRuntime_block_2699_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2701)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2699_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2699) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2701) (flapperRuntime_block_2699_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2699 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 2701: gas (0x5a). No RD transition is asserted. Summaries resume at pc 2702 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 2702: call (0xf1). No RD transition is asserted. Summaries resume at pc 2703 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `flapperRuntime_block_2703_taken`. -/
def flapperRuntime_block_2703_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2703. -/
theorem flapperRuntime_block_2703_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2719) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2703) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2719) (flapperRuntime_block_2703_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2719) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2719)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2703_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2719) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2703) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2719) (flapperRuntime_block_2703_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2703_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2703_fallthrough`. -/
def flapperRuntime_block_2703_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 2703. -/
theorem flapperRuntime_block_2703_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2703) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2710) (flapperRuntime_block_2703_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 2719) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2710)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2703_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2703) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2710) (flapperRuntime_block_2703_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_2703_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2710. -/
theorem flapperRuntime_block_2710 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2710) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_2719`. -/
def flapperRuntime_block_2719_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 281474976710655) (storageRead ee.codeOwner (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) x4) (UInt256.ofNat 5))) :: (UInt256.ofNat ee.header.timestamp) :: (UInt256.ofNat 2762) :: x4 :: x5 :: x6 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_2719`. -/
def flapperRuntime_block_2719_memory {mem : ByteArray} {x6 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2719. -/
theorem flapperRuntime_block_2719 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4936) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2719) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4936) (flapperRuntime_block_2719_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (flapperRuntime_block_2719_memory (mem := mem) (x6 := x6)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) x4)) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r17⟩ := RD.sstore r16 hperm (by native_decide) (by evm_ov)
  have r18 := r17.pop (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by native_decide) (by evm_ov)
  have r21 := r20.push2 (UInt256.ofNat 2762) (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.timestamp (by native_decide) (by evm_ov)
  have r24 := r23.swap1 (by native_decide) (by evm_ov)
  have r25 := r24.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r26 := r25.and (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 4936) (by native_decide) (by evm_ov)
  have r28 := r27.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4936)) r28 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2719_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4936) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2719) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4936) (flapperRuntime_block_2719_stack (ee := ee) (mem := mem) (σ := σ) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) (flapperRuntime_block_2719_memory (mem := mem) (x6 := x6)) aw' rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x6.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) x4)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2719 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2762`. -/
def flapperRuntime_block_2762_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `flapperRuntime_block_2762`. -/
def flapperRuntime_block_2762_memory {mem : ByteArray} {x3 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2762. -/
theorem flapperRuntime_block_2762 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2762) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x4 (flapperRuntime_block_2762_stack (R := R)) (flapperRuntime_block_2762_memory (mem := mem) (x3 := x3)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, (storageWrite ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 281474976710655) (UInt256.ofNat 160)))) (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.land (UInt256.ofNat 281474976710655) x0))))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.swap4 (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := RD.mstore r4 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.swap4 (by native_decide) (by evm_ov)
  have r12 := RD.keccak256 r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r18 := r17.swap5 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  have r20 := r19.swap5 (by native_decide) (by evm_ov)
  have r21 := r20.and (by native_decide) (by evm_ov)
  have r22 := r21.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r24 := r23.shl (by native_decide) (by evm_ov)
  have r25 := r24.mul (by native_decide) (by evm_ov)
  have r26 := r25.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r28 := r27.shl (by native_decide) (by evm_ov)
  have r29 := r28.not (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.swap5 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.swap4 (by native_decide) (by evm_ov)
  have r34 := r33.swap1 (by native_decide) (by evm_ov)
  have r35 := r34.swap4 (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  have r38 := r37.swap3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r39⟩ := RD.sstore r38 hperm (by native_decide) (by evm_ov)
  have r40 := r39.pop (by native_decide) (by evm_ov)
  have r41 := r40.pop (by native_decide) (by evm_ov)
  have r42 := r41.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r42⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2762_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2762) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x4 (flapperRuntime_block_2762_stack (R := R)) (flapperRuntime_block_2762_memory (mem := mem) (x3 := x3)) aw' rdata (cA, (storageWrite ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.lor (UInt256.land (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x3.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 281474976710655) (UInt256.ofNat 160)))) (UInt256.mul (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.land (UInt256.ofNat 281474976710655) x0))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2762 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_2824`. -/
def flapperRuntime_block_2824_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.ofNat 281474976710655) (storageRead ee.codeOwner σ (UInt256.ofNat 5))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 2824. -/
theorem flapperRuntime_block_2824 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2824) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x0 (flapperRuntime_block_2824_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r7⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2824_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2824) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x0 (flapperRuntime_block_2824_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2824 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_2838_taken`. -/
def flapperRuntime_block_2838_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2838. -/
theorem flapperRuntime_block_2838_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2931) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2838) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2931) R (flapperRuntime_block_2838_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
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
  have r17 := r16.push2 (UInt256.ofNat 2931) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2931)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2838_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 2931) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2838) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2931) R (flapperRuntime_block_2838_taken_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2838_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_2838_fallthrough`. -/
def flapperRuntime_block_2838_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2838. -/
theorem flapperRuntime_block_2838_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2838) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2862) R (flapperRuntime_block_2838_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
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
  have r17 := r16.push2 (UInt256.ofNat 2931) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 2862)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2838_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2838) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2862) R (flapperRuntime_block_2838_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2838_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 2862. -/
theorem flapperRuntime_block_2862 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2862) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
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
  have r14 := r13.push1 (UInt256.ofNat 22) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 6587126949345211569731300552376908706606052991211865) (width := 22) (op := .PUSH22) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 82) (by native_decide) (by evm_ov)
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

/-- Final stack for bytecode block summary `flapperRuntime_block_2931`. -/
def flapperRuntime_block_2931_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `flapperRuntime_block_2931`. -/
def flapperRuntime_block_2931_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 2931. -/
theorem flapperRuntime_block_2931 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2931) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x1 (flapperRuntime_block_2931_stack (R := R)) (flapperRuntime_block_2931_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 1))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.mstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := r12.dup2 (by native_decide) (by evm_ov)
  have r14 := r13.swap1 (by native_decide) (by evm_ov)
  have r15 := RD.mstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := RD.keccak256 r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r20 := r19.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r21⟩ := RD.sstore r20 hperm (by native_decide) (by evm_ov)
  have r22 := r21.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r22⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_2931_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 2931) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x1 (flapperRuntime_block_2931_stack (R := R)) (flapperRuntime_block_2931_memory (mem := mem) (x0 := x0)) aw' rdata (cA, (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) x0).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 1))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_2931 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end flapperRuntimeBlocks
