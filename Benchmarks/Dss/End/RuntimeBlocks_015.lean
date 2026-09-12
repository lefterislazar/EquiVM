import Reasoning.SummaryPatterns
import Benchmarks.Dss.End.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace endRuntimeBlocks

/-- Final stack for bytecode block summary `endRuntime_block_10217`. -/
def endRuntime_block_10217_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  (x1 :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10217. -/
theorem endRuntime_block_10217 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10224) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10217) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10224) (endRuntime_block_10217_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata (cA, σ) (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.dup2 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 10224) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10224)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_10217_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10224) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10217) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10224) (endRuntime_block_10217_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_10217 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_10222`. -/
def endRuntime_block_10222_stack {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {R : List UInt256} : List UInt256 :=
  (x2 :: x0 :: x1 :: x2 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10222. -/
theorem endRuntime_block_10222 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10222) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10224) (endRuntime_block_10222_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((4))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10224)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_10222_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10222) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10224) (endRuntime_block_10222_stack (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_10222 hstack h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_10224`. -/
def endRuntime_block_10224_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  (x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10224. -/
theorem endRuntime_block_10224 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10224) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 x4 (endRuntime_block_10224_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 7) (C + ((21))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap4 (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_10224_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains x4 = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10224) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 x4 (endRuntime_block_10224_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_10224 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `endRuntime_block_10231`. -/
def endRuntime_block_10231_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 1000000000000000000) :: x1 :: (UInt256.ofNat 10139) :: x0 :: (UInt256.ofNat 0) :: x0 :: x1 :: R)

/-- Automatically generated RD summary for bytecode block at pc 10231. -/
theorem endRuntime_block_10231 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10170) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10231) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10170) (endRuntime_block_10231_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata (cA, σ) (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 10139) (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.pushConst (UInt256.ofNat 1000000000000000000) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 10170) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 10170)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem endRuntime_block_10231_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.End.endBytecode 0).contains (UInt256.ofNat 10170) = true)
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10231) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10170) (endRuntime_block_10231_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (endRuntime_block_10231 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 10252. -/
theorem endRuntime_block_10252 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD Benchmarks.Dss.End.endBytecode ee g s0 (UInt256.ofNat 10252) R mem aw rdata (cA, σ) k C)
    : RDinvalid Benchmarks.Dss.End.endBytecode g s0 := by
  let r0 := h
  exact RD.invalid r0 (by native_decide)

end endRuntimeBlocks
