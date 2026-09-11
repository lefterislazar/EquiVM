import Reasoning.SummaryPatterns
import Benchmarks.Dss.Flapper.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace flapperRuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 785. -/
theorem flapperRuntime_block_785 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 785) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_789`. -/
def flapperRuntime_block_789_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 789. -/
theorem flapperRuntime_block_789 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 3334) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 789) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 3334) (flapperRuntime_block_789_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 3334) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3334)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_789_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 3334) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 789) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 3334) (flapperRuntime_block_789_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_789 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_796_taken`. -/
def flapperRuntime_block_796_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) :: (UInt256.ofNat 4) :: (UInt256.ofNat 313) :: R)

/-- Automatically generated RD summary for bytecode block at pc 796. -/
theorem flapperRuntime_block_796_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 818) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 796) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 818) (flapperRuntime_block_796_taken_stack (ee := ee) (R := R)) mem aw rdata (cA, σ) (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 313) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.lt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 818) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 818)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_796_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 818) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 796) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 818) (flapperRuntime_block_796_taken_stack (ee := ee) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_796_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_796_fallthrough`. -/
def flapperRuntime_block_796_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) :: (UInt256.ofNat 4) :: (UInt256.ofNat 313) :: R)

/-- Automatically generated RD summary for bytecode block at pc 796. -/
theorem flapperRuntime_block_796_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 796) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 814) (flapperRuntime_block_796_fallthrough_stack (ee := ee) (R := R)) mem aw rdata (cA, σ) (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 313) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.lt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 818) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 814)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_796_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 796) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 814) (flapperRuntime_block_796_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_796_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 814. -/
theorem flapperRuntime_block_814 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 814) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_818`. -/
def flapperRuntime_block_818_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes ((UInt256.ofNat 32) + x1).toNat 32)) :: (uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 818. -/
theorem flapperRuntime_block_818 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 3901) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 818) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 3901) (flapperRuntime_block_818_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata (cA, σ) (k + 10) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.calldataload (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 3901) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 3901)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_818_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 3901) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 818) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 3901) (flapperRuntime_block_818_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_818 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_831`. -/
def flapperRuntime_block_831_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 573) :: R)

/-- Automatically generated RD summary for bytecode block at pc 831. -/
theorem flapperRuntime_block_831 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4553) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 831) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4553) (flapperRuntime_block_831_stack (R := R)) mem aw rdata (cA, σ) (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 573) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4553) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4553)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_831_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4553) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 831) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4553) (flapperRuntime_block_831_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_831 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_839`. -/
def flapperRuntime_block_839_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 313) :: R)

/-- Automatically generated RD summary for bytecode block at pc 839. -/
theorem flapperRuntime_block_839 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4574) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 839) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4574) (flapperRuntime_block_839_stack (R := R)) mem aw rdata (cA, σ) (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 313) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4574) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4574)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_839_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4574) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 839) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4574) (flapperRuntime_block_839_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_839 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_847`. -/
def flapperRuntime_block_847_stack {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 313) :: R)

/-- Automatically generated RD summary for bytecode block at pc 847. -/
theorem flapperRuntime_block_847 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4580) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 847) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4580) (flapperRuntime_block_847_stack (R := R)) mem aw rdata (cA, σ) (k + 4) (C + ((15))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 313) (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 4580) (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4580)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_847_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4580) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 847) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4580) (flapperRuntime_block_847_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_847 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_855_taken`. -/
def flapperRuntime_block_855_taken_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) :: (UInt256.ofNat 4) :: (UInt256.ofNat 360) :: R)

/-- Automatically generated RD summary for bytecode block at pc 855. -/
theorem flapperRuntime_block_855_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 877) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 855) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 877) (flapperRuntime_block_855_taken_stack (ee := ee) (R := R)) mem aw rdata (cA, σ) (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 360) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.lt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 877) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 877)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_855_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 877) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 855) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 877) (flapperRuntime_block_855_taken_stack (ee := ee) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_855_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_855_fallthrough`. -/
def flapperRuntime_block_855_fallthrough_stack {ee : ExecutionEnv} {R : List UInt256} : List UInt256 :=
  ((UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) :: (UInt256.ofNat 4) :: (UInt256.ofNat 360) :: R)

/-- Automatically generated RD summary for bytecode block at pc 855. -/
theorem flapperRuntime_block_855_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 855) R mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 873) (flapperRuntime_block_855_fallthrough_stack (ee := ee) (R := R)) mem aw rdata (cA, σ) (k + 12) (C + ((40))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 360) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.lt (by native_decide) (by evm_ov)
  have r10 := r9.iszero (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 877) (by native_decide) (by evm_ov)
  have r12 := r11.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 873)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_855_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4)) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 855) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 873) (flapperRuntime_block_855_fallthrough_stack (ee := ee) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_855_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 873. -/
theorem flapperRuntime_block_873 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 873) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_877`. -/
def flapperRuntime_block_877_stack {ee : ExecutionEnv} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((uInt256OfByteArray (ee.calldata.readBytes x1.toNat 32)) :: R)

/-- Automatically generated RD summary for bytecode block at pc 877. -/
theorem flapperRuntime_block_877 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4586) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4586) (flapperRuntime_block_877_stack (ee := ee) (x1 := x1) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((17))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.calldataload (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 4586) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 4586)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_877_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 4586) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 877) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4586) (flapperRuntime_block_877_stack (ee := ee) (x1 := x1) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_877 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_884`. -/
def flapperRuntime_block_884_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((storageRead ee.codeOwner σ (UInt256.ofNat 8)) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 884. -/
theorem flapperRuntime_block_884 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 884) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x0 (flapperRuntime_block_884_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r5⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_884_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 884) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x0 (flapperRuntime_block_884_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_884 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 890. -/
theorem flapperRuntime_block_890_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (storageRead ee.codeOwner σ (UInt256.ofNat 7))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 964) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 890) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 964) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 964) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 964)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_890_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (storageRead ee.codeOwner σ (UInt256.ofNat 7))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 964) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 890) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 964) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_890_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 890. -/
theorem flapperRuntime_block_890_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (storageRead ee.codeOwner σ (UInt256.ofNat 7))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 890) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 899) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.iszero (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 964) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 899)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_890_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.isZero (storageRead ee.codeOwner σ (UInt256.ofNat 7))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 890) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 899) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_890_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 899. -/
theorem flapperRuntime_block_899 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 899) R mem aw rdata (cA, σ) k C)
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
  have r14 := r13.push1 (UInt256.ofNat 18) (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  have r18 := RD.mstore r17 (by native_decide) (by evm_ov)
  have r19 := r18.pushConst (UInt256.ofNat 6134740029783185170736863992692972624377445) (width := 18) (op := .PUSH18) (by decide) (by native_decide) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
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

/-- Final memory for bytecode block summary `flapperRuntime_block_964_taken`. -/
def flapperRuntime_block_964_taken_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 964. -/
theorem flapperRuntime_block_964_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1062) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 964) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1062) (x0 :: R) (flapperRuntime_block_964_taken_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
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
  have r21 := r20.push2 (UInt256.ofNat 1062) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1062)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_964_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1062) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 964) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1062) (x0 :: R) (flapperRuntime_block_964_taken_memory (mem := mem) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_964_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_964_fallthrough`. -/
def flapperRuntime_block_964_fallthrough_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 964. -/
theorem flapperRuntime_block_964_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 964) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 996) (x0 :: R) (flapperRuntime_block_964_fallthrough_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
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
  have r21 := r20.push2 (UInt256.ofNat 1062) (by native_decide) (by evm_ov)
  have r22 := r21.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 996)) r22 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_964_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 964) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 996) (x0 :: R) (flapperRuntime_block_964_fallthrough_memory (mem := mem) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_964_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 996. -/
theorem flapperRuntime_block_996 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 996) R mem aw rdata (cA, σ) k C)
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

/-- Final stack for bytecode block summary `flapperRuntime_block_1062`. -/
def flapperRuntime_block_1062_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.ofNat 0) :: (UInt256.ofNat 100) :: (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) :: (memLoad (UInt256.ofNat 64) ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)))).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32)) :: ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 100)) :: (UInt256.ofNat 3140843579) :: (UInt256.land (storageRead ee.codeOwner σ (UInt256.ofNat 3)) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: x0 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_1062`. -/
def flapperRuntime_block_1062_memory {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} : ByteArray :=
  ((storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))).toByteArray.write 0 ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 2)))).toByteArray.write 0 ((UInt256.ofNat ee.codeOwner.val).toByteArray.write 0 ((UInt256.shiftLeft (UInt256.ofNat 3140843579) (UInt256.ofNat 224)).toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)).toNat 32) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1062. -/
theorem flapperRuntime_block_1062 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1062) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1148) (flapperRuntime_block_1062_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (flapperRuntime_block_1062_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0)) (M (M (M (M (M (M (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 4)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 36)) (⟨32⟩ : UInt256)) ((memLoad (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x0.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 68)) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.dup2 (by native_decide) (by evm_ov)
  have r7 := RD.mstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.dup1 (by native_decide) (by evm_ov)
  have r13 := r12.dup3 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r18⟩ := RD.sload r17 (by native_decide) (by evm_ov)
  have r19 := r18.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := RD.mload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 224) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.dup2 (by native_decide) (by evm_ov)
  have r27 := RD.mstore r26 (by native_decide) (by evm_ov)
  have r28 := r27.address (by native_decide) (by evm_ov)
  have r29 := r28.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r30 := r29.dup3 (by native_decide) (by evm_ov)
  have r31 := r30.add (by native_decide) (by evm_ov)
  have r32 := RD.mstore r31 (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r34 := r33.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r36 := r35.shl (by native_decide) (by evm_ov)
  have r37 := r36.sub (by native_decide) (by evm_ov)
  have r38 := r37.swap3 (by native_decide) (by evm_ov)
  have r39 := r38.dup4 (by native_decide) (by evm_ov)
  have r40 := r39.and (by native_decide) (by evm_ov)
  have r41 := r40.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r42 := r41.dup3 (by native_decide) (by evm_ov)
  have r43 := r42.add (by native_decide) (by evm_ov)
  have r44 := RD.mstore r43 (by native_decide) (by evm_ov)
  have r45 := r44.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r46 := r45.dup2 (by native_decide) (by evm_ov)
  have r47 := r46.add (by native_decide) (by evm_ov)
  have r48 := r47.swap2 (by native_decide) (by evm_ov)
  have r49 := r48.swap1 (by native_decide) (by evm_ov)
  have r50 := r49.swap2 (by native_decide) (by evm_ov)
  have r51 := RD.mstore r50 (by native_decide) (by evm_ov)
  have r52 := r51.swap2 (by native_decide) (by evm_ov)
  have r53 := RD.mload r52 (by native_decide) (by evm_ov)
  have r54 := r53.swap4 (by native_decide) (by evm_ov)
  have r55 := r54.and (by native_decide) (by evm_ov)
  have r56 := r55.swap3 (by native_decide) (by evm_ov)
  have r57 := r56.push4 (UInt256.ofNat 3140843579) (by native_decide) (by evm_ov)
  have r58 := r57.swap3 (by native_decide) (by evm_ov)
  have r59 := r58.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r60 := r59.dup1 (by native_decide) (by evm_ov)
  have r61 := r60.dup5 (by native_decide) (by evm_ov)
  have r62 := r61.add (by native_decide) (by evm_ov)
  have r63 := r62.swap4 (by native_decide) (by evm_ov)
  have r64 := r63.swap2 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1148)) r64 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1062_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1062) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1148) (flapperRuntime_block_1062_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (R := R)) (flapperRuntime_block_1062_memory (ee := ee) (mem := mem) (σ := σ) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1062 hstack h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1148_taken`. -/
def flapperRuntime_block_1148_taken_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x6)) :: x6 :: x0 :: x3 :: ((UInt256.sub x2 x3) + x1) :: x3 :: x0 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1148. -/
theorem flapperRuntime_block_1148_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1170) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1148) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1170) (flapperRuntime_block_1148_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.swap3 (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.dup8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := r10.extcodesize (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1170) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1170)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1148_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1170) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1148) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1170) (flapperRuntime_block_1148_taken_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1148_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1148_fallthrough`. -/
def flapperRuntime_block_1148_fallthrough_stack {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {x2 : UInt256} {x3 : UInt256} {x4 : UInt256} {x5 : UInt256} {x6 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero (extCodeSizeWord σ x6)) :: x6 :: x0 :: x3 :: ((UInt256.sub x2 x3) + x1) :: x3 :: x0 :: x4 :: x5 :: x6 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1148. -/
theorem flapperRuntime_block_1148_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1148) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1166) (flapperRuntime_block_1148_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.swap3 (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.dup3 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.add (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.dup8 (by native_decide) (by evm_ov)
  have r10 := r9.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r11⟩ := r10.extcodesize (by native_decide) (by evm_ov)
  have r12 := r11.iszero (by native_decide) (by evm_ov)
  have r13 := r12.dup1 (by native_decide) (by evm_ov)
  have r14 := r13.iszero (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 1170) (by native_decide) (by evm_ov)
  have r16 := r15.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1166)) r16 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1148_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero (extCodeSizeWord σ x6))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1148) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1166) (flapperRuntime_block_1148_fallthrough_stack (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (x3 := x3) (x4 := x4) (x5 := x5) (x6 := x6) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1148_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1166. -/
theorem flapperRuntime_block_1166 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1166) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_1170`. -/
def flapperRuntime_block_1170_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1170. -/
theorem flapperRuntime_block_1170 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1170) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1172) (flapperRuntime_block_1170_stack (R := R)) mem aw rdata (cA, σ) (k + 2) (C + ((3))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1172)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1170_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1170) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1172) (flapperRuntime_block_1170_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1170 hstack h)
  exact ⟨_, k', C', h'⟩

/- Execution split boundary at pc 1172: gas (0x5a). No RD transition is asserted. Summaries resume at pc 1173 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 1173: call (0xf1). No RD transition is asserted. Summaries resume at pc 1174 from a fresh symbolic RD state. -/

/-- Final stack for bytecode block summary `flapperRuntime_block_1174_taken`. -/
def flapperRuntime_block_1174_taken_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1174. -/
theorem flapperRuntime_block_1174_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1190) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1174) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1190) (flapperRuntime_block_1174_taken_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1190) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1190)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1174_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1190) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1174) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1190) (flapperRuntime_block_1174_taken_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1174_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1174_fallthrough`. -/
def flapperRuntime_block_1174_fallthrough_stack {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.isZero x0) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1174. -/
theorem flapperRuntime_block_1174_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1174) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1181) (flapperRuntime_block_1174_fallthrough_stack (x0 := x0) (R := R)) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := r0.iszero (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.iszero (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 1190) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1181)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1174_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.isZero x0)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1174) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1181) (flapperRuntime_block_1174_fallthrough_stack (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1174_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1181. -/
theorem flapperRuntime_block_1181 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1181) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := RD.returndatacopyFullPush1Dup1 r0 (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)
  have r2 := r1.returndatasize (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  exact RD.rev r3 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_1190`. -/
def flapperRuntime_block_1190_stack {R : List UInt256} : List UInt256 :=
  R

/-- Final memory for bytecode block summary `flapperRuntime_block_1190`. -/
def flapperRuntime_block_1190_memory {mem : ByteArray} {x4 : UInt256} : ByteArray :=
  ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1190. -/
theorem flapperRuntime_block_1190 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x5 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1190) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x5 (flapperRuntime_block_1190_stack (R := R)) (flapperRuntime_block_1190_memory (mem := mem) (x4 := x4)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, (storageWrite ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 0)) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.ofNat 0)) ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.ofNat 0))) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.dup3 (by native_decide) (by evm_ov)
  have r8 := RD.mstore r7 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r12 := r11.dup2 (by native_decide) (by evm_ov)
  have r13 := r12.swap1 (by native_decide) (by evm_ov)
  have r14 := RD.mstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r16 := r15.dup3 (by native_decide) (by evm_ov)
  have r17 := RD.keccak256 r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sstore r19 hperm (by native_decide) (by evm_ov)
  have r21 := r20.swap1 (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := r23.dup3 (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sstore r25 hperm (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r28 := r27.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r29⟩ := RD.sstore r28 hperm (by native_decide) (by evm_ov)
  have r30 := r29.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r30⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1190_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x5 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1190) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x5 (flapperRuntime_block_1190_stack (R := R)) (flapperRuntime_block_1190_memory (mem := mem) (x4 := x4)) aw' rdata (cA, (storageWrite ee.codeOwner (storageWrite ee.codeOwner (storageWrite ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) (UInt256.ofNat 0)) ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)) + (UInt256.ofNat 1)) (UInt256.ofNat 0)) ((UInt256.ofNat 2) + (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 1).toByteArray.write 0 (x4.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32))) (UInt256.ofNat 0))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1190 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_1225_taken`. -/
def flapperRuntime_block_1225_taken_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1225. -/
theorem flapperRuntime_block_1225_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1318) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1225) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1318) R (flapperRuntime_block_1225_taken_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
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
  have r17 := r16.push2 (UInt256.ofNat 1318) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1318)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1225_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1318) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1225) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1318) R (flapperRuntime_block_1225_taken_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1225_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final memory for bytecode block summary `flapperRuntime_block_1225_fallthrough`. -/
def flapperRuntime_block_1225_fallthrough_memory {ee : ExecutionEnv} {mem : ByteArray} : ByteArray :=
  ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1225. -/
theorem flapperRuntime_block_1225_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1225) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1249) R (flapperRuntime_block_1225_fallthrough_memory (ee := ee) (mem := mem)) (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
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
  have r17 := r16.push2 (UInt256.ofNat 1318) (by native_decide) (by evm_ov)
  have r18 := r17.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1249)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1225_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) ((UInt256.ofNat 0).toByteArray.write 0 ((UInt256.ofNat ee.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) (UInt256.ofNat 32).toNat 32)))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1225) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1249) R (flapperRuntime_block_1225_fallthrough_memory (ee := ee) (mem := mem)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1225_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1249. -/
theorem flapperRuntime_block_1249 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1249) R mem aw rdata (cA, σ) k C)
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

/-- Automatically generated RD summary for bytecode block at pc 1318. -/
theorem flapperRuntime_block_1318_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1342) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1318) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1342) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 6448487) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1342) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1342)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1318_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1342) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1318) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1342) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1318_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1318. -/
theorem flapperRuntime_block_1318_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1318) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1333) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 6448487) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1342) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1333)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1318_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 6448487) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1318) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1333) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1318_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1333. -/
theorem flapperRuntime_block_1333 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1333) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 4) x0)) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1543) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1543)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1333_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1333) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 4) x0)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1333 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1342. -/
theorem flapperRuntime_block_1342_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1386) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1342) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1386) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1907995) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1386) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1386)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1342_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1386) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1342) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1386) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1342_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1342. -/
theorem flapperRuntime_block_1342_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1342) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1357) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1907995) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1386) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1357)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1342_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1907995) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1342) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1357) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1342_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1357. -/
theorem flapperRuntime_block_1357 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1357) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.land x0 (UInt256.ofNat 281474976710655)) (UInt256.land (UInt256.lnot (UInt256.ofNat 281474976710655)) (storageRead ee.codeOwner σ (UInt256.ofNat 5)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.dup4 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.or (by native_decide) (by evm_ov)
  have r11 := r10.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r12⟩ := RD.sstore r11 hperm (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 1543) (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1543)) r14 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1357_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1357) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.land x0 (UInt256.ofNat 281474976710655)) (UInt256.land (UInt256.lnot (UInt256.ofNat 281474976710655)) (storageRead ee.codeOwner σ (UInt256.ofNat 5)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1357 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1386. -/
theorem flapperRuntime_block_1386_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1442) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1386) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 7627125) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1442) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1442)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1386_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1442) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1386) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1386_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1386. -/
theorem flapperRuntime_block_1386_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1386) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1401) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 7627125) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 232) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1442) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1401)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1386_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 7627125) (UInt256.ofNat 232)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1386) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1401) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1386_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1401. -/
theorem flapperRuntime_block_1401 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1401) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.mul (UInt256.land x0 (UInt256.ofNat 281474976710655)) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48))) (UInt256.land (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680)) (storageRead ee.codeOwner σ (UInt256.ofNat 5)))))) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.pushConst (UInt256.ofNat 79228162514264056118567239680) (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have r5 := r4.not (by native_decide) (by evm_ov)
  have r6 := r5.and (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
  have r9 := r8.shl (by native_decide) (by evm_ov)
  have r10 := r9.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r11 := r10.dup5 (by native_decide) (by evm_ov)
  have r12 := r11.and (by native_decide) (by evm_ov)
  have r13 := r12.mul (by native_decide) (by evm_ov)
  have r14 := r13.or (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sstore r15 hperm (by native_decide) (by evm_ov)
  have r17 := r16.push2 (UInt256.ofNat 1543) (by native_decide) (by evm_ov)
  have r18 := r17.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1543)) r18 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1401_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1401) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 5) (UInt256.lor (UInt256.mul (UInt256.land x0 (UInt256.ofNat 281474976710655)) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 48))) (UInt256.land (UInt256.lnot (UInt256.ofNat 79228162514264056118567239680)) (storageRead ee.codeOwner σ (UInt256.ofNat 5)))))) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1401 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1442. -/
theorem flapperRuntime_block_1442_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1466) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1466) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1776217) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1466) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1466)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1442_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234)) x1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1466) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1466) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1442_taken hstack hcond hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1442. -/
theorem flapperRuntime_block_1442_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1457) (x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((32))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.pushConst (UInt256.ofNat 1776217) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 234) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.eq (by native_decide) (by evm_ov)
  have r7 := r6.iszero (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 1466) (by native_decide) (by evm_ov)
  have r9 := r8.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1457)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1442_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.eq (UInt256.shiftLeft (UInt256.ofNat 1776217) (UInt256.ofNat 234)) x1)) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1442) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1457) (x0 :: x1 :: R) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1442_fallthrough hstack hcond h)
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1457. -/
theorem flapperRuntime_block_1457 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1457) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 8) x0)) k' C' := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 8) (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sstore r3 hperm (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 1543) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1543)) r6 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1457_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = true)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1543) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1457) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: R) mem aw' rdata (cA, (storageWrite ee.codeOwner σ (UInt256.ofNat 8) x0)) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1457 hstack hperm hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1466. -/
theorem flapperRuntime_block_1466 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1466) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := RD.mload r3 (by native_decide) (by evm_ov)
  have r5 := r4.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 229) (by native_decide) (by evm_ov)
  have r7 := r6.shl (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := RD.mstore r8 (by native_decide) (by evm_ov)
  have r10 := r9.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := RD.mstore r13 (by native_decide) (by evm_ov)
  have r15 := r14.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 36) (by native_decide) (by evm_ov)
  have r17 := r16.dup3 (by native_decide) (by evm_ov)
  have r18 := r17.add (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.pushConst (UInt256.ofNat 31853391384571087244709448248362826078249281944411185996983893856618098552064) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 68) (by native_decide) (by evm_ov)
  have r22 := r21.dup3 (by native_decide) (by evm_ov)
  have r23 := r22.add (by native_decide) (by evm_ov)
  have r24 := RD.mstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.swap1 (by native_decide) (by evm_ov)
  have r26 := RD.mload r25 (by native_decide) (by evm_ov)
  have r27 := r26.swap1 (by native_decide) (by evm_ov)
  have r28 := r27.dup2 (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.push1 (UInt256.ofNat 100) (by native_decide) (by evm_ov)
  have r32 := r31.add (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  exact RD.rev r33 (by native_decide) (by evm_ov)

/-- Final stack for bytecode block summary `flapperRuntime_block_1543`. -/
def flapperRuntime_block_1543_stack {R : List UInt256} : List UInt256 :=
  R

/-- Automatically generated RD summary for bytecode block at pc 1543. -/
theorem flapperRuntime_block_1543 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x2 (flapperRuntime_block_1543_stack (R := R)) mem aw rdata (cA, σ) (k + 4) (C + ((13))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r4 (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1543_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x2 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1543) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x2 (flapperRuntime_block_1543_stack (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (flapperRuntime_block_1543 hstack hvalid h)
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1547`. -/
def flapperRuntime_block_1547_stack {ee : ExecutionEnv} {σ : AccountMap} {x0 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) (storageRead ee.codeOwner σ (UInt256.ofNat 2))) :: x0 :: R)

/-- Automatically generated RD summary for bytecode block at pc 1547. -/
theorem flapperRuntime_block_1547 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1547) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x0 (flapperRuntime_block_1547_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
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
theorem flapperRuntime_block_1547_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x0 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1547) (x0 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x0 (flapperRuntime_block_1547_stack (ee := ee) (σ := σ) (x0 := x0) (R := R)) mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1547 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Final stack for bytecode block summary `flapperRuntime_block_1562`. -/
def flapperRuntime_block_1562_stack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap} {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.land (UInt256.div (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)) + (UInt256.ofNat 2))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 208))) (UInt256.ofNat 281474976710655)) :: (UInt256.land (UInt256.ofNat 281474976710655) (UInt256.div (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)) + (UInt256.ofNat 2))) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))) :: (UInt256.land (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)) + (UInt256.ofNat 2))) (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))) :: (storageRead ee.codeOwner σ ((keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)) + (UInt256.ofNat 1))) :: (storageRead ee.codeOwner σ (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32))) :: x1 :: R)

/-- Final memory for bytecode block summary `flapperRuntime_block_1562`. -/
def flapperRuntime_block_1562_memory {mem : ByteArray} {x0 : UInt256} : ByteArray :=
  (x0.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem (UInt256.ofNat 32).toNat 32) (UInt256.ofNat 0).toNat 32)

/-- Automatically generated RD summary for bytecode block at pc 1562. -/
theorem flapperRuntime_block_1562 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1562) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x1 (flapperRuntime_block_1562_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (flapperRuntime_block_1562_memory (mem := mem) (x0 := x0)) (M (M (M aw (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64)) rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.mstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := RD.mstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.swap2 (by native_decide) (by evm_ov)
  have r14 := RD.keccak256 r13 (by native_decide) (by evm_ov)
  have r15 := r14.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r16⟩ := RD.sload r15 (by native_decide) (by evm_ov)
  have r17 := r16.swap2 (by native_decide) (by evm_ov)
  have r18 := r17.dup2 (by native_decide) (by evm_ov)
  have r19 := r18.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r20⟩ := RD.sload r19 (by native_decide) (by evm_ov)
  have r21 := r20.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r22 := r21.swap1 (by native_decide) (by evm_ov)
  have r23 := r22.swap2 (by native_decide) (by evm_ov)
  have r24 := r23.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, r25⟩ := RD.sload r24 (by native_decide) (by evm_ov)
  have r26 := r25.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r27 := r26.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r29 := r28.shl (by native_decide) (by evm_ov)
  have r30 := r29.sub (by native_decide) (by evm_ov)
  have r31 := r30.dup2 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  have r34 := r33.pushConst (UInt256.ofNat 281474976710655) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have r35 := r34.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r36 := r35.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r37 := r36.shl (by native_decide) (by evm_ov)
  have r38 := r37.dup3 (by native_decide) (by evm_ov)
  have r39 := r38.div (by native_decide) (by evm_ov)
  have r40 := r39.dup2 (by native_decide) (by evm_ov)
  have r41 := r40.and (by native_decide) (by evm_ov)
  have r42 := r41.swap2 (by native_decide) (by evm_ov)
  have r43 := r42.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r44 := r43.push1 (UInt256.ofNat 208) (by native_decide) (by evm_ov)
  have r45 := r44.shl (by native_decide) (by evm_ov)
  have r46 := r45.swap1 (by native_decide) (by evm_ov)
  have r47 := r46.div (by native_decide) (by evm_ov)
  have r48 := r47.and (by native_decide) (by evm_ov)
  have r49 := r48.dup6 (by native_decide) (by evm_ov)
  have r50 := r49.jump (by native_decide) hvalid (by evm_ov)
  exact ⟨_, _, r50⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1562_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains x1 = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1562) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 x1 (flapperRuntime_block_1562_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (R := R)) (flapperRuntime_block_1562_memory (mem := mem) (x0 := x0)) aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1562 hstack hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1630. -/
theorem flapperRuntime_block_1630_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 7))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1704) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1630) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1704) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1704) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1704)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1630_taken_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 7))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J Benchmarks.Dss.Flapper.flapperBytecode 0).contains (UInt256.ofNat 1704) = true)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1630) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1704) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1630_taken hstack hcond hvalid h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

/-- Automatically generated RD summary for bytecode block at pc 1630. -/
theorem flapperRuntime_block_1630_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 7))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1630) R mem aw rdata (cA, σ) k C)
    : ∃ (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1641) R mem aw rdata (cA, σ) k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 7) (by native_decide) (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r5 := r4.eq (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 1704) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1641)) r7 (by native_decide)
  exact ⟨_, _, rFinal⟩

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem flapperRuntime_block_1630_fallthrough_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (UInt256.eq (UInt256.ofNat 1) (storageRead ee.codeOwner σ (UInt256.ofNat 7))) = (UInt256.ofNat 0))
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1630) R mem aw rdata (cA, σ) k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 1641) R mem aw' rdata (cA, σ) k' C' := by
  obtain ⟨k0, C0, h0⟩ := flapperRuntime_block_1630_fallthrough hstack hcond h
  obtain ⟨k', C', h'⟩ := RD.pack h0
  exact ⟨_, k', C', h'⟩

end flapperRuntimeBlocks
