import Reasoning.SummaryPatterns
import Benchmarks.Dss.Flapper.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace flapperRuntimeBlocks

/-- Automatically generated RD summary for bytecode block at pc 4991. -/
theorem flapperRuntime_block_4991 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4991) R mem aw rdata (cA, σ) k C)
    : RDrev Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  have r1 := r0.push1 (UInt256.ofNat 0) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  exact RD.rev r2 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 4995. -/
theorem flapperRuntime_block_4995 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (h : RD Benchmarks.Dss.Flapper.flapperBytecode ee g s0 (UInt256.ofNat 4995) R mem aw rdata (cA, σ) k C)
    : RDinvalid Benchmarks.Dss.Flapper.flapperBytecode g s0 := by
  let r0 := h
  exact RD.invalid r0 (by native_decide)

end flapperRuntimeBlocks
