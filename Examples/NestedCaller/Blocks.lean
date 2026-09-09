import Reasoning.SummaryPatterns
import Examples.NestedCaller.Bytecode

open Solm ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace nestedCallerBlocks

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem nestedCaller_block_0_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (solcCallFailedWord ee.weiValue) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 15) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 15) (ee.weiValue :: R) ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.solcSummaryFreeMemoryPointer (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r2 := RD.solcSummaryCallvalueCondition (by exact ⟨r1, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r3 := r2.push2 (UInt256.ofNat 15) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 15)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 0. -/
theorem nestedCaller_block_0_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (solcCallFailedWord ee.weiValue) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 0) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 12) (ee.weiValue :: R) ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 8) (C + ((30) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := RD.solcSummaryFreeMemoryPointer (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r2 := RD.solcSummaryCallvalueCondition (by exact ⟨r1, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r3 := r2.push2 (UInt256.ofNat 15) (by native_decide) (by evm_ov)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 12)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 12. -/
theorem nestedCaller_block_12 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 12) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  exact RD.solcSummaryRevert0 (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem nestedCaller_block_15_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (solcCalldataTooShortWord (UInt256.ofNat ee.calldata.size)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 41) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 41) R mem aw rdata (cA, σ) (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.solcSummaryCalldataSizeCondition (target := (UInt256.ofNat 41)) (op := .PUSH2) (width := 2) (by exact ⟨r2, by native_decide, by native_decide, by native_decide, by decide, by native_decide, by evm_ov⟩)
  have r4 := r3.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 41)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 15. -/
theorem nestedCaller_block_15_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hcond : (solcCalldataTooShortWord (UInt256.ofNat ee.calldata.size)) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 15) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 25) R mem aw rdata (cA, σ) (k + 7) (C + ((24))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := RD.solcSummaryCalldataSizeCondition (target := (UInt256.ofNat 41)) (op := .PUSH2) (width := 2) (by exact ⟨r2, by native_decide, by native_decide, by native_decide, by decide, by native_decide, by evm_ov⟩)
  have r4 := r3.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 25)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 25. -/
theorem nestedCaller_block_25_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (solcSelectorMatches (UInt256.ofNat 941609360) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 45) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 25) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 45) ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R) mem aw rdata (cA, σ) (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := RD.solcSummarySelectorLoad (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r2 := RD.solcSummarySelectorCondition (expected := (UInt256.ofNat 941609360)) (target := (UInt256.ofNat 45)) (op := .PUSH2) (width := 2) (by exact ⟨r1, by native_decide, by native_decide, by native_decide, by decide, by native_decide, by evm_ov⟩)
  have r3 := r2.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 45)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 25. -/
theorem nestedCaller_block_25_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (solcSelectorMatches (UInt256.ofNat 941609360) (UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224))) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 25) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 41) ((UInt256.shiftRight (uInt256OfByteArray (ee.calldata.readBytes (⟨0⟩ : UInt256).toNat 32)) (UInt256.ofNat 224)) :: R) mem aw rdata (cA, σ) (k + 9) (C + ((33))) := by
  let r0 := h
  have r1 := RD.solcSummarySelectorLoad (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r2 := RD.solcSummarySelectorCondition (expected := (UInt256.ofNat 941609360)) (target := (UInt256.ofNat 45)) (op := .PUSH2) (width := 2) (by exact ⟨r1, by native_decide, by native_decide, by native_decide, by decide, by native_decide, by evm_ov⟩)
  have r3 := r2.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 41)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 41. -/
theorem nestedCaller_block_41 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 41) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  exact RD.solcSummaryRevert0 (by exact ⟨r1, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 45. -/
theorem nestedCaller_block_45 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 491) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 45) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 491) ((UInt256.ofNat 4) :: ((UInt256.ofNat 4) + (UInt256.sub (UInt256.ofNat ee.calldata.size) (UInt256.ofNat 4))) :: (UInt256.ofNat 66) :: (UInt256.ofNat 71) :: R) mem aw rdata (cA, σ) (k + 14) (C + ((44))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 71) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.calldatasize (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.dup2 (by native_decide) (by evm_ov)
  have r8 := r7.add (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 66) (by native_decide) (by evm_ov)
  have r11 := r10.swap2 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 491) (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 491)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 66. -/
theorem nestedCaller_block_66 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 93) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 66) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 93) R mem aw rdata (cA, σ) (k + 3) (C + ((12))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 93) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 93)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 71. -/
theorem nestedCaller_block_71 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 568) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 71) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 568) ((memLoad (UInt256.ofNat 64) aw mem) :: x0 :: (UInt256.ofNat 84) :: R) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 8) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 84) (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 568) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 568)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 84. -/
theorem nestedCaller_block_84 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 84) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RDret NestedCaller.nestedCallerBytecode g s0 (cA, σ) (mem.readWithPadding (memLoad (UInt256.ofNat 64) aw mem).toNat (UInt256.sub x0 (memLoad (UInt256.ofNat 64) aw mem)).toNat) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r3 := RD.mload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup1 (by native_decide) (by evm_ov)
  have r5 := r4.swap2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  exact RD.ret r7 (by native_decide) (by evm_ov)

/-- Automatically generated RD summary for bytecode block at pc 93. -/
theorem nestedCaller_block_93_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 16))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 107) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 93) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 107) ((⟨0⟩ : UInt256) :: x0 :: R) mem aw rdata (cA, σ) (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 107) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 107)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 93. -/
theorem nestedCaller_block_93_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.gt x0 (UInt256.ofNat 16))) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 93) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 104) ((⟨0⟩ : UInt256) :: x0 :: R) mem aw rdata (cA, σ) (k + 8) (C + ((28))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.gt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 107) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 104)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 104. -/
theorem nestedCaller_block_104 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 104) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  exact RD.solcSummaryRevert0 (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 107. -/
theorem nestedCaller_block_107 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 107) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 116) ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: R) mem aw rdata (cA, σ) (k + 9) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push0 (by native_decide) (by evm_ov)
  have r7 := r6.push0 (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 116)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 116. -/
theorem nestedCaller_block_116_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 180) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 116) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 180) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 180) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 180)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 116. -/
theorem nestedCaller_block_116_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 x3)) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 116) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 125) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) (k + 7) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.lt (by native_decide) (by evm_ov)
  have r5 := r4.iszero (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 180) (by native_decide) (by evm_ov)
  have r7 := r6.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 125)) r7 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 125. -/
theorem nestedCaller_block_125 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 191) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 125) (x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 191) (x0 :: x4 :: (UInt256.ofNat 135) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: x3 :: x4 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((22))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 135) (by native_decide) (by evm_ov)
  have r3 := r2.dup7 (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 191) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 191)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 135. -/
theorem nestedCaller_block_135_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (⟨0⟩ : UInt256)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 150) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 135) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 150) (x0 :: R) mem aw rdata (cA, σ) (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 150) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 150)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 135. -/
theorem nestedCaller_block_135_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (⟨0⟩ : UInt256)) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 135) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 145) (x0 :: R) mem aw rdata (cA, σ) (k + 8) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.push0 (by native_decide) (by evm_ov)
  have r5 := r4.dup2 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 150) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 145)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 145. -/
theorem nestedCaller_block_145 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 169) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 145) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 169) R mem aw rdata (cA, σ) (k + 3) (C + ((13))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 169) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 169)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 150. -/
theorem nestedCaller_block_150_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 1)) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 164) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 150) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 164) (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 164)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 150. -/
theorem nestedCaller_block_150_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.sub x0 (UInt256.ofNat 1)) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 150) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 159) (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((23))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.sub (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 164) (by native_decide) (by evm_ov)
  have r6 := r5.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 159)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 159. -/
theorem nestedCaller_block_159 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 1 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 180) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 159) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 180) R mem aw rdata (cA, σ) (k + 3) (C + ((13))) := by
  let r0 := h
  have r1 := r0.pop (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 180) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 180)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 164. -/
theorem nestedCaller_block_164 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 164) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 169) (x1 :: x0 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((11))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.swap3 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 169)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 169. -/
theorem nestedCaller_block_169 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 116) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 169) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 116) (((UInt256.ofNat 1) + x0) :: R) mem aw rdata (cA, σ) (k + 8) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.add (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 116) (by native_decide) (by evm_ov)
  have r8 := r7.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 116)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 180. -/
theorem nestedCaller_block_180 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x5 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 180) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x5 (x1 :: R) mem aw rdata (cA, σ) (k + 11) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.dup1 (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 191. -/
theorem nestedCaller_block_191 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 191) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 194) ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: R) mem aw rdata (cA, σ) (k + 3) (C + ((5))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 194)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Execution split boundary at pc 194: gas (0x5a). No RD transition is asserted. Summaries resume at pc 195 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 195. -/
theorem nestedCaller_block_195_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 (UInt256.ofNat 1000))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 215) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 195) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 215) (x0 :: R) mem aw rdata (cA, σ) (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1000) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 215) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 215)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 195. -/
theorem nestedCaller_block_195_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.lt x0 (UInt256.ofNat 1000))) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 195) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 207) (x0 :: R) mem aw rdata (cA, σ) (k + 8) (C + ((30))) := by
  let r0 := h
  have r1 := r0.swap1 (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 1000) (by native_decide) (by evm_ov)
  have r4 := r3.dup2 (by native_decide) (by evm_ov)
  have r5 := r4.lt (by native_decide) (by evm_ov)
  have r6 := r5.iszero (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 215) (by native_decide) (by evm_ov)
  have r8 := r7.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 207)) r8 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 207. -/
theorem nestedCaller_block_207 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 340) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 207) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 340) ((⟨0⟩ : UInt256) :: R) mem aw rdata (cA, σ) (k + 6) (C + ((20))) := by
  let r0 := h
  have r1 := r0.push0 (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 340) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 340)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 215. -/
theorem nestedCaller_block_215 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 568) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 215) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 568) (((UInt256.ofNat 4) + (memLoad (UInt256.ofNat 64) aw mem)) :: x2 :: (UInt256.ofNat 272) :: (UInt256.ofNat 3674743872) :: (UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) x3) :: x0 :: x1 :: x2 :: x3 :: R) ((solcLeftAlignedSelectorWord (UInt256.ofNat 3674743872)).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) aw mem).toNat 32) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) aw mem) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 22) (C + ((69) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (memLoad (UInt256.ofNat 64) aw mem) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup4 (by native_decide) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r4 := r3.and (by native_decide) (by evm_ov)
  have r5 := r4.push4 (UInt256.ofNat 3674743872) (by native_decide) (by evm_ov)
  have r6 := r5.dup5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r8 := RD.mload r7 (by native_decide) (by evm_ov)
  have r9 := r8.dup3 (by native_decide) (by evm_ov)
  have r10 := RD.solcSummaryLeftAlignedSelector (by exact ⟨r9, by native_decide, by native_decide, by native_decide, by native_decide, by evm_ov⟩)
  have r11 := r10.dup2 (by native_decide) (by evm_ov)
  have r12 := RD.mstore r11 (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 4) (by native_decide) (by evm_ov)
  have r14 := r13.add (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 272) (by native_decide) (by evm_ov)
  have r16 := r15.swap2 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := r17.push2 (UInt256.ofNat 568) (by native_decide) (by evm_ov)
  have r19 := r18.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 568)) r19 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 272. -/
theorem nestedCaller_block_272 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 272) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 284) (x2 :: (⟨0⟩ : UInt256) :: (memLoad (UInt256.ofNat 64) aw mem) :: (UInt256.sub x0 (memLoad (UInt256.ofNat 64) aw mem)) :: (memLoad (UInt256.ofNat 64) aw mem) :: (UInt256.ofNat 32) :: x0 :: x1 :: x2 :: R) mem (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 10) (C + ((27) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r4 := RD.mload r3 (by native_decide) (by evm_ov)
  have r5 := r4.dup1 (by native_decide) (by evm_ov)
  have r6 := r5.dup4 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.dup8 (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 284)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/- Execution split boundary at pc 284: gas (0x5a). No RD transition is asserted. Summaries resume at pc 285 from a fresh symbolic RD state. -/

/- Unsupported instruction boundary at pc 285: call (0xf1). No RD transition is asserted. Summaries resume at pc 286 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 286. -/
theorem nestedCaller_block_286_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (solcCallSucceededWord x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 300) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 286) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 300) ((solcCallFailedWord x0) :: R) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := RD.solcSummaryCallSuccessCondition (target := (UInt256.ofNat 300)) (op := .PUSH2) (width := 2) (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by decide, by native_decide, by evm_ov⟩)
  have r2 := r1.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 300)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 286. -/
theorem nestedCaller_block_286_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (solcCallSucceededWord x0) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 286) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 293) ((solcCallFailedWord x0) :: R) mem aw rdata (cA, σ) (k + 5) (C + ((22))) := by
  let r0 := h
  have r1 := RD.solcSummaryCallSuccessCondition (target := (UInt256.ofNat 300)) (op := .PUSH2) (width := 2) (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by decide, by native_decide, by evm_ov⟩)
  have r2 := r1.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 293)) r2 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 293. -/
theorem nestedCaller_block_293 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 293) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  exact RD.solcSummaryReturnDataCopyRevert (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 300. -/
theorem nestedCaller_block_300 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 613) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 300) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 613) ((memLoad (UInt256.ofNat 64) aw mem) :: ((memLoad (UInt256.ofNat 64) aw mem) + (UInt256.ofNat rdata.size)) :: (UInt256.ofNat 336) :: R) (((memLoad (UInt256.ofNat 64) aw mem) + (UInt256.land ((UInt256.ofNat rdata.size) + (UInt256.ofNat 31)) (UInt256.lnot (UInt256.ofNat 31)))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32) (M (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 28) (C + ((81) + (memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) + (memExpansionCost (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) (UInt256.ofNat 64) (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r7 := RD.mload r6 (by native_decide) (by evm_ov)
  have r8 := r7.returndatasize (by native_decide) (by evm_ov)
  have r9 := r8.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r10 := r9.not (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 31) (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.add (by native_decide) (by evm_ov)
  have r14 := r13.and (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := r15.add (by native_decide) (by evm_ov)
  have r17 := r16.dup1 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := RD.mstore r18 (by native_decide) (by evm_ov)
  have r20 := r19.pop (by native_decide) (by evm_ov)
  have r21 := r20.dup2 (by native_decide) (by evm_ov)
  have r22 := r21.add (by native_decide) (by evm_ov)
  have r23 := r22.swap1 (by native_decide) (by evm_ov)
  have r24 := r23.push2 (UInt256.ofNat 336) (by native_decide) (by evm_ov)
  have r25 := r24.swap2 (by native_decide) (by evm_ov)
  have r26 := r25.swap1 (by native_decide) (by evm_ov)
  have r27 := r26.push2 (UInt256.ofNat 613) (by native_decide) (by evm_ov)
  have r28 := r27.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 613)) r28 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 336. -/
theorem nestedCaller_block_336 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 336) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 340) (x0 :: R) mem aw rdata (cA, σ) (k + 4) (C + ((8))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 340)) r4 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 340. -/
theorem nestedCaller_block_340 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 340) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 346. -/
theorem nestedCaller_block_346 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 346) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  exact RD.solcSummaryRevert0 (by exact ⟨r1, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 350. -/
theorem nestedCaller_block_350 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x1 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 350) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x1 ((UInt256.land x0 (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) :: R) mem aw rdata (cA, σ) (k + 11) (C + ((33))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push20 (UInt256.ofNat 1461501637330902918203684832716283019655932542975) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.and (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.swap2 (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.pop (by native_decide) (by evm_ov)
  have r11 := r10.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r11 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 381. -/
theorem nestedCaller_block_381 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 350) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 381) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 350) (x0 :: (UInt256.ofNat 391) :: (⟨0⟩ : UInt256) :: x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 391) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.push2 (UInt256.ofNat 350) (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 350)) r6 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 391. -/
theorem nestedCaller_block_391 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 391) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 (x0 :: R) mem aw rdata (cA, σ) (k + 7) (C + ((22))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.swap2 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r7 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 398. -/
theorem nestedCaller_block_398 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 381) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 398) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 381) (x0 :: (UInt256.ofNat 407) :: x0 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 407) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 381) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 381)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 407. -/
theorem nestedCaller_block_407_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 417) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 407) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 417) (x1 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 417) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 417)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 407. -/
theorem nestedCaller_block_407_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 x0) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 407) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 414) (x1 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 417) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 414)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 414. -/
theorem nestedCaller_block_414 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 414) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  exact RD.solcSummaryRevert0 (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 417. -/
theorem nestedCaller_block_417 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x1 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 417) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x1 R mem aw rdata (cA, σ) (k + 3) (C + ((11))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 420. -/
theorem nestedCaller_block_420 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 398) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 420) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 398) ((uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: (UInt256.ofNat 434) :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: x0 :: R) mem aw rdata (cA, σ) (k + 10) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 434) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 398) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 398)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 434. -/
theorem nestedCaller_block_434 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 434) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 440. -/
theorem nestedCaller_block_440 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x1 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 440) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x1 (x0 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((27))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.swap1 (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 449. -/
theorem nestedCaller_block_449 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 440) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 449) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 440) (x0 :: (UInt256.ofNat 458) :: x0 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 458) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 440) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 440)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 458. -/
theorem nestedCaller_block_458_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 x0) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 468) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 458) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 468) (x1 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 468) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 468)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 458. -/
theorem nestedCaller_block_458_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (hcond : (UInt256.eq x1 x0) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 458) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 465) (x1 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((20))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup2 (by native_decide) (by evm_ov)
  have r3 := r2.eq (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 468) (by native_decide) (by evm_ov)
  have r5 := r4.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 465)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 465. -/
theorem nestedCaller_block_465 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 465) R mem aw rdata (cA, σ) k C)
    : RDrev NestedCaller.nestedCallerBytecode g s0 := by
  let r0 := h
  exact RD.solcSummaryRevert0 (by exact ⟨r0, by native_decide, by native_decide, by native_decide, by evm_ov⟩)

/-- Automatically generated RD summary for bytecode block at pc 468. -/
theorem nestedCaller_block_468 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x1 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 468) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x1 R mem aw rdata (cA, σ) (k + 3) (C + ((11))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.pop (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 471. -/
theorem nestedCaller_block_471 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 449) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 471) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 449) ((uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: (UInt256.ofNat 485) :: (uInt256OfByteArray (ee.calldata.readBytes x0.toNat 32)) :: x0 :: R) mem aw rdata (cA, σ) (k + 10) (C + ((31))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.calldataload (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 485) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 449) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 449)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 485. -/
theorem nestedCaller_block_485 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 485) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 491. -/
theorem nestedCaller_block_491_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 513) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 491) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 513) ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 11) (C + ((36))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 513) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 513)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 491. -/
theorem nestedCaller_block_491_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 64))) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 491) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 505) ((⟨0⟩ : UInt256) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 11) (C + ((36))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push0 (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r5 := r4.dup4 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.sub (by native_decide) (by evm_ov)
  have r8 := r7.slt (by native_decide) (by evm_ov)
  have r9 := r8.iszero (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 513) (by native_decide) (by evm_ov)
  have r11 := r10.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 505)) r11 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 505. -/
theorem nestedCaller_block_505 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 346) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 505) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 346) ((UInt256.ofNat 512) :: R) mem aw rdata (cA, σ) (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 512) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 346) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 346)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 512. -/
theorem nestedCaller_block_512 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 512) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 513) R mem aw rdata (cA, σ) (k + 1) (C + ((1))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 513)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 513. -/
theorem nestedCaller_block_513 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 420) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 513) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 420) ((x2 + (⟨0⟩ : UInt256)) :: x3 :: (UInt256.ofNat 526) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 526) (by native_decide) (by evm_ov)
  have r4 := r3.dup6 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.dup7 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 420) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 420)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 526. -/
theorem nestedCaller_block_526 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 471) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 526) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 471) ((x4 + (UInt256.ofNat 32)) :: x5 :: (UInt256.ofNat 543) :: (UInt256.ofNat 32) :: x2 :: x0 :: x4 :: x5 :: R) mem aw rdata (cA, σ) (k + 12) (C + ((37))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r6 := r5.push2 (UInt256.ofNat 543) (by native_decide) (by evm_ov)
  have r7 := r6.dup6 (by native_decide) (by evm_ov)
  have r8 := r7.dup3 (by native_decide) (by evm_ov)
  have r9 := r8.dup7 (by native_decide) (by evm_ov)
  have r10 := r9.add (by native_decide) (by evm_ov)
  have r11 := r10.push2 (UInt256.ofNat 471) (by native_decide) (by evm_ov)
  have r12 := r11.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 471)) r12 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 543. -/
theorem nestedCaller_block_543 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 x6 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x6 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 543) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x6 (x0 :: x3 :: R) mem aw rdata (cA, σ) (k + 10) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.swap3 (by native_decide) (by evm_ov)
  have r8 := r7.swap1 (by native_decide) (by evm_ov)
  have r9 := r8.pop (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r10 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 553. -/
theorem nestedCaller_block_553 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 440) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 553) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 440) (x0 :: (UInt256.ofNat 562) :: x0 :: R) mem aw rdata (cA, σ) (k + 5) (C + ((18))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 562) (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := r3.push2 (UInt256.ofNat 440) (by native_decide) (by evm_ov)
  have r5 := r4.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 440)) r5 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 562. -/
theorem nestedCaller_block_562 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 562) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 R (x0.toByteArray.write 0 mem x2.toNat 32) (M aw x2 (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 6) (C + ((19) + (memExpansionCost aw x2 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.dup3 (by native_decide) (by evm_ov)
  have r3 := RD.mstore r2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 568. -/
theorem nestedCaller_block_568 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 553) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 568) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 553) (x1 :: (x0 + (⟨0⟩ : UInt256)) :: (UInt256.ofNat 587) :: (x0 + (UInt256.ofNat 32)) :: x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 14) (C + ((42))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.add (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 587) (by native_decide) (by evm_ov)
  have r9 := r8.push0 (by native_decide) (by evm_ov)
  have r10 := r9.dup4 (by native_decide) (by evm_ov)
  have r11 := r10.add (by native_decide) (by evm_ov)
  have r12 := r11.dup5 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 553) (by native_decide) (by evm_ov)
  have r14 := r13.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 553)) r14 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 587. -/
theorem nestedCaller_block_587 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 587) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 593. -/
theorem nestedCaller_block_593 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 449) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 593) (x0 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 449) ((memLoad x0 aw mem) :: (UInt256.ofNat 607) :: (memLoad x0 aw mem) :: x0 :: R) mem (M aw x0 (⟨32⟩ : UInt256)) rdata (cA, σ) (k + 10) (C + ((31) + (memExpansionCost aw x0 (⟨32⟩ : UInt256)))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.dup2 (by native_decide) (by evm_ov)
  have r4 := RD.mload r3 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := r5.pop (by native_decide) (by evm_ov)
  have r7 := r6.push2 (UInt256.ofNat 607) (by native_decide) (by evm_ov)
  have r8 := r7.dup2 (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 449) (by native_decide) (by evm_ov)
  have r10 := r9.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 449)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 607. -/
theorem nestedCaller_block_607 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x3 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 607) (x0 :: x1 :: x2 :: x3 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x3 (x0 :: R) mem aw rdata (cA, σ) (k + 6) (C + ((19))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap3 (by native_decide) (by evm_ov)
  have r3 := r2.swap2 (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.pop (by native_decide) (by evm_ov)
  have r6 := r5.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r6 (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 613. -/
theorem nestedCaller_block_613_taken {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) ≠ (UInt256.ofNat 0))
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 634) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 613) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 634) ((⟨0⟩ : UInt256) :: x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 634) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiT (by native_decide) hcond hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 634)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 613. -/
theorem nestedCaller_block_613_fallthrough {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hcond : (UInt256.isZero (UInt256.slt (UInt256.sub x1 x0) (UInt256.ofNat 32))) = (UInt256.ofNat 0))
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 613) (x0 :: x1 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 626) ((⟨0⟩ : UInt256) :: x0 :: x1 :: R) mem aw rdata (cA, σ) (k + 10) (C + ((34))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r4 := r3.dup3 (by native_decide) (by evm_ov)
  have r5 := r4.dup5 (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.slt (by native_decide) (by evm_ov)
  have r8 := r7.iszero (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 634) (by native_decide) (by evm_ov)
  have r10 := r9.jumpiNT (by native_decide) hcond (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 626)) r10 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 626. -/
theorem nestedCaller_block_626 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 346) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 626) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 346) ((UInt256.ofNat 633) :: R) mem aw rdata (cA, σ) (k + 3) (C + ((14))) := by
  let r0 := h
  have r1 := r0.push2 (UInt256.ofNat 633) (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 346) (by native_decide) (by evm_ov)
  have r3 := r2.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 346)) r3 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 633. -/
theorem nestedCaller_block_633 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {R : List UInt256}
    (hstack : R.length + 0 ≤ 1024)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 633) R mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 634) R mem aw rdata (cA, σ) (k + 1) (C + ((1))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 634)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 634. -/
theorem nestedCaller_block_634 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains (UInt256.ofNat 593) = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 634) (x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 593) ((x1 + (⟨0⟩ : UInt256)) :: x2 :: (UInt256.ofNat 647) :: (⟨0⟩ : UInt256) :: x0 :: x1 :: x2 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((29))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.push0 (by native_decide) (by evm_ov)
  have r3 := r2.push2 (UInt256.ofNat 647) (by native_decide) (by evm_ov)
  have r4 := r3.dup5 (by native_decide) (by evm_ov)
  have r5 := r4.dup3 (by native_decide) (by evm_ov)
  have r6 := r5.dup6 (by native_decide) (by evm_ov)
  have r7 := r6.add (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 593) (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 593)) r9 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Automatically generated RD summary for bytecode block at pc 647. -/
theorem nestedCaller_block_647 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 x3 x4 x5 : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J NestedCaller.nestedCallerBytecode 0).contains x5 = true)
    (h : RD NestedCaller.nestedCallerBytecode ee g s0 (UInt256.ofNat 647) (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: R) mem aw rdata (cA, σ) k C)
    : RD NestedCaller.nestedCallerBytecode ee g s0 x5 (x0 :: R) mem aw rdata (cA, σ) (k + 9) (C + ((26))) := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap2 (by native_decide) (by evm_ov)
  have r3 := r2.pop (by native_decide) (by evm_ov)
  have r4 := r3.pop (by native_decide) (by evm_ov)
  have r5 := r4.swap3 (by native_decide) (by evm_ov)
  have r6 := r5.swap2 (by native_decide) (by evm_ov)
  have r7 := r6.pop (by native_decide) (by evm_ov)
  have r8 := r7.pop (by native_decide) (by evm_ov)
  have r9 := r8.jump (by native_decide) hvalid (by evm_ov)
  exact RD.normalizeCounters r9 (by omega) (by omega)

end nestedCallerBlocks
