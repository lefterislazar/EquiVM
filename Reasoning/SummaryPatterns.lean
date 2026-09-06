import Reasoning.Solc

/-!
Small, hypothesis-free Solidity bytecode sequences used by the generated RD block
summaries.  These are deliberately separate from the more general pattern library:
each well-formedness predicate packages the incoming cursor, exact decode facts,
and the one stack-capacity fact needed by the sequence.
-/

namespace Reasoning.Theory

open ABI Ethereum Ethereum.EVM Reasoning.Reach

theorem solcSummaryReturnDataCopyGuard (rdata : ByteArray) :
    (⟨0⟩ : UInt256).toNat + (UInt256.ofNat rdata.size).toNat ≤ rdata.size := by
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]
  set c := UInt256.ofNat rdata.size with hc
  have hcle : c.toNat ≤ rdata.size := by
    rw [hc]
    exact Nat.mod_le _ _
  simpa only [Nat.zero_add, hc] using hcle

@[reducible] def solcSummaryFreeMemoryPointerWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨128⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2) = some (.MSTORE, .none) ∧
  stk.length + 2 ≤ 1024

theorem RD.solcSummaryFreeMemoryPointer
    (hwf : solcSummaryFreeMemoryPointerWf code ee g s0 pc stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) stk
      ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)
      (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata acc
      (k + 3) (C + (9 + memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hov⟩
  have r1 := h.push1 (UInt256.ofNat 128) hd0 (by omega)
  have r2 := r1.push1 (UInt256.ofNat 64) hd1 (by simp only [List.length_cons]; omega)
  have r3 := RD.mstore r2 hd2 (by omega)
  exact RD.normalizeCounters r3 (by omega) (by omega)

@[reducible] def solcSummaryAddressMaskWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2) =
    some (.Push .PUSH1, some (⟨160⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2) =
    some (.SHL, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
    some (.SUB, .none) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryAddressMask
    (hwf : solcSummaryAddressMaskWf code ee g s0 pc stk mem aw rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
      (solcAddrMask :: stk) mem aw rdata acc (k + 5) (C + 15) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hd4, hov⟩
  have r1 := h.push1 (UInt256.ofNat 1) hd0 (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) hd1 (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) hd2 (by evm_ov)
  have r4 := r3.shl hd3 (by evm_ov)
  have r5 := r4.sub hd4 (by evm_ov)
  simpa [solcAddrMask] using RD.normalizeCounters r5 (by omega) (by omega)

@[reducible] def solcSummaryFreeMemoryPointerLoadWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.DUP1, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none) ∧
  stk.length + 2 ≤ 1024

theorem RD.solcSummaryFreeMemoryPointerLoad
    (hwf : solcSummaryFreeMemoryPointerLoadWf code ee g s0 pc stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩)
      (memLoad (UInt256.ofNat 64) aw mem :: UInt256.ofNat 64 :: stk) mem
      (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata acc (k + 3)
      (C + (9 + memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hov⟩
  have r1 := h.push1 (UInt256.ofNat 64) hd0 (by evm_ov)
  have r2 := r1.dup1 hd1 (by evm_ov)
  have r3 := RD.mload r2 hd2 (by evm_ov)
  exact RD.normalizeCounters r3 (by omega) (by omega)

@[reducible] def solcSummaryErrorSelectorStoreWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc base : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (base :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH3, some (⟨4594637⟩, 3)) ∧
  decode code (pc + UInt256.ofNat 4) = some (.Push .PUSH1, some (⟨229⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 4 + UInt256.ofNat 2) = some (.SHL, .none) ∧
  decode code (pc + UInt256.ofNat 4 + UInt256.ofNat 2 + ⟨1⟩) = some (.DUP2, .none) ∧
  decode code (pc + UInt256.ofNat 4 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
    some (.MSTORE, .none) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryErrorSelectorStore
    (hwf : solcSummaryErrorSelectorStoreWf code ee g s0 pc base stk mem aw rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 4 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (base :: stk)
      (solcErrorStringSelector.toByteArray.write 0 mem base.toNat 32)
      (M aw base (⟨32⟩ : UInt256)) rdata acc (k + 5)
      (C + (15 + memExpansionCost aw base (⟨32⟩ : UInt256))) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hd4, hov⟩
  have r1 := h.pushConst (UInt256.ofNat 4594637) (width := 3) (op := .PUSH3)
    (by decide) hd0 (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 229) hd1 (by evm_ov)
  have r3 := r2.shl hd2 (by evm_ov)
  have r4 := r3.dup2 hd3 (by evm_ov)
  have r5 := RD.mstore r4 hd4 (by evm_ov)
  simpa [solcErrorStringSelector] using RD.normalizeCounters r5 (by omega) (by omega)

@[reducible] def solcSummaryErrorRevertFinalizerWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (a b c : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (k C : ℕ) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  RD code ee g s0 pc (a :: b :: c :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨68⟩, 1)) ∧
  decode code p2 = some (.DUP3, .none) ∧
  decode code p3 = some (.ADD, .none) ∧
  decode code p4 = some (.MSTORE, .none) ∧
  decode code p5 = some (.SWAP1, .none) ∧
  decode code p6 = some (.MLOAD, .none) ∧
  decode code p7 = some (.SWAP1, .none) ∧
  decode code p8 = some (.DUP2, .none) ∧
  decode code p9 = some (.SWAP1, .none) ∧
  decode code p10 = some (.SUB, .none) ∧
  decode code p11 = some (.Push .PUSH1, some (⟨100⟩, 1)) ∧
  decode code p13 = some (.ADD, .none) ∧
  decode code p14 = some (.SWAP1, .none) ∧
  decode code p15 = some (.REVERT, .none) ∧
  stk.length + 5 ≤ 1024

theorem RD.solcSummaryErrorRevertFinalizer
    (hwf : solcSummaryErrorRevertFinalizerWf code ee g s0 pc a b c stk mem aw rdata acc k C) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨h, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12,
      hd13, hov⟩
  have r1 := h.push1 (UInt256.ofNat 68) hd0 (by evm_ov)
  have r2 := r1.dup3 hd1 (by evm_ov)
  have r3 := r2.add hd2 (by evm_ov)
  have r4 := RD.mstore r3 hd3 (by evm_ov)
  have r5 := r4.swap1 hd4 (by evm_ov)
  have r6 := RD.mload r5 hd5 (by evm_ov)
  have r7 := r6.swap1 hd6 (by evm_ov)
  have r8 := r7.dup2 hd7 (by evm_ov)
  have r9 := r8.swap1 hd8 (by evm_ov)
  have r10 := r9.sub hd9 (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 100) hd10 (by evm_ov)
  have r12 := r11.add hd11 (by evm_ov)
  have r13 := r12.swap1 hd12 (by evm_ov)
  exact r13.rev hd13 (by evm_ov)

@[reducible] def solcSummaryRevert0Wf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.PUSH0, .none) ∧
  decode code (pc + ⟨1⟩) = some (.PUSH0, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.REVERT, .none) ∧
  stk.length + 2 ≤ 1024

theorem RD.solcSummaryRevert0
    (hwf : solcSummaryRevert0Wf code ee g s0 pc stk mem aw rdata acc k C) :
    RDrev code g s0 := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hov⟩
  exact RD.revertStub h hd0 hd1 hd2 hov

@[reducible] def solcSummaryLegacyRevert0Wf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.DUP1, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.REVERT, .none) ∧
  stk.length + 2 ≤ 1024

theorem RD.solcSummaryLegacyRevert0
    (hwf : solcSummaryLegacyRevert0Wf code ee g s0 pc stk mem aw rdata acc k C) :
    RDrev code g s0 := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hov⟩
  exact RD.solcPush1Dup1Revert0 h hd0 hd1 hd2 hov

@[reducible] def solcSummaryReturnDataCopyRevertWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩) = some (.PUSH0, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.RETURNDATACOPY, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.PUSH0, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.REVERT, .none) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryReturnDataCopyRevert
    (hwf : solcSummaryReturnDataCopyRevertWf code ee g s0 pc stk mem aw rdata acc k C) :
    RDrev code g s0 := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hov⟩
  obtain ⟨mem', aw', k', C', r4⟩ := RD.returndatacopyFull h hd0 hd1 hd2 hd3 hov
  exact r4.returndatasize hd4 (by omega)
    |>.push0 hd5 (by simp only [List.length_cons]; omega)
    |>.rev hd6 (by omega)

@[reducible] def solcSummaryLegacyReturnDataCopyRevertWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.RETURNDATACOPY, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
    some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    UInt256.ofNat 2) = some (.REVERT, .none) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryLegacyReturnDataCopyRevert
    (hwf : solcSummaryLegacyReturnDataCopyRevertWf code ee g s0 pc stk mem aw rdata acc k C) :
    RDrev code g s0 := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hov⟩
  have r1 := h.returndatasize hd0 (by omega)
  have r2 := r1.push1 ⟨0⟩ hd1 (by simp only [List.length_cons]; omega)
  have r3 := r2.dup1 hd2 (by simp only [List.length_cons]; omega)
  have r4 := RD.returndatacopy r3 hd3 (solcSummaryReturnDataCopyGuard rdata) (by omega)
  exact r4.returndatasize hd4 (by omega)
    |>.push1 ⟨0⟩ hd5 (by simp only [List.length_cons]; omega)
    |>.rev hd6 (by omega)

@[reducible] def solcSummarySelectorLoadWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc : UInt256) (rest : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc rest mem aw rdata acc k C ∧
  decode code pc = some (.PUSH0, .none) ∧
  decode code (pc + ⟨1⟩) = some (.CALLDATALOAD, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨224⟩, 1)) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.SHR, .none) ∧
  rest.length + 2 ≤ 1024

theorem RD.solcSummarySelectorLoad
    (hwf : solcSummarySelectorLoadWf code ee g s0 pc rest mem aw rdata acc k C) :
    RD code ee g s0 (pc + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
      (solcSelectorWord ee :: rest) mem aw rdata acc (k + 4) (C + 11) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hov⟩
  have r1 := h.push0 hd0 (by omega)
  have r2 := r1.calldataload hd1 (by omega)
  have r3 := r2.push1 ⟨224⟩ hd2 (by simp only [List.length_cons]; omega)
  have r4 := r3.shr hd3 (by omega)
  simpa [solcSelectorWord] using RD.normalizeCounters r4 (by omega) (by omega)

@[reducible] def solcSummaryLegacySelectorLoadWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc : UInt256)
    (rest : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc rest mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.CALLDATALOAD, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩) =
    some (.Push .PUSH1, some (⟨224⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) = some (.SHR, .none) ∧
  rest.length + 2 ≤ 1024

theorem RD.solcSummaryLegacySelectorLoad
    (hwf : solcSummaryLegacySelectorLoadWf code ee g s0 pc rest mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩)
      (solcSelectorWord ee :: rest) mem aw rdata acc (k + 4) (C + 12) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hov⟩
  have r1 := h.push1 ⟨0⟩ hd0 (by omega)
  have r2 := r1.calldataload hd1 (by omega)
  have r3 := r2.push1 ⟨224⟩ hd2 (by simp only [List.length_cons]; omega)
  have r4 := r3.shr hd3 (by omega)
  simpa [solcSelectorWord] using RD.normalizeCounters r4 (by omega) (by omega)

end Reasoning.Theory
