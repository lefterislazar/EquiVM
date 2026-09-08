import Reasoning.Solc

/-!
Small, hypothesis-free Solidity bytecode sequences used by the generated RD block
summaries.  These are deliberately separate from the more general pattern library:
each well-formedness predicate packages the incoming cursor, exact decode facts,
and the one stack-capacity fact needed by the sequence.
-/

namespace Reasoning.Theory

open ABI Ethereum Ethereum.EVM Reasoning.Reach

private theorem u256_ofNat_add (a b : ℕ) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  change ((a % UInt256.size) + (b % UInt256.size)) % UInt256.size =
    (a + b) % UInt256.size
  simp only [Nat.add_mod, Nat.mod_mod]

private theorem u256_add_ofNat_ofNat (pc : UInt256) (a b : ℕ) :
    pc + UInt256.ofNat a + UInt256.ofNat b = pc + UInt256.ofNat (a + b) := by
  rw [u256_add_assoc, u256_ofNat_add]

/-! ## Canonical words exposed by generated summaries -/

/-- The low-`bits` mask constructed by `1; 1; bits; SHL; SUB`. -/
def solcLowMask (bits : UInt256) : UInt256 :=
  UInt256.sub (UInt256.shiftLeft ⟨1⟩ bits) ⟨1⟩

theorem solcLowMask_eq (bits : UInt256) :
    solcLowMask bits = UInt256.sub (UInt256.shiftLeft ⟨1⟩ bits) ⟨1⟩ := rfl

/-- The all-ones EVM word constructed by `PUSH1 0; NOT`. -/
def solcUintMax : UInt256 := UInt256.lnot ⟨0⟩

theorem solcUintMax_toNat : solcUintMax.toNat = UInt256.size - 1 := by
  unfold solcUintMax UInt256.lnot
  decide

/-- A selector placed in the high four bytes of an ABI call-data word. -/
def solcLeftAlignedSelectorWord (selector : UInt256) : UInt256 :=
  UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ selector) ⟨224⟩

theorem solcLeftAlignedSelectorWord_eq (selector : UInt256) :
    solcLeftAlignedSelectorWord selector =
      UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ selector) ⟨224⟩ := rfl

/-- EVM Boolean normalization: one exactly when `word` is nonzero. -/
def solcBoolWord (word : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero word)

/-- The equality word used by a Solidity selector arm. -/
def solcSelectorMatches (expected actual : UInt256) : UInt256 := UInt256.eq expected actual

/-- The comparison word used by a Solidity binary-search selector split. -/
def solcSelectorBelowPivot (pivot actual : UInt256) : UInt256 := UInt256.gt pivot actual

/-- The pair of Boolean words retained by solc's call-success guard. -/
def solcCallFailedWord (status : UInt256) : UInt256 := UInt256.isZero status
def solcCallSucceededWord (status : UInt256) : UInt256 := solcBoolWord status

/-- Nonzero exactly when calldata is too short to contain a selector. -/
def solcCalldataTooShortWord (size : UInt256) : UInt256 := UInt256.lt size ⟨4⟩

/-- Nonzero when the calldata tail after the selector contains `need` bytes. -/
def solcStaticArgsSufficientWord (size need : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.lt (UInt256.sub size ⟨4⟩) need)

/-- Nonzero when returndata contains at least one ABI word. -/
def solcReturnWordAvailableWord (size : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.lt size ⟨32⟩)

/-- The success condition constructed by solc's checked-add helper. -/
def solcCheckedAddOkWord (a b : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.lt (a + b) a)

/-- The success condition constructed by solc's checked-sub helper. -/
def solcCheckedSubOkWord (a b : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.gt (UInt256.sub a b) a)

theorem solcBoolWord_eq (word : UInt256) :
    solcBoolWord word = UInt256.isZero (UInt256.isZero word) := rfl
theorem solcSelectorMatches_eq (expected actual : UInt256) :
    solcSelectorMatches expected actual = UInt256.eq expected actual := rfl
theorem solcSelectorBelowPivot_eq (pivot actual : UInt256) :
    solcSelectorBelowPivot pivot actual = UInt256.gt pivot actual := rfl
theorem solcCallSucceededWord_eq (status : UInt256) :
    solcCallSucceededWord status = UInt256.isZero (UInt256.isZero status) := rfl
theorem solcStaticArgsSufficientWord_eq (size need : UInt256) :
    solcStaticArgsSufficientWord size need =
      UInt256.isZero (UInt256.lt (UInt256.sub size ⟨4⟩) need) := rfl
theorem solcReturnWordAvailableWord_eq (size : UInt256) :
    solcReturnWordAvailableWord size = UInt256.isZero (UInt256.lt size ⟨32⟩) := rfl
theorem solcCheckedAddOkWord_eq (a b : UInt256) :
    solcCheckedAddOkWord a b = UInt256.isZero (UInt256.lt (a + b) a) := rfl
theorem solcCheckedSubOkWord_eq (a b : UInt256) :
    solcCheckedSubOkWord a b = UInt256.isZero (UInt256.gt (UInt256.sub a b) a) := rfl

theorem twoWordHashMem_keccak_solcMappingSlot (key slot : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key slot mem) = solcMappingSlot slot key := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    twoWordHashMem_read0_64_any]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

theorem twoWordHashMemSlotFirst_keccak_solcMappingSlot
    (key slot : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMemSlotFirst key slot mem) =
      solcMappingSlot slot key := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    twoWordHashMemSlotFirst_read0_64_any]
  unfold solcMappingSlot
  exact mappingSlot_single key slot

theorem twoWordHashMem_keccak_solcMappingSlot_ofNat (key slot : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem key slot mem) =
      solcMappingSlot slot key := by
  simpa using twoWordHashMem_keccak_solcMappingSlot key slot mem

theorem twoWordHashMemSlotFirst_keccak_solcMappingSlot_ofNat
    (key slot : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMemSlotFirst key slot mem) = solcMappingSlot slot key := by
  simpa using twoWordHashMemSlotFirst_keccak_solcMappingSlot key slot mem

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
    RD code ee g s0 (pc + UInt256.ofNat 5) stk
      ((UInt256.ofNat 128).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)
      (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata acc
      (k + 3) (C + (9 + memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hov⟩
  have r1 := h.push1 (UInt256.ofNat 128) hd0 (by omega)
  have r2 := r1.push1 (UInt256.ofNat 64) hd1 (by simp only [List.length_cons]; omega)
  have r3 := RD.mstore r2 hd2 (by omega)
  simpa only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
    u256_add_assoc, u256_ofNat_add, Nat.reduceAdd] using
    RD.normalizeCounters r3 (by omega) (by omega)

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
      (pc + UInt256.ofNat 8)
      (solcAddrMask :: stk) mem aw rdata acc (k + 5) (C + 15) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hd4, hov⟩
  have r1 := h.push1 (UInt256.ofNat 1) hd0 (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) hd1 (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) hd2 (by evm_ov)
  have r4 := r3.shl hd3 (by evm_ov)
  have r5 := r4.sub hd4 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 8) r5
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcAddrMask, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

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
    RD code ee g s0 (pc + UInt256.ofNat 4)
      (memLoad (UInt256.ofNat 64) aw mem :: UInt256.ofNat 64 :: stk) mem
      (M aw (UInt256.ofNat 64) (⟨32⟩ : UInt256)) rdata acc (k + 3)
      (C + (9 + memExpansionCost aw (UInt256.ofNat 64) (⟨32⟩ : UInt256))) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hov⟩
  have r1 := h.push1 (UInt256.ofNat 64) hd0 (by evm_ov)
  have r2 := r1.dup1 hd1 (by evm_ov)
  have r3 := RD.mload r2 hd2 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 4) r3
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  exact RD.normalizeCounters rFinalPc (by omega) (by omega)

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
      (pc + UInt256.ofNat 9)
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
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 9) r5
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat])
  simpa [solcErrorStringSelector, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

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
  have r4 := RD.returndatacopyFull h hd0 hd1 hd2 hd3 hov
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
  have r4 := RD.returndatacopyFullPush1Dup1 h hd0 hd1 hd2 hd3 hov
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
    RD code ee g s0 (pc + UInt256.ofNat 5)
      (solcSelectorWord ee :: rest) mem aw rdata acc (k + 4) (C + 11) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hov⟩
  have r1 := h.push0 hd0 (by omega)
  have r2 := r1.calldataload hd1 (by omega)
  have r3 := r2.push1 ⟨224⟩ hd2 (by simp only [List.length_cons]; omega)
  have r4 := r3.shr hd3 (by omega)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 5) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcSelectorWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

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
    RD code ee g s0 (pc + UInt256.ofNat 6)
      (solcSelectorWord ee :: rest) mem aw rdata acc (k + 4) (C + 12) := by
  rcases hwf with ⟨h, hd0, hd1, hd2, hd3, hov⟩
  have r1 := h.push1 ⟨0⟩ hd0 (by omega)
  have r2 := r1.calldataload hd1 (by omega)
  have r3 := r2.push1 ⟨224⟩ hd2 (by simp only [List.length_cons]; omega)
  have r4 := r3.shr hd3 (by omega)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 6) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcSelectorWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

/-! ## Parameterized word-building patterns -/

@[reducible] def solcSummaryLowMaskWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc bits : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2) =
    some (.Push .PUSH1, some (bits, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2) =
    some (.SHL, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
    some (.SUB, .none) ∧ stk.length + 3 ≤ 1024

theorem RD.solcSummaryLowMask
    (hwf : solcSummaryLowMaskWf code ee g s0 pc bits stk mem aw rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 8)
      (solcLowMask bits :: stk) mem aw rdata acc
      (k + 5) (C + 15) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, hov⟩
  have r1 := h.push1 ⟨1⟩ h0 (by omega)
  have r2 := r1.push1 ⟨1⟩ h1 (by evm_ov)
  have r3 := r2.push1 bits h2 (by evm_ov)
  have r4 := r3.shl h3 (by evm_ov)
  have r5 := r4.sub h4 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 8) r5
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcLowMask, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryUintMaxWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.NOT, .none) ∧ stk.length + 1 ≤ 1024

theorem RD.solcSummaryUintMax
    (hwf : solcSummaryUintMaxWf code ee g s0 pc stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 3) (solcUintMax :: stk)
      mem aw rdata acc (k + 2) (C + 6) := by
  rcases hwf with ⟨h, h0, h1, hov⟩
  have r1 := h.push1 ⟨0⟩ h0 (by omega)
  have r2 := r1.not h1 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 3) r2
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcUintMax, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryLeftAlignedSelectorWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc selector : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (selector :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH4, some (⟨4294967295⟩, 4)) ∧
  decode code (pc + UInt256.ofNat 5) = some (.AND, .none) ∧
  decode code (pc + UInt256.ofNat 5 + ⟨1⟩) =
    some (.Push .PUSH1, some (⟨224⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2) =
    some (.SHL, .none) ∧ stk.length + 2 ≤ 1024

theorem RD.solcSummaryLeftAlignedSelector
    (hwf : solcSummaryLeftAlignedSelectorWf code ee g s0 pc selector stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 9)
      (solcLeftAlignedSelectorWord selector :: stk)
      mem aw rdata acc (k + 4) (C + 12) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, hov⟩
  have r1 := h.push4 ⟨4294967295⟩ h0 (by evm_ov)
  have r2 := r1.and h1 (by evm_ov)
  have r3 := r2.push1 ⟨224⟩ h2 (by evm_ov)
  have r4 := r3.shl h3 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 9) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcLeftAlignedSelectorWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryBoolNormalizeWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc word : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (word :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.ISZERO, .none) ∧
  decode code (pc + ⟨1⟩) = some (.ISZERO, .none) ∧ stk.length + 1 ≤ 1024

theorem RD.solcSummaryBoolNormalize
    (hwf : solcSummaryBoolNormalizeWf code ee g s0 pc word stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 2) (solcBoolWord word :: stk) mem aw rdata acc
      (k + 2) (C + 6) := by
  rcases hwf with ⟨h, h0, h1, hov⟩
  have r1 := h.iszero h0 (by omega)
  have r2 := r1.iszero h1 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 2) r2
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcBoolWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

/-! ## Condition-producing prefixes (the following JUMPI remains primitive) -/

@[reducible] def solcSummarySelectorConditionWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc actual expected target : UInt256)
    (op : Operation.POp) (width : ℕ) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (actual :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH4, some (expected, 4)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 5) = some (.EQ, .none) ∧ op ≠ .PUSH0 ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩) =
    some (.Push op, some (target, width)) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummarySelectorCondition
    (hwf : solcSummarySelectorConditionWf code ee g s0 pc actual expected target op width
      stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat (7 + width.succ))
      (target :: solcSelectorMatches expected actual :: actual :: stk)
      mem aw rdata acc (k + 4) (C + 12) := by
  rcases hwf with ⟨h, h0, h1, h2, hop, h3, hov⟩
  have r1 := h.dup1 h0 (by evm_ov)
  have r2 := r1.push4 expected h1 (by evm_ov)
  have r3 := r2.eq h2 (by evm_ov)
  have r4 := r3.pushConst target hop h3 (by evm_ov)
  have rFinalPc := RD.normalizePC
      (pc' := pc + UInt256.ofNat (7 + width.succ)) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcSelectorMatches, u256_add_assoc, u256_ofNat_add] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummarySelectorSplitConditionWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc actual pivot target : UInt256)
    (op : Operation.POp) (width : ℕ) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (actual :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH4, some (pivot, 4)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 5) = some (.GT, .none) ∧ op ≠ .PUSH0 ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩) =
    some (.Push op, some (target, width)) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummarySelectorSplitCondition
    (hwf : solcSummarySelectorSplitConditionWf code ee g s0 pc actual pivot target op width
      stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat (7 + width.succ))
      (target :: solcSelectorBelowPivot pivot actual :: actual :: stk)
      mem aw rdata acc (k + 4) (C + 12) := by
  rcases hwf with ⟨h, h0, h1, h2, hop, h3, hov⟩
  have r1 := h.dup1 h0 (by evm_ov)
  have r2 := r1.push4 pivot h1 (by evm_ov)
  have r3 := r2.gt h2 (by evm_ov)
  have r4 := r3.pushConst target hop h3 (by evm_ov)
  have rFinalPc := RD.normalizePC
      (pc' := pc + UInt256.ofNat (7 + width.succ)) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcSelectorBelowPivot, u256_add_assoc, u256_ofNat_add] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryCallSuccessConditionWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc status target : UInt256) (op : Operation.POp)
    (width : ℕ) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (k C : ℕ) : Prop :=
  RD code ee g s0 pc (status :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.ISZERO, .none) ∧
  decode code (pc + ⟨1⟩) = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none) ∧ op ≠ .PUSH0 ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.Push op, some (target, width)) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryCallSuccessCondition
    (hwf : solcSummaryCallSuccessConditionWf code ee g s0 pc status target op width
      stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat (3 + width.succ))
      (target :: solcCallSucceededWord status :: solcCallFailedWord status :: stk)
      mem aw rdata acc (k + 4) (C + 12) := by
  rcases hwf with ⟨h, h0, h1, h2, hop, h3, hov⟩
  have r1 := h.iszero h0 (by evm_ov)
  have r2 := r1.dup1 h1 (by evm_ov)
  have r3 := r2.iszero h2 (by evm_ov)
  have r4 := r3.pushConst target hop h3 (by evm_ov)
  have rFinalPc := RD.normalizePC
      (pc' := pc + UInt256.ofNat (3 + width.succ)) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcCallSucceededWord, solcCallFailedWord, solcBoolWord, u256_add_assoc,
    u256_ofNat_add] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryCallvalueConditionWf (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (pc : UInt256) (stk : List UInt256)
    (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.CALLVALUE, .none) ∧
  decode code (pc + ⟨1⟩) = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none) ∧ stk.length + 2 ≤ 1024

theorem RD.solcSummaryCallvalueCondition
    (hwf : solcSummaryCallvalueConditionWf code ee g s0 pc stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat 3)
      (solcCallFailedWord ee.weiValue :: ee.weiValue :: stk)
      mem aw rdata acc (k + 3) (C + 8) := by
  rcases hwf with ⟨h, h0, h1, h2, hov⟩
  have r1 := h.callvalue h0 (by evm_ov)
  have r2 := r1.dup1 h1 (by evm_ov)
  have r3 := r2.iszero h2 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 3) r3
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcCallFailedWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryCalldataSizeConditionWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc target : UInt256)
    (op : Operation.POp) (width : ℕ) (stk : List UInt256) (mem : ByteArray)
    (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none) ∧ op ≠ .PUSH0 ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
    some (.Push op, some (target, width)) ∧
  stk.length + 2 ≤ 1024

theorem RD.solcSummaryCalldataSizeCondition
    (hwf : solcSummaryCalldataSizeConditionWf code ee g s0 pc target op width
      stk mem aw rdata acc k C) :
    RD code ee g s0 (pc + UInt256.ofNat (4 + width.succ))
      (target :: solcCalldataTooShortWord (UInt256.ofNat ee.calldata.size) :: stk)
      mem aw rdata acc (k + 4) (C + 11) := by
  rcases hwf with ⟨h, h0, h1, h2, hop, h3, hov⟩
  have r1 := h.push1 ⟨4⟩ h0 (by evm_ov)
  have r2 := r1.calldatasize h1 (by evm_ov)
  have r3 := r2.lt h2 (by evm_ov)
  have r4 := r3.pushConst target hop h3 (by evm_ov)
  have rFinalPc := RD.normalizePC
      (pc' := pc + UInt256.ofNat (4 + width.succ)) r4
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcCalldataTooShortWord, u256_add_assoc, u256_ofNat_add] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryReturnDataSizeConditionWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc target : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.RETURNDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP2, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
    some (.ISZERO, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.Push .PUSH2, some (target, 2)) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryReturnDataSizeCondition
    (hwf : solcSummaryReturnDataSizeConditionWf code ee g s0 pc target stk mem aw rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 9)
      (target :: solcReturnWordAvailableWord (UInt256.ofNat rdata.size) ::
        UInt256.ofNat rdata.size :: stk)
      mem aw rdata acc (k + 6) (C + 17) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, hov⟩
  have r1 := h.returndatasize h0 (by evm_ov)
  have r2 := r1.push1 ⟨32⟩ h1 (by evm_ov)
  have r3 := r2.dup2 h2 (by evm_ov)
  have r4 := r3.lt h3 (by evm_ov)
  have r5 := r4.iszero h4 (by evm_ov)
  have r6 := r5.push2 target h5 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 9) r6
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcReturnWordAvailableWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryStaticArgsConditionWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc ret need target : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc stk mem aw rdata acc k C ∧
  decode code pc = some (.JUMPDEST, .none) ∧
  decode code (pc + ⟨1⟩) = some (.Push .PUSH2, some (ret, 2)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3) = some (.Push .PUSH1, some (⟨4⟩, 1)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2) = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩) =
    some (.CALLDATASIZE, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
    some (.SUB, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.Push .PUSH1, some (need, 1)) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    UInt256.ofNat 2) = some (.DUP2, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.ISZERO, .none) ∧
  decode code (pc + ⟨1⟩ + UInt256.ofNat 3 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
    UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH2, some (target, 2)) ∧
  stk.length + 5 ≤ 1024

theorem RD.solcSummaryStaticArgsCondition
    (hwf : solcSummaryStaticArgsConditionWf code ee g s0 pc ret need target stk mem aw
      rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 17)
      (target :: solcStaticArgsSufficientWord (UInt256.ofNat ee.calldata.size) need ::
        UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: stk)
      mem aw rdata acc (k + 11) (C + 30) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hov⟩
  have r1 := h.jumpdest h0 (by evm_ov)
  have r2 := r1.push2 ret h1 (by evm_ov)
  have r3 := r2.push1 ⟨4⟩ h2 (by evm_ov)
  have r4 := r3.dup1 h3 (by evm_ov)
  have r5 := r4.calldatasize h4 (by evm_ov)
  have r6 := r5.sub h5 (by evm_ov)
  have r7 := r6.push1 need h6 (by evm_ov)
  have r8 := r7.dup2 h7 (by evm_ov)
  have r9 := r8.lt h8 (by evm_ov)
  have r10 := r9.iszero h9 (by evm_ov)
  have r11 := r10.push2 target h10 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 17) r11
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcStaticArgsSufficientWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryCheckedArithmeticWf (arith cmp : Operation)
    (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (pc target b a : UInt256) (stk : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (acc : Batteries.RBSet AccountAddress compare × AccountMap)
    (k C : ℕ) : Prop :=
  RD code ee g s0 pc (b :: a :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.JUMPDEST, .none) ∧
  decode code (pc + ⟨1⟩) = some (.DUP1, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.DUP3, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (arith, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.DUP3, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.DUP2, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (cmp, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.ISZERO, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.Push .PUSH2, some (target, 2)) ∧ stk.length + 5 ≤ 1024

theorem RD.solcSummaryCheckedAddCondition
    (hwf : solcSummaryCheckedArithmeticWf .ADD .LT code ee g s0 pc target b a stk
      mem aw rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 11)
      (target :: solcCheckedAddOkWord a b :: (a + b) :: b :: a :: stk)
      mem aw rdata acc (k + 9) (C + 25) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, h6, h7, h8, hov⟩
  have r1 := h.jumpdest h0 (by evm_ov)
  have r2 := r1.dup1 h1 (by evm_ov)
  have r3 := r2.dup3 h2 (by evm_ov)
  have r4 := r3.add h3 (by evm_ov)
  have r5 := r4.dup3 h4 (by evm_ov)
  have r6 := r5.dup2 h5 (by evm_ov)
  have r7 := r6.lt h6 (by evm_ov)
  have r8 := r7.iszero h7 (by evm_ov)
  have r9 := r8.push2 target h8 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 11) r9
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcCheckedAddOkWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

theorem RD.solcSummaryCheckedSubCondition
    (hwf : solcSummaryCheckedArithmeticWf .SUB .GT code ee g s0 pc target b a stk
      mem aw rdata acc k C) :
    RD code ee g s0
      (pc + UInt256.ofNat 11)
      (target :: solcCheckedSubOkWord a b :: UInt256.sub a b :: b :: a :: stk)
      mem aw rdata acc (k + 9) (C + 25) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, h6, h7, h8, hov⟩
  have r1 := h.jumpdest h0 (by evm_ov)
  have r2 := r1.dup1 h1 (by evm_ov)
  have r3 := r2.dup3 h2 (by evm_ov)
  have r4 := r3.sub h3 (by evm_ov)
  have r5 := r4.dup3 h4 (by evm_ov)
  have r6 := r5.dup2 h5 (by evm_ov)
  have r7 := r6.gt h6 (by evm_ov)
  have r8 := r7.iszero h7 (by evm_ov)
  have r9 := r8.push2 target h8 (by evm_ov)
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 11) r9
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcCheckedSubOkWord, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

/-! ## Mapping scratch-memory hashes -/

@[reducible] def solcSummaryMappingHashKeyFirstWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc key slot : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (key :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.SWAP1, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩) = some (.DUP2, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = some (.MSTORE, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.Push .PUSH1, some (slot, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
    some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2) = some (.MSTORE, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) = some (.SWAP1, .none) ∧
  decode code (pc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
    UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.KECCAK256, .none) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryMappingHashKeyFirst
    (hwf : solcSummaryMappingHashKeyFirstWf code ee g s0 pc key slot stk mem aw
      rdata acc k C) :
    let aw1 := M aw ⟨0⟩ ⟨32⟩
    let aw2 := M aw1 ⟨32⟩ ⟨32⟩
    let aw3 := M aw2 ⟨0⟩ ⟨64⟩
    RD code ee g s0
      (pc + UInt256.ofNat 14)
      (solcMappingSlot slot key :: stk) (twoWordHashMem key slot mem) aw3 rdata acc
      (k + 10)
      (C + (27 + memExpansionCost aw ⟨0⟩ ⟨32⟩ +
        memExpansionCost aw1 ⟨32⟩ ⟨32⟩ + memExpansionCost aw2 ⟨0⟩ ⟨64⟩ +
        (30 + 6 *
          (((⟨64⟩ : UInt256).toNat + 31) / 32)))) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hov⟩
  have r1 := h.push1 ⟨0⟩ h0 (by evm_ov)
  have r2 := r1.swap1 h1 (by evm_ov)
  have r3 := r2.dup2 h2 (by evm_ov)
  have r4 := RD.mstore r3 h3 (by evm_ov)
  have r5 := r4.push1 slot h4 (by evm_ov)
  have r6 := r5.push1 ⟨32⟩ h5 (by evm_ov)
  have r7 := RD.mstore r6 h6 (by evm_ov)
  have r8 := r7.push1 ⟨64⟩ h7 (by evm_ov)
  have r9 := r8.swap1 h8 (by evm_ov)
  have r10 := RD.keccak256 r9 h9 (by evm_ov)
  change RD code ee g s0 _
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem key slot mem) :: stk)
    (twoWordHashMem key slot mem) _ rdata acc _ _ at r10
  rw [twoWordHashMem_keccak_solcMappingSlot] at r10
  dsimp
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 14) r10
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  exact RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryMappingHashSlotFirstWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc key slot : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (key :: stk) mem aw rdata acc k C ∧
  decode code pc = some (.Push .PUSH1, some (slot, 1)) ∧
  decode code (pc + UInt256.ofNat 2) = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2) = some (.MSTORE, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩) =
    some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2) =
    some (.SWAP1, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
    some (.DUP2, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
    ⟨1⟩) = some (.MSTORE, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
    ⟨1⟩ + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
    ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) = some (.SWAP1, .none) ∧
  decode code (pc + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
    ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.KECCAK256, .none) ∧
  stk.length + 3 ≤ 1024

theorem RD.solcSummaryMappingHashSlotFirst
    (hwf : solcSummaryMappingHashSlotFirstWf code ee g s0 pc key slot stk mem aw
      rdata acc k C) :
    let aw1 := M aw ⟨32⟩ ⟨32⟩
    let aw2 := M aw1 ⟨0⟩ ⟨32⟩
    let aw3 := M aw2 ⟨0⟩ ⟨64⟩
    RD code ee g s0
      (pc + UInt256.ofNat 14)
      (solcMappingSlot slot key :: stk) (twoWordHashMemSlotFirst key slot mem) aw3 rdata acc
      (k + 10)
      (C + (27 + memExpansionCost aw ⟨32⟩ ⟨32⟩ +
        memExpansionCost aw1 ⟨0⟩ ⟨32⟩ + memExpansionCost aw2 ⟨0⟩ ⟨64⟩ +
        (30 + 6 *
          (((⟨64⟩ : UInt256).toNat + 31) / 32)))) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hov⟩
  have r1 := h.push1 slot h0 (by evm_ov)
  have r2 := r1.push1 ⟨32⟩ h1 (by evm_ov)
  have r3 := RD.mstore r2 h2 (by evm_ov)
  have r4 := r3.push1 ⟨0⟩ h3 (by evm_ov)
  have r5 := r4.swap1 h4 (by evm_ov)
  have r6 := r5.dup2 h5 (by evm_ov)
  have r7 := RD.mstore r6 h6 (by evm_ov)
  have r8 := r7.push1 ⟨64⟩ h7 (by evm_ov)
  have r9 := r8.swap1 h8 (by evm_ov)
  have r10 := RD.keccak256 r9 h9 (by evm_ov)
  change RD code ee g s0 _
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMemSlotFirst key slot mem) :: stk)
    (twoWordHashMemSlotFirst key slot mem) _ rdata acc _ _ at r10
  rw [twoWordHashMemSlotFirst_keccak_solcMappingSlot] at r10
  dsimp
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 14) r10
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  exact RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcNestedMappingInnerPrefixWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none) ∧
  decode code p1 = some (.Push .PUSH1, some (slot, 1)) ∧
  decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
  decode code p5 = some (.SWAP1, .none) ∧
  decode code p6 = some (.DUP2, .none) ∧
  decode code p7 = some (.MSTORE, .none) ∧
  decode code p8 = some (.Push .PUSH1, some (⟨0⟩, 1)) ∧
  decode code p10 = some (.SWAP3, .none) ∧
  decode code p11 = some (.DUP4, .none) ∧
  decode code p12 = some (.MSTORE, .none) ∧
  decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1)) ∧
  decode code p15 = some (.DUP1, .none) ∧
  decode code p16 = some (.DUP5, .none) ∧
  decode code p17 = some (.KECCAK256, .none)

@[reducible] def solcSummaryNestedMappingInnerHashWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc slot spender owner : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (spender :: owner :: stk) mem aw rdata acc k C ∧
  solcNestedMappingInnerPrefixWf code pc slot ∧ stk.length + 6 ≤ 1024

theorem RD.solcSummaryNestedMappingInnerHash
    (hwf : solcSummaryNestedMappingInnerHashWf code ee g s0 pc slot spender owner stk
      mem aw rdata acc k C) :
    let aw1 := M aw ⟨32⟩ ⟨32⟩
    let aw2 := M aw1 ⟨0⟩ ⟨32⟩
    let aw3 := M aw2 ⟨0⟩ ⟨64⟩
    RD code ee g s0 (pc + UInt256.ofNat 18)
      (solcMappingSlot slot owner :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: stk)
      (twoWordHashMemSlotFirst owner slot mem) aw3 rdata acc (k + 14)
      (C + (37 + memExpansionCost aw ⟨32⟩ ⟨32⟩ +
        memExpansionCost aw1 ⟨0⟩ ⟨32⟩ + memExpansionCost aw2 ⟨0⟩ ⟨64⟩ +
        (30 + 6 *
          (((⟨64⟩ : UInt256).toNat + 31) / 32)))) := by
  rcases hwf with ⟨h, hw, hov⟩
  rcases hw with
    ⟨h0, h1, h3, h5, h6, h7, h8, h10, h11, h12, h13, h15, h16, h17⟩
  have r1 := h.jumpdest h0 (by evm_ov)
  have r2 := r1.push1 slot h1 (by evm_ov)
  have r3 := r2.push1 ⟨32⟩ h3 (by evm_ov)
  have r4 := r3.swap1 h5 (by evm_ov)
  have r5 := r4.dup2 h6 (by evm_ov)
  have r6 := RD.mstore r5 h7 (by evm_ov)
  have r7 := r6.push1 ⟨0⟩ h8 (by evm_ov)
  have r8 := r7.swap3 h10 (by evm_ov)
  have r9 := r8.dup4 h11 (by evm_ov)
  have r10 := RD.mstore r9 h12 (by evm_ov)
  have r11 := r10.push1 ⟨64⟩ h13 (by evm_ov)
  have r12 := r11.dup1 h15 (by evm_ov)
  have r13 := r12.dup5 h16 (by evm_ov)
  have r14 := RD.keccak256 r13 h17 (by evm_ov)
  change RD code ee g s0 _
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMemSlotFirst owner slot mem) ::
      ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: stk)
    (twoWordHashMemSlotFirst owner slot mem) _ rdata acc _ _ at r14
  rw [twoWordHashMemSlotFirst_keccak_solcMappingSlot] at r14
  dsimp
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 18) r14
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  simpa [solcNestedMappingGetterAfterInnerHashPc, u256_add_ofNat_ofNat] using
    RD.normalizeCounters rFinalPc (by omega) (by omega)

@[reducible] def solcSummaryNestedMappingOuterHashWf (code : ByteArray)
    (ee : ExecutionEnv) (g : Sat256) (s0 : State) (pc innerSlot spender : UInt256)
    (stk : List UInt256) (mem : ByteArray) (aw : UInt256) (rdata : ByteArray)
    (acc : Batteries.RBSet AccountAddress compare × AccountMap) (k C : ℕ) : Prop :=
  RD code ee g s0 pc (innerSlot :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: stk)
    mem aw rdata acc k C ∧
  decode code pc = some (.SWAP1, .none) ∧
  decode code (pc + ⟨1⟩) = some (.SWAP2, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.MSTORE, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.SWAP1, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.DUP3, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = some (.MSTORE, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.SWAP1, .none) ∧
  decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
    some (.KECCAK256, .none) ∧ stk.length + 5 ≤ 1024

theorem RD.solcSummaryNestedMappingOuterHash
    (hwf : solcSummaryNestedMappingOuterHashWf code ee g s0 pc innerSlot spender stk mem aw
      rdata acc k C) :
    let aw1 := M aw ⟨32⟩ ⟨32⟩
    let aw2 := M aw1 ⟨0⟩ ⟨32⟩
    let aw3 := M aw2 ⟨0⟩ ⟨64⟩
    RD code ee g s0 (pc + UInt256.ofNat 8)
      (solcMappingSlot innerSlot spender :: stk) (twoWordHashMemSlotFirst spender innerSlot mem)
      aw3 rdata acc (k + 8)
      (C + (21 + memExpansionCost aw ⟨32⟩ ⟨32⟩ +
        memExpansionCost aw1 ⟨0⟩ ⟨32⟩ + memExpansionCost aw2 ⟨0⟩ ⟨64⟩ +
        (30 + 6 *
          (((⟨64⟩ : UInt256).toNat + 31) / 32)))) := by
  rcases hwf with ⟨h, h0, h1, h2, h3, h4, h5, h6, h7, hov⟩
  have r1 := h.swap1 h0 (by evm_ov)
  have r2 := r1.swap2 h1 (by evm_ov)
  have r3 := RD.mstore r2 h2 (by evm_ov)
  have r4 := r3.swap1 h3 (by evm_ov)
  have r5 := r4.dup3 h4 (by evm_ov)
  have r6 := RD.mstore r5 h5 (by evm_ov)
  have r7 := r6.swap1 h6 (by evm_ov)
  have r8 := RD.keccak256 r7 h7 (by evm_ov)
  change RD code ee g s0 _
    (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMemSlotFirst spender innerSlot mem) :: stk)
    (twoWordHashMemSlotFirst spender innerSlot mem) _ rdata acc _ _ at r8
  rw [twoWordHashMemSlotFirst_keccak_solcMappingSlot] at r8
  dsimp
  have rFinalPc := RD.normalizePC (pc' := pc + UInt256.ofNat 8) r8
    (by simp only [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 from rfl,
      u256_add_ofNat_ofNat, Nat.reduceAdd])
  exact RD.normalizeCounters rFinalPc (by omega) (by omega)

end Reasoning.Theory
