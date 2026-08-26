import Reasoning.Reach
import Reasoning.Storage

/-!
# Reach-Auto ─ symbolic `RD` opcode steps

These variants expose deterministic opcode results directly in the resulting `RD` term.  In particular, callers do not have to introduce aliases for memory writes, loaded or hashed words,
active-word growth, or memory-expansion costs and then prove that each alias equals its definition.

The trade-off is a larger symbolic term, but repeated opcode applications can expand the machine
state without routine equality witnesses.  Premises that select genuinely different behavior are
retained: decode and stack bounds, return-data bounds, static-mode permission, and out-of-gas
conditions.  Control-flow proofs and call/create-style system operations remain in `Reach`.

Opcodes whose original `Reach` lemma already exposes its deterministic result directly do not need
a duplicate here.
-/
open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory
open Reasoning.Reach

set_option maxRecDepth 10000

namespace Auto

def M (aw start size : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat start.toNat size.toNat)

def memLoad (a aw : UInt256) (m : ByteArray) : UInt256 :=
  if a.toNat ≥ m.size ∨ a ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (m.readWithPadding a.toNat 32))

def keccakWord (a b : UInt256) (m : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (m.readWithPadding a.toNat b.toNat)))

def memExpansionCost (aw start size : UInt256) : ℕ :=
  Cₘ (M aw start size) - Cₘ aw

/-- A compact symbolic storage read.  Its definition is available when concrete map reasoning is
    needed, but ordinary opcode chaining retains the named term. -/
@[irreducible] def storageRead (owner : AccountAddress) (σ : AccountMap)
    (slot : UInt256) : UInt256 :=
  σ.find? owner |>.option ⟨0⟩ (fun account => account.storage.findD slot ⟨0⟩)

/-- A compact symbolic storage write, including the EVM zero-value deletion behavior. -/
@[irreducible] def storageWrite (owner : AccountAddress) (σ : AccountMap)
    (slot value : UInt256) : AccountMap :=
  sstoreAccountMap owner σ slot value

/-- Read a slot from an account already obtained from the account map. -/
@[irreducible] def accountStorageRead (account : Account) (slot : UInt256) : UInt256 :=
  account.storage.findD slot ⟨0⟩

/-- Update an account already known to be present, without repeating the account-map lookup. -/
@[irreducible] def storageWritePresent (owner : AccountAddress) (σ : AccountMap) (account : Account)
    (slot value : UInt256) : AccountMap :=
  σ.insert owner
    (if value == default then { account with storage := account.storage.erase slot }
     else { account with storage := account.storage.insert slot value })

/-! The implementation equations are deliberately not simp lemmas.  They provide an explicit
escape hatch for concrete map proofs while keeping routine simplification at the symbolic API. -/

theorem storageRead_eq (owner : AccountAddress) (σ : AccountMap) (slot : UInt256) :
    storageRead owner σ slot =
      (σ.find? owner |>.option ⟨0⟩ (fun account => account.storage.findD slot ⟨0⟩)) := by
  rw [storageRead]

theorem storageWrite_eq (owner : AccountAddress) (σ : AccountMap) (slot value : UInt256) :
    storageWrite owner σ slot value = sstoreAccountMap owner σ slot value := by
  rw [storageWrite]

theorem accountStorageRead_eq (account : Account) (slot : UInt256) :
    accountStorageRead account slot = account.storage.findD slot ⟨0⟩ := by
  rw [accountStorageRead]

theorem storageWritePresent_eq (owner : AccountAddress) (σ : AccountMap) (account : Account)
    (slot value : UInt256) :
    storageWritePresent owner σ account slot value =
      σ.insert owner
        (if value == default then { account with storage := account.storage.erase slot }
         else { account with storage := account.storage.insert slot value }) := by
  rw [storageWritePresent]

@[simp]
theorem storageRead_of_present {owner : AccountAddress} {σ : AccountMap} {account : Account}
    {slot : UInt256} (haccount : σ.find? owner = some account) :
    storageRead owner σ slot = accountStorageRead account slot := by
  simp [storageRead, accountStorageRead, haccount, Option.option]

@[simp]
theorem storageWrite_of_present {owner : AccountAddress} {σ : AccountMap} {account : Account}
    {slot value : UInt256} (haccount : σ.find? owner = some account) :
    storageWrite owner σ slot value = storageWritePresent owner σ account slot value := by
  simp [storageWrite, sstoreAccountMap, storageWritePresent, haccount, Option.option]

@[simp]
theorem storageRead_of_missing {owner : AccountAddress} {σ : AccountMap} {slot : UInt256}
    (haccount : σ.find? owner = none) : storageRead owner σ slot = ⟨0⟩ := by
  simp [storageRead, haccount, Option.option]

@[simp]
theorem storageWrite_of_missing {owner : AccountAddress} {σ : AccountMap} {slot value : UInt256}
    (haccount : σ.find? owner = none) : storageWrite owner σ slot value = σ := by
  simp [storageWrite, sstoreAccountMap, haccount, Option.option]

/-- Reading the slot just written returns the written value.  This form is tailored to symbolic
    chains that used `RD.sstore_of_present`. -/
@[simp]
theorem storageRead_storageWritePresent_same (owner : AccountAddress) (σ : AccountMap)
    (account : Account) (slot value : UInt256) :
    storageRead owner (storageWritePresent owner σ account slot value) slot = value := by
  rw [storageRead, storageWritePresent, accountMap_find_insert_self]
  simp only [Option.option]
  by_cases hzero : (value == (default : UInt256)) = true
  · have hvalue : value = (default : UInt256) := eq_of_beq hzero
    subst value
    simpa using storage_findD_erase_self account.storage slot ⟨0⟩
  · simpa [hzero] using storage_findD_insert_self account.storage slot value ⟨0⟩

/-- A write to another slot leaves this read unchanged. -/
@[simp]
theorem storageRead_storageWritePresent_ne (owner : AccountAddress) (σ : AccountMap)
    (account : Account) {readSlot writeSlot value : UInt256} (hne : readSlot ≠ writeSlot) :
    storageRead owner (storageWritePresent owner σ account writeSlot value) readSlot =
      accountStorageRead account readSlot := by
  rw [storageRead, storageWritePresent, accountStorageRead, accountMap_find_insert_self]
  simp only [Option.option]
  by_cases hzero : (value == (default : UInt256)) = true
  · simp only [hzero, if_true]
    exact storage_findD_erase_ne account.storage readSlot writeSlot ⟨0⟩ hne
  · simp only [hzero]
    exact storage_findD_insert_ne account.storage readSlot writeSlot value ⟨0⟩ hne

/-- General read-after-write law for distinct slots, including the missing-account case. -/
@[simp]
theorem storageRead_storageWrite_ne (owner : AccountAddress) (σ : AccountMap)
    {readSlot writeSlot value : UInt256} (hne : readSlot ≠ writeSlot) :
    storageRead owner (storageWrite owner σ writeSlot value) readSlot =
      storageRead owner σ readSlot := by
  rw [storageRead, storageWrite, storageRead]
  exact sstoreAccountMap_storage_findD_ne σ owner readSlot writeSlot value hne

/-- General same-slot read-after-write law when the account is known to exist. -/
@[simp]
theorem storageRead_storageWrite_same_of_present {owner : AccountAddress} {σ : AccountMap}
    {account : Account} {slot value : UInt256} (haccount : σ.find? owner = some account) :
    storageRead owner (storageWrite owner σ slot value) slot = value := by
  rw [storageWrite_of_present haccount]
  exact storageRead_storageWritePresent_same owner σ account slot value

/- TODO: some property that two sequential expansions can be collapsed to one-/

/- TODO: Is this lemma available somewhere? -/
/-
lemma UInt256_ofNat_toNat : ∀ (a : UInt256), UInt256.ofNat a.toNat = a := by
  intro a
  simp [UInt256.ofNat, UInt256.toNat, Id.run]

lemma UInt256_toNat_ofNat_le : ∀ (a : ℕ), (UInt256.ofNat a).toNat ≤ a := by
  intro a
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Nat.mod_le]
-/

/-
lemma memExpansionConcat : ∀ (aw f1 l1 f2 l2 : UInt256),
  l2 ≠ ⟨0⟩ →
  f2 + l2 > f1 + l1 →
  memExpansionCost (M aw f1 l1) f2 l2 =
    memExpansionCost aw f2 l2 := by
  intros aw f1 l1 f2 l2 hl2_neq hgt
  simp [memExpansionCost, M, MachineState.M]
  split <;> rename_i hl2
  · split <;> rename_i hl1
    · simp [UInt256_ofNat_toNat]
    · simp [UInt256_ofNat_toNat]
  · split <;> rename_i hl1
    · simp [UInt256_ofNat_toNat]
    · simp [max]
      split <;> split <;> split <;> rename_i hmax2
      <;> sorry
      -/




theorem RD.mstore {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none))
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t
      (b.toByteArray.write 0 mem a.toNat 32)
      (M aw a ⟨32⟩)
      rdata acc (k + 1)
      (C + (memExpansionCost aw a ⟨32⟩ + 3))
      := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := mstore_xstep hcode hpc hdec hstk hov
    simp
    have hmcS : memoryExpansionCost s .MSTORE = memExpansionCost aw a ⟨32⟩ := by
      simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      conv => rhs; arg 1; arg 1; arg 1; arg 3; change 32
    by_cases gg : g.toNat < C + (memExpansionCost aw a ⟨32⟩ + 3)
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMStore s a b t,
        ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hx := hX.trans (stepContinue hgas st hk (by omega))
        simpa only [Nat.add_sub_add_right] using hx
      · simp only [stMStore]; exact hcode
      · simp only [stMStore]; rw [hpc]
      · rfl
      · simp only [stMStore, hmcS, memExpansionCost]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
        congr
      · simp only [stMStore]; rw [hmem]
      · simp only [stMStore, M, haw]
        conv => rhs; arg 1; arg 3; change 32
      · simp only [stMStore]; exact hrdata
      · simp only [stMStore]; exact hacc
      · exact hee
      · exact hworld

/-- `CALLDATACOPY`: pops destination, calldata offset, and length; copies calldata bytes into memory. -/
theorem RD.calldatacopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CALLDATACOPY, .none))
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t
      (ee.calldata.write b.toNat mem a.toNat c.toNat)
      (M aw a c)
      rdata acc (k + 1)
      (C + (memExpansionCost aw a c + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32))))
      := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .CALLDATACOPY = memExpansionCost aw a c := by
      simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
    have st := calldatacopy_xstep hcode hpc hdec hstk hov
    rw [collapse_two_stage] at st
    by_cases gg : g.toNat < C + (memExpansionCost aw a c + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < memExpansionCost aw a c + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      rw [hmcS] at st
      refine Or.inr ⟨stCalldatacopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCalldatacopy]; exact hcode
      · simp only [stCalldatacopy]; rw [hpc]
      · rfl
      · simp only [stCalldatacopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCalldatacopy]; rw [hee, hmem]
      · simp only [stCalldatacopy, M, haw];
      · simp only [stCalldatacopy]; exact hrdata
      · simp only [stCalldatacopy]; exact hacc
      · exact hee
      · exact hworld

/-- `CODECOPY`: pops destination, code offset, and length; copies code bytes into memory. -/
theorem RD.codecopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.CODECOPY, .none))
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t
      (code.write b.toNat mem a.toNat c.toNat)
      (M aw a c)
      rdata acc
      (k + 1)
      (C + (memExpansionCost aw a c + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .CODECOPY = memExpansionCost aw a c := by
      simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
    have st := codecopy_xstep hcode hpc hdec hstk hov
    rw [collapse_two_stage] at st
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (memExpansionCost aw a c  + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < memExpansionCost aw a c + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stCodecopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stCodecopy]; exact hcode
      · simp only [stCodecopy]; rw [hpc]
      · rfl
      · simp only [stCodecopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stCodecopy]; rw [hcode, hmem]
      · simp only [stCodecopy, M]; rw [haw]
      · simp only [stCodecopy]; exact hrdata
      · simp only [stCodecopy]; exact hacc
      · exact hee
      · exact hworld

set_option maxHeartbeats 1000000 in
/-- `RETURNDATACOPY`: the bounds check remains semantic, while the copied memory, active words,
    and memory-expansion cost are exposed as symbolic terms. -/
theorem RD.returndatacopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t
      (rdata.write b.toNat mem a.toNat c.toNat)
      (M aw a c) rdata acc (k + 1)
      (C + (memExpansionCost aw a c
        + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  apply Reasoning.Reach.RD.returndatacopy
    (memExpansionCost aw a c)
    (rdata.write b.toNat mem a.toNat c.toNat)
    (M aw a c) h hdec hguard
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · rfl
  · rfl
  · exact hov

/-- `MLOAD`: the loaded word, active words, and memory-expansion cost are all retained
    symbolically instead of being named and justified by separate hypotheses. -/
theorem RD.mload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (memLoad a aw mem :: t) mem
      (M aw a ⟨32⟩) rdata acc (k + 1)
      (C + (memExpansionCost aw a ⟨32⟩ + 3)) := by
  apply Reasoning.Reach.RD.mload
    (memExpansionCost aw a ⟨32⟩) (memLoad a aw mem) (M aw a ⟨32⟩) h hdec
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
    conv => rhs; arg 1; arg 1; arg 1; arg 3; change 32
  · rfl
  · simp [M]
    conv => rhs; arg 1; arg 3; change 32
  · exact hov

/-- `KECCAK256`: retain the hash application and all memory-derived quantities symbolically. -/
theorem RD.keccak256 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.KECCAK256, .none))
    (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (keccakWord a b mem :: t) mem
      (M aw a b) rdata acc (k + 1)
      (C + (memExpansionCost aw a b + (GasConstants.Gkeccak256
        + GasConstants.Gkeccak256word * ((b.toNat + 31) / 32)))) := by
  apply Reasoning.Reach.RD.keccak256
    (memExpansionCost aw a b) (keccakWord a b mem) (M aw a b) h hdec
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · rfl
  · rfl
  · exact hov

/-- `LOG1`: retain only the static-mode permission premise; memory cost and active words
    are computed from the carried symbolic state. -/
theorem RD.log1 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG1, .none))
    (hperm : ee.perm = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem (M aw a b) rdata acc (k + 1)
      (C + (memExpansionCost aw a b + (GasConstants.Glog
        + GasConstants.Glogdata * b.toNat + GasConstants.Glogtopic))) := by
  apply Reasoning.Reach.RD.log1
    (memExpansionCost aw a b) (M aw a b) h hdec hperm
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · rfl
  · exact hov

/-- `LOG3`: symbolic memory cost and active-word expansion. -/
theorem RD.log3 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG3, .none))
    (hperm : ee.perm = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem (M aw a b) rdata acc (k + 1)
      (C + (memExpansionCost aw a b + (GasConstants.Glog
        + GasConstants.Glogdata * b.toNat + 3 * GasConstants.Glogtopic))) := by
  apply Reasoning.Reach.RD.log3
    (memExpansionCost aw a b) (M aw a b) h hdec hperm
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · rfl
  · exact hov

/-- `LOG4`: symbolic memory cost and active-word expansion. -/
theorem RD.log4 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG4, .none))
    (hperm : ee.perm = true)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem (M aw a b) rdata acc (k + 1)
      (C + (memExpansionCost aw a b + (GasConstants.Glog
        + GasConstants.Glogdata * b.toNat + 4 * GasConstants.Glogtopic))) := by
  apply Reasoning.Reach.RD.log4
    (memExpansionCost aw a b) (M aw a b) h hdec hperm
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · rfl
  · exact hov

/-! ### Storage operations

The warm/cold gas cost still depends on the untracked substate, so the counters remain
existential exactly as in `Reach`.  Only the account-map read and write expressions are named.
-/

/-- `SLOAD` with its account-map lookup retained as the compact `storageRead` term. -/
theorem RD.sload {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {slot : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: t) mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.SLOAD, .none))
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (storageRead ee.codeOwner σ slot :: t)
      mem aw rdata (cA, σ) k' C' := by
  simpa only [storageRead] using Reasoning.Reach.RD.sload h hdec hov

/- TODO: see if this is more practical -/
/-- `SLOAD` when the executing account has already been resolved from the account map. -/
theorem RD.sload_of_present {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {account : Account}
    {k C : ℕ} {slot : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: t) mem aw rdata (cA, σ) k C)
    (hdec : decode code pc = some (.SLOAD, .none))
    (haccount : σ.find? ee.codeOwner = some account)
    (hov : t.length + 1 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) (accountStorageRead account slot :: t)
      mem aw rdata (cA, σ) k' C' := by
  simpa only [storageRead_of_present haccount] using RD.sload h hdec hov

/-- `SSTORE` with its account-map update retained as the compact `storageWrite` term. -/
theorem RD.sstore {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {slot value : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: value :: t) mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.SSTORE, .none))
    (hov : t.length ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) t mem aw rdata
      (cA, storageWrite ee.codeOwner σ slot value) k' C' := by
  simpa only [storageWrite] using Reasoning.Reach.RD.sstore h hperm hdec hov

/- TODO: see if this is more practical -/
/-- `SSTORE` when the executing account has already been resolved from the account map. -/
theorem RD.sstore_of_present {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {account : Account}
    {k C : ℕ} {slot value : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (slot :: value :: t) mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hdec : decode code pc = some (.SSTORE, .none))
    (haccount : σ.find? ee.codeOwner = some account)
    (hov : t.length ≤ 1024) :
    ∃ k' C', RD code ee g s0 (pc + ⟨1⟩) t mem aw rdata
      (cA, storageWritePresent ee.codeOwner σ account slot value) k' C' := by
  simpa only [storageWrite_of_present haccount] using RD.sstore h hperm hdec hov

/-- `RETURN`: expose the returned memory slice directly, without separate cost or value aliases. -/
theorem RD.ret {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {off len : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURN, .none))
    (hov : t.length ≤ 1024) :
    RDret code g s0 acc (mem.readWithPadding off.toNat len.toNat) := by
  apply Reasoning.Reach.RD.ret (memExpansionCost aw off len)
    (mem.readWithPadding off.toNat len.toNat) h hdec
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · rfl
  · exact hov

/-- `REVERT`: compute its memory-expansion cost symbolically; no output alias is needed because
    `RDrev` deliberately forgets the returned bytes. -/
theorem RD.rev {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {off len : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (off :: len :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.REVERT, .none))
    (hov : t.length ≤ 1024) :
    RDrev code g s0 := by
  apply Reasoning.Reach.RD.rev (memExpansionCost aw off len) h hdec
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · exact hov

/- Is this relevant?
/-- `RETURNDATACOPY` terminal out-of-gas result with its memory cost expanded symbolically. -/
theorem RD.returndatacopyOOG_error {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hOOG : g.toNat < memExpansionCost aw a c)
    (hov : t.length ≤ 1024) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass := by
  apply Reasoning.Reach.RD.returndatacopyOOG_error
    (memExpansionCost aw a c) h hdec hguard
  · intro s hawS hstkS
    simp [memExpansionCost, M, memoryExpansionCost, memoryExpansionCost.μᵢ', hawS, hstkS]
  · exact hOOG
  · exact hov
  -/

/- Is this relevant?
/-- `RETURNDATACOPY` terminal out-of-gas result, packaged as `RDrev`. -/
theorem RD.returndatacopyOOG {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.RETURNDATACOPY, .none))
    (hguard : b.toNat + c.toNat ≤ rdata.size)
    (hOOG : g.toNat < memExpansionCost aw a c)
    (hov : t.length ≤ 1024) :
    RDrev code g s0 :=
  Or.inl (RD.returndatacopyOOG_error h hdec hguard hOOG hov)
  -/

/-- `GAS`: unlike the existential result in the general lemma, `RD`'s carried cumulative cost
    determines the pushed post-instruction gas exactly. -/
theorem RD.gas {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.GAS, .none))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) ((g.subNat (C + 2)).toUInt256 :: stk)
      mem aw rdata acc (k + 1) (C + 2) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
      hee, hworld⟩
  · exact Or.inl hoog
  · have st := gas_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 2
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stGas s,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stGas]; exact hcode
      · simp only [stGas]; rw [hpc]
      · simp only [stGas]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub, hstk]
      · simp only [stGas]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stGas]; exact hmem
      · simp only [stGas]; exact haw
      · simp only [stGas]; exact hrdata
      · simp only [stGas]; exact hacc
      · exact hee
      · exact hworld


end Auto
end Reasoning.Reach
