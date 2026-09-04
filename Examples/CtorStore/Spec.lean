import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# CtorStore — Solm specification for a constructor-storage equivalence test

The constructor takes a `uint256` argument and writes it to storage slot 0.  The storage field is
private so the runtime surface stays empty while the constructor proof exercises ABI arguments and
`SSTORE`.
-/

open Solm ABI Ethereum

namespace CtorStore

/-- The ABI/Solm type `uint256`. -/
def uint256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))

def storageDecls : List StorageDecl :=
  [{ name := "stored", ty := .elem (.int (.uint ⟨256, by decide⟩)) }]

def storedLoc : StorageLoc :=
  { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
    type := .int (.uint ⟨256, by decide⟩) }

/-- Generated Solidity backend for the full-word `stored` value at slot 0. -/
def storageBackend : StorageBackend :=
  solidityStorage! [([] : List StructDecl)] [storageDecls]

/-- A payable constructor stores its `uint256` argument into slot 0. -/
def ctor : ConstructorDecl :=
  { params := [{ name := "x", ty := uint256 }]
    body := [ .assign .storage { base := "stored" } (.var "x") ] }

/-- Solm specification of `CtorStore`; the private storage field has no public runtime transition. -/
def contract : ContractDecl :=
  { name := "CtorStore"
    storage := storageDecls
    ctor := ctor
    transitions := [] }

end CtorStore

/-- Verification config: `stored` at slot 0 and Solidity constructor deployment encoding. -/
def ctorStoreConfig : Config :=
  { storage := CtorStore.storageBackend
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment CtorStore.contract.ctor.params }

@[simp] theorem ctorStoreConfig_read_stored (evm : EVM.State) :
    ctorStoreConfig.storage.read { base := "stored", steps := [] }
        (.elem (.int (.uint ⟨256, by decide⟩))) evm =
      .ok (storageLocLoad evm CtorStore.storedLoc) := by
  change (solidityStorageBackend _).read _ (.elem (.int (.uint ⟨256, by decide⟩))) evm = _
  apply solidityStorageBackend_read_elem
  rfl

theorem ctorStoreConfig_write_stored {evm evm' : EVM.State} {i : Int}
    (hstore : storageLocStore evm CtorStore.storedLoc (.int i) = some evm') :
    ctorStoreConfig.storage.write { base := "stored", steps := [] }
        (.elem (.int (.uint ⟨256, by decide⟩))) (.int i) evm = .ok evm' := by
  change (solidityStorageBackend _).write _ (.elem (.int (.uint ⟨256, by decide⟩)))
    (.int i) evm = _
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore
