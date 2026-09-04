import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# OpenZeppelin Ownable2Step benchmark spec

Solm specification for the concrete `Ownable2StepBench` wrapper.  The deployed runtime has the
OpenZeppelin `Ownable2Step` storage shape: `_owner` in slot 0 and `_pendingOwner` in slot 1.
-/

open Solm ABI

namespace OpenZeppelinBench.Ownable2Step

def addr : ABIType := .elem .address
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def zeroAddr : Expr := .cast (.intLit 0) addrSt

def ownerRef : StorageRef := { base := "_owner" }
def pendingOwnerRef : StorageRef := { base := "_pendingOwner" }

def storageDecls : List StorageDecl :=
  [ { name := "_owner", ty := addrSt },
    { name := "_pendingOwner", ty := addrSt } ]

def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageBackend : StorageBackend :=
  solidityStorage! [([] : List StructDecl)] [storageDecls]

def ownerTransition : TransitionDecl :=
  { name := "owner"
    params := []
    returnType := [addr]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage ownerRef)] ] }

def pendingOwnerTransition : TransitionDecl :=
  { name := "pendingOwner"
    params := []
    returnType := [addr]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage pendingOwnerRef)] ] }

def transferOwnershipTransition : TransitionDecl :=
  { name := "transferOwnership"
    params := [{ name := "newOwner", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage pendingOwnerRef (.var "newOwner") ] }

def acceptOwnershipTransition : TransitionDecl :=
  { name := "acceptOwnership"
    params := []
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage pendingOwnerRef) sender),
        .assign .storage pendingOwnerRef zeroAddr,
        .assign .storage ownerRef sender ] }

def renounceOwnershipTransition : TransitionDecl :=
  { name := "renounceOwnership"
    params := []
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.storage ownerRef) sender),
        .assign .storage pendingOwnerRef zeroAddr,
        .assign .storage ownerRef zeroAddr ] }

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "initialOwner", ty := addr }]
    body :=
      [ .require (.binary .ne (.var "initialOwner") zeroAddr),
        .assign .storage ownerRef (.var "initialOwner") ] }

def contract : ContractDecl :=
  { name := "Ownable2StepBench"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ acceptOwnershipTransition,
        ownerTransition,
        pendingOwnerTransition,
        renounceOwnershipTransition,
        transferOwnershipTransition ] }

def config : Config :=
  { storage := storageBackend
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

@[simp] theorem config_read_owner (evm : EVM.State) :
    config.storage.read { base := "_owner", steps := [] } (.elem .address) evm =
      .ok (storageLocLoad evm (addrLoc ⟨0⟩)) := by
  apply solidityStorageBackend_read_elem
  rfl

@[simp] theorem config_read_pendingOwner (evm : EVM.State) :
    config.storage.read { base := "_pendingOwner", steps := [] } (.elem .address) evm =
      .ok (storageLocLoad evm (addrLoc ⟨1⟩)) := by
  apply solidityStorageBackend_read_elem
  rfl

theorem config_write_owner {evm evm' : EVM.State} {value : Value}
    (hstore : storageLocStore evm (addrLoc ⟨0⟩) value = some evm') :
    config.storage.write { base := "_owner", steps := [] } (.elem .address) value evm = .ok evm' := by
  apply solidityStorageBackend_write_elem (loc := addrLoc ⟨0⟩)
  · rfl
  · exact hstore

theorem config_write_pendingOwner {evm evm' : EVM.State} {value : Value}
    (hstore : storageLocStore evm (addrLoc ⟨1⟩) value = some evm') :
    config.storage.write { base := "_pendingOwner", steps := [] } (.elem .address) value evm = .ok evm' := by
  apply solidityStorageBackend_write_elem (loc := addrLoc ⟨1⟩)
  · rfl
  · exact hstore

end OpenZeppelinBench.Ownable2Step
