import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# OpenZeppelin Pausable benchmark spec

Solm specification for `PausableBench`, a concrete wrapper around the abstract OpenZeppelin
`Pausable` utility.  Events are intentionally omitted; storage, guards, and return values are
modelled.
-/

open Solm ABI

namespace OpenZeppelinBench.Pausable

def boolTy : ABIType := .elem .bool
def boolSt : StorageType := .elem .bool

def pausedRef : StorageRef := { base := "_paused" }

def storageDecls : List StorageDecl :=
  [ { name := "_paused", ty := boolSt } ]

def boolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def storageBackend : StorageBackend :=
  solidityStorage! [([] : List StructDecl)] [storageDecls]

def pausedTransition : TransitionDecl :=
  { name := "paused"
    params := []
    returnType := [boolTy]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage pausedRef)] ] }

def pauseTransition : TransitionDecl :=
  { name := "pause"
    params := []
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.unary .not (.storage pausedRef)),
        .assign .storage pausedRef (.boolLit true) ] }

def unpauseTransition : TransitionDecl :=
  { name := "unpause"
    params := []
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage pausedRef),
        .assign .storage pausedRef (.boolLit false) ] }

def guardedWhenNotPausedTransition : TransitionDecl :=
  { name := "guardedWhenNotPaused"
    params := []
    returnType := [boolTy]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.unary .not (.storage pausedRef)),
        .return [(.boolLit true)] ] }

def guardedWhenPausedTransition : TransitionDecl :=
  { name := "guardedWhenPaused"
    params := []
    returnType := [boolTy]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage pausedRef),
        .return [(.boolLit true)] ] }

def constructorDecl : ConstructorDecl :=
  { params := []
    body := [ .assign .storage pausedRef (.boolLit false) ] }

def contract : ContractDecl :=
  { name := "PausableBench"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ guardedWhenNotPausedTransition,
        guardedWhenPausedTransition,
        pauseTransition,
        pausedTransition,
        unpauseTransition ] }

def config : Config :=
  { storage := storageBackend
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

@[simp] theorem config_read_paused (evm : EVM.State) :
    config.storage.read { base := "_paused", steps := [] } (.elem .bool) evm =
      .ok (storageLocLoad evm (boolLoc ⟨0⟩)) := by
  apply solidityStorageBackend_read_elem
  rfl

theorem config_write_paused {evm evm' : EVM.State} {value : Value}
    (hstore : storageLocStore evm (boolLoc ⟨0⟩) value = some evm') :
    config.storage.write { base := "_paused", steps := [] } (.elem .bool) value evm = .ok evm' := by
  apply solidityStorageBackend_write_elem (loc := boolLoc ⟨0⟩)
  · rfl
  · exact hstore

end OpenZeppelinBench.Pausable
