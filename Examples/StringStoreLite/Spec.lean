import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# StringStoreLite — focused string storage example

This is the first-line string infrastructure test. It intentionally avoids nested dynamic storage
such as `string[]` and keeps the default proof target on one Solidity single-slot dynamic string:

* `set(string)` decodes dynamic ABI string calldata, copies it to memory, and writes a string slot;
* `clearCurrent` checks whole-value storage-to-memory copy followed by clear;
* `currentLength` checks the storage length read.

The heavier `Examples.StringStore` directory remains the stress test for dynamic arrays of strings.
-/

open Solm ABI Ethereum

namespace StringStoreLite

/-! ## Types -/

def uint8Int : IntType := .uint ⟨8, by decide⟩
def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def stringTy : ABIType := .string
def bytesTy : ABIType := .bytes

def uint8St : StorageType := .elem (.int uint8Int)
def uint256St : StorageType := .elem (.int uint256Int)
def stringSt : StorageType := .string
def bytesSt : StorageType := .bytes

/-! ## Storage refs -/

def currentRef : StorageRef := { base := "current" }

def currentByteRef (i : Expr) : StorageRef := { base := "current", steps := [.aindex i] }

def storageDecls : List StorageDecl :=
  [ { name := "current", ty := stringSt } ]

/-! ## Transitions -/

def setTransition : TransitionDecl :=
  { name := "set"
    params := [{ name := "value", ty := stringTy }]
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.var "value"),
        .assign .storage currentRef (.var "copy"),
        .return [(.arrayLength .localVar { base := "copy" })] ] }

def clearCurrentTransition : TransitionDecl :=
  { name := "clearCurrent"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "copy" (some stringTy) (.storage currentRef),
        .delete currentRef,
        .return [(.arrayLength .localVar { base := "copy" })] ] }

def currentLengthGetter : TransitionDecl :=
  { name := "currentLength"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.arrayLength .storage currentRef)] ] }

def stringStoreLiteContract : ContractDecl :=
  { name := "StringStoreLite"
    storage := storageDecls
    ctor := { params := [], body := [] }
    transitions := [setTransition, clearCurrentTransition, currentLengthGetter] }

/-! ## Solidity string/bytes storage layout -/

def uint8Loc (slot : Ethereum.UInt256) (offset : Fin 32) : StorageLoc :=
  { slot := slot, offset := offset, size := 1, hbound := by omega, type := .int uint8Int }

def bytesLikeDataBase (baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC baseSlot.toByteArray)

abbrev bytesLikeLengthLoc := Solm.bytesLikeLengthLoc

def bytesLikeByteLoc? (baseSlot : Ethereum.UInt256) (index : KeyValue)
    (evm : EVM.State) : Option StorageLoc :=
  match index with
  | .int i =>
      if i < 0 then
        none
      else
        let idx := i.toNat
        if checkBytesPacked baseSlot evm then
          if hidx : idx < 31 then
            some (uint8Loc baseSlot ⟨31 - idx, by omega⟩)
          else
            none
        else
          some (uint8Loc
            (bytesLikeDataBase baseSlot + Ethereum.UInt256.ofNat (idx / 32))
            ⟨31 - (idx % 32), by
              have hmod : idx % 32 < 32 := Nat.mod_lt idx (by decide)
              omega⟩)
  | _ => none

def stringStoreLiteLayout : StorageLayout :=
  solidityLayout! [([] : List StructDecl)] [storageDecls]

def stringStoreLiteStorageBackend : StorageBackend :=
  solidityStorageBackend stringStoreLiteLayout

@[simp] theorem stringStoreLiteLayout_current (evm : EVM.State) :
    stringStoreLiteLayout { base := "current" } evm =
      some (Solm.bytesLikeLengthLoc ⟨0⟩ evm) :=
  rfl

end StringStoreLite

def stringStoreLiteConfig : Config :=
  { storage := StringStoreLite.stringStoreLiteStorageBackend
    externalABI := defaultExternalCallABI
    selfDeployment :=
      genSolidityConstructorDeployment StringStoreLite.stringStoreLiteContract.ctor.params }

@[simp] theorem stringStoreLiteConfig_storage :
    stringStoreLiteConfig.storage = StringStoreLite.stringStoreLiteStorageBackend :=
  rfl

/-- Proof-facing spelling of the backend operation used to read the string length. -/
abbrev stringStoreLiteStorageLength? (evm : EVM.State) (er : EvaledStorageRef) :
    EvalResult Nat :=
  stringStoreLiteConfig.storage.length er .string evm

/-- Proof-facing spelling of a typed read from the generated backend. -/
abbrev stringStoreLiteReadStorage? (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) : EvalResult Value :=
  stringStoreLiteConfig.storage.read er ty evm

/-- Proof-facing spelling of a typed write through the generated backend. -/
abbrev stringStoreLiteWriteStorage? (evm : EVM.State) (er : EvaledStorageRef)
    (ty : StorageType) (value : Value) : EvalResult EVM.State :=
  stringStoreLiteConfig.storage.write er ty value evm

theorem stringStoreLiteStorageLength_current (evm : EVM.State) :
    stringStoreLiteStorageLength? evm { base := "current" } =
      solidityNatResultToEval
        (solidityDecodeBytesLengthHeader
          (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)) := by
  unfold stringStoreLiteStorageLength?
  rw [stringStoreLiteConfig_storage]
  change solidityStorageLength? StringStoreLite.stringStoreLiteLayout
    { base := "current" } .string evm = _
  simp [solidityStorageLength?, solidityReadBytesLength?,
    StringStoreLite.stringStoreLiteLayout_current]
  unfold Solm.bytesLikeLengthLoc
  split <;> rfl

theorem stringStoreLiteReadStorage_current (evm : EVM.State) :
    stringStoreLiteReadStorage? evm { base := "current" } .string =
      solidityValueResultToEval
        (solidityReadBytesValue? StringStoreLite.stringStoreLiteLayout
          { base := "current" } evm) := by
  unfold stringStoreLiteReadStorage?
  rw [stringStoreLiteConfig_storage]
  change solidityReadStorage? StringStoreLite.stringStoreLiteLayout evm
    { base := "current" } .string = _
  simp [solidityReadStorage?]

@[simp] theorem stringStoreLiteConfig_storage_current_length :
    stringStoreLiteConfig.storage.locate? { base := "current", steps := [] } =
      fun evm => some (StringStoreLite.bytesLikeLengthLoc ⟨0⟩ evm) :=
  rfl
