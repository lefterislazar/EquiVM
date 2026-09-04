import Solm.Semantics
import Solm.SolidityLayout
import Solm.MetaSolidityLayout

/-!
# ERC20 — Solm specification for `ERC20.sol`

This is the Solm-level specification for the core ERC20 surface:
`totalSupply`, `balanceOf`, `allowance`, `approve`, `transfer`, and `transferFrom`.
The Solidity contract emits the standard events, but the current Solm statement tracks storage and
return values only.
-/

open Solm ABI

namespace ERC20

def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)

def uint256Storage : StorageType := .elem (.int uint256Int)

def addr : ABIType := .elem .address

def sender : Expr := .env .caller

def valueInUInt256 (expr : Expr) : Expr := .inRange uint256Int expr

def balanceOfRef (owner : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex owner] }

def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }

def totalSupplyRef : StorageRef :=
  { base := "totalSupply" }

def erc20StorageDecls : List StorageDecl :=
  [ { name := "balanceOf", ty := .mapping .address uint256Storage },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256Storage) },
    { name := "totalSupply", ty := uint256Storage },
    { name := "array", ty := .array (.elem .address) 5 } ]

def erc20Uint256Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def erc20MappingSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def erc20BalanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  erc20MappingSlot (keyValueToWord owner) ⟨0⟩

def erc20AllowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  erc20MappingSlot (keyValueToWord owner) ⟨1⟩

def erc20AllowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  erc20MappingSlot (keyValueToWord spender) (erc20AllowanceOwnerSlot owner)

@[simp] theorem erc20BalanceOfSlot_eq (owner : KeyValue) :
    erc20BalanceOfSlot owner = erc20MappingSlot (keyValueToWord owner) ⟨0⟩ :=
  rfl

@[simp] theorem erc20AllowanceOwnerSlot_eq (owner : KeyValue) :
    erc20AllowanceOwnerSlot owner = erc20MappingSlot (keyValueToWord owner) ⟨1⟩ :=
  rfl

@[simp] theorem erc20AllowanceSlot_eq (owner spender : KeyValue) :
    erc20AllowanceSlot owner spender =
      erc20MappingSlot (keyValueToWord spender)
        (erc20MappingSlot (keyValueToWord owner) ⟨1⟩) :=
  rfl

/-- The complete ERC20 storage backend, generated at elaboration time from the Solidity
    declarations.  Its generated locator is a single closed term rather than a runtime traversal
    of `erc20StorageDecls`. -/
def erc20GeneratedStorageBackend : StorageBackend :=
  solidityStorage! [([] : List StructDecl)] [erc20StorageDecls]

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "initialSupply", ty := uint256 }]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (balanceOfRef sender) (.var "initialSupply"),
        .assign .storage totalSupplyRef (.var "initialSupply") ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage totalSupplyRef)] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (balanceOfRef (.var "owner")))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := [uint256]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (allowanceRef (.var "owner") (.var "spender")))] ] }

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .assign .storage (allowanceRef sender (.var "spender")) (.var "value"),
        .return [(.boolLit true)] ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "to", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef sender)),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (balanceOfRef sender) (.binary .sub (.var "fromBalance") (.var "value")),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign .storage (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return [(.boolLit true)] ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "from", ty := addr }, { name := "to", ty := addr },
      { name := "value", ty := uint256 }]
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "currentAllowance" (some uint256) (.storage (allowanceRef (.var "from") sender)),
        .require (.binary .ge (.var "currentAllowance") (.var "value")),
        .letDecl "fromBalance" (some uint256) (.storage (balanceOfRef (.var "from"))),
        .require (.binary .ge (.var "fromBalance") (.var "value")),
        .assign .storage (allowanceRef (.var "from") sender)
          (.binary .sub (.var "currentAllowance") (.var "value")),
        .assign .storage (balanceOfRef (.var "from"))
          (valueInUInt256
            (.binary .sub (.storage (balanceOfRef (.var "from"))) (.var "value"))),
        .letDecl "toBalance" (some uint256) (.storage (balanceOfRef (.var "to"))),
        .letDecl "newToBalance" (some uint256)
          (valueInUInt256 (.binary .add (.var "toBalance") (.var "value"))),
        .assign .storage (balanceOfRef (.var "to")) (.var "newToBalance"),
        .return [(.boolLit true)] ] }

def erc20Contract : ContractDecl :=
  { name := "ERC20"
    storage := erc20StorageDecls
    ctor := constructorDecl
    transitions :=
      [ approveTransition,
        totalSupplyTransition,
        transferFromTransition,
        balanceOfTransition,
        transferTransition,
        allowanceTransition ] }

end ERC20

def erc20Config : Config :=
  { storage := ERC20.erc20GeneratedStorageBackend
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment ERC20.erc20Contract.ctor.params }

@[simp] theorem erc20Config_storage_totalSupply :
    erc20Config.storage.locate? { base := "totalSupply", steps := [] } =
      fun _ => some (ERC20.erc20Uint256Loc ⟨2⟩) :=
  rfl

@[simp] theorem erc20Config_storage_balanceOf (owner : KeyValue) :
    erc20Config.storage.locate? { base := "balanceOf", steps := [.mindex owner] } =
      fun _ => some (ERC20.erc20Uint256Loc (ERC20.erc20BalanceOfSlot owner)) :=
  rfl

@[simp] theorem erc20Config_storage_allowance (owner spender : KeyValue) :
    erc20Config.storage.locate? { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      fun _ => some (ERC20.erc20Uint256Loc (ERC20.erc20AllowanceSlot owner spender)) :=
  rfl

@[simp] theorem erc20Config_read_totalSupply (evm : EVM.State) :
    erc20Config.storage.read { base := "totalSupply", steps := [] }
        ERC20.uint256Storage evm =
      .ok (storageLocLoad evm (ERC20.erc20Uint256Loc ⟨2⟩)) := by
  change (solidityStorageBackend _).read _ (.elem (.int ERC20.uint256Int)) evm = _
  apply solidityStorageBackend_read_elem
  rfl

@[simp] theorem erc20Config_read_balanceOf (owner : KeyValue) (evm : EVM.State) :
    erc20Config.storage.read { base := "balanceOf", steps := [.mindex owner] }
        ERC20.uint256Storage evm =
      .ok (storageLocLoad evm (ERC20.erc20Uint256Loc (ERC20.erc20BalanceOfSlot owner))) := by
  change (solidityStorageBackend _).read _ (.elem (.int ERC20.uint256Int)) evm = _
  apply solidityStorageBackend_read_elem
  rfl

@[simp] theorem erc20Config_read_allowance (owner spender : KeyValue) (evm : EVM.State) :
    erc20Config.storage.read
        { base := "allowance", steps := [.mindex owner, .mindex spender] }
        ERC20.uint256Storage evm =
      .ok (storageLocLoad evm
        (ERC20.erc20Uint256Loc (ERC20.erc20AllowanceSlot owner spender))) := by
  change (solidityStorageBackend _).read _ (.elem (.int ERC20.uint256Int)) evm = _
  apply solidityStorageBackend_read_elem
  rfl

theorem erc20Config_write_totalSupply {evm evm' : EVM.State} {n : Int}
    (hstore : storageLocStore evm (ERC20.erc20Uint256Loc ⟨2⟩) (.int n) = some evm') :
    erc20Config.storage.write { base := "totalSupply", steps := [] }
        ERC20.uint256Storage (.int n) evm = .ok evm' := by
  change (solidityStorageBackend _).write _ (.elem (.int ERC20.uint256Int)) (.int n) evm = _
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore

theorem erc20Config_write_balanceOf {evm evm' : EVM.State} (owner : KeyValue) {n : Int}
    (hstore : storageLocStore evm
      (ERC20.erc20Uint256Loc (ERC20.erc20BalanceOfSlot owner)) (.int n) = some evm') :
    erc20Config.storage.write { base := "balanceOf", steps := [.mindex owner] }
        ERC20.uint256Storage (.int n) evm = .ok evm' := by
  change (solidityStorageBackend _).write _ (.elem (.int ERC20.uint256Int)) (.int n) evm = _
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore

theorem erc20Config_write_allowance {evm evm' : EVM.State} (owner spender : KeyValue) {n : Int}
    (hstore : storageLocStore evm
      (ERC20.erc20Uint256Loc (ERC20.erc20AllowanceSlot owner spender)) (.int n) = some evm') :
    erc20Config.storage.write
        { base := "allowance", steps := [.mindex owner, .mindex spender] }
        ERC20.uint256Storage (.int n) evm = .ok evm' := by
  change (solidityStorageBackend _).write _ (.elem (.int ERC20.uint256Int)) (.int n) evm = _
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore
