import Solm.Semantics
import Solm.MetaSolidityLayout

/-!
# OpenZeppelin AccessControl benchmark spec

Solm specification for the concrete `AccessControlBench` wrapper.  The wrapper grants
`DEFAULT_ADMIN_ROLE` to `msg.sender` in its constructor.  Events and custom-error payloads are
omitted; storage effects and return values are modelled.
-/

open Solm ABI

namespace OpenZeppelinBench.AccessControl

def uint256Int : IntType := .uint ⟨256, by decide⟩
def bytes4Width : Fin 32 := ⟨3, by decide⟩
def bytes32Width : Fin 32 := ⟨31, by decide⟩

def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytes4 : ABIType := .elem (.bytes bytes4Width)
def bytes32 : ABIType := .elem (.bytes bytes32Width)

def boolSt : StorageType := .elem .bool
def bytes32St : StorageType := .elem (.bytes bytes32Width)

def sender : Expr := .env .caller
def defaultAdminRole : Expr := .fixedBytesLit bytes32Width (List.replicate 32 0)
def ierc165Id : Expr := .fixedBytesLit bytes4Width [0x01, 0xff, 0xc9, 0xa7]
def iaccessControlId : Expr := .fixedBytesLit bytes4Width [0x79, 0x65, 0xdb, 0x0b]

def roleHasRoleRef (role account : Expr) : StorageRef :=
  { base := "_roles", steps := [.mindex role, .field "hasRole", .mindex account] }

def roleAdminRef (role : Expr) : StorageRef :=
  { base := "_roles", steps := [.mindex role, .field "adminRole"] }

def roleDataSt : StorageType :=
  .struct "RoleData" [("hasRole", .mapping .address boolSt), ("adminRole", bytes32St)]

def storageDecls : List StorageDecl :=
  [ { name := "_roles", ty := .mapping (.bytes bytes32Width) roleDataSt } ]

def roleDataStruct : StructDecl :=
  { name := "RoleData"
    fields :=
      [ { name := "hasRole", ty := .mapping .address boolSt },
        { name := "adminRole", ty := bytes32St } ] }

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def addSlot (slot : Ethereum.UInt256) (offset : Nat) : Ethereum.UInt256 :=
  EVM.word (slot.toNat + offset)

def roleDataSlot (role : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord role) ⟨0⟩

def roleHasRoleSlot (role account : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord account) (roleDataSlot role)

def roleAdminSlot (role : KeyValue) : Ethereum.UInt256 :=
  addSlot (roleDataSlot role) 1

def boolLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 1, hbound := by decide, type := .bool }

def bytes32Loc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .bytes bytes32Width }

def storageBackend : StorageBackend :=
  solidityStorage! [([roleDataStruct] : List StructDecl)] [storageDecls]

def defaultAdminRoleTransition : TransitionDecl :=
  { name := "DEFAULT_ADMIN_ROLE"
    params := []
    returnType := [bytes32]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [defaultAdminRole] ] }

def supportsInterfaceTransition : TransitionDecl :=
  { name := "supportsInterface"
    params := [{ name := "interfaceId", ty := bytes4 }]
    returnType := [boolTy]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [
          (.binary .or
            (.binary .eq (.var "interfaceId") iaccessControlId)
            (.binary .eq (.var "interfaceId") ierc165Id))] ] }

def hasRoleTransition : TransitionDecl :=
  { name := "hasRole"
    params := [{ name := "role", ty := bytes32 }, { name := "account", ty := addr }]
    returnType := [boolTy]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (roleHasRoleRef (.var "role") (.var "account")))] ] }

def getRoleAdminTransition : TransitionDecl :=
  { name := "getRoleAdmin"
    params := [{ name := "role", ty := bytes32 }]
    returnType := [bytes32]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [(.storage (roleAdminRef (.var "role")))] ] }

def grantRoleTransition : TransitionDecl :=
  { name := "grantRole"
    params := [{ name := "role", ty := bytes32 }, { name := "account", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "adminRole" (some bytes32) (.storage (roleAdminRef (.var "role"))),
        .require (.storage (roleHasRoleRef (.var "adminRole") sender)),
        .ite
          (.unary .not (.storage (roleHasRoleRef (.var "role") (.var "account"))))
          [ .assign .storage (roleHasRoleRef (.var "role") (.var "account")) (.boolLit true) ]
          [] ] }

def revokeRoleTransition : TransitionDecl :=
  { name := "revokeRole"
    params := [{ name := "role", ty := bytes32 }, { name := "account", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .letDecl "adminRole" (some bytes32) (.storage (roleAdminRef (.var "role"))),
        .require (.storage (roleHasRoleRef (.var "adminRole") sender)),
        .ite
          (.storage (roleHasRoleRef (.var "role") (.var "account")))
          [ .assign .storage (roleHasRoleRef (.var "role") (.var "account")) (.boolLit false) ]
          [] ] }

def renounceRoleTransition : TransitionDecl :=
  { name := "renounceRole"
    params := [{ name := "role", ty := bytes32 }, { name := "callerConfirmation", ty := addr }]
    returnType := []
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.binary .eq (.var "callerConfirmation") sender),
        .ite
          (.storage (roleHasRoleRef (.var "role") (.var "callerConfirmation")))
          [ .assign .storage (roleHasRoleRef (.var "role") (.var "callerConfirmation"))
              (.boolLit false) ]
          [] ] }

def constructorDecl : ConstructorDecl :=
  { params := []
    body :=
      [ .assign .storage (roleHasRoleRef defaultAdminRole sender) (.boolLit true) ] }

def contract : ContractDecl :=
  { name := "AccessControlBench"
    storage := storageDecls
    ctor := constructorDecl
    structs := [roleDataStruct]
    transitions :=
      [ defaultAdminRoleTransition,
        getRoleAdminTransition,
        grantRoleTransition,
        hasRoleTransition,
        renounceRoleTransition,
        revokeRoleTransition,
        supportsInterfaceTransition ] }

def config : Config :=
  { storage := storageBackend
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

@[simp] theorem config_read_hasRole (evm : EVM.State) (role account : KeyValue) :
    config.storage.read
        { base := "_roles", steps := [.mindex role, .field "hasRole", .mindex account] }
        (.elem .bool) evm =
      .ok (storageLocLoad evm (boolLoc (roleHasRoleSlot role account))) := by
  apply solidityStorageBackend_read_elem
  rfl

@[simp] theorem config_read_adminRole (evm : EVM.State) (role : KeyValue) :
    config.storage.read { base := "_roles", steps := [.mindex role, .field "adminRole"] }
        (.elem (.bytes bytes32Width)) evm =
      .ok (storageLocLoad evm (bytes32Loc (roleAdminSlot role))) := by
  apply solidityStorageBackend_read_elem
  rfl

theorem config_write_hasRole {evm evm' : EVM.State} {role account : KeyValue} {value : Value}
    (hstore : storageLocStore evm (boolLoc (roleHasRoleSlot role account)) value = some evm') :
    config.storage.write
        { base := "_roles", steps := [.mindex role, .field "hasRole", .mindex account] }
        (.elem .bool) value evm = .ok evm' := by
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore

end OpenZeppelinBench.AccessControl
