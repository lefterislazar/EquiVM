import Examples.ERC20.Spec
import Solm.VyperLayout

/-!
# Vyper ERC20 — Solm specification and storage layout

The source behavior is the same ERC20 Solm AST used by `Examples/ERC20`; the compiler-specific
part is the Vyper storage layout.  Vyper 0.4.3's `layout` output for `ERC20.vy` is:

* `balanceOf`: slot 0
* `allowance`: slot 1
* `totalSupply`: slot 2

For `HashMap`, Vyper derives entries as `keccak256(baseSlot ++ key)`, unlike Solidity's
`keccak256(key ++ baseSlot)`.
-/

open Solm ABI

namespace VyperERC20

abbrev uint256Int : IntType := ERC20.uint256Int
abbrev uint256 : ABIType := ERC20.uint256
abbrev uint256Storage : StorageType := ERC20.uint256Storage
abbrev addr : ABIType := ERC20.addr

abbrev sender : Expr := ERC20.sender

abbrev balanceOfRef (owner : Expr) : StorageRef :=
  ERC20.balanceOfRef owner

abbrev allowanceRef (owner spender : Expr) : StorageRef :=
  ERC20.allowanceRef owner spender

abbrev totalSupplyRef : StorageRef :=
  ERC20.totalSupplyRef

abbrev erc20StorageDecls : List StorageDecl :=
  ERC20.erc20StorageDecls

abbrev erc20Contract : ContractDecl :=
  ERC20.erc20Contract

def erc20BalanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  vyperMappingSlot ⟨0⟩ owner

def erc20AllowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  vyperMappingSlot ⟨1⟩ owner

def erc20AllowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  vyperMappingSlot (erc20AllowanceOwnerSlot owner) spender

def erc20StorageLayout : StorageLayout :=
  fun ref _ =>
    match ref.base, ref.steps with
    | "balanceOf", [.mindex owner] => some (vyperUint256Loc (erc20BalanceOfSlot owner))
    | "allowance", [.mindex owner, .mindex spender] =>
        some (vyperUint256Loc (erc20AllowanceSlot owner spender))
    | "totalSupply", [] => some (vyperUint256Loc ⟨2⟩)
    | _, _ => none

@[simp] theorem erc20BalanceOfSlot_eq (owner : KeyValue) :
    erc20BalanceOfSlot owner = vyperMappingSlot ⟨0⟩ owner :=
  rfl

@[simp] theorem erc20AllowanceOwnerSlot_eq (owner : KeyValue) :
    erc20AllowanceOwnerSlot owner = vyperMappingSlot ⟨1⟩ owner :=
  rfl

@[simp] theorem erc20AllowanceSlot_eq (owner spender : KeyValue) :
    erc20AllowanceSlot owner spender =
      vyperMappingSlot (vyperMappingSlot ⟨1⟩ owner) spender :=
  rfl

@[simp] theorem erc20StorageLayout_totalSupply :
    erc20StorageLayout { base := "totalSupply", steps := [] } =
      fun _ => some (vyperUint256Loc ⟨2⟩) :=
  rfl

@[simp] theorem erc20StorageLayout_balanceOf (owner : KeyValue) :
    erc20StorageLayout { base := "balanceOf", steps := [.mindex owner] } =
      fun _ => some (vyperUint256Loc (erc20BalanceOfSlot owner)) :=
  rfl

@[simp] theorem erc20StorageLayout_allowance (owner spender : KeyValue) :
    erc20StorageLayout { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      fun _ => some (vyperUint256Loc (erc20AllowanceSlot owner spender)) :=
  rfl

def erc20StorageBackend : StorageBackend :=
  solidityStorageBackend erc20StorageLayout

end VyperERC20

def vyperERC20Config : Config :=
  { storage := VyperERC20.erc20StorageBackend
    externalABI := defaultExternalCallABI
    abiDecodeMode := DecodeMode.vyper
    selfDeployment := genSolidityConstructorDeployment VyperERC20.erc20Contract.ctor.params }

@[simp] theorem vyperERC20Config_storage_totalSupply :
    vyperERC20Config.storage.locate? { base := "totalSupply", steps := [] } =
      fun _ => some (vyperUint256Loc ⟨2⟩) :=
  rfl

@[simp] theorem vyperERC20Config_storage_balanceOf (owner : KeyValue) :
    vyperERC20Config.storage.locate? { base := "balanceOf", steps := [.mindex owner] } =
      fun _ => some (vyperUint256Loc (VyperERC20.erc20BalanceOfSlot owner)) :=
  rfl

@[simp] theorem vyperERC20Config_storage_allowance (owner spender : KeyValue) :
    vyperERC20Config.storage.locate? { base := "allowance", steps := [.mindex owner, .mindex spender] } =
      fun _ => some (vyperUint256Loc (VyperERC20.erc20AllowanceSlot owner spender)) :=
  rfl

@[simp] theorem vyperERC20Config_read_totalSupply (evm : EVM.State) :
    vyperERC20Config.storage.read { base := "totalSupply", steps := [] }
        VyperERC20.uint256Storage evm =
      .ok (storageLocLoad evm (vyperUint256Loc ⟨2⟩)) := by
  apply solidityStorageBackend_read_elem
  rfl

@[simp] theorem vyperERC20Config_read_balanceOf (owner : KeyValue) (evm : EVM.State) :
    vyperERC20Config.storage.read { base := "balanceOf", steps := [.mindex owner] }
        VyperERC20.uint256Storage evm =
      .ok (storageLocLoad evm (vyperUint256Loc (VyperERC20.erc20BalanceOfSlot owner))) := by
  apply solidityStorageBackend_read_elem
  rfl

@[simp] theorem vyperERC20Config_read_allowance
    (owner spender : KeyValue) (evm : EVM.State) :
    vyperERC20Config.storage.read
        { base := "allowance", steps := [.mindex owner, .mindex spender] }
        VyperERC20.uint256Storage evm =
      .ok (storageLocLoad evm (vyperUint256Loc
        (VyperERC20.erc20AllowanceSlot owner spender))) := by
  apply solidityStorageBackend_read_elem
  rfl

theorem vyperERC20Config_write_totalSupply {evm evm' : EVM.State} {n : Int}
    (hstore : storageLocStore evm (vyperUint256Loc ⟨2⟩) (.int n) = some evm') :
    vyperERC20Config.storage.write { base := "totalSupply", steps := [] }
        VyperERC20.uint256Storage (.int n) evm = .ok evm' := by
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore

theorem vyperERC20Config_write_balanceOf {evm evm' : EVM.State}
    (owner : KeyValue) {n : Int}
    (hstore : storageLocStore evm
      (vyperUint256Loc (VyperERC20.erc20BalanceOfSlot owner)) (.int n) = some evm') :
    vyperERC20Config.storage.write { base := "balanceOf", steps := [.mindex owner] }
        VyperERC20.uint256Storage (.int n) evm = .ok evm' := by
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore

theorem vyperERC20Config_write_allowance {evm evm' : EVM.State}
    (owner spender : KeyValue) {n : Int}
    (hstore : storageLocStore evm
      (vyperUint256Loc (VyperERC20.erc20AllowanceSlot owner spender)) (.int n) = some evm') :
    vyperERC20Config.storage.write
        { base := "allowance", steps := [.mindex owner, .mindex spender] }
        VyperERC20.uint256Storage (.int n) evm = .ok evm' := by
  apply solidityStorageBackend_write_elem
  · rfl
  · exact hstore
