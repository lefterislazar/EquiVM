import Solm.Semantics
import Solm.SolidityLayout

/-!
# Token used by Act's multisource AMM fixture

This models the complete public surface of the independently compiled `Token` selected by
`tests/hevm/pass/multisource/amm/amm.json`.  It is not the shorter base contract embedded in
`amm.sol`: this implementation additionally exposes `burn`, `burnFrom`, and `mint`.
-/

open Solm ABI

namespace Benchmarks.ActAmmToken

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool

def uint256St : StorageType := .elem (.int uint256Int)

def sender : Expr := .env .caller
def maxUint256 : Int := (2 : Int) ^ 256 - 1
def u256 (e : Expr) : Expr := .inRange uint256Int e
def checkedAdd (x y : Expr) : Expr := u256 (.binary .add x y)
def checkedSub (x y : Expr) : Expr := u256 (.binary .sub x y)

/-! ## Storage -/

def totalSupplyRef : StorageRef := { base := "totalSupply" }
def balanceOfRef (owner : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex owner] }
def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }

def storageDecls : List StorageDecl :=
  [ { name := "totalSupply", ty := uint256St },
    { name := "balanceOf", ty := .mapping .address uint256St },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256St) } ]

def mapSlot (key baseSlot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (ffi.KEC (key.toByteArray ++ baseSlot.toByteArray))

def balanceOfSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨1⟩

def allowanceOwnerSlot (owner : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord owner) ⟨2⟩

def allowanceSlot (owner spender : KeyValue) : Ethereum.UInt256 :=
  mapSlot (keyValueToWord spender) (allowanceOwnerSlot owner)

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256Int }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "totalSupply", [] => some (wordLoc ⟨0⟩)
    | "balanceOf", [.mindex owner] => some (wordLoc (balanceOfSlot owner))
    | "allowance", [.mindex owner, .mindex spender] =>
        some (wordLoc (allowanceSlot owner spender))
    | _, _ => none

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

/-! ## Constructor and getters -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "_totalSupply", ty := uint256 }]
    body := nonpayable ++
      [ .assign .storage totalSupplyRef (.var "_totalSupply"),
        .assign .storage (balanceOfRef sender) (.var "_totalSupply") ] }

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply"
    params := []
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage totalSupplyRef)] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf"
    params := [{ name := "owner", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage (balanceOfRef (.var "owner")))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++
      [ .return [(.storage (allowanceRef (.var "owner") (.var "spender")))] ] }

/-! ## Mutating functions -/

def approveTransition : TransitionDecl :=
  { name := "approve"
    params := [{ name := "spender", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++
      [ .ite (.binary .ne (.var "spender") sender)
          [ .assign .storage (allowanceRef sender (.var "spender")) (.var "value") ] [],
        .return [(.boolLit true)] ] }

def transferTransition : TransitionDecl :=
  { name := "transfer"
    params := [{ name := "value", ty := uint256 }, { name := "to", ty := addr }]
    returnType := [boolTy]
    body := nonpayable ++
      [ .assign .storage (balanceOfRef sender)
          (checkedSub (.storage (balanceOfRef sender)) (.var "value")),
        .assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")),
        .return [(.boolLit true)] ] }

def transferFromTransition : TransitionDecl :=
  { name := "transferFrom"
    params := [{ name := "from", ty := addr }, { name := "to", ty := addr },
      { name := "value", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++
      [ .ite
          (.binary .and
            (.binary .ne (.var "from") sender)
            (.binary .ne (.storage (allowanceRef (.var "from") sender))
              (.intLit maxUint256)))
          [ .assign .storage (allowanceRef (.var "from") sender)
              (checkedSub (.storage (allowanceRef (.var "from") sender)) (.var "value")) ] [],
        .assign .storage (balanceOfRef (.var "from"))
          (checkedSub (.storage (balanceOfRef (.var "from"))) (.var "value")),
        .assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "value")),
        .return [(.boolLit true)] ] }

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [{ name := "value", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++
      [ .assign .storage totalSupplyRef
          (checkedSub (.storage totalSupplyRef) (.var "value")),
        .assign .storage (balanceOfRef sender)
          (checkedSub (.storage (balanceOfRef sender)) (.var "value")),
        .return [(.boolLit true)] ] }

def burnFromTransition : TransitionDecl :=
  { name := "burnFrom"
    params := [{ name := "account", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++
      [ .ite
          (.binary .and
            (.binary .ne (.var "account") sender)
            (.binary .ne (.storage (allowanceRef (.var "account") sender))
              (.intLit maxUint256)))
          [ .assign .storage (allowanceRef (.var "account") sender)
              (checkedSub (.storage (allowanceRef (.var "account") sender)) (.var "value")) ] [],
        .assign .storage totalSupplyRef
          (checkedSub (.storage totalSupplyRef) (.var "value")),
        .assign .storage (balanceOfRef (.var "account"))
          (checkedSub (.storage (balanceOfRef (.var "account"))) (.var "value")),
        .return [(.boolLit true)] ] }

def mintTransition : TransitionDecl :=
  { name := "mint"
    params := [{ name := "account", ty := addr }, { name := "value", ty := uint256 }]
    returnType := [boolTy]
    body := nonpayable ++
      [ .assign .storage totalSupplyRef
          (checkedAdd (.storage totalSupplyRef) (.var "value")),
        .assign .storage (balanceOfRef (.var "account"))
          (checkedAdd (.storage (balanceOfRef (.var "account"))) (.var "value")),
        .return [(.boolLit true)] ] }

def contract : ContractDecl :=
  { name := "Token"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ allowanceTransition,
        approveTransition,
        balanceOfTransition,
        burnTransition,
        burnFromTransition,
        mintTransition,
        totalSupplyTransition,
        transferTransition,
        transferFromTransition ] }

def config : Config :=
  { storage := storageLayout
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.ActAmmToken
