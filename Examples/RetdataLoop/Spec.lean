import Solm.Semantics
import Solm.SolidityLayout

/-!
# RetdataLoop — symbolic loop with low-level call returndata accumulation

This is a deliberately small proof-target scaffold for the case where a loop has:

* a symbolic upper bound (`targets.length`);
* low-level calls whose receiver and calldata depend on the iteration;
* dynamic `bytes` returndata allocated by solc on every successful iteration;
* scalar accumulation from a decoded `uint256`, avoiding dynamic `bytes[]` array support.

The intended proof shape is a BlindAuction-Reveal-style parallel execution invariant, enriched with
a symbolic free-memory cursor.
-/

open Solm ABI

namespace RetdataLoop

def uint256Int : IntType := .uint ⟨256, by decide⟩

def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def bytesTy : ABIType := .bytes
def addrArrayTy : ABIType := .dynamicArray addr

def uint256St : StorageType := .elem (.int uint256Int)

def varRef (name : Ident) : StorageRef := { base := name }
def localIndex (name : Ident) (idx : Expr) : StorageRef :=
  { base := name, steps := [.aindex idx] }

def localLength (name : Ident) : Expr :=
  .arrayLength .localVar (varRef name)

def arrGet (name : Ident) (idx : Expr) : Expr :=
  .index (.var name) idx

def arrSet (name : Ident) (idx value : Expr) : Stmt :=
  .assign .localVar (localIndex name idx) value

def eqE (x y : Expr) : Expr := .binary .eq x y
def ltE (x y : Expr) : Expr := .binary .lt x y
def addE (x y : Expr) : Expr := .binary .add x y
def u256 (x : Expr) : Expr := .inRange uint256Int x

def collectCalldataExpr : Expr :=
  .abiEncodePacked [(uint256, .var "i")]

def decodeReturndataExpr : Expr :=
  .abiDecode uint256 (.var "returndata")

def collectTransition : TransitionDecl :=
  { name := "collect"
    params :=
      [ { name := "targets", ty := addrArrayTy } ]
    returnType := [uint256]
    body :=
      [ .require (eqE (.env .callvalue) (.intLit 0)),
        .letDecl "n" (some uint256) (localLength "targets"),
        .letDecl "total" (some uint256) (.intLit 0),
        .for
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (ltE (.var "i") (.var "n"))
          [ .assign .localVar (varRef "i") (u256 (addE (.var "i") (.intLit 1))) ]
          [ .lowLevelCall
              (arrGet "targets" (.var "i"))
              (.intLit 0)
              collectCalldataExpr
              "ok"
              "returndata",
            .require (.var "ok"),
            .require (eqE (localLength "returndata") (.intLit 32)),
            .letDecl "value" (some uint256) decodeReturndataExpr,
            .assign .localVar (varRef "total") (u256 (addE (.var "total") (.var "value"))) ],
        .return [.var "total"] ] }

def contract : ContractDecl :=
  { name := "RetdataLoop"
    storage := []
    ctor := { params := [], body := [] }
    transitions := [collectTransition] }

end RetdataLoop

def retdataLoopConfig : Config :=
  { storage := { layout := fun _ _ => none }
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment RetdataLoop.contract.ctor.params }
