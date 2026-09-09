import Solm.Semantics
import Solm.SolidityLayout

namespace NestedCaller

open Solm ABI Ethereum

abbrev uint256 : ABIType := .elem (.int (.uint ⟨256, by decide⟩))
abbrev addr : ABIType := .elem .address

def sampleFunction : FunctionDecl where
  name := "sample"
  params := [{ name := "target", ty := addr }, { name := "i", ty := uint256 }]
  returnType := [uint256]
  body :=
    [ .letGas "remaining",
      .ite (.binary .lt (.var "remaining") (.intLit 1000)) [.return [.intLit 0]] [],
      .externalCall (.var "target") "probe" (.intLit 0) [.var "i"] "value",
      .return [.var "value"] ]

def loopBody : List Stmt :=
  [ .internalCall "sample" [.var "target", .var "i"] "value",
    .ite (.binary .eq (.var "value") (.intLit 0)) [.continue] [],
    .ite (.binary .eq (.var "value") (.intLit 1)) [.break] [],
    .letDecl "last" none (.var "value") ]

def loopPost : List Stmt :=
  [.letDecl "i" none (.binary .add (.var "i") (.intLit 1))]

def runTransition : TransitionDecl where
  name := "run"
  params := [{ name := "target", ty := addr }, { name := "count", ty := uint256 }]
  returnType := [uint256]
  body :=
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .require (.binary .le (.var "count") (.intLit 16)),
      .letDecl "last" none (.intLit 0),
      .for [.letDecl "i" none (.intLit 0)] (.binary .lt (.var "i") (.var "count"))
        loopPost loopBody,
      .return [.var "last"] ]

def nestedCallerContract : ContractDecl where
  name := "NestedCaller"
  storage := []
  ctor := { params := [], body := [] }
  functions := [sampleFunction]
  transitions := [runTransition]

def probeSelector : ByteArray := ⟨#[0xdb, 0x08, 0x24, 0x40]⟩

def nestedCallerConfig : Config where
  storage := { layout := fun _ _ => none }
  externalABI :=
    { encode? := fun name args =>
        if name = "probe" then
          match args with
          | [.int i] => some (probeSelector ++ (EVM.wordOfInt i).toByteArray)
          | _ => none
        else none
      decode? := fun name bytes =>
        if name = "probe" then ABI.decodeReturnValues? [uint256] bytes else none }
  selfDeployment := genSolidityConstructorDeployment nestedCallerContract.ctor.params

end NestedCaller
