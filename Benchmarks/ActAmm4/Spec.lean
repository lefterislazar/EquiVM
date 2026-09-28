import Solm.Semantics
import Solm.SolidityLayout

/-!
# Solm model for Act's `sand/amm4` Amm

The model includes the inherited Token surface and leaves reserve-token interactions as typed,
opaque EVM calls. Solidity 0.8 overflow, underflow, and division-by-zero behavior is explicit.
-/

open Solm ABI

namespace Benchmarks.ActAmm4

def uint256Int : IntType := .uint ⟨256, by decide⟩
def uint256 : ABIType := .elem (.int uint256Int)
def addr : ABIType := .elem .address
def boolTy : ABIType := .elem .bool
def uint256St : StorageType := .elem (.int uint256Int)
def addrSt : StorageType := .elem .address

def sender : Expr := .env .caller
def thisAddr : Expr := .env .this
def maxUint256 : Int := (2 : Int) ^ 256 - 1
def minimumLiquidity : Int := 1000
def u256 (e : Expr) : Expr := .inRange uint256Int e
def checkedAdd (x y : Expr) : Expr := u256 (.binary .add x y)
def checkedSub (x y : Expr) : Expr := u256 (.binary .sub x y)
def checkedMul (x y : Expr) : Expr := u256 (.binary .mul x y)

def selectorBytes (a b c d : UInt8) : ByteArray := ⟨#[a, b, c, d]⟩
def balanceOfSelector : ByteArray := selectorBytes 0x70 0xa0 0x82 0x31
def transferSelector : ByteArray := selectorBytes 0xb7 0x76 0x0c 0x8f

def decodeReturn? (ty : ABIType) (out : EVM.Bytes) : Option (List Value) :=
  (ABI.decodeReturnValueWithMode? DecodeMode.modern ty out).map (fun v => [v])

def externalABI : ExternalCallABI where
  encode? := fun name args =>
    if name = "balanceOf" then
      ABI.encodeCallWithSelector? balanceOfSelector [addr] args
    else if name = "transfer" then
      ABI.encodeCallWithSelector? transferSelector [uint256, addr] args
    else
      none
  decode? := fun name out =>
    if name = "balanceOf" then
      decodeReturn? uint256 out
    else if name = "transfer" then
      decodeReturn? boolTy out
    else
      none

/-! ## Storage -/

def totalSupplyRef : StorageRef := { base := "totalSupply" }
def balanceOfRef (owner : Expr) : StorageRef :=
  { base := "balanceOf", steps := [.mindex owner] }
def allowanceRef (owner spender : Expr) : StorageRef :=
  { base := "allowance", steps := [.mindex owner, .mindex spender] }
def token0Ref : StorageRef := { base := "token0" }
def token1Ref : StorageRef := { base := "token1" }
def reserve0Ref : StorageRef := { base := "reserve0" }
def reserve1Ref : StorageRef := { base := "reserve1" }

def storageDecls : List StorageDecl :=
  [ { name := "totalSupply", ty := uint256St },
    { name := "balanceOf", ty := .mapping .address uint256St },
    { name := "allowance", ty := .mapping .address (.mapping .address uint256St) },
    { name := "token0", ty := addrSt },
    { name := "token1", ty := addrSt },
    { name := "reserve0", ty := uint256St },
    { name := "reserve1", ty := uint256St } ]

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
def addrLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 20, hbound := by decide, type := .address }

def storageLayout : StorageLayout where
  layout ref _ :=
    match ref.base, ref.steps with
    | "totalSupply", [] => some (wordLoc ⟨0⟩)
    | "balanceOf", [.mindex owner] => some (wordLoc (balanceOfSlot owner))
    | "allowance", [.mindex owner, .mindex spender] =>
        some (wordLoc (allowanceSlot owner spender))
    | "token0", [] => some (addrLoc ⟨3⟩)
    | "token1", [] => some (addrLoc ⟨4⟩)
    | "reserve0", [] => some (wordLoc ⟨5⟩)
    | "reserve1", [] => some (wordLoc ⟨6⟩)
    | _, _ => none

def nonpayable : List Stmt :=
  [ .require (.binary .eq (.env .callvalue) (.intLit 0)) ]

def checkedDivInto (name : Ident) (numerator denominator : Expr) : List Stmt :=
  [ .require (.binary .ne denominator (.intLit 0)),
    .letDecl name (some uint256) (.binary .div numerator denominator) ]

def tokenBalance (token : Expr) (name : Ident) : Stmt :=
  .externalCall token "balanceOf" (.intLit 0) [thisAddr] name false
def tokenTransfer (token amount recipient : Expr) (name : Ident) : Stmt :=
  .externalCall token "transfer" (.intLit 0) [amount, recipient] name

/-! ## Inherited Token functions -/

def totalSupplyTransition : TransitionDecl :=
  { name := "totalSupply", params := [], returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage totalSupplyRef)] ] }

def balanceOfTransition : TransitionDecl :=
  { name := "balanceOf", params := [{ name := "owner", ty := addr }], returnType := [uint256]
    body := nonpayable ++ [ .return [(.storage (balanceOfRef (.var "owner")))] ] }

def allowanceTransition : TransitionDecl :=
  { name := "allowance"
    params := [{ name := "owner", ty := addr }, { name := "spender", ty := addr }]
    returnType := [uint256]
    body := nonpayable ++
      [ .return [(.storage (allowanceRef (.var "owner") (.var "spender")))] ] }

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

/-! ## AMM functions -/

def mintTransition : TransitionDecl :=
  { name := "mint", params := [{ name := "to", ty := addr }], returnType := [uint256]
    body := nonpayable ++
      [ .require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
        tokenBalance (.storage token0Ref) "balance0",
        tokenBalance (.storage token1Ref) "balance1",
        .letDecl "amount0" (some uint256)
          (checkedSub (.var "balance0") (.storage reserve0Ref)),
        .letDecl "amount1" (some uint256)
          (checkedSub (.var "balance1") (.storage reserve1Ref)),
        .letDecl "liq0Numerator" (some uint256)
          (checkedMul (.var "amount0") (.storage totalSupplyRef)) ] ++
      checkedDivInto "liq0" (.var "liq0Numerator") (.storage reserve0Ref) ++
      [ .letDecl "liq1Numerator" (some uint256)
          (checkedMul (.var "amount1") (.storage totalSupplyRef)) ] ++
      checkedDivInto "liq1" (.var "liq1Numerator") (.storage reserve1Ref) ++
      [ .ite (.binary .le (.var "liq0") (.var "liq1"))
          [ .letDecl "liquidity" (some uint256) (.var "liq0") ]
          [ .letDecl "liquidity" (some uint256) (.var "liq1") ],
        .require (.binary .ne (.var "liquidity") (.intLit 0)),
        .assign .storage totalSupplyRef
          (checkedAdd (.storage totalSupplyRef) (.var "liquidity")),
        .assign .storage (balanceOfRef (.var "to"))
          (checkedAdd (.storage (balanceOfRef (.var "to"))) (.var "liquidity")),
        .assign .storage reserve0Ref (.var "balance0"),
        .assign .storage reserve1Ref (.var "balance1"),
        .return [(.var "liquidity")] ] }

def burnTransition : TransitionDecl :=
  { name := "burn"
    params := [{ name := "liquidity", ty := uint256 }, { name := "to", ty := addr }]
    returnType := []
    body := nonpayable ++
      [ .require (.binary .ne (.storage totalSupplyRef) (.intLit 0)),
        .letDecl "amount0Numerator" (some uint256)
          (checkedMul (.var "liquidity") (.storage reserve0Ref)) ] ++
      checkedDivInto "amount0" (.var "amount0Numerator") (.storage totalSupplyRef) ++
      [ .letDecl "amount1Numerator" (some uint256)
          (checkedMul (.var "liquidity") (.storage reserve1Ref)) ] ++
      checkedDivInto "amount1" (.var "amount1Numerator") (.storage totalSupplyRef) ++
      [ .assign .storage totalSupplyRef
          (checkedSub (.storage totalSupplyRef) (.var "liquidity")),
        .assign .storage (balanceOfRef sender)
          (checkedSub (.storage (balanceOfRef sender)) (.var "liquidity")),
        tokenTransfer (.storage token0Ref) (.var "amount0") (.var "to") "transfer0Ok",
        tokenTransfer (.storage token1Ref) (.var "amount1") (.var "to") "transfer1Ok",
        tokenBalance (.storage token0Ref) "newBalance0",
        tokenBalance (.storage token1Ref) "newBalance1",
        .assign .storage reserve0Ref (.var "newBalance0"),
        .assign .storage reserve1Ref (.var "newBalance1") ] }

def swapTransition : TransitionDecl :=
  { name := "swap"
    params := [{ name := "amount0Out", ty := uint256 },
      { name := "amount1Out", ty := uint256 }, { name := "to", ty := addr }]
    returnType := []
    body := nonpayable ++
      [ .require (.binary .or
          (.binary .gt (.var "amount0Out") (.intLit 0))
          (.binary .gt (.var "amount1Out") (.intLit 0))),
        .require (.binary .and
          (.binary .lt (.var "amount0Out") (.storage reserve0Ref))
          (.binary .lt (.var "amount1Out") (.storage reserve1Ref))),
        .require (.binary .and
          (.binary .ne (.var "to") (.storage token0Ref))
          (.binary .ne (.var "to") (.storage token1Ref))),
        tokenTransfer (.storage token0Ref) (.var "amount0Out") (.var "to") "transfer0Ok",
        tokenTransfer (.storage token1Ref) (.var "amount1Out") (.var "to") "transfer1Ok",
        tokenBalance (.storage token0Ref) "balance0",
        tokenBalance (.storage token1Ref) "balance1",
        .letDecl "reserve0AfterOut" (some uint256)
          (checkedSub (.storage reserve0Ref) (.var "amount0Out")),
        .ite (.binary .gt (.var "balance0") (.var "reserve0AfterOut"))
          [ .letDecl "amount0In" (some uint256)
              (checkedSub (.var "balance0") (.var "reserve0AfterOut")) ]
          [ .letDecl "amount0In" (some uint256) (.intLit 0) ],
        .letDecl "reserve1AfterOut" (some uint256)
          (checkedSub (.storage reserve1Ref) (.var "amount1Out")),
        .ite (.binary .gt (.var "balance1") (.var "reserve1AfterOut"))
          [ .letDecl "amount1In" (some uint256)
              (checkedSub (.var "balance1") (.var "reserve1AfterOut")) ]
          [ .letDecl "amount1In" (some uint256) (.intLit 0) ],
        .require (.binary .or
          (.binary .gt (.var "amount0In") (.intLit 0))
          (.binary .gt (.var "amount1In") (.intLit 0))),
        .letDecl "newProduct" (some uint256)
          (checkedMul (.var "balance0") (.var "balance1")),
        .letDecl "oldProduct" (some uint256)
          (checkedMul (.storage reserve0Ref) (.storage reserve1Ref)),
        .require (.binary .ge (.var "newProduct") (.var "oldProduct")),
        .assign .storage reserve0Ref (.var "balance0"),
        .assign .storage reserve1Ref (.var "balance1") ] }

/-! ## Constructor and contract -/

def constructorDecl : ConstructorDecl :=
  { params := [{ name := "t0", ty := addr }, { name := "t1", ty := addr },
      { name := "liquidity", ty := uint256 }]
    body := nonpayable ++
      [ .letDecl "baseSupply" (some uint256)
          (checkedSub (.var "liquidity") (.intLit minimumLiquidity)),
        .assign .storage totalSupplyRef (.var "baseSupply"),
        .assign .storage (balanceOfRef sender) (.var "baseSupply"),
        .require (.binary .ne (.var "t0") (.var "t1")),
        .assign .storage token0Ref (.var "t0"),
        .assign .storage token1Ref (.var "t1"),
        .letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity")),
        tokenBalance (.storage token0Ref) "initialBalance0",
        tokenBalance (.storage token1Ref) "initialBalance1",
        .letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1")),
        .require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
        .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .assign .storage totalSupplyRef (.var "liquidity"),
        .assign .storage (balanceOfRef thisAddr) (.intLit minimumLiquidity),
        .assign .storage (balanceOfRef sender) (.var "baseSupply"),
        tokenBalance (.storage token0Ref) "reserveBalance0",
        .assign .storage reserve0Ref (.var "reserveBalance0"),
        tokenBalance (.storage token1Ref) "reserveBalance1",
        .assign .storage reserve1Ref (.var "reserveBalance1") ] }

def contract : ContractDecl :=
  { name := "Amm"
    storage := storageDecls
    ctor := constructorDecl
    transitions :=
      [ allowanceTransition,
        approveTransition,
        balanceOfTransition,
        burnTransition,
        mintTransition,
        swapTransition,
        totalSupplyTransition,
        transferTransition,
        transferFromTransition ] }

def config : Config :=
  { storage := storageLayout
    externalABI := externalABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Benchmarks.ActAmm4
