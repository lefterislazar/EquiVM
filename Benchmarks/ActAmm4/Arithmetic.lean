import Benchmarks.ActAmm4.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

-- LIBRARY CANDIDATE: Reasoning.SolmBody, uint256 checked subtraction of evaluated operands.
theorem amm4EvalCheckedSub_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hle : b ≤ a) (ha : a < UInt256.size) :
    evalExpr? cfg frame evm (checkedSub x y) =
      .ok (.int (Int.ofNat (a - b))) := by
  change a < 2 ^ 256 at ha
  simp only [checkedSub, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int, Int.ofNat_sub hle]
  omega

theorem amm4EvalCheckedSub_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hunder : a < b) :
    evalExpr? cfg frame evm (checkedSub x y) = .revert := by
  simp only [checkedSub, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int]
  omega

theorem amm4EvalCheckedAdd_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hfit : a + b < UInt256.size) :
    evalExpr? cfg frame evm (checkedAdd x y) =
      .ok (.int (Int.ofNat (a + b))) := by
  change a + b < 2 ^ 256 at hfit
  simp only [checkedAdd, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int]
  omega

theorem amm4EvalCheckedAdd_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hover : UInt256.size ≤ a + b) :
    evalExpr? cfg frame evm (checkedAdd x y) = .revert := by
  change 2 ^ 256 ≤ a + b at hover
  simp only [checkedAdd, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int]
  omega

theorem amm4EvalCheckedMul_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hfit : a * b < UInt256.size) :
    evalExpr? cfg frame evm (checkedMul x y) =
      .ok (.int (Int.ofNat (a * b))) := by
  change a * b < 2 ^ 256 at hfit
  simp only [checkedMul, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int]
  omega

theorem amm4EvalCheckedMul_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hover : UInt256.size ≤ a * b) :
    evalExpr? cfg frame evm (checkedMul x y) = .revert := by
  change 2 ^ 256 ≤ a * b at hover
  simp only [checkedMul, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int]
  omega

theorem amm4EvalNatNeZero_true {cfg : Config} {frame : Frame} {evm : EVM.State}
    {y : Expr} {b : ℕ}
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hb : 0 < b) :
    evalExpr? cfg frame evm (.binary .ne y (.intLit 0)) =
      .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hy]
  omega

theorem amm4EvalNatNeZero_false {cfg : Config} {frame : Frame} {evm : EVM.State}
    {y : Expr}
    (hy : evalExpr? cfg frame evm y = .ok (.int 0)) :
    evalExpr? cfg frame evm (.binary .ne y (.intLit 0)) =
      .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hy]

theorem amm4EvalNatDiv_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hb : 0 < b) :
    evalExpr? cfg frame evm (.binary .div x y) =
      .ok (.int (Int.ofNat (a / b))) := by
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [hb.ne', Int.natCast_ediv]

-- LIBRARY CANDIDATE: Reasoning.SolmBody, ordering evaluated natural-number integers.
theorem amm4EvalNatLe_true {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hle : a ≤ b) :
    evalExpr? cfg frame evm (.binary .le x y) = .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy, hle]

theorem amm4EvalNatLe_false {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hgt : b < a) :
    evalExpr? cfg frame evm (.binary .le x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy]
  omega

-- LIBRARY CANDIDATE: Reasoning.SolmBody, a one-statement local binding block.
theorem amm4LetDeclOne {cfg : Config} {C : ContractDecl} {locals : Store}
    {evm : EVM.State} {name : Ident} {ty : Option ABIType}
    {expr : Expr} {value : Value}
    (heval : evalExpr? cfg { contract := C, locals := locals } evm expr = .ok value) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [.letDecl name ty expr]
      (.ok { contract := C, locals := locals.insert name value } evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl heval) ExecBlock.nil

end Benchmarks.ActAmm4
