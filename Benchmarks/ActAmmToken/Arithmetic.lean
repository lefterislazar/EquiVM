import Benchmarks.ActAmmToken.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmmToken

-- LIBRARY CANDIDATE: Reasoning.SolmBody, uint256 checked subtraction of evaluated operands.
theorem tokenEvalCheckedSub_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
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

theorem tokenEvalCheckedSub_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : ℕ}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b)))
    (hunder : a < b) :
    evalExpr? cfg frame evm (checkedSub x y) = .revert := by
  simp only [checkedSub, u256, evalExpr?, hx, hy, EvalResult.bind, bind,
    evalBinaryOp?, pure]
  simp [uint256Int]
  omega

theorem tokenEvalCheckedAdd_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
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

theorem tokenEvalCheckedAdd_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
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


end Benchmarks.ActAmmToken
