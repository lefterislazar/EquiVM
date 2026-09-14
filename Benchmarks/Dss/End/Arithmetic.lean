import Benchmarks.Dss.End.Pack

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

abbrev endUIntValue (w : UInt256) : Value :=
  .int (Int.ofNat w.toNat)

abbrev endGenericMulProduct (x y : UInt256) : UInt256 :=
  UInt256.mul x y

abbrev endGenericMulStore (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (endUIntValue y)).insert "x" (endUIntValue x)

abbrev endGenericMulZStore (x y : UInt256) : Store :=
  (endGenericMulStore x y).insert "z" (endUIntValue (endGenericMulProduct x y))

abbrev endGenericRmulMStore (x y : UInt256) : Store :=
  (endGenericMulStore x y).insert "m" (endUIntValue (endGenericMulProduct x y))

abbrev endGenericRmulResult (x y : UInt256) : UInt256 :=
  UInt256.div (endGenericMulProduct x y) endRayWord

theorem endGenericMulStore_get_x (x y : UInt256) :
    (endGenericMulStore x y).get? "x" = some (endUIntValue x) := by
  exact store_get_self ((∅ : Store).insert "y" (endUIntValue y)) "x" (endUIntValue x)

theorem endGenericMulStore_get_y (x y : UInt256) :
    (endGenericMulStore x y).get? "y" = some (endUIntValue y) := by
  unfold endGenericMulStore
  rw [store_get_ne ((∅ : Store).insert "y" (endUIntValue y)) (k := "x") (a := "y")
    (endUIntValue x) (by decide)]
  exact store_get_self (∅ : Store) "y" (endUIntValue y)

theorem endGenericMulStore_getElem_x (x y : UInt256) :
    (endGenericMulStore x y)["x"] = endUIntValue x := by
  have hopt : (endGenericMulStore x y)["x"]? = some (endUIntValue x) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endGenericMulStore_get_x x y
  have hmem : "x" ∈ endGenericMulStore x y := by
    simp [endGenericMulStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endGenericMulStore x y) "x" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endGenericMulStore_getElem_y (x y : UInt256) :
    (endGenericMulStore x y)["y"] = endUIntValue y := by
  have hopt : (endGenericMulStore x y)["y"]? = some (endUIntValue y) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endGenericMulStore_get_y x y
  have hmem : "y" ∈ endGenericMulStore x y := by
    simp [endGenericMulStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endGenericMulStore x y) "y" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endGenericMulZStore_get_z (x y : UInt256) :
    (endGenericMulZStore x y).get? "z" =
      some (endUIntValue (endGenericMulProduct x y)) := by
  exact store_get_self (endGenericMulStore x y) "z" (endUIntValue (endGenericMulProduct x y))

theorem endGenericMulZStore_get_x (x y : UInt256) :
    (endGenericMulZStore x y).get? "x" = some (endUIntValue x) := by
  unfold endGenericMulZStore
  rw [store_get_ne (endGenericMulStore x y) (k := "z") (a := "x")
    (endUIntValue (endGenericMulProduct x y)) (by decide)]
  exact endGenericMulStore_get_x x y

theorem endGenericMulZStore_get_y (x y : UInt256) :
    (endGenericMulZStore x y).get? "y" = some (endUIntValue y) := by
  unfold endGenericMulZStore
  rw [store_get_ne (endGenericMulStore x y) (k := "z") (a := "y")
    (endUIntValue (endGenericMulProduct x y)) (by decide)]
  exact endGenericMulStore_get_y x y

theorem endGenericMulZStore_getElem_x (x y : UInt256) :
    (endGenericMulZStore x y)["x"] = endUIntValue x := by
  have hopt : (endGenericMulZStore x y)["x"]? = some (endUIntValue x) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endGenericMulZStore_get_x x y
  have hmem : "x" ∈ endGenericMulZStore x y := by
    simp [endGenericMulZStore, endGenericMulStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endGenericMulZStore x y) "x" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endGenericMulZStore_getElem_y (x y : UInt256) :
    (endGenericMulZStore x y)["y"] = endUIntValue y := by
  have hopt : (endGenericMulZStore x y)["y"]? = some (endUIntValue y) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endGenericMulZStore_get_y x y
  have hmem : "y" ∈ endGenericMulZStore x y := by
    simp [endGenericMulZStore, endGenericMulStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endGenericMulZStore x y) "y" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endGenericMulZStore_getElem_z (x y : UInt256) :
    (endGenericMulZStore x y)["z"] = endUIntValue (endGenericMulProduct x y) := by
  have hopt :
      (endGenericMulZStore x y)["z"]? = some (endUIntValue (endGenericMulProduct x y)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endGenericMulZStore_get_z x y
  have hmem : "z" ∈ endGenericMulZStore x y := by
    simp [endGenericMulZStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endGenericMulZStore x y) "z" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endGenericRmulMStore_get_m (x y : UInt256) :
    (endGenericRmulMStore x y).get? "m" =
      some (endUIntValue (endGenericMulProduct x y)) := by
  exact store_get_self (endGenericMulStore x y) "m" (endUIntValue (endGenericMulProduct x y))

theorem endGenericRmulMStore_get_x (x y : UInt256) :
    (endGenericRmulMStore x y).get? "x" = some (endUIntValue x) := by
  unfold endGenericRmulMStore
  rw [store_get_ne (endGenericMulStore x y) (k := "m") (a := "x")
    (endUIntValue (endGenericMulProduct x y)) (by decide)]
  exact endGenericMulStore_get_x x y

theorem endGenericRmulMStore_get_y (x y : UInt256) :
    (endGenericRmulMStore x y).get? "y" = some (endUIntValue y) := by
  unfold endGenericRmulMStore
  rw [store_get_ne (endGenericMulStore x y) (k := "m") (a := "y")
    (endUIntValue (endGenericMulProduct x y)) (by decide)]
  exact endGenericMulStore_get_y x y

theorem endGenericRmulMStore_getElem_m (x y : UInt256) :
    (endGenericRmulMStore x y)["m"] = endUIntValue (endGenericMulProduct x y) := by
  have hopt :
      (endGenericRmulMStore x y)["m"]? = some (endUIntValue (endGenericMulProduct x y)) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact endGenericRmulMStore_get_m x y
  have hmem : "m" ∈ endGenericRmulMStore x y := by
    simp [endGenericRmulMStore, Std.HashMap.mem_insert]
  have hpos := getElem?_pos (endGenericRmulMStore x y) "m" hmem
  rw [hpos] at hopt
  exact Option.some.inj hopt

theorem endGenericMulProduct_toNat (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    (endGenericMulProduct x y).toNat = x.toNat * y.toNat := by
  unfold endGenericMulProduct
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]

theorem endEvalGenericMulExpr (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) =
      .ok (endUIntValue (endGenericMulProduct x y)) := by
  have hprod := endGenericMulProduct_toNat x y hfit
  have hfitPow : x.toNat * y.toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hnotHi :
      ¬ Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact Int.ofNat_lt.mpr hfitPow
  have hmulInt :
      Int.ofNat x.toNat * Int.ofNat y.toNat = Int.ofNat (x.toNat * y.toNat) := by
    exact (Nat.cast_mul x.toNat y.toNat).symm
  unfold u256
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int, endUIntValue]
  rw [hmulInt]
  have hcond :
      (decide (Int.ofNat (x.toNat * y.toNat) < 0) ||
        decide (Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg : decide (Int.ofNat (x.toNat * y.toNat) < 0) = false :=
      decide_eq_false (show ¬ Int.ofNat (x.toNat * y.toNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [hprod, endGenericMulProduct, endUIntValue]

theorem endEvalGenericMulExpr_revert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    evalExpr? config { contract := contract, locals := endGenericMulStore x y } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) =
      .revert := by
  have hhi :
      decide (Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ (256 : Nat)) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  have hmulInt :
      Int.ofNat x.toNat * Int.ofNat y.toNat = Int.ofNat (x.toNat * y.toNat) := by
    exact (Nat.cast_mul x.toNat y.toNat).symm
  unfold u256
  simp only [evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int, endUIntValue]
  rw [hmulInt, hhi]
  simp

theorem endEvalGenericMulGuard (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endGenericMulZStore x y } evm
      (.binary .or
        (.binary .eq (.var "y") (.intLit 0))
        (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
      .ok (.bool true) := by
  by_cases hy : y = ⟨0⟩
  · simp [evalExpr?, endGenericMulZStore_getElem_y, hy, EvalResult.ofOption,
      EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  · have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy (uint256_toNat_eq_zero hzero)
    have hyIntNe : Int.ofNat y.toNat ≠ 0 := by
      intro hzero
      exact hyNatNe (Int.ofNat_eq_zero.mp hzero)
    have hprod := endGenericMulProduct_toNat x y hfit
    have hdiv :
        Int.ofNat (endGenericMulProduct x y).toNat / Int.ofNat y.toNat =
          Int.ofNat x.toNat := by
      rw [hprod]
      have hnat : (x.toNat * y.toNat) / y.toNat = x.toNat := by
        rw [Nat.mul_comm]
        exact Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hyNatNe)
      change (((x.toNat * y.toNat : Nat) : Int) / ((y.toNat : Nat) : Int)) =
        (((x.toNat : Nat) : Int))
      rw [← Int.natCast_div]
      exact congrArg Int.ofNat hnat
    simp only [evalExpr?, endGenericMulZStore_get_x, endGenericMulZStore_get_y,
      endGenericMulZStore_get_z, EvalResult.ofOption, EvalResult.bind, bind, pure,
      evalBinaryOp?, endUIntValue]
    rw [hdiv]
    have hyValue : (Value.int (Int.ofNat y.toNat) == Value.int 0) = false := by
      simp [hyNatNe]
    rw [hyValue]
    rw [if_neg hyIntNe]
    simp

theorem endGenericMulFunctionOk (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := endGenericMulZStore x y } evm
        (some [endUIntValue (endGenericMulProduct x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [mulFunction, endGenericMulZStore] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalGenericMulExpr evm x y hfit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalGenericMulGuard evm x y hfit)) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.var "z"])
          (values := [endUIntValue (endGenericMulProduct x y)])
          (by
            simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
              endGenericMulZStore_get_z])))

theorem endGenericMulFunctionRevert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      mulFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [mulFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalGenericMulExpr_revert evm x y hover)))

theorem endEvalGenericRmulMulArgs (evm : EVM.State) (x y : UInt256) :
    evalExprs? config { contract := contract, locals := endGenericMulStore x y } evm
      [.var "x", .var "y"] =
      .ok [endUIntValue x, endUIntValue y] := by
  simp [evalExprs?, evalExpr?, endGenericMulStore_get_x, endGenericMulStore_get_y,
    endGenericMulStore_getElem_x, endGenericMulStore_getElem_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem endBindParams_mul_generic (x y : UInt256) :
    bindParams? mulFunction.params [endUIntValue x, endUIntValue y] =
      some (endGenericMulStore x y) := by
  simp [bindParams?, mulFunction, endGenericMulStore, endUIntValue]

theorem endGenericRmulInternalMulOk (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endGenericMulStore x y } evm
      (.internalCall "mul" [.var "x", .var "y"] "m")
      (.ok { contract := contract, locals := endGenericRmulMStore x y } evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endGenericRmulMStore] using
    internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endGenericMulStore x y })
      (evm := evm) (calleeEvm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .var "y"])
      (argVals := [endUIntValue x, endUIntValue y])
      (callee := mulFunction) (locals := endGenericMulStore x y)
      (calleeSolm := { contract := contract, locals := endGenericMulZStore x y })
      (value := some [endUIntValue (endGenericMulProduct x y)])
      (endEvalGenericRmulMulArgs evm x y)
      (by
        change lookupCallable? contract "mul" = some mulFunction.toCallable
        rfl)
      (endBindParams_mul_generic x y)
      (endGenericMulFunctionOk evm x y hfit)

theorem endGenericRmulInternalMulRevert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecStmt config { contract := contract, locals := endGenericMulStore x y } evm
      (.internalCall "mul" [.var "x", .var "y"] "m") .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endGenericMulStore x y })
    (evm := evm) (name := "mul") (retVar := "m")
    (args := [.var "x", .var "y"])
    (argVals := [endUIntValue x, endUIntValue y])
    (callee := mulFunction) (locals := endGenericMulStore x y)
    (endEvalGenericRmulMulArgs evm x y)
    (by
      change lookupCallable? contract "mul" = some mulFunction.toCallable
      rfl)
    (endBindParams_mul_generic x y)
    (endGenericMulFunctionRevert evm x y hover)

theorem endEvalGenericRmulReturn (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endGenericRmulMStore x y } evm
      (.binary .div (.var "m") (.intLit RAY)) =
      .ok (endUIntValue (endGenericRmulResult x y)) := by
  have hprod := endGenericMulProduct_toNat x y hfit
  have hres :
      (endGenericRmulResult x y).toNat = (x.toNat * y.toNat) / endRayNat := by
    unfold endGenericRmulResult
    rw [udiv_toNat, hprod, endRayWord_toNat]
  have hdiv :
      Int.ofNat (endGenericMulProduct x y).toNat / RAY =
        Int.ofNat (endGenericRmulResult x y).toNat := by
    rw [endRay_int_eq, hprod, hres]
    change (((x.toNat * y.toNat : Nat) : Int) / ((endRayNat : Nat) : Int)) =
      (((x.toNat * y.toNat) / endRayNat : Nat) : Int)
    rw [← Int.natCast_div]
  simp only [evalExpr?, endGenericRmulMStore_get_m, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?, endUIntValue]
  rw [hdiv]
  have hrayNe : RAY ≠ 0 := by
    native_decide
  simp [hrayNe]

theorem endGenericRmulFunctionOk (evm : EVM.State) (x y : UInt256)
    (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      rmulFunction.body
      (.returned { contract := contract, locals := endGenericRmulMStore x y } evm
        (some [endUIntValue (endGenericRmulResult x y)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [rmulFunction] using
    (ExecBlock.consNormal
      (endGenericRmulInternalMulOk evm x y hfit) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.binary .div (.var "m") (.intLit RAY)])
          (values := [endUIntValue (endGenericRmulResult x y)])
          (by
            simp [evalExprs?, endEvalGenericRmulReturn evm x y hfit,
              EvalResult.bind, bind, pure])))

theorem endGenericRmulFunctionRevert (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := endGenericMulStore x y } evm
      rmulFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [rmulFunction] using
    (ExecBlock.consRevert
      (endGenericRmulInternalMulRevert evm x y hover))

end Benchmarks.Dss.End
