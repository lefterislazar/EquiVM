import Benchmarks.Dss.End.Debt
import Benchmarks.Dss.End.ParamGetters
import Benchmarks.Dss.End.SimpleGetters
import Benchmarks.Dss.End.RuntimeBlocks_010
import Benchmarks.Dss.End.RuntimeBlocks_014
import Reasoning.CallRefinement
import Reasoning.RuntimeRefinement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 30000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## `pack(uint256)` -/

abbrev endPackStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "wad" (.int (Int.ofNat (endArg0Word I).toNat))

theorem endDecode_legacyUint_wad_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [uint256] I.calldata =
      some (endPackStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["wad"])
    (types := [uint256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?, uint256, uint256Int]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := I.calldata.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues ["wad"]
      [.int (Int.ofNat (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat)] ∅ =
    some (endPackStore I)
  simp [decodeCalldata.insertValues, endPackStore, endArg0Word]
  rw [hword4]

theorem endDecode_legacyUint_wad_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [uint256] I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := ["wad"])
    (types := [uint256]) (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?, uint256, uint256Int]
  have htake0n : ¬ ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short
    (mode := DecodeMode.legacySolc05) (start := 0) htake0n]
  simp only [Option.bind, bind]

theorem endPackStore_get_wad (I : ExecutionEnv) :
    (endPackStore I).get? "wad" =
      some (.int (Int.ofNat (endArg0Word I).toNat)) := by
  exact store_get_self (∅ : Store) "wad" (.int (Int.ofNat (endArg0Word I).toNat))

theorem endPackStore_get_debt_none (I : ExecutionEnv) :
    (endPackStore I).get? "debt" = none := by
  change (((∅ : Store).insert "wad"
    (.int (Int.ofNat (endArg0Word I).toNat))).get? "debt") = none
  rw [store_get_ne (∅ : Store) (k := "wad") (a := "debt")
    (.int (Int.ofNat (endArg0Word I).toNat)) (by decide)]
  simp

theorem endEvalDebt_pack (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endPackStore I } evm
        (.storage debtRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endPackStore I } evm
      debtRef = .ok { base := "debt", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "debt", steps := [] } : EvaledStorageRef)
      = some (.elem (.int uint256Int)) := by
    decide
  rw [evalExpr_storage_scalar (slot := debtRef)
    (er := { base := "debt", steps := [] })
    (t := .int uint256Int)
    (loc := wordLoc ⟨11⟩)
    (hbase := endPackStore_get_debt_none I)
    (her := her)
    (hty := hty)
    (hloc := endConfig_storage_debt),
    endRuntimeStorageLocLoad_uint256]

theorem endEvalDebtGuard_pack_false (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endPackStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalDebt_pack evm I, hdebt]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalDebtGuard_pack_true (evm : EVM.State) (I : ExecutionEnv)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endPackStore I } evm
      (.binary .ne (.storage debtRef) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalDebt_pack evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      ¬ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat = 0 := by
    intro hzero
    exact hdebt (uint256_toNat_eq_zero hzero)
  simp [evalBinaryOp?, hnat]

theorem endPackBodyDebtFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ = ⟨0⟩) :
    ExecTransitionBody config contract evm (endPackStore I)
      packTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalDebtGuard_pack_false evm I hdebt)))

abbrev endRayNat : Nat := 1000000000000000000000000000

abbrev endRayWord : UInt256 := UInt256.ofNat endRayNat

abbrev endPackVatTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 1))

abbrev endPackVowTarget (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 4))

abbrev endPackMoveSelectorWord : UInt256 := UInt256.ofNat 3140843579

abbrev endPackMoveAmt (I : ExecutionEnv) : UInt256 :=
  UInt256.mul (endArg0Word I) endRayWord

theorem endRayWord_toNat : endRayWord.toNat = endRayNat := by
  native_decide

theorem endMulRayDiv_eq (wad : UInt256)
    (hfit : wad.toNat * endRayNat < UInt256.size) :
    UInt256.div (UInt256.mul wad endRayWord) endRayWord = wad := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, endRayWord_toNat, Nat.mod_eq_of_lt hfit]
  rw [Nat.mul_comm wad.toNat endRayNat]
  rw [Nat.mul_div_right _ (by native_decide : 0 < endRayNat)]

theorem endMulRaySuccessCond (wad : UInt256)
    (hfit : wad.toNat * endRayNat < UInt256.size) :
    UInt256.eq (UInt256.div (UInt256.mul wad endRayWord) endRayWord) wad ≠ ⟨0⟩ := by
  rw [endMulRayDiv_eq wad hfit, uInt256_eq_self]
  decide

theorem u256_mul_div_ne_of_overflow (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (UInt256.mul x y) y ≠ x := by
  intro heq
  have hnat := congrArg UInt256.toNat heq
  rw [udiv_toNat] at hnat
  have hltProd : (UInt256.mul x y).toNat < y.toNat * x.toNat := by
    exact lt_of_lt_of_le (UInt256.mul x y).val.isLt
      (by simpa [Nat.mul_comm] using hover)
  have hlt : (UInt256.mul x y).toNat / y.toNat < x.toNat := by
    exact Nat.div_lt_of_lt_mul hltProd
  exact (Nat.lt_irrefl x.toNat) (by simpa [hnat] using hlt)

theorem endMulRayFailCond (wad : UInt256)
    (hover : UInt256.size ≤ wad.toNat * endRayNat) :
    UInt256.eq (UInt256.div (UInt256.mul wad endRayWord) endRayWord) wad =
      UInt256.ofNat 0 := by
  exact u256_eq_of_ne
    (u256_mul_div_ne_of_overflow wad endRayWord (by
      simpa [endRayWord_toNat] using hover))

theorem endAddSuccessCond (x y : UInt256)
    (hfit : x.toNat + y.toNat < UInt256.size) :
    UInt256.isZero (UInt256.lt (x + y) y) ≠ ⟨0⟩ := by
  have hsum : (x + y).toNat = x.toNat + y.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hlt : UInt256.lt (x + y) y = ⟨0⟩ := by
    exact ult_zero (by rw [hsum]; omega)
  rw [hlt]
  decide

abbrev endMulRayStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "y" (.int RAY)).insert "x"
    (.int (Int.ofNat (endArg0Word I).toNat))

abbrev endMulRayZStore (I : ExecutionEnv) : Store :=
  (endMulRayStore I).insert "z" (.int (Int.ofNat (endPackMoveAmt I).toNat))

theorem endRay_int_eq : RAY = Int.ofNat endRayNat := by
  native_decide

theorem endMulRayStore_get_x (I : ExecutionEnv) :
    (endMulRayStore I).get? "x" =
      some (.int (Int.ofNat (endArg0Word I).toNat)) := by
  exact store_get_self ((∅ : Store).insert "y" (.int RAY)) "x"
    (.int (Int.ofNat (endArg0Word I).toNat))

theorem endMulRayStore_get_y (I : ExecutionEnv) :
    (endMulRayStore I).get? "y" = some (.int RAY) := by
  unfold endMulRayStore
  rw [store_get_ne ((∅ : Store).insert "y" (.int RAY)) (k := "x") (a := "y")
    (.int (Int.ofNat (endArg0Word I).toNat)) (by decide)]
  exact store_get_self (∅ : Store) "y" (.int RAY)

theorem endMulRayZStore_get_z (I : ExecutionEnv) :
    (endMulRayZStore I).get? "z" =
      some (.int (Int.ofNat (endPackMoveAmt I).toNat)) := by
  exact store_get_self (endMulRayStore I) "z"
    (.int (Int.ofNat (endPackMoveAmt I).toNat))

theorem endMulRayZStore_get_x (I : ExecutionEnv) :
    (endMulRayZStore I).get? "x" =
      some (.int (Int.ofNat (endArg0Word I).toNat)) := by
  unfold endMulRayZStore
  rw [store_get_ne (endMulRayStore I) (k := "z") (a := "x")
    (.int (Int.ofNat (endPackMoveAmt I).toNat)) (by decide)]
  exact endMulRayStore_get_x I

theorem endMulRayZStore_get_y (I : ExecutionEnv) :
    (endMulRayZStore I).get? "y" = some (.int RAY) := by
  unfold endMulRayZStore
  rw [store_get_ne (endMulRayStore I) (k := "z") (a := "y")
    (.int (Int.ofNat (endPackMoveAmt I).toNat)) (by decide)]
  exact endMulRayStore_get_y I

theorem endPackMoveAmt_toNat (I : ExecutionEnv)
    (hfit : (endArg0Word I).toNat * endRayNat < UInt256.size) :
    (endPackMoveAmt I).toNat = (endArg0Word I).toNat * endRayNat := by
  unfold endPackMoveAmt
  rw [u256_mul_toNat, endRayWord_toNat, Nat.mod_eq_of_lt hfit]

theorem endEvalMulRayExpr_pack (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endArg0Word I).toNat * endRayNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endMulRayStore I } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) =
      .ok (.int (Int.ofNat (endPackMoveAmt I).toNat)) := by
  have hprod := endPackMoveAmt_toNat I hfit
  have hfitPow : (endArg0Word I).toNat * endRayNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hnotHi :
      ¬ Int.ofNat ((endArg0Word I).toNat * endRayNat) ≥
        (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact Int.ofNat_lt.mpr hfitPow
  have hmulInt :
      (Int.ofNat (endArg0Word I).toNat) * RAY =
        Int.ofNat ((endArg0Word I).toNat * endRayNat) := by
    rw [endRay_int_eq]
    exact (Nat.cast_mul (endArg0Word I).toNat endRayNat).symm
  unfold u256
  simp only [evalExpr?, endMulRayStore_get_x, endMulRayStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int]
  rw [hmulInt]
  have hcond :
      (decide (Int.ofNat ((endArg0Word I).toNat * endRayNat) < 0) ||
        decide (Int.ofNat ((endArg0Word I).toNat * endRayNat) ≥
          (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg :
        decide (Int.ofNat ((endArg0Word I).toNat * endRayNat) < 0) = false :=
      decide_eq_false (show ¬ Int.ofNat ((endArg0Word I).toNat * endRayNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat ((endArg0Word I).toNat * endRayNat) ≥
          (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [hprod]

theorem endEvalMulRayExpr_pack_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endArg0Word I).toNat * endRayNat) :
    evalExpr? config { contract := contract, locals := endMulRayStore I } evm
      (u256 (.binary .mul (.var "x") (.var "y"))) =
      .revert := by
  have hhi :
      decide (Int.ofNat ((endArg0Word I).toNat * endRayNat) ≥
        (2 : Int) ^ (256 : Nat)) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  have hmulInt :
      Int.ofNat (endArg0Word I).toNat * RAY =
        Int.ofNat ((endArg0Word I).toNat * endRayNat) := by
    rw [endRay_int_eq]
    exact (Nat.cast_mul (endArg0Word I).toNat endRayNat).symm
  unfold u256
  simp only [evalExpr?, endMulRayStore_get_x, endMulRayStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int]
  rw [hmulInt, hhi]
  simp

theorem endEvalMulRayGuard_pack (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endArg0Word I).toNat * endRayNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endMulRayZStore I } evm
      (.binary .or
        (.binary .eq (.var "y") (.intLit 0))
        (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
      .ok (.bool true) := by
  have hprod := endPackMoveAmt_toNat I hfit
  have hdiv :
      Int.ofNat (endPackMoveAmt I).toNat / RAY =
        Int.ofNat (endArg0Word I).toNat := by
    rw [endRay_int_eq, hprod]
    have hnat :
        ((endArg0Word I).toNat * endRayNat) / endRayNat =
          (endArg0Word I).toNat := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_right (endArg0Word I).toNat
        (by native_decide : 0 < endRayNat)
    change (((endArg0Word I).toNat * endRayNat : Nat) : Int) /
        ((endRayNat : Nat) : Int) = (((endArg0Word I).toNat : Nat) : Int)
    rw [← Int.natCast_div]
    exact congrArg Int.ofNat hnat
  simp only [evalExpr?, endMulRayZStore_get_x, endMulRayZStore_get_y,
    endMulRayZStore_get_z, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?]
  rw [hdiv]
  have hrayValue : (Value.int RAY == Value.int 0) = false := by
    native_decide
  have hrayNe : RAY ≠ 0 := by
    native_decide
  rw [hrayValue]
  simp [hrayNe]

theorem endMulRayFunctionOk (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endArg0Word I).toNat * endRayNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endMulRayStore I } evm
      mulFunction.body
      (.returned { contract := contract, locals := endMulRayZStore I } evm
        (some [.int (Int.ofNat (endPackMoveAmt I).toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [mulFunction] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl (endEvalMulRayExpr_pack evm I hfit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalMulRayGuard_pack evm I hfit)) <|
      ExecBlock.consReturn
        (ExecStmt.return (by
          change (do
              let value ← evalExpr? config
                { contract := contract, locals := endMulRayZStore I } evm (.var "z")
              let values ← pure []
              pure (value :: values)) =
            EvalResult.ok [Value.int (Int.ofNat (endPackMoveAmt I).toNat)]
          rw [evalExpr?]
          simp [EvalResult.ofOption, EvalResult.bind, bind, pure])))

theorem endMulRayFunctionRevert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endArg0Word I).toNat * endRayNat) :
    ExecFuncBody config { contract := contract, locals := endMulRayStore I } evm
      mulFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [mulFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalMulRayExpr_pack_revert evm I hover)))

abbrev endPackAmtStore (I : ExecutionEnv) : Store :=
  (endPackStore I).insert "amt" (.int (Int.ofNat (endPackMoveAmt I).toNat))

theorem endPackAmtStore_get_amt (I : ExecutionEnv) :
    (endPackAmtStore I).get? "amt" =
      some (.int (Int.ofNat (endPackMoveAmt I).toNat)) := by
  exact store_get_self (endPackStore I) "amt"
    (.int (Int.ofNat (endPackMoveAmt I).toNat))

theorem endPackAmtStore_get_wad (I : ExecutionEnv) :
    (endPackAmtStore I).get? "wad" =
      some (.int (Int.ofNat (endArg0Word I).toNat)) := by
  unfold endPackAmtStore
  rw [store_get_ne (endPackStore I) (k := "amt") (a := "wad")
    (.int (Int.ofNat (endPackMoveAmt I).toNat)) (by decide)]
  exact endPackStore_get_wad I

theorem endPackAmtStore_get_vat_none (I : ExecutionEnv) :
    (endPackAmtStore I).get? "vat" = none := by
  unfold endPackAmtStore
  rw [store_get_ne (endPackStore I) (k := "amt") (a := "vat")
    (.int (Int.ofNat (endPackMoveAmt I).toNat)) (by decide)]
  change (((∅ : Store).insert "wad"
    (.int (Int.ofNat (endArg0Word I).toNat))).get? "vat") = none
  rw [store_get_ne (∅ : Store) (k := "wad") (a := "vat")
    (.int (Int.ofNat (endArg0Word I).toNat)) (by decide)]
  simp

theorem endPackAmtStore_get_vow_none (I : ExecutionEnv) :
    (endPackAmtStore I).get? "vow" = none := by
  unfold endPackAmtStore
  rw [store_get_ne (endPackStore I) (k := "amt") (a := "vow")
    (.int (Int.ofNat (endPackMoveAmt I).toNat)) (by decide)]
  change (((∅ : Store).insert "wad"
    (.int (Int.ofNat (endArg0Word I).toNat))).get? "vow") = none
  rw [store_get_ne (∅ : Store) (k := "wad") (a := "vow")
    (.int (Int.ofNat (endArg0Word I).toNat)) (by decide)]
  simp

theorem endEvalPackMulArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endPackStore I } evm
      [.var "wad", .intLit RAY] =
      .ok [.int (Int.ofNat (endArg0Word I).toNat), .int RAY] := by
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem endBindParams_mul_pack (I : ExecutionEnv) :
    bindParams? mulFunction.params
      [.int (Int.ofNat (endArg0Word I).toNat), .int RAY] =
      some (endMulRayStore I) := by
  simp [bindParams?, mulFunction, endMulRayStore]

theorem endPackInternalMulOk (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endArg0Word I).toNat * endRayNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := endPackStore I } evm
      (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
      (.ok { contract := contract, locals := endPackAmtStore I } evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endPackAmtStore] using
    internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := endPackStore I })
      (evm := evm) (calleeEvm := evm) (name := "mul") (retVar := "amt")
      (args := [.var "wad", .intLit RAY])
      (argVals := [.int (Int.ofNat (endArg0Word I).toNat), .int RAY])
      (callee := mulFunction) (locals := endMulRayStore I)
      (calleeSolm := { contract := contract, locals := endMulRayZStore I })
      (value := some [.int (Int.ofNat (endPackMoveAmt I).toNat)])
      (endEvalPackMulArgs evm I)
      (by
        change lookupCallable? contract "mul" = some mulFunction.toCallable
        rfl)
      (endBindParams_mul_pack I)
      (endMulRayFunctionOk evm I hfit)

theorem endPackInternalMulRevert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endArg0Word I).toNat * endRayNat) :
    ExecStmt config { contract := contract, locals := endPackStore I } evm
      (.internalCall "mul" [.var "wad", .intLit RAY] "amt") .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := endPackStore I })
    (evm := evm) (name := "mul") (retVar := "amt")
    (args := [.var "wad", .intLit RAY])
    (argVals := [.int (Int.ofNat (endArg0Word I).toNat), .int RAY])
    (callee := mulFunction) (locals := endMulRayStore I)
    (endEvalPackMulArgs evm I)
    (by
      change lookupCallable? contract "mul" = some mulFunction.toCallable
      rfl)
    (endBindParams_mul_pack I)
    (endMulRayFunctionRevert evm I hover)

theorem endEvalVatAddress_pack (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endPackAmtStore I } evm
        (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endPackAmtStore I } evm
      vatRef = .ok { base := "vat", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endPackAmtStore_get_vat_none I) (her := her)
    (hty := hty) (hloc := endConfig_storage_vat),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalVowAddress_pack (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endPackAmtStore I } evm
        vowAddr =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  have her : evalStorageRef config { contract := contract, locals := endPackAmtStore I } evm
      vowRef = .ok { base := "vow", steps := [] } := by
    simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage ({ base := "vow", steps := [] } : EvaledStorageRef)
      = some (.elem .address) := by
    decide
  unfold vowAddr
  rw [evalExpr_storage_scalar (t := .address)
    (hbase := endPackAmtStore_get_vow_none I) (her := her)
    (hty := hty) (hloc := endConfig_storage_vow),
    endRuntimeStorageLocLoad_address_offset0]

theorem endEvalPackMoveArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := endPackAmtStore I } evm
      [sender, vowAddr, .var "amt"] =
      .ok [.address evm.executionEnv.source,
        .address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            solcAddrMask).toNat),
        .int (Int.ofNat (endPackMoveAmt I).toNat)] := by
  simp [evalExprs?, evalExpr?, sender, envValue, EvalResult.ofOption, EvalResult.bind, bind, pure,
    endEvalVowAddress_pack]

theorem endPackSlotLoad_eq_of_callRel {s0 cA σ I evm}
    (h : CallStateRel s0 I (cA, σ) evm) (slot : UInt256) :
    UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask =
      UInt256.land (storageRead I.codeOwner σ slot) solcAddrMask := by
  have hraw :
      Solm.EVM.storageLoad evm I.codeOwner slot = storageRead I.codeOwner σ slot := by
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, storageRead_eq]
      using (accountMapEquiv_storage_findD h.accounts I.codeOwner slot (default : UInt256)).symm
  rw [h.env]
  exact congrArg (fun w => UInt256.land w solcAddrMask) hraw

theorem endPackSourceWord_clean (I : ExecutionEnv) :
    UInt256.land solcAddrMask (UInt256.ofNat I.source.val) =
      UInt256.ofNat I.source.val := by
  change UInt256.land solcAddrMask (solcSourceWord I) = solcSourceWord I
  exact solcAddrMask_clean_left (solcSourceWord_canonical I)

theorem endPackVatTarget_canonical (σ : AccountMap) (I : ExecutionEnv) :
    (endPackVatTarget σ I).toNat < EVM.addressModulus := by
  unfold endPackVatTarget
  rw [u256_land_comm solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 1))]
  exact solcAddrMask_result_canonical _

theorem endPackVowTarget_canonical (σ : AccountMap) (I : ExecutionEnv) :
    (endPackVowTarget σ I).toNat < EVM.addressModulus := by
  unfold endPackVowTarget
  rw [u256_land_comm solcAddrMask (storageRead I.codeOwner σ (UInt256.ofNat 4))]
  exact solcAddrMask_result_canonical _

theorem endPackVowTarget_clean (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land solcAddrMask (endPackVowTarget σ I) = endPackVowTarget σ I := by
  exact solcAddrMask_clean_left (endPackVowTarget_canonical σ I)

theorem endExternalEncode_move_branch (args : List Value) :
    config.externalABI.encode? "move" args =
      ABI.encodeCallWithSelector? moveSelector [addr, addr, uint256] args := by
  dsimp only [config, externalABI]
  rw [if_neg (by decide : ¬ "move" = "cage")]
  rw [if_neg (by decide : ¬ "move" = "vatIlks")]
  rw [if_neg (by decide : ¬ "move" = "catIlks")]
  rw [if_neg (by decide : ¬ "move" = "dogIlks")]
  rw [if_neg (by decide : ¬ "move" = "spotIlks")]
  rw [if_neg (by decide : ¬ "move" = "urns")]
  rw [if_neg (by decide : ¬ "move" = "dai")]
  rw [if_neg (by decide : ¬ "move" = "debt")]
  rw [if_pos (by decide : "move" = "move")]

theorem endEncodeAddress_source (I : ExecutionEnv) :
    encodeABIValue? addr (.address I.source) =
      some (EVM.Word.toBytesBE (UInt256.ofNat I.source.val)) := by
  have hsourceWord : EVM.word I.source.val = UInt256.ofNat I.source.val := by rfl
  simp [addr, encodeABIValue?, encodeABIWord?, hsourceWord]

theorem endEncodeAddress_vow (σ : AccountMap) (I : ExecutionEnv) :
    encodeABIValue? addr
      (.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat)) =
      some (EVM.Word.toBytesBE (endPackVowTarget σ I)) := by
  have hvowMod :
      (endPackVowTarget σ I).toNat % AccountAddress.size =
        (endPackVowTarget σ I).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size]
      using endPackVowTarget_canonical σ I
  have hvowWord :
      EVM.word (endPackVowTarget σ I).toNat = endPackVowTarget σ I :=
    u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, hvowMod, hvowWord]

theorem endEncodeABIWord_uint256 (w : UInt256) :
    encodeABIWord? uint256 (.int (Int.ofNat w.toNat)) = some w := by
  have hword : EVM.word w.toNat = w :=
    u256_ofNat_toNat _
  have hlt : w.toNat < EVM.twoPow 256 := by
    change w.val.val < EVM.twoPow 256
    exact w.val.isLt
  simp [uint256, uint256Int, encodeABIWord?, hword, hlt]

theorem endEncodeUint_packAmt (I : ExecutionEnv) :
    encodeABIValue? uint256 (.int (Int.ofNat (endPackMoveAmt I).toNat)) =
      some (EVM.Word.toBytesBE (endPackMoveAmt I)) := by
  rw [ABI.encodeABIValue?.eq_def]
  change (do
      let word ← encodeABIWord? uint256 (.int (Int.ofNat (endPackMoveAmt I).toNat))
      some (EVM.Word.toBytesBE word)) =
    some (EVM.Word.toBytesBE (endPackMoveAmt I))
  rw [endEncodeABIWord_uint256]
  simp only [bind, Option.bind]

def endPackMovePayloadBytes (σ : AccountMap) (I : ExecutionEnv) : List UInt8 :=
  (EVM.Word.toBytesBE (UInt256.ofNat I.source.val) ++
    EVM.Word.toBytesBE (endPackVowTarget σ I)) ++
    EVM.Word.toBytesBE (endPackMoveAmt I)

def endPackMoveEncodedCall (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  moveSelector ++ ⟨(endPackMovePayloadBytes σ I).toArray⟩

theorem endEncodeABIValues_move (σ : AccountMap) (I : ExecutionEnv) :
    encodeABIValues? [addr, addr, uint256]
      [.address I.source,
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .int (Int.ofNat (endPackMoveAmt I).toNat)] =
      some (endPackMovePayloadBytes σ I) := by
  have hhead : abiTupleHeadSize? [addr, addr, uint256] = some 96 := by native_decide
  have hdynAddr : isDynamicABIType addr = false := by native_decide
  have hdynUint : isDynamicABIType uint256 = false := by native_decide
  rw [ABI.encodeABIValues?.eq_1]
  rw [hhead]
  simp only [bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_source I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, List.nil_append, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeAddress_vow σ I, hdynAddr]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_2]
  rw [endEncodeUint_packAmt I, hdynUint]
  simp only [Bool.false_eq_true, if_false, bind, Option.bind]
  rw [ABI.encodeABIValuesFrom?.eq_1]
  simp only [endPackMovePayloadBytes, List.append_nil]

theorem endEncodeCallWithSelector_move (σ : AccountMap) (I : ExecutionEnv) :
    ABI.encodeCallWithSelector? moveSelector [addr, addr, uint256]
      [.address I.source,
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .int (Int.ofNat (endPackMoveAmt I).toNat)] =
      some (endPackMoveEncodedCall σ I) := by
  rw [encodeCallWithSelector?]
  rw [endEncodeABIValues_move σ I]
  simp [endPackMoveEncodedCall, endPackMovePayloadBytes]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem endExternalEncode_move (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "move"
      [.address I.source,
        .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
        .int (Int.ofNat (endPackMoveAmt I).toNat)] =
      some (endPackMoveEncodedCall σ I) := by
  rw [endExternalEncode_move_branch]
  exact endEncodeCallWithSelector_move σ I

theorem endExternalDecode_move (out : ByteArray) :
    config.externalABI.decode? "move" out = some [] := by
  rfl

theorem endEvalVatExtCodeSize_pack (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endPackAmtStore I } evm
        (.extCodeSize (.storage vatRef)) =
      .ok (.int (Int.ofNat
        (extCodeSizeWord evm.accountMap
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask)).toNat)) := by
  rw [evalExpr?]
  rw [endEvalVatAddress_pack evm I]
  simp only [EvalResult.bind, bind]
  simp only [extCodeSizeWord, State.lookupAccount, accountAddress_ofUInt256_eq_ofNat_toNat]
  cases hacc : evm.accountMap.find?
      (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)
  · rfl
  · rfl

theorem endEvalVatCodeGuard_pack_false (evm : EVM.State) (I : ExecutionEnv)
    (hnocode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endPackAmtStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_pack evm I, hnocode]
  simp [EvalResult.bind, bind, pure, evalExpr?, evalBinaryOp?]

theorem endEvalVatCodeGuard_pack_true (evm : EVM.State) (I : ExecutionEnv)
    (hcode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endPackAmtStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalVatExtCodeSize_pack evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hpos : 0 <
      (extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask)).toNat := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      exact hcode (uint256_toNat_eq_zero hzero))
  simp [evalBinaryOp?, hpos]

theorem endPackBodyPrefixOk (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hmulFit : (endArg0Word I).toNat * endRayNat < UInt256.size)
    (hvatCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endPackStore I } evm
      (nonpayable ++
        [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
          .internalCall "mul" [.var "wad", .intLit RAY] "amt",
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
      (.ok { contract := contract, locals := endPackAmtStore I } evm) := by
  simpa [nonpayable] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtGuard_pack_true evm I hdebt)) <|
      ExecBlock.consNormal
        (endPackInternalMulOk evm I hmulFit) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalVatCodeGuard_pack_true evm I hvatCode)) <|
      ExecBlock.nil)

theorem endPackBodyMulFail (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hover : UInt256.size ≤ (endArg0Word I).toNat * endRayNat) :
    ExecTransitionBody config contract evm (endPackStore I)
      packTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtGuard_pack_true evm I hdebt)) <|
      ExecBlock.consRevert
        (endPackInternalMulRevert evm I hover))

theorem endPackBodyVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hdebt : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩ ≠ ⟨0⟩)
    (hmulFit : (endArg0Word I).toNat * endRayNat < UInt256.size)
    (hvatNoCode : extCodeSizeWord evm.accountMap
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask) = ⟨0⟩) :
    ExecTransitionBody config contract evm (endPackStore I)
      packTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [packTransition, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalDebtGuard_pack_true evm I hdebt)) <|
      ExecBlock.consNormal
        (endPackInternalMulOk evm I hmulFit) <|
      ExecBlock.consRevert
        (ExecStmt.requireFalse (endEvalVatCodeGuard_pack_false evm I hvatNoCode)))

abbrev endPackMoveCallMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  endRuntimeBlocks.endRuntime_block_6462_taken_memory
    (mem := solcFreePtrMem) (x0 := endPackMoveAmt I)
    (x1 := endPackVowTarget σ I) (x2 := UInt256.ofNat I.source.val)
    (x3 := endPackMoveSelectorWord)

theorem endPackMoveCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (endPackMoveCallMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  unfold endPackMoveCallMem
  dsimp [endRuntimeBlocks.endRuntime_block_6462_taken_memory]
  rw [hload]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)).toNat = 132 from by native_decide]
  rw [show ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256))).toNat = 164
    from by native_decide]
  rw [show ((UInt256.ofNat 32) +
      ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)))).toNat = 196
    from by native_decide]
  let moveSelWord : UInt256 :=
    UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) endPackMoveSelectorWord)
      (UInt256.ofNat 224)
  let addrMask : UInt256 :=
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
  let memSel : ByteArray := moveSelWord.toByteArray.write 0 solcFreePtrMem 128 32
  let memSource : ByteArray :=
    (UInt256.land addrMask (UInt256.ofNat I.source.val)).toByteArray.write 0 memSel 132 32
  let memVow : ByteArray :=
    (UInt256.land addrMask (endPackVowTarget σ I)).toByteArray.write 0 memSource 164 32
  have hsizeSel : 128 + 32 ≤ memSel.size :=
    toByteArray_write_size_ge_off_add32_unbounded moveSelWord solcFreePtrMem 128
  have hsizeSource : 132 + 32 ≤ memSource.size :=
    toByteArray_write_size_ge_off_add32_unbounded
      (UInt256.land addrMask (UInt256.ofNat I.source.val)) memSel 132
  have hsizeVow : 164 + 32 ≤ memVow.size :=
    toByteArray_write_size_ge_off_add32_unbounded
      (UInt256.land addrMask (endPackVowTarget σ I)) memSource 164
  change ((endPackMoveAmt I).toByteArray.write 0 memVow 196 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap_unbounded
    (endPackMoveAmt I) memVow 196 64 (by omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land addrMask (endPackVowTarget σ I)) memSource 164 64 (by omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land addrMask (UInt256.ofNat I.source.val)) memSel 132 64
      (by omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    moveSelWord solcFreePtrMem 128 64 (by rw [solcFreePtrMem_size]) (by omega)]
  exact solcFreePtrMem_read64

theorem endPackMoveCallMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (endPackMoveCallMem σ I) = ⟨128⟩ := by
  change (if (⟨64⟩ : UInt256).toNat ≥ (endPackMoveCallMem σ I).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((endPackMoveCallMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩
  exact mloadFreePtrValue (mem := endPackMoveCallMem σ I)
    (by
      have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
        simpa [memLoad] using solcFreePtrMem_mload64
      unfold endPackMoveCallMem
      dsimp [endRuntimeBlocks.endRuntime_block_6462_taken_memory]
      rw [hload]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
      rw [show ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)).toNat = 132 from by native_decide]
      rw [show ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256))).toNat = 164
        from by native_decide]
      rw [show ((UInt256.ofNat 32) +
          ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)))).toNat = 196
        from by native_decide]
      let moveSelWord : UInt256 :=
        UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) endPackMoveSelectorWord)
          (UInt256.ofNat 224)
      let addrMask : UInt256 :=
        UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)
      let memSel : ByteArray := moveSelWord.toByteArray.write 0 solcFreePtrMem 128 32
      let memSource : ByteArray :=
        (UInt256.land addrMask (UInt256.ofNat I.source.val)).toByteArray.write 0 memSel 132 32
      let baseMem : ByteArray :=
        (UInt256.land addrMask (endPackVowTarget σ I)).toByteArray.write 0 memSource 164 32
      have hge := toByteArray_write_size_ge_off_add32_unbounded
        (endPackMoveAmt I) baseMem 196
      change 64 < ((endPackMoveAmt I).toByteArray.write 0 baseMem 196 32).size
      omega)
    (by
      exact endPackMoveCallMem_read64 σ I)

abbrev endPackCallAddrMask : UInt256 :=
  UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)

abbrev endPackMoveSelectorEncodedWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land (UInt256.ofNat 4294967295) endPackMoveSelectorWord)
    (UInt256.ofNat 224)

abbrev endPackMoveMemSel : ByteArray :=
  endPackMoveSelectorEncodedWord.toByteArray.write 0 solcFreePtrMem 128 32

abbrev endPackMoveMemSource (I : ExecutionEnv) : ByteArray :=
  (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val)).toByteArray.write 0
    endPackMoveMemSel 132 32

abbrev endPackMoveMemVow (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.land endPackCallAddrMask (endPackVowTarget σ I)).toByteArray.write 0
    (endPackMoveMemSource I) 164 32

abbrev endPackMoveMemFull (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (endPackMoveAmt I).toByteArray.write 0 (endPackMoveMemVow σ I) 196 32

theorem endPackCallAddrMask_eq_solc :
    endPackCallAddrMask = solcAddrMask := by
  native_decide

theorem endPackMoveCallMem_eq_full (σ : AccountMap) (I : ExecutionEnv) :
    endPackMoveCallMem σ I = endPackMoveMemFull σ I := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  unfold endPackMoveCallMem endPackMoveMemFull endPackMoveMemVow endPackMoveMemSource
    endPackMoveMemSel endPackMoveSelectorEncodedWord endPackCallAddrMask
  dsimp [endRuntimeBlocks.endRuntime_block_6462_taken_memory]
  rw [hload]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
  rw [show ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)).toNat = 132 from by native_decide]
  rw [show ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256))).toNat = 164
    from by native_decide]
  rw [show ((UInt256.ofNat 32) +
      ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256)))).toNat = 196
    from by native_decide]

theorem endPackMoveMemSel_size_ge160 : 160 ≤ endPackMoveMemSel.size := by
  exact toByteArray_write_size_ge_off_add32_unbounded endPackMoveSelectorEncodedWord
    solcFreePtrMem 128

theorem endPackMoveMemSource_size_ge164 (I : ExecutionEnv) :
    164 ≤ (endPackMoveMemSource I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val)) endPackMoveMemSel 132

theorem endPackMoveMemVow_size_ge196 (σ : AccountMap) (I : ExecutionEnv) :
    196 ≤ (endPackMoveMemVow σ I).size := by
  exact toByteArray_write_size_ge_off_add32_unbounded
    (UInt256.land endPackCallAddrMask (endPackVowTarget σ I)) (endPackMoveMemSource I) 164

theorem endPackMoveCallMem_size_ge228 (σ : AccountMap) (I : ExecutionEnv) :
    228 ≤ (endPackMoveCallMem σ I).size := by
  rw [endPackMoveCallMem_eq_full σ I]
  exact toByteArray_write_size_ge_off_add32_unbounded (endPackMoveAmt I)
    (endPackMoveMemVow σ I) 196

theorem endPackMoveSelectorEncodedWord_prefix :
    (endPackMoveSelectorEncodedWord.toByteArray).extract 0 4 = moveSelector := by
  native_decide

theorem endPackMoveCallMem_readSelector (σ : AccountMap) (I : ExecutionEnv) :
    (endPackMoveCallMem σ I).readWithPadding 128 4 = moveSelector := by
  rw [endPackMoveCallMem_eq_full σ I]
  change (((endPackMoveAmt I).toByteArray.write 0 (endPackMoveMemVow σ I) 196 32).readWithPadding
      128 4) = moveSelector
  rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
    (endPackMoveMemVow_size_ge196 σ I) (by omega)
    (by have := endPackMoveMemVow_size_ge196 σ I; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
    (endPackMoveMemSource_size_ge164 I) (by omega)
    (by have := endPackMoveMemSource_size_ge164 I; omega) (by decide) (by decide)]
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
    (by have := endPackMoveMemSel_size_ge160; omega) (by omega)
    (by have := endPackMoveMemSel_size_ge160; omega) (by decide) (by decide)]
  change ((endPackMoveSelectorEncodedWord.toByteArray.write 0 solcFreePtrMem 128 32).readWithPadding
      128 4) = moveSelector
  have hwindow := toByteArray_write_read_window_of_gap_unbounded
    endPackMoveSelectorEncodedWord solcFreePtrMem 128 0 4
    (by decide) (by decide) (by decide)
  simp only [Nat.add_zero] at hwindow
  rw [hwindow, endPackMoveSelectorEncodedWord_prefix]

theorem endPackMoveCallMem_readSource (σ : AccountMap) (I : ExecutionEnv) :
    (endPackMoveCallMem σ I).readWithPadding 132 32 =
      (UInt256.ofNat I.source.val).toByteArray := by
  rw [endPackMoveCallMem_eq_full σ I]
  change (((endPackMoveAmt I).toByteArray.write 0 (endPackMoveMemVow σ I) 196 32).readWithPadding
      132 32) = (UInt256.ofNat I.source.val).toByteArray
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackMoveAmt I)
    (endPackMoveMemVow σ I) 196 132
    (by have := endPackMoveMemVow_size_ge196 σ I; omega) (by omega)]
  rw [toByteArray_write_read_below_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (endPackVowTarget σ I)) (endPackMoveMemSource I)
    164 132 (by have := endPackMoveMemSource_size_ge164 I; omega) (by omega)]
  change ((UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val)).toByteArray.write 0
      endPackMoveMemSel 132 32).readWithPadding 132 32 =
    (UInt256.ofNat I.source.val).toByteArray
  rw [toByteArray_write_read_back_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (UInt256.ofNat I.source.val)) endPackMoveMemSel 132]
  rw [endPackCallAddrMask_eq_solc, endPackSourceWord_clean I]

theorem endPackMoveCallMem_readVow (σ : AccountMap) (I : ExecutionEnv) :
    (endPackMoveCallMem σ I).readWithPadding 164 32 =
      (endPackVowTarget σ I).toByteArray := by
  rw [endPackMoveCallMem_eq_full σ I]
  change (((endPackMoveAmt I).toByteArray.write 0 (endPackMoveMemVow σ I) 196 32).readWithPadding
      164 32) = (endPackVowTarget σ I).toByteArray
  rw [toByteArray_write_read_below_of_gap_unbounded (endPackMoveAmt I)
    (endPackMoveMemVow σ I) 196 164
    (by have := endPackMoveMemVow_size_ge196 σ I; omega) (by omega)]
  change ((UInt256.land endPackCallAddrMask (endPackVowTarget σ I)).toByteArray.write 0
      (endPackMoveMemSource I) 164 32).readWithPadding 164 32 =
    (endPackVowTarget σ I).toByteArray
  rw [toByteArray_write_read_back_of_gap_unbounded
    (UInt256.land endPackCallAddrMask (endPackVowTarget σ I)) (endPackMoveMemSource I) 164]
  rw [endPackCallAddrMask_eq_solc, endPackVowTarget_clean σ I]

theorem endPackMoveCallMem_readAmt (σ : AccountMap) (I : ExecutionEnv) :
    (endPackMoveCallMem σ I).readWithPadding 196 32 =
      (endPackMoveAmt I).toByteArray := by
  rw [endPackMoveCallMem_eq_full σ I]
  change (((endPackMoveAmt I).toByteArray.write 0 (endPackMoveMemVow σ I) 196 32).readWithPadding
      196 32) = (endPackMoveAmt I).toByteArray
  exact toByteArray_write_read_back_of_gap_unbounded (endPackMoveAmt I)
    (endPackMoveMemVow σ I) 196

theorem endPackMoveCallMem_readCallData (σ : AccountMap) (I : ExecutionEnv) :
    (endPackMoveCallMem σ I).readWithPadding 128 100 =
      endPackMoveEncodedCall σ I := by
  have hsize := endPackMoveCallMem_size_ge228 σ I
  rw [show 100 = 4 + 96 from rfl]
  rw [byteArray_readWithPadding_split (endPackMoveCallMem σ I) 128 4 96
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 128 + 4 = 132 by norm_num]
  rw [show 96 = 32 + 64 from rfl]
  rw [byteArray_readWithPadding_split (endPackMoveCallMem σ I) 132 32 64
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 132 + 32 = 164 by norm_num]
  rw [show 64 = 32 + 32 from rfl]
  rw [byteArray_readWithPadding_split (endPackMoveCallMem σ I) 164 32 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  rw [show 164 + 32 = 196 by norm_num]
  rw [endPackMoveCallMem_readSelector σ I, endPackMoveCallMem_readSource σ I,
    endPackMoveCallMem_readVow σ I, endPackMoveCallMem_readAmt σ I]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [endPackMoveEncodedCall, endPackMovePayloadBytes, toByteArray_eq_toBytesBE]

theorem endX_pack_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd824 := endRuntimeBlocks.endRuntime_block_806_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_824 (R :=
      endRuntimeBlocks.endRuntime_block_806_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_806_fallthrough_stack]) (by simpa using rd824)

theorem endX_pack_to_body {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6345⟩
      [endArg0Word I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd828 := endRuntimeBlocks.endRuntime_block_806_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd6345 := endRuntimeBlocks.endRuntime_block_828
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_806_taken_stack] using rd828)
  have hoff : (UInt256.ofNat 4).toNat = 4 := by native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_828_stack, endArg0Word, calldataWord, hoff]
      using rd6345⟩

theorem endX_pack_debt_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : solcSlotWord σ I ⟨11⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_pack_to_body (g := g) hsz36 hsize hreach
  have hcond :
      storageRead I.codeOwner σ (UInt256.ofNat 11) = UInt256.ofNat 0 := by
    rw [storageRead_eq]
    simpa using hdebt
  obtain ⟨_, _, rdRevert⟩ := endRuntimeBlocks.endRuntime_block_6345_fallthrough
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcond rdBody
  exact endRuntimeBlocks.endRuntime_block_6353
    (R := [endArg0Word I, ⟨562⟩, sel])
    (by simp) rdRevert

theorem endX_pack_to_move_setup {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : solcSlotWord σ I ⟨11⟩ ≠ ⟨0⟩)
    (hmulFit : (endArg0Word I).toNat * endRayNat < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6462⟩
      [endPackMoveAmt I, endPackVowTarget σ I, UInt256.ofNat I.source.val,
        endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdBody⟩ := endX_pack_to_body (g := g) hsz36 hsize hreach
  have hcondDebt :
      storageRead I.codeOwner σ (UInt256.ofNat 11) ≠ UInt256.ofNat 0 := by
    intro hzero
    rw [storageRead_eq] at hzero
    exact hdebt (by simpa using hzero)
  obtain ⟨_, _, rd6413⟩ := endRuntimeBlocks.endRuntime_block_6345_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcondDebt
    (by jump_dest) rdBody
  obtain ⟨_, _, rd10170⟩ := endRuntimeBlocks.endRuntime_block_6413
    (x0 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_6413_stack, endPackVatTarget,
      endPackVowTarget, endPackMoveSelectorWord, endRayWord] using rd6413)
  have hcondRay : UInt256.isZero endRayWord = ⟨0⟩ := by
    native_decide
  have rd10180 := endRuntimeBlocks.endRuntime_block_10170_fallthrough
    (x0 := endRayWord)
    (R := [endArg0Word I, ⟨6462⟩, endPackVowTarget σ I, UInt256.ofNat I.source.val,
      endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondRay
    (by simpa [endRuntimeBlocks.endRuntime_block_6413_stack, endPackVatTarget,
      endPackVowTarget, endPackMoveSelectorWord, endRayWord] using rd10170)
  have hrayNe : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10194 := endRuntimeBlocks.endRuntime_block_10180_taken
    (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨0⟩ : UInt256))
    (x2 := endRayWord) (x3 := endArg0Word I)
    (R := [⟨6462⟩, endPackVowTarget σ I, UInt256.ofNat I.source.val,
      endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrayNe (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10170_fallthrough_stack] using rd10180)
  have rd10197 := endRuntimeBlocks.endRuntime_block_10194
    (x0 := endPackMoveAmt I) (x1 := endRayWord) (x2 := endArg0Word I)
    (R := [endPackMoveAmt I, endRayWord, endArg0Word I, ⟨6462⟩,
      endPackVowTarget σ I, UInt256.ofNat I.source.val, endPackMoveSelectorWord,
      endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_10180_taken_stack, endPackMoveAmt]
      using rd10194)
  have hcondMul := endMulRaySuccessCond (endArg0Word I) hmulFit
  have rd10108 := endRuntimeBlocks.endRuntime_block_10197_taken
    (x0 := UInt256.eq (UInt256.div (endPackMoveAmt I) endRayWord) (endArg0Word I))
    (R := [endPackMoveAmt I, endRayWord, endArg0Word I, ⟨6462⟩,
      endPackVowTarget σ I, UInt256.ofNat I.source.val, endPackMoveSelectorWord,
      endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondMul (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10194_stack, endPackMoveAmt] using rd10197)
  have rd6462 := endRuntimeBlocks.endRuntime_block_10108
    (x0 := endPackMoveAmt I) (x1 := endRayWord) (x2 := endArg0Word I)
    (x3 := (⟨6462⟩ : UInt256))
    (R := [endPackVowTarget σ I, UInt256.ofNat I.source.val, endPackMoveSelectorWord,
      endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10197_taken_stack] using rd10108)
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_10108_stack] using rd6462⟩

theorem endX_pack_mul_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : solcSlotWord σ I ⟨11⟩ ≠ ⟨0⟩)
    (hmulOverflow : UInt256.size ≤ (endArg0Word I).toNat * endRayNat)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdBody⟩ := endX_pack_to_body (g := g) hsz36 hsize hreach
  have hcondDebt :
      storageRead I.codeOwner σ (UInt256.ofNat 11) ≠ UInt256.ofNat 0 := by
    intro hzero
    rw [storageRead_eq] at hzero
    exact hdebt (by simpa using hzero)
  obtain ⟨_, _, rd6413⟩ := endRuntimeBlocks.endRuntime_block_6345_taken
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcondDebt
    (by jump_dest) rdBody
  obtain ⟨_, _, rd10170⟩ := endRuntimeBlocks.endRuntime_block_6413
    (x0 := endArg0Word I) (R := [⟨562⟩, sel])
    (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_6413_stack, endPackVatTarget,
      endPackVowTarget, endPackMoveSelectorWord, endRayWord] using rd6413)
  have hcondRay : UInt256.isZero endRayWord = ⟨0⟩ := by
    native_decide
  have rd10180 := endRuntimeBlocks.endRuntime_block_10170_fallthrough
    (x0 := endRayWord)
    (R := [endArg0Word I, ⟨6462⟩, endPackVowTarget σ I, UInt256.ofNat I.source.val,
      endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondRay
    (by simpa [endRuntimeBlocks.endRuntime_block_6413_stack, endPackVatTarget,
      endPackVowTarget, endPackMoveSelectorWord, endRayWord] using rd10170)
  have hrayNe : endRayWord ≠ ⟨0⟩ := by
    native_decide
  have rd10194 := endRuntimeBlocks.endRuntime_block_10180_taken
    (x0 := (⟨0⟩ : UInt256)) (x1 := (⟨0⟩ : UInt256))
    (x2 := endRayWord) (x3 := endArg0Word I)
    (R := [⟨6462⟩, endPackVowTarget σ I, UInt256.ofNat I.source.val,
      endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrayNe (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_10170_fallthrough_stack] using rd10180)
  have rd10197 := endRuntimeBlocks.endRuntime_block_10194
    (x0 := endPackMoveAmt I) (x1 := endRayWord) (x2 := endArg0Word I)
    (R := [endPackMoveAmt I, endRayWord, endArg0Word I, ⟨6462⟩,
      endPackVowTarget σ I, UInt256.ofNat I.source.val, endPackMoveSelectorWord,
      endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp)
    (by simpa [endRuntimeBlocks.endRuntime_block_10180_taken_stack, endPackMoveAmt]
      using rd10194)
  have hcondMul := endMulRayFailCond (endArg0Word I) hmulOverflow
  have rd10202 := endRuntimeBlocks.endRuntime_block_10197_fallthrough
    (x0 := UInt256.eq (UInt256.div (endPackMoveAmt I) endRayWord) (endArg0Word I))
    (R := [endPackMoveAmt I, endRayWord, endArg0Word I, ⟨6462⟩,
      endPackVowTarget σ I, UInt256.ofNat I.source.val, endPackMoveSelectorWord,
      endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hcondMul
    (by simpa [endRuntimeBlocks.endRuntime_block_10194_stack, endPackMoveAmt] using rd10197)
  exact endRuntimeBlocks.endRuntime_block_10202
    (R := endRuntimeBlocks.endRuntime_block_10197_fallthrough_stack
      (R := [endPackMoveAmt I, endRayWord, endArg0Word I, ⟨6462⟩,
        endPackVowTarget σ I, UInt256.ofNat I.source.val, endPackMoveSelectorWord,
        endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_10197_fallthrough_stack])
    rd10202

theorem endX_pack_vat_no_code {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : solcSlotWord σ I ⟨11⟩ ≠ ⟨0⟩)
    (hmulFit : (endArg0Word I).toNat * endRayNat < UInt256.size)
    (hnocode : extCodeSizeWord σ (endPackVatTarget σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd6462⟩ :=
    endX_pack_to_move_setup (g := g) hsz36 hsize hdebt hmulFit hreach
  have hcond :
      UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) =
        UInt256.ofNat 0 := by
    rw [hnocode]
    decide
  obtain ⟨_, _, rd6544⟩ := endRuntimeBlocks.endRuntime_block_6462_fallthrough
    (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcond rd6462
  exact endRuntimeBlocks.endRuntime_block_6544
    (R := endRuntimeBlocks.endRuntime_block_6462_fallthrough_stack
      (mem := solcFreePtrMem) (σ := σ) (x0 := endPackMoveAmt I)
      (x1 := endPackVowTarget σ I) (x2 := UInt256.ofNat I.source.val)
      (x3 := endPackMoveSelectorWord) (x4 := endPackVatTarget σ I)
      (R := [endArg0Word I, ⟨562⟩, sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_6462_fallthrough_stack])
    rd6544

theorem endX_pack_to_move_call {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdebt : solcSlotWord σ I ⟨11⟩ ≠ ⟨0⟩)
    (hmulFit : (endArg0Word I).toNat * endRayNat < UInt256.size)
    (hvatCode : extCodeSizeWord σ (endPackVatTarget σ I) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ aw k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6550⟩
      [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩,
        ⟨228⟩, endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel]
      (endPackMoveCallMem σ I) aw ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd6462⟩ :=
    endX_pack_to_move_setup (g := g) hsz36 hsize hdebt hmulFit hreach
  have hcondCode :
      UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I))) ≠
        UInt256.ofNat 0 := by
    rw [Reasoning.Theory.isZero_eq_zero_of_ne hvatCode]
    native_decide
  obtain ⟨aw6548, k6548, C6548, rd6548⟩ :=
    endRuntimeBlocks.endRuntime_block_6462_taken_packed
      (R := [endArg0Word I, ⟨562⟩, sel]) (by simp) hcondCode (by jump_dest) rd6462
  have hfreeOrig : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := by
    simpa [memLoad] using solcFreePtrMem_mload64
  have hfreeCall : memLoad (UInt256.ofNat 64) (endPackMoveCallMem σ I) = ⟨128⟩ :=
    endPackMoveCallMem_mload64 σ I
  have hend :
      ((UInt256.ofNat 32) +
        ((UInt256.ofNat 32) +
          ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + memLoad (UInt256.ofNat 64) solcFreePtrMem)))) =
        ⟨228⟩ := by
    rw [hfreeOrig]
    native_decide
  have hend' :
      ((UInt256.ofNat 32) +
        ((UInt256.ofNat 32) +
          ((UInt256.ofNat 32) + ((UInt256.ofNat 4) + (⟨128⟩ : UInt256))))) =
        ⟨228⟩ := by
    native_decide
  have hlen' : UInt256.sub (⟨228⟩ : UInt256) ⟨128⟩ = ⟨100⟩ := by
    native_decide
  have hrd6548' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6548⟩
        (UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)) ::
          [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩,
            ⟨228⟩, endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
        (endPackMoveCallMem σ I) aw6548 ByteArray.empty (cA, σ) k6548 C6548 := by
    have hfreeCallRaw := hfreeCall
    dsimp [endPackMoveCallMem, endRuntimeBlocks.endRuntime_block_6462_taken_memory] at hfreeCallRaw
    rw [hfreeOrig] at hfreeCallRaw
    dsimp [endRuntimeBlocks.endRuntime_block_6462_taken_stack,
      endRuntimeBlocks.endRuntime_block_6462_taken_memory] at rd6548
    rw [hfreeOrig] at rd6548
    rw [hfreeCallRaw] at rd6548
    rw [hend'] at rd6548
    rw [hlen'] at rd6548
    simpa [endPackMoveCallMem, endRuntimeBlocks.endRuntime_block_6462_taken_memory, hfreeOrig]
      using rd6548
  have rd6550 := endRuntimeBlocks.endRuntime_block_6548
    (x0 := UInt256.isZero (extCodeSizeWord σ (endPackVatTarget σ I)))
    (R := [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩,
      ⟨228⟩, endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel])
    (by simp) hrd6548'
  exact ⟨aw6548, _, _, by simpa [endRuntimeBlocks.endRuntime_block_6548_stack] using rd6550⟩

abbrev endPackMoveCallRest (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [⟨228⟩, endPackMoveSelectorWord, endPackVatTarget σ I, endArg0Word I, ⟨562⟩, sel]

abbrev endPackMoveCallStack (σ : AccountMap) (I : ExecutionEnv) (sel : UInt256) :
    List UInt256 :=
  [endPackVatTarget σ I, ⟨0⟩, ⟨128⟩, ⟨100⟩, ⟨128⟩, ⟨0⟩] ++
    endPackMoveCallRest σ I sel

abbrev endPackMoveCallCursor (cA : Batteries.RBSet AccountAddress compare)
    (σ : AccountMap) (I : ExecutionEnv) (sel aw : UInt256) (rdata : ByteArray) : Cursor :=
  { pc := ⟨6550⟩, stack := endPackMoveCallStack σ I sel,
    mem := endPackMoveCallMem σ I, aw := aw, rdata := rdata, world := (cA, σ) }

abbrev endPackMoveCallAw (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (MachineState.M aw.toNat (⟨128⟩ : UInt256).toNat
      (⟨100⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat)

abbrev endPackAfterMoveFrame (I : ExecutionEnv) : Frame :=
  { contract := contract, locals := (endPackAmtStore I).insert "_move" (collapseReturns []) }

abbrev endPackAfterMoveStatusCursor (σ : AccountMap) (I : ExecutionEnv)
    (sel aw : UInt256) (out : ByteArray)
    (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := ⟨6568⟩,
    stack := endRuntimeBlocks.endRuntime_block_6552_taken_stack (x0 := (⟨1⟩ : UInt256))
      (R := endPackMoveCallRest σ I sel),
    mem := endPackMoveCallMem σ I, aw := endPackMoveCallAw aw, rdata := out,
    world := world }

theorem endPackCallCopyZero (out mem : ByteArray) (off : UInt256) :
    out.write 0 mem off.toNat (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = mem := by
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
      exact Nat.zero_le _
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero]

theorem endPackMoveExternalCallRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw rdata k C evm}
    (hperm : I.perm = true) :
    BlockRefinesFrom endBytecode I g (initState cA gh bl σ σ₀ g A I) config
      (endPackMoveCallCursor cA σ I sel aw rdata)
      k C { contract := contract, locals := endPackAmtStore I } evm
      (fun cur _ e => CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e)
      [ .externalCall (.storage vatRef) "move" (.intLit 0)
          [sender, vowAddr, .var "amt"] "_move" ]
      (sequenceExit ⟨6568⟩
        (fun cur frame e =>
          frame = endPackAfterMoveFrame I ∧
          CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
          cur.stack =
            endRuntimeBlocks.endRuntime_block_6552_taken_stack (x0 := (⟨1⟩ : UInt256))
              (R := endPackMoveCallRest σ I sel) ∧
          cur.mem = endPackMoveCallMem σ I ∧
          cur.aw = endPackMoveCallAw aw)
        (runtimeExit (.abi []))) := by
  refine BlockRefinesFrom.gas
    (by change decode endBytecode ⟨6550⟩ = some (.GAS, .none); decide)
    (by simp) ?_
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0)
    (tgt := AccountAddress.ofNat (endPackVatTarget σ I).toNat)
    (argVals := [.address I.source,
      .address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
      .int (Int.ofNat (endPackMoveAmt I).toNat)])
    (hstack := fun _ => rfl) (hState := fun h => h)
    (hreceiver := ?_) (heth := ?_) (hargs := ?_) (hword := ?_) (htarget := ?_)
    (hencode := ?_) (hdec := by
      change decode endBytecode ⟨6551⟩ = some (.CALL, .none)
      decide) (hperm := hperm) (hov := by simp [endPackMoveCallRest])
    (hRevert := trivial) (hsuccess := ?_) (hfailure := ?_)
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 1)
    rw [h.env] at hload
    rw [endEvalVatAddress_pack]
    rw [h.env]
    change EvalResult.ok (Value.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 1))
        solcAddrMask).toNat)) =
        EvalResult.ok (Value.address (AccountAddress.ofNat (endPackVatTarget σ I).toNat))
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 1)) solcAddrMask]
  · intro _
    simp [evalExpr?, pure]
  · intro h
    have hload := endPackSlotLoad_eq_of_callRel h (UInt256.ofNat 4)
    rw [h.env] at hload
    rw [endEvalPackMoveArgs]
    rw [h.env]
    change EvalResult.ok
      [Value.address I.source,
        Value.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner (UInt256.ofNat 4))
            solcAddrMask).toNat),
        Value.int (Int.ofNat (endPackMoveAmt I).toNat)] =
      EvalResult.ok
        [Value.address I.source,
          Value.address (AccountAddress.ofNat (endPackVowTarget σ I).toNat),
          Value.int (Int.ofNat (endPackMoveAmt I).toNat)]
    rw [hload]
    rw [u256_land_comm (storageRead I.codeOwner σ (UInt256.ofNat 4)) solcAddrMask]
  · intro _
    decide
  · intro _
    apply Fin.ext
    show (endPackVatTarget σ I).toNat % EVM.addressModulus % AccountAddress.size =
      (endPackVatTarget σ I).val % AccountAddress.size % AccountAddress.size
    rw [show EVM.addressModulus = AccountAddress.size from by decide]
    rfl
  · intro _
    rw [endExternalEncode_move]
    change some (endPackMoveEncodedCall σ I) =
      some ((endPackMoveCallMem σ I).readWithPadding 128 100)
    rw [endPackMoveCallMem_readCallData]
  · intro out evm' world' k' C'
    dsimp only
    intro _ _
    rw [endExternalDecode_move out]
    intro rd hrel
    have rd6568 := endRuntimeBlocks.endRuntime_block_6552_taken
      (x0 := (⟨1⟩ : UInt256)) (R := endPackMoveCallRest σ I sel)
      (by simp) (by native_decide) (by jump_dest)
      (by simpa [gasCursor, callCursor, endPackCallCopyZero, endPackMoveCallStack,
        endPackMoveCallAw] using rd)
    refine ⟨.ok (endPackAfterMoveFrame I) evm',
      Endpoint.reached (endPackAfterMoveStatusCursor σ I sel aw out world'),
      ExecBlock.nil, ?_, ?_⟩
    · exact ⟨_, _, by simpa [endPackAfterMoveStatusCursor, endPackMoveCallAw] using rd6568⟩
    · exact ⟨rfl, rfl, hrel, rfl, rfl, rfl⟩
  · intro out world' k' C'
    dsimp only
    intro rd
    have rd6559 := endRuntimeBlocks.endRuntime_block_6552_fallthrough
      (x0 := (⟨0⟩ : UInt256)) (R := endPackMoveCallRest σ I sel)
      (by simp) (by native_decide)
      (by simpa [gasCursor, callCursor, endPackCallCopyZero, endPackMoveCallStack,
        endPackMoveCallAw] using rd)
    exact endRuntimeBlocks.endRuntime_block_6559
      (R := endRuntimeBlocks.endRuntime_block_6552_fallthrough_stack
        (x0 := (⟨0⟩ : UInt256)) (R := endPackMoveCallRest σ I sel))
      (by simp [endRuntimeBlocks.endRuntime_block_6552_fallthrough_stack,
        endPackMoveCallRest])
      rd6559

abbrev endPackBagSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (UInt256.ofNat 16) (UInt256.ofNat I.source.val)

abbrev endPackBagWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endPackBagSlot I)

abbrev endPackBagNewWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  endPackBagWord evm I + endArg0Word I

abbrev endPackBagWorldWord
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  storageRead I.codeOwner world.2 (endPackBagSlot I)

abbrev endPackBagWorldNewWord
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  endArg0Word I + endPackBagWorldWord world I

abbrev endPackBagStoredWorld
    (world : Batteries.RBSet AccountAddress compare × AccountMap) (I : ExecutionEnv) :
    Batteries.RBSet AccountAddress compare × AccountMap :=
  (world.1, storageWrite I.codeOwner world.2 (endPackBagSlot I)
    (endPackBagWorldNewWord world I))

abbrev endPackAddStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat (endArg0Word I).toNat))).insert "x"
    (.int (Int.ofNat (endPackBagWord evm I).toNat))

abbrev endPackAddZStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  (endPackAddStore evm I).insert "z" (.int (Int.ofNat (endPackBagNewWord evm I).toNat))

abbrev endPackAfterAddFrame (evm : EVM.State) (I : ExecutionEnv) : Frame :=
  { contract := contract,
    locals := (endPackAfterMoveFrame I).locals.insert "bagNew"
      (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) }

theorem endPackBagSlot_source (I : ExecutionEnv) :
    bagSlot (.address I.source) = endPackBagSlot I := by
  unfold bagSlot mapSlot endPackBagSlot solcMappingSlot
  rw [keyValueToWord_address]
  rw [show (⟨16⟩ : UInt256) = UInt256.ofNat 16 from by native_decide]

theorem endPackBagHashSlot (mem : ByteArray) (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 16).toByteArray.write 0
          ((UInt256.ofNat I.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = endPackBagSlot I := by
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.ofNat I.source.val) (UInt256.ofNat 16) mem) =
    endPackBagSlot I
  simp [endPackBagSlot, twoWordHashMem_keccak_solcMappingSlot_ofNat]

theorem endPackStorageLoad_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) (slot : UInt256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner slot =
      solcSlotWord σ I slot := by
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
    Account.lookupStorage, Batteries.RBMap.findD]

theorem endPackVatTarget_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) :
    UInt256.land
        (Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner ⟨1⟩)
        solcAddrMask =
      endPackVatTarget σ I := by
  rw [show (⟨1⟩ : UInt256) = UInt256.ofNat 1 by rfl]
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, Batteries.RBMap.findD, endPackVatTarget, storageRead_eq,
    u256_land_comm]

theorem endPackVatTarget_accountMapEquiv {σ τ I}
    (hστ : accountMapEquiv σ τ) :
    endPackVatTarget σ I = endPackVatTarget τ I := by
  have hVatRead :
      storageRead I.codeOwner σ (UInt256.ofNat 1) =
        storageRead I.codeOwner τ (UInt256.ofNat 1) := by
    simpa [storageRead_eq] using
      accountMapEquiv_storage_findD hστ I.codeOwner (UInt256.ofNat 1) (default : UInt256)
  unfold endPackVatTarget
  rw [hVatRead]

theorem endPackVatCodeSize_accountMapEquiv {σ τ I}
    (hστ : accountMapEquiv σ τ) :
    extCodeSizeWord σ (endPackVatTarget σ I) =
      extCodeSizeWord τ (endPackVatTarget τ I) := by
  have htarget := endPackVatTarget_accountMapEquiv (I := I) hστ
  rw [htarget]
  exact extCodeSizeWord_accountMapEquiv hστ (endPackVatTarget τ I)

theorem endPackRawSlotLoad_eq_of_callRel {s0 cA σ I evm}
    (h : CallStateRel s0 I (cA, σ) evm) (slot : UInt256) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot =
      storageRead I.codeOwner σ slot := by
  have hraw :
      Solm.EVM.storageLoad evm I.codeOwner slot = storageRead I.codeOwner σ slot := by
    simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, storageRead_eq]
      using (accountMapEquiv_storage_findD h.accounts I.codeOwner slot (default : UInt256)).symm
  rw [h.env]
  exact hraw

theorem endPackAfterMoveFrame_get_wad (I : ExecutionEnv) :
    (endPackAfterMoveFrame I).locals.get? "wad" =
      some (.int (Int.ofNat (endArg0Word I).toNat)) := by
  change (((endPackAmtStore I).insert "_move" (collapseReturns [])).get? "wad") =
    some (.int (Int.ofNat (endArg0Word I).toNat))
  rw [store_get_ne (endPackAmtStore I) (k := "_move") (a := "wad")
    (collapseReturns []) (by decide)]
  exact endPackAmtStore_get_wad I

theorem endPackAfterMoveFrame_get_bag_none (I : ExecutionEnv) :
    (endPackAfterMoveFrame I).locals.get? "bag" = none := by
  change (((endPackAmtStore I).insert "_move" (collapseReturns [])).get? "bag") = none
  rw [store_get_ne (endPackAmtStore I) (k := "_move") (a := "bag")
    (collapseReturns []) (by decide)]
  unfold endPackAmtStore
  rw [store_get_ne (endPackStore I) (k := "amt") (a := "bag")
    (.int (Int.ofNat (endPackMoveAmt I).toNat)) (by decide)]
  change (((∅ : Store).insert "wad"
    (.int (Int.ofNat (endArg0Word I).toNat))).get? "bag") = none
  rw [store_get_ne (∅ : Store) (k := "wad") (a := "bag")
    (.int (Int.ofNat (endArg0Word I).toNat)) (by decide)]
  simp

theorem endPackAddStore_get_x (evm : EVM.State) (I : ExecutionEnv) :
    (endPackAddStore evm I).get? "x" =
      some (.int (Int.ofNat (endPackBagWord evm I).toNat)) := by
  exact store_get_self ((∅ : Store).insert "y" (.int (Int.ofNat (endArg0Word I).toNat)))
    "x" (.int (Int.ofNat (endPackBagWord evm I).toNat))

theorem endPackAddStore_get_y (evm : EVM.State) (I : ExecutionEnv) :
    (endPackAddStore evm I).get? "y" =
      some (.int (Int.ofNat (endArg0Word I).toNat)) := by
  unfold endPackAddStore
  rw [store_get_ne ((∅ : Store).insert "y" (.int (Int.ofNat (endArg0Word I).toNat)))
    (k := "x") (a := "y") (.int (Int.ofNat (endPackBagWord evm I).toNat)) (by decide)]
  exact store_get_self (∅ : Store) "y" (.int (Int.ofNat (endArg0Word I).toNat))

theorem endPackAddZStore_get_z (evm : EVM.State) (I : ExecutionEnv) :
    (endPackAddZStore evm I).get? "z" =
      some (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) := by
  exact store_get_self (endPackAddStore evm I) "z"
    (.int (Int.ofNat (endPackBagNewWord evm I).toNat))

theorem endPackAddZStore_get_x (evm : EVM.State) (I : ExecutionEnv) :
    (endPackAddZStore evm I).get? "x" =
      some (.int (Int.ofNat (endPackBagWord evm I).toNat)) := by
  unfold endPackAddZStore
  rw [store_get_ne (endPackAddStore evm I) (k := "z") (a := "x")
    (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) (by decide)]
  exact endPackAddStore_get_x evm I

theorem endPackBagNew_toNat (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size) :
    (endPackBagNewWord evm I).toNat =
      (endPackBagWord evm I).toNat + (endArg0Word I).toNat := by
  unfold endPackBagNewWord
  rw [uadd_toNat, Nat.mod_eq_of_lt hfit]

theorem endPackAddSuccessCond (wad bagOld : UInt256)
    (hfit : bagOld.toNat + wad.toNat < UInt256.size) :
    UInt256.isZero (UInt256.lt (wad + bagOld) bagOld) ≠ UInt256.ofNat 0 := by
  have hfitComm : wad.toNat + bagOld.toNat < UInt256.size := by omega
  have haddNat : (wad + bagOld).toNat = wad.toNat + bagOld.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfitComm]
  have hlt : UInt256.lt (wad + bagOld) bagOld = (⟨0⟩ : UInt256) := by
    exact ult_zero (by rw [haddNat]; omega)
  rw [hlt]
  decide

theorem endPackAddFailCond (wad bagOld : UInt256)
    (hover : UInt256.size ≤ bagOld.toNat + wad.toNat) :
    UInt256.isZero (UInt256.lt (wad + bagOld) bagOld) = UInt256.ofNat 0 := by
  have hoverComm : UInt256.size ≤ wad.toNat + bagOld.toNat := by omega
  have hsum_lt2 : wad.toNat + bagOld.toNat < 2 * UInt256.size := by
    have hw : wad.toNat < UInt256.size := wad.val.isLt
    have hb : bagOld.toNat < UInt256.size := bagOld.val.isLt
    omega
  have hmod : (wad.toNat + bagOld.toNat) % UInt256.size =
      wad.toNat + bagOld.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hoverComm]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (wad + bagOld).toNat =
      wad.toNat + bagOld.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (wad + bagOld) bagOld = (⟨1⟩ : UInt256) := by
    apply ult_one
    rw [haddNat]
    have hw : wad.toNat < UInt256.size := wad.val.isLt
    omega
  rw [hlt]
  decide

theorem endEvalBagStorage_pack (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) :
    evalExpr? config (endPackAfterMoveFrame I) evm (.storage (bagRef sender)) =
      .ok (.int (Int.ofNat (endPackBagWord evm I).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := endPackAfterMoveFrame_get_bag_none I)
    (her := by
      simp [evalStorageRef, evalStorageRefStep, bagRef, sender, envValue,
        endPackAfterMoveFrame, valueToKey?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_bag (.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256, endPackBagWord, henv, endPackBagSlot_source]

theorem endEvalPackAddArgs (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) :
    evalExprs? config (endPackAfterMoveFrame I) evm
      [.storage (bagRef sender), .var "wad"] =
      .ok [.int (Int.ofNat (endPackBagWord evm I).toNat),
        .int (Int.ofNat (endArg0Word I).toNat)] := by
  rw [evalExprs?]
  rw [endEvalBagStorage_pack evm I henv]
  simp only [EvalResult.bind, bind, pure]
  rw [evalExprs?]
  rw [evalExpr?]
  rw [endPackAfterMoveFrame_get_wad I]
  simp [EvalResult.ofOption, EvalResult.bind, bind, pure, evalExprs?]

theorem endBindParams_add_pack (evm : EVM.State) (I : ExecutionEnv) :
    bindParams? addFunction.params
      [.int (Int.ofNat (endPackBagWord evm I).toNat),
        .int (Int.ofNat (endArg0Word I).toNat)] =
      some (endPackAddStore evm I) := by
  simp [bindParams?, addFunction, endPackAddStore]

theorem endEvalAddPackExpr (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endPackAddStore evm I } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .ok (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) := by
  have hsum := endPackBagNew_toNat evm I hfit
  have hfitPow : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < 2 ^ 256 := by
    simpa [UInt256.size] using hfit
  have hnotHi :
      ¬ Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) ≥
        (2 : Int) ^ (256 : Nat) := by
    rw [not_le]
    exact Int.ofNat_lt.mpr hfitPow
  have haddInt :
      Int.ofNat (endPackBagWord evm I).toNat + Int.ofNat (endArg0Word I).toNat =
        Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) := by
    exact (Nat.cast_add (endPackBagWord evm I).toNat (endArg0Word I).toNat).symm
  unfold u256
  simp only [evalExpr?, endPackAddStore_get_x, endPackAddStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int]
  rw [haddInt]
  have hcond :
      (decide (Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) < 0) ||
        decide (Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) ≥
          (2 : Int) ^ (256 : Nat))) = false := by
    have hdecNeg :
        decide (Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) < 0) =
          false :=
      decide_eq_false (show
        ¬ Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) < 0 from
        not_lt_of_ge (Int.natCast_nonneg _))
    have hdecHi :
        decide (Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) ≥
          (2 : Int) ^ (256 : Nat)) = false :=
      decide_eq_false hnotHi
    rw [hdecNeg, hdecHi]
    rfl
  rw [hcond]
  simp [hsum]

theorem endEvalAddPackExpr_revert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endPackBagWord evm I).toNat + (endArg0Word I).toNat) :
    evalExpr? config { contract := contract, locals := endPackAddStore evm I } evm
      (u256 (.binary .add (.var "x") (.var "y"))) =
      .revert := by
  have hhi :
      decide (Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) ≥
        (2 : Int) ^ (256 : Nat)) = true := by
    exact decide_eq_true (Int.ofNat_le.mpr (by simpa [UInt256.size] using hover))
  have haddInt :
      Int.ofNat (endPackBagWord evm I).toNat + Int.ofNat (endArg0Word I).toNat =
        Int.ofNat ((endPackBagWord evm I).toNat + (endArg0Word I).toNat) := by
    exact (Nat.cast_add (endPackBagWord evm I).toNat (endArg0Word I).toNat).symm
  unfold u256
  simp only [evalExpr?, endPackAddStore_get_x, endPackAddStore_get_y,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, uint256Int]
  rw [haddInt, hhi]
  simp

theorem endEvalAddPackGuard (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := endPackAddZStore evm I } evm
      (.binary .ge (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hsum := endPackBagNew_toNat evm I hfit
  have hgeProp :
      Int.ofNat (endPackBagWord evm I).toNat ≤
        Int.ofNat (endPackBagNewWord evm I).toNat := by
    rw [hsum]
    exact Int.ofNat_le.mpr (by omega)
  have hge :
      decide (Int.ofNat (endPackBagNewWord evm I).toNat ≥
        Int.ofNat (endPackBagWord evm I).toNat) = true := by
    exact decide_eq_true hgeProp
  simp only [evalExpr?, endPackAddZStore_get_z, endPackAddZStore_get_x,
    EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp?]
  rw [hge]

theorem endAddPackFunctionOk (evm : EVM.State) (I : ExecutionEnv)
    (hfit : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endPackAddStore evm I } evm
      addFunction.body
      (.returned { contract := contract, locals := endPackAddZStore evm I } evm
        (some [.int (Int.ofNat (endPackBagNewWord evm I).toNat)])) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [addFunction, endPackAddZStore] using
    (ExecBlock.consNormal
      (ExecStmt.letDecl
        (name := "z") (ty := some uint256)
        (expr := u256 (.binary .add (.var "x") (.var "y")))
        (value := .int (Int.ofNat (endPackBagNewWord evm I).toNat))
        (endEvalAddPackExpr evm I hfit)) <|
      ExecBlock.consNormal
        (ExecStmt.requireTrue (endEvalAddPackGuard evm I hfit)) <|
      ExecBlock.consReturn (stmts := [])
        (ExecStmt.return
          (exprs := [.var "z"])
          (values := [.int (Int.ofNat (endPackBagNewWord evm I).toNat)])
          (by
            simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
              endPackAddZStore_get_z])))

theorem endAddPackFunctionRevert (evm : EVM.State) (I : ExecutionEnv)
    (hover : UInt256.size ≤ (endPackBagWord evm I).toNat + (endArg0Word I).toNat) :
    ExecFuncBody config { contract := contract, locals := endPackAddStore evm I } evm
      addFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [addFunction] using
    (ExecBlock.consRevert
      (ExecStmt.letDeclRevert (endEvalAddPackExpr_revert evm I hover)))

theorem endPackInternalAddOk (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hfit : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size) :
    ExecStmt config (endPackAfterMoveFrame I) evm
      (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew")
      (.ok (endPackAfterAddFrame evm I) evm) := by
  simpa [resumeAfterInternalCall, collapseReturns, endPackAfterAddFrame] using
    internalCallFunctionReturn
      (cfg := config) (caller := endPackAfterMoveFrame I)
      (evm := evm) (calleeEvm := evm) (name := "add") (retVar := "bagNew")
      (args := [.storage (bagRef sender), .var "wad"])
      (argVals := [.int (Int.ofNat (endPackBagWord evm I).toNat),
        .int (Int.ofNat (endArg0Word I).toNat)])
      (callee := addFunction) (locals := endPackAddStore evm I)
      (calleeSolm := { contract := contract, locals := endPackAddZStore evm I })
      (value := some [.int (Int.ofNat (endPackBagNewWord evm I).toNat)])
      (endEvalPackAddArgs evm I henv)
      (by
        change lookupCallable? contract "add" = some addFunction.toCallable
        rfl)
      (endBindParams_add_pack evm I)
      (endAddPackFunctionOk evm I hfit)

theorem endPackInternalAddRevert (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hover : UInt256.size ≤ (endPackBagWord evm I).toNat + (endArg0Word I).toNat) :
    ExecStmt config (endPackAfterMoveFrame I) evm
      (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew") .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := endPackAfterMoveFrame I) (evm := evm)
    (name := "add") (retVar := "bagNew")
    (args := [.storage (bagRef sender), .var "wad"])
    (argVals := [.int (Int.ofNat (endPackBagWord evm I).toNat),
      .int (Int.ofNat (endArg0Word I).toNat)])
    (callee := addFunction) (locals := endPackAddStore evm I)
    (endEvalPackAddArgs evm I henv)
    (by
      change lookupCallable? contract "add" = some addFunction.toCallable
      rfl)
    (endBindParams_add_pack evm I)
    (endAddPackFunctionRevert evm I hover)

theorem endPackAfterAddFrame_get_bagNew (evm : EVM.State) (I : ExecutionEnv) :
    (endPackAfterAddFrame evm I).locals.get? "bagNew" =
      some (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) := by
  exact store_get_self (endPackAfterMoveFrame I).locals "bagNew"
    (.int (Int.ofNat (endPackBagNewWord evm I).toNat))

theorem endEvalBagNew_pack (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config (endPackAfterAddFrame evm I) evm (.var "bagNew") =
      .ok (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) := by
  simp [evalExpr?, EvalResult.ofOption, endPackAfterAddFrame_get_bagNew]

theorem endAssignBagNew_pack (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I) :
    assignStorageRef? config (endPackAfterAddFrame evm I) evm
        .storage (bagRef sender) (.int (Int.ofNat (endPackBagNewWord evm I).toNat)) =
      .ok (endPackAfterAddFrame evm I,
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (endPackBagSlot I) (endPackBagNewWord evm I)) := by
  rw [assignStorageRef_storage_scalar
    (slot := bagRef sender)
    (er := { base := "bag", steps := [.mindex (.address evm.executionEnv.source)] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (bagSlot (.address evm.executionEnv.source)))
    (n := Int.ofNat (endPackBagNewWord evm I).toNat)
    (hbase := by
      simp [endPackAfterAddFrame, endPackAfterMoveFrame, endPackAmtStore, endPackStore, bagRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, bagRef, sender, envValue,
        endPackAfterAddFrame, endPackAfterMoveFrame, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_bag (.address evm.executionEnv.source))
    (hstore := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm (bagSlot (.address evm.executionEnv.source))
          (endPackBagNewWord evm I))]
  rw [henv, endPackBagSlot_source I]

theorem endPackAfterMoveSuffixOk (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hfit : (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size) :
    ExecBlock config (endPackAfterMoveFrame I) evm
      [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
        .assign .storage (bagRef sender) (.var "bagNew") ]
      (.ok (endPackAfterAddFrame evm I)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (endPackBagSlot I) (endPackBagNewWord evm I))) := by
  exact ExecBlock.consNormal (endPackInternalAddOk evm I henv hfit) <|
    ExecBlock.consNormal
      (ExecStmt.assign (endEvalBagNew_pack evm I) (endAssignBagNew_pack evm I henv))
      ExecBlock.nil

theorem endPackAfterMoveSuffixRevert (evm : EVM.State) (I : ExecutionEnv)
    (henv : evm.executionEnv = I)
    (hover : UInt256.size ≤ (endPackBagWord evm I).toNat + (endArg0Word I).toNat) :
    ExecBlock config (endPackAfterMoveFrame I) evm
      [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
        .assign .storage (bagRef sender) (.var "bagNew") ]
      .reverted := by
  exact ExecBlock.consRevert (endPackInternalAddRevert evm I henv hover)

theorem endX_pack_after_move_success {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (hfit : (endPackBagWorldWord world I).toNat + (endArg0Word I).toNat < UInt256.size)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6568⟩
      (endRuntimeBlocks.endRuntime_block_6552_taken_stack (x0 := (⟨1⟩ : UInt256))
        (R := endPackMoveCallRest preσ I sel))
      (endPackMoveCallMem preσ I) aw rdata world k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (endPackBagStoredWorld world I) ByteArray.empty := by
  obtain ⟨k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_6568
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨228⟩ : UInt256))
      (x2 := endPackMoveSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endPackMoveCallRest] using rd)
  have rd10092' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
        [endArg0Word I, endPackBagWorldWord world I, ⟨6599⟩,
          endArg0Word I, ⟨562⟩, sel]
        (endRuntimeBlocks.endRuntime_block_6568_memory
          (ee := I) (mem := endPackMoveCallMem preσ I))
        (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256))
          (UInt256.ofNat 32) (⟨32⟩ : UInt256))
          (UInt256.ofNat 0) (UInt256.ofNat 64))
        rdata world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_6568_stack, endPackMoveCallRest,
      endPackBagWorldWord, endPackBagHashSlot] using rd10092
  have hcond := endPackAddSuccessCond (endArg0Word I) (endPackBagWorldWord world I) hfit
  have rd10108 := endRuntimeBlocks.endRuntime_block_10092_taken
    (cA := world.1) (σ := world.2)
    (x0 := endArg0Word I) (x1 := endPackBagWorldWord world I)
    (R := [⟨6599⟩, endArg0Word I, ⟨562⟩, sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    hcond (by jump_dest) rd10092'
  have rd6599 := endRuntimeBlocks.endRuntime_block_10108
    (cA := world.1) (σ := world.2)
    (x0 := endArg0Word I + endPackBagWorldWord world I)
    (x1 := endArg0Word I) (x2 := endPackBagWorldWord world I)
    (x3 := (⟨6599⟩ : UInt256)) (R := [endArg0Word I, ⟨562⟩, sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    (by jump_dest)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_10092_taken_stack] using rd10108)
  obtain ⟨k562, C562, rd562⟩ := endRuntimeBlocks.endRuntime_block_6599
    (cA := world.1) (σ := world.2)
    (x0 := endPackBagWorldNewWord world I) (x1 := endArg0Word I)
    (x2 := (⟨562⟩ : UInt256)) (R := [sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    hperm (by jump_dest)
    (by
      simpa [endPackBagWorldNewWord, u256_add_comm,
        endRuntimeBlocks.endRuntime_block_10108_stack] using rd6599)
  have rd562' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨562⟩ [sel]
        (endRuntimeBlocks.endRuntime_block_6599_memory
          (ee := I)
          (mem := endRuntimeBlocks.endRuntime_block_6568_memory
            (ee := I) (mem := endPackMoveCallMem preσ I))
          (x1 := endArg0Word I))
        (M (M (M (M (M (M (M
          (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256))
            (UInt256.ofNat 32) (⟨32⟩ : UInt256))
            (UInt256.ofNat 0) (UInt256.ofNat 64))
          (UInt256.ofNat 0) (⟨32⟩ : UInt256))
          (UInt256.ofNat 32) (⟨32⟩ : UInt256))
          (UInt256.ofNat 0) (UInt256.ofNat 64))
          (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          (memLoad (UInt256.ofNat 64)
            ((UInt256.ofNat 16).toByteArray.write 0
              ((UInt256.ofNat I.source.val).toByteArray.write 0
                (endRuntimeBlocks.endRuntime_block_6568_memory
                  (ee := I) (mem := endPackMoveCallMem preσ I))
                (UInt256.ofNat 0).toNat 32)
              (UInt256.ofNat 32).toNat 32))
            (⟨32⟩ : UInt256))
          (UInt256.ofNat 64) (⟨32⟩ : UInt256))
          (memLoad (UInt256.ofNat 64)
            (endRuntimeBlocks.endRuntime_block_6599_memory
              (ee := I)
              (mem := endRuntimeBlocks.endRuntime_block_6568_memory
                (ee := I) (mem := endPackMoveCallMem preσ I))
              (x1 := endArg0Word I)))
            ((UInt256.sub
              (memLoad (UInt256.ofNat 64)
                ((UInt256.ofNat 16).toByteArray.write 0
                  ((UInt256.ofNat I.source.val).toByteArray.write 0
                    (endRuntimeBlocks.endRuntime_block_6568_memory
                      (ee := I) (mem := endPackMoveCallMem preσ I))
                    (UInt256.ofNat 0).toNat 32)
                  (UInt256.ofNat 32).toNat 32))
              (memLoad (UInt256.ofNat 64)
                (endRuntimeBlocks.endRuntime_block_6599_memory
                  (ee := I)
                  (mem := endRuntimeBlocks.endRuntime_block_6568_memory
                    (ee := I) (mem := endPackMoveCallMem preσ I))
                  (x1 := endArg0Word I)))) + (UInt256.ofNat 32)))
        rdata (endPackBagStoredWorld world I) k562 C562 := by
    simpa [endPackBagStoredWorld, endPackBagWorldNewWord, endPackBagHashSlot,
      endRuntimeBlocks.endRuntime_block_6599_stack] using rd562
  exact endRuntimeBlocks.endRuntime_block_562
    (cA := (endPackBagStoredWorld world I).1)
    (σ := (endPackBagStoredWorld world I).2)
    (R := [sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    rd562'

theorem endX_pack_after_move_add_fail {cA gh bl σ σ₀ A I} {g : Sat256}
    {preσ : AccountMap} {sel aw rdata k C}
    {world : Batteries.RBSet AccountAddress compare × AccountMap}
    (hover : UInt256.size ≤ (endPackBagWorldWord world I).toNat + (endArg0Word I).toNat)
    (rd : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨6568⟩
      (endRuntimeBlocks.endRuntime_block_6552_taken_stack (x0 := (⟨1⟩ : UInt256))
        (R := endPackMoveCallRest preσ I sel))
      (endPackMoveCallMem preσ I) aw rdata world k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k10092, C10092, rd10092⟩ :=
    endRuntimeBlocks.endRuntime_block_6568
      (cA := world.1) (σ := world.2)
      (x0 := UInt256.isZero (⟨1⟩ : UInt256)) (x1 := (⟨228⟩ : UInt256))
      (x2 := endPackMoveSelectorWord) (x3 := endPackVatTarget preσ I)
      (x4 := endArg0Word I) (R := [⟨562⟩, sel])
      (by
        simp only [List.length_cons, List.length_nil]
        omega)
      (by jump_dest)
      (by
        simpa [endPackMoveCallRest] using rd)
  have rd10092' :
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
        [endArg0Word I, endPackBagWorldWord world I, ⟨6599⟩,
          endArg0Word I, ⟨562⟩, sel]
        (endRuntimeBlocks.endRuntime_block_6568_memory
          (ee := I) (mem := endPackMoveCallMem preσ I))
        (M (M (M aw (UInt256.ofNat 0) (⟨32⟩ : UInt256))
          (UInt256.ofNat 32) (⟨32⟩ : UInt256))
          (UInt256.ofNat 0) (UInt256.ofNat 64))
        rdata world k10092 C10092 := by
    simpa [endRuntimeBlocks.endRuntime_block_6568_stack, endPackMoveCallRest,
      endPackBagWorldWord, endPackBagHashSlot] using rd10092
  have hcond := endPackAddFailCond (endArg0Word I) (endPackBagWorldWord world I) hover
  have rd10104 := endRuntimeBlocks.endRuntime_block_10092_fallthrough
    (cA := world.1) (σ := world.2)
    (x0 := endArg0Word I) (x1 := endPackBagWorldWord world I)
    (R := [⟨6599⟩, endArg0Word I, ⟨562⟩, sel])
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    hcond rd10092'
  exact endRuntimeBlocks.endRuntime_block_10104
    (cA := world.1) (σ := world.2)
    (R := endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack
      (x0 := endArg0Word I) (x1 := endPackBagWorldWord world I)
      (R := [⟨6599⟩, endArg0Word I, ⟨562⟩, sel]))
    (by
      simp [endRuntimeBlocks.endRuntime_block_10092_fallthrough_stack])
    rd10104

theorem endPackAfterMoveSuffixRefines {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel aw : UInt256}
    (hperm : I.perm = true) :
    StmtsRefine endBytecode I g (initState cA gh bl σ σ₀ g A I) config ⟨6568⟩
      (fun cur frame e =>
        frame = endPackAfterMoveFrame I ∧
        CallStateRel (initState cA gh bl σ σ₀ g A I) I cur.world e ∧
        cur.stack =
          endRuntimeBlocks.endRuntime_block_6552_taken_stack (x0 := (⟨1⟩ : UInt256))
            (R := endPackMoveCallRest σ I sel) ∧
        cur.mem = endPackMoveCallMem σ I ∧
        cur.aw = endPackMoveCallAw aw)
      [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
        .assign .storage (bagRef sender) (.var "bagNew") ]
      (runtimeExit (.abi [])) := by
  intro cur k C frame evm hpc rd hP
  rcases hP with ⟨hframe, hrel, hstack, hmem, _haw⟩
  cases hframe
  have hbagEq :
      endPackBagWord evm I = endPackBagWorldWord cur.world I :=
    endPackRawSlotLoad_eq_of_callRel hrel (endPackBagSlot I)
  by_cases hfit :
      (endPackBagWorldWord cur.world I).toNat + (endArg0Word I).toNat < UInt256.size
  · have hfitSource :
        (endPackBagWord evm I).toNat + (endArg0Word I).toNat < UInt256.size := by
      simpa [hbagEq] using hfit
    have hsource := endPackAfterMoveSuffixOk evm I hrel.env hfitSource
    have rdret := endX_pack_after_move_success
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := σ) (sel := sel) (aw := cur.aw)
      (rdata := cur.rdata) (k := k) (C := C) (world := cur.world)
      hperm hfit
      (by
        simpa [hpc, hstack, hmem] using rd)
    have hvalue :
        endPackBagWorldNewWord cur.world I = endPackBagNewWord evm I := by
      simp [endPackBagWorldNewWord, endPackBagWorldWord, endPackBagNewWord, hbagEq,
        u256_add_comm]
    have hstored :=
      hrel.storageStore_codeOwner (endPackBagSlot I) (endPackBagNewWord evm I)
    exact BlockProgress.ofRDret hsource rdret
      (by
        simpa [endPackBagStoredWorld] using hstored.created.symm)
      (by
        simpa [endPackBagStoredWorld, storageWrite, hvalue] using hstored.accounts)
      abiVoidFallthrough
  · have hoverWorld :
        UInt256.size ≤ (endPackBagWorldWord cur.world I).toNat + (endArg0Word I).toNat := by
      omega
    have hoverSource :
        UInt256.size ≤ (endPackBagWord evm I).toNat + (endArg0Word I).toNat := by
      simpa [hbagEq] using hoverWorld
    have hsource := endPackAfterMoveSuffixRevert evm I hrel.env hoverSource
    have hrev := endX_pack_after_move_add_fail
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (preσ := σ) (sel := sel) (aw := cur.aw)
      (rdata := cur.rdata) (k := k) (C := C) (world := cur.world)
      hoverWorld
      (by
        simpa [hpc, hstack, hmem] using rd)
    exact BlockProgress.ofRDrev hsource hrev

theorem endPackBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 30))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨806⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 30 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some packTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 30 (by omega) hsel
  have hdispatchSel : selectorDispatchMsg contract I.calldata = some packTransition := by
    rw [selectorDispatchMsg_eq_dispatchList]
    have hdList := hd
    rw [dispatchMsg_eq_dispatchList contract I.calldata] at hdList
    simpa [endTransitionAt, transitions] using hdList
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (packTransition.params.map Param.name) (transitionSignature packTransition).paramTypes
        I.calldata = some (endPackStore I) := by
      simpa [config, packTransition, transitionSignature, uint256] using
        endDecode_legacyUint_wad_ok (I := I) hsz36
    have hDebtWord :
        solcSlotWord σ_evm I ⟨11⟩ = solcSlotWord σ_solm I ⟨11⟩ :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
    by_cases hdebtSolm : solcSlotWord σ_solm I ⟨11⟩ = ⟨0⟩
    · have hdebtEvm : solcSlotWord σ_evm I ⟨11⟩ = ⟨0⟩ :=
        hDebtWord.trans hdebtSolm
      have hdebtSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨11⟩ = ⟨0⟩ := by
        rw [endPackStorageLoad_init_eq]
        exact hdebtSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endPackStore I) packTransition.body .reverted := by
        simpa [initState] using
          endPackBodyDebtFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hdebtSrc
      exact (endX_pack_debt_fail (g := Sat256.ofUInt256 g) hsz36 hsize hdebtEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
    · have hdebtEvm : solcSlotWord σ_evm I ⟨11⟩ ≠ ⟨0⟩ := by
        intro hbad
        exact hdebtSolm (hDebtWord.symm.trans hbad)
      have hdebtSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner ⟨11⟩ ≠ ⟨0⟩ := by
        rw [endPackStorageLoad_init_eq]
        exact hdebtSolm
      by_cases hmulFit : (endArg0Word I).toNat * endRayNat < UInt256.size
      · have hCodeEq :
            extCodeSizeWord σ_evm (endPackVatTarget σ_evm I) =
              extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) :=
          endPackVatCodeSize_accountMapEquiv (I := I) hAccounts
        by_cases hvatNoCodeEvm :
            extCodeSizeWord σ_evm (endPackVatTarget σ_evm I) = ⟨0⟩
        · have hvatNoCodeSolm :
              extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) = ⟨0⟩ :=
            hCodeEq.symm.trans hvatNoCodeEvm
          have hvatNoCodeSrc :
              extCodeSizeWord
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
                (UInt256.land
                  (Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    ⟨1⟩)
                  solcAddrMask) = ⟨0⟩ := by
            rw [endPackVatTarget_init_eq]
            simpa [initState] using hvatNoCodeSolm
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (endPackStore I) packTransition.body .reverted := by
            simpa [initState] using
              endPackBodyVatNoCode
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simp only [initState]; exact hwv) hdebtSrc hmulFit hvatNoCodeSrc
          exact (endX_pack_vat_no_code (g := Sat256.ofUInt256 g) hsz36 hsize
              hdebtEvm hmulFit hvatNoCodeEvm hreach)
            |>.reEquivExecutionRevert hcode hd hdec hbody
        · have hvatCodeSolm :
              extCodeSizeWord σ_solm (endPackVatTarget σ_solm I) ≠ ⟨0⟩ := by
            intro hzero
            exact hvatNoCodeEvm (hCodeEq.trans hzero)
          have hvatCodeSrc :
              extCodeSizeWord
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap
                (UInt256.land
                  (Solm.EVM.storageLoad
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
                    ⟨1⟩)
                  solcAddrMask) ≠ ⟨0⟩ := by
            rw [endPackVatTarget_init_eq]
            simpa [initState] using hvatCodeSolm
          obtain ⟨awCall, kCall, CCall, rdCall⟩ :=
            endX_pack_to_move_call (g := Sat256.ofUInt256 g)
              hsz36 hsize hdebtEvm hmulFit hvatNoCodeEvm hreach
          have hprefix :
              ExecBlock config { contract := contract, locals := endPackStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (nonpayable ++
                  [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
                    .internalCall "mul" [.var "wad", .intLit RAY] "amt",
                    .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ])
                (.ok { contract := contract, locals := endPackAmtStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) :=
            endPackBodyPrefixOk
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hdebtSrc hmulFit hvatCodeSrc
          have hpostRel :
              CallStateRel
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) I
                (cA, σ_evm)
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) :=
            CallStateRel.initState hAccounts
          have htail :
              BlockRefinesFrom endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) config
                (endPackMoveCallCursor cA σ_evm I sel awCall ByteArray.empty)
                kCall CCall { contract := contract, locals := endPackAmtStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (fun cur _ e =>
                  CallStateRel
                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                    I cur.world e)
                ([ .externalCall (.storage vatRef) "move" (.intLit 0)
                    [sender, vowAddr, .var "amt"] "_move" ] ++
                  [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
                    .assign .storage (bagRef sender) (.var "bagNew") ])
                (runtimeExit (.abi [])) := by
            refine BlockRefinesFrom.seqOrExit
              (endPackMoveExternalCallRefines
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
                (aw := awCall) (rdata := ByteArray.empty) (k := kCall)
                (C := CCall)
                (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                hperm) ?_
            exact endPackAfterMoveSuffixRefines
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := sel)
              (aw := awCall) hperm
          have hprogress :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endPackStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                ((nonpayable ++
                  [ .require (.binary .ne (.storage debtRef) (.intLit 0)),
                    .internalCall "mul" [.var "wad", .intLit RAY] "amt",
                    .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) ]) ++
                  ([ .externalCall (.storage vatRef) "move" (.intLit 0)
                      [sender, vowAddr, .var "amt"] "_move" ] ++
                    [ .internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew",
                      .assign .storage (bagRef sender) (.var "bagNew") ]))
                (runtimeExit (.abi [])) :=
            BlockProgress.seqOfRD
              (R := fun cur _ e =>
                CallStateRel
                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                  I cur.world e)
              hprefix
              (by
                simpa [endPackMoveCallCursor] using rdCall)
              hpostRel
              htail
          have hprogressBody :
              BlockProgress endBytecode I (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                config { contract := contract, locals := endPackStore I }
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                packTransition.body (runtimeExit (.abi [])) := by
            simpa [packTransition, checkedExternalCallStmts, List.append_assoc] using hprogress
          simpa [Sat256.ofUInt256, Sat256.toUInt256] using
            (hprogressBody.toRuntimeEquivalenceFor hcode
              (convention := .abi [])
              (by
                intro result hfunc
                exact solmExec.intro hdispatchSel rfl hdec
                  (by simp [initState, Sat256.ofUInt256, Sat256.toUInt256]) hfunc)
              (by
                intro result endpoint h
                exact h))
      · have hmulOverflow : UInt256.size ≤ (endArg0Word I).toNat * endRayNat := by
          omega
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (endPackStore I) packTransition.body .reverted := by
          simpa [initState] using
            endPackBodyMulFail
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) hdebtSrc hmulOverflow
        exact (endX_pack_mul_fail (g := Sat256.ofUInt256 g) hsz36 hsize
            hdebtEvm hmulOverflow hreach)
          |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (packTransition.params.map Param.name) (transitionSignature packTransition).paramTypes
        I.calldata = none := by
      simpa [config, packTransition, transitionSignature, uint256] using
        endDecode_legacyUint_wad_none_short (I := I) hsz4 hshort
    exact (endX_pack_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
