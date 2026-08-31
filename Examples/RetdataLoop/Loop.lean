import Examples.RetdataLoop.Spec
import Reasoning.ABI
import Reasoning.Reach
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory

namespace RetdataLoop

/-!
This file isolates the Reveal-style coupled loop step for `RetdataLoop.collect`.

The theorem below is intentionally bytecode-parametric: it fixes the Solm loop condition, post
statement, and body, proves the source guard obligations from a small invariant shape, and leaves
the bytecode routing/body obligations to the runtime proof.
-/

def collectLoopCond : Expr :=
  ltE (.var "i") (.var "n")

def collectLoopPost : List Stmt :=
  [ .assign .localVar (varRef "i") (u256 (addE (.var "i") (.intLit 1))) ]

def collectLoopBody : List Stmt :=
  [ .lowLevelCall
      (arrGet "targets" (.var "i"))
      (.intLit 0)
      collectCalldataExpr
      "ok"
      "returndata",
    .require (.var "ok"),
    .require (eqE (localLength "returndata") (.intLit 32)),
    .letDecl "value" (some uint256) decodeReturndataExpr,
    .assign .localVar (varRef "total") (u256 (addE (.var "total") (.var "value"))) ]

private theorem evalExpr_var_value {cfg : Config} {C : ContractDecl}
    (evm : EVM.State) (locals : Store) (name : Ident) (v : Value)
    (h : locals.get? name = some v) :
    evalExpr? cfg { contract := C, locals := locals } evm (.var name) = .ok v := by
  rw [evalExpr?]
  change EvalResult.ofOption .unboundVariable (locals.get? name) = .ok v
  rw [h]
  rfl

private theorem evalExpr_var_int {cfg : Config} {C : ContractDecl}
    (evm : EVM.State) (locals : Store) (name : Ident) (n : Int)
    (h : locals.get? name = some (.int n)) :
    evalExpr? cfg { contract := C, locals := locals } evm (.var name) = .ok (.int n) :=
  evalExpr_var_value evm locals name (.int n) h

theorem evalTargetsIndex_of_get {locals : Store} {evm : EVM.State}
    (targets : List Value) (idx : UInt256) (rawVal target : Value)
    (harr : locals.get? "targets" = some (.array targets))
    (hi : locals.get? "i" = some (.int (Int.ofNat idx.toNat)))
    (hbound : idx.toNat < targets.length)
    (hlookup : lookupNth? targets idx.toNat = some rawVal)
    (hnorm : normalizeRawBoolWord? rawVal = .ok target) :
    evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
      (arrGet "targets" (.var "i")) = .ok target := by
  unfold arrGet
  rw [evalExpr?]
  simp only [
    evalExpr_var_value (cfg := retdataLoopConfig) (C := contract)
      evm locals "targets" (.array targets) harr,
    evalExpr_var_int (cfg := retdataLoopConfig) (C := contract)
      evm locals "i" (Int.ofNat idx.toNat) hi,
    EvalResult.bind, bind]
  unfold evalIndex?
  change
    (if 0 ≤ Int.ofNat idx.toNat ∧ Int.ofNat idx.toNat < targets.length then
      match lookupNth? targets (Int.ofNat idx.toNat).toNat with
      | some v => normalizeRawBoolWord? v
      | none => .error .typeError
    else .revert) = .ok target
  rw [if_pos]
  · simp [hlookup, hnorm]
  · constructor
    · exact Int.natCast_nonneg idx.toNat
    · have hb : (idx.toNat : Int) < (targets.length : Int) := by
        exact_mod_cast hbound
      simpa using hb

theorem evalCollectLoopCond_true_of_get (evm : EVM.State) (locals : Store)
    (n i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hn : locals.get? "n" = some (.int (Int.ofNat n.toNat)))
    (hbound : i.toNat < n.toNat) :
    evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopCond = .ok (.bool true) := by
  unfold collectLoopCond ltE
  rw [evalExpr?]
  simp only [
    evalExpr_var_int (cfg := retdataLoopConfig) (C := contract)
      evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr_var_int (cfg := retdataLoopConfig) (C := contract)
      evm locals "n" (Int.ofNat n.toNat) hn,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound
  all_goals decide

theorem evalCollectLoopCond_false_of_get (evm : EVM.State) (locals : Store)
    (n i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hn : locals.get? "n" = some (.int (Int.ofNat n.toNat)))
    (hbound : n.toNat ≤ i.toNat) :
    evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopCond = .ok (.bool false) := by
  unfold collectLoopCond ltE
  rw [evalExpr?]
  simp only [
    evalExpr_var_int (cfg := retdataLoopConfig) (C := contract)
      evm locals "i" (Int.ofNat i.toNat) hi,
    evalExpr_var_int (cfg := retdataLoopConfig) (C := contract)
      evm locals "n" (Int.ofNat n.toNat) hn,
    EvalResult.bind, bind]
  simp [evalBinaryOp?]
  exact hbound
  all_goals decide

def collectCallLocals (locals : Store) (out : ByteArray) : Store :=
  (locals.insert "ok" (.bool true)).insert "returndata" (.bytes out)

def collectCallFailureLocals (locals : Store) (out : ByteArray) : Store :=
  (locals.insert "ok" (.bool false)).insert "returndata" (.bytes out)

def collectValueLocals (locals : Store) (out : ByteArray) (value : UInt256) : Store :=
  (collectCallLocals locals out).insert "value" (.int (Int.ofNat value.toNat))

theorem evalDecodeReturndata_uint256_ok {locals : Store} {evm : EVM.State}
    {out : ByteArray} (hlo : 32 ≤ out.size) (hhi : out.size < (2 : Nat) ^ 255) :
    evalExpr? retdataLoopConfig
      { contract := contract, locals := collectCallLocals locals out } evm
      decodeReturndataExpr =
        .ok (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
  have hdec :
      ABI.decodeReturnValueWithMode? retdataLoopConfig.abiDecodeMode uint256 out =
        some (.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))) := by
    simpa [retdataLoopConfig, uint256] using
      Reasoning.Theory.decodeReturnValue_uint256_ok (returndata := out) hlo hhi
  unfold decodeReturndataExpr collectCallLocals
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rw [Reasoning.Theory.store_get_self]
  simp
  rw [hdec]
  rfl

theorem evalReturndataLength_eq_32_of_size {locals : Store} {evm : EVM.State}
    {out : ByteArray} (hout : out.size = 32) :
    evalExpr? retdataLoopConfig
      { contract := contract, locals := collectCallLocals locals out } evm
      (eqE (localLength "returndata") (.intLit 32)) = .ok (.bool true) := by
  unfold collectCallLocals eqE localLength varRef
  simp only [evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  rw [Reasoning.Theory.store_get_self]
  simp [evalBinaryOp?, hout]

theorem evalReturndataLength_ne_32_of_size_ne {locals : Store} {evm : EVM.State}
    {out : ByteArray} (hne : out.size ≠ 32) :
    evalExpr? retdataLoopConfig
      { contract := contract, locals := collectCallLocals locals out } evm
      (eqE (localLength "returndata") (.intLit 32)) = .ok (.bool false) := by
  unfold collectCallLocals eqE localLength varRef
  simp only [evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  rw [Reasoning.Theory.store_get_self]
  have hneInt : ¬ ((out.size : Int) = 32) := by
    intro h
    apply hne
    exact_mod_cast h
  simp [evalBinaryOp?, hneInt]

theorem evalCollectTotalAdd_of_get {locals : Store} {evm : EVM.State}
    (total value : UInt256)
    (htotal : locals.get? "total" = some (.int (Int.ofNat total.toNat)))
    (hfit : total.toNat + value.toNat < UInt256.size) :
    evalExpr? retdataLoopConfig
      { contract := contract, locals := collectValueLocals locals out value } evm
      (u256 (addE (.var "total") (.var "value"))) =
        .ok (.int (Int.ofNat (total.toNat + value.toNat))) := by
  unfold collectValueLocals collectCallLocals u256 addE
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_ne,
      Reasoning.Theory.store_get_ne, htotal]
  · simp only [EvalResult.ofOption, evalBinaryOp?]
    have hnonneg : ¬ ((Int.ofNat total.toNat + Int.ofNat value.toNat : Int) < 0) := by
      have ht0 : (0 : Int) ≤ Int.ofNat total.toNat := Int.natCast_nonneg _
      have hv0 : (0 : Int) ≤ Int.ofNat value.toNat := Int.natCast_nonneg _
      omega
    have hlt : (Int.ofNat total.toNat + Int.ofNat value.toNat : Int) < 2 ^ (256 : Nat) := by
      have hfit' : total.toNat + value.toNat < 2 ^ (256 : Nat) := by
        simpa [UInt256.size] using hfit
      have hfitCast :
          ((total.toNat + value.toNat : Nat) : Int) < ((2 ^ (256 : Nat) : Nat) : Int) := by
        exact_mod_cast hfit'
      simpa [Nat.cast_add] using hfitCast
    simp [uint256Int]
    exact ⟨by omega, by simpa using hlt⟩
  · decide
  · decide
  · decide

theorem evalCollectTotalAdd_revert_of_get {locals : Store} {evm : EVM.State}
    (total value : UInt256)
    (htotal : locals.get? "total" = some (.int (Int.ofNat total.toNat)))
    (hover : UInt256.size ≤ total.toNat + value.toNat) :
    evalExpr? retdataLoopConfig
      { contract := contract, locals := collectValueLocals locals out value } evm
      (u256 (addE (.var "total") (.var "value"))) =
        .revert := by
  unfold collectValueLocals collectCallLocals u256 addE
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_ne,
      Reasoning.Theory.store_get_ne, htotal]
  · simp only [EvalResult.ofOption, evalBinaryOp?]
    have hge : (2 : Int) ^ 256 ≤
        (Int.ofNat total.toNat + Int.ofNat value.toNat) := by
      have hover' : (2 : Nat) ^ 256 ≤ total.toNat + value.toNat := by
        simpa [UInt256.size] using hover
      have hcast :
          ((2 : Nat) ^ 256 : Int) ≤
            ((total.toNat + value.toNat : Nat) : Int) := by
        exact_mod_cast hover'
      simpa [Nat.cast_add] using hcast
    have hif :
        Int.ofNat total.toNat + Int.ofNat value.toNat < 0 ∨
          (2 : Int) ^ 256 ≤ Int.ofNat total.toNat + Int.ofNat value.toNat := by
      exact Or.inr hge
    simp [uint256Int]
    intro _hnonneg
    norm_num at hge ⊢
    exact hge
  · decide
  · decide
  · decide

theorem assignCollectTotal_local {locals : Store} {evm : EVM.State}
    (out : ByteArray) (value newTotal total : UInt256)
    (htotal : locals.get? "total" = some (.int (Int.ofNat total.toNat))) :
    assignStorageRef? retdataLoopConfig
      { contract := contract, locals := collectValueLocals locals out value } evm
      .localVar (varRef "total") (.int (Int.ofNat newTotal.toNat)) =
        .ok
          ({ contract := contract,
             locals := (collectValueLocals locals out value).insert "total"
                (.int (Int.ofNat newTotal.toNat)) }, evm) := by
  unfold assignStorageRef? varRef
  simp [updateLocalPath?]
  unfold collectValueLocals collectCallLocals
  rw [← Std.HashMap.get?_eq_getElem?]
  rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_ne,
      Reasoning.Theory.store_get_ne, htotal]
  · rfl
  · decide
  · decide
  · decide

theorem collectLoopBody_success_of_eval_assign {locals locals' : Store}
    {evm evm' : EVM.State} {target : AccountAddress} {calldata out : ByteArray}
    {value newTotal : UInt256}
    (hreceiver :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        (arrGet "targets" (.var "i")) = .ok (.address target))
    (hdata :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        collectCalldataExpr = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) 0 calldata (true, evm', out))
    (hout : out.size = 32)
    (hdecode :
      evalExpr? retdataLoopConfig
        { contract := contract, locals := collectCallLocals locals out } evm'
        decodeReturndataExpr = .ok (.int (Int.ofNat value.toNat)))
    (htotal :
      evalExpr? retdataLoopConfig
        { contract := contract, locals := collectValueLocals locals out value } evm'
        (u256 (addE (.var "total") (.var "value"))) =
          .ok (.int (Int.ofNat newTotal.toNat)))
    (hassign :
      assignStorageRef? retdataLoopConfig
        { contract := contract, locals := collectValueLocals locals out value } evm'
        .localVar (varRef "total")
          (.int (Int.ofNat newTotal.toNat)) =
          .ok ({ contract := contract, locals := locals' }, evm')) :
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopBody (.ok { contract := contract, locals := locals' } evm') := by
  unfold collectLoopBody
  refine ExecBlock.consNormal
    (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess hreceiver (by simp [evalExpr?, pure]) hdata hcall
  · refine ExecBlock.consNormal
      (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
      (evm' := evm') ?_ ?_
    · exact ExecStmt.requireTrue
        (evalExpr_var_value (cfg := retdataLoopConfig) (C := contract)
          evm' ((locals.insert "ok" (.bool true)).insert "returndata" (.bytes out))
          "ok" (.bool true) (by
            rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_self]
            decide))
    · refine ExecBlock.consNormal
        (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
        (evm' := evm') ?_ ?_
      · exact ExecStmt.requireTrue (evalReturndataLength_eq_32_of_size (locals := locals) hout)
      · refine ExecBlock.consNormal
          (solm' := ({ contract := contract, locals := collectValueLocals locals out value } : Frame))
          (evm' := evm') ?_ ?_
        · exact ExecStmt.letDecl hdecode
        · refine ExecBlock.consNormal ?_ ExecBlock.nil
          exact ExecStmt.assign htotal (by simpa [varRef] using hassign)

theorem collectLoopBody_call_failure_revert {locals : Store}
    {evm evm' : EVM.State} {target : AccountAddress} {calldata out : ByteArray}
    (hreceiver :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        (arrGet "targets" (.var "i")) = .ok (.address target))
    (hdata :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        collectCalldataExpr = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) 0 calldata (false, evm', out)) :
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopBody .reverted := by
  unfold collectLoopBody
  refine ExecBlock.consNormal
    (solm' := ({ contract := contract, locals := collectCallFailureLocals locals out } : Frame))
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallFailure hreceiver (by simp [evalExpr?, pure]) hdata hcall
  · refine ExecBlock.consRevert ?_
    exact ExecStmt.requireFalse
      (evalExpr_var_value (cfg := retdataLoopConfig) (C := contract)
        evm' ((locals.insert "ok" (.bool false)).insert "returndata" (.bytes out))
        "ok" (.bool false) (by
          rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_self]
          decide))

theorem collectLoopBody_bad_length_revert {locals : Store}
    {evm evm' : EVM.State} {target : AccountAddress} {calldata out : ByteArray}
    (hreceiver :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        (arrGet "targets" (.var "i")) = .ok (.address target))
    (hdata :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        collectCalldataExpr = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) 0 calldata (true, evm', out))
    (hne : out.size ≠ 32) :
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopBody .reverted := by
  unfold collectLoopBody
  refine ExecBlock.consNormal
    (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess hreceiver (by simp [evalExpr?, pure]) hdata hcall
  · refine ExecBlock.consNormal
      (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
      (evm' := evm') ?_ ?_
    · exact ExecStmt.requireTrue
        (evalExpr_var_value (cfg := retdataLoopConfig) (C := contract)
          evm' ((locals.insert "ok" (.bool true)).insert "returndata" (.bytes out))
          "ok" (.bool true) (by
            rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_self]
            decide))
    · refine ExecBlock.consRevert ?_
      exact ExecStmt.requireFalse
        (evalReturndataLength_ne_32_of_size_ne (locals := locals) hne)

theorem collectLoopBody_overflow_revert {locals : Store}
    {evm evm' : EVM.State} {target : AccountAddress} {calldata out : ByteArray}
    (total : UInt256)
    (hreceiver :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        (arrGet "targets" (.var "i")) = .ok (.address target))
    (hdata :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        collectCalldataExpr = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) 0 calldata (true, evm', out))
    (hout : out.size = 32)
    (htotal : locals.get? "total" = some (.int (Int.ofNat total.toNat)))
    (hover :
      UInt256.size ≤
        total.toNat +
          (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat) :
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopBody .reverted := by
  unfold collectLoopBody
  let value : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  have hlo : 32 ≤ out.size := by omega
  have hhi : out.size < (2 : Nat) ^ 255 := by omega
  have hdecodedNat :
      value.toNat = fromByteArrayBigEndian (out.extract 0 32) := by
    unfold value
    exact UInt256.toNat_ofNat_of_lt
      (Reasoning.Theory.fromByteArrayBigEndian_extract0_32_lt hlo)
  refine ExecBlock.consNormal
    (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess hreceiver (by simp [evalExpr?, pure]) hdata hcall
  · refine ExecBlock.consNormal
      (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
      (evm' := evm') ?_ ?_
    · exact ExecStmt.requireTrue
        (evalExpr_var_value (cfg := retdataLoopConfig) (C := contract)
          evm' ((locals.insert "ok" (.bool true)).insert "returndata" (.bytes out))
          "ok" (.bool true) (by
            rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_self]
            decide))
    · refine ExecBlock.consNormal
        (solm' := ({ contract := contract, locals := collectCallLocals locals out } : Frame))
        (evm' := evm') ?_ ?_
      · exact ExecStmt.requireTrue (evalReturndataLength_eq_32_of_size (locals := locals) hout)
      · refine ExecBlock.consNormal
          (solm' := ({ contract := contract, locals := collectValueLocals locals out value } : Frame))
          (evm' := evm') ?_ ?_
        · exact ExecStmt.letDecl (by
            simpa [collectValueLocals, hdecodedNat] using
              evalDecodeReturndata_uint256_ok (locals := locals) (evm := evm') hlo hhi)
        · exact ExecBlock.consRevert
            (ExecStmt.assignExprRevert
              (evalCollectTotalAdd_revert_of_get
                (locals := locals) (evm := evm') total value htotal hover))

theorem collectLoopBody_success_of_gets {locals : Store}
    {evm evm' : EVM.State} {target : AccountAddress} {calldata out : ByteArray}
    (total : UInt256)
    (hreceiver :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        (arrGet "targets" (.var "i")) = .ok (.address target))
    (hdata :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        collectCalldataExpr = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) 0 calldata (true, evm', out))
    (hout : out.size = 32)
    (htotal : locals.get? "total" = some (.int (Int.ofNat total.toNat)))
    (hfit :
      total.toNat +
          (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat <
        UInt256.size) :
    let value : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    let newTotal : UInt256 := UInt256.ofNat (total.toNat + value.toNat)
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopBody
      (.ok
        { contract := contract,
          locals := (collectValueLocals locals out value).insert "total"
            (.int (Int.ofNat newTotal.toNat)) } evm') := by
  intro value newTotal
  have hlo : 32 ≤ out.size := by omega
  have hhi : out.size < (2 : Nat) ^ 255 := by omega
  have hdecodedNat :
      value.toNat = fromByteArrayBigEndian (out.extract 0 32) := by
    unfold value
    exact UInt256.toNat_ofNat_of_lt
      (Reasoning.Theory.fromByteArrayBigEndian_extract0_32_lt hlo)
  have hnewNat : newTotal.toNat = total.toNat + value.toNat := by
    unfold newTotal
    exact UInt256.toNat_ofNat_of_lt hfit
  refine collectLoopBody_success_of_eval_assign
    (locals := locals)
    (locals' :=
      (collectValueLocals locals out value).insert "total"
        (.int (Int.ofNat newTotal.toNat)))
    (evm := evm) (evm' := evm') (target := target) (calldata := calldata)
    (out := out) (value := value) (newTotal := newTotal)
    hreceiver hdata hcall hout ?_ ?_ ?_
  · rw [hdecodedNat]
    exact evalDecodeReturndata_uint256_ok (locals := locals) (evm := evm') hlo hhi
  · rw [hnewNat]
    exact evalCollectTotalAdd_of_get
      (locals := locals) (evm := evm') total value htotal hfit
  · exact assignCollectTotal_local
      (locals := locals) (evm := evm') out value newTotal total htotal

theorem collectLoopPost_success_of_get {locals : Store} {evm : EVM.State} (i : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hfit : i.toNat + 1 < UInt256.size) :
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopPost
      (.ok
        { contract := contract,
          locals := locals.insert "i" (.int (Int.ofNat i.toNat + 1)) } evm) := by
  unfold collectLoopPost u256 addE varRef
  refine ExecBlock.consNormal ?_ ExecBlock.nil
  refine ExecStmt.assign (value := .int (Int.ofNat i.toNat + 1)) ?_ ?_
  · simp only [evalExpr?, EvalResult.bind, bind, pure]
    rw [hi]
    simp only [EvalResult.ofOption, evalBinaryOp?]
    have hnonneg : ¬ ((Int.ofNat i.toNat + 1 : Int) < 0) := by
      have hn0 : (0 : Int) ≤ Int.ofNat i.toNat := Int.natCast_nonneg _
      omega
    have hlt : (Int.ofNat i.toNat + 1 : Int) < 2 ^ (256 : Nat) := by
      have hfit' : i.toNat + 1 < 2 ^ (256 : Nat) := by
        simpa [UInt256.size] using hfit
      have hfitCast : ((i.toNat + 1 : Nat) : Int) < ((2 ^ (256 : Nat) : Nat) : Int) := by
        exact_mod_cast hfit'
      simpa [Nat.cast_add, Nat.cast_one] using hfitCast
    simp [uint256Int]
    constructor
    · have hn0 : (0 : Int) ≤ Int.ofNat i.toNat := Int.natCast_nonneg _
      omega
    · simpa using hlt
  · simp [assignStorageRef?, updateLocalPath?]
    rw [← Std.HashMap.get?_eq_getElem?, hi]
    rfl

theorem collectLoopBody_then_post_success_of_gets {locals : Store}
    {evm evm' : EVM.State} {target : AccountAddress} {calldata out : ByteArray}
    (i total : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hreceiver :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        (arrGet "targets" (.var "i")) = .ok (.address target))
    (hdata :
      evalExpr? retdataLoopConfig { contract := contract, locals := locals } evm
        collectCalldataExpr = .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) 0 calldata (true, evm', out))
    (hout : out.size = 32)
    (htotal : locals.get? "total" = some (.int (Int.ofNat total.toNat)))
    (hfitTotal :
      total.toNat +
          (UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))).toNat <
        UInt256.size)
    (hfitIdx : i.toNat + 1 < UInt256.size) :
    let value : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    let newTotal : UInt256 := UInt256.ofNat (total.toNat + value.toNat)
    let bodyLocals : Store :=
      (collectValueLocals locals out value).insert "total"
        (.int (Int.ofNat newTotal.toNat))
    ExecBlock retdataLoopConfig { contract := contract, locals := locals } evm
      collectLoopBody (.ok { contract := contract, locals := bodyLocals } evm') ∧
    ExecBlock retdataLoopConfig { contract := contract, locals := bodyLocals } evm'
      collectLoopPost
      (.ok
        { contract := contract,
          locals := bodyLocals.insert "i" (.int (Int.ofNat i.toNat + 1)) } evm') := by
  intro value newTotal bodyLocals
  constructor
  · exact collectLoopBody_success_of_gets
      (locals := locals) (evm := evm) (evm' := evm') (target := target)
      (calldata := calldata) (out := out) total
      hreceiver hdata hcall hout htotal hfitTotal
  · have hiBody :
        bodyLocals.get? "i" = some (.int (Int.ofNat i.toNat)) := by
      unfold bodyLocals collectValueLocals collectCallLocals
      rw [Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_ne,
        Reasoning.Theory.store_get_ne, Reasoning.Theory.store_get_ne, hi]
      · decide
      · decide
      · decide
      · decide
    exact collectLoopPost_success_of_get
      (locals := bodyLocals) (evm := evm') i hiBody hfitIdx

/-- RetdataLoop-specialized wrapper around `RD.execForLoopOrRevertCarryFull`.

The shape hypothesis connects the variant to the source locals:
`i + v = n`, so variant `0` means the source guard is false, while variant `v + 1`
means the source guard is true. The carried state `α` is where a later runtime proof should
store dynamic-memory facts such as retained return-data regions and the free-memory cursor.
-/
theorem collectLoop_from_body_or_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {code : ByteArray} {rdata : ByteArray} {α : Type}
    (header bodyHeader exit : UInt256)
    (Inv : ℕ → α → Store → EVM.State → Prop)
    (idx n : α → UInt256)
    (stk : α → List UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (exitStk : α → List UInt256)
    (hshape : ∀ v a L evm, Inv v a L evm →
      L.get? "i" = some (.int (Int.ofNat (idx a).toNat)) ∧
      L.get? "n" = some (.int (Int.ofNat (n a).toNat)) ∧
      (idx a).toNat + v = (n a).toNat ∧
      (idx a).toNat ≤ (n a).toNat)
    (hexit : ∀ a L evm, Inv 0 a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C', RD code ee g s0 exit (exitStk a) (mem a) (aw a) rdata (acc a) k' C')
    (henter : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      ∃ k' C', RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k' C')
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
      RD code ee g s0 bodyHeader (stk a) (mem a) (aw a) rdata (acc a) k C →
      (ExecBlock retdataLoopConfig { contract := contract, locals := L } evm
          collectLoopBody .reverted ∧
        RDrev code g s0) ∨
      ∃ a' L1 evm1 L2 evm2 k' C',
        (ExecBlock retdataLoopConfig { contract := contract, locals := L } evm
            collectLoopBody
            (.ok { contract := contract, locals := L1 } evm1) ∨
          ExecBlock retdataLoopConfig { contract := contract, locals := L } evm
            collectLoopBody
            (.continue { contract := contract, locals := L1 } evm1)) ∧
        ExecBlock retdataLoopConfig { contract := contract, locals := L1 } evm1
          collectLoopPost
          (.ok { contract := contract, locals := L2 } evm2) ∧
        Inv v a' L2 evm2 ∧
        RD code ee g s0 header (stk a') (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD code ee g s0 header (stk a) (mem a) (aw a) rdata (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop retdataLoopConfig
          { contract := contract, locals := L } evm
          collectLoopCond collectLoopPost collectLoopBody
          (.ok { contract := contract, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD code ee g s0 exit (exitStk a') (mem a') (aw a') rdata (acc a') k' C') ∨
      (ExecForLoop retdataLoopConfig
          { contract := contract, locals := L } evm
          collectLoopCond collectLoopPost collectLoopBody .reverted ∧
        RDrev code g s0) := by
  refine Reasoning.Reach.RD.execForLoopOrRevertCarryFull
    (cfg := retdataLoopConfig) (contract := contract)
    (code := code) (ee := ee) (g := g) (s0 := s0) (rdata := rdata)
    (header := header) (bodyHeader := bodyHeader) (exit := exit)
    (condExpr := collectLoopCond) (post := collectLoopPost) (body := collectLoopBody)
    (Inv := Inv) (stk := stk) (mem := mem) (aw := aw) (acc := acc) (exitStk := exitStk)
    ?_ hexit ?_ henter hbody
  · intro a L evm hInv
    rcases hshape 0 a L evm hInv with ⟨hi, hn, hvar, _hle⟩
    exact evalCollectLoopCond_false_of_get evm L (n a) (idx a) hi hn (by omega)
  · intro v a L evm hInv
    rcases hshape (v + 1) a L evm hInv with ⟨hi, hn, hvar, _hle⟩
    exact evalCollectLoopCond_true_of_get evm L (n a) (idx a) hi hn (by omega)

end RetdataLoop
