import Benchmarks.ActAmm4.ConstructorBase
import Benchmarks.ActAmm4.Arithmetic
import Benchmarks.ActAmm4.Storage
import Benchmarks.ActAmm4.Transfer
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

def amm4CtorLocals (t0 t1 : AccountAddress) (liquidity : Int) : Store :=
  Std.HashMap.ofList
    [("t0", .address t0), ("t1", .address t1), ("liquidity", .int liquidity)]

theorem amm4CtorEvalLiquidity (t0 t1 : AccountAddress) (liquidity : Int)
    (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (.var "liquidity") = .ok (.int liquidity) := by
  have hget :
      (Std.HashMap.ofList
        [("t0", Value.address t0), ("t1", Value.address t1),
          ("liquidity", Value.int liquidity)])["liquidity"]? =
          some (.int liquidity) :=
    Std.HashMap.getElem?_ofList_of_mem
      (k := "liquidity") (k' := "liquidity") (v := Value.int liquidity)
      (by decide) (by simp) (by simp)
  simp only [evalExpr?]
  rw [Std.HashMap.get?_eq_getElem?]
  rw [show (amm4CtorLocals t0 t1 liquidity)["liquidity"]? =
    some (.int liquidity) from by simpa [amm4CtorLocals] using hget]
  rfl

theorem amm4CtorBaseSupply_revert (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hunder : liquidity.toNat < 1000) :
    evalExpr? config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) = .revert := by
  have hx : evalExpr? config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (.var "liquidity") =
        .ok (.int (Int.ofNat liquidity.toNat)) := by
    simpa [Int.toNat_of_nonneg h0] using amm4CtorEvalLiquidity t0 t1 liquidity evm
  have hy : evalExpr? config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (.intLit minimumLiquidity) = .ok (.int (Int.ofNat 1000)) := by
    simp [minimumLiquidity, evalExpr?, pure]
  exact amm4EvalCheckedSub_revert hx hy hunder

theorem amm4CtorBaseSupply_ok (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) =
        .ok (.int (Int.ofNat (liquidity.toNat - 1000))) := by
  have hx : evalExpr? config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (.var "liquidity") =
        .ok (.int (Int.ofNat liquidity.toNat)) := by
    simpa [Int.toNat_of_nonneg h0] using amm4CtorEvalLiquidity t0 t1 liquidity evm
  have hy : evalExpr? config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (.intLit minimumLiquidity) = .ok (.int (Int.ofNat 1000)) := by
    simp [minimumLiquidity, evalExpr?, pure]
  exact amm4EvalCheckedSub_ok hx hy hle hfit

def amm4CtorAfterBaseLocals (t0 t1 : AccountAddress)
    (liquidity : Int) : Store :=
  (amm4CtorLocals t0 t1 liquidity).insert "baseSupply"
    (.int (Int.ofNat (liquidity.toNat - 1000)))

def amm4CtorAfterSupply (evm : EVM.State) (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.ofNat (liquidity.toNat - 1000))

theorem amm4CtorEvalBaseSupply (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    evalExpr? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm (.var "baseSupply") =
        .ok (.int (Int.ofNat (liquidity.toNat - 1000))) := by
  simp only [evalExpr?, amm4CtorAfterBaseLocals, store_get_self,
    EvalResult.ofOption]

theorem amm4CtorAssignSupply (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State)
    (hfit : liquidity.toNat < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm .storage totalSupplyRef
      (.int (Int.ofNat (liquidity.toNat - 1000))) =
        .ok ({ contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity },
          amm4CtorAfterSupply evm liquidity) := by
  apply assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (hbase := by
      change (amm4CtorAfterBaseLocals t0 t1 liquidity).get? "totalSupply" = none
      rw [amm4CtorAfterBaseLocals,
        store_get_ne (amm4CtorLocals t0 t1 liquidity)
          (k := "baseSupply") (a := "totalSupply") _ (by decide)]
      simp [amm4CtorLocals])
    (her := by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  have hword : (UInt256.ofNat (liquidity.toNat - 1000)).toNat =
      liquidity.toNat - 1000 := by
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)
  simpa only [amm4CtorAfterSupply, hword] using
    amm4StorageLocStore_uint256 evm ⟨0⟩
      (UInt256.ofNat (liquidity.toNat - 1000))

theorem amm4CtorAfterBaseLocals_balanceOf_none (t0 t1 : AccountAddress)
    (liquidity : Int) :
    (amm4CtorAfterBaseLocals t0 t1 liquidity).get? "balanceOf" = none := by
  rw [amm4CtorAfterBaseLocals,
    store_get_ne (amm4CtorLocals t0 t1 liquidity)
      (k := "baseSupply") (a := "balanceOf") _ (by decide)]
  simp [amm4CtorLocals]

theorem amm4CtorEvalSenderRef (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm (balanceOfRef sender) = .ok (amm4TransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, amm4TransferSenderRef, sender, envValue, hsrc]

def amm4CtorAfterSender (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (amm4TransferSenderSlot I)
    (UInt256.ofNat (liquidity.toNat - 1000))

theorem amm4CtorAssignSender (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (I : ExecutionEnv)
    (hfit : liquidity.toNat < UInt256.size)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm .storage (balanceOfRef sender)
      (.int (Int.ofNat (liquidity.toNat - 1000))) =
        .ok ({ contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity },
          amm4CtorAfterSender evm I liquidity) := by
  apply assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (er := amm4TransferSenderRef I)
    (loc := wordLoc (amm4TransferSenderSlot I))
    (amm4CtorAfterBaseLocals_balanceOf_none t0 t1 liquidity)
    (amm4CtorEvalSenderRef t0 t1 liquidity evm I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
  have hword : (UInt256.ofNat (liquidity.toNat - 1000)).toNat =
      liquidity.toNat - 1000 := by
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)
  simpa only [amm4CtorAfterSender, hword] using
    amm4StorageLocStore_uint256 evm (amm4TransferSenderSlot I)
      (UInt256.ofNat (liquidity.toNat - 1000))

theorem amm4CtorEvalT0 (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    evalExpr? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm (.var "t0") = .ok (.address t0) := by
  have hget : (amm4CtorAfterBaseLocals t0 t1 liquidity).get? "t0" =
      some (.address t0) := by
    rw [amm4CtorAfterBaseLocals,
      store_get_ne (amm4CtorLocals t0 t1 liquidity)
        (k := "baseSupply") (a := "t0") _ (by decide)]
    unfold amm4CtorLocals
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_mem
      (k := "t0") (k' := "t0") (v := Value.address t0)
      (by decide) (by simp) (by simp)
  simp only [evalExpr?, hget, EvalResult.ofOption]

theorem amm4CtorEvalT1 (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    evalExpr? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm (.var "t1") = .ok (.address t1) := by
  have hget : (amm4CtorAfterBaseLocals t0 t1 liquidity).get? "t1" =
      some (.address t1) := by
    rw [amm4CtorAfterBaseLocals,
      store_get_ne (amm4CtorLocals t0 t1 liquidity)
        (k := "baseSupply") (a := "t1") _ (by decide)]
    unfold amm4CtorLocals
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_mem
      (k := "t1") (k' := "t1") (v := Value.address t1)
      (by decide) (by simp) (by simp)
  simp only [evalExpr?, hget, EvalResult.ofOption]

private theorem amm4CtorEvalAddressNe_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (heq : a = b) :
    evalExpr? cfg frame evm (.binary .ne x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy, heq]

theorem amm4CtorEqualTokensGuard_false (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (heq : t0 = t1) :
    evalExpr? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm (.binary .ne (.var "t0") (.var "t1")) =
        .ok (.bool false) := by
  exact amm4CtorEvalAddressNe_false
    (amm4CtorEvalT0 t0 t1 liquidity evm)
    (amm4CtorEvalT1 t0 t1 liquidity evm) heq

theorem amm4SolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract
      [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := amm4CtorLocals t0 t1 liquidity)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · exact bodyReverts_nonPayable (cfg := config) (contract := contract)
      (locals := amm4CtorLocals t0 t1 liquidity) hwv

theorem amm4SolmCtorExecReverts_underflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hunder : liquidity.toNat < 1000)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract
      [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
    (Sat256.ofUInt256 g) A I
  refine solmCtorExec.intro
    (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity)
    ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .letDecl "baseSupply" (some uint256)
          (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) :: _)
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm, initState] using hwv)
    · exact ExecBlock.consRevert
        (ExecStmt.letDeclRevert
          (amm4CtorBaseSupply_revert t0 t1 liquidity evm h0 hunder))

theorem amm4SolmCtorExecReverts_equalTokens
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (heq : t0 = t1)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract
      [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := amm4CtorAfterSupply evm liquidity
  let evm2 := amm4CtorAfterSender evm1 I liquidity
  have hsrc : evm1.executionEnv.source = I.source := by
    simp [evm1, amm4CtorAfterSupply, storageStore_executionEnv,
      evm, initState]
  refine solmCtorExec.intro
    (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity)
    ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .letDecl "baseSupply" (some uint256)
          (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) ::
        .assign .storage totalSupplyRef (.var "baseSupply") ::
        .assign .storage (balanceOfRef sender) (.var "baseSupply") ::
        .require (.binary .ne (.var "t0") (.var "t1")) :: _)
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm, initState] using hwv)
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (amm4CtorBaseSupply_ok t0 t1 liquidity evm h0 hle hfit)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (amm4CtorEvalBaseSupply t0 t1 liquidity evm)
        (amm4CtorAssignSupply t0 t1 liquidity evm hfit)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (amm4CtorEvalBaseSupply t0 t1 liquidity evm1)
        (amm4CtorAssignSender t0 t1 liquidity evm1 I hfit hsrc)) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (amm4CtorEqualTokensGuard_false t0 t1 liquidity evm2 heq))

end Benchmarks.ActAmm4
