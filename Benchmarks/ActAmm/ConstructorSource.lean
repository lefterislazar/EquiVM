import Benchmarks.ActAmm.ConstructorBase
import Benchmarks.ActAmm.Arithmetic
import Benchmarks.ActAmm.Storage
import Benchmarks.ActAmm.Transfer
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

def ammCtorLocals (t0 t1 : AccountAddress) (liquidity : Int) : Store :=
  Std.HashMap.ofList
    [("t0", .address t0), ("t1", .address t1), ("liquidity", .int liquidity)]

theorem ammCtorEvalLiquidity (t0 t1 : AccountAddress) (liquidity : Int)
    (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
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
  rw [show (ammCtorLocals t0 t1 liquidity)["liquidity"]? =
    some (.int liquidity) from by simpa [ammCtorLocals] using hget]
  rfl

theorem ammCtorBaseSupply_revert (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hunder : liquidity.toNat < 1000) :
    evalExpr? config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) = .revert := by
  have hx : evalExpr? config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (.var "liquidity") =
        .ok (.int (Int.ofNat liquidity.toNat)) := by
    simpa [Int.toNat_of_nonneg h0] using ammCtorEvalLiquidity t0 t1 liquidity evm
  have hy : evalExpr? config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (.intLit minimumLiquidity) = .ok (.int (Int.ofNat 1000)) := by
    simp [minimumLiquidity, evalExpr?, pure]
  exact ammEvalCheckedSub_revert hx hy hunder

theorem ammCtorBaseSupply_ok (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    evalExpr? config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) =
        .ok (.int (Int.ofNat (liquidity.toNat - 1000))) := by
  have hx : evalExpr? config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (.var "liquidity") =
        .ok (.int (Int.ofNat liquidity.toNat)) := by
    simpa [Int.toNat_of_nonneg h0] using ammCtorEvalLiquidity t0 t1 liquidity evm
  have hy : evalExpr? config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm (.intLit minimumLiquidity) = .ok (.int (Int.ofNat 1000)) := by
    simp [minimumLiquidity, evalExpr?, pure]
  exact ammEvalCheckedSub_ok hx hy hle hfit

def ammCtorAfterBaseLocals (t0 t1 : AccountAddress)
    (liquidity : Int) : Store :=
  (ammCtorLocals t0 t1 liquidity).insert "baseSupply"
    (.int (Int.ofNat (liquidity.toNat - 1000)))

def ammCtorAfterSupply (evm : EVM.State) (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.ofNat (liquidity.toNat - 1000))

theorem ammCtorEvalBaseSupply (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    evalExpr? config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm (.var "baseSupply") =
        .ok (.int (Int.ofNat (liquidity.toNat - 1000))) := by
  simp only [evalExpr?, ammCtorAfterBaseLocals, store_get_self,
    EvalResult.ofOption]

theorem ammCtorAssignSupply (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State)
    (hfit : liquidity.toNat < UInt256.size) :
    assignStorageRef? config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm .storage totalSupplyRef
      (.int (Int.ofNat (liquidity.toNat - 1000))) =
        .ok ({ contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity },
          ammCtorAfterSupply evm liquidity) := by
  apply assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (hbase := by
      change (ammCtorAfterBaseLocals t0 t1 liquidity).get? "totalSupply" = none
      rw [ammCtorAfterBaseLocals,
        store_get_ne (ammCtorLocals t0 t1 liquidity)
          (k := "baseSupply") (a := "totalSupply") _ (by decide)]
      simp [ammCtorLocals])
    (her := by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  have hword : (UInt256.ofNat (liquidity.toNat - 1000)).toNat =
      liquidity.toNat - 1000 := by
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)
  simpa only [ammCtorAfterSupply, hword] using
    ammStorageLocStore_uint256 evm ⟨0⟩
      (UInt256.ofNat (liquidity.toNat - 1000))

theorem ammCtorAfterBaseLocals_balanceOf_none (t0 t1 : AccountAddress)
    (liquidity : Int) :
    (ammCtorAfterBaseLocals t0 t1 liquidity).get? "balanceOf" = none := by
  rw [ammCtorAfterBaseLocals,
    store_get_ne (ammCtorLocals t0 t1 liquidity)
      (k := "baseSupply") (a := "balanceOf") _ (by decide)]
  simp [ammCtorLocals]

theorem ammCtorEvalSenderRef (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm (balanceOfRef sender) = .ok (ammTransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    valueToKey?, ammTransferSenderRef, sender, envValue, hsrc]

def ammCtorAfterSender (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (ammTransferSenderSlot I)
    (UInt256.ofNat (liquidity.toNat - 1000))

theorem ammCtorAssignSender (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (I : ExecutionEnv)
    (hfit : liquidity.toNat < UInt256.size)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm .storage (balanceOfRef sender)
      (.int (Int.ofNat (liquidity.toNat - 1000))) =
        .ok ({ contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity },
          ammCtorAfterSender evm I liquidity) := by
  apply assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int))
    (er := ammTransferSenderRef I)
    (loc := wordLoc (ammTransferSenderSlot I))
    (ammCtorAfterBaseLocals_balanceOf_none t0 t1 liquidity)
    (ammCtorEvalSenderRef t0 t1 liquidity evm I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      ammTransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
  have hword : (UInt256.ofNat (liquidity.toNat - 1000)).toNat =
      liquidity.toNat - 1000 := by
    exact ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)
  simpa only [ammCtorAfterSender, hword] using
    ammStorageLocStore_uint256 evm (ammTransferSenderSlot I)
      (UInt256.ofNat (liquidity.toNat - 1000))

theorem ammCtorEvalT0 (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    evalExpr? config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm (.var "t0") = .ok (.address t0) := by
  have hget : (ammCtorAfterBaseLocals t0 t1 liquidity).get? "t0" =
      some (.address t0) := by
    rw [ammCtorAfterBaseLocals,
      store_get_ne (ammCtorLocals t0 t1 liquidity)
        (k := "baseSupply") (a := "t0") _ (by decide)]
    unfold ammCtorLocals
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_mem
      (k := "t0") (k' := "t0") (v := Value.address t0)
      (by decide) (by simp) (by simp)
  simp only [evalExpr?, hget, EvalResult.ofOption]

theorem ammCtorEvalT1 (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    evalExpr? config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm (.var "t1") = .ok (.address t1) := by
  have hget : (ammCtorAfterBaseLocals t0 t1 liquidity).get? "t1" =
      some (.address t1) := by
    rw [ammCtorAfterBaseLocals,
      store_get_ne (ammCtorLocals t0 t1 liquidity)
        (k := "baseSupply") (a := "t1") _ (by decide)]
    unfold ammCtorLocals
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_mem
      (k := "t1") (k' := "t1") (v := Value.address t1)
      (by decide) (by simp) (by simp)
  simp only [evalExpr?, hget, EvalResult.ofOption]

private theorem ammCtorEvalAddressNe_false {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (heq : a = b) :
    evalExpr? cfg frame evm (.binary .ne x y) = .ok (.bool false) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy, heq]

theorem ammCtorEqualTokensGuard_false (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (heq : t0 = t1) :
    evalExpr? config
      { contract := contract, locals := ammCtorAfterBaseLocals t0 t1 liquidity }
      evm (.binary .ne (.var "t0") (.var "t1")) =
        .ok (.bool false) := by
  exact ammCtorEvalAddressNe_false
    (ammCtorEvalT0 t0 t1 liquidity evm)
    (ammCtorEvalT1 t0 t1 liquidity evm) heq

theorem ammSolmCtorExecReverts_nonpayable
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
    (argsStore := ammCtorLocals t0 t1 liquidity)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · exact bodyReverts_nonPayable (cfg := config) (contract := contract)
      (locals := ammCtorLocals t0 t1 liquidity) hwv

theorem ammSolmCtorExecReverts_underflow
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
    (argsStore := ammCtorLocals t0 t1 liquidity)
    ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
      evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .letDecl "baseSupply" (some uint256)
          (checkedSub (.var "liquidity") (.intLit minimumLiquidity)) :: _)
      .reverted
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simpa [evm, initState] using hwv)
    · exact ExecBlock.consRevert
        (ExecStmt.letDeclRevert
          (ammCtorBaseSupply_revert t0 t1 liquidity evm h0 hunder))

theorem ammSolmCtorExecReverts_equalTokens
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
  let evm1 := ammCtorAfterSupply evm liquidity
  let evm2 := ammCtorAfterSender evm1 I liquidity
  have hsrc : evm1.executionEnv.source = I.source := by
    simp [evm1, ammCtorAfterSupply, storageStore_executionEnv,
      evm, initState]
  refine solmCtorExec.intro
    (evmState := evm)
    (argsStore := ammCtorLocals t0 t1 liquidity)
    ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := ammCtorLocals t0 t1 liquidity }
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
      (ExecStmt.letDecl (ammCtorBaseSupply_ok t0 t1 liquidity evm h0 hle hfit)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (ammCtorEvalBaseSupply t0 t1 liquidity evm)
        (ammCtorAssignSupply t0 t1 liquidity evm hfit)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign (ammCtorEvalBaseSupply t0 t1 liquidity evm1)
        (ammCtorAssignSender t0 t1 liquidity evm1 I hfit hsrc)) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse (ammCtorEqualTokensGuard_false t0 t1 liquidity evm2 heq))

end Benchmarks.ActAmm
