import Benchmarks.ActAmm4.ConstructorSource
import Benchmarks.ActAmm4.ConstructorArgsTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorAddressWord_roundtrip (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a).toNat = a := by
  apply Fin.ext
  change (a.val % EVM.twoPow 256) % AccountAddress.size = a.val
  have hbig : a.val < EVM.twoPow 256 := by
    have hsmall := a.isLt
    simp [AccountAddress.size, EVM.twoPow] at hsmall ⊢
    omega
  rw [Nat.mod_eq_of_lt hbig, Nat.mod_eq_of_lt a.isLt]

def amm4CtorAfterToken0 (evm : EVM.State) (t0 : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      (EVM.word t0))

theorem amm4CtorAfterBaseLocals_token0_none (t0 t1 : AccountAddress)
    (liquidity : Int) :
    (amm4CtorAfterBaseLocals t0 t1 liquidity).get? "token0" = none := by
  rw [amm4CtorAfterBaseLocals,
    store_get_ne (amm4CtorLocals t0 t1 liquidity)
      (k := "baseSupply") (a := "token0") _ (by decide)]
  simp [amm4CtorLocals]

theorem amm4CtorAssignToken0 (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    assignStorageRef? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm .storage token0Ref (.address t0) =
        .ok ({ contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity },
          amm4CtorAfterToken0 evm t0) := by
  apply assignStorageRef_storage_scalar_value
    (ty := .elem .address)
    (er := ({ base := "token0", steps := [] } : EvaledStorageRef))
    (loc := addrLoc ⟨3⟩)
    (amm4CtorAfterBaseLocals_token0_none t0 t1 liquidity)
    (by simp [evalStorageRef, evalStorageRefSteps, token0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by trivial)
  simpa only [amm4CtorAfterToken0, addrLoc, addressOffset0Loc,
    amm4CtorAddressWord_roundtrip] using
      storageLocStore_address_offset0 evm ⟨3⟩ (EVM.word t0)
        (amm4CtorAddressWord_canonical t0)

def amm4CtorAfterToken1 (evm : EVM.State) (t1 : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
      (EVM.word t1))

theorem amm4CtorAfterBaseLocals_token1_none (t0 t1 : AccountAddress)
    (liquidity : Int) :
    (amm4CtorAfterBaseLocals t0 t1 liquidity).get? "token1" = none := by
  rw [amm4CtorAfterBaseLocals,
    store_get_ne (amm4CtorLocals t0 t1 liquidity)
      (k := "baseSupply") (a := "token1") _ (by decide)]
  simp [amm4CtorLocals]

theorem amm4CtorAssignToken1 (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) :
    assignStorageRef? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm .storage token1Ref (.address t1) =
        .ok ({ contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity },
          amm4CtorAfterToken1 evm t1) := by
  apply assignStorageRef_storage_scalar_value
    (ty := .elem .address)
    (er := ({ base := "token1", steps := [] } : EvaledStorageRef))
    (loc := addrLoc ⟨4⟩)
    (amm4CtorAfterBaseLocals_token1_none t0 t1 liquidity)
    (by simp [evalStorageRef, evalStorageRefSteps, token1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by trivial)
  simpa only [amm4CtorAfterToken1, addrLoc, addressOffset0Loc,
    amm4CtorAddressWord_roundtrip] using
      storageLocStore_address_offset0 evm ⟨4⟩ (EVM.word t1)
        (amm4CtorAddressWord_canonical t1)

private theorem amm4CtorEvalAddressNe_true {cfg : Config} {frame : Frame}
    {evm : EVM.State} {x y : Expr} {a b : AccountAddress}
    (hx : evalExpr? cfg frame evm x = .ok (.address a))
    (hy : evalExpr? cfg frame evm y = .ok (.address b))
    (hne : a ≠ b) :
    evalExpr? cfg frame evm (.binary .ne x y) = .ok (.bool true) := by
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, hx, hy, hne]

theorem amm4CtorDistinctTokensGuard_true (t0 t1 : AccountAddress)
    (liquidity : Int) (evm : EVM.State) (hne : t0 ≠ t1) :
    evalExpr? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm (.binary .ne (.var "t0") (.var "t1")) =
        .ok (.bool true) := by
  exact amm4CtorEvalAddressNe_true
    (amm4CtorEvalT0 t0 t1 liquidity evm)
    (amm4CtorEvalT1 t0 t1 liquidity evm) hne

def amm4CtorSourceStoredPrefix : List Stmt :=
  nonpayable ++
    [ .letDecl "baseSupply" (some uint256)
        (checkedSub (.var "liquidity") (.intLit minimumLiquidity)),
      .assign .storage totalSupplyRef (.var "baseSupply"),
      .assign .storage (balanceOfRef sender) (.var "baseSupply"),
      .require (.binary .ne (.var "t0") (.var "t1")),
      .assign .storage token0Ref (.var "t0"),
      .assign .storage token1Ref (.var "t1") ]

theorem amm4CtorSourceStoredPrefix_ok
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
    (hne : t0 ≠ t1) (hwv : I.weiValue = ⟨0⟩) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := amm4CtorAfterSupply evm liquidity
    let evm2 := amm4CtorAfterSender evm1 I liquidity
    let evm3 := amm4CtorAfterToken0 evm2 t0
    let evm4 := amm4CtorAfterToken1 evm3 t1
    ExecBlock config { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm amm4CtorSourceStoredPrefix
      (.ok { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
        evm4) := by
  intro evm evm1 evm2 evm3 evm4
  have hsrc : evm1.executionEnv.source = I.source := by
    simp [evm1, amm4CtorAfterSupply, storageStore_executionEnv,
      evm, initState]
  change ExecBlock config
    { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
    evm
    [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
      .letDecl "baseSupply" (some uint256)
        (checkedSub (.var "liquidity") (.intLit minimumLiquidity)),
      .assign .storage totalSupplyRef (.var "baseSupply"),
      .assign .storage (balanceOfRef sender) (.var "baseSupply"),
      .require (.binary .ne (.var "t0") (.var "t1")),
      .assign .storage token0Ref (.var "t0"),
      .assign .storage token1Ref (.var "t1") ]
    (.ok { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm4)
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
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (amm4CtorDistinctTokensGuard_true t0 t1 liquidity evm2 hne)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (amm4CtorEvalT0 t0 t1 liquidity evm2)
      (amm4CtorAssignToken0 t0 t1 liquidity evm2)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (amm4CtorEvalT1 t0 t1 liquidity evm3)
      (amm4CtorAssignToken1 t0 t1 liquidity evm3)) ?_
  exact ExecBlock.nil

end Benchmarks.ActAmm4
