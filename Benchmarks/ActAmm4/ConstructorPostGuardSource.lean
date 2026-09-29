import Benchmarks.ActAmm4.ConstructorArithmeticSource
import Benchmarks.ActAmm4.ConstructorPostGuardSender

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorAfterSquareLocals_supply_none
    (t0 t1 : AccountAddress) (liquidity : Int) (ret1 ret2 : ByteArray) :
    (amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2).get? "totalSupply" = none := by
  simp only [amm4CtorAfterSquareLocals, amm4CtorAfterProductLocals,
    amm4CtorAfterInitialBalance0Locals, amm4CtorAfterInitialBalance1Locals,
    amm4CtorAfterBaseLocals]
  repeat rw [store_get_ne _ _ (by decide)]
  simp [amm4CtorLocals]

def amm4CtorPostGuardAfterSupply (evm : EVM.State) (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.ofNat liquidity.toNat)

theorem amm4CtorPostGuardAssignSupply
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hfit : liquidity.toNat < UInt256.size) :
    assignStorageRef? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm .storage totalSupplyRef (.int liquidity) =
      .ok (⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩,
        amm4CtorPostGuardAfterSupply evm liquidity) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (evm' := amm4CtorPostGuardAfterSupply evm liquidity)
    (slot := totalSupplyRef) (n := liquidity)
    (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (amm4CtorAfterSquareLocals_supply_none t0 t1 liquidity ret1 ret2)
    (by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
  have hword : (UInt256.ofNat liquidity.toNat).toNat = liquidity.toNat :=
    ulit_toNat' _ hfit
  have hliq : (Int.ofNat liquidity.toNat) = liquidity := Int.toNat_of_nonneg h0
  simpa only [amm4CtorPostGuardAfterSupply, hword, hliq] using
    amm4StorageLocStore_uint256 evm ⟨0⟩ (UInt256.ofNat liquidity.toNat)

theorem amm4CtorPostGuardSupplyStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hfit : liquidity.toNat < UInt256.size) :
    ExecStmt config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.assign .storage totalSupplyRef (.var "liquidity"))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (amm4CtorPostGuardAfterSupply evm liquidity)) := by
  exact ExecStmt.assign
    (amm4CtorEvalLiquidityAfterSquare t0 t1 liquidity ret1 ret2 evm)
    (amm4CtorPostGuardAssignSupply t0 t1 liquidity ret1 ret2 evm h0 hfit)

def amm4CtorSelfSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address I.codeOwner)

theorem amm4CtorSelfSlot_eq_solc (I : ExecutionEnv) :
    solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val) =
      amm4CtorSelfSlot I := by
  unfold amm4CtorSelfSlot balanceOfSlot mapSlot solcMappingSlot
  rw [amm4Source_keyValueToWord I.codeOwner]

def amm4CtorSelfRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.codeOwner)] }

theorem amm4CtorAfterSquareLocals_balanceOf_none
    (t0 t1 : AccountAddress) (liquidity : Int) (ret1 ret2 : ByteArray) :
    (amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2).get? "balanceOf" = none := by
  simp only [amm4CtorAfterSquareLocals, amm4CtorAfterProductLocals,
    amm4CtorAfterInitialBalance0Locals, amm4CtorAfterInitialBalance1Locals,
    amm4CtorAfterBaseLocals]
  repeat rw [store_get_ne _ _ (by decide)]
  simp [amm4CtorLocals]

theorem amm4CtorEvalSelfRef
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalStorageRef config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (balanceOfRef thisAddr) = .ok (amm4CtorSelfRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, thisAddr, evalExpr?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, valueToKey?, envValue, howner, amm4CtorSelfRef]

def amm4CtorPostGuardAfterSelf (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (balanceOfSlot (.address evm.executionEnv.codeOwner)) ⟨1000⟩

theorem amm4CtorPostGuardAssignSelf
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    assignStorageRef? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm .storage (balanceOfRef thisAddr) (.int 1000) =
      .ok (⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩,
        amm4CtorPostGuardAfterSelf evm) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (evm' := amm4CtorPostGuardAfterSelf evm)
    (slot := balanceOfRef thisAddr) (n := 1000)
    (ty := .elem (.int uint256Int))
    (er := amm4CtorSelfRef I) (loc := wordLoc (amm4CtorSelfSlot I))
    (amm4CtorAfterSquareLocals_balanceOf_none t0 t1 liquidity ret1 ret2)
    (amm4CtorEvalSelfRef t0 t1 liquidity ret1 ret2 evm I howner)
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4CtorSelfRef, uint256St, storageTypeStep?])
    (by rfl)
  simpa only [amm4CtorPostGuardAfterSelf, amm4CtorSelfSlot,
    amm4CtorSelfRef, howner] using
    amm4StorageLocStore_uint256 evm
      (balanceOfSlot (.address evm.executionEnv.codeOwner)) ⟨1000⟩

theorem amm4CtorPostGuardSelfStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    ExecStmt config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.assign .storage (balanceOfRef thisAddr) (.intLit minimumLiquidity))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (amm4CtorPostGuardAfterSelf evm)) := by
  exact ExecStmt.assign (by simp [evalExpr?, minimumLiquidity, pure])
    (amm4CtorPostGuardAssignSelf t0 t1 liquidity ret1 ret2 evm I howner)

theorem amm4CtorEvalBaseSupplyAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "baseSupply") =
      .ok (.int (Int.ofNat (liquidity.toNat - 1000))) := by
  simp only [evalExpr?, amm4CtorAfterSquareLocals,
    amm4CtorAfterProductLocals, amm4CtorAfterInitialBalance0Locals,
    amm4CtorAfterInitialBalance1Locals]
  repeat rw [store_get_ne _ _ (by decide)]
  simpa only [evalExpr?] using amm4CtorEvalBaseSupply t0 t1 liquidity evm

theorem amm4CtorEvalSenderRefAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (balanceOfRef sender) = .ok (amm4TransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, sender, evalExpr?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, valueToKey?, envValue, hsrc, amm4TransferSenderRef]

def amm4CtorPostGuardAfterSender (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (amm4TransferSenderSlot I) (UInt256.ofNat (liquidity.toNat - 1000))

theorem amm4CtorPostGuardAssignSender
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (hfit : liquidity.toNat < UInt256.size)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm .storage (balanceOfRef sender)
      (.int (Int.ofNat (liquidity.toNat - 1000))) =
      .ok (⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩,
        amm4CtorPostGuardAfterSender evm I liquidity) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (evm' := amm4CtorPostGuardAfterSender evm I liquidity)
    (slot := balanceOfRef sender) (n := Int.ofNat (liquidity.toNat - 1000))
    (ty := .elem (.int uint256Int))
    (er := amm4TransferSenderRef I) (loc := wordLoc (amm4TransferSenderSlot I))
    (amm4CtorAfterSquareLocals_balanceOf_none t0 t1 liquidity ret1 ret2)
    (amm4CtorEvalSenderRefAfterSquare t0 t1 liquidity ret1 ret2 evm I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      amm4TransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
  have hword : (UInt256.ofNat (liquidity.toNat - 1000)).toNat =
      liquidity.toNat - 1000 :=
    ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)
  simpa only [amm4CtorPostGuardAfterSender, hword] using
    amm4StorageLocStore_uint256 evm (amm4TransferSenderSlot I)
      (UInt256.ofNat (liquidity.toNat - 1000))

theorem amm4CtorPostGuardSenderStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (hfit : liquidity.toNat < UInt256.size)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecStmt config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.assign .storage (balanceOfRef sender) (.var "baseSupply"))
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (amm4CtorPostGuardAfterSender evm I liquidity)) := by
  exact ExecStmt.assign
    (amm4CtorEvalBaseSupplyAfterSquare t0 t1 liquidity ret1 ret2 evm)
    (amm4CtorPostGuardAssignSender t0 t1 liquidity ret1 ret2 evm I hfit hsrc)

theorem amm4CtorSourcePostGuardStorageSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm2 : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hfit : liquidity.toNat < UInt256.size)
    (howner : evm2.executionEnv.codeOwner = I.codeOwner)
    (hsrc : evm2.executionEnv.source = I.source)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))])) ++
        [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
         .require (.binary .gt (.var "liquidity") (.intLit 0))])
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))])) ++
        [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
         .require (.binary .gt (.var "liquidity") (.intLit 0))]) ++
        [.assign .storage totalSupplyRef (.var "liquidity"),
         .assign .storage (balanceOfRef thisAddr) (.intLit minimumLiquidity),
         .assign .storage (balanceOfRef sender) (.var "baseSupply")])
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (amm4CtorPostGuardAfterSender
          (amm4CtorPostGuardAfterSelf
            (amm4CtorPostGuardAfterSupply evm2 liquidity)) I liquidity)) := by
  let evm3 := amm4CtorPostGuardAfterSupply evm2 liquidity
  let evm4 := amm4CtorPostGuardAfterSelf evm3
  let evm5 := amm4CtorPostGuardAfterSender evm4 I liquidity
  have howner3 : evm3.executionEnv.codeOwner = I.codeOwner := by
    simpa [evm3, amm4CtorPostGuardAfterSupply, storageStore_executionEnv] using howner
  have hsrc4 : evm4.executionEnv.source = I.source := by
    simpa [evm4, evm3, amm4CtorPostGuardAfterSelf,
      amm4CtorPostGuardAfterSupply, storageStore_executionEnv] using hsrc
  have htail : ExecBlock config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2
      [.assign .storage totalSupplyRef (.var "liquidity"),
       .assign .storage (balanceOfRef thisAddr) (.intLit minimumLiquidity),
       .assign .storage (balanceOfRef sender) (.var "baseSupply")]
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm5) := by
    apply ExecBlock.consNormal
      (amm4CtorPostGuardSupplyStmt t0 t1 liquidity ret1 ret2 evm2 h0 hfit)
    apply ExecBlock.consNormal
      (amm4CtorPostGuardSelfStmt t0 t1 liquidity ret1 ret2 evm3 I howner3)
    apply ExecBlock.consNormal
      (amm4CtorPostGuardSenderStmt t0 t1 liquidity ret1 ret2 evm4 I hfit hsrc4)
    exact ExecBlock.nil
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
