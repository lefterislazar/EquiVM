import Benchmarks.ActAmm.ConstructorArithmeticSource
import Benchmarks.ActAmm.ConstructorPostGuardSender

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorAfterSquareLocals_supply_none
    (t0 t1 : AccountAddress) (liquidity : Int) (ret1 ret2 : ByteArray) :
    (ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2).get? "totalSupply" = none := by
  simp only [ammCtorAfterSquareLocals, ammCtorAfterProductLocals,
    ammCtorAfterInitialBalance0Locals, ammCtorAfterInitialBalance1Locals,
    ammCtorAfterBaseLocals]
  repeat rw [store_get_ne _ _ (by decide)]
  simp [ammCtorLocals]

def ammCtorPostGuardAfterSupply (evm : EVM.State) (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.ofNat liquidity.toNat)

theorem ammCtorPostGuardAssignSupply
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hfit : liquidity.toNat < UInt256.size) :
    assignStorageRef? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm .storage totalSupplyRef (.int liquidity) =
      .ok (⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩,
        ammCtorPostGuardAfterSupply evm liquidity) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (evm' := ammCtorPostGuardAfterSupply evm liquidity)
    (slot := totalSupplyRef) (n := liquidity)
    (ty := .elem (.int uint256Int))
    (er := ({ base := "totalSupply", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨0⟩)
    (ammCtorAfterSquareLocals_supply_none t0 t1 liquidity ret1 ret2)
    (by simp [evalStorageRef, evalStorageRefSteps, totalSupplyRef,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
  have hword : (UInt256.ofNat liquidity.toNat).toNat = liquidity.toNat :=
    ulit_toNat' _ hfit
  have hliq : (Int.ofNat liquidity.toNat) = liquidity := Int.toNat_of_nonneg h0
  simpa only [ammCtorPostGuardAfterSupply, hword, hliq] using
    ammStorageLocStore_uint256 evm ⟨0⟩ (UInt256.ofNat liquidity.toNat)

theorem ammCtorPostGuardSupplyStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State)
    (h0 : 0 ≤ liquidity) (hfit : liquidity.toNat < UInt256.size) :
    ExecStmt config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.assign .storage totalSupplyRef (.var "liquidity"))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (ammCtorPostGuardAfterSupply evm liquidity)) := by
  exact ExecStmt.assign
    (ammCtorEvalLiquidityAfterSquare t0 t1 liquidity ret1 ret2 evm)
    (ammCtorPostGuardAssignSupply t0 t1 liquidity ret1 ret2 evm h0 hfit)

def ammCtorSelfSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (.address I.codeOwner)

theorem ammCtorSelfSlot_eq_solc (I : ExecutionEnv) :
    solcMappingSlot ⟨1⟩ (UInt256.ofNat I.codeOwner.val) =
      ammCtorSelfSlot I := by
  unfold ammCtorSelfSlot balanceOfSlot mapSlot solcMappingSlot
  rw [ammSource_keyValueToWord I.codeOwner]

def ammCtorSelfRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "balanceOf", steps := [.mindex (.address I.codeOwner)] }

theorem ammCtorAfterSquareLocals_balanceOf_none
    (t0 t1 : AccountAddress) (liquidity : Int) (ret1 ret2 : ByteArray) :
    (ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2).get? "balanceOf" = none := by
  simp only [ammCtorAfterSquareLocals, ammCtorAfterProductLocals,
    ammCtorAfterInitialBalance0Locals, ammCtorAfterInitialBalance1Locals,
    ammCtorAfterBaseLocals]
  repeat rw [store_get_ne _ _ (by decide)]
  simp [ammCtorLocals]

theorem ammCtorEvalSelfRef
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalStorageRef config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (balanceOfRef thisAddr) = .ok (ammCtorSelfRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, thisAddr, evalExpr?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, valueToKey?, envValue, howner, ammCtorSelfRef]

def ammCtorPostGuardAfterSelf (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (balanceOfSlot (.address evm.executionEnv.codeOwner)) ⟨1000⟩

theorem ammCtorPostGuardAssignSelf
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    assignStorageRef? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm .storage (balanceOfRef thisAddr) (.int 1000) =
      .ok (⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩,
        ammCtorPostGuardAfterSelf evm) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (evm' := ammCtorPostGuardAfterSelf evm)
    (slot := balanceOfRef thisAddr) (n := 1000)
    (ty := .elem (.int uint256Int))
    (er := ammCtorSelfRef I) (loc := wordLoc (ammCtorSelfSlot I))
    (ammCtorAfterSquareLocals_balanceOf_none t0 t1 liquidity ret1 ret2)
    (ammCtorEvalSelfRef t0 t1 liquidity ret1 ret2 evm I howner)
    (by simp [storageTypeAt?, contract, storageDecls,
      ammCtorSelfRef, uint256St, storageTypeStep?])
    (by rfl)
  simpa only [ammCtorPostGuardAfterSelf, ammCtorSelfSlot,
    ammCtorSelfRef, howner] using
    ammStorageLocStore_uint256 evm
      (balanceOfSlot (.address evm.executionEnv.codeOwner)) ⟨1000⟩

theorem ammCtorPostGuardSelfStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    ExecStmt config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.assign .storage (balanceOfRef thisAddr) (.intLit minimumLiquidity))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (ammCtorPostGuardAfterSelf evm)) := by
  exact ExecStmt.assign (by simp [evalExpr?, minimumLiquidity, pure])
    (ammCtorPostGuardAssignSelf t0 t1 liquidity ret1 ret2 evm I howner)

theorem ammCtorEvalBaseSupplyAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (.var "baseSupply") =
      .ok (.int (Int.ofNat (liquidity.toNat - 1000))) := by
  simp only [evalExpr?, ammCtorAfterSquareLocals,
    ammCtorAfterProductLocals, ammCtorAfterInitialBalance0Locals,
    ammCtorAfterInitialBalance1Locals]
  repeat rw [store_get_ne _ _ (by decide)]
  simpa only [evalExpr?] using ammCtorEvalBaseSupply t0 t1 liquidity evm

theorem ammCtorEvalSenderRefAfterSquare
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm (balanceOfRef sender) = .ok (ammTransferSenderRef I) := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    balanceOfRef, sender, evalExpr?, EvalResult.bind, EvalResult.ofOption,
    bind, pure, valueToKey?, envValue, hsrc, ammTransferSenderRef]

def ammCtorPostGuardAfterSender (evm : EVM.State) (I : ExecutionEnv)
    (liquidity : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (ammTransferSenderSlot I) (UInt256.ofNat (liquidity.toNat - 1000))

theorem ammCtorPostGuardAssignSender
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (hfit : liquidity.toNat < UInt256.size)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm .storage (balanceOfRef sender)
      (.int (Int.ofNat (liquidity.toNat - 1000))) =
      .ok (⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩,
        ammCtorPostGuardAfterSender evm I liquidity) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩)
    (evm := evm) (evm' := ammCtorPostGuardAfterSender evm I liquidity)
    (slot := balanceOfRef sender) (n := Int.ofNat (liquidity.toNat - 1000))
    (ty := .elem (.int uint256Int))
    (er := ammTransferSenderRef I) (loc := wordLoc (ammTransferSenderSlot I))
    (ammCtorAfterSquareLocals_balanceOf_none t0 t1 liquidity ret1 ret2)
    (ammCtorEvalSenderRefAfterSquare t0 t1 liquidity ret1 ret2 evm I hsrc)
    (by simp [storageTypeAt?, contract, storageDecls,
      ammTransferSenderRef, uint256St, storageTypeStep?])
    (by rfl)
  have hword : (UInt256.ofNat (liquidity.toNat - 1000)).toNat =
      liquidity.toNat - 1000 :=
    ulit_toNat' _ (lt_of_le_of_lt (Nat.sub_le _ _) hfit)
  simpa only [ammCtorPostGuardAfterSender, hword] using
    ammStorageLocStore_uint256 evm (ammTransferSenderSlot I)
      (UInt256.ofNat (liquidity.toNat - 1000))

theorem ammCtorPostGuardSenderStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) (evm : EVM.State) (I : ExecutionEnv)
    (hfit : liquidity.toNat < UInt256.size)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecStmt config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm
      (.assign .storage (balanceOfRef sender) (.var "baseSupply"))
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (ammCtorPostGuardAfterSender evm I liquidity)) := by
  exact ExecStmt.assign
    (ammCtorEvalBaseSupplyAfterSquare t0 t1 liquidity ret1 ret2 evm)
    (ammCtorPostGuardAssignSender t0 t1 liquidity ret1 ret2 evm I hfit hsrc)

theorem ammCtorSourcePostGuardStorageSuccess
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
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((((((ammCtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"]) ++
        [.letDecl "balanceProduct" (some uint256)
          (checkedMul (.var "initialBalance0") (.var "initialBalance1"))]) ++
        [.letDecl "liquiditySquared" (some uint256)
          (checkedMul (.var "liquidity") (.var "liquidity"))])) ++
        [.require (.binary .eq (.var "liquiditySquared") (.var "balanceProduct")),
         .require (.binary .gt (.var "liquidity") (.intLit 0))])
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2)) :
    ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (((((((ammCtorSourceStoredPrefix ++
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
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (ammCtorPostGuardAfterSender
          (ammCtorPostGuardAfterSelf
            (ammCtorPostGuardAfterSupply evm2 liquidity)) I liquidity)) := by
  let evm3 := ammCtorPostGuardAfterSupply evm2 liquidity
  let evm4 := ammCtorPostGuardAfterSelf evm3
  let evm5 := ammCtorPostGuardAfterSender evm4 I liquidity
  have howner3 : evm3.executionEnv.codeOwner = I.codeOwner := by
    simpa [evm3, ammCtorPostGuardAfterSupply, storageStore_executionEnv] using howner
  have hsrc4 : evm4.executionEnv.source = I.source := by
    simpa [evm4, evm3, ammCtorPostGuardAfterSelf,
      ammCtorPostGuardAfterSupply, storageStore_executionEnv] using hsrc
  have htail : ExecBlock config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm2
      [.assign .storage totalSupplyRef (.var "liquidity"),
       .assign .storage (balanceOfRef thisAddr) (.intLit minimumLiquidity),
       .assign .storage (balanceOfRef sender) (.var "baseSupply")]
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩ evm5) := by
    apply ExecBlock.consNormal
      (ammCtorPostGuardSupplyStmt t0 t1 liquidity ret1 ret2 evm2 h0 hfit)
    apply ExecBlock.consNormal
      (ammCtorPostGuardSelfStmt t0 t1 liquidity ret1 ret2 evm3 I howner3)
    apply ExecBlock.consNormal
      (ammCtorPostGuardSenderStmt t0 t1 liquidity ret1 ret2 evm4 I hfit hsrc4)
    exact ExecBlock.nil
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
