import Benchmarks.ActAmm4.ConstructorFourthCallSource
import Benchmarks.ActAmm4.ConstructorReturnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorAfterReserveBalance1Locals_reserve1_none
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 ret4 : ByteArray) :
    (amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4).get?
      "reserve1" = none := by
  rw [amm4CtorAfterReserveBalance1Locals,
    store_get_ne (amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
      ret1 ret2 ret3)
      (k := "reserveBalance1") (a := "reserve1") _ (by decide)]
  simp only [amm4CtorAfterReserveBalance0Locals, amm4CtorAfterSquareLocals,
    amm4CtorAfterProductLocals, amm4CtorAfterInitialBalance0Locals,
    amm4CtorAfterInitialBalance1Locals, amm4CtorAfterBaseLocals]
  repeat rw [store_get_ne _ _ (by decide)]
  simp [amm4CtorLocals]

theorem amm4CtorEvalReserveBalance1
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 ret4 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, amm4CtorAfterReserveBalance1Locals t0 t1 liquidity
        ret1 ret2 ret3 ret4⟩ evm (.var "reserveBalance1") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (ret4.extract 0 32)))) := by
  simp [evalExpr?, amm4CtorAfterReserveBalance1Locals,
    EvalResult.ofOption]

def amm4CtorAfterReserve1Store (evm : EVM.State)
    (ret4 : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (UInt256.ofNat (fromByteArrayBigEndian (ret4.extract 0 32)))

theorem amm4CtorAssignReserve1
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 ret4 : ByteArray) (evm : EVM.State)
    (hlo4 : 32 ≤ ret4.size) :
    assignStorageRef? config
      ⟨contract, amm4CtorAfterReserveBalance1Locals t0 t1 liquidity
        ret1 ret2 ret3 ret4⟩ evm .storage reserve1Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (ret4.extract 0 32)))) =
      .ok (⟨contract, amm4CtorAfterReserveBalance1Locals t0 t1 liquidity
        ret1 ret2 ret3 ret4⟩, amm4CtorAfterReserve1Store evm ret4) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, amm4CtorAfterReserveBalance1Locals t0 t1 liquidity
      ret1 ret2 ret3 ret4⟩)
    (evm := evm) (evm' := amm4CtorAfterReserve1Store evm ret4)
    (slot := reserve1Ref)
    (n := Int.ofNat (fromByteArrayBigEndian (ret4.extract 0 32)))
    (ty := .elem (.int uint256Int))
    (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨6⟩)
    (amm4CtorAfterReserveBalance1Locals_reserve1_none
      t0 t1 liquidity ret1 ret2 ret3 ret4)
    (by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
  have hfit := fromByteArrayBigEndian_extract0_32_lt hlo4
  have hword : (UInt256.ofNat
      (fromByteArrayBigEndian (ret4.extract 0 32))).toNat =
      fromByteArrayBigEndian (ret4.extract 0 32) :=
    ulit_toNat' _ hfit
  simpa only [amm4CtorAfterReserve1Store, hword] using
    amm4StorageLocStore_uint256 evm ⟨6⟩
      (UInt256.ofNat (fromByteArrayBigEndian (ret4.extract 0 32)))

theorem amm4CtorReserve1StoreStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 ret4 : ByteArray) (evm : EVM.State)
    (hlo4 : 32 ≤ ret4.size) :
    ExecStmt config
      ⟨contract, amm4CtorAfterReserveBalance1Locals t0 t1 liquidity
        ret1 ret2 ret3 ret4⟩ evm
      (.assign .storage reserve1Ref (.var "reserveBalance1"))
      (.ok ⟨contract, amm4CtorAfterReserveBalance1Locals t0 t1 liquidity
        ret1 ret2 ret3 ret4⟩ (amm4CtorAfterReserve1Store evm ret4)) := by
  exact ExecStmt.assign
    (amm4CtorEvalReserveBalance1 t0 t1 liquidity ret1 ret2 ret3 ret4 evm)
    (amm4CtorAssignReserve1 t0 t1 liquidity ret1 ret2 ret3 ret4 evm hlo4)

theorem amm4CtorSourceReserve1Stored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    {evm4 : EVM.State} {ret1 ret2 ret3 ret4 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hlo4 : 32 ≤ ret4.size)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (amm4CtorSourceReserve0Prefix ++
        [tokenBalance (.storage token1Ref) "reserveBalance1"])
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4⟩
        evm4)) :
    ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((amm4CtorSourceReserve0Prefix ++
        [tokenBalance (.storage token1Ref) "reserveBalance1"]) ++
        [.assign .storage reserve1Ref (.var "reserveBalance1")])
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4⟩
        (amm4CtorAfterReserve1Store evm4 ret4)) := by
  exact execBlock_append hprefix
    (ExecBlock.consNormal
      (amm4CtorReserve1StoreStmt t0 t1 liquidity ret1 ret2 ret3 ret4 evm4 hlo4)
      ExecBlock.nil)

theorem amm4CtorAfterReserve1Store_shape
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} (ret4 : ByteArray) :
    amm4CtorAfterReserve1Store
      (initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I) ret4 =
      initState createdAccounts genesisBlockHeader blocks
        (amm4CtorReserve1Map I σ
          (UInt256.ofNat (fromByteArrayBigEndian (ret4.extract 0 32))))
        σ₀ (Sat256.ofUInt256 g) A I := by
  simp [amm4CtorAfterReserve1Store,
    amm4CtorStorageStore_eq_updateAccountMap,
    amm4CtorReserve1Map, initState]

theorem amm4CtorReserve1Maps_equiv
    (I : ExecutionEnv) (σE σS : AccountMap) (reserve1 : UInt256)
    (hAccounts : accountMapEquiv σE σS) :
    accountMapEquiv (amm4CtorReserve1Map I σE reserve1)
      (amm4CtorReserve1Map I σS reserve1) := by
  unfold amm4CtorReserve1Map
  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨6⟩ reserve1 hAccounts

theorem amm4SolmCtorExecSuccess_afterReserves
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    {evmFinal : EVM.State} {ret1 ret2 ret3 ret4 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((amm4CtorSourceReserve0Prefix ++
        [tokenBalance (.storage token1Ref) "reserveBalance1"]) ++
        [.assign .storage reserve1Ref (.var "reserveBalance1")])
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4⟩
        evmFinal)) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I
      (.returned
        ⟨contract,
          amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4⟩
        evmFinal none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σstart σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl,
      amm4CtorSourceReserve0Prefix, amm4CtorSourcePostGuardPrefix,
      amm4CtorSourceStoredPrefix, nonpayable] using
      (ExecFuncBody.execBlockOK hprefix)

end Benchmarks.ActAmm4
