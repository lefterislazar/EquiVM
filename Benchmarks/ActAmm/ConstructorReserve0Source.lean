import Benchmarks.ActAmm.ConstructorThirdCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorAfterReserveBalance0Locals_reserve0_none
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) :
    (ammCtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3).get?
      "reserve0" = none := by
  rw [ammCtorAfterReserveBalance0Locals,
    store_get_ne (ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
      (k := "reserveBalance0") (a := "reserve0") _ (by decide)]
  simp only [ammCtorAfterSquareLocals, ammCtorAfterProductLocals,
    ammCtorAfterInitialBalance0Locals, ammCtorAfterInitialBalance1Locals,
    ammCtorAfterBaseLocals]
  repeat rw [store_get_ne _ _ (by decide)]
  simp [ammCtorLocals]

theorem ammCtorEvalReserveBalance0
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) (evm : EVM.State) :
    evalExpr? config
      ⟨contract, ammCtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩ evm (.var "reserveBalance0") =
      .ok (.int (Int.ofNat
        (fromByteArrayBigEndian (ret3.extract 0 32)))) := by
  simp [evalExpr?, ammCtorAfterReserveBalance0Locals,
    EvalResult.ofOption]

def ammCtorAfterReserve0Store (evm : EVM.State)
    (ret3 : ByteArray) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (UInt256.ofNat (fromByteArrayBigEndian (ret3.extract 0 32)))

theorem ammCtorAssignReserve0
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) (evm : EVM.State)
    (hlo3 : 32 ≤ ret3.size) :
    assignStorageRef? config
      ⟨contract, ammCtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩ evm .storage reserve0Ref
      (.int (Int.ofNat (fromByteArrayBigEndian (ret3.extract 0 32)))) =
      .ok (⟨contract, ammCtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩, ammCtorAfterReserve0Store evm ret3) := by
  apply assignStorageRef_storage_scalar
    (cfg := config)
    (solm := ⟨contract, ammCtorAfterReserveBalance0Locals t0 t1 liquidity
      ret1 ret2 ret3⟩)
    (evm := evm) (evm' := ammCtorAfterReserve0Store evm ret3)
    (slot := reserve0Ref)
    (n := Int.ofNat (fromByteArrayBigEndian (ret3.extract 0 32)))
    (ty := .elem (.int uint256Int))
    (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
    (loc := wordLoc ⟨5⟩)
    (ammCtorAfterReserveBalance0Locals_reserve0_none
      t0 t1 liquidity ret1 ret2 ret3)
    (by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref,
      EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
  have hfit := fromByteArrayBigEndian_extract0_32_lt hlo3
  have hword : (UInt256.ofNat
      (fromByteArrayBigEndian (ret3.extract 0 32))).toNat =
      fromByteArrayBigEndian (ret3.extract 0 32) :=
    ulit_toNat' _ hfit
  simpa only [ammCtorAfterReserve0Store, hword] using
    ammStorageLocStore_uint256 evm ⟨5⟩
      (UInt256.ofNat (fromByteArrayBigEndian (ret3.extract 0 32)))

theorem ammCtorReserve0StoreStmt
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) (evm : EVM.State)
    (hlo3 : 32 ≤ ret3.size) :
    ExecStmt config
      ⟨contract, ammCtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩ evm
      (.assign .storage reserve0Ref (.var "reserveBalance0"))
      (.ok ⟨contract, ammCtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩ (ammCtorAfterReserve0Store evm ret3)) := by
  exact ExecStmt.assign
    (ammCtorEvalReserveBalance0 t0 t1 liquidity ret1 ret2 ret3 evm)
    (ammCtorAssignReserve0 t0 t1 liquidity ret1 ret2 ret3 evm hlo3)

theorem ammCtorSourceReserve0Stored
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    {evm3 : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hlo3 : 32 ≤ ret3.size)
    (hprefix : ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (ammCtorSourcePostGuardPrefix ++
        [tokenBalance (.storage token0Ref) "reserveBalance0"])
      (.ok ⟨contract,
        ammCtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3⟩
        evm3)) :
    ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((ammCtorSourcePostGuardPrefix ++
        [tokenBalance (.storage token0Ref) "reserveBalance0"]) ++
        [.assign .storage reserve0Ref (.var "reserveBalance0")])
      (.ok ⟨contract,
        ammCtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3⟩
        (ammCtorAfterReserve0Store evm3 ret3)) := by
  exact execBlock_append hprefix
    (ExecBlock.consNormal
      (ammCtorReserve0StoreStmt t0 t1 liquidity ret1 ret2 ret3 evm3 hlo3)
      ExecBlock.nil)

theorem ammCtorAfterReserve0Store_shape
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} (ret3 : ByteArray) :
    ammCtorAfterReserve0Store
      (initState createdAccounts genesisBlockHeader blocks σ σ₀
        (Sat256.ofUInt256 g) A I) ret3 =
      initState createdAccounts genesisBlockHeader blocks
        (ammCtorReserve0Map I σ
          (UInt256.ofNat (fromByteArrayBigEndian (ret3.extract 0 32))))
        σ₀ (Sat256.ofUInt256 g) A I := by
  simp [ammCtorAfterReserve0Store,
    ammCtorStorageStore_eq_updateAccountMap,
    ammCtorReserve0Map, initState]

theorem ammCtorReserve0Maps_equiv
    (I : ExecutionEnv) (σE σS : AccountMap) (reserve0 : UInt256)
    (hAccounts : accountMapEquiv σE σS) :
    accountMapEquiv (ammCtorReserve0Map I σE reserve0)
      (ammCtorReserve0Map I σS reserve0) := by
  unfold ammCtorReserve0Map
  exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ reserve0 hAccounts

end Benchmarks.ActAmm
