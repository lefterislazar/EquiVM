import Benchmarks.ActAmm4.ConstructorReserve0Trace
import Benchmarks.ActAmm4.ConstructorPostGuardSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorAfterSquareLocals_token0_none
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) :
    (amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2).get? "token0" = none := by
  simp only [amm4CtorAfterSquareLocals, amm4CtorAfterProductLocals,
    amm4CtorAfterInitialBalance0Locals, amm4CtorAfterInitialBalance1Locals]
  repeat rw [store_get_ne _ _ (by decide)]
  exact amm4CtorAfterBaseLocals_token0_none t0 t1 liquidity

theorem amm4CtorThirdCallSourceReceiver
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2 }
      (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I) (.storage token0Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (amm4CtorInitialToken0Target I σ_evm))) := by
  have hrecv := amm4MintEvalToken0
    (evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I)
    (locals := amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
    (amm4CtorAfterSquareLocals_token0_none t0 t1 liquidity ret1 ret2)
  have htarget := amm4CtorInitialToken0Target_equiv I σ_evm σ_solm hAccounts
  rw [htarget]
  simpa only [initState, Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
    Ethereum.Account.lookupStorage, amm4CtorInitialToken0Target,
    amm4CtorStorageWord] using hrecv

def amm4CtorSourcePostGuardPrefix :=
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

theorem amm4SolmCtorExecReverts_thirdCallFailed
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      amm4CtorSourcePostGuardPrefix
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (false, evm', ret3) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := amm4CtorThirdCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      evm (amm4CtorSourcePostGuardPrefix ++
        tokenBalance (.storage token0Ref) "reserveBalance0" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallFailure
        (sendVal := 0) (evm' := evm') (out := ret3)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)))

theorem amm4SolmCtorExecReverts_thirdCallShort
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : ret3.size < 32)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      amm4CtorSourcePostGuardPrefix
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret3) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := amm4CtorThirdCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      evm (amm4CtorSourcePostGuardPrefix ++
        tokenBalance (.storage token0Ref) "reserveBalance0" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        (sendVal := 0) (evm' := evm') (out := ret3)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)
        (amm4MintDecodeBalance_short hshort)))

def amm4CtorAfterReserveBalance0Locals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) : Store :=
  (amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2).insert
    "reserveBalance0" (.int (Int.ofNat
      (fromByteArrayBigEndian (ret3.extract 0 32))))

theorem amm4CtorSourceReserveBalance0Success
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlo : 32 ≤ ret3.size) (hbound : ret3.size < 2 ^ 138)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      amm4CtorSourcePostGuardPrefix
      (.ok ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret3) false) :
    ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (amm4CtorSourcePostGuardPrefix ++
        [tokenBalance (.storage token0Ref) "reserveBalance0"])
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3⟩ evm') := by
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := amm4CtorThirdCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : ret3.size < 2 ^ 255)
  have htail : ExecBlock config
      ⟨contract, amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm1 [tokenBalance (.storage token0Ref) "reserveBalance0"]
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3⟩
        evm') := by
    simp only [tokenBalance]
    simpa [amm4CtorAfterReserveBalance0Locals, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (sendVal := 0) (evm' := evm') (out := ret3)
          hreceiver (by simp [evalExpr?, pure]) hargs
          (by simpa only [amm4CtorAddressVal] using hcall) hdec)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
