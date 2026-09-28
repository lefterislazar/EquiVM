import Benchmarks.ActAmm.ConstructorReserve0Trace
import Benchmarks.ActAmm.ConstructorPostGuardSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem ammCtorAfterSquareLocals_token0_none
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) :
    (ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2).get? "token0" = none := by
  simp only [ammCtorAfterSquareLocals, ammCtorAfterProductLocals,
    ammCtorAfterInitialBalance0Locals, ammCtorAfterInitialBalance1Locals]
  repeat rw [store_get_ne _ _ (by decide)]
  exact ammCtorAfterBaseLocals_token0_none t0 t1 liquidity

theorem ammCtorThirdCallSourceReceiver
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    evalExpr? config
      { contract := contract,
        locals := ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2 }
      (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I) (.storage token0Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (ammCtorInitialToken0Target I σ_evm))) := by
  have hrecv := ammMintEvalToken0
    (evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I)
    (locals := ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
    (ammCtorAfterSquareLocals_token0_none t0 t1 liquidity ret1 ret2)
  have htarget := ammCtorInitialToken0Target_equiv I σ_evm σ_solm hAccounts
  rw [htarget]
  simpa only [initState, Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
    Ethereum.Account.lookupStorage, ammCtorInitialToken0Target,
    ammCtorStorageWord] using hrecv

def ammCtorSourcePostGuardPrefix :=
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

theorem ammSolmCtorExecReverts_thirdCallFailed
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hprefix : ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ammCtorSourcePostGuardPrefix
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (ammCtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (false, evm', ret3) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := ammCtorThirdCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 hAccounts
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := ammCtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      evm (ammCtorSourcePostGuardPrefix ++
        tokenBalance (.storage token0Ref) "reserveBalance0" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallFailure
        (sendVal := 0) (evm' := evm') (out := ret3)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [ammCtorAddressVal] using hcall)))

theorem ammSolmCtorExecReverts_thirdCallShort
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : ret3.size < 32)
    (hprefix : ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ammCtorSourcePostGuardPrefix
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (ammCtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret3) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := ammCtorThirdCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 hAccounts
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := ammCtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      evm (ammCtorSourcePostGuardPrefix ++
        tokenBalance (.storage token0Ref) "reserveBalance0" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        (sendVal := 0) (evm' := evm') (out := ret3)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [ammCtorAddressVal] using hcall)
        (ammMintDecodeBalance_short hshort)))

def ammCtorAfterReserveBalance0Locals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) : Store :=
  (ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2).insert
    "reserveBalance0" (.int (Int.ofNat
      (fromByteArrayBigEndian (ret3.extract 0 32))))

theorem ammCtorSourceReserveBalance0Success
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlo : 32 ≤ ret3.size) (hbound : ret3.size < 2 ^ 138)
    (hprefix : ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ammCtorSourcePostGuardPrefix
      (.ok ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (ammCtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret3) false) :
    ExecBlock config
      ⟨contract, ammCtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (ammCtorSourcePostGuardPrefix ++
        [tokenBalance (.storage token0Ref) "reserveBalance0"])
      (.ok ⟨contract,
        ammCtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3⟩ evm') := by
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := ammCtorThirdCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 hAccounts
  have hargs := ammMintEvalBalanceArgs (evm := evm1)
    (locals := ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
  have hdec := ammMintDecodeBalance_ok hlo
    (by omega : ret3.size < 2 ^ 255)
  have htail : ExecBlock config
      ⟨contract, ammCtorAfterSquareLocals t0 t1 liquidity ret1 ret2⟩
      evm1 [tokenBalance (.storage token0Ref) "reserveBalance0"]
      (.ok ⟨contract,
        ammCtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3⟩
        evm') := by
    simp only [tokenBalance]
    simpa [ammCtorAfterReserveBalance0Locals, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (sendVal := 0) (evm' := evm') (out := ret3)
          hreceiver (by simp [evalExpr?, pure]) hargs
          (by simpa only [ammCtorAddressVal] using hcall) hdec)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm
