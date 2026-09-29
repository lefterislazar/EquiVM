import Benchmarks.ActAmm4.ConstructorFourthCall
import Benchmarks.ActAmm4.ConstructorReserve0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorFinalToken1Target_equiv
    (I : ExecutionEnv) (σE σS : AccountMap)
    (hAccounts : accountMapEquiv σE σS) :
    amm4CtorFinalToken1Target I σE = amm4CtorFinalToken1Target I σS := by
  unfold amm4CtorFinalToken1Target
  rw [show amm4CtorStorageWord σE I ⟨4⟩ =
      amm4CtorStorageWord σS I ⟨4⟩ from
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩]

theorem amm4CtorAfterReserveBalance0Locals_token1_none
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray) :
    (amm4CtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3).get?
      "token1" = none := by
  rw [amm4CtorAfterReserveBalance0Locals,
    store_get_ne (amm4CtorAfterSquareLocals t0 t1 liquidity ret1 ret2)
      (k := "reserveBalance0") (a := "token1") _ (by decide)]
  simp only [amm4CtorAfterSquareLocals, amm4CtorAfterProductLocals,
    amm4CtorAfterInitialBalance0Locals, amm4CtorAfterInitialBalance1Locals]
  repeat rw [store_get_ne _ _ (by decide)]
  exact amm4CtorAfterBaseLocals_token1_none t0 t1 liquidity

theorem amm4CtorFourthCallSourceReceiver
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 : ByteArray)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
          ret1 ret2 ret3 }
      (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I) (.storage token1Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (amm4CtorFinalToken1Target I σ_evm))) := by
  have hrecv := amm4MintEvalToken1
    (evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I)
    (locals := amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
      ret1 ret2 ret3)
    (amm4CtorAfterReserveBalance0Locals_token1_none
      t0 t1 liquidity ret1 ret2 ret3)
  have htarget := amm4CtorFinalToken1Target_equiv I σ_evm σ_solm hAccounts
  rw [htarget]
  simpa only [initState, Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
    Ethereum.Account.lookupStorage, amm4CtorFinalToken1Target,
    amm4CtorStorageWord] using hrecv

theorem amm4CtorFourthCallSourceTransport
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A : Substate} {I : ExecutionEnv} {z : Bool}
    {evm'_evm : EVM.State} {ret : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall : typedCallViaEVM config
      (initState createdAccounts genesisBlockHeader blocks σ_evm σ₀
        (Sat256.ofUInt256 g) A I)
      (AccountAddress.ofUInt256 (amm4CtorFinalToken1Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (z, evm'_evm, ret) false) :
    ∃ σ'_solm,
      typedCallViaEVM config
        (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (amm4CtorFinalToken1Target I σ_evm))
        "balanceOf" 0 [.address I.codeOwner]
        (z, { initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := evm'_evm.substate
          createdAccounts := evm'_evm.createdAccounts }, ret) false ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  obtain ⟨σ'_solm, hcall', hequiv⟩ :=
    amm4TypedCallTransport
      (evmS := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I)
      hcall (by simpa [initState] using hAccounts)
      rfl rfl rfl rfl rfl rfl
  exact ⟨σ'_solm, by simpa [initState] using hcall', hequiv⟩

def amm4CtorSourceReserve0Prefix :=
  (amm4CtorSourcePostGuardPrefix ++
    [tokenBalance (.storage token0Ref) "reserveBalance0"]) ++
    [.assign .storage reserve0Ref (.var "reserveBalance0")]

theorem amm4SolmCtorExecReverts_fourthCallFailed
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 ret4 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      amm4CtorSourceReserve0Prefix
      (.ok ⟨contract, amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (amm4CtorFinalToken1Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (false, evm', ret4) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := amm4CtorFourthCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 ret3 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
      ret1 ret2 ret3)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      evm (amm4CtorSourceReserve0Prefix ++
        tokenBalance (.storage token1Ref) "reserveBalance1" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallFailure
        (sendVal := 0) (evm' := evm') (out := ret4)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)))

theorem amm4SolmCtorExecReverts_fourthCallShort
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 ret4 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : ret4.size < 32)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      amm4CtorSourceReserve0Prefix
      (.ok ⟨contract, amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (amm4CtorFinalToken1Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret4) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := amm4CtorFourthCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 ret3 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
      ret1 ret2 ret3)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      evm (amm4CtorSourceReserve0Prefix ++
        tokenBalance (.storage token1Ref) "reserveBalance1" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        (sendVal := 0) (evm' := evm') (out := ret4)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)
        (amm4MintDecodeBalance_short hshort)))

def amm4CtorAfterReserveBalance1Locals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 ret3 ret4 : ByteArray) : Store :=
  (amm4CtorAfterReserveBalance0Locals t0 t1 liquidity ret1 ret2 ret3).insert
    "reserveBalance1" (.int (Int.ofNat
      (fromByteArrayBigEndian (ret4.extract 0 32))))

theorem amm4CtorSourceReserveBalance1Success
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap} {g : UInt256}
    {A Apre : Substate} {I : ExecutionEnv}
    {evm' : EVM.State} {ret1 ret2 ret3 ret4 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlo : 32 ≤ ret4.size) (hbound : ret4.size < 2 ^ 138)
    (hprefix : ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      amm4CtorSourceReserve0Prefix
      (.ok ⟨contract, amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) Apre I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) Apre I)
      (AccountAddress.ofUInt256 (amm4CtorFinalToken1Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret4) false) :
    ExecBlock config
      ⟨contract, amm4CtorLocals t0 t1 liquidity⟩
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (amm4CtorSourceReserve0Prefix ++
        [tokenBalance (.storage token1Ref) "reserveBalance1"])
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4⟩
        evm') := by
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) Apre I
  have hreceiver := amm4CtorFourthCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := Apre) (I := I)
    t0 t1 liquidity ret1 ret2 ret3 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
      ret1 ret2 ret3)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : ret4.size < 2 ^ 255)
  have htail : ExecBlock config
      ⟨contract, amm4CtorAfterReserveBalance0Locals t0 t1 liquidity
        ret1 ret2 ret3⟩
      evm1 [tokenBalance (.storage token1Ref) "reserveBalance1"]
      (.ok ⟨contract,
        amm4CtorAfterReserveBalance1Locals t0 t1 liquidity ret1 ret2 ret3 ret4⟩
        evm') := by
    simp only [tokenBalance]
    simpa [amm4CtorAfterReserveBalance1Locals, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (sendVal := 0) (evm' := evm') (out := ret4)
          hreceiver (by simp [evalExpr?, pure]) hargs
          (by simpa only [amm4CtorAddressVal] using hcall) hdec)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
