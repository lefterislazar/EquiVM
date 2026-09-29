import Benchmarks.ActAmm4.ConstructorSecondCall
import Benchmarks.ActAmm4.ConstructorFirstCallSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorInitialToken0Target_equiv
    (I : ExecutionEnv) (σ_evm σ_solm : AccountMap)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    amm4CtorInitialToken0Target I σ_evm =
      amm4CtorInitialToken0Target I σ_solm := by
  unfold amm4CtorInitialToken0Target
  rw [show amm4CtorStorageWord σ_evm I ⟨3⟩ =
      amm4CtorStorageWord σ_solm I ⟨3⟩ from
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩]

theorem amm4CtorAfterInitialBalance1Locals_token0_none
    (t0 t1 : AccountAddress) (liquidity : Int) (ret : ByteArray) :
    (amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret).get? "token0" = none := by
  rw [amm4CtorAfterInitialBalance1Locals,
    store_get_ne (amm4CtorAfterBaseLocals t0 t1 liquidity)
      (k := "initialBalance1") (a := "token0") _ (by decide)]
  exact amm4CtorAfterBaseLocals_token0_none t0 t1 liquidity

theorem amm4CtorSecondCallSourceReceiver
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int) (ret1 : ByteArray)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    evalExpr? config
      { contract := contract,
        locals := amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1 }
      (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I) (.storage token0Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (amm4CtorInitialToken0Target I σ_evm))) := by
  have hrecv := amm4MintEvalToken0
    (evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I)
    (locals := amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1)
    (amm4CtorAfterInitialBalance1Locals_token0_none t0 t1 liquidity ret1)
  have htarget := amm4CtorInitialToken0Target_equiv I σ_evm σ_solm hAccounts
  rw [htarget]
  simpa only [initState, Solm.EVM.storageLoad, Ethereum.State.lookupAccount,
    Ethereum.Account.lookupStorage, amm4CtorInitialToken0Target,
    amm4CtorStorageWord] using hrecv

theorem amm4CtorSecondCallSourceTransport
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {z : Bool}
    {evm'_evm : EVM.State}
    {ret : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall : typedCallViaEVM config
      (initState createdAccounts genesisBlockHeader blocks σ_evm σ₀
        (Sat256.ofUInt256 g) A I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (z, evm'_evm, ret) false) :
    ∃ σ'_solm,
      typedCallViaEVM config
        (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I)
        (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
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

theorem amm4CtorFirstCallSourcePost_shape
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ σs σ₀ : AccountMap}
    {g : UInt256}
    {A A1 : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := amm4CtorAfterSupply evm liquidity
    let evm2 := amm4CtorAfterSender evm1 I liquidity
    let evm3 := amm4CtorAfterToken0 evm2 t0
    let evm4 := amm4CtorAfterToken1 evm3 t1
    { evm4 with accountMap := σs, substate := A1, createdAccounts := cA } =
      initState cA genesisBlockHeader blocks σs σ₀ (Sat256.ofUInt256 g) A1 I := by
  intro evm evm1 evm2 evm3 evm4
  have hshape := amm4CtorStoredSourceState_shape
    (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader) (blocks := blocks)
    (σ := σ) (σ₀ := σ₀) (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit
  change evm4 = { evm with accountMap := amm4CtorToken1Storage I σ (EVM.word liquidity.toNat) t0 t1 } at hshape
  rw [hshape]
  simp [evm, initState]

theorem amm4SolmCtorExecReverts_secondCallFailed
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A A1 : Substate}
    {I : ExecutionEnv}
    {evm' : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"])
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1 }
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A1 I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A1 I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (false, evm', ret2) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) A1 I
  have hreceiver := amm4CtorSecondCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := A1) (I := I)
    t0 t1 liquidity ret1 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm ((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        tokenBalance (.storage token0Ref) "initialBalance0" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallFailure
        (sendVal := 0) (evm' := evm') (out := ret2)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)))

theorem amm4SolmCtorExecReverts_secondCallShort
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A A1 : Substate}
    {I : ExecutionEnv}
    {evm' : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : ret2.size < 32)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"])
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1 }
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A1 I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A1 I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret2) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σstart σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σstart σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) A1 I
  have hreceiver := amm4CtorSecondCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := A1) (I := I)
    t0 t1 liquidity ret1 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm ((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        tokenBalance (.storage token0Ref) "initialBalance0" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        (sendVal := 0) (evm' := evm') (out := ret2)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)
        (amm4MintDecodeBalance_short hshort)))

def amm4CtorAfterInitialBalance0Locals
    (t0 t1 : AccountAddress) (liquidity : Int)
    (ret1 ret2 : ByteArray) : Store :=
  (amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1).insert
    "initialBalance0" (.int (Int.ofNat (fromByteArrayBigEndian (ret2.extract 0 32))))

theorem amm4CtorSourceInitialBalance0Success
    {createdAccounts cA : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σstart σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A A1 : Substate}
    {I : ExecutionEnv}
    {evm' : EVM.State}
    {ret1 ret2 : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlo : 32 ≤ ret2.size) (hbound : ret2.size < 2 ^ 138)
    (hprefix : ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      (amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"])
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1 }
        (initState cA genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A1 I)))
    (hcall : typedCallViaEVM config
      (initState cA genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A1 I)
      (AccountAddress.ofUInt256 (amm4CtorInitialToken0Target I σ_evm))
      "balanceOf" 0 [.address I.codeOwner] (true, evm', ret2) false) :
    ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      (initState createdAccounts genesisBlockHeader blocks σstart σ₀
        (Sat256.ofUInt256 g) A I)
      ((amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"]) ++
        [tokenBalance (.storage token0Ref) "initialBalance0"])
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 } evm') := by
  let evm1 := initState cA genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) A1 I
  have hreceiver := amm4CtorSecondCallSourceReceiver
    (createdAccounts := cA) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := A1) (I := I)
    t0 t1 liquidity ret1 hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm1)
    (locals := amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : ret2.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals :=
        amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret1 }
      evm1 [tokenBalance (.storage token0Ref) "initialBalance0"]
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance0Locals t0 t1 liquidity ret1 ret2 } evm') := by
    simp only [tokenBalance]
    simpa [amm4CtorAfterInitialBalance0Locals, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (sendVal := 0) (evm' := evm') (out := ret2)
          hreceiver (by simp [evalExpr?, pure]) hargs
          (by simpa only [amm4CtorAddressVal] using hcall) hdec)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
