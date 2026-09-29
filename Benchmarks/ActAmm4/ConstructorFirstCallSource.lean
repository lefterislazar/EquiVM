import Benchmarks.ActAmm4.ConstructorFirstCall
import Benchmarks.ActAmm4.ConstructorBridge
import Benchmarks.ActAmm4.MintSourceArithmetic
import Benchmarks.ActAmm4.MintCallTransport

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000000

theorem amm4CtorAddressVal (a : AccountAddress) : EVM.address a.val = a := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN, EVM.twoPow, AccountAddress.size]

theorem amm4CtorFirstCallSourceTransport
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
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall : typedCallViaEVM config
      (initState createdAccounts genesisBlockHeader blocks
        (amm4CtorToken1Storage I σ_evm (EVM.word liquidity.toNat) t0 t1)
        σ₀ (Sat256.ofUInt256 g) A I)
      (AccountAddress.ofUInt256
        (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1))
      "balanceOf" 0 [.address I.codeOwner] (z, evm'_evm, ret) false) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := amm4CtorAfterSupply evm liquidity
    let evm2 := amm4CtorAfterSender evm1 I liquidity
    let evm3 := amm4CtorAfterToken0 evm2 t0
    let evm4 := amm4CtorAfterToken1 evm3 t1
    ∃ σ'_solm,
      typedCallViaEVM config evm4
        (AccountAddress.ofUInt256
          (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1))
        "balanceOf" 0 [.address evm4.executionEnv.codeOwner]
        (z, { evm4 with
          accountMap := σ'_solm
          substate := evm'_evm.substate
          createdAccounts := evm'_evm.createdAccounts }, ret) false ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  intro evm evm1 evm2 evm3 evm4
  have hshape : evm4 =
      { evm with accountMap :=
        amm4CtorToken1Storage I σ_solm (EVM.word liquidity.toNat) t0 t1 } :=
    amm4CtorStoredSourceState_shape t0 t1 liquidity h0 hle hfit
  have heq : accountMapEquiv
      (amm4CtorToken1Storage I σ_evm (EVM.word liquidity.toNat) t0 t1)
      (amm4CtorToken1Storage I σ_solm (EVM.word liquidity.toNat) t0 t1) :=
    amm4CtorToken1Storage_equiv I σ_evm σ_solm
      (EVM.word liquidity.toNat) t0 t1 hAccounts
  obtain ⟨σ'_solm, hcall', hequiv⟩ :=
    amm4TypedCallTransport (evmS := evm4) hcall
      (by simpa [hshape, evm, initState] using heq)
      (by rw [hshape]; rfl)
      (by rw [hshape]; rfl)
      (by rw [hshape]; rfl)
      (by rw [hshape]; rfl)
      (by rw [hshape]; rfl)
      (by rw [hshape]; rfl)
  refine ⟨σ'_solm, ?_, hequiv⟩
  simpa [hshape, evm, initState] using hcall'

theorem amm4CtorFirstCallSourceReceiver
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := amm4CtorAfterSupply evm liquidity
    let evm2 := amm4CtorAfterSender evm1 I liquidity
    let evm3 := amm4CtorAfterToken0 evm2 t0
    let evm4 := amm4CtorAfterToken1 evm3 t1
    evalExpr? config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm4 (.storage token1Ref) =
      .ok (.address (AccountAddress.ofUInt256
        (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1))) := by
  intro evm evm1 evm2 evm3 evm4
  have hshape : evm4 =
      { evm with accountMap :=
        amm4CtorToken1Storage I σ_solm (EVM.word liquidity.toNat) t0 t1 } :=
    amm4CtorStoredSourceState_shape t0 t1 liquidity h0 hle hfit
  have htarget := amm4CtorInitialToken1Target_equiv I σ_evm σ_solm
    (EVM.word liquidity.toNat) t0 t1 hAccounts
  have hread : UInt256.land
      (Solm.EVM.storageLoad evm4 evm4.executionEnv.codeOwner ⟨4⟩)
      solcAddrMask =
      amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1 := by
    rw [htarget, amm4CtorInitialToken1Target_eq_masked]
    simp only [hshape, evm, initState, Solm.EVM.storageLoad,
      Ethereum.State.lookupAccount, Ethereum.Account.lookupStorage,
      amm4CtorStorageWord]
  rw [← hread]
  exact amm4MintEvalToken1
    (evm := evm4) (locals := amm4CtorAfterBaseLocals t0 t1 liquidity)
    (amm4CtorAfterBaseLocals_token1_none t0 t1 liquidity)

theorem amm4SolmCtorExecReverts_firstCallFailed
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm' : EVM.State}
    {ret : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (hne : t0 ≠ t1) (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall :
      let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := amm4CtorAfterSupply evm liquidity
      let evm2 := amm4CtorAfterSender evm1 I liquidity
      let evm3 := amm4CtorAfterToken0 evm2 t0
      let evm4 := amm4CtorAfterToken1 evm3 t1
      typedCallViaEVM config evm4
        (AccountAddress.ofUInt256
          (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1))
        "balanceOf" 0 [.address evm4.executionEnv.codeOwner]
        (false, evm', ret) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := amm4CtorAfterSupply evm liquidity
  let evm2 := amm4CtorAfterSender evm1 I liquidity
  let evm3 := amm4CtorAfterToken0 evm2 t0
  let evm4 := amm4CtorAfterToken1 evm3 t1
  have hprefix := amm4CtorSourceStoredPrefix_ok
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hne hwv
  have hreceiver := amm4CtorFirstCallSourceReceiver
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
    (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm4)
    (locals := amm4CtorAfterBaseLocals t0 t1 liquidity)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (amm4CtorSourceStoredPrefix ++ tokenBalance (.storage token1Ref)
        "initialBalance1" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallFailure
        (sendVal := 0) (evm' := evm') (out := ret)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)))

theorem amm4SolmCtorExecReverts_firstCallDepth
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (hne : t0 ≠ t1) (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth = 1024) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := amm4CtorAfterSupply evm liquidity
  let evm2 := amm4CtorAfterSender evm1 I liquidity
  let evm3 := amm4CtorAfterToken0 evm2 t0
  let evm4 := amm4CtorAfterToken1 evm3 t1
  let tgt := AccountAddress.ofUInt256
    (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1)
  have hshape : evm4 =
      { evm with accountMap :=
        amm4CtorToken1Storage I σ_solm (EVM.word liquidity.toNat) t0 t1 } :=
    amm4CtorStoredSourceState_shape t0 t1 liquidity h0 hle hfit
  have hcall : typedCallViaEVM config evm4 tgt "balanceOf" 0
      [.address evm4.executionEnv.codeOwner]
      (false, { evm4 with substate := (evm4.addAccessedAccount tgt).substate },
        ByteArray.empty) false := by
    apply callNotMade_depthLimit
      (calldata := (amm4CtorInitialToken1ArgMem I t0 t1
        (EVM.word liquidity.toNat)).readWithPadding 224 36)
    · simpa [hshape, evm, initState] using
        amm4CtorInitialToken1ArgMem_encode I t0 t1 (EVM.word liquidity.toNat)
    · simpa [hshape, evm, initState] using hdepth
  exact amm4SolmCtorExecReverts_firstCallFailed
    (createdAccounts := createdAccounts)
    (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hne hwv hAccounts hcall

theorem amm4SolmCtorExecReverts_firstCallShort
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm' : EVM.State}
    {ret : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (hne : t0 ≠ t1) (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : ret.size < 32)
    (hcall :
      let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := amm4CtorAfterSupply evm liquidity
      let evm2 := amm4CtorAfterSender evm1 I liquidity
      let evm3 := amm4CtorAfterToken0 evm2 t0
      let evm4 := amm4CtorAfterToken1 evm3 t1
      typedCallViaEVM config evm4
        (AccountAddress.ofUInt256
          (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1))
        "balanceOf" 0 [.address evm4.executionEnv.codeOwner]
        (true, evm', ret) false) :
    solmCtorExec config contract [.address t0, .address t1, .int liquidity]
      createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I .reverted := by
  let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := amm4CtorAfterSupply evm liquidity
  let evm2 := amm4CtorAfterSender evm1 I liquidity
  let evm3 := amm4CtorAfterToken0 evm2 t0
  let evm4 := amm4CtorAfterToken1 evm3 t1
  have hprefix := amm4CtorSourceStoredPrefix_ok
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hne hwv
  have hreceiver := amm4CtorFirstCallSourceReceiver
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
    (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm4)
    (locals := amm4CtorAfterBaseLocals t0 t1 liquidity)
  refine solmCtorExec.intro (evmState := evm)
    (argsStore := amm4CtorLocals t0 t1 liquidity) ?_ rfl rfl ?_
  · rfl
  · apply ExecFuncBody.execBlockRevert
    change ExecBlock config
      { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (amm4CtorSourceStoredPrefix ++ tokenBalance (.storage token1Ref)
        "initialBalance1" :: _) .reverted
    exact execBlock_append hprefix
      (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        (sendVal := 0) (evm' := evm') (out := ret)
        hreceiver (by simp [evalExpr?, pure]) hargs
        (by simpa only [amm4CtorAddressVal] using hcall)
        (amm4MintDecodeBalance_short hshort)))

def amm4CtorAfterInitialBalance1Locals
    (t0 t1 : AccountAddress) (liquidity : Int) (ret : ByteArray) : Store :=
  (amm4CtorAfterBaseLocals t0 t1 liquidity).insert "initialBalance1"
    (.int (Int.ofNat (fromByteArrayBigEndian (ret.extract 0 32))))

theorem amm4CtorSourceInitialBalance1Success
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {evm' : EVM.State}
    {ret : ByteArray}
    (t0 t1 : AccountAddress) (liquidity : Int)
    (h0 : 0 ≤ liquidity) (hle : 1000 ≤ liquidity.toNat)
    (hfit : liquidity.toNat < UInt256.size)
    (hne : t0 ≠ t1) (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlo : 32 ≤ ret.size) (hbound : ret.size < 2 ^ 138)
    (hcall :
      let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I
      let evm1 := amm4CtorAfterSupply evm liquidity
      let evm2 := amm4CtorAfterSender evm1 I liquidity
      let evm3 := amm4CtorAfterToken0 evm2 t0
      let evm4 := amm4CtorAfterToken1 evm3 t1
      typedCallViaEVM config evm4
        (AccountAddress.ofUInt256
          (amm4CtorInitialToken1Target I σ_evm (EVM.word liquidity.toNat) t0 t1))
        "balanceOf" 0 [.address evm4.executionEnv.codeOwner]
        (true, evm', ret) false) :
    let evm := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
      (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := amm4CtorLocals t0 t1 liquidity }
      evm (amm4CtorSourceStoredPrefix ++
        [tokenBalance (.storage token1Ref) "initialBalance1"])
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret } evm') := by
  intro evm
  let evm1 := amm4CtorAfterSupply evm liquidity
  let evm2 := amm4CtorAfterSender evm1 I liquidity
  let evm3 := amm4CtorAfterToken0 evm2 t0
  let evm4 := amm4CtorAfterToken1 evm3 t1
  have hprefix := amm4CtorSourceStoredPrefix_ok
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hne hwv
  have hreceiver := amm4CtorFirstCallSourceReceiver
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
    (g := g) (A := A) (I := I)
    t0 t1 liquidity h0 hle hfit hAccounts
  have hargs := amm4MintEvalBalanceArgs (evm := evm4)
    (locals := amm4CtorAfterBaseLocals t0 t1 liquidity)
  have hdec := amm4MintDecodeBalance_ok hlo
    (by omega : ret.size < 2 ^ 255)
  have htail : ExecBlock config
      { contract := contract, locals := amm4CtorAfterBaseLocals t0 t1 liquidity }
      evm4 [tokenBalance (.storage token1Ref) "initialBalance1"]
      (.ok { contract := contract, locals :=
        amm4CtorAfterInitialBalance1Locals t0 t1 liquidity ret } evm') := by
    simp only [tokenBalance]
    simpa [amm4CtorAfterInitialBalance1Locals, collapseReturns] using
      (ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (sendVal := 0) (evm' := evm') (out := ret)
          hreceiver (by simp [evalExpr?, pure]) hargs
          (by simpa only [amm4CtorAddressVal] using hcall) hdec)
        ExecBlock.nil)
  exact execBlock_append hprefix htail

end Benchmarks.ActAmm4
