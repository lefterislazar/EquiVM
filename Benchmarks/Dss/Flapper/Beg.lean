import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperBegWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (UInt256.ofNat 4)

theorem flapperX_beg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨646⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperBegWord σ I)) := by
  obtain ⟨_, _, rd646⟩ := hreach
  have rd2975 := flapperRuntimeBlocks.flapperRuntime_block_646
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd646
  obtain ⟨_, _, rd313⟩ := flapperRuntimeBlocks.flapperRuntime_block_2975
    (x0 := UInt256.ofNat 313) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd2975
  have hret := flapperRuntimeBlocks.flapperRuntime_block_313
    (x0 := flapperBegWord σ I) (R := [UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd313
  change RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
    (flapperScalarReturnBytes (flapperBegWord σ I)) at hret
  simpa using hret

theorem flapperDispatch_beg {cd : ByteArray}
    (hsel : ((⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some begTransition := by
  refine dispatchMsg_eq_some_of_split (pre := [])
    (post := [bidsTransition, cageTransition, dealTransition, denyTransition,
      fileTransition, fillTransition, gemTransition, kickTransition, kicksTransition,
      lidTransition, liveTransition, relyTransition, tauTransition, tendTransition,
      tickTransition, ttlTransition, vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp at ht
  · rw [flapperBegSelectorBytes]
    exact hsel

theorem flapperDecode_beg {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (begTransition.params.map Param.name)
      (transitionSignature begTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem flapperBegBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hlocals : locals.get? "beg" = none) :
    ExecTransitionBody config contract evm locals begTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm begRef =
          .ok { base := "beg", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, begRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "beg", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by
        decide
      have hloc : config.storage.layout ({ base := "beg", steps := [] } : EvaledStorageRef) =
          fun _ => some (wordLoc ⟨4⟩) := by
        funext evm'
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256])

theorem flapperBegBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 0))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨646⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz := calldata_size_ge_of_selIs I (⟨#[0x7d, 0x78, 0x0d, 0x82]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_beg (cd := I.calldata) hselLit
  have hdec := flapperDecode_beg (I := I) hsz
  have hword : flapperBegWord σ_evm I = flapperBegWord σ_solm I := by
    change storageRead I.codeOwner σ_evm (UInt256.ofNat 4) =
      storageRead I.codeOwner σ_solm (UInt256.ofNat 4)
    rw [storageRead_eq, storageRead_eq]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 4) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ begTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flapperBegWord σ_solm I).toNat))])) := by
    simpa [flapperBegWord, storageRead_eq, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage] using
      flapperBegBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (flapperX_beg (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (flapperBegWord σ_evm I)))

end Benchmarks.Dss.Flapper
