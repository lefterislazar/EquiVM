import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (UInt256.ofNat 7)

theorem flapperX_live {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨654⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperLiveWord σ I)) := by
  obtain ⟨_, _, rd654⟩ := hreach
  have rd2981 := flapperRuntimeBlocks.flapperRuntime_block_654
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd654
  obtain ⟨_, _, rd313⟩ := flapperRuntimeBlocks.flapperRuntime_block_2981
    (x0 := UInt256.ofNat 313) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd2981
  have hret := flapperRuntimeBlocks.flapperRuntime_block_313
    (x0 := flapperLiveWord σ I) (R := [UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd313
  change RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
    (flapperScalarReturnBytes (flapperLiveWord σ I)) at hret
  simpa using hret

theorem flapperDispatch_live {cd : ByteArray}
    (hsel : ((⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some liveTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition])
    (post := [relyTransition, tauTransition, tendTransition, tickTransition,
      ttlTransition, vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
    · rw [flapperDenySelectorBytes, hcd]; decide
    · rw [flapperFileSelectorBytes, hcd]; decide
    · rw [flapperFillSelectorBytes, hcd]; decide
    · rw [flapperGemSelectorBytes, hcd]; decide
    · rw [flapperKickSelectorBytes, hcd]; decide
    · rw [flapperKicksSelectorBytes, hcd]; decide
    · rw [flapperLidSelectorBytes, hcd]; decide
  · rw [flapperLiveSelectorBytes]
    exact hsel

theorem flapperDecode_live {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (liveTransition.params.map Param.name)
      (transitionSignature liveTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem flapperLiveBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hlocals : locals.get? "live" = none) :
    ExecTransitionBody config contract evm locals liveTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm liveRef =
          .ok { base := "live", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "live", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by
        decide
      have hloc : config.storage.layout ({ base := "live", steps := [] } : EvaledStorageRef) =
          fun _ => some (wordLoc ⟨7⟩) := by
        funext evm'
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256])

theorem flapperLiveBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 11))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨654⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz := calldata_size_ge_of_selIs I (⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_live (cd := I.calldata) hselLit
  have hdec := flapperDecode_live (I := I) hsz
  have hword : flapperLiveWord σ_evm I = flapperLiveWord σ_solm I := by
    change storageRead I.codeOwner σ_evm (UInt256.ofNat 7) =
      storageRead I.codeOwner σ_solm (UInt256.ofNat 7)
    rw [storageRead_eq, storageRead_eq]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 7) ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flapperLiveWord σ_solm I).toNat))])) := by
    simpa [flapperLiveWord, storageRead_eq, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage] using
      flapperLiveBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (flapperX_live (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (uint256ReturnEncoding (flapperLiveWord σ_evm I)))

end Benchmarks.Dss.Flapper
