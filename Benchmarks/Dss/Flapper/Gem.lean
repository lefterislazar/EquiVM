import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperGemWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 3)) solcAddrMask

theorem flapperX_gem {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨638⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperGemWord σ I)) := by
  obtain ⟨_, _, rd638⟩ := hreach
  have rd2960 := flapperRuntimeBlocks.flapperRuntime_block_638
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd638
  obtain ⟨_, _, rd405⟩ := flapperRuntimeBlocks.flapperRuntime_block_2960
    (x0 := UInt256.ofNat 405) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd2960
  have hret := flapperRuntimeBlocks.flapperRuntime_block_405
    (x0 := UInt256.land flapperAddressMask (storageRead I.codeOwner σ (UInt256.ofNat 3)))
    (R := [UInt256.ofNat 405, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd405
  change RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
    (flapperScalarReturnBytes
      (UInt256.land
        (UInt256.land flapperAddressMask (storageRead I.codeOwner σ (UInt256.ofNat 3)))
        flapperAddressMask)) at hret
  simpa [flapperGemWord, flapperSolcAddrMask_clean] using hret

theorem flapperDispatch_gem {cd : ByteArray}
    (hsel : ((⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some gemTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition])
    (post := [kickTransition, kicksTransition, lidTransition, liveTransition,
      relyTransition, tauTransition, tendTransition, tickTransition, ttlTransition,
      vatTransition, wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
    · rw [flapperDenySelectorBytes, hcd]; decide
    · rw [flapperFileSelectorBytes, hcd]; decide
    · rw [flapperFillSelectorBytes, hcd]; decide
  · rw [flapperGemSelectorBytes]
    exact hsel

theorem flapperDecode_gem {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (gemTransition.params.map Param.name)
      (transitionSignature gemTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem flapperGemBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hlocals : locals.get? "gem" = none) :
    ExecTransitionBody config contract evm locals gemTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm gemRef =
          .ok { base := "gem", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, gemRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "gem", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by
        decide
      have hloc : config.storage.layout ({ base := "gem", steps := [] } : EvaledStorageRef) =
          fun _ => some (addrLoc ⟨3⟩) := by
        funext evm'
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := hloc), flapperStorageLocLoad_address])

theorem flapperGemBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 7))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨638⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz := calldata_size_ge_of_selIs I (⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_gem (cd := I.calldata) hselLit
  have hdec := flapperDecode_gem (I := I) hsz
  have hslot : storageRead I.codeOwner σ_evm (UInt256.ofNat 3) =
      storageRead I.codeOwner σ_solm (UInt256.ofNat 3) := by
    rw [storageRead_eq, storageRead_eq]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 3) ⟨0⟩
  have hword : flapperGemWord σ_evm I = flapperGemWord σ_solm I := by
    simp [flapperGemWord, hslot]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ gemTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (flapperGemWord σ_solm I).toNat))])) := by
    simpa [flapperGemWord, storageRead_eq, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage] using
      flapperGemBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (flapperX_gem (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (abit := .elem .address)
        (rv := .address (AccountAddress.ofNat (flapperGemWord σ_evm I).toNat))
        (o := UInt256.toByteArray (flapperGemWord σ_evm I))
        (by
          simpa [flapperGemWord] using
            solcAddressReturnEncoding rfl (storageRead I.codeOwner σ_evm (UInt256.ofNat 3))))

end Benchmarks.Dss.Flapper
