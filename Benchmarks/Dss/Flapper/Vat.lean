import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_003

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperVatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (storageRead I.codeOwner σ (UInt256.ofNat 2)) solcAddrMask

theorem flapperX_vat {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨397⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperVatWord σ I)) := by
  obtain ⟨_, _, rd397⟩ := hreach
  have rd1547 := flapperRuntimeBlocks.flapperRuntime_block_397
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd397
  obtain ⟨_, _, rd405⟩ := flapperRuntimeBlocks.flapperRuntime_block_1547
    (x0 := UInt256.ofNat 405) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd1547
  have hret := flapperRuntimeBlocks.flapperRuntime_block_405
    (x0 := UInt256.land flapperAddressMask (storageRead I.codeOwner σ (UInt256.ofNat 2)))
    (R := [UInt256.ofNat 405, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd405
  change RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
    (flapperScalarReturnBytes
      (UInt256.land
        (UInt256.land flapperAddressMask (storageRead I.codeOwner σ (UInt256.ofNat 2)))
        flapperAddressMask)) at hret
  simpa [flapperVatWord, flapperSolcAddrMask_clean] using hret

theorem flapperDispatch_vat {cd : ByteArray}
    (hsel : ((⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some vatTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition,
      tendTransition, tickTransition, ttlTransition])
    (post := [wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [flapperLiveSelectorBytes, hcd]; decide
    · rw [flapperRelySelectorBytes, hcd]; decide
    · rw [flapperTauSelectorBytes, hcd]; decide
    · rw [flapperTendSelectorBytes, hcd]; decide
    · rw [flapperTickSelectorBytes, hcd]; decide
    · rw [flapperTtlSelectorBytes, hcd]; decide
  · rw [flapperVatSelectorBytes]
    exact hsel

theorem flapperDecode_vat {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (vatTransition.params.map Param.name)
      (transitionSignature vatTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem flapperVatBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hlocals : locals.get? "vat" = none) :
    ExecTransitionBody config contract evm locals vatTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm vatRef =
          .ok { base := "vat", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by
        decide
      have hloc : config.storage.layout ({ base := "vat", steps := [] } : EvaledStorageRef) =
          fun _ => some (addrLoc ⟨2⟩) := by
        funext evm'
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := hloc), flapperStorageLocLoad_address])

theorem flapperVatBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 17))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨397⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz := calldata_size_ge_of_selIs I (⟨#[0x36, 0x56, 0x9e, 0x77]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_vat (cd := I.calldata) hselLit
  have hdec := flapperDecode_vat (I := I) hsz
  have hslot : storageRead I.codeOwner σ_evm (UInt256.ofNat 2) =
      storageRead I.codeOwner σ_solm (UInt256.ofNat 2) := by
    rw [storageRead_eq, storageRead_eq]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 2) ⟨0⟩
  have hword : flapperVatWord σ_evm I = flapperVatWord σ_solm I := by
    simp [flapperVatWord, hslot]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vatTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (flapperVatWord σ_solm I).toNat))])) := by
    simpa [flapperVatWord, storageRead_eq, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage] using
      flapperVatBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (flapperX_vat (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (abit := .elem .address)
        (rv := .address (AccountAddress.ofNat (flapperVatWord σ_evm I).toNat))
        (o := UInt256.toByteArray (flapperVatWord σ_evm I))
        (by
          simpa [flapperVatWord] using
            solcAddressReturnEncoding rfl (storageRead I.codeOwner σ_evm (UInt256.ofNat 2))))

end Benchmarks.Dss.Flapper
