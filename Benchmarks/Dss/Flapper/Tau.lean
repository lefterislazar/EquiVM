import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_003
import Benchmarks.Dss.Flapper.RuntimeBlocks_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperTauWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5)) flapperUint48Shift)
    flapperUint48Mask

theorem flapperX_tau {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨831⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperTauWord σ I)) := by
  obtain ⟨_, _, rd831⟩ := hreach
  have rd4553 := flapperRuntimeBlocks.flapperRuntime_block_831
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd831
  obtain ⟨_, _, rd573⟩ := flapperRuntimeBlocks.flapperRuntime_block_4553
    (x0 := UInt256.ofNat 573) (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest)
    rd4553
  have hret := flapperRuntimeBlocks.flapperRuntime_block_573
    (x0 := UInt256.land flapperUint48Mask
      (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5)) flapperUint48Shift))
    (R := [UInt256.ofNat 573, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd573
  change RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
    (flapperScalarReturnBytes
      (UInt256.land
        (UInt256.land flapperUint48Mask
          (UInt256.div (storageRead I.codeOwner σ (UInt256.ofNat 5)) flapperUint48Shift))
        flapperUint48Mask)) at hret
  simpa [flapperTauWord, flapperUint48Mask_clean] using hret

theorem flapperDispatch_tau {cd : ByteArray}
    (hsel : ((⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some tauTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition, liveTransition, relyTransition])
    (post := [tendTransition, tickTransition, ttlTransition, vatTransition,
      wardsTransition, yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
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
  · rw [flapperTauSelectorBytes]
    exact hsel

theorem flapperDecode_tau {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (tauTransition.params.map Param.name)
      (transitionSignature tauTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem flapperTauBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hlocals : locals.get? "tau" = none) :
    ExecTransitionBody config contract evm locals tauTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (UInt256.land
            (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
              flapperUint48Shift)
            flapperUint48Mask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm tauRef =
          .ok { base := "tau", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, tauRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "tau", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint48Int)) := by
        decide
      have hloc : config.storage.layout ({ base := "tau", steps := [] } : EvaledStorageRef) =
          fun _ => some (uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide)) := by
        funext evm'
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]
      rw [evalExpr_storage_scalar (t := .int uint48Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint48_offset6])

theorem flapperTauBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 13))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨831⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz := calldata_size_ge_of_selIs I (⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_tau (cd := I.calldata) hselLit
  have hdec := flapperDecode_tau (I := I) hsz
  have hslot : storageRead I.codeOwner σ_evm (UInt256.ofNat 5) =
      storageRead I.codeOwner σ_solm (UInt256.ofNat 5) := by
    rw [storageRead_eq, storageRead_eq]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (UInt256.ofNat 5) ⟨0⟩
  have hword : flapperTauWord σ_evm I = flapperTauWord σ_solm I := by
    simp [flapperTauWord, hslot]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ tauTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flapperTauWord σ_solm I).toNat))])) := by
    simpa [flapperTauWord, storageRead_eq, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage] using
      flapperTauBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (flapperX_tau (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
      (returnEquiv_of_encode (abit := .elem (.int uint48Int))
        (rv := .int (Int.ofNat (flapperTauWord σ_evm I).toNat))
        (o := UInt256.toByteArray (flapperTauWord σ_evm I))
        (flapperUint48ReturnEncoding (flapperTauWord σ_evm I)
          (by
            simpa [flapperTauWord] using
              flapperUint48Word_lt
                (UInt256.div (storageRead I.codeOwner σ_evm (UInt256.ofNat 5))
                  flapperUint48Shift))))

end Benchmarks.Dss.Flapper
