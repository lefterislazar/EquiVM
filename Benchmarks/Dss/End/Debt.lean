import Benchmarks.Dss.End.Common
import Benchmarks.Dss.End.RuntimeBlocks_004

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

def endDebtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I ⟨11⟩

@[simp] theorem endConfig_storage_debt :
    config.storage.layout { base := "debt", steps := [] } =
      fun _ => some (wordLoc ⟨11⟩) :=
  rfl

/-- The Solm `debt()` body returns the word stored in slot 11. -/
theorem endDebtBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "debt" = none) :
    ExecTransitionBody config contract evm locals debtTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          debtRef = .ok { base := "debt", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "debt", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_debt), endRuntimeStorageLocLoad_uint256])

/-- The EVM `debt()` wrapper loads slot 11 and returns it as a single ABI word. -/
theorem endX_debt {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨501⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endDebtWord σ I)) := by
  simpa [endDebtWord] using
    (RD.solcWordGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨501⟩) (routine := ⟨1309⟩) (slot := ⟨11⟩)
      (returnPc := ⟨509⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcWordSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endDebtSelector_size {I : ExecutionEnv}
    (hsel : endSelectorMatches I (endSelBytes 11)) :
    4 ≤ I.calldata.size := by
  exact calldata_size_ge_of_selIs I (endSelBytes 11) (by rfl) hsel

theorem endDispatch_debt {cd : ByteArray}
    (hsel : (endSelBytes 11 == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some debtTransition := by
  have hcd : cd.extract 0 4 = endSelBytes 11 := (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [wardsTransition, vatTransition, catTransition, dogTransition, vowTransition,
      potTransition, spotTransition, cureTransition, liveTransition, whenTransition, waitTransition])
    (post := [tagTransition, gapTransition, ArtTransition, fixTransition, bagTransition,
      outTransition, relyTransition, denyTransition, fileAddressTransition, fileUintTransition,
      cageTransition, cageIlkTransition, snipTransition, skipTransition, skimTransition,
      freeTransition, thawTransition, flowTransition, packTransition, cashTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hs : selectorOf wardsTransition = endSelBytes 0 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 0 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf vatTransition = endSelBytes 1 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 1 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf catTransition = endSelBytes 2 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 2 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf dogTransition = endSelBytes 3 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 3 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf vowTransition = endSelBytes 4 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 4 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf potTransition = endSelBytes 5 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 5 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf spotTransition = endSelBytes 6 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 6 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf cureTransition = endSelBytes 7 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 7 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf liveTransition = endSelBytes 8 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 8 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf whenTransition = endSelBytes 9 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 9 (by omega)
      rw [hs, hcd]; decide
    · have hs : selectorOf waitTransition = endSelBytes 10 := by
        simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 10 (by omega)
      rw [hs, hcd]; decide
  · have hs : selectorOf debtTransition = endSelBytes 11 := by
      simpa [endTransitionAt, transitions] using endRuntimeSelectorBytes_at 11 (by omega)
    rw [hs]
    exact hsel

theorem endDecode_debt {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (debtTransition.params.map Param.name)
      (transitionSignature debtTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz

theorem endDebtBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 11))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨501⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endDebtSelector_size hsel
  have hd := endDispatch_debt (cd := I.calldata) hsel
  have hdec := endDecode_debt (I := I) hsz
  have hword : endDebtWord σ_evm I = endDebtWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ debtTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endDebtWord σ_solm I).toNat))])) := by
    simpa [endDebtWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      endDebtBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_debt (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody (by rw [hword]) hAccounts
    (returnEquiv_of_encode (endUint256ReturnEncoding (endDebtWord σ_evm I)))

end Benchmarks.Dss.End
