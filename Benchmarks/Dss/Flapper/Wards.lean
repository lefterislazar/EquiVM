import Benchmarks.Dss.Flapper.Common
import Benchmarks.Dss.Flapper.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

def flapperWardsKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land flapperAddressMask (calldataWord I.calldata 4)

def flapperWardsWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  storageRead I.codeOwner σ (solcMappingSlot (UInt256.ofNat 0) (flapperWardsKey I))

theorem flapperWardsHashMem_eq (key : UInt256) :
    flapperRuntimeBlocks.flapperRuntime_block_3316_memory
        (mem := solcFreePtrMem) (x0 := key) =
      twoWordHashMemSlotFirst key (UInt256.ofNat 0) solcFreePtrMem := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3316_memory,
    twoWordHashMemSlotFirst, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 32).toNat = 32 by decide,
    show (UInt256.ofNat 0).toNat = 0 by decide]

theorem flapperWardsHashMem_size (key : UInt256) :
    (flapperRuntimeBlocks.flapperRuntime_block_3316_memory
        (mem := solcFreePtrMem) (x0 := key)).size = 96 := by
  rw [flapperWardsHashMem_eq]
  unfold twoWordHashMemSlotFirst
  exact wordAt0Mem_size_96 key
    (wordAt32Mem_size_96 (UInt256.ofNat 0) solcFreePtrMem_size)

theorem flapperWardsHashMem_read64 (key : UInt256) :
    (flapperRuntimeBlocks.flapperRuntime_block_3316_memory
        (mem := solcFreePtrMem) (x0 := key)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [flapperWardsHashMem_eq]
  unfold twoWordHashMemSlotFirst wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [wordAt32Mem_size_96 (UInt256.ofNat 0) solcFreePtrMem_size]; omega)
      (by omega)
      (by rw [wordAt32Mem_size_96 (UInt256.ofNat 0) solcFreePtrMem_size])]
  unfold wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [solcFreePtrMem_size]; omega)
      (by omega)
      (by rw [solcFreePtrMem_size])]
  exact solcFreePtrMem_read64

theorem flapperWardsHashSlot (key : UInt256) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_3316_memory
          (mem := solcFreePtrMem) (x0 := key)) =
      solcMappingSlot (UInt256.ofNat 0) key := by
  rw [flapperWardsHashMem_eq]
  unfold keccakWord solcMappingSlot
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 64).toNat = 64 by decide,
    twoWordHashMemSlotFirst_read0_64_any]
  exact mappingSlot_single key (UInt256.ofNat 0)

theorem flapperX_wards_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨729⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperWardsWord σ I)) := by
  obtain ⟨_, _, rd729⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 32)
      (by simpa using hsz36) hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd751 := flapperRuntimeBlocks.flapperRuntime_block_729_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond (by jump_dest) rd729
  have rd3316 := flapperRuntimeBlocks.flapperRuntime_block_751
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 313, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd751
  have rd3316Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 3316)
        (flapperWardsKey I :: UInt256.ofNat 313 :: [sel])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [flapperWardsKey, calldataWord] using rd3316⟩
  obtain ⟨_, _, rd3316'⟩ := rd3316Ex
  obtain ⟨_, _, rd313raw⟩ := flapperRuntimeBlocks.flapperRuntime_block_3316
    (x0 := flapperWardsKey I) (x1 := UInt256.ofNat 313) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    (by jump_dest) rd3316'
  have hslot :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((flapperWardsKey I).toByteArray.write 0
            ((UInt256.ofNat 0).toByteArray.write 0 solcFreePtrMem
              (UInt256.ofNat 32).toNat 32)
            (UInt256.ofNat 0).toNat 32) =
        solcMappingSlot (UInt256.ofNat 0) (flapperWardsKey I) := by
    simpa [flapperRuntimeBlocks.flapperRuntime_block_3316_memory] using
      flapperWardsHashSlot (flapperWardsKey I)
  have haw :
      M (M (M (UInt256.ofNat 3) (UInt256.ofNat 32) (⟨32⟩ : UInt256))
        (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64) =
        UInt256.ofNat 3 := by
    native_decide
  have rd313Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 313)
        (flapperWardsWord σ I :: UInt256.ofNat 313 :: [sel])
        (flapperRuntimeBlocks.flapperRuntime_block_3316_memory
          (mem := solcFreePtrMem) (x0 := flapperWardsKey I))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [flapperWardsWord, flapperRuntimeBlocks.flapperRuntime_block_3316_stack,
        hslot, haw] using rd313raw⟩
  obtain ⟨_, _, rd313⟩ := rd313Ex
  have hret := RD.solcReturnWordFromMem
    (code := flapperBytecode) (pc := UInt256.ofNat 313)
    (val := flapperWardsWord σ I)
    (ret := UInt256.ofNat 313) (R := [sel])
    rd313
    (by
      dsimp [solcReturnWordFromMemWf]
      exact ⟨by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide, by native_decide, by native_decide,
        by native_decide, by native_decide, by native_decide, by native_decide⟩)
    (mloadFreePtrValue (by rw [flapperWardsHashMem_size (flapperWardsKey I)]; decide)
      (flapperWardsHashMem_read64 (flapperWardsKey I)))
    (by rfl)
    (solcScratchReturnMem_mload64
      (flapperWardsWord σ I)
      (flapperWardsHashMem_size (flapperWardsKey I))
      (flapperWardsHashMem_read64 (flapperWardsKey I)))
    (solcScratchReturnMem_read128
      (flapperWardsWord σ I)
      (flapperWardsHashMem_size (flapperWardsKey I)))
    (by simp only [List.length_singleton]; omega)
  simpa using hret

theorem flapperX_wards_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨729⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd729⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 1 := by
    apply ult_one
    rw [usub_ofNat_word_toNat
      (c := UInt256.ofNat 4)
      (by change 4 ≤ I.calldata.size; omega) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) = UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd747 := flapperRuntimeBlocks.flapperRuntime_block_729_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd729
  exact flapperRuntimeBlocks.flapperRuntime_block_747
    (R := flapperRuntimeBlocks.flapperRuntime_block_729_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_729_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd747

theorem flapperDispatch_wards {cd : ByteArray}
    (hsel : ((⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some wardsTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition,
      denyTransition, fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition,
      tendTransition, tickTransition, ttlTransition, vatTransition])
    (post := [yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    · rw [flapperVatSelectorBytes, hcd]; decide
  · rw [flapperWardsSelectorBytes]
    exact hsel

theorem flapperDecode_wards_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "arg0"
        (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [abiAddress] I.calldata =
    some ((∅ : Store).insert "arg0"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
  exact decodeCalldata_legacyAddress_ok hsz36

theorem flapperDecode_wards_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (wardsTransition.params.map Param.name)
      (transitionSignature wardsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["arg0"] [abiAddress] I.calldata = none
  exact decodeCalldata_legacyAddress_none_short hsz4 hshort

theorem flapperWardsBodyReturns (evm : EVM.State) (usrWord : UInt256)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat usrWord.toNat)))
      wardsTransition.body
      (.returned
        { contract := contract,
          locals := ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat usrWord.toNat))) }
        evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (solcMappingSlot (UInt256.ofNat 0) (UInt256.land solcAddrMask usrWord))).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      let locals := ((∅ : Store).insert "arg0"
        (.address (AccountAddress.ofNat usrWord.toNat)))
      let er : EvaledStorageRef :=
        { base := "wards", steps := [.mindex (.address (AccountAddress.ofNat usrWord.toNat))] }
      have hbase : locals.get? "wards" = none := by
        simp [locals]
      have her :
          evalStorageRef config { contract := contract, locals := locals } evm
              (wardsRef (.var "arg0")) = .ok er := by
        simp [locals, er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, wardsRef,
          evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
        simp [er, contract, storageDecls, storageTypeAt?, storageTypeStep?, uint256St]
      have hloc : config.storage.layout er =
          fun _ => some (wordLoc
            (solcMappingSlot (UInt256.ofNat 0) (UInt256.land solcAddrMask usrWord))) := by
        funext evm'
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er, wardsSlot,
          mapSlot, solcMappingSlot, keyValueToWord_address_ofNat_mask]
        rfl
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hbase) (her := her)
        (hty := hty) (hloc := hloc), flapperStorageLocLoad_uint256])

theorem flapperWardsBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 18))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨729⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 := calldata_size_ge_of_selIs I (⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ : ByteArray)
    rfl hselLit
  have hd := flapperDispatch_wards (cd := I.calldata) hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_wards_ok (I := I) hsz36
    have hword : flapperWardsWord σ_evm I = flapperWardsWord σ_solm I := by
      change storageRead I.codeOwner σ_evm
          (solcMappingSlot (UInt256.ofNat 0) (flapperWardsKey I)) =
        storageRead I.codeOwner σ_solm
          (solcMappingSlot (UInt256.ofNat 0) (flapperWardsKey I))
      rw [storageRead_eq, storageRead_eq]
      exact accountMapEquiv_storage_findD hAccounts I.codeOwner
        (solcMappingSlot (UInt256.ofNat 0) (flapperWardsKey I)) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ((∅ : Store).insert "arg0"
            (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
          wardsTransition.body
          (.returned
            { contract := contract,
              locals := ((∅ : Store).insert "arg0"
                (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (flapperWardsWord σ_solm I).toNat))])) := by
      simpa [flapperWardsWord, flapperWardsKey, storageRead_eq, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage] using
        flapperWardsBodyReturns
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4)
          (by simp only [initState]; exact hwv)
    exact (flapperX_wards_ok (g := Sat256.ofUInt256 g) hsize hsz36 hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by rw [hword]) hAccounts
        (returnEquiv_of_encode (uint256ReturnEncoding (flapperWardsWord σ_evm I)))
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_wards_none_short (I := I) hsz4 hshort
    have hrev := flapperX_wards_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
