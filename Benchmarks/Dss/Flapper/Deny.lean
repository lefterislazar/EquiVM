import Benchmarks.Dss.Flapper.Rely
import Benchmarks.Dss.Flapper.RuntimeBlocks_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

theorem flapperDenyAuthHashMem_eq (I : ExecutionEnv) :
    flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
        (ee := I) (mem := solcFreePtrMem) =
      twoWordHashMem (flapperRelyAuthWord I) (UInt256.ofNat 0) solcFreePtrMem := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory,
    flapperRelyAuthWord, twoWordHashMem, wordAt0Mem, wordAt32Mem,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperDenyAuthHashSlot (I : ExecutionEnv) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
          (ee := I) (mem := solcFreePtrMem)) =
      flapperRelyAuthSlot I := by
  rw [flapperDenyAuthHashMem_eq]
  simpa [flapperRelyAuthSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat (flapperRelyAuthWord I)
      (UInt256.ofNat 0) solcFreePtrMem

theorem flapperDenyStoreHashMem_eq (I : ExecutionEnv) (mem : ByteArray) :
    flapperRuntimeBlocks.flapperRuntime_block_3080_memory
        (mem := mem) (x0 := flapperRelyUsrWord I) =
      twoWordHashMem (flapperRelyUsrWord I) (UInt256.ofNat 0) mem := by
  simp [flapperRuntimeBlocks.flapperRuntime_block_3080_memory, flapperRelyUsrWord,
    twoWordHashMem, wordAt0Mem, wordAt32Mem, flapperRelySolcMask_clean_left,
    show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]

theorem flapperDenyStoreHashSlot (I : ExecutionEnv) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (flapperRuntimeBlocks.flapperRuntime_block_3080_memory
          (mem := mem) (x0 := flapperRelyUsrWord I)) =
      flapperRelyUsrSlot I := by
  rw [flapperDenyStoreHashMem_eq]
  simpa [flapperRelyUsrSlot] using
    twoWordHashMem_keccak_solcMappingSlot_ofNat (flapperRelyUsrWord I)
      (UInt256.ofNat 0) mem

theorem flapperX_deny_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) = UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨662⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flapperBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (flapperRelyUsrSlot I) (UInt256.ofNat 0))
      ByteArray.empty := by
  obtain ⟨_, _, rd662⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 32)
      (by simpa using hsz36) hsize
  have hcondLen :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd684 := flapperRuntimeBlocks.flapperRuntime_block_662_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd662
  have rd2987raw := flapperRuntimeBlocks.flapperRuntime_block_684
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd684
  have rd2987Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2987)
        (flapperRelyUsrWord I :: UInt256.ofNat 360 :: [sel])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [flapperRelyUsrWord, calldataWord, flapperAddressMask_eq_solcAddrMask] using
        rd2987raw⟩
  obtain ⟨_, _, rd2987⟩ := rd2987Ex
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              (flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
                (ee := I) (mem := solcFreePtrMem)))) ≠ UInt256.ofNat 0 := by
    rw [flapperDenyAuthHashSlot, hauth]
    decide
  obtain ⟨_, _, rd3080raw⟩ := flapperRuntimeBlocks.flapperRuntime_block_2987_taken
    (R := flapperRelyUsrWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondAuth (by jump_dest) rd2987
  have hmaskUsr :
      UInt256.land solcAddrMask (flapperRelyUsrWord I) = flapperRelyUsrWord I := by
    simp [flapperRelyUsrWord, flapperRelySolcMask_clean_left]
  have hstoreSlotRaw :
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 0).toByteArray.write 0
            ((UInt256.land solcAddrMask (flapperRelyUsrWord I)).toByteArray.write 0
              (flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
                (ee := I) (mem := solcFreePtrMem))
              (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32) =
        flapperRelyUsrSlot I := by
    rw [hmaskUsr]
    rw [show (UInt256.ofNat 0).toNat = 0 by decide,
      show (UInt256.ofNat 32).toNat = 32 by decide]
    change
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        (twoWordHashMem (flapperRelyUsrWord I) (UInt256.ofNat 0)
          (flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
            (ee := I) (mem := solcFreePtrMem))) =
        flapperRelyUsrSlot I
    simpa [flapperRelyUsrSlot] using
      twoWordHashMem_keccak_solcMappingSlot_ofNat (flapperRelyUsrWord I)
        (UInt256.ofNat 0)
        (flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
          (ee := I) (mem := solcFreePtrMem))
  obtain ⟨_, _, rd360raw⟩ := flapperRuntimeBlocks.flapperRuntime_block_3080
    (x0 := flapperRelyUsrWord I) (x1 := UInt256.ofNat 360) (R := [sel])
    (by simp only [List.length_singleton]; omega)
    hperm (by jump_dest) rd3080raw
  have rd360Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 360)
        [sel]
        (flapperRuntimeBlocks.flapperRuntime_block_3080_memory
          (mem := flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
            (ee := I) (mem := solcFreePtrMem))
          (x0 := flapperRelyUsrWord I))
        (M (M (M (M (M (M (UInt256.ofNat 3) (UInt256.ofNat 0) (⟨32⟩ : UInt256))
          (UInt256.ofNat 32) (⟨32⟩ : UInt256)) (UInt256.ofNat 0) (UInt256.ofNat 64))
          (UInt256.ofNat 0) (⟨32⟩ : UInt256)) (UInt256.ofNat 32) (⟨32⟩ : UInt256))
          (UInt256.ofNat 0) (UInt256.ofNat 64))
        ByteArray.empty
        (cA, storageWrite I.codeOwner σ (flapperRelyUsrSlot I) (UInt256.ofNat 0)) k C := by
    exact ⟨_, _, by
      simpa [flapperRuntimeBlocks.flapperRuntime_block_3080_stack,
        hstoreSlotRaw] using rd360raw⟩
  obtain ⟨_, _, rd360⟩ := rd360Ex
  exact flapperRuntimeBlocks.flapperRuntime_block_360
    (R := [sel])
    (by simp only [List.length_singleton]; omega)
    rd360

theorem flapperX_deny_auth_revert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz36 : 36 ≤ I.calldata.size)
    (hauth : storageRead I.codeOwner σ (flapperRelyAuthSlot I) ≠ UInt256.ofNat 1)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨662⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd662⟩ := hreach
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
          (UInt256.ofNat 32) = UInt256.ofNat 0 := by
    exact solcDecodeLenCheckOkUnsigned
      (head := UInt256.ofNat 4) (need := UInt256.ofNat 32)
      (by simpa using hsz36) hsize
  have hcondLen :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
            (UInt256.ofNat 32)) ≠ UInt256.ofNat 0 := by
    rw [hlt]
    decide
  have rd684 := flapperRuntimeBlocks.flapperRuntime_block_662_taken
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondLen (by jump_dest) rd662
  have rd2987raw := flapperRuntimeBlocks.flapperRuntime_block_684
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4))
    (x1 := UInt256.ofNat 4) (R := [UInt256.ofNat 360, sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    (by jump_dest) rd684
  have rd2987Ex :
      ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) (UInt256.ofNat 2987)
        (flapperRelyUsrWord I :: UInt256.ofNat 360 :: [sel])
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [flapperRelyUsrWord, calldataWord, flapperAddressMask_eq_solcAddrMask] using
        rd2987raw⟩
  obtain ⟨_, _, rd2987⟩ := rd2987Ex
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              (flapperRuntimeBlocks.flapperRuntime_block_2987_taken_memory
                (ee := I) (mem := solcFreePtrMem)))) = UInt256.ofNat 0 := by
    rw [flapperDenyAuthHashSlot]
    exact u256_eq_of_ne (by
      intro h
      exact hauth h.symm)
  obtain ⟨_, _, rd3011⟩ := flapperRuntimeBlocks.flapperRuntime_block_2987_fallthrough
    (R := flapperRelyUsrWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcondAuth rd2987
  exact flapperRuntimeBlocks.flapperRuntime_block_3011
    (R := flapperRelyUsrWord I :: UInt256.ofNat 360 :: [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    rd3011

theorem flapperX_deny_short {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsize : I.calldata.size < UInt256.size) (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flapperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨662⟩
      [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flapperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd662⟩ := hreach
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
  have rd680 := flapperRuntimeBlocks.flapperRuntime_block_662_fallthrough
    (R := [sel])
    (by simp only [List.length_cons, List.length_nil]; omega)
    hcond rd662
  exact flapperRuntimeBlocks.flapperRuntime_block_680
    (R := flapperRuntimeBlocks.flapperRuntime_block_662_fallthrough_stack
      (ee := I) (R := [sel]))
    (by simp only [flapperRuntimeBlocks.flapperRuntime_block_662_fallthrough_stack,
      List.length_cons, List.length_nil]; omega)
    rd680

theorem flapperDispatch_deny {cd : ByteArray}
    (hsel : ((⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some denyTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [begTransition, bidsTransition, cageTransition, dealTransition])
    (post := [fileTransition, fillTransition, gemTransition, kickTransition,
      kicksTransition, lidTransition, liveTransition, relyTransition, tauTransition,
      tendTransition, tickTransition, ttlTransition, vatTransition, wardsTransition,
      yankTransition])
    rfl rfl ?_ ?_
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · rw [flapperBegSelectorBytes, hcd]; decide
    · rw [flapperBidsSelectorBytes, hcd]; decide
    · rw [flapperCageSelectorBytes, hcd]; decide
    · rw [flapperDealSelectorBytes, hcd]; decide
  · rw [flapperDenySelectorBytes]
    exact hsel

theorem flapperDecode_deny_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata =
      some ((∅ : Store).insert "usr"
        (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["usr"] [abiAddress] I.calldata =
    some ((∅ : Store).insert "usr"
      (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
  exact decodeCalldata_legacyAddress_ok hsz36

theorem flapperDecode_deny_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode
      (denyTransition.params.map Param.name)
      (transitionSignature denyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["usr"] [abiAddress] I.calldata = none
  exact decodeCalldata_legacyAddress_none_short hsz4 hshort

theorem flapperDenyBodyReturns (evm : EVM.State) (usrWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) = UInt256.ofNat 1) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "usr" (.address (AccountAddress.ofNat usrWord.toNat)))
      denyTransition.body
      (.returned
        { contract := contract,
          locals := ((∅ : Store).insert "usr"
            (.address (AccountAddress.ofNat usrWord.toNat))) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (solcMappingSlot (UInt256.ofNat 0) (UInt256.land solcAddrMask usrWord))
          (UInt256.ofNat 0))
        none) := by
  let locals := ((∅ : Store).insert "usr"
    (.address (AccountAddress.ofNat usrWord.toNat)))
  let solm : Frame := { contract := contract, locals := locals }
  let er : EvaledStorageRef :=
    { base := "wards",
      steps := [.mindex (.address (AccountAddress.ofNat usrWord.toNat))] }
  let slot := solcMappingSlot (UInt256.ofNat 0) (UInt256.land solcAddrMask usrWord)
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals]
  have hguard :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool true) := by
    exact flapperRelyAuthGuard_true evm locals hbaseWards hauth
  have hrhs : evalExpr? config solm evm (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hbase : locals.get? "wards" = none := hbaseWards
  have her :
      evalStorageRef config solm evm (wardsRef (.var "usr")) = .ok er := by
    simp [locals, solm, er, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, wardsRef,
      evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)) := by
    simp [er, contract, storageDecls, storageTypeAt?, storageTypeStep?, uint256St]
  have hloc : config.storage.layout er = fun _ => some (wordLoc slot) := by
    funext evm'
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, er, wardsSlot,
      slot, mapSlot, solcMappingSlot, keyValueToWord_address_ofNat_mask]
    rfl
  have hstore :
      storageLocStore evm (wordLoc slot) (.int 0) =
        some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat 0)) := by
    simpa [wordLoc, uint256Loc,
      show Int.ofNat (UInt256.ofNat 0).toNat = (0 : Int) by decide] using
      storageLocStore_uint256 evm slot (UInt256.ofNat 0)
  have hassign :
      assignStorageRef? config solm evm .storage (wardsRef (.var "usr")) (.int 0) =
        .ok (solm, Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
          (UInt256.ofNat 0)) :=
    assignStorageRef_storage_scalar (ty := .elem (.int uint256Int))
      (hbase := hbase) (her := her) (hty := hty) (hloc := hloc) (hstore := hstore)
  exact ExecFuncBody.execBlockOK <| by
    simpa [denyTransition, nonpayable, auth, locals, solm, slot] using
      nonpayableRequireAssignStorageBlock (cfg := config) (solm := solm)
        (evm := evm)
        (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat 0))
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rhs := .intLit 0) (ref := wardsRef (.var "usr"))
        (value := .int 0) hwv hguard hrhs hassign

theorem flapperDenyBodyRevertsAuth (evm : EVM.State) (usrWord : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (flapperRelyAuthSlot evm.executionEnv) ≠ UInt256.ofNat 1) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "usr" (.address (AccountAddress.ofNat usrWord.toNat)))
      denyTransition.body
      .reverted := by
  let locals := ((∅ : Store).insert "usr"
    (.address (AccountAddress.ofNat usrWord.toNat)))
  let solm : Frame := { contract := contract, locals := locals }
  have hbaseWards : locals.get? "wards" = none := by
    simp [locals]
  have hguard :
      evalExpr? config solm evm (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
        .ok (.bool false) := by
    exact flapperRelyAuthGuard_false evm locals hbaseWards hauth
  exact ExecFuncBody.execBlockRevert <| by
    simpa [denyTransition, nonpayable, auth, locals, solm] using
      nonpayableSecondRequireReverts (cfg := config) (solm := solm) (evm := evm)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [.assign .storage (wardsRef (.var "usr")) (.intLit 0)])
        hwv hguard

theorem flapperDenyBody
    {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 4))
    (hreach : FlapperBodyReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) g ⟨662⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have hselLit : ((⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) ==
      I.calldata.extract 0 4) = true := by
    simpa [selIs, flapperSelBytes] using hsel
  have hsz4 := calldata_size_ge_of_selIs I
    (⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ : ByteArray) rfl hselLit
  have hd := flapperDispatch_deny (cd := I.calldata) hselLit
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec := flapperDecode_deny_ok (I := I) hsz36
    by_cases hauthEvm : storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) =
        UInt256.ofNat 1
    · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let usrWord := calldataWord I.calldata 4
      let usrSlot := flapperRelyUsrSlot I
      have hloadEq :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (flapperRelyAuthSlot evmSolm.executionEnv) =
            storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
        have hmap :
            Solm.EVM.storageLoad
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (flapperRelyAuthSlot I) =
              Solm.EVM.storageLoad evmSolm I.codeOwner (flapperRelyAuthSlot I) := by
          exact storageLoad_accountMapEquiv
            (evm1 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (evm2 := evmSolm)
            (by simpa [evmSolm, initState] using hAccounts)
            I.codeOwner (flapperRelyAuthSlot I)
        have hread :
            Solm.EVM.storageLoad
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (flapperRelyAuthSlot I) =
              storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
          simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            storageRead_eq]
        simpa [evmSolm, initState] using hmap.symm.trans hread
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) = UInt256.ofNat 1 := by
        rw [hloadEq]
        exact hauthEvm
      have hbody :
          ExecTransitionBody config contract evmSolm
            ((∅ : Store).insert "usr"
              (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
            denyTransition.body
            (.returned
              { contract := contract,
                locals := ((∅ : Store).insert "usr"
                  (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) }
              (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner usrSlot
                (UInt256.ofNat 0))
              none) := by
        simpa [evmSolm, usrWord, usrSlot, flapperRelyUsrSlot, flapperRelyUsrWord,
          flapperAddressMask_eq_solcAddrMask] using
          flapperDenyBodyReturns evmSolm usrWord
            (by simp only [evmSolm, initState]; exact hwv) hauthSolm
      have hCreated :
          cA =
            (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner usrSlot
              (UInt256.ofNat 0)).createdAccounts := by
        rw [storageStore_createdAccounts]
        simp [evmSolm, initState]
      have hAccounts' :
          accountMapEquiv
            (storageWrite I.codeOwner σ_evm usrSlot (UInt256.ofNat 0))
            (Solm.EVM.storageStore evmSolm evmSolm.executionEnv.codeOwner usrSlot
              (UInt256.ofNat 0)).accountMap := by
        rw [storageWrite_eq, storageStore_accountMap]
        simpa [evmSolm, initState] using
          accountMapEquiv_sstoreAccountMap I.codeOwner usrSlot (UInt256.ofNat 0) hAccounts
      have henc : returnEquiv ByteArray.empty none denyTransition.returnType := by
        simpa [denyTransition] using
          (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
            (dvs := []) rfl rfl encodeReturnValues_nil)
      exact (flapperX_deny_ok (g := Sat256.ofUInt256 g) hsize hsz36 hperm hauthEvm hreach)
        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody hCreated hAccounts' henc
    · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let usrWord := calldataWord I.calldata 4
      have hloadEq :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
              (flapperRelyAuthSlot evmSolm.executionEnv) =
            storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
        have hmap :
            Solm.EVM.storageLoad
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (flapperRelyAuthSlot I) =
              Solm.EVM.storageLoad evmSolm I.codeOwner (flapperRelyAuthSlot I) := by
          exact storageLoad_accountMapEquiv
            (evm1 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (evm2 := evmSolm)
            (by simpa [evmSolm, initState] using hAccounts)
            I.codeOwner (flapperRelyAuthSlot I)
        have hread :
            Solm.EVM.storageLoad
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (flapperRelyAuthSlot I) =
              storageRead I.codeOwner σ_evm (flapperRelyAuthSlot I) := by
          simp [initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
            storageRead_eq]
        simpa [evmSolm, initState] using hmap.symm.trans hread
      have hauthSolm :
          Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner
            (flapperRelyAuthSlot evmSolm.executionEnv) ≠ UInt256.ofNat 1 := by
        intro hbad
        exact hauthEvm (by rw [← hloadEq]; exact hbad)
      have hbody :
          ExecTransitionBody config contract evmSolm
            ((∅ : Store).insert "usr"
              (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)))
            denyTransition.body .reverted := by
        simpa [evmSolm, usrWord] using
          flapperDenyBodyRevertsAuth evmSolm usrWord
            (by simp only [evmSolm, initState]; exact hwv) hauthSolm
      exact (flapperX_deny_auth_revert (g := Sat256.ofUInt256 g) hsize hsz36 hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec := flapperDecode_deny_none_short (I := I) hsz4 hshort
    have hrev := flapperX_deny_short
      (g := Sat256.ofUInt256 g) hsize hsz4 hshort hreach
    exact hrev.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.Flapper
