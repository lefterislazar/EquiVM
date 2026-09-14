import Benchmarks.Dss.End.Constructor
import Benchmarks.Dss.End.ParamGetters
import Benchmarks.Dss.End.RuntimeBlocks_009

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace Benchmarks.Dss.End

/-! ## Administration helpers for `rely(address)` and `deny(address)` -/

abbrev endUsrAddressStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "usr" (endArg0AddressValue I)

abbrev endSenderWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev endAuthSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (endSenderWord I)

theorem endDecode_legacyAddress_usr_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["usr"] [addr] I.calldata =
      some (endUsrAddressStore I) := by
  simpa [addr, endUsrAddressStore, endArg0AddressValue, endArg0Word] using
    (decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "usr") hsz36)

theorem endDecode_legacyAddress_usr_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 ["usr"] [addr] I.calldata = none := by
  simpa [addr] using
    (decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "usr") hsz4 hshort)

theorem endSenderWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = endAuthSlot I := by
  simp [endAuthSlot, endSenderWord, wardsSlot, mapSlot, solcMappingSlot,
    keyValueToWord_address]

theorem endAuthStorageRead_eq (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) :
    storageRead I.codeOwner σ
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          ((UInt256.ofNat 0).toByteArray.write 0
            ((UInt256.ofNat I.source.val).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
            (UInt256.ofNat 32).toNat 32))
      = solcSlotWord σ I (endAuthSlot I) := by
  rw [endCtorWardsSlot_eq mem I.source, endSenderWardsSlot_eq I]
  rw [storageRead_eq]

theorem endArg0AddressWord_clean (I : ExecutionEnv) :
    UInt256.land (endArg0AddressWord I) solcAddrMask = endArg0AddressWord I := by
  simpa [endArg0AddressWord, u256_land_comm solcAddrMask (endArg0Word I)] using
    solcAddrMask_clean (solcAddrMask_result_canonical (endArg0Word I))

theorem endArg0AddressWord_clean_left (I : ExecutionEnv) :
    UInt256.land solcAddrMask (endArg0AddressWord I) = endArg0AddressWord I := by
  rw [u256_land_comm solcAddrMask (endArg0AddressWord I)]
  exact endArg0AddressWord_clean I

theorem endAdminStoreSlot_eq (I : ExecutionEnv) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
        ((UInt256.ofNat 0).toByteArray.write 0
          ((UInt256.land (endArg0AddressWord I)
            (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
              (UInt256.ofNat 1))).toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32)
          (UInt256.ofNat 32).toNat 32)
      = solcMappingSlot ⟨0⟩ (endArg0AddressWord I) := by
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  rw [hmask, endArg0AddressWord_clean I]
  rw [show (UInt256.ofNat 0).toNat = 0 by decide,
    show (UInt256.ofNat 32).toNat = 32 by decide]
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (endArg0AddressWord I) (UInt256.ofNat 0) mem) =
    solcMappingSlot ⟨0⟩ (endArg0AddressWord I)
  simpa using
    twoWordHashMem_keccak_solcMappingSlot_ofNat
      (endArg0AddressWord I) (UInt256.ofNat 0) mem

theorem endEvalAuthStorage (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endUsrAddressStore I } evm
        (.storage (wardsRef sender)) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (wardsSlot (.address evm.executionEnv.source))).toNat)) := by
  rw [evalExpr_storage_scalar (t := .int uint256Int)
    (hbase := by simp [endUsrAddressStore, wardsRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, valueToKey?,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, envValue])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_wards (.address evm.executionEnv.source))]
  simp [endRuntimeStorageLocLoad_uint256]

theorem endEvalAuthGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endUsrAddressStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool true) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat = 1 := by
    rw [hauth]
    rfl
  simp [evalBinaryOp?, hnat]

theorem endEvalAuthGuard_false (evm : EVM.State) (I : ExecutionEnv)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endUsrAddressStore I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) =
      .ok (.bool false) := by
  rw [evalExpr?] <;> try (intro h; cases h)
  rw [endEvalAuthStorage evm I]
  simp only [EvalResult.bind, bind, pure, evalExpr?]
  have hnotNat :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source))).toNat ≠ 1 := by
    intro hnat
    exact hauth (by
      apply u256_inj
      simpa using hnat)
  simp [evalBinaryOp?, hnotNat]

theorem endAssignWardsUsr (evm : EVM.State) (I : ExecutionEnv) (val : UInt256) :
    assignStorageRef? config { contract := contract, locals := endUsrAddressStore I } evm
        .storage (wardsRef (.var "usr")) (.int (Int.ofNat val.toNat)) =
      .ok ({ contract := contract, locals := endUsrAddressStore I },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (wardsSlot (endArg0AddressKey I)) val) := by
  rw [assignStorageRef_storage_scalar
    (slot := wardsRef (.var "usr"))
    (er := { base := "wards", steps := [.mindex (endArg0AddressKey I)] })
    (ty := .elem (.int uint256Int))
    (loc := wordLoc (wardsSlot (endArg0AddressKey I)))
    (n := Int.ofNat val.toNat)
    (hbase := by simp [endUsrAddressStore, wardsRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, wardsRef, endUsrAddressStore, endArg0AddressValue,
        endArg0AddressKey, valueToKey?, EvalResult.bind, EvalResult.ofOption,
        bind, pure, evalExpr?])
    (hty := by simp [storageTypeAt?, contract, storageDecls, storageTypeStep?, uint256St])
    (hloc := endConfig_storage_wards (endArg0AddressKey I))
    (hstore := by
      simpa [wordLoc, uint256Loc] using
        storageLocStore_uint256 evm (wardsSlot (endArg0AddressKey I)) val)]

theorem endRelyBodyAuthPass (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩) :
    ExecTransitionBody config contract evm (endUsrAddressStore I) relyTransition.body
      (.returned { contract := contract, locals := endUsrAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (wardsSlot (endArg0AddressKey I)) ⟨1⟩)
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [relyTransition, nonpayable, auth] using
    (nonpayableRequireAssignStorageBlock (cfg := config)
      (solm := { contract := contract, locals := endUsrAddressStore I }) (evm := evm)
      (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (wardsSlot (endArg0AddressKey I)) ⟨1⟩)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 1) (ref := wardsRef (.var "usr")) (value := .int 1)
      hwv (endEvalAuthGuard_true evm I hauth)
      (by simp [evalExpr?, pure])
      (by simpa using endAssignWardsUsr evm I ⟨1⟩))

theorem endDenyBodyAuthPass (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) = ⟨1⟩) :
    ExecTransitionBody config contract evm (endUsrAddressStore I) denyTransition.body
      (.returned { contract := contract, locals := endUsrAddressStore I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (wardsSlot (endArg0AddressKey I)) ⟨0⟩)
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [denyTransition, nonpayable, auth] using
    (nonpayableRequireAssignStorageBlock (cfg := config)
      (solm := { contract := contract, locals := endUsrAddressStore I }) (evm := evm)
      (evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (wardsSlot (endArg0AddressKey I)) ⟨0⟩)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rhs := .intLit 0) (ref := wardsRef (.var "usr")) (value := .int 0)
      hwv (endEvalAuthGuard_true evm I hauth)
      (by simp [evalExpr?, pure])
      (by simpa using endAssignWardsUsr evm I ⟨0⟩))

theorem endAdminBodyAuthFail (evm : EVM.State) (I : ExecutionEnv) (rest : List Stmt)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (wardsSlot (.address evm.executionEnv.source)) ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (endUsrAddressStore I)
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) :: rest)
      .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    nonpayableSecondRequireReverts hwv (endEvalAuthGuard_false evm I hauth)

theorem endAuthStorageLoad_init_eq
    (cA gh bl σ σ₀ A I) (g : Sat256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner
        (wardsSlot (.address I.source)) =
      solcSlotWord σ I (endAuthSlot I) := by
  simp [initState, Solm.EVM.storageLoad, State.lookupAccount, solcSlotWord,
    endSenderWardsSlot_eq I, Account.lookupStorage, Batteries.RBMap.findD]

theorem endReachRely {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 18)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨760⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 18 (by omega) hsel
  obtain ⟨_, _, h343⟩ := endReachFirstArm343 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm343Eq I hsz 0 (by omega))
        (by simpa [endArm343Index] using
          endSelectorMiss_of_match 4 18 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm343Eq I hsz 1 (by omega))
        (by simpa [endArm343Index] using
          endSelectorMiss_of_match 15 18 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm343Eq I hsz 2 (by omega))
        (by simpa [endArm343Index] using
          endSelectorMiss_of_match 10 18 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨343⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm343Eq I hsz 3 (by omega))
      (by simpa [endArm343Index] using hsel)
  exact RD.dispatchTo ⟨760⟩ 3 h343
    (fun j hj => endArms343WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endX_rely_to_auth {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨760⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5275⟩
      [endArg0AddressWord I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd782 := endRuntimeBlocks.endRuntime_block_760_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd5275 := endRuntimeBlocks.endRuntime_block_782
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨562⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_760_taken_stack] using rd782)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_782_stack, endArg0AddressWord,
      endArg0Word, calldataWord, hmask] using rd5275⟩

theorem endX_rely_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨760⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (wardsSlot (endArg0AddressKey I)) ⟨1⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rdAuth⟩ := endX_rely_to_auth (g := g) hsz36 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem, hauth]
    decide
  obtain ⟨_, _, rdStoreEntry⟩ := endRuntimeBlocks.endRuntime_block_5275_taken
    (R := [endArg0AddressWord I, ⟨562⟩, sel]) (by simp) hcondAuth
    (by jump_dest) rdAuth
  obtain ⟨_, _, rdStop⟩ := endRuntimeBlocks.endRuntime_block_5364
    (x0 := endArg0AddressWord I) (x1 := ⟨562⟩) (R := [sel])
    (by simp) hperm (by jump_dest) (by simpa using rdStoreEntry)
  exact endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_5364_stack,
        endAdminStoreSlot_eq I
          (endRuntimeBlocks.endRuntime_block_5275_taken_memory
            (ee := I) (mem := solcFreePtrMem)),
        endWardsSlot_eq I] using rdStop)

theorem endX_rely_auth_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨760⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_rely_to_auth (g := g) hsz36 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) = (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem]
    exact uInt256_eq_zero_of_ne (by
      intro heq
      exact hauth (uInt256_eq_one_eq heq).symm)
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_5275_fallthrough
    (R := [endArg0AddressWord I, ⟨562⟩, sel]) (by simp) hcondAuth rdAuth
  exact endRuntimeBlocks.endRuntime_block_5299
    (R := [endArg0AddressWord I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_rely_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨760⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd778 := endRuntimeBlocks.endRuntime_block_760_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_778 (R :=
      endRuntimeBlocks.endRuntime_block_760_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_760_fallthrough_stack]) (by simpa using rd778)

theorem endRelyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 18))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨760⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 18 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some relyTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 18 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (relyTransition.params.map Param.name) (transitionSignature relyTransition).paramTypes
        I.calldata = some (endUsrAddressStore I) := by
      simpa [config, relyTransition, transitionSignature, addr] using
        endDecode_legacyAddress_usr_ok (I := I) hsz36
    have hAuthWord :
        solcSlotWord σ_evm I (endAuthSlot I) = solcSlotWord σ_solm I (endAuthSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endAuthSlot I) ⟨0⟩
    by_cases hauthSolm : solcSlotWord σ_solm I (endAuthSlot I) = ⟨1⟩
    · have hauthEvm : solcSlotWord σ_evm I (endAuthSlot I) = ⟨1⟩ :=
        hAuthWord.trans hauthSolm
      have hauthSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (wardsSlot (.address I.source)) = ⟨1⟩ := by
        rw [endAuthStorageLoad_init_eq]
        exact hauthSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endUsrAddressStore I) relyTransition.body
            (.returned { contract := contract, locals := endUsrAddressStore I }
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (wardsSlot (endArg0AddressKey I)) ⟨1⟩)
              none) := by
        simpa [initState] using
          endRelyBodyAuthPass
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hauthSrc
      exact (endX_rely_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauthEvm hreach)
        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
          (by rw [storageStore_createdAccounts]; rfl)
          (by
            simpa [initState, storageWrite_eq, storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (wardsSlot (endArg0AddressKey I)) ⟨1⟩ hAccounts)
          (by
            exact returnEquiv.fallthrough (dvs := []) rfl
              (by simp [relyTransition]) (by simp [relyTransition]))
    · have hauthEvm : solcSlotWord σ_evm I (endAuthSlot I) ≠ ⟨1⟩ := by
        intro hbad
        exact hauthSolm (hAuthWord.symm.trans hbad)
      have hauthSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (wardsSlot (.address I.source)) ≠ ⟨1⟩ := by
        rw [endAuthStorageLoad_init_eq]
        exact hauthSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endUsrAddressStore I) relyTransition.body .reverted := by
        simpa [relyTransition, nonpayable, auth] using
          endAdminBodyAuthFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            [ .assign .storage (wardsRef (.var "usr")) (.intLit 1) ]
            (by simp only [initState]; exact hwv) hauthSrc
      exact (endX_rely_auth_fail (g := Sat256.ofUInt256 g) hsz36 hsize hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (relyTransition.params.map Param.name) (transitionSignature relyTransition).paramTypes
        I.calldata = none := by
      simpa [config, relyTransition, transitionSignature, addr] using
        endDecode_legacyAddress_usr_none_short (I := I) hsz4 hshort
    exact (endX_rely_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

theorem endReachDeny {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : endSelectorMatches I (endSelBytes 19)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩
      [endRuntimeSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword := endSelWord_eq_at I hsz 19 (by omega) hsel
  obtain ⟨_, _, h223⟩ := endReachFirstArm223 (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hword]; native_decide) (by rw [hword]; native_decide) (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ j))
        (endRuntimeSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact endEqIfZero (endArm223Eq I hsz 0 (by omega))
        (by simpa [endArm223Index] using
          endSelectorMiss_of_match 26 19 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm223Eq I hsz 1 (by omega))
        (by simpa [endArm223Index] using
          endSelectorMiss_of_match 16 19 (by omega) (by omega) (by omega) hsel)
    · exact endEqIfZero (endArm223Eq I hsz 2 (by omega))
        (by simpa [endArm223Index] using
          endSelectorMiss_of_match 8 19 (by omega) (by omega) (by omega) hsel)
  have htake : UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode ⟨223⟩ 3))
      (endRuntimeSelWord I) ≠ ⟨0⟩ :=
    endEqIfNeZero (endArm223Eq I hsz 3 (by omega))
      (by simpa [endArm223Index] using hsel)
  exact RD.dispatchTo ⟨941⟩ 3 h223
    (fun j hj => endArms223WellFormed j (by omega)) heq0 htake
    (by jump_dest) (by native_decide) (by simp)

theorem endX_deny_to_auth {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7500⟩
      [endArg0AddressWord I, ⟨562⟩, sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckOkUnsigned_4_32 (I := I) hsz36 hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rd963 := endRuntimeBlocks.endRuntime_block_941_taken
    (R := [sel]) (by simp) hcond (by jump_dest) rdEntry
  have rd7500 := endRuntimeBlocks.endRuntime_block_963
    (x0 := UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (x1 := ⟨4⟩)
    (R := [⟨562⟩, sel]) (by simp) (by jump_dest)
    (by simpa [endRuntimeBlocks.endRuntime_block_941_taken_stack] using rd963)
  have hmask :
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1) = solcAddrMask := by
    native_decide
  exact ⟨_, _, by
    simpa [endRuntimeBlocks.endRuntime_block_963_stack, endArg0AddressWord,
      endArg0Word, calldataWord, hmask] using rd7500⟩

theorem endX_deny_ok {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hauth : solcSlotWord σ I (endAuthSlot I) = ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, storageWrite I.codeOwner σ (wardsSlot (endArg0AddressKey I)) ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, rdAuth⟩ := endX_deny_to_auth (g := g) hsz36 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) ≠ (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem, hauth]
    decide
  obtain ⟨_, _, rdStoreEntry⟩ := endRuntimeBlocks.endRuntime_block_7500_taken
    (R := [endArg0AddressWord I, ⟨562⟩, sel]) (by simp) hcondAuth
    (by jump_dest) rdAuth
  obtain ⟨_, _, rdStop⟩ := endRuntimeBlocks.endRuntime_block_7589
    (x0 := endArg0AddressWord I) (x1 := ⟨562⟩) (R := [sel])
    (by simp) hperm (by jump_dest) (by simpa using rdStoreEntry)
  exact endRuntimeBlocks.endRuntime_block_562 (R := [sel]) (by simp)
    (by
      simpa [endRuntimeBlocks.endRuntime_block_7589_stack,
        endAdminStoreSlot_eq I
          (endRuntimeBlocks.endRuntime_block_7500_taken_memory
            (ee := I) (mem := solcFreePtrMem)),
        endWardsSlot_eq I] using rdStop)

theorem endX_deny_auth_fail {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hauth : solcSlotWord σ I (endAuthSlot I) ≠ ⟨1⟩)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdAuth⟩ := endX_deny_to_auth (g := g) hsz36 hsize hreach
  have hcondAuth :
      UInt256.eq (UInt256.ofNat 1)
          (storageRead I.codeOwner σ
            (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
              ((UInt256.ofNat 0).toByteArray.write 0
                ((UInt256.ofNat I.source.val).toByteArray.write 0 solcFreePtrMem
                  (UInt256.ofNat 0).toNat 32)
                (UInt256.ofNat 32).toNat 32))) = (UInt256.ofNat 0) := by
    rw [endAuthStorageRead_eq σ I solcFreePtrMem]
    exact uInt256_eq_zero_of_ne (by
      intro heq
      exact hauth (uInt256_eq_one_eq heq).symm)
  obtain ⟨_, _, rdRevertEntry⟩ := endRuntimeBlocks.endRuntime_block_7500_fallthrough
    (R := [endArg0AddressWord I, ⟨562⟩, sel]) (by simp) hcondAuth rdAuth
  exact endRuntimeBlocks.endRuntime_block_7524
    (R := [endArg0AddressWord I, ⟨562⟩, sel]) (by simp) rdRevertEntry

theorem endX_deny_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  have hlt := endSolcDecodeLenCheckShortUnsigned_4_32 (I := I) hsz4 hshort hsize
  have hcond :
      UInt256.isZero
          (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rd959 := endRuntimeBlocks.endRuntime_block_941_fallthrough
    (R := [sel]) (by simp) hcond rdEntry
  exact endRuntimeBlocks.endRuntime_block_959 (R :=
      endRuntimeBlocks.endRuntime_block_941_fallthrough_stack (ee := I) (R := [sel]))
    (by simp [endRuntimeBlocks.endRuntime_block_941_fallthrough_stack]) (by simpa using rd959)

theorem endDenyBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 19))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨941⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 := endSelectorMatches_size 19 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some denyTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 19 (by omega) hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdec : decodeCalldataWithMode config.abiDecodeMode
        (denyTransition.params.map Param.name) (transitionSignature denyTransition).paramTypes
        I.calldata = some (endUsrAddressStore I) := by
      simpa [config, denyTransition, transitionSignature, addr] using
        endDecode_legacyAddress_usr_ok (I := I) hsz36
    have hAuthWord :
        solcSlotWord σ_evm I (endAuthSlot I) = solcSlotWord σ_solm I (endAuthSlot I) :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endAuthSlot I) ⟨0⟩
    by_cases hauthSolm : solcSlotWord σ_solm I (endAuthSlot I) = ⟨1⟩
    · have hauthEvm : solcSlotWord σ_evm I (endAuthSlot I) = ⟨1⟩ :=
        hAuthWord.trans hauthSolm
      have hauthSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (wardsSlot (.address I.source)) = ⟨1⟩ := by
        rw [endAuthStorageLoad_init_eq]
        exact hauthSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endUsrAddressStore I) denyTransition.body
            (.returned { contract := contract, locals := endUsrAddressStore I }
              (Solm.EVM.storageStore
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                I.codeOwner (wardsSlot (endArg0AddressKey I)) ⟨0⟩)
              none) := by
        simpa [initState] using
          endDenyBodyAuthPass
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simp only [initState]; exact hwv) hauthSrc
      exact (endX_deny_ok (g := Sat256.ofUInt256 g) hsz36 hsize hperm hauthEvm hreach)
        |>.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
          (by rw [storageStore_createdAccounts]; rfl)
          (by
            simpa [initState, storageWrite_eq, storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (wardsSlot (endArg0AddressKey I)) ⟨0⟩ hAccounts)
          (by
            exact returnEquiv.fallthrough (dvs := []) rfl
              (by simp [denyTransition]) (by simp [denyTransition]))
    · have hauthEvm : solcSlotWord σ_evm I (endAuthSlot I) ≠ ⟨1⟩ := by
        intro hbad
        exact hauthSolm (hAuthWord.symm.trans hbad)
      have hauthSrc :
          Solm.EVM.storageLoad
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              I.codeOwner (wardsSlot (.address I.source)) ≠ ⟨1⟩ := by
        rw [endAuthStorageLoad_init_eq]
        exact hauthSolm
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (endUsrAddressStore I) denyTransition.body .reverted := by
        simpa [denyTransition, nonpayable, auth] using
          endAdminBodyAuthFail
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            [ .assign .storage (wardsRef (.var "usr")) (.intLit 0) ]
            (by simp only [initState]; exact hwv) hauthSrc
      exact (endX_deny_auth_fail (g := Sat256.ofUInt256 g) hsz36 hsize hauthEvm hreach)
        |>.reEquivExecutionRevert hcode hd hdec hbody
  · have hshort : I.calldata.size < 36 := by omega
    have hdec : decodeCalldataWithMode config.abiDecodeMode
        (denyTransition.params.map Param.name) (transitionSignature denyTransition).paramTypes
        I.calldata = none := by
      simpa [config, denyTransition, transitionSignature, addr] using
        endDecode_legacyAddress_usr_none_short (I := I) hsz4 hshort
    exact (endX_deny_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hd hdec

end Benchmarks.Dss.End
